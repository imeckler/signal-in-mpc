#!/usr/bin/env python3
"""Build/check the unverified native refresh prototype; never run network MPC.

The refresh-only MP-SPDZ copy has a recorded TLS policy patch. The shared
backend source remains untouched. Local native checks and memory-BIO TLS
handshakes do not substitute for a five-party execution or a security proof.
"""
import hashlib
import json
from pathlib import Path
import platform
import shutil
import socket
import subprocess
import tarfile

ROOT = Path(__file__).resolve().parents[1]
BUILD = ROOT / '.deps/sharing-refresh'
ORIGINAL = ROOT / '.deps/MP-SPDZ'
ISOLATED = BUILD / 'MP-SPDZ'


def hardened_tls(source):
    old_mode = 'set_verify_mode(boost::asio::ssl::verify_peer);\n        set_verify_callback(boost::asio::ssl::host_name_verification(other));'
    if source.count(old_mode) != 1 or source.count('context::tlsv12') != 1:
        raise RuntimeError('Unexpected pinned TLS source; review patch before building')
    source = source.replace('context::tlsv12', 'context::tlsv13')
    source = source.replace('        add_verify_path(SSL_DIR);', '''        add_verify_path(SSL_DIR);
        SSL_CTX_set_session_cache_mode(native_handle(), SSL_SESS_CACHE_OFF);
        SSL_CTX_set_options(native_handle(), SSL_OP_NO_TICKET);
        if (SSL_CTX_set_num_tickets(native_handle(), 0) != 1)
            throw runtime_error("cannot disable refresh TLS tickets");''')
    helper = '''#include <memory>
#include <openssl/pem.h>

#define TLS_MPC_REFRESH_TRANSPORT_POLICY 2

inline void refresh_verify_peer(
        boost::asio::ssl::stream<boost::asio::ip::tcp::socket>& socket,
        const string& other)
{
    const string certificate_file = string(SSL_DIR) + other + ".pem";
    std::unique_ptr<BIO, decltype(&BIO_free)> input(
            BIO_new_file(certificate_file.c_str(), "r"), BIO_free);
    if (!input) throw runtime_error("cannot read pinned refresh peer certificate");
    std::shared_ptr<X509> expected(
            PEM_read_bio_X509(input.get(), nullptr, nullptr, nullptr), X509_free);
    if (!expected) throw runtime_error("invalid pinned refresh peer certificate");
    socket.set_verify_mode(boost::asio::ssl::verify_peer |
            boost::asio::ssl::verify_fail_if_no_peer_cert);
    socket.set_verify_callback([expected, other](bool verified,
            boost::asio::ssl::verify_context& context)
    {
        if (!verified) return false;
        if (X509_STORE_CTX_get_error_depth(context.native_handle()) != 0) return true;
        auto presented = X509_STORE_CTX_get_current_cert(context.native_handle());
        return presented && X509_cmp(presented, expected.get()) == 0 &&
                boost::asio::ssl::host_name_verification(other)(true, context);
    });
}

'''
    source = source.replace('class ssl_socket :', helper + 'class ssl_socket :')
    return source.replace(old_mode, 'refresh_verify_peer(*this, other);')


def verify_source_and_copy():
    pin = json.loads((ROOT / 'benchmarks/config/dependencies.json').read_text())['mp_spdz']
    archive = ROOT / '.deps/mp-spdz-v0.4.4.tar.gz'
    if hashlib.sha256(archive.read_bytes()).hexdigest() != pin['source_archive_sha256']:
        raise RuntimeError('Pinned archive digest mismatch')
    BUILD.mkdir(parents=True, exist_ok=True)
    if not ISOLATED.exists():
        if platform.system() == 'Darwin':
            subprocess.run(['cp', '-cR', str(ORIGINAL), str(ISOLATED)], check=True)
        else:
            shutil.copytree(ORIGINAL, ISOLATED)
    checked = 0
    patch = None
    with tarfile.open(archive) as files:
        prefix = files.getmembers()[0].name.split('/')[0]
        for member in files:
            if not member.isfile():
                continue
            relative = Path(member.name).relative_to(prefix)
            expected = files.extractfile(member).read()
            if (ORIGINAL / relative).read_bytes() != expected:
                raise RuntimeError(f'Shared backend source changed: {relative}')
            target = ISOLATED / relative
            actual = target.read_bytes()
            if str(relative) == 'Networking/ssl_sockets.h':
                patched = hardened_tls(expected.decode()).encode()
                # Upgrade the earlier reviewed mandatory-certificate overlay;
                # it lacked exact leaf pinning against peer-issued role certs.
                previous_patch = 'f041e216e216ac287ded05701254533bbb6fa80b127e9cac59ecf019270cae71'
                if actual not in [expected, patched] and hashlib.sha256(actual).hexdigest() != previous_patch:
                    raise RuntimeError('Refresh TLS overlay contains an unreviewed change')
                if actual != patched:
                    target.write_bytes(patched)
                patch = {'path': str(relative),
                         'original_sha256': hashlib.sha256(expected).hexdigest(),
                         'patched_sha256': hashlib.sha256(patched).hexdigest()}
            elif actual != expected:
                raise RuntimeError(f'Refresh backend source changed: {relative}')
            checked += 1
    return pin, patch, checked


def logged(command, name):
    with (BUILD / name).open('w') as output:
        subprocess.run(command, cwd=ISOLATED, stdout=output,
                       stderr=subprocess.STDOUT, check=True)


def main():
    pin, patch, checked = verify_source_and_copy()
    logged(['make', '-j2', 'libSPDZ.so'], 'backend-build.log')
    if platform.system() == 'Darwin':
        # The upstream install name is just "libSPDZ.so". Do not accidentally
        # load the unpatched library when launched from a different directory.
        library = ISOLATED / 'libSPDZ.so'
        identity = subprocess.check_output(['otool', '-D', str(library)], text=True)
        if identity.splitlines()[-1] != str(library):
            subprocess.run(['install_name_tool', '-id', str(library), str(library)], check=True)
    logged(['make', '-f', str(ROOT / 'refresh/Makefile'),
            f'REFRESH_ROOT={ROOT / "refresh"}', f'REFRESH_BUILD={BUILD}', '-j2'],
           'adapter-build.log')
    results = []
    przs_results = []
    for domain in ['fp25519', 'ccd40', 'ccd64']:
        output = subprocess.check_output([str(BUILD / 'refresh-local-checks'), domain],
                                         cwd=ISOLATED, text=True)
        results.append(json.loads(output))
        output = subprocess.check_output([str(BUILD / 'refresh-przs-checks'), domain],
                                         cwd=ISOLATED, text=True)
        przs_results.append(json.loads(output))
    tls = json.loads(subprocess.check_output([str(BUILD / 'refresh-tls-checks')],
                                            cwd=ISOLATED, text=True))
    try:
        with socket.socket() as probe:
            probe.bind(('127.0.0.1', 0))
        socket_status = 'available_but_network_mpc_not_run_by_this_script'
    except OSError as error:
        socket_status = f'unavailable: {error}'
    report = {
        'backend_pin': pin['commit'], 'pinned_source_files_verified': checked,
        'isolated_tls_patch': patch, 'native_local_checks': results,
        'experimental_przs_local_checks': przs_results,
        'tls_memory_bio_checks': tls, 'socket_status': socket_status,
        'network_mpc_executed': False, 'proactive_security_proved': False,
        'native_sources_sha256': {
            str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in sorted((ROOT / 'refresh').glob('*'))
            if path.suffix in ['.h', '.cpp']},
        'scope': 'Compiled candidate adapter, native primitive/format checks and local TLS handshakes only',
    }
    (BUILD / 'checks.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
