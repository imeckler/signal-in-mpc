#!/usr/bin/env python3
"""Audit compact SHA compression equivalence and public exported fixtures."""

import argparse
import ctypes
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tarfile
import time

HERE = Path(__file__).resolve().parent
REFERENCE = HERE.parent
ROOT = REFERENCE.parent
sys.path.insert(0, str(REFERENCE))
sys.path.insert(0, str(ROOT))
from extract import PINS, check_sources, digest, inventory
from backend_adapter.boolean import load
from backend_adapter.aig import statistics
from scripts.check_lean_crypto import evaluate_lanes

MODELS = ["Aeneas/Std/Core/Iter.lean", "Aeneas/Std/Core/Cmp.lean",
          "Aeneas/Std/Array/Array.lean", "Aeneas/Std/Scalar/Core.lean",
          "Aeneas/Std/Scalar/CloneCopy.lean", "Aeneas/Std/Scalar/EqOrd.lean",
          "Aeneas/Std/Scalar/Bitwise.lean", "Aeneas/Std/Scalar/Ops/Sub.lean",
          "Aeneas/Std/Scalar/Ops/Rem.lean", "Aeneas/Std/Scalar/Rotate.lean",
          "Aeneas/Std/Scalar/WrappingOps/Add.lean", "Aeneas/Std/Primitives.lean",
          "Aeneas/Std/WP.lean"]
MODULES = ["LibSignalReference/Generated/Sha256Compact/Types",
           "LibSignalReference/Generated/Sha256Compact/Funs",
           "LibSignalReference/Proofs/ShaCompactReference",
           "LibSignalReference/Proofs/ShaCompactCompression", "LibSignalReference/Proofs/ShaCompact",
           "LibSignalReference/Proofs/ShaCompactEquivalence"]
ROOT_FILES = ["TlsMpc/Signal/ShaCompact.lean", "TlsMpc/Sha256.lean", "TlsMpc/ByteCircuit.lean", "TlsMpc/AigExport.lean",
              "TlsMpc/BvConstruct.lean", "backend_adapter/aig.py", "backend_adapter/boolean.py",
              "scripts/check_lean_crypto.py", "SignalReference/MetadataWork/trim_step_metadata.py"]


def fixtures(library):
    # Exact public OpenSSL header layout: h[8], Nl, Nh, data[16], num, md_len.
    class Context(ctypes.Structure):
        _fields_ = [('h', ctypes.c_uint * 8), ('Nl', ctypes.c_uint), ('Nh', ctypes.c_uint),
                    ('data', ctypes.c_uint * 16), ('num', ctypes.c_uint), ('md_len', ctypes.c_uint)]
    if ctypes.sizeof(ctypes.c_uint) != 4 or ctypes.sizeof(Context) != 112:
        raise ValueError('OpenSSL SHA256_CTX layout differs from the reviewed header')
    crypto = ctypes.CDLL(str(library))
    crypto.SHA256_Transform.argtypes = [ctypes.POINTER(Context), ctypes.POINTER(ctypes.c_ubyte)]
    crypto.SHA256_Transform.restype = None
    crypto.OpenSSL_version.argtypes = [ctypes.c_int]
    crypto.OpenSSL_version.restype = ctypes.c_char_p

    def transform(raw):
        context = Context()
        context.h[:] = [int.from_bytes(raw[i:i + 4], 'big') for i in range(0, 32, 4)]
        block = (ctypes.c_ubyte * 64).from_buffer_copy(raw[32:])
        crypto.SHA256_Transform(ctypes.byref(context), block)
        return b''.join(int(word).to_bytes(4, 'big') for word in context.h)

    inputs = [bytes(96), bytes([255]) * 96, bytes(range(96)), bytes([0x55, 0xaa]) * 48]
    inputs += [hashlib.shake_256(f'public-compact-compress-{i}'.encode()).digest(96) for i in range(32)]
    expected = [transform(raw) for raw in inputs]
    initial = bytes.fromhex('6a09e667bb67ae853c6ef372a54ff53a510e527f9b05688c1f83d9ab5be0cd19')
    for length in (0, 1, 3, 7, 15, 31, 32, 54, 55):
        message = hashlib.shake_256(f'public-compact-message-{length}'.encode()).digest(length)
        block = message + b'\x80' + bytes(55 - length) + (8 * length).to_bytes(8, 'big')
        raw = initial + block
        answer = transform(raw)
        if answer != hashlib.sha256(message).digest():
            raise AssertionError('OpenSSL compression ABI disagrees with independent hash interface')
        inputs.append(raw)
        expected.append(answer)
    return inputs, expected, crypto.OpenSSL_version(0).decode()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packages-dir', type=Path, required=True)
    parser.add_argument('--libcrypto', type=Path,
                        default=Path('/opt/homebrew/opt/openssl@3/lib/libcrypto.3.dylib'))
    args = parser.parse_args()
    check_sources()
    subprocess.run([sys.executable, str(REFERENCE / 'MetadataWork/trim_step_metadata.py'), '--canonical'], check=True)
    review = json.loads((REFERENCE / 'Extraction/sha256-compact-metadata/review.json').read_text())
    selected = inventory(REFERENCE / 'Extraction/libsignal_sha256_compact_reviewed.llbc')
    if (review['aeneas_exit_code'] or review['remaining_external_templates'] or selected['has_errors']
            or selected['body_kinds'] != {'Structured': 2, 'Opaque': 11}):
        raise ValueError('Incomplete reviewed compression translation')
    generated = REFERENCE / 'LibSignalReference/Generated/Sha256Compact'
    if sorted(p.name for p in generated.glob('*.lean')) != ['Funs.lean', 'Types.lean']:
        raise ValueError('Unexpected reference templates')
    names = re.findall(r'^def ([^\s]+)', (generated / 'Funs.lean').read_text(), re.M)
    if names != ['consts.K32', 'sha256.soft.compact.compress_u32_loop.body',
                 'sha256.soft.compact.compress_u32_loop', 'sha256.soft.compact.compress_u32']:
        raise ValueError('Selected function inventory differs')
    if re.search(r'^\s*(?:def|opaque|structure|inductive)\b', (generated / 'Types.lean').read_text(), re.M):
        raise ValueError('Unselected iterator metadata remains in generated types')
    sources = [REFERENCE / (module + '.lean') for module in MODULES]
    for path in sources:
        if re.search(r'\b(sorry|admit|axiom|native_decide)\b', path.read_text()):
            raise ValueError(f'Unfinished or externally checked proof: {path}')
    backend = (REFERENCE / PINS['aeneas']['directory'] / 'backends/lean').resolve()
    archive = ROOT / '.deps/aeneas-macos-aarch64-2026-08-27.tar.gz'
    if digest(archive) != PINS['aeneas']['macos_aarch64_archive_sha256']:
        raise ValueError('Official Aeneas archive hash differs')
    with tarfile.open(archive) as bundle:
        for name in MODELS:
            if bundle.extractfile('backends/lean/' + name).read() != (backend / name).read_bytes():
                raise ValueError(f'Standard model differs from official archive: {name}')
    for path in (ROOT / 'lean-toolchain', REFERENCE / 'lean-toolchain', backend / 'lean-toolchain'):
        if path.read_text().strip() != PINS['aeneas']['lean_toolchain']:
            raise ValueError(f'Lean toolchain differs: {path}')
    package_paths = []
    for package in json.loads((backend / 'lake-manifest.json').read_text())['packages']:
        directory = args.packages_dir / package['name']
        revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=directory, text=True).strip()
        if revision != package['rev']:
            raise ValueError(f'Cached dependency revision differs: {directory}')
        path = directory / '.lake/build/lib/lean'
        if path.is_dir():
            package_paths.append(path)
    tracked = [ROOT / p for p in ROOT_FILES] + sources + [Path(__file__), HERE / 'Export.lean']
    hashes = {str(path.relative_to(ROOT)): digest(path) for path in tracked}
    subprocess.run(['lake', 'build', 'TlsMpc.Signal.ShaCompact'], cwd=ROOT, check=True)
    output = REFERENCE / '.lake/build/lib/lean'
    env = os.environ.copy()
    env['LEAN_PATH'] = os.pathsep.join(str(p) for p in
        [output, ROOT / '.lake/build/lib/lean', backend / '.lake/build/lib/lean', *package_paths])
    for module in MODULES:
        target = output / (module + '.olean')
        target.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(['lean', '-o', str(target), module + '.lean'], cwd=REFERENCE, env=env, check=True)
    result = subprocess.run(['lean', 'ShaCompactWork/Checks.lean'], cwd=REFERENCE, env=env,
                            check=True, text=True, capture_output=True)
    reports = re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", result.stdout)
    expected_count = len(re.findall(r'^#print axioms ', (HERE / 'Checks.lean').read_text(), re.M))
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    if len(reports) != expected_count or any({x.strip() for x in names.split(',') if x.strip()} - allowed
                                           for _, names in reports):
        raise ValueError('Unexpected or missing theorem assumption report')
    print(result.stdout, end='')
    artifact_path = ROOT / '.deps/signal-sha-compact-artifacts/compress.json'
    artifact_path.parent.mkdir(parents=True, exist_ok=True)
    started = time.perf_counter()
    with artifact_path.open('w') as target:
        subprocess.run(['lean', '--run', 'ShaCompactWork/Export.lean'], cwd=REFERENCE, env=env,
                       stdout=target, check=True, timeout=300)
    elapsed = time.perf_counter() - started
    image = load(artifact_path)
    if image['input_bits'] != 768 or image['input_widths'] != [32] * 24 or len(image['outputs']) != 256:
        raise ValueError('Compression artifact ABI differs')
    raw, expected, version = fixtures(args.libcrypto)
    if evaluate_lanes(image, raw) != expected:
        raise AssertionError('Exported circuit differs from OpenSSL compression')
    if hashes != {str(path.relative_to(ROOT)): digest(path) for path in tracked}:
        raise ValueError('Proof/export sources changed during the audit')
    report = {'checked_at_utc': datetime.now(timezone.utc).isoformat(),
              'operation_refinement_checked': True, 'canonical_reference_integrated': True,
              'selected_operation': 'actual locked sha2 0.11.0 soft::compact::compress_u32',
              'domain': 'every eight-word u32 state and sixteen-word u32 block; success and all output bits',
              'additional_trusted_extraction_step': 'MetadataWork/trim_step_metadata.py, independently reviewed exact dead-dictionary-field filtering',
              'metadata_review': review, 'normalized_llbc_inventory': selected,
              'checked_theorems': [name for name, _ in reports], 'allowed_foundational_axioms': sorted(allowed),
              'custom_crypto_models': [], 'custom_axioms': [], 'rust_source_patches': [],
              'standard_model_sources_sha256': {name: digest(backend / name) for name in MODELS},
              'sources_sha256': hashes, 'artifact_sha256': digest(artifact_path),
              'export_seconds': elapsed, 'fixture_lanes': len(raw), 'all_outputs_match': True,
              'oracle': version + ' SHA256_Transform; 9 padded cases also checked against hashlib.sha256',
              'libcrypto_sha256': digest(args.libcrypto), 'adapter_statistics': statistics(image),
              'backend_bytecode_compiled': False, 'native_mpc_executed': False,
              'whole_sha_digest_hmac_hkdf_refinement_established': False,
              'root_full_list_sha_compression_equivalence_established': True,
              'root_full_digest_hmac_wrapper_equivalence_established': False}
    (HERE / 'proof-check.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'Checked {expected_count} theorem endpoints and {len(raw)} public compression fixtures.', flush=True)


if __name__ == '__main__':
    main()
