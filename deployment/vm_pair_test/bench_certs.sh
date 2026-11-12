#!/bin/sh
# Certificates for the field engine's connections between the two parties.
#
# The field engine's library speaks TLS between the parties and expects, in Player-Data/ under the
# working directory: this party's key and certificate (P0.key/P0.pem for party 0, P1.* for party 1)
# and the other party's certificate, with OpenSSL's hashed links. Its own script makes both
# parties' keys on one machine; this one makes each party's key on its own machine, so only
# certificates (public) are exchanged.
#
#   bench_certs.sh init PARTY WORKDIR        make this party's key and certificate (PARTY is 0 or 1)
#   bench_certs.sh trust PEER.pem WORKDIR    install the other party's certificate and rehash
#
# Certificates are self-signed, named P0 / P1, valid 30 days. OPENSSL=/path/to/openssl overrides
# the openssl binary (macOS: use Homebrew's, the system one has no `rehash`).
set -eu
OPENSSL=${OPENSSL:-openssl}
usage() { echo "usage: $0 init PARTY(0|1) WORKDIR | trust PEER.pem WORKDIR" >&2; exit 2; }
[ $# -eq 3 ] || usage
case "$1" in
init)
    party=$2; dir=$3/Player-Data
    case "$party" in 0|1) ;; *) usage ;; esac
    mkdir -p "$dir"
    if [ -e "$dir/P$party.key" ]; then echo "$dir/P$party.key exists; not overwriting" >&2; exit 1; fi
    umask 077
    "$OPENSSL" req -newkey rsa:2048 -nodes -x509 -days 30 -subj "/CN=P$party" \
        -keyout "$dir/P$party.key" -out "$dir/P$party.pem" 2>/dev/null
    chmod 600 "$dir/P$party.key"; chmod 644 "$dir/P$party.pem"
    "$OPENSSL" rehash "$dir" >/dev/null
    echo "made $dir/P$party.key (stays here) and $dir/P$party.pem (send this file to the other machine)"
    ;;
trust)
    pem=$2; dir=$3/Player-Data
    [ -f "$pem" ] || { echo "no such file: $pem" >&2; exit 1; }
    if grep -q "PRIVATE KEY" "$pem"; then echo "$pem contains a private key; send only the .pem certificate" >&2; exit 1; fi
    subject=$("$OPENSSL" x509 -in "$pem" -noout -subject -nameopt multiline | sed -n 's/^ *commonName *= *//p')
    case "$subject" in P0|P1) ;; *) echo "unexpected certificate name: $subject" >&2; exit 1 ;; esac
    [ -e "$dir/$subject.key" ] && { echo "$subject is this machine's own party; expected the other party's certificate" >&2; exit 1; }
    mkdir -p "$dir"
    cp "$pem" "$dir/$subject.pem"; chmod 644 "$dir/$subject.pem"
    "$OPENSSL" rehash "$dir" >/dev/null
    echo "installed $dir/$subject.pem; fingerprint (compare with the other machine's):"
    "$OPENSSL" x509 -in "$dir/$subject.pem" -noout -fingerprint -sha256
    ;;
*) usage ;;
esac
