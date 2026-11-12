#!/bin/sh
# WireGuard between the two test machines. Each machine makes its own key; only public keys and
# public addresses are exchanged. Run as root on each machine (Ubuntu 24.04: wireguard-tools).
#
#   wg_setup.sh keygen                              make this machine's key; prints its PUBLIC key
#   wg_setup.sh up SIDE PEER_PUBLIC_KEY PEER_ADDR   SIDE is a or b; PEER_ADDR the other machine's public IPv4
#   wg_setup.sh status                              handshake age, transfer counters, MTU
#   wg_setup.sh down                                remove the tunnel, its configuration and the key
#
# Tunnel addresses: side a = 10.77.0.1, side b = 10.77.0.2 (a /30 used by nothing else here).
# UDP port 51820 on both (WG_PORT overrides); MTU 1420 (WG_MTU overrides). The peer is allowed
# only its one tunnel address. Open UDP 51820 from the other machine's public address in the
# provider's firewall; nothing else of the test needs a public port.
set -eu
NAME=vmpair
DIR=/etc/wireguard
PORT=${WG_PORT:-51820}
MTU=${WG_MTU:-1420}
[ "$(id -u)" = 0 ] || { echo "run as root" >&2; exit 1; }
command -v wg >/dev/null || { echo "wireguard-tools is not installed (apt-get install wireguard-tools)" >&2; exit 1; }
case "${1:-}" in
keygen)
    umask 077; mkdir -p "$DIR"
    [ -e "$DIR/$NAME.key" ] || wg genkey >"$DIR/$NAME.key"
    echo "public key of this machine (give it to the other side):"
    wg pubkey <"$DIR/$NAME.key"
    ;;
up)
    [ $# -eq 4 ] || { echo "usage: $0 up a|b PEER_PUBLIC_KEY PEER_PUBLIC_IPV4" >&2; exit 2; }
    case "$2" in a) mine=10.77.0.1; theirs=10.77.0.2 ;; b) mine=10.77.0.2; theirs=10.77.0.1 ;; *) echo "SIDE is a or b" >&2; exit 2 ;; esac
    [ -e "$DIR/$NAME.key" ] || { echo "run '$0 keygen' first" >&2; exit 1; }
    umask 077
    cat >"$DIR/$NAME.conf" <<EOF
[Interface]
PrivateKey = $(cat "$DIR/$NAME.key")
Address = $mine/30
ListenPort = $PORT
MTU = $MTU

[Peer]
PublicKey = $3
AllowedIPs = $theirs/32
Endpoint = $4:$PORT
PersistentKeepalive = 25
EOF
    wg-quick down "$NAME" 2>/dev/null || true
    wg-quick up "$NAME"
    echo "this machine: $mine   other machine: $theirs   (ping -c 3 $theirs once both sides are up)"
    ;;
status)
    wg show "$NAME"; ip -details link show "$NAME" | grep -o 'mtu [0-9]*'
    ;;
down)
    wg-quick down "$NAME" 2>/dev/null || true
    rm -f "$DIR/$NAME.conf" "$DIR/$NAME.key"
    echo "tunnel, configuration and key removed"
    ;;
*) echo "usage: $0 keygen | up a|b PEER_PUBLIC_KEY PEER_PUBLIC_IPV4 | status | down" >&2; exit 2 ;;
esac
