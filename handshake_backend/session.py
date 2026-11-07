"""Composable TLS secret stages for one mixed MP-SPDZ VM.

This is a compiler-side adapter, NOT an interactive transport/controller bridge.
Public parameters may be shared-register constants or agreed runtime public
inputs converted to bits by the caller. No key or decrypted application data
is opened here. Algorithms are loaded from the Lean artifacts.
"""
from dataclasses import dataclass
from pathlib import Path
from backend_adapter.boolean import load
from .field_dag import load as load_field, MODULUS
from .mixed import execute_secret, execute_boolean, fresh_scalar_fields, field_to_wire_bits


@dataclass
class Traffic:
    secret: list
    key: list
    iv: list


@dataclass
class Handshake:
    client: Traffic
    server: Traffic
    main: list


class Kernels:
    def __init__(self, directory):
        self.directory = Path(directory)
        self.field = load_field(self.directory / 'x25519-field.json')
        self.images = {}

    def circuit(self, name, inputs):
        if name not in self.images:
            self.images[name] = load(self.directory / (name + '.json'))
        return execute_boolean(self.images[name], inputs)

    def begin(self):
        from Compiler.types import sint
        scalar = fresh_scalar_fields()
        public_key = execute_secret(self.field, scalar + [sint(9)])[0]
        # Caller may explicitly release ONLY this public key.
        return scalar, field_to_wire_bits(public_key)

    def traffic(self, secret):
        output = self.circuit('tls-traffic-keys', secret)
        return Traffic(secret, output[:128], output[128:224])

    def derive(self, scalar, peer_u, hello_hash):
        from Compiler.types import sint
        from Compiler.library import check_point, runtime_error_if
        shared = execute_secret(self.field, scalar + [peer_u])[0]
        # Only a uniformly masked value is opened. A zero random mask causes
        # harmless false abort (1/p); zero ECDH is always rejected before HKDF.
        masked = shared * sint.get_random()
        check_point()
        runtime_error_if(masked.reveal(check=True) == 0, 'all-zero ECDH or zero random mask')
        secret_bytes = field_to_wire_bits(shared)
        output = self.circuit('tls-handshake-secrets', secret_bytes + hello_hash)
        return Handshake(self.traffic(output[256:512]), self.traffic(output[512:768]), output[768:1024])

    def open_handshake(self, keys, sequence, wire):
        if len(wire) % 8:
            raise ValueError('record must contain whole bytes')
        return self.circuit('tls-open-handshake-record-' + str(len(wire)//8),
                            keys.server.key + keys.server.iv + sequence + wire)

    def verify_finished(self, keys, transcript_hash, message):
        # Only this acceptance byte may be released by the controller.
        return self.circuit('tls-verify-finished', keys.server.secret + transcript_hash + message)

    def finish(self, keys, server_hash, client_hash, certificate, zero_sequence):
        from Compiler.GC.types import sbit
        output = self.circuit('tls-application-secrets', keys.main + server_hash)
        application = (self.traffic(output[:256]), self.traffic(output[256:512]))
        verify_data = self.circuit('tls-finished', keys.client.secret + client_hash)
        header = [sbit((byte >> bit) & 1) for byte in (20,0,0,32) for bit in range(7,-1,-1)]
        content = certificate + header + verify_data
        wire = self.circuit('tls-seal-record-22-' + str(len(content)//8) + '-0',
                            keys.client.key + keys.client.iv + zero_sequence + content)
        return application, wire
