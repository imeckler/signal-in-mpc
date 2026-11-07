"""Differential tests of the actual circuit-building source, not MPC execution.

Independent oracles: cryptography/OpenSSL AES, Python hashlib/HMAC/HKDF,
RFC 8448 section 3 key-schedule vectors, and libsignal's chain-key fixture.
All inputs are synthetic. No connection to Signal is made.
"""

import hashlib
import unittest

from cryptography.hazmat.primitives.ciphers.aead import AESGCM

from test_support.circuit import bit_value, evaluate, opened
from test_support.reference import cbc, hkdf, mac, signal_reference
from tls_mpc import crypto, signal, tls13


class Primitives(unittest.TestCase):
    def test_private_input_bit_order_and_no_secret_branch(self):
        inputs = {'data': [bytes(range(19)), bytes(range(19, 38))]}
        shared = evaluate(inputs, lambda c, x: x['data'])
        self.assertEqual(opened(shared, 0), inputs['data'][0])
        self.assertEqual(opened(shared, 1), inputs['data'][1])
        with self.assertRaises(TypeError):
            bool(shared[0])

    def test_sha256_padding_boundaries(self):
        for length in (0, 55, 56, 63, 64, 119, 120, 137):
            data = bytes((i * 19) % 256 for i in range(length))
            with self.subTest(length=length):
                result = evaluate({'data': [data]}, lambda c, x: crypto.sha256(c, x['data']))
                self.assertEqual(opened(result), hashlib.sha256(data).digest())

    def test_hmac_long_key_and_multiblock_message(self):
        keys, messages = [b'k' * 97, b'v' * 97], [bytes(range(133)), b'm' * 133]
        result = evaluate({'key': keys, 'message': messages},
                          lambda c, x: crypto.HmacSha256(c, x['key']).digest(x['message']))
        for lane in range(2):
            self.assertEqual(opened(result, lane), mac(keys[lane], messages[lane]))

    def test_hkdf_rfc5869(self):
        ikm, salt, info = b'\x0b' * 22, bytes(range(13)), bytes(range(0xf0, 0xfa))
        result = evaluate({'ikm': [ikm], 'salt': [salt]},
                          lambda c, x: crypto.hkdf_expand(c, crypto.hkdf_extract(c, x['salt'], x['ikm']),
                                                          c.public(info), 42))
        self.assertEqual(opened(result).hex(),
                         '3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf34007208d5b887185865')

    def test_gcm_known_answer(self):
        result = evaluate({'key': [bytes(16)], 'nonce': [bytes(12)], 'text': [bytes(16)]},
                          lambda c, x: crypto.gcm_seal(c, x['key'], x['nonce'], x['text'], []))
        self.assertEqual(opened(result[0]).hex(), '0388dace60b6a392f328c2b971b2fe78')
        self.assertEqual(opened(result[1]).hex(), 'ab6e47d42cec13bdf53a67b21257bddf')

    def test_gcm_partial_blocks_and_corruption(self):
        key, nonce, aad, plaintext = bytes(range(16)), bytes(range(12)), b'header123', b'secret' * 7
        wire = AESGCM(key).encrypt(nonce, plaintext, aad)
        bad = wire[:-1] + bytes([wire[-1] ^ 1])
        inputs = {'key': [key, key], 'nonce': [nonce, nonce], 'aad': [aad, aad], 'wire': [wire, bad]}
        valid, text = evaluate(inputs, lambda c, x: crypto.gcm_open(c, x['key'], x['nonce'],
                              x['wire'][:-128], x['aad'], x['wire'][-128:]))
        self.assertEqual([bit_value(valid, i) for i in range(2)], [1, 0])
        self.assertEqual(opened(text, 0), plaintext)
        self.assertEqual(opened(text, 1), bytes(len(plaintext)))

    def test_inverse_sbox_exhaustive(self):
        values = [bytes([i]) for i in range(256)]
        result = evaluate({'byte': values},
                          lambda c, x: crypto._aes_inv_sbox(c, crypto._aes_sbox(c, x['byte'])))
        for lane in range(256):
            self.assertEqual(opened(result, lane), values[lane])

    def test_aes256_cbc_encrypt_decrypt(self):
        key, iv = bytes(range(32)), bytes(range(16))
        for length in (0, 15, 16, 17, 80):
            with self.subTest(length=length):
                plaintext = bytes(range(length))
                expected = cbc(key, iv, plaintext)
                result = evaluate({'key': [key], 'iv': [iv], 'text': [plaintext], 'cipher': [expected]},
                                  lambda c, x: (crypto.cbc_seal(c, x['key'], x['iv'], x['text']),
                                                crypto.cbc_open(c, x['key'], x['iv'], x['cipher'])))
                sealed, (valid, text, size) = result
                self.assertEqual(opened(sealed), expected)
                self.assertEqual(bit_value(valid), 1)
                self.assertEqual(int.from_bytes(opened(size)), length)
                self.assertEqual(opened(text), plaintext + bytes(len(expected) - length))

    def test_cbc_bad_padding_is_masked(self):
        key, iv = bytes(32), bytes(16)
        malformed = [b'x' * 15 + b'\x00', b'x' * 14 + b'\x03\x02', b'\x11' * 16]
        result = evaluate({'key': [key] * 3, 'iv': [iv] * 3,
                           'wire': [cbc(key, iv, x, pad=False) for x in malformed]},
                          lambda c, x: crypto.cbc_open(c, x['key'], x['iv'], x['wire']))
        for lane in range(3):
            self.assertEqual(bit_value(result[0], lane), 0)
            self.assertEqual(opened(result[1], lane), bytes(16))
            self.assertEqual(opened(result[2], lane), bytes(2))


class Tls13(unittest.TestCase):
    def test_rfc8448_application_and_finished(self):
        master = bytes.fromhex('18df06843d13a08bf2a449844c5f8a478001bc4d4c627984d5a41da8d0402919')
        transcript = bytes.fromhex('9608102a0f1ccc6db6250b7b7e417b1a000eaada3daae4777a7686c9ff83df13')
        client_hs = bytes.fromhex('b3eddb126e067f35a780b3abf45e2d8f3b1a950738f52e9600746a0e27a55a21')
        def run(c, x):
            client, server = tls13.application_secrets(c, x['master'], x['hash'])
            return client, server, tls13.finished_verify_data(c, x['hs'], x['hash']), tls13.next_traffic_secret(c, client)
        client, server, finished, updated = evaluate({'master': [master], 'hash': [transcript], 'hs': [client_hs]}, run)
        self.assertEqual(opened(client).hex(), '9e40646ce79a7f9dc05af8889bce6552875afa0b06df0087f792ebb7c17504a5')
        self.assertEqual(opened(server).hex(), 'a11af9f05531f856ad47116b45a950328204b4f44bfb6b3a4b4f1f3fcb631643')
        self.assertEqual(opened(finished).hex(), 'a8ec436d677634ae525ac1fcebe11a039ec17694fac6e98527b642f2edd5ce61')
        label = b'tls13 traffic upd'
        expected_update = mac(opened(client), b'\x00\x20' + bytes([len(label)]) + label + b'\x00\x01')
        self.assertEqual(opened(updated), expected_update)

    def test_rfc8448_complete_finished_record(self):
        key = bytes.fromhex('dbfaa693d1762c5b666af5d950258d01')
        iv = bytes.fromhex('5bd3c71b836e0b76bb73265f')
        message = bytes.fromhex('14000020a8ec436d677634ae525ac1fcebe11a039ec17694fac6e98527b642f2edd5ce61')
        expected = bytes.fromhex('170303003575ec4dc238cce60b298044a71e219c56cc77b0517fe9b93c7a4bfc44d87f38f80338ac98fc46deb384bd1caeacab6867d726c40546')
        record = evaluate({'key': [key], 'iv': [iv], 'message': [message]},
                          lambda c, x: tls13.seal_record(c, x['key'], x['iv'], 0, x['message'], content_type=22))
        self.assertEqual(record.header + opened(record.encrypted), expected)

    def test_rfc8448_handshake_keys(self):
        # https://www.rfc-editor.org/rfc/rfc8448.html#section-3
        dhe = bytes.fromhex('8bd4054fb55b9d63fdfbacf9f04b9f0d35e6d63f537563efd46272900f89492d')
        transcript = bytes.fromhex('860c06edc07858ee8e78f0e7428c58edd6b43f2ca3e6e95f02ed063cf0e1cad8')
        def run(c, x):
            secrets = tls13.handshake_secrets(c, x['dhe'], x['hash'])
            return secrets, tls13.traffic_keys(c, secrets.server)
        secrets, (key, iv) = evaluate({'dhe': [dhe], 'hash': [transcript]}, run)
        self.assertEqual(opened(secrets.client).hex(), 'b3eddb126e067f35a780b3abf45e2d8f3b1a950738f52e9600746a0e27a55a21')
        self.assertEqual(opened(secrets.server).hex(), 'b67b7d690cc16c4e75e54213cb2d37b4e9c912bcded9105d42befd59d391ad38')
        self.assertEqual(opened(secrets.master).hex(), '18df06843d13a08bf2a449844c5f8a478001bc4d4c627984d5a41da8d0402919')
        self.assertEqual(opened(key).hex(), '3fce516009c21727d0f2e4e86ee403bc')
        self.assertEqual(opened(iv).hex(), '5d313eb2671276ee13000b30')

    def test_records_match_aesgcm_across_lanes(self):
        keys, ivs, messages = [bytes(range(16)), b'k' * 16], [bytes(range(12)), b'i' * 12], [b'hello', b'world']
        sequence, padding = 0x0102030405060708, 3
        def run(c, x):
            sealed = tls13.seal_record(c, x['key'], x['iv'], sequence, x['text'], padding=padding)
            return sealed, tls13.open_record(c, x['key'], x['iv'], sequence, sealed.header, sealed.encrypted)
        sealed, result = evaluate({'key': keys, 'iv': ivs, 'text': messages}, run)
        for lane in range(2):
            nonce = bytes(a ^ b for a, b in zip(ivs[lane], bytes(4) + sequence.to_bytes(8, 'big')))
            expected = AESGCM(keys[lane]).encrypt(nonce, messages[lane] + b'\x17' + bytes(padding), sealed.header)
            self.assertEqual(opened(sealed.encrypted, lane), expected)
            self.assertEqual(bit_value(result.valid, lane), 1)
            self.assertEqual(opened(result.content, lane), messages[lane] + bytes(padding + 1))
            self.assertEqual(opened(result.content_length, lane), b'\x00\x05')
            self.assertEqual(opened(result.content_type, lane), b'\x17')

    def test_inner_type_and_tag_fail_closed(self):
        key, iv = bytes(16), bytes(12)
        inners = [b'\x00\x00\x00', b'a\x19\x00', b'\x16\x00\x00', b'\x17\x00\x00', b'a\x17\x00']
        header = b'\x17\x03\x03\x00\x13'
        wires = [AESGCM(key).encrypt(iv, inner, header) for inner in inners]
        wires[-1] = wires[-1][:-1] + bytes([wires[-1][-1] ^ 1])
        result = evaluate({'key': [key] * 5, 'iv': [iv] * 5, 'wire': wires},
                          lambda c, x: tls13.open_record(c, x['key'], x['iv'], 0, header, x['wire']))
        for lane, valid in enumerate((0, 0, 0, 1, 0)):
            self.assertEqual(bit_value(result.valid, lane), valid)
            self.assertEqual(opened(result.content, lane), bytes(3))
            self.assertEqual(opened(result.content_length, lane), bytes(2))
            self.assertEqual(opened(result.content_type, lane), b'\x17' if valid else b'\x00')

    def test_public_record_limits(self):
        for sequence in (-1, 1 << 64):
            with self.assertRaises(ValueError):
                evaluate({}, lambda c, x: tls13.record_nonce(c, c.public(bytes(12)), sequence))
        with self.assertRaises(ValueError):
            evaluate({}, lambda c, x: tls13.seal_record(c, c.public(bytes(16)), c.public(bytes(12)),
                                                       0, c.public(bytes(16385))))
        with self.assertRaises(ValueError):
            evaluate({}, lambda c, x: tls13.open_record(c, c.public(bytes(16)), c.public(bytes(12)),
                                                       0, b'\x17\x03\x03\x00\x12', c.public(bytes(17))))


class Signal(unittest.TestCase):
    chain = bytes.fromhex('8ab72d6f4cc5ac0d387eaf463378ddb28edd07385b1cb01250c715982e7ad48f')
    ratchet, sender, recipient = [b'\x05' + bytes([i]) * 32 for i in (2, 3, 4)]
    addresses = b'\x00' + b'a' * 16 + b'\x01' + b'\x00' + b'b' * 16 + b'\x02'

    def test_upstream_chain_key_fixture(self):
        keys = evaluate({'chain': [self.chain]}, lambda c, x: signal.chain_step(c, x['chain'], pq_key=None))
        self.assertEqual(opened(keys.cipher).hex(), 'bf51e9d75e0e31031051f82a2491ffc084fa298b7793bd9db620056febf45217')
        self.assertEqual(opened(keys.mac).hex(), 'c6c77d6a73a354337a56435e34607dfe48e3ace14e77314dc6abc172e7a7030b')
        self.assertEqual(opened(keys.next_chain).hex(), '28e8f8fee54b801eef7c5cfb2f17f32c7b334485bbb70fac6ec10342a246d15d')

    def test_send_current_wire_format_with_shared_addresses_and_pq_input(self):
        plaintext, pq_key, pq_message = b'message' * 19, b'p' * 32, b'opaque SPQR bytes'
        inputs = {'chain': [self.chain], 'text': [plaintext], 'pq_key': [pq_key], 'pq': [pq_message],
                  'addresses': [self.addresses], 'ratchet': [self.ratchet], 'sender': [self.sender], 'recipient': [self.recipient]}
        result = evaluate(inputs, lambda c, x: signal.seal_message(
            c, x['chain'], x['text'], counter=128, previous_counter=16384, ratchet_key=x['ratchet'],
            sender_identity=x['sender'], receiver_identity=x['recipient'],
            pq=signal.PqStep(x['pq_key'], x['pq']), addresses=x['addresses']))
        expected = signal_reference(self.chain, plaintext, pq_key, pq_message, self.addresses,
                                    self.ratchet, self.sender, self.recipient, 128, 16384)
        self.assertEqual(opened(result.wire), expected)
        self.assertEqual(opened(result.next_chain), mac(self.chain, b'\x02'))
        self.assertEqual(result.next_counter, 129)

    def test_receive_authentication_padding_and_state(self):
        text = b'secret plaintext'
        good = signal_reference(self.chain, text, None, b'', self.addresses, self.ratchet, self.sender, self.recipient)
        bad_mac = good[:-1] + bytes([good[-1] ^ 1])
        bad_pad = signal_reference(self.chain, b'', None, b'', self.addresses, self.ratchet, self.sender,
                                   self.recipient, raw_padded=b'p' * 31 + b'\x00')
        wrong_address = signal_reference(self.chain, text, None, b'', bytes(36), self.ratchet, self.sender, self.recipient)
        wrong_counter = signal_reference(self.chain, text, None, b'', self.addresses, self.ratchet,
                                         self.sender, self.recipient, counter=1)
        wires = [good, bad_mac, bad_pad, wrong_address, wrong_counter]
        inputs = {name: [value] * 5 for name, value in [('chain', self.chain), ('ratchet', self.ratchet),
                  ('sender', self.sender), ('recipient', self.recipient), ('addresses', self.addresses)]}
        inputs['wire'] = wires
        result = evaluate(inputs, lambda c, x: signal.open_message(
            c, x['chain'], x['wire'], shape=signal.MessageShape(0, 0, 32, 0, True),
            expected_ratchet_key=x['ratchet'], sender_identity=x['sender'], receiver_identity=x['recipient'],
            pq_key=None, expected_addresses=x['addresses']))
        for lane in range(5):
            self.assertEqual(bit_value(result.valid, lane), int(lane == 0))
            self.assertEqual(opened(result.content, lane), text + bytes(16) if lane == 0 else bytes(32))
            self.assertEqual(int.from_bytes(opened(result.content_length, lane)), len(text) if lane == 0 else 0)
            self.assertEqual(opened(result.next_chain, lane), mac(self.chain, b'\x02') if lane == 0 else self.chain)

    def test_application_padding(self):
        for size in (0, 79, 80):
            result = evaluate({'text': [b'x' * size]}, lambda c, x: signal.pad_content(c, x['text']))
            expected = b'x' * size + b'\x80' + bytes((-size - 1) % 80)
            self.assertEqual(opened(result), expected)


if __name__ == '__main__':
    unittest.main()
