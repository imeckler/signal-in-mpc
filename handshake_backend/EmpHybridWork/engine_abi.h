/* The C ABI between the Rust worker shell (node_worker/) and the two engines
 * (REORGANIZATION_PLAN.md sections 5.6, 5.7; stage S8).
 *
 * What crosses this boundary: configuration, opaque handles (64-bit numbers naming values
 * that stay inside the engines), public bits and field elements being supplied or opened, and
 * public counters. NOTHING here takes bytes to send to anyone: the engines open and use their
 * own sockets (the Boolean engine's channel on PORT and its siblings, the field engine's on
 * PORT+10); the Rust shell owns the only other sockets (the control link and the server).
 * A reviewer checks that by reading this file: no function below has a "send" parameter.
 *
 * Every function returns 0 on success and 1 on failure; after a failure ea_error_message()
 * describes it (until the next failing call on this thread). No C++ exception crosses the
 * boundary. Handles are never reused within a session; freeing a handle twice, or using one
 * that was never issued, is a failure, never another value.
 *
 * Opening rules (which handle may be opened) are the shell's (S9, node_worker/src/handles.rs);
 * the engine functions below open whatever they are given, exactly as the engines do today.
 *
 * Build: compiled once per security mode (malicious, semi-honest) by build_hybrid_v3.py
 * --engine-abi, as a static library with the field engine object. The production library's
 * field engine is built WITHOUT EMP_HYBRID_TEST_FAULTS; the "-test" library keeps it and also
 * allows the unpinned (non-strict) kernel loading used by the development fixtures.
 */
#ifndef EMP_HYBRID_ENGINE_ABI_H
#define EMP_HYBRID_ENGINE_ABI_H
#include <stddef.h>
#include <stdint.h>
#ifdef __cplusplus
extern "C" {
#endif

typedef struct ea_session ea_session;

/* Bytes allocated by the library (ea_legacy_dispatch's reply); release with ea_bytes_free. */
typedef struct ea_bytes { uint8_t *data; size_t len; } ea_bytes;

/* ---- build identity ---------------------------------------------------------------- */
/* "malicious-128" or "semi-honest" (dyn_session.h SECURITY_MODE). */
const char *ea_security_mode(void);
/* 1 in the -test library (fault hooks compiled in, unpinned kernels allowed), else 0. */
int ea_test_build(void);
/* The last failure on this thread. */
const char *ea_error_message(void);
void ea_bytes_free(ea_bytes *bytes);

/* ---- session -------------------------------------------------------------------------- */
typedef struct ea_config {
    int party;                  /* 0 (leader, listens) or 1 (dials) */
    unsigned port;              /* Boolean engine channel: party 0 listens here, party 1 dials it */
    unsigned field_port;        /* field engine (FieldEngine `port`) */
    const char *peer;           /* other worker's numeric IPv4; NULL or "" = 127.0.0.1 */
    const char *listen;         /* party 0's listen address; NULL or "" = all interfaces */
    const char *field_peer;     /* FieldEngine `peer`; NULL = local coordination exchange */
    unsigned stock_factories;   /* AND-triple factories (0: mint inside each circuit run) */
    size_t stock_batch, stock_reserve;
    unsigned field_batch, field_reserve, field_lines;
    int field_direct;           /* 0 or 1 */
    const char *challenge_domain;  /* Challenge domain, "tls-worker-v3:session=" + session hex */
} ea_config;

/* Opens the engines' links and starts both engines (interactive: both parties call it with
 * the same values, in the same order relative to their other engine calls). */
int ea_session_create(const ea_config *config, ea_session **out);
/* Stops the engines and closes their links. Accepts NULL. */
void ea_session_destroy(ea_session *session);

typedef struct ea_counters {
    uint64_t and_gates, boolean_bytes, field_bytes, field_products, stock_minted;
    double stock_seconds;
} ea_counters;
int ea_counters_read(ea_session *session, ea_counters *out);
/* The C++ measurement rows (profile.h) to stderr, each line starting with `prefix`. */
int ea_profile_report(ea_session *session, const char *prefix);

/* ---- loading: a pinned flat circuit (lean_circuit.h; the file is hashed, compared with the
 * pin and parsed from the same bytes) ------------------------------------------------------ */
int ea_circuit_load(ea_session *session, const char *path, const char *sha256_hex, uint64_t *out);
int ea_circuit_shape(ea_session *session, uint64_t circuit, uint32_t *input_bits, uint32_t *output_bits);
int ea_circuit_free(ea_session *session, uint64_t circuit);

/* ---- Boolean engine. Bits are one byte each, 0 or 1. -------------------------------- */
/* One owner's private bits (owner 0 or 1); the other party passes `count` placeholder bits. */
int ea_bool_input_private(ea_session *session, int owner, const uint8_t *bits, size_t count, uint64_t *out);
/* Both parties supply `count` bits; out_a holds party 0's, out_b party 1's. */
int ea_bool_input_both(ea_session *session, const uint8_t *bits, size_t count, uint64_t *out_a, uint64_t *out_b);
int ea_bool_public(ea_session *session, const uint8_t *bits, size_t count, uint64_t *out);
/* `copies` disjoint copies of the circuit side by side (LeanCircuit::parallel). */
int ea_bool_run(ea_session *session, uint64_t circuit, uint32_t copies, uint64_t input, uint64_t *out);
/* Opens to both parties; `count` must be the handle's width. */
int ea_bool_open(ea_session *session, uint64_t handle, uint8_t *bits, size_t count);
/* Opens to `recipient` (0 or 1) only; the other party's `bits` are all zero. */
int ea_bool_open_to(ea_session *session, uint64_t handle, int recipient, uint8_t *bits, size_t count);
int ea_bool_concat(ea_session *session, const uint64_t *handles, size_t count, uint64_t *out);
int ea_bool_pick(ea_session *session, uint64_t handle, const uint64_t *indices, size_t count, uint64_t *out);
int ea_bool_slice(ea_session *session, uint64_t handle, size_t lo, size_t hi, uint64_t *out);
int ea_bool_interleave(ea_session *session, uint64_t a, uint64_t b, uint64_t *out);
int ea_bool_width(ea_session *session, uint64_t handle, size_t *out);
int ea_bool_free(ea_session *session, uint64_t handle);

/* ---- field engine. Elements are 32 bytes little-endian, canonical (< 2^255 - 19). ---- */
/* Each party's `count` local coins; outs_a / outs_b (count each) are party 0's and 1's. */
int ea_field_input_coins(ea_session *session, const uint64_t *local, size_t count, uint64_t *outs_a, uint64_t *outs_b);
int ea_field_input_elements(ea_session *session, const uint8_t *local, size_t count, uint64_t *outs_a, uint64_t *outs_b);
int ea_field_constant(ea_session *session, uint64_t value, uint64_t *out);
int ea_field_public(ea_session *session, const uint8_t element[32], uint64_t *out);
int ea_field_add(ea_session *session, uint64_t a, uint64_t b, uint64_t *out);
int ea_field_sub(ea_session *session, uint64_t a, uint64_t b, uint64_t *out);
int ea_field_scale(ea_session *session, uint64_t a, uint64_t constant, uint64_t *out);
/* a / c for a public nonzero canonical c. */
int ea_field_divide_public(ea_session *session, uint64_t a, const uint8_t c[32], uint64_t *out);
int ea_field_mul(ea_session *session, const uint64_t *a, const uint64_t *b, size_t count, uint64_t *outs);
int ea_field_check(ea_session *session);
/* Opens `count` handles (with the MAC check) into 32*count bytes. */
int ea_field_checked_open(ea_session *session, const uint64_t *handles, size_t count, uint8_t *out);
int ea_field_free(ea_session *session, uint64_t handle);

/* ---- the legacy library (legacy_abi.cpp): today's Worker::dispatch, minus the shell, for the
 * operations not yet moved to Lean scripts (emptied S9-S16, deleted S16). ------------------ */
typedef struct ea_legacy_config {
    const char *cache_script;   /* argv[4] of the worker: circuit_cache.py (unused when pinned) */
    const char *session;        /* the full session string: agreed on every request */
    int ladder_agreement, typed_open, hinted;   /* 0 or 1 */
    int peer_wait_seconds;      /* the legacy agreement's bounded wait; 0: no limit */
    int require_pinned;         /* 1: refuse unless CIRCUIT_MANIFEST strict mode is on (always
                                   1 in the production library, whatever is passed) */
} ea_legacy_config;
/* Creates the TLS and service kernels and generates the first conversion masks (interactive). */
int ea_legacy_open(ea_session *session, const ea_legacy_config *config);
/* One worker operation that is not the shell's. Only the operations of the legacy set are
 * accepted (1-7, 12-16, 30, 32, 33, 36-38, 40-66, 80, 81); every other code fails. The reply
 * is written to `out` (release with ea_bytes_free). */
int ea_legacy_dispatch(ea_session *session, uint8_t code, uint64_t sequence, const uint8_t *payload, size_t len, ea_bytes *out);
/* Operation 90's engine half: make connection `index` the active one (parks the TLS and
 * WebSocket state of the current one). */
int ea_legacy_select(ea_session *session, uint64_t index);
/* Operation 91's engine half: the active connection's TLS and WebSocket state becomes fresh. */
int ea_legacy_reset(ea_session *session);
/* Operation 8 and every failure: drop all private TLS state and every parked connection. */
int ea_legacy_abort(ea_session *session);

#ifdef __cplusplus
}
#endif
#endif
