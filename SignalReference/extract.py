#!/usr/bin/env python3
"""Orchestrate real upstream extraction; this contains no Signal implementation."""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
PINS = json.loads((HERE / "pins.json").read_text())

PROFILES = {
    "key_accessors": {
        "package": "libsignal-protocol",
        "starts": [f"crate::ratchet::keys::*::{name}" for name in
                   ("new", "key", "index", "cipher_key", "mac_key", "iv", "counter")],
        "extra": [], "subdir": "KeyAccessors", "namespace": "LibSignalReference",
        "expected_functions": 9,
    },
    "clamp": {
        "package": "curve25519-dalek@5.0.0",
        "starts": ["crate::scalar::clamp_integer"],
        "extra": [], "subdir": "Clamp", "namespace": "LibSignalClamp",
        "expected_functions": 1,
    },
    "aes256_key_schedule": {
        "package": "aes@0.9.1",
        "starts": ["crate::soft::fixslice::aes256_key_schedule"],
        "extra": ["--no-dedup-serialized-ast"],
        "subdir": "Aes256KeySchedule", "namespace": "RustCryptoAesKeySchedule",
        "rustflags": '--cfg aes_backend="soft"',
    },
    "sha256_compact": {
        "package": "sha2@0.11.0",
        "starts": ["crate::sha256::soft::compact::compress_u32"],
        "extra": [], "subdir": "Sha256Compact", "namespace": "RustCryptoSha256",
        "rustflags": '--cfg sha2_256_backend="soft" --cfg sha2_backend_soft="compact"',
    },
    "sha256_to_words": {
        "package": "sha2@0.11.0",
        "starts": ["crate::sha256::soft::to_u32s"],
        "extra": ["--no-dedup-serialized-ast"], "subdir": "Sha256ToWords", "namespace": "RustCryptoSha256ToWords",
        "rustflags": '--cfg sha2_256_backend="soft" --cfg sha2_backend_soft="compact"',
    },
    "sha256_word_closure": {
        "package": "sha2@0.11.0",
        "starts": ["crate::sha256::soft::to_u32s::*::call_mut"],
        "extra": [], "subdir": "Sha256WordClosure", "namespace": "RustCryptoSha256WordClosure",
        "rustflags": '--cfg sha2_256_backend="soft" --cfg sha2_backend_soft="compact"',
    },
    "sha256_to_words_bodies": {
        "package": "sha2@0.11.0",
        "starts": ["crate::sha256::soft::to_u32s"],
        "extra": ["--include=core::array::from_fn", "--include=core::array::try_from_fn",
                  "--include=core::array::try_from_fn_erased"],
        "subdir": "Sha256ToWordsBodies", "namespace": "RustCryptoSha256ToWordsBodies",
        "rustflags": '--cfg sha2_256_backend="soft" --cfg sha2_backend_soft="compact"',
        "miri_sysroot": "PaddingWork/Unpad/Sysroot",
    },
    "sha256_compact_mono": {
        "package": "sha2@0.11.0",
        "starts": ["crate::sha256::soft::compact::compress_u32"],
        "extra": ["--monomorphize"], "subdir": "Sha256CompactMono", "namespace": "RustCryptoSha256",
        "rustflags": '--cfg sha2_256_backend="soft" --cfg sha2_backend_soft="compact"',
    },
    "sha256_compact_bodies": {
        "package": "sha2@0.11.0",
        "starts": ["crate::sha256::soft::compact::compress_u32"],
        "extra": ["--monomorphize", "--extract-opaque-bodies"],
        "subdir": "Sha256CompactBodies", "namespace": "RustCryptoSha256",
        "rustflags": '--cfg sha2_256_backend="soft" --cfg sha2_backend_soft="compact"',
    },
    "sha256_compact_bodies_scoped": {
        "package": "sha2@0.11.0",
        "starts": ["crate::sha256::soft::compact::compress_u32"],
        "extra": ["--monomorphize", "--extract-opaque-bodies", "--exclude=core::array"],
        "subdir": "Sha256CompactBodiesScoped", "namespace": "RustCryptoSha256",
        "rustflags": '--cfg sha2_256_backend="soft" --cfg sha2_backend_soft="compact"',
    },
    "sha256_compact_scoped": {
        "package": "sha2@0.11.0",
        "starts": ["crate::sha256::soft::compact::compress_u32"],
        "extra": ["--exclude=core::iter::range::Step::forward_overflowing",
                  "--exclude=core::iter::range::Step::backward_overflowing"],
        "subdir": "Sha256CompactScoped", "namespace": "RustCryptoSha256",
        "rustflags": '--cfg sha2_256_backend="soft" --cfg sha2_backend_soft="compact"',
    },
    "sha256_compact_full_mir_mono": {
        "package": "sha2@0.11.0",
        "starts": ["crate::sha256::soft::compact::compress_u32"],
        "extra": ["--monomorphize",
                  "--include=core::iter::traits::collect::*::into_iter",
                  "--include=core::iter::range::*::next",
                  "--include=core::iter::range::*::spec_next"],
        "subdir": "Sha256CompactFullMirMono", "namespace": "RustCryptoSha256",
        "rustflags": '--cfg sha2_256_backend="soft" --cfg sha2_backend_soft="compact"',
        "miri_sysroot": "PaddingWork/Unpad/Sysroot",
    },
    "message_type": {
        "package": "libsignal-protocol",
        "starts": ["{core::convert::TryFrom for crate::protocol::CiphertextMessageType}::try_from"],
        "extra": ["--include=derive_more", "--start-from-if-exists=crate::protocol::*::try_from"],
        "subdir": "MessageType", "namespace": "LibSignalMessageType",
        "expected_functions": 6,
    },
    "pkcs7_pad": {
        "package": "block-padding@0.4.2",
        "starts": ["{crate::Padding for crate::Pkcs7}::raw_pad"],
        "extra": ["--start-from-if-exists=crate::*::raw_pad"],
        "subdir": "Pkcs7Pad", "namespace": "RustCryptoPkcs7",
    },
    "pkcs7_pad_scoped": {
        "package": "block-padding@0.4.2",
        "starts": ["{crate::Padding for crate::Pkcs7}::raw_pad"],
        "extra": ["--start-from-if-exists=crate::*::raw_pad",
                  "--exclude=crate::Padding::pad", "--exclude=crate::Padding::unpad",
                  "--exclude=crate::Padding::pad_detached", "--exclude=crate::Padding::unpad_blocks",
                  "--exclude=crate::*::raw_unpad", "--exclude=crate::*::unpad"],
        "subdir": "Pkcs7PadScoped", "namespace": "RustCryptoPkcs7",
    },
    "pkcs7_pad_selected": {
        "package": "block-padding@0.4.2",
        "starts": ["{crate::Padding for crate::Pkcs7}::raw_pad"],
        "extra": ["--start-from-if-exists=crate::*::raw_pad",
                  "--exclude=crate::Padding::pad", "--exclude=crate::Padding::unpad",
                  "--exclude=crate::Padding::pad_detached", "--exclude=crate::Padding::unpad_blocks",
                  "--exclude=crate::*::raw_unpad", "--exclude=crate::*::unpad",
                  "--exclude=hybrid_array::traits::ArraySize"],
        "subdir": "Padding", "namespace": "RustCryptoPadding",
        "expected_functions": 13, "expected_generated_functions": 1,
        "modeled_std_functions": [
            "core::slice::{impl}::len", "core::fmt::{impl}::from_str",
            "core::slice::index::{impl}::index_mut", "core::slice::{impl}::fill",
            "core::slice::index::{impl}::get", "core::slice::index::{impl}::get_mut",
            "core::slice::index::{impl}::get_unchecked",
            "core::slice::index::{impl}::get_unchecked_mut",
            "core::slice::index::{impl}::index", "core::slice::index::{impl}::index_mut",
            "core::clone::impls::{impl}::clone", "core::slice::index::{impl}::index",
        ],
        "discarded_metadata_types": ["core::fmt::Arguments"],
        "discarded_metadata_functions": ["core::fmt::{impl}::from_str"],
    },
    "service_id_encode": {
        "package": "libsignal-core",
        "starts": ["crate::address::*::service_id_fixed_width_binary",
                   "{core::convert::TryFrom for crate::address::ServiceIdKind}::try_from"],
        "extra": ["--include=uuid", "--include=derive_more",
                  "--start-from-if-exists=crate::address::*::try_from"],
        "subdir": "ServiceIdEncode", "namespace": "LibSignalServiceId",
        "expected_functions": 24, "expected_generated_functions": 13,
        "modeled_std_functions": [
            "core::convert::{impl}::into", "core::array::{impl}::index_mut",
            "core::slice::{impl}::copy_from_slice", "core::slice::index::{impl}::index_mut",
            "core::slice::index::{impl}::get", "core::slice::index::{impl}::get_mut",
            "core::slice::index::{impl}::get_unchecked", "core::slice::index::{impl}::get_unchecked_mut",
            "core::slice::index::{impl}::index", "core::slice::index::{impl}::index_mut",
            "core::array::{impl}::index", "core::slice::index::{impl}::index",
            "core::clone::impls::{impl}::clone",
        ],
    },
    "service_id_decode": {
        "package": "libsignal-core",
        "starts": ["crate::address::*::parse_from_service_id_fixed_width_binary"],
        "extra": ["--include=uuid", "--include=derive_more",
                  "--include=core::option::*::branch",
                  "--include=core::option::*::from_residual",
                  "--include=core::result::*::ok"],
        "subdir": "ServiceIdDecode", "namespace": "LibSignalServiceIdDecode",
    },
    "service_id_decode_mono": {
        "package": "libsignal-core",
        "starts": ["crate::address::*::parse_from_service_id_fixed_width_binary"],
        "extra": ["--include=uuid", "--include=derive_more", "--monomorphize",
                  "--include=core::option::*::branch",
                  "--include=core::option::*::from_residual",
                  "--include=core::result::*::ok"],
        "subdir": "ServiceIdDecodeMono", "namespace": "LibSignalServiceIdDecode",
    },
    "service_id_decode_full_mir": {
        "package": "libsignal-core",
        "starts": ["crate::address::*::parse_from_service_id_fixed_width_binary"],
        "extra": ["--include=uuid", "--include=derive_more",
                  "--include=core::option::*::branch",
                  "--include=core::option::*::from_residual",
                  "--include=core::result::*::ok"],
        "subdir": "ServiceIdDecodeFullMir", "namespace": "LibSignalServiceIdDecode",
        "miri_sysroot": "../.deps/full-mir-std-2026-08-18/Sysroot",
        "target_cache": ".deps/libsignal-charon-full-mir-std-target",
    },
    "service_id_kind": {
        "package": "libsignal-core",
        "starts": ["{core::convert::TryFrom for crate::address::ServiceIdKind}::try_from"],
        "extra": ["--include=derive_more",
                  "--start-from-if-exists=crate::address::*::try_from"],
        "subdir": "ServiceIdKind", "namespace": "LibSignalServiceIdKind",
    },
    "sha256_round": {
        "package": "sha2@0.11.0",
        "starts": ["crate::sha256::wasm32_simd128::sha_round"],
        "extra": [], "subdir": "Sha256Round", "namespace": "RustCryptoSha256Round",
        "rustflags": "-C target-feature=+simd128", "target": "wasm32-wasip1",
        "expected_functions": 3, "expected_generated_functions": 1,
        "modeled_std_functions": ["core::num::{impl}::wrapping_add", "core::num::{impl}::rotate_right"],
    },
    "aes_sub_bytes": {
        "package": "aes@0.9.1",
        "starts": ["crate::soft::fixslice::sub_bytes", "crate::soft::fixslice::sub_bytes_nots"],
        "extra": [], "subdir": "AesSubBytes", "namespace": "RustCryptoAesSubBytes",
        "rustflags": '--cfg aes_backend="soft"',
        "expected_functions": 3, "expected_generated_functions": 2,
        "modeled_std_functions": ["core::slice::{impl}::len"],
        "discarded_metadata_types": ["core::fmt::Arguments"],
        "scope_note": "Actual portable64-bit software S-box with debug-assertions from the selected Cargo dev build; sub_bytes_nots restores the four NOTs moved into the real key schedule. Full cipher composition is separate.",
    },
    "symmetric_keys": {
        "package": "libsignal-protocol",
        "starts": [f"crate::ratchet::keys::*::{name}" for name in
                   ("next_chain_key", "message_keys", "derive_keys", "generate_keys")],
        "extra": [], "subdir": "SymmetricKeys", "namespace": "SignalSymmetricKeys",
    },
    "symmetric_keys_mono": {
        "package": "libsignal-protocol",
        "starts": [f"crate::ratchet::keys::*::{name}" for name in
                   ("next_chain_key", "message_keys", "derive_keys", "generate_keys")],
        "extra": ["--monomorphize", "--extract-opaque-bodies"],
        "subdir": "SymmetricKeysMono", "namespace": "SignalSymmetricKeysMono",
    },
}
PROFILES["sha256_compact_reviewed"] = json.loads((HERE / "Extraction/sha-compact-profile.json").read_text())
PROFILES["aes_layout"] = json.loads((HERE / "Extraction/aes-layout-profile.json").read_text())
for name in ("aes_mix_columns_0", "aes_shift_rows", "aes_mix_phases", "aes_inverse_write"):
    PROFILES[name] = json.loads((HERE / "Extraction" / f"{name}-profile.json").read_text())
PROFILES["pkcs7_unpad_selected"] = json.loads((HERE / "Extraction/unpad-profile.json").read_text())
PROFILES["sha256_compact_full_mir_complete"] = {
    **PROFILES["sha256_compact_full_mir_mono"],
    "extra": [*PROFILES["sha256_compact_full_mir_mono"]["extra"],
              "--include=core::iter::range::*::forward_unchecked",
              "--include=core::num::*::unchecked_add"],
    "subdir": "Sha256CompactFullMirComplete",
}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_sources() -> Path:
    source = (HERE / PINS["libsignal"]["source_directory"]).resolve()
    for name, expected in PINS["libsignal"]["files"].items():
        actual = digest(source / name)
        if actual != expected:
            raise ValueError(f"pinned libsignal source differs: {name}: {actual}")
    for dependency, pin in PINS["signal_dependencies"].items():
        for name, expected in pin["files"].items():
            actual = digest((HERE / pin["source_directory"]).resolve() / name)
            if actual != expected:
                raise ValueError(f"pinned dependency differs: {dependency}/{name}: {actual}")
    return source


def check_full_mir(profile: dict) -> None:
    if "full_mir_manifest" not in profile:
        return
    path = HERE / profile["full_mir_manifest"]
    if digest(path) != profile["full_mir_manifest_sha256"]:
        raise ValueError("full-MIR provenance manifest differs from reviewed profile")
    data = json.loads(path.read_text())
    for name, expected in data["sysroot_source_files_sha256"].items():
        if digest(ROOT / data["source_directory"] / name) != expected:
            raise ValueError(f"full-MIR Rust source differs: {name}")
    for name, expected in data["sysroot_artifact_sha256"].items():
        if digest(ROOT / data["sysroot_directory"] / name) != expected:
            raise ValueError(f"full-MIR artifact differs: {name}")
    for name in ("miri", "rust_source"):
        if digest(ROOT / data[name + "_archive"]) != data[name + "_archive_sha256"]:
            raise ValueError(f"official full-MIR archive differs: {name}")


def check_discarded_metadata(profile: dict, generated: Path) -> None:
    definitions = profile.get("expected_generated_definitions")
    if definitions is not None and re.findall(r"^def ([^\s]+)", (generated / "Funs.lean").read_text(), re.M) != definitions:
        raise ValueError("generated function inventory differs")
    if not profile.get("discarded_metadata_types"):
        return
    text = "\n".join(path.read_text() for path in generated.glob("*.lean"))
    type_names = re.findall(r"^\s*(?:opaque|structure|inductive|def)\s+([^\s:=]+)",
                            (generated / "Types.lean").read_text(), re.M)
    if type_names != profile.get("expected_generated_types", []) or any(
            name in text for name in profile.get("forbidden_generated_namespaces", ["core.fmt"])):
        raise ValueError("discarded metadata remains computationally relevant")


def check_body_dependencies(profile: dict, llbc: Path) -> None:
    expected = profile.get("expected_body_regular_function_ids")
    if expected is None:
        return
    def references(value):
        if isinstance(value, dict):
            if type(value.get("Regular")) is int:
                yield value["Regular"]
            for child in value.values():
                yield from references(child)
        elif isinstance(value, list):
            for child in value:
                yield from references(child)
    translated = json.loads(llbc.read_text())["translated"]
    actual = sorted(set(ref for fn in translated["fun_decls"] if fn
                        for ref in references(fn.get("body"))))
    if actual != expected or any(translated["global_decls"]):
        raise ValueError("selected body function dependencies differ")


def name_of(meta: dict) -> str:
    return "::".join(element["Ident"][0] if "Ident" in element else "{impl}"
                     for element in meta["name"])


def body_kind(body: str | dict) -> str:
    return next(iter(body)) if isinstance(body, dict) else body


def inventory(path: Path) -> dict:
    data = json.loads(path.read_text())
    translated = data["translated"]
    options = translated["options"]
    functions = [fn for fn in translated["fun_decls"] if fn is not None]
    external = []
    for fn in functions:
        kind = body_kind(fn["body"])
        if kind != "Structured":
            external.append({"id": fn["def_id"], "name": name_of(fn["item_meta"]),
                             "body_kind": kind, "span": fn["item_meta"]["span"]})
    external_types = [{"id": decl["def_id"], "name": name_of(decl["item_meta"]),
                       "kind": body_kind(decl["kind"]), "span": decl["item_meta"]["span"]}
                      for decl in translated["type_decls"] if decl is not None
                      and body_kind(decl["kind"]) not in ("Struct", "Enum")]
    return {
        "llbc_sha256": digest(path),
        "charon_version": data["charon_version"],
        "has_errors": data["has_errors"],
        "counts": {key: len([x for x in translated[key] if x is not None]) for key in
                   ("type_decls", "fun_decls", "global_decls", "trait_decls", "trait_impls", "ordered_decls")},
        "body_kinds": dict(Counter(body_kind(fn["body"]) for fn in functions)),
        "external_functions": external,
        "external_or_union_types": external_types,
        "source_files": [{"id": file["id"], "name": file["name"],
                          "crate_name": file["crate_name"]}
                         for file in translated["files"]],
        "explicit_exclusions": translated["options"]["exclude"],
        "explicit_opaque_patterns": translated["options"]["opaque"],
        "preset_hidden_traits": (["core::marker::Sized", "core::marker::MetaSized",
                                  "core::marker::PointeeSized", "core::marker::Tuple",
                                  "core::clone::TrivialClone"] if options["hide_marker_traits"] else [])
            + (["core::alloc::Allocator"] if options["hide_allocator"] else []),
        "translation_options": {key: options[key] for key in
                                ("preset", "sysroot", "monomorphize", "monomorphize_mut",
                                 "extract_opaque_bodies", "precise_drops", "desugar_drops",
                                 "skip_borrowck", "no_typecheck", "lift_associated_types")},
        "entry_patterns": translated["options"]["start_from"],
        "selected_functions": [{"id": fn["def_id"], "name": name_of(fn["item_meta"]),
                                "body_kind": body_kind(fn["body"]),
                                "span": fn["item_meta"]["span"]} for fn in functions],
        "proof_status": "not established by extraction; run the Lean proof checks",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("profile", choices=PROFILES)
    parser.add_argument("--inventory-only", action="store_true")
    parser.add_argument("--charon-only", action="store_true", help="Write checked actual LLBC without invoking Aeneas")
    args = parser.parse_args()
    profile = PROFILES[args.profile]
    if args.profile == "aes_inverse_write" and not args.inventory_only:
        subprocess.run([sys.executable, str(HERE / "AesInverseLayoutWork/extract_inverse.py"),
                        "InvBitsliceScoped", "--charon-only"], check=True)
        return subprocess.run([sys.executable, str(HERE / profile["trusted_declaration_selection"]),
                               "--canonical"], check=False).returncode
    if args.profile == "sha256_compact_reviewed" and not args.inventory_only:
        subprocess.run([sys.executable, str(Path(__file__).resolve()), "sha256_compact", "--charon-only"], check=True)
        return subprocess.run([sys.executable, str(HERE / "MetadataWork/trim_step_metadata.py"), "--canonical"], check=False).returncode
    check_full_mir(profile)
    source = check_sources()
    output = HERE / "Extraction" / f"libsignal_{args.profile}.llbc"
    report = HERE / "Extraction" / f"{args.profile}.json"
    logs = HERE / "Extraction/logs"
    logs.mkdir(parents=True, exist_ok=True)
    if args.inventory_only:
        report.write_text(json.dumps(inventory(output), indent=2) + "\n")
        print(report.relative_to(ROOT))
        return 0

    rust = ROOT / ".deps/rust-nightly-2026-08-18"
    charon = (HERE / PINS["charon"]["directory"] / "target/release/charon").resolve()
    aeneas = (HERE / PINS["aeneas"]["directory"] / "aeneas").resolve()
    version = subprocess.check_output([str(charon), "version"], text=True).strip()
    if PINS["charon"]["commit"] not in version:
        raise ValueError(f"wrong Charon revision: {version}")
    version = subprocess.check_output([str(aeneas), "-version"], text=True).strip()
    if PINS["aeneas"]["release"] not in version:
        raise ValueError(f"wrong Aeneas revision: {version}")
    version = subprocess.check_output([str(rust / "bin/rustc"), "--version"], text=True).strip()
    if version != PINS["charon"]["rustc_version"]:
        raise ValueError(f"wrong Rust compiler: {version}")

    env = os.environ.copy()
    env.update({"PATH": str(rust / "bin") + os.pathsep + env.get("PATH", ""),
                "CHARON_TOOLCHAIN_IS_IN_PATH": "1",
                "DYLD_LIBRARY_PATH": str(rust / "lib"),
                "LD_LIBRARY_PATH": str(rust / "lib"),
                "CARGO_HOME": str(ROOT / ".deps/libsignal-cargo-home"),
                "CARGO_TARGET_DIR": str(ROOT / ".deps/libsignal-charon-target")})
    if "rustflags" in profile:
        env["RUSTFLAGS"] = profile["rustflags"]
    if "miri_sysroot" in profile:
        sysroot = (HERE / profile["miri_sysroot"]).resolve()
        if not (sysroot / "lib/rustlib/aarch64-apple-darwin").is_dir():
            raise ValueError("the selected full-MIR sysroot has not been built")
        env["CHARON_MIRI_SYSROOTS"] = str(sysroot)
        env["CARGO_TARGET_DIR"] = str(ROOT / profile.get("target_cache", ".deps/libsignal-charon-full-mir-target"))
    if "@" in profile["package"]:
        # Cargo's workspace-wrapper fingerprint does not invalidate registry
        # dependencies. Clean only this disposable dependency build before
        # selecting it as the extraction's primary package.
        subprocess.run([str(rust / "bin/cargo"), "clean", "--package",
                        profile["package"], "--target", profile.get("target", "aarch64-apple-darwin")],
                       cwd=source, env=env, check=True, stdout=subprocess.DEVNULL)
    command = [str(charon), "cargo", "--preset=aeneas",
               "--sysroot=" + ("miri" if "miri_sysroot" in profile else "default"),
               "--error-on-warnings", "--start-from=" + ",".join(profile["starts"]),
               *profile["extra"], "--dest-file=" + str(output), "--",
               "--package", profile["package"], "--lib", "--locked", "--offline",
               *(["--target", profile["target"]] if "target" in profile else [])]
    # Removing only our previous generated artifact prevents accepting stale output.
    output.unlink(missing_ok=True)
    with (logs / f"{args.profile}-charon.log").open("w") as log:
        result = subprocess.run(command, cwd=source, env=env, stdout=log, stderr=subprocess.STDOUT)
    if not output.exists():
        raise RuntimeError(f"Charon failed ({result.returncode}); see {logs}")
    audit = inventory(output)
    audit["charon_command"] = [str(x).replace(str(ROOT), "$WORKSPACE") for x in command]
    audit["rustflags"] = env.get("RUSTFLAGS", "")
    audit["target"] = profile.get("target", "aarch64-apple-darwin")
    audit["charon_exit_code"] = result.returncode
    if "miri_sysroot" in profile:
        audit["full_mir_sysroot"] = profile["miri_sysroot"]
    if "scope_note" in profile:
        audit["scope_note"] = profile["scope_note"]
    report.write_text(json.dumps(audit, indent=2) + "\n")
    if result.returncode or audit["has_errors"] or not audit["counts"]["ordered_decls"]:
        raise RuntimeError(f"incomplete Charon extraction; see {report}")
    complete_profile = "expected_functions" in profile
    modeled = profile.get("modeled_std_functions", [])
    audit["modeled_std_functions"] = modeled
    discarded = profile.get("discarded_metadata_types", [])
    audit["discarded_metadata_types"] = discarded
    audit["discarded_metadata_functions"] = profile.get("discarded_metadata_functions", [])
    if complete_profile and (sorted(fn["name"] for fn in audit["external_functions"]) != sorted(modeled) or
                             sorted(ty["name"] for ty in audit["external_or_union_types"]) !=
                                sorted(discarded + profile.get("modeled_std_types", [])) or
                             audit["counts"]["fun_decls"] != profile["expected_functions"]):
        raise RuntimeError(f"unexpected or opaque functions; see {report}")

    if args.charon_only:
        print(f"{args.profile}: checked actual Charon LLBC; Aeneas was not requested")
        return 0

    destination = HERE if complete_profile else HERE / "Extraction/Incomplete"
    subdir = "/LibSignalReference/Generated/" + profile["subdir"] if complete_profile else "/" + profile["subdir"]
    command = [str(aeneas), "-backend", "lean", str(output), "-dest", str(destination),
               "-subdir", subdir, "-split-files", "-namespace", profile["namespace"],
               "-no-progress-bar", "-warnings-as-errors"]
    generated = destination / subdir.lstrip("/")
    # Otherwise an older external template can survive a later complete export
    # and appear incorrectly in its generated-file inventory.
    for previous in generated.glob("*.lean"):
        previous.unlink()
    with (logs / f"{args.profile}-aeneas.log").open("w") as log:
        result = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    audit["aeneas_exit_code"] = result.returncode
    audit["generated_files"] = {str(p.relative_to(HERE)): digest(p)
                                for p in sorted(generated.glob("*.lean"))}
    report.write_text(json.dumps(audit, indent=2) + "\n")
    if result.returncode:
        raise RuntimeError(f"Aeneas translation is incomplete; see {logs}")
    if complete_profile:
        check_body_dependencies(profile, output)
        text = "\n".join(p.read_text() for p in generated.glob("*.lean"))
        if any(generated.glob("*_Template.lean")) or re.search(r"\b(sorry|admit|axiom)\b", text):
            raise RuntimeError("generated reference has unimplemented obligations")
        if len(re.findall(r"^def\s", (generated / "Funs.lean").read_text(), re.M)) != profile.get("expected_generated_functions", profile["expected_functions"]):
            raise RuntimeError("Aeneas silently dropped selected functions")
        check_discarded_metadata(profile, generated)
    print(f"{args.profile}: generated actual Rust reference; Lean refinement checks remain separate")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError, RuntimeError, subprocess.CalledProcessError) as error:
        print(f"extraction refused: {error}", file=sys.stderr)
        raise SystemExit(1)
