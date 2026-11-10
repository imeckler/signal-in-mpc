import Lake
open Lake DSL
require «tls-mpc» from "../.."
require aeneas from "../../.deps/aeneas-2026-08-27/backends/lean"
package preKeyReferenceWork where
  srcDir := ".."
@[default_target]
lean_lib PreKeyReferenceWork where
  roots := #[`PreKeyReferenceWork.Proofs]
