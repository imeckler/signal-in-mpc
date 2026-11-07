import Lake
open Lake DSL

require «tls-mpc» from ".."
require aeneas from "../.deps/aeneas-2026-08-27/backends/lean"

package signalReference

@[default_target]
lean_lib LibSignalReference
