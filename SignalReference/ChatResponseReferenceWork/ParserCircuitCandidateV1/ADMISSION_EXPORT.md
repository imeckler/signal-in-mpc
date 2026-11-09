# Minimal admission exporter and exact resource counts

AdmissionProgram is a minimal computational import used only for export. The
independent kernel bridge proves exact generic program equality and HEq of the
dependent compiled circuit to the already-proved compact runAdmit. HEq is needed
only because compiler result types include output length. No computation,
private payload or rejection behavior is assumed or changed.

After TLS60288 terminated PASS and released its heavy window, the sequential
admission-only exports passed under Lean-M2048/45s and a2GiB RSS acceptance
ceiling. Measured combined child peakRSS is1,333,100,544B. Original and compact
both execute1,043 ANDs/608 XORs at AND depth25 (raw2,867 ANDs). Input/output bits
shrink7,936/7,856 to4,736/4,656. Compression removes copied state input/output
wires here; admission logic gate/depth costs are unchanged. No timing comparison,
byte re-export, native benchmark or runtime promotion is made. Exact source,
artifact and backend statistics hashes are in profile-admission-audit.json.

Earlier terminal attempts are unaccepted resource evidence only: OS preexec
heap-limit setup failed before Lean launch; proof-heavy and then minimal imports
under-M256 failed during metadata kernel checking. An empty Lean+Core minimal
import smoke passed at1,266,171,904B RSS even under-M256, showing that Lean's
allocation limit is not a total RSS limit. No larger export was attempted while
TLS60288 remained live. Failed outputs are isolated under Build/profile-admission-
v1 and Build/profile-admission-minimal-v1; final graphs use the separate released
window directory. export-resource-evidence.json records the exact terminal data.
