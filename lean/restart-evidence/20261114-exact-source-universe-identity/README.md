# Source-universe identity and actual identity-prefix resources

Checked source: f1fec5d6fa0098bc453dcdee417d1b7aa6a7be68. Prior checkpoint: 43ffe583f8f3f4b035d8a7ede419b873e5b8e112.

The source-created universe is now the exact result of the native ref(U)/Mu(U)
request, including after structurally valid source-heap growth. The actual
identity enumeration prefix preserves the existing state/order/resource
contracts. Whole-worker output history and one finite common original-root
completion remain open. Compiled Haskell correspondence is not proved.

The checked source is sufficient to reproduce these Lean proof results. Logs
record derived results. This packet also preserves failed inputs, repairs and
marked drafts absent from the final code. It contains no compiled objects or
copied import overlays.

Use the pinned checkout and Nix shell. Archived publication drivers contain
the exact build, strict-check and independent-import commands. Run jobs serially
with the recorded 4 GiB cap. Verify source-pins.json.gz before rerunning.
Run lake build MicroCFTA.Audit and lake env lean -j1 -DwarningAsError=true
MicroCFTA/Audit.lean from lean/ inside the pinned Nix shell. Recreate /tmp output
directories and regenerate an archived driver's absolute-path source pins if
the original private paths no longer exist; do not treat those paths as build
dependencies of the public source.

The latest strict Audit checks 95,945 imported project theorems and separately
81 explicit reports: 79 standard-axiom and two axiom-free reports. The counts
do not establish the complete objective.

archived-inputs.json maps saved bytes to original paths and hashes. manifest.json
covers every payload file, including nested manifest.json files. It excludes
only the exact root manifest.json file. Verify source byte identities after
decompression. The source tree digest is 9a407e6a1620e3010dd49a898571be4b8c6da9b22b6eb9b71e800eb55089e058.

checkpoint-note.md.gz preserves the exact template bytes for finalize.py.
Decompress the template when reconstructing its private run directory.
