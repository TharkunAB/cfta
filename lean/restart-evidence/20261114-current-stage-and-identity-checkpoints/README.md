# Source-universe identity and actual identity-prefix resources

Checked source: ccc7f3dc59f50966b90fec1ae49eda7bc54cfc3e. Prior checkpoint: f2e625838efa2c444487eba46d3a58c9f622424c.

The exact observed initial root narrowing now derives source-heap growth.
Supported actual identity prefixes preserve the existing state/order/resource
contracts at every common budget. Callback and captured-child completion now
retain the actual narrowing index with all configured contracts preserved. Whole-worker output history and one finite common original-root
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

The latest strict Audit checks 95,968 imported project theorems and separately
85 explicit reports: 83 standard-axiom and two axiom-free reports. The counts
do not establish the complete objective.

archived-inputs.json maps saved bytes to original paths and hashes. manifest.json
covers every payload file, including nested manifest.json files. It excludes
only the exact root manifest.json file. Verify source byte identities after
decompression. The source tree digest is 4e35ece2cbc2fbc5dd3033e6a47d5a27234e8b2a31a6ce45de4483729c917573.
