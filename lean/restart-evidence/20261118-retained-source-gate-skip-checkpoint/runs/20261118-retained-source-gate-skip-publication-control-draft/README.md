# Retained source gate and shared skip publication

Root copies `prepare-publication.py` into `20261118-retained-source-gate-skip-work` after review. Root then runs it. The preparer validates the actual staged bytes, private check 15994, and the pushed Source 1a3 checkpoint. It creates a fresh publication runtime only after these checks pass. It does not change normal Source or Git.

Root runs `check.py` in an 8 GiB memory scope with zero swap. The five gates are public build, strict Gate and Skip compilation with inherited bindings, independent imports, Audit build, and strict Audit. The two strict modules use one fresh namespace. Their outputs cannot be links to normal cache objects. The strict public queries run against those same fresh objects. No cache data is copied. All proofs use the existing default limits, one Lean thread, and fatal warnings.

The expected totals are 6279 Source files, 5279 Audit imports, 726 Audit reports, and 321 independent reports. Audit has 720 standard reports and six axiom-free reports. Independent checks have 318 standard reports and three axiom-free reports. Only the two new public statements receive fresh component credit. They extend 518 inherited reports to 520. All 264 resource reports stay inherited. No private theorem or definition is added.

The old Gate owner remains an exact 5721-byte prefix. The entire old 433976-byte Audit block follows one 63-byte Skip import. Two public axiom queries follow the old block. The only historical Source overrides are the Gate and Audit BEFORE snapshots in Work57. The script checks the prior archive, actual publication receipts, Source pins, and toolchain pins. It does not replay axiom strings as proof evidence.

The Gate theorem derives a false gate for an available value under genuine past source inventory. The Skip theorem derives the actual shared skip at the same queried state and fourth component. It keeps the actual saved query memos. Complete worker preparation and query admissions remain separate. Native inhabitance, guard truth, Type/Marker compatibility, finite completion, and Haskell correspondence remain open. The checked query-sequence Seeds component is preserved.

These controllers are frozen candidates. They have not been executed. Root owns publication, Source commits, cleanup, and checkpoint assembly.
