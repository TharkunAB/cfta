# Type-position callback public review

Status: CLEAR. Recorded 2026-10-24 04:11:56 CEST. This reviewer read all 40 actual signatures, all 32 complete axiom reports, and both complete installed 209-line modules. The modules and selected repairs were authored by Root and required_memos; this reviewer authored neither module. No compiler, prepared program, Git mutation, or repository edit by this reviewer.

Public raw output is 21238 B/269 lines, SHA256 `84e95c6ff4e95e533d09d3d6410efb0e6243ac5a78a75f99f49d4369642c5fb1`. Its ordered names exactly match public-declarations.json and the actual 40 #check plus 32 #print axioms commands. Installed Positions SHA256 `f43e8f437cd6a51d2aa3cf343ebebc046317fc0f40b1c4a67df8e293fac02b5d` and RecordTypes SHA256 `c5a714825eab5f8efa89eaecbc5cae7438136834010d4270257d145af108bfbf` match the actual selected strict source snapshots byte for byte.

## Source behavior and exact statement scope

Positions defines the three concrete pure helpers. It retains full Label+Formula symbols and recognizes only exact ordinary Top app/4 and filter/2. typePositions uses the source nested right-fold order; hole insertion uses the existing ascending unique set view. A false-position hole leaves the incoming list unchanged. programHoles retains raw IDs, function-before-argument order and duplicates, including two equal occurrences. Other program shapes and complete type-position subtrees add no program holes. openProgram preserves concrete full labels and type/program child positions, drops children of hole/truncation markers, and uses ordinary ?, ?program#<raw Nat>, and Mu placeholders. Native source mapping is Pruning.hs147–175 and199–213.

Every public helper theorem is a literal branch, membership, or hole-insertion set fact. In particular, the Nodup and sorted statements concern a true-position hole insertion. They do not claim that arbitrary incoming lists or every unchanged branch are already canonical. A native IntSet realization requires ascending unique inputs, as the installed module header states. Native Int bounds, nonnegative ID encoding, decimal/Text formatting and extraction from Haskell values remain explicit representation boundaries. No helper claims typing soundness, a completed program or full-driver behavior.

RecordTypes maps native Pruning.hs99–112 directly. typesLast first returns the actual concrete pending-order choice; only on none does it select the first raw candidate outside the type list. atTypes is exact raw membership plus absence from every pending entry, without representative lookup. updatedTypes tests the incoming metadata.types.contains uv, then updates from the raw fragment; an inr node event keeps the types unchanged. recordTypes skips the template oracle entirely for an empty catalog. Otherwise it calls the existing concrete SourcePruningOracle.oracle, then updates only pending/types and retains the exact openHoles/typing fields. It does not take an arbitrary desired-result oracle or a ReadOnlyOracle premise.

The recordTypes_empty and recordTypes_inr signatures assert equality of actual complete actions with pure actions, not merely result equality. The metadata theorem needs only an actual success and retains precisely the types update, openHoles and typing; it does not claim that pending or prune are unchanged. The frame theorem requires initial UnionFind.Total and an actual success. Its Frame retains counter, all values, obligations, both complete ancestries, and all exact representative/root-size reachability facts; it does not promise literal forest equality.

Paired agreement fixes the same graph/catalog/metadata/raw current/event, allows independent successful left/right fuel bounds, and requires input Frame plus left Total. It concludes equality of the entire callback result and Frame of the actual final states. One-sided transport requires only the frame, left totality and one actual left success; it constructs an actual right success and finite right bound, with the identical result and complete final frame. It assumes neither right success, equal fuel, Safe/Finished, valid typing, accepted completion nor the desired callback result. moreFuel retains the exact successful result and complete final state. Proofs compose the existing concrete oracle at actual middle states.

No full typedTypes extension/dead-hole observation, narrow/emptyAt, union/Mu node view, native node-ID realization, typing-refinement soundness, full enumeration stream/multiplicity, native errors, convergence, or whole-goal result is claimed here. The separate native-node-view plan remains a prerequisite for that later callback. These two modules need no new such premise to prove their narrower observation results.

## Complete public inventory

The list below covers all printed public declarations in order. Source line numbers refer to the installed module named in the first column. Axioms are the actual reports, not inferred from proof syntax. Definitions/structures have no axiom-report claim in this output.

| Module | Declaration | Source line | Actual theorem axioms |
|---|---|---:|---|
| SourcePruningPositions | typePositions | 18 | not reported (definition/structure) |
| SourcePruningPositions | programHoles | 38 | not reported (definition/structure) |
| SourcePruningPositions | openProgram | 53 | not reported (definition/structure) |
| SourcePruningPositions | typePositions_hole_true | 76 | propext, Classical.choice, Quot.sound |
| SourcePruningPositions | typePositions_hole_false | 81 | propext, Classical.choice, Quot.sound |
| SourcePruningPositions | typePositions_hole_member | 86 | propext, Classical.choice, Quot.sound |
| SourcePruningPositions | typePositions_hole_nodup | 92 | propext, Classical.choice, Quot.sound |
| SourcePruningPositions | typePositions_hole_sorted | 98 | propext, Classical.choice, Quot.sound |
| SourcePruningPositions | typePositions_type_node | 104 | propext, Classical.choice, Quot.sound |
| SourcePruningPositions | typePositions_app | 110 | propext, Classical.choice, Quot.sound |
| SourcePruningPositions | typePositions_filter | 117 | propext, Classical.choice, Quot.sound |
| SourcePruningPositions | programHoles_type | 123 | propext, Classical.choice, Quot.sound |
| SourcePruningPositions | programHoles_hole | 131 | propext, Classical.choice, Quot.sound |
| SourcePruningPositions | programHoles_app | 134 | propext, Classical.choice, Quot.sound |
| SourcePruningPositions | programHoles_app_member | 140 | propext, Classical.choice, Quot.sound |
| SourcePruningPositions | programHoles_filter | 146 | propext, Classical.choice, Quot.sound |
| SourcePruningPositions | programHoles_repeated | 152 | propext, Classical.choice, Quot.sound |
| SourcePruningPositions | programHoles_other_four | 159 | propext, Classical.choice, Quot.sound |
| SourcePruningPositions | openProgram_type_hole | 165 | propext, Classical.choice, Quot.sound |
| SourcePruningPositions | openProgram_program_hole | 170 | propext, Classical.choice, Quot.sound |
| SourcePruningPositions | openProgram_truncated | 176 | propext, Classical.choice, Quot.sound |
| SourcePruningPositions | openProgram_type_node | 181 | propext, Classical.choice, Quot.sound |
| SourcePruningPositions | openProgram_app | 188 | propext, Classical.choice, Quot.sound |
| SourcePruningPositions | openProgram_filter | 196 | propext, Classical.choice, Quot.sound |
| SourcePruningPositions | openProgram_other_four | 202 | propext, Classical.choice, Quot.sound |
| SourcePruningRecordTypes | Metadata | 24 | not reported (definition/structure) |
| SourcePruningRecordTypes | typesLast | 35 | not reported (definition/structure) |
| SourcePruningRecordTypes | atTypes | 41 | not reported (definition/structure) |
| SourcePruningRecordTypes | updatedTypes | 45 | not reported (definition/structure) |
| SourcePruningRecordTypes | recordTypes | 50 | not reported (definition/structure) |
| SourcePruningRecordTypes | typesLast_pending | 58 | propext |
| SourcePruningRecordTypes | typesLast_fallback | 64 | propext |
| SourcePruningRecordTypes | atTypes_exact | 70 | propext, Quot.sound |
| SourcePruningRecordTypes | recordTypes_empty | 76 | propext, Classical.choice, Quot.sound |
| SourcePruningRecordTypes | recordTypes_inr | 83 | propext, Classical.choice, Quot.sound |
| SourcePruningRecordTypes | recordTypes_metadata | 89 | propext, Classical.choice, Quot.sound |
| SourcePruningRecordTypes | recordTypes_frame | 106 | propext, Classical.choice, Quot.sound |
| SourcePruningRecordTypes | recordTypes_agrees | 125 | propext, Classical.choice, Quot.sound |
| SourcePruningRecordTypes | recordTypes_moreFuel | 162 | propext, Classical.choice, Quot.sound |
| SourcePruningRecordTypes | recordTypes_transport | 178 | propext, Classical.choice, Quot.sound |

All 32 actual axiom sets are permitted subsets: 29 are exactly {propext, Classical.choice, Quot.sound}; typesLast_pending and typesLast_fallback use {propext}; atTypes_exact uses {propext, Quot.sound}. No custom or sorry axiom appears. No axiom-free claim is made.

## Correlated selected evidence

Positions-check-6 and callback-check-2 pass with literal empty raw logs, warning-as-error and all linters; both source snapshots equal the installed modules. The installed focused build passes. Public check passes. Aggregate Audit passes with 3678 jobs and 76071 checked theorem dependencies; its only warning is the older replayed unused inputs warning. Earlier attempts and the compiler-path correction are retained in the area; this review does not relabel these as clean first attempts or assert a new aggregate history count. positions-selection.json records the earlier 188-line proposal, while installation.json records the final two 209-line selections.

## Exact inspected identities

- `/home/tritlo/Code/mcfta/lean/MicroCFTA/SourcePruningPositions.lean`: 11125 B; SHA256 `f43e8f437cd6a51d2aa3cf343ebebc046317fc0f40b1c4a67df8e293fac02b5d`.
- `/home/tritlo/Code/mcfta/lean/MicroCFTA/SourcePruningRecordTypes.lean`: 13138 B; SHA256 `c5a714825eab5f8efa89eaecbc5cae7438136834010d4270257d145af108bfbf`.
- `/home/tritlo/Code/mcfta/specftacular/src/Specftacular/Pruning.hs`: 16989 B; SHA256 `5970dd7d9e67bb925fbd079921768ac08dc91d1c34e9ecfbc3d59795f0287f61`.
- `/home/tritlo/Code/mcfta/lean/MicroCFTA/EnumerationCompressionFrame.lean`: 8220 B; SHA256 `5b6e6a4b11c21b949874db500e23aa074fcdd4e0de683f46f33863113dc91375`.
- `/home/tritlo/Code/mcfta/lean/MicroCFTA/SourcePruningOracle.lean`: 20956 B; SHA256 `cb782c5dcc18b8dfe87927778523df97f38c9cf3fe1e9946e4f24f1ffbdc69e0`.
- `/tmp/mcfta-pruning-record-types-20261024/public-declarations.json`: 4402 B; SHA256 `f30da30a60c70c2ffedda497f24b2335c0fa0080c56129de54290368d1b081c9`.
- `/tmp/mcfta-pruning-record-types-20261024/public-1/raw.log`: 21238 B; SHA256 `84e95c6ff4e95e533d09d3d6410efb0e6243ac5a78a75f99f49d4369642c5fb1`.
- `/tmp/mcfta-pruning-record-types-20261024/public-1/checked.lean`: 4621 B; SHA256 `9be46e8cdcb84eeebd10936d38c2278c7dcde27d5a9d25607f176f3f9bbbd8fe`.
- `/tmp/mcfta-pruning-record-types-20261024/public-1/report.json`: 498 B; SHA256 `e2c72c09dc460e89d179279bf5657d8915377fec6a7f129abc56bd1c983e1295`.
- `/tmp/mcfta-pruning-record-types-20261024/installation.json`: 380 B; SHA256 `76b09a903957a84b0f293af7f3c86bfde709271a5e440e34e518f239f663d2c9`.
- `/tmp/mcfta-pruning-record-types-20261024/positions-selection.json`: 241 B; SHA256 `a33782b81c5e0fe25a7fb1f4aee7120fef2f00ba9e045d77526e9819de49f80e`.
- `/tmp/mcfta-pruning-record-types-20261024/compiler-path-repair.json`: 312 B; SHA256 `1efeb1f59067c9c46818ef0422cf3d3c38a7249b7b88c6fb9d819f0688326125`.
- `/tmp/mcfta-pruning-record-types-20261024/positions-check-6/report.json`: 643 B; SHA256 `8743ad5419c131fbbf3b6501a0ecec5df174190f7e71a55125ae20228e3680bd`.
- `/tmp/mcfta-pruning-record-types-20261024/positions-check-6/MicroCFTA/SourcePruningPositions.lean`: 11125 B; SHA256 `f43e8f437cd6a51d2aa3cf343ebebc046317fc0f40b1c4a67df8e293fac02b5d`.
- `/tmp/mcfta-pruning-record-types-20261024/callback-check-2/report.json`: 645 B; SHA256 `a17900ae1eb747c2433fb5aa9be9ad564c2c523c4088778c4be3bba6828b83f0`.
- `/tmp/mcfta-pruning-record-types-20261024/callback-check-2/MicroCFTA/SourcePruningRecordTypes.lean`: 13138 B; SHA256 `c5a714825eab5f8efa89eaecbc5cae7438136834010d4270257d145af108bfbf`.
- `/tmp/mcfta-pruning-record-types-20261024/installed-build-1/report.json`: 319 B; SHA256 `8ec210b42988924c928fd99980711e32b59a3157d277c12bf45708cf16e82506`.
- `/tmp/mcfta-pruning-record-types-20261024/installed-build-1/raw.log`: 164 B; SHA256 `3d8abfb05e622195c94b8afad39df5e3c33cdec667fe09487e9895d540b7e305`.
- `/tmp/mcfta-pruning-record-types-20261024/audit-1/report.json`: 300 B; SHA256 `2799ddeaeb9aa8703d8abefe401fbf6e572b8c47fbc725d980c4dd199a0c05ce`.
- `/tmp/mcfta-pruning-record-types-20261024/audit-1/raw.log`: 615 B; SHA256 `8341ffb1be41ec053bba57070ccd61326f2eeaf9462990164e296819e44de013`.
