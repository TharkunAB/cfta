# Terminal waiting gains: source assessment

The suspected raw-ID mismatch is absent from the current source. `writeUVarValue` passes the current `_uvarRepresentative` forest into its count fold. Each gained or lost occurrence updates the key `uvarToInt (UnionFind.root (scGetUVar sc) uf)` (Enumeration.hs448–466). The native code does not require incoming suspended variables to have already been replaced by their representatives.

`mergeNodeIntoUVarVal` supplies gained=incoming constraints and lost=[]; it then inherits ancestry and checks Empty (513–525). The terminal caller first records old representatives, unions the terminal variables, moves distinct old counters to the winner, assimilates the original recorded list, and passes the partition's descendant constraints into that merge (712–747). Partition and descent retain the variable names. Their role is path/caller provenance, not canonicalization of waiting keys (150–179). Duplicates count as separate occurrences.

The logical operation agrees at the mathematical level: `EnumerationCanonicalWaiting.count roots` maps every suspended `sc.var` to `roots sc.var` before the ordered count fold (24–27). The selected `gained_correct` contract uses this operation after appending incomingScs++oldScs. Prefix completion already derives `Roots joined.representatives (mergedRoots roots recorded winner)`. Fold retains the forest, and Incoming's read Frame retains all finite root paths. These facts identify the same merged root map at the actual write prefix. They do not require a canonicalized incoming list.

Pure-root adequacy is also existing work. `SourceUnionFindRoot.root_eq`, `root_correct`, `root_terminates` and `root_moreFuel` relate the bounded read-only worker to actual findRoot and finite paths. Native `UnionFind.root` follows parents without compression or missing-root insertion (128–137). A finite valid forest is required; this inspection establishes no claim for cycles. No executable reproducer was run, and no reachable counterexample to this specific suspicion was found.

The next material gap is the source-specific cached-index projection at the SAME actual terminal write/inherit prefix, rather than another canonical-count identity. It should consume genuine prefix roots/counts, the retained current forest/read frame and actual old-slot/write equations; compute the native gained-only waiting update and the written slot's expandable flag; and relate these to the derived canonical view. Existing `EnumerationPureSelection.write_correct` and `transfer_correct` are useful ingredients, but their candidate predicate uses an abstract Graph. They cannot certify the checked native Value/handle path by an assumed Graph equality. The current action returns moved waiting as a staging view; it does not execute the derived gained-map update.

Machine Int/IntMap/IntSet extraction remains separate. Existing modular proofs handle raw reference counts; reuse requires the canonicalized value view and actual class-total bounds. Initial constrained-recursion flag provenance, the exact terminal/descendant partition, and enumerateOutUVarWith's later ancestry reset and write at captured original uv′ also remain open. That write must not be replaced by a write at winner. This assessment supplies no full caller, maintained native-index, Safe/LiveRoots, convergence or whole-driver language claim. H6 remains strongest; the whole goal is active.

The timestamp is 2026-10-25T00:25:03.265410+02:00. This is source/data inspection only. Root owns all bodies and execution. Whole/cut identities are retained in the sibling source-index.json.

| Source | Whole SHA-256 | Inclusive cuts |
|---|---|---|
| `/home/tritlo/Code/mcfta/cfta/src/Data/CFTA/Enumeration.hs` | `949c484539483f0e646b069899be127a57f0897353b24b92e51a5d90654cec07` | 150–179, 448–466, 490–525, 712–747, 879–903 |
| `/home/tritlo/Code/mcfta/cfta/src/Data/CFTA/Internal/UnionFind.hs` | `096db1d6a4d693cebfc9cb643486434baee93e3379c5a411d3edd556d102d434` | 128–137 |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/SourceUnionFindRoot.lean` | `83e4cca222e43535bd10b33ef11c4a323132cbe399fd59dee76180ff27ef219f` | 14–63 |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/EnumerationCanonicalWaiting.lean` | `a941b9b49e87115f26ecba015bc23e15a3d873410ac943ded77ff5f8963057bd` | 16–37, 83–90 |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/SourcePruningEnumerationTerminalPrefix.lean` | `bc975e650b8ee6cecba75605107cbf2ad458e02137854994d91541b4b63d9b30` | 46–79 |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/SourcePruningEnumerationFold.lean` | `0a5ae94315af7024fc4cc80bcc00163996fceaf95568969df73401fea9c2db16` | 88–104 |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/EnumerationCompressionFrame.lean` | `5b6e6a4b11c21b949874db500e23aa074fcdd4e0de683f46f33863113dc91375` | 20–36 |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/EnumerationPureSelection.lean` | `32c3840fbade865c3e9342f6b7dddcc44fbfef0db0185b4950aedce3912e6729` | 20–36, 67–96, 164–171 |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/EnumerationWaitingModular.lean` | `0c315b0092e786313e248e5d9023117aa61a1c54d2c7280de1930a78e014ee8f` | 38–43, 84–110 |
| `/tmp/mcfta-pruning-enumeration-terminal-20261024-proposal/gained-header.lean.txt` | `9217a689ec2932334c88628fb9484d1e0d21936f6504e5742812e85c84a73ce2` | 1–9 |
| `/home/tritlo/Code/mcfta/lean/notes-main-525d722e.md` | `c18c7fe021e792a0f61ab3e3d8233bd008bbe8f8f6b04e18127329fe2a3cd259` | 9–57 |
