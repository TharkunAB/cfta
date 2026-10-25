# Actual entry and native ordinary alternatives

## Current result

Entry preservation: `4f85bd0adff78903bbe771f4816b2033d39b69ec`.
Ordinary composition: `ae1a6b4cb99e6532e53c3f5ebb68bdfb8a712a90`.
Main remains `153e1a211b56dd78bd22f6b427fb78e673041d55`.
The whole formalization goal stays ACTIVE.

`SourcePruningEnumerationNativeOrdinary.complete` composes actual selected
entry with the admitted native alternative scan. It derives common sufficient
finite bounds. Entry captures the same raw root that was ready at its input.
The scan uses the cache returned by that entry. Each alternative restores
this enumeration cache and retains the reached native caller and queries.
Every processed receipt retains its own reached-heap cache certificate.

The admitted scan completes every selected edge with a supported annotation,
including valid rejections. Unsupported preparation gives an explicit stop.
The theorem does not assume a future successful entry or alternative trace.
It does not assert that any edge accepts a term.

## Source boundary

The wrapper covers the ordinary nonterminal-parent arm of
`enumerateOutUVarWith enumerateShallowHere`. `orderedRawStep` uses this arm.
The pruning expander also uses `enumerateShallowHere`.
Enumeration.hs:783 requires both an ordinary `Node` and no terminal trie in
the parent suspended bucket. Readiness, native flags and `InputsPending`
do not imply that terminal condition. The new premise states it explicitly.
Nonterminal parent inputs can descend into terminal child inputs. The existing
native child dispatcher retains those terminal cases.

The actual source reads `_edgesOf` at Enumeration.hs:785. The wrapper takes
the corresponding pure callback. Admission requires every returned edge to
belong to the decoded parent's stored edge list. It does not require that
callback to return every stored edge. Order and duplicate occurrences remain.
The semantic adequacy of a pruning edge-selection callback remains separate.

The wrapper does not implement terminal-parent expansion or normalization of
Empty, Mu or Union parents. These cases retain the exact entry result and
return no ordinary scan. The existing entry action still records its actual
ancestry effects. No fallback execution is claimed.
`enumerateFully'` supplies `enumerateNode`, whose ordinary children recurse
immediately. This is not the same ordinary expander.

No Haskell defect or repair is identified. The external Haskell fix handoff
remains first in root FINDINGS. Haskell runtime source is unchanged.

## Entry and numeric admission

`run` calls `Entry.enter` once. Its first result component retains the full
raw entry list at every bound, including errors and rejection. The second
component scans alternatives only for an actual singleton ordinary entry
with a nonterminal parent bucket. `entry_readback` is an unconditional exact
projection law. `terminal` proves the fixed-bound terminal exclusion.

`Ranges` requests numeric branch admission only at actual singleton entry
endpoints. It supplies no successful entry, cache invariant or future trace.
The completion proof first calls `SelectedEntry.complete`. It identifies the
actual decode with the stored ordinary parent. Its returned index equalities
prove that framing the actual entered core yields the returned entered cache.
The proof then calls `NativeBranchCompletion.complete` once at that cache.
Representative bounds combine by addition. The other branch bounds retain
their existing stable extension laws.

Initial premises retain genuine caller Context, readiness at the actual entry
input, the actual stored pending handle, native realization, root paths,
canonical waiting counts, native flags and inherited `InputsPending`.
Readiness before a separate narrowing or oracle callback is insufficient
without a preservation theorem for that callback.

`SelectedEntry.complete` now also exports `RenderStable`. Its proof already
established unchanged values, counter and obligations, safe output and full
class equivalence. Existing `pending_read` and `incoming_read` can therefore
transport global reference facts through this actual entry operation.
The wrapper returns the same preservation structure for its entry receipt.
No new entry precondition was added.

## Remaining reference history

`Ready.avoids` excludes the target from its own bucket. It does not exclude
that target from all stored buckets. `PendingReferences` before entry permits
references to a target that is still pending. These two premises alone cannot
justify `PendingReferences` after finalization.

The required additional fact is `IncomingAvoid target` at the selected state.
The actual unblocked waiting receipt can derive it through
`Selection.unblocked_avoids`. Entry can transport it with the new export.
Native pending writes, terminal assimilation and child traversal must then
preserve it and the avoidance of all old enumerated classes. This includes
post-write raw-empty rejection. Existing safety, enumerated origin and root
protection do not by themselves constrain newly stored references.

Finalization can then use `setValue_pending` for its exact captured raw-slot
write. `FragmentAvoid` remains a separate obligation about fragment holes.
`PendingReferences` inspects stored suspended references, not fragment holes.
Each alternative keeps its own enumeration cache, so these invariants must
be stated per receipt rather than for an invented merged final cache.

## Verification

Both final changed modules pass Lean 4.34.1 with all linters and warnings as
errors. Entry passes on its first strict attempt. Ordinary attempt 1 reports
one unused simplifier argument. Attempt 2 removes that argument and passes.
All attempted sources and complete raw logs are retained. No production
proof limit or linter setting changed.

The installed entry build and aggregate Audit pass. The audit checks 76699
theorem dependencies in 3747 jobs. All six public declarations pass installed
readback. The complete public log has 249 lines and 16893 bytes. Its SHA-256 is
`be2dcb77e507f614d6e0868bde8b6fd40e544d42bd1d4504cffb13cc49b6e449`.
All axiom sets are subsets of `propext`, `Classical.choice` and `Quot.sound`.
The older unused `inputs` warning remains unchanged.
Checks run serially under 4 GiB heavy-management caps with no swap.
Evidence remains in `restart-evidence/20261025-native-ordinary`.

H6, the earlier native alternative workers and the optimized interned core
remain unchanged. No Haskell runtime tests were repeated because executable
Haskell source did not change.

## Strongest claim and next work

H6 remains the strongest end-to-end result. Covered closed construction,
valid initial constraint cache and original allocation history, any prescribed
finite budget and number of modeled node calls derive sufficient finite fuels
and one mathematical width chosen after construction. With empty inherited
payload, the final available value has exactly the original finite-tree
language under the formal formula and entailment interfaces.

Next prove native reference provenance and incoming avoidance through actual
child mutations. Then derive global pending and fragment dependency history,
successful receipt semantics and whole-driver language preservation. Parent
normalization, terminal-parent execution, narrowing and oracle preservation
remain explicit integration boundaries. Initial-only numeric admission remains
open. The serial alternative worker also leaves arbitrary Haskell demand,
full raw-stream erasure, physical maps, machine integers and concrete solver
correspondence open. No practical resource or convergence bound is claimed.
