# Original-model historical key shapes

Checked at 2026-10-28 23:26 CET. Source `59186c80ebae41dd672e560fa2196526d5dca368` on formalize.
The full formalization goal remains ACTIVE and incomplete.

## Strongest current statement

The Lean model of the optimized interned core has conditional checked rendered
soundness. Under the stated semantic/resource contracts, fixed-PCS and
whole-Discharged, a checked rendered output satisfies the source semantics. Increasing
recursive depth retains the existing ordered output prefix. A finite-depth
prepared run retains its actual outcome and resource histories, canonical and
proper storage, arity and physical projection under its original input gates.
These results do not assert that an output exists. A configured stop can emit a
partial output. DONE does not imply Discharged.

The earlier local callback theorem derives the same assignment model, actual
framed Packet, proper storage and a non-stuck restart at a literal successful
recording call. It does not require an output history. It does not prove every
recursive call completes or the original chosen model is eventually emitted.

This checkpoint adds a finite complete trie-shape family for historical
recursion keys. It also proves that an actual modeled prepared selected segment,
including its successful recording callback, retains that family. It does not
yet give a uniform bound on native boundary handles or whole-driver depth.

## Exact new contracts

`ModelKeyShapes.trieShapes whole` enumerates bounded lists over the earlier
`ModelPathDomain.relativePaths whole`. The path domain includes relative paths
in every subtree of the original term. `keyShapes whole` enumerates bounded lists
over those trie shapes. The actual key sorts and removes duplicate tries.
Original `Satisfies`, `AssignmentOrigins`, `Canonical`, a live slot and its literal
stored `unenumerated (some handle) scs` derive membership of the ACTUAL
`EnumerationState.recursionKey handle scs`. Both families are finite Lean lists.
They need no new runtime definition or dependency. They are proof domains.

`KeyAncestry carrier state` constrains `key.tries` in both complete history fields:
`expansionAncestry` and `recursionAncestry slot` for EVERY natural slot. The latter
must include slots beyond the current counter. Actual allocation reads the old
ancestry at the fresh-counter slot. A predicate restricted to live slots would
not justify that read. The literal initial state has empty histories and
satisfies any carrier.

`Entry.enter_key_ancestry` uses the original input model, origins, canonicality,
alignment, original carrier and literal actual successful entry. It derives the
inserted key shape at actual Mu or explicit-Union boundaries from the original
stored representative. It does not assume arbitrary inserted-key membership.
Other decoded cases do not add a key. Native repeat checking and actual entry
insertion remain distinct operations.

Actual allocation, native-index/writeSlot/ordinary preparation, cached
assimilation, own-class suspension, selected residual recording and finalization
retain the original carrier. Actual terminal prefix, raw dispatch, incoming
adaptation, cached preparation, ordered folds, terminal adapter, full child
dispatch and ordered child traversal retain it at their actual returned cores
or attached caches. Complete and arbitrary-observation stopped traversals are
covered. Rejected, merged-empty and synthetic empty adaptations remain covered.
Private adapter helpers derive their row facts from concrete dispatch observers.
No public future-state invariant supplier is added.

Actual selected and captured head observers retain the carrier at complete,
rejected and stopped-some caches. Captured completion uses the same actual
finalizer. Actual opaque completion uses its real child cache and captured
finalizer. Source stored handles remain distinct from prepared available values.

`PreparedRecursive.SelectedHistoryReceipt.key_ancestry` starts with the original
receipt input's model, origins, canonicality and `KeyAncestry (keyShapes whole)`.
It identifies the actual raw entry from the selected preparation observation.
That entry derives the new shape. Either actual completed receipt branch then
retains the same carrier. The theorem needs no model at the entered or returned
state. The receipt itself is the existing actual completed-segment observation;
the theorem does not establish that a receipt exists.

`SelectedHistoryReceipt.key_ancestry_after_callback` composes that result with
the literal successful `recordTypes` call. The existing actual frame preserves
both history fields. Either returned Bool is covered. No future callback model,
new carrier or arbitrary cache transport is assumed. To repeat the modeled-entry
argument through recursion, the chosen-model preservation obligation remains.

## Biggest remaining gaps

1. Actual chosen-model preservation through recursive emission. Accepted local
   head and restart transport already exist. The remaining work must connect
   actual recursive outputs and callbacks to the original chosen model. Fresh
   assignments are branch-specific. Different branches can reuse fresh numeric
   identifiers. Do not replace these assignments by one global fresh map.
2. Sufficient recursive depth derived from original source inputs. An earlier
   ordered allocating callback can prevent a later selected row from being
   reached. Prove earlier completion or a valid same-target emission argument.
   Output-prefix retention, stable finite-depth results and local non-stuck do
   not establish output existence or whole search termination.
3. Native identities in actual inserted recursion keys. Entry adds keys only at
   Mu/explicit-Union boundaries. The current `FiniteOrdinaryKeys` theorem excludes
   these cases. A finite physical inventory at each reached heap is not a
   uniform original-source family across allocating queries. Prove a finite
   original structural boundary family closed under generated native operations,
   then bound actual boundary handles or their cardinality along a branch.
4. Complete policy/solver/origin/public API contracts and correspondence with
   the optimized Haskell implementation remain separate obligations. Preserve
   older constructor/equality developments as secondary targets.

## Native-factor audit and rejected shortcuts

`SourceCurrentAllocatedFiniteOrdinaryKeys` excludes Mu/Union. `query_complete`
and `SourceCurrentAllocatedNativeInventoryRebase.extend` replace the inventory
source by the current pre-query heap and append current operands. Their Original
provenance can hold for a newly closed resident value. It does not establish that
the value has a startup physical handle. `Fits`, `Reserved` and `roomBits` are
local facts at supplied states and depths. They do not derive sufficient depth.
`encodeNode` uses the raw natural entry identity plus one. A mathematical
word-width bound on all future entry identities does not follow.

`InternedMuDepthInventory` gives a strict count decrease under its actual Lower
hypothesis. This checkpoint does not derive that hypothesis through all selected
preparation and explicit-Union operations. A uniform cardinality bound along an
actual branch may suffice. A literal startup Nat list across all allocation
orders can be stronger than the required theorem. The missing result is not an
admitted divergence counterexample or evidence of a Haskell defect.

Do not resurrect the earlier unproved A=f(A)|a divergence proposal. Empty-bucket
Mu can park. Keys omit enumeration variable identifiers. Union narrowing can
change a key and equality paths can grow. Any new counterexample needs a literal
actual all-depth argument or an independently checked native reproducer.

## Validation and preserved failures

Seventeen additive modules contain 35 public theorems, six private proof helpers,
two finite proof-domain functions and one history predicate. Total: 1,589 lines,
84,435 bytes. Enumerator/native/Haskell runtime definitions are unchanged.
All 17 modules and Audit pass exact Lean 4.34.1 strict checks with
`-DwarningAsError=true -Dlinter.all=true`. Audit passes 4,572 jobs and checks the
axiom dependencies of 81,854 theorem declarations. Only propext,
Classical.choice and Quot.sound are allowed. Counts are validation evidence.

There are 39 compiler commands: 37 passes and two preserved draft failures.
All final inputs pass. The first new captured proof exposed dependent match
generalization through its observation proof. The second exposed an unreduced
outer cached-own match before child traversal. Explicit non-generalizing result
matches and explicit outer reduction fixed these proof errors. Public semantic
assumptions did not change. The original candidates, exact input snapshots and
full raw logs remain. No linter suppression, placeholder, native_decide, custom
axiom or budget increase was added. All compiler commands ran serially with
measured memory.max/high 4,294,967,296 and memory.swap.max zero.

Public readback has 777 theorem checks with axiom lists and 66 definition bodies:
3,357,308 bytes, SHA256
e070cbd47953ced82b1d1dcab2eba1121d7b43571269ef1c0f413f2ce876e485.
The prior 3,301,695 bytes remain an exact prefix. All 55,613 new bytes were read
in four complete contiguous ranges. No new public-type display cut remains.
All 4,554 old non-Audit Lean, 403 stronger-source and 817 Haskell/Cabal identities
remain unchanged. Audit keeps its exact earlier body after seventeen imports.
All nineteen earlier document bodies remain exact suffixes. Twenty final
documents are preserved. Six source-scope manifests verify 194 recorded artifact
identities. Literal cuts remain literal cuts. Earlier UNTESTED candidate labels
remain unchanged; final source hashes identify the versions checked by the root.

## External Haskell repair record

No Haskell source changed. No Haskell check ran. No new Haskell defect or fix was
established. The two repairs affect only new Lean proof elaboration. The native
boundary-inventory limitation is a missing proof, not an implementation bug.
Root FINDINGS.md retains every earlier external Haskell repair record unchanged.
Record any later Haskell defect, proposed repair, actual fix and focused evidence
there so another worker can act on it.

## Restart and publication

Five source commits end at `59186c80ebae41dd672e560fa2196526d5dca368`. Exact remote and tracking
heads match on `git@github.com:TharkunAB/cfta.git`, refs/heads/formalize.
Origin/main d1ca06a1dd0c7488205feda613b529df21a08669 is an ancestor.
Refresh upstream before new work. Preserve unrelated work and every marked draft.
SSH port 443 uses ssh.github.com and the existing trusted github.com host key.
No remote URL or SSH configuration changed. Normal formalize pushes remain
explicitly authorized. The full goal stays ACTIVE. Do not pause or complete it
merely because this checked checkpoint is published.

Board sequence 712, post `5b9df506-738e-43ea-93b6-632b37912317`, has exact
verified author, content and metadata. The msg-board skill supplies the shared
project note. The complete unfiltered evidence is in
`lean/restart-evidence/20261028-model-key-universe/`. Verify or reconstruct it
with that directory's README and standard-library verifier. It includes every
regular file from `/tmp/mcfta-model-key-universe-20261028/`, including failures,
scopes, candidates, all command inputs, full readback, prior/final documents,
measurements, Git receipts and exact board readback. Preserve frozen areas and
fresh reconstructions. Use a new writable directory for the next proof step.

Read this note, then NEXT-PROMPT.md, HANDOFF.md and FINDINGS.md front matter.
Use PreparedEntryModels, PreparedFiniteReceiptModels, PreparedCallbackProgress,
PreparedFiniteHeadCoverage, PreparedFiniteSiblingCoverage and the new
PreparedReceiptKeyAncestry as the current local contracts. Do not duplicate local
model transport or add the desired future model as a hypothesis. Continue with
a source-derived boundary carrier or the actual chosen-model emission theorem.
Keep compilation and native execution serial under the existing 4 GiB cap.
