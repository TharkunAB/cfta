# Pending-slot producer plan

Source-only assessment. The companion freeze record gives the actual time and full source/cut hashes. No proof body, compiler, prepared-program execution, Git action, or repository change was made.

Recommend encoded allocation, encoded slot replacement, and composition with actual native narrowing. General assimilation cannot yet follow from the existing `Graph` interface. An ordered observation batch is a smaller alternative for the `typedTypes` read loop.

## Source writes

- `cfta/src/Data/CFTA/Enumeration.hs391–407` allocates a UVar and stores `UVarUnenumerated x []`. `prepareShallowChild789–802` then stores the SAME node with its full suspended list. This is allocation plus replacement, not intersection.
- `intersectUVarValue201–221` keeps the other optional node when one input is absent. Two present nodes call actual native intersection. With `checkEmpty`, a constrained recursive result can then become `EmptyNode`.
- `assimilateUvarVal490–511` reads both raw slots, writes their intersection to the target, eliminates the source, and combines ancestry. `mergeNodeIntoUVarVal513–526` first resolves the representative, then intersects and writes before the emptiness guard.
- `enumerateUntil'978–1005` writes a narrowed node only when its identity differs. It keeps the suspended list. Its repeated-recursion branch clears that list and keeps the SAME node. These writes change the value array, so their effects are not compression frames.
- `specftacular/src/Specftacular/Pruning.hs124` sequences ALL `getUnexpandedNode` actions in ascending open-hole order. The following pure `or` can demand only a prefix of the lazy `emptyAt` results. A coupled native-heap trace must retain this distinction.

## Three precise statement candidates

Use the existing full `SourcePruningTemplates.Symbol`. Keep `EnumGuard` and `NativeGuard` distinct. The names are proposals, not declarations or accepted proof scope. No new packet, state type, decoder, or semantic callback is required.

1. `allocate_available_realized`. Inputs: native `heap`, enumeration `before`, complete interned `value`, `Coherent heap`, `Available heap value`, `value.free = []`, `PendingRealized heap before`, and `before.counter = before.values.length`. Derive an existential `node`, `encodeNode value = some node`, actual `Success (allocate (some node)) before before.counter (allocated (some node) before)`, the returned UVar's exact new-slot equation, and `PendingRealized heap (allocated (some node) before)`. Derive the handle/readback with `available_readback`; use `allocate_exact` and `allocated_slot`. Old slots keep their original certificates. Alignment is needed for the returned UVar to name the appended slot; realization alone does not imply alignment.

2. `write_available_realized`. Inputs: the same native certificates and realization, raw `slot`, arbitrary suspended list `scs`, and `slot < before.values.length`. Derive an existential computed `node`, actual successful `setValue slot (.unenumerated (some node) scs)`, exact final state `{before with values := before.values.set slot (.unenumerated (some node) scs)}`, its exact new-slot readback, and `PendingRealized heap` of that state. The new certificate comes from the actual available value, not an assumed final invariant. The in-range premise supplies source-insert/list-set correspondence and actual readback. This also handles unchanged-node suspended-list changes. Writing `.enumerated` or `.eliminated` adds no pending obligation and can use the same local list argument without another public abstraction.

3. `narrowed_slot_complete`. Inputs: `Ready heap`, `PendingRealized heap before`, and a genuine raw read `before.values[slot]? = some (.unenumerated (some oldNode) scs)`, plus source parameters `fits`, `admits`, and `key` and the existing `DecidableEq (EdgeKey Symbol NativeGuard)` instance. Derive the complete old value from realization. Derive finite actual `narrowAt fits admits nativeFuel key value heap = .done result nextHeap`, `Keeps heap nextHeap`, available closed `result`, and its computed `nextNode`/readback. Propagate EVERY old slot to `nextHeap`. Retain the source Empty rejection: derive either `result = .empty` with no successful slot-write branch, or `result ≠ .empty` and execute the raw-slot suffix `if nextNode = oldNode then pure () else setValue slot (.unenumerated (some nextNode) scs)`, concluding its exact final enumeration state and `PendingRealized nextHeap` there. This is a derived case split, not a supplied nonempty-result premise. This is the source write after representative capture. It does not prove that the raw slot is a canonical representative without the actual preceding representative packet. Return the native heap explicitly; do not add it to the enumeration state.

For candidate 3, `SourcePruningNativeView.narrowAt_complete60–79` supplies the actual native result and cache history. Its final Ready supplies Coherent through `ready.semantic.1.normal.facts.coherent`. `available_readback` derives the handle. `realized_preserved` with `Frame.refl` and the derived Keeps transports the old slots. Candidate 2 handles the changed-ID branch; the unchanged branch retains realization directly. No `emptyAt`, second driver run, or numeric oracle is needed.

The existing Lean loop `EnumerationUntil106–124` accepts a PURE narrowing function on Nat handles. It does not already carry this returned native heap. Therefore candidate 3 is the concrete coupled write suffix, not a theorem that the whole old parameterized loop now maintains the native heap. Later composition must identify its supplied pure narrowing result with the computed handle and retain the same physical heap trace. The model handle equality is not a proof of native NodeId extraction.

Estimate 135–180 ordinary lines for all three candidates, with an exact-header review before a proposed hard200 limit. This is an estimate, not authorization or a verified source size. The two slot results alone should fit about70–115 lines. Defer the narrowing wrapper if its exact statement would make the component excessive.

## Intersection obstruction

`lean/MicroCFTA/EnumerationState.lean51–53` exposes only `node : Nat → Node` and `intersect : Nat → Nat → Nat`. `intersectValues144–151` installs that returned Nat with no native heap effect. `IntersectionCorrect` and `intersection_semantics` are language laws; neither supplies a computed native readback or cache history. Storage preservation constrains UVar addresses, not the pending node handle.

The interface permits an intersection function that returns an unissued handle while its inputs decode. Its `node` function can classify that handle as nonempty, so the source-model emptiness guard cannot establish realization. This is an interface obstruction, not a Haskell defect. Existing `EnumerationInternedRows.graph26–29` takes an arbitrary `meet` and uses a separate bounded row-cache carrier. It does not solve this full-value correspondence.

The missing producer must decode BOTH actual stored operands, run their actual native intersection in ONE evolving heap, retain its returned complete value and cache histories, derive closed availability, and encode the exact handle written to the slot. That handle must match the SAME modeled `graph.intersect` result. Assuming a blanket final-handle agreement law only moves this obligation into a premise. Constrained-recursion emptiness normalization, union/Mu behavior, and the current concrete finite-model/rank inputs must also be retained.

Do not claim unconditional `assimilate` or `mergeNode` preservation from the current graph interface. A later concrete intersection producer can feed the slot arguments above. Existing `EnumerationCorrectness.assimilate_exact277–296`, `mergeNode_exact327–346`, and storage lemmas969–995 then identify the actual writes. Failed or rejected branches have no successful final-state claim. Native exceptions and model errors remain separate.

## Smaller ordered-read alternative

Given fixed native `heap`, `PendingRealized heap before`, `StorageValid before`, and `∀ uv ∈ holes, uv < before.counter`, derive one common finite `fuel`, exact ordered `observed : List (Option Nat)`, and actual `Success (holes.mapM (getUnexpandedNode fuel)) before observed after`. Conclude full `Frame before after`, `StorageValid after`, retained realization, and `All₂` pairing each raw input UVar with its optional output. Every `some node` must decode to an available closed complete value in the SAME native heap. Preserve length, order, and duplicates. Ascending uniqueness is a caller's actual IntSet/list correspondence, not an implicit theorem premise.

Use `observation_complete88–120`, `observation_storage80–86`, `Frame.counter`, frame transitivity, and `getUnexpandedNode_moreFuel70–76`. A list induction generalizes the current state/results. It retains the remaining allocated bounds through the unchanged counter and combines head/rest fuel by addition and `EnumerationExecution.retains_mapM51–61`.

`EnumerationExecution.mapM_terminates371–391` requires a local step for EVERY argument of the action's input type. It cannot directly consume only membership-restricted bounds for arbitrary Nat inputs. Use the restricted list induction, or explicitly attach bounded inputs and prove the resulting map correspondence. Do not silently discard the allocated-bound premise.

Estimate80–125 lines for this alternative, with one actual batch theorem and a small ordered-relation helper only if necessary. It advances `typedTypes`, but does not establish realization after writes, derive metadata open-hole bounds, or run every pure `emptyAt` check eagerly. The latter must follow the source's lazy Boolean prefix after ALL UF observations.

## Exact dependencies and scope

- `SourcePruningEnumerationObservation` now exists as a122-line installed file. Its public API includes the additive `observation_storage`; use the exact current source hash in the freeze record. Root owns these proofs. Arity authored the original declarations and this plan; this assessment is not an independent reproof of that foundation.
- Slot producers need only the existing import `MicroCFTA.SourcePruningEnumerationObservation`. It reaches codec/native view and the enumeration actions. The batch can explicitly import `MicroCFTA.EnumerationExecution`.
- `EnumerationState.allocate_exact578–579` and `allocated_slot588–591` expose the actual allocation and returned slot. No Total or Ready premise is needed for the isolated allocation/write results beyond their listed certificates.
- `SourcePruningEnumerationNodes.available_readback35–48` derives encode/decode from Coherent, Available, and literal closedness. `lookupNode_keeps51–74` retains computed readback under actual Keeps.
- `SourceEqualityRequiredCache19–43` supplies Ready, Keeps, unchanged-state effects, and transitivity. Available growth and issued history are not inferred from value-array replacement.
- Installed Lean v4.34.1 `Init/Data/List/Lemmas.lean618–679` supplies exact public `List.getElem?_set_self`, `List.getElem?_set_ne`, `List.getElem?_set`, and `List.set_getElem_self`. No guessed list-index API is needed.

Native NodeId extraction, graph/child-handle realization, source cached-index maintenance, all-state `typedTypes` preservation, native error streams, general pruning soundness, and H6 end-to-end resources remain open. No new compiler, Audit, seal, or push result is claimed here.

The original58-payload observation declaration owner is unchanged. Its `pins.json` SHA is `94dba813e177ed8cab70595bd11172a7174a9924dddc9e58df63aa75d41f1301`; its `FROZEN.json` SHA is `332b279d5c98cf57c010a2f7ecba728ca1a115fbe9bfcba71a43a3a3ae87492c`. The companion freeze record pins all full current source files and inclusive cuts by absolute path, bytes, and SHA256. No new executable or proof body is included.
