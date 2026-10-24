# Outer pruning wrapper and finite completion

Updated: 2026-10-24.
Main: `74250bd889685da436cdbfe32ac4b5a0878ffd09`, incorporated.
Proof: `f1b32242e383a19ddaf907e01d8173729223526a`.

## Exact definition and results

SourcePruningOuterNarrow models the outer narrow callback in prunedPrograms.
It uses the existing Metadata Typing and native Result types. Symbol is the
complete refined-label alphabet. Guard, Typing and Key remain independent.
The source public callbacks holeKey, fits and admits remain explicit inputs.

The definition first inspects the complete input Value. Mu returns that same
Value and native heap. Every other shape then tests the original selected raw
UVar in metadata.types. A member also returns the same complete Value and heap.
Only the fallback calls the actual native-model narrowAt operation. Its key is
holeKey metadata.typing uv, with that original raw UVar. Neither bypass computes
a key, reads rows, constructs a node or invokes the fallback.

The all-fuel Mu and type-membership equations retain every stored field and
the exact heap. They include fuel zero and need no Ready or desired output
premise. The non-Mu, non-type equation retains the actual narrowAt result,
including its exact failure and heap effects. Union is not a Mu bypass.
The metadata input is unchanged. Native IntSet correspondence remains separate.

Ready heap, input availability and input closedness derive a finite actual
wrapper completion. The result retains the actual native heap, Keeps, result
availability and closedness. Every larger fuel returns that same chosen result
and heap. Bypasses use the same heap and the existing pure_keeps result. The
fallback obtains its actual output from narrowAt_complete. It adds no supplied
result, final Ready or desired computation equation. The combined result does
not assert Ordinary because the bypasses retain the original Mu or union.

No new carrier, metadata type, state predicate, proof helper or instance is
added. The model has one definition and four theorems. Concrete typing/key
laws are not premises of these operational branch and completion results.

## Validation and retained work

The first actual strict Lean attempt, source-check-2, passes with an empty
log. Earlier source-check-1 stopped in setup before Lean read a source. Its
failed capped receipt remains separate from the four actual passing checks.
The public readback passes with all five full types and no display omission.
The installed build passes 567 jobs. Audit passes 3686 jobs and
76128 dependency checks. Its single warning is the older
InternedFreshOrdinaryClosedCompletion replay. There is no new-source warning.
All five complete public types and actual axiom reports were read.
All five declarations report only propext, Classical.choice and Quot.sound.
Exact frozen declarations, scoped types, source cuts, independent reviews,
raw inputs/results and capped resource receipts remain. The full baseline has
129494 tracked files. The preceding narrowing checkpoint's post-seal receipts
remain. Earlier sealed evidence stays unchanged.

## Next proof and boundaries

Connect the wrapper to actual realized pending observations before selecting
a bypass. Retain the actual enumeration entry state after compression. Use
the existing narrowing suffix only in the fallback. If it derives oldValue
again, identify both values by the same actual lookup. A bypass must not run
native narrowing merely to discover its old Value. The driver still checks
Empty after the wrapper, including an Empty value returned by a bypass.

The raw UVar determines membership and key selection. A second representative
read determines only the changed write address. The pure Nat callback and
graph classification in EnumerationUntil still need a source-specific bridge
to the explicit native heap and complete values. Native NodeId extraction,
waiting and expandable caches, memo2, intersection/assimilation, open-hole
bounds, ordered reads, lazy demand and the whole oracle/continuation remain.

The concrete PartialTyping, holeTypeOf, canonicalVariables, constantFits and
typeAdmits representations and laws remain open. Existing bounded typing-rule
models do not supply those operations. Semantic pruning, typedTypes, global
canonicality, mutation histories, selected-current protection, cached
scheduling, phase4, resources, practical width, runtime/solver correspondence
and convergence remain open. H23 and older constructor/equality targets stay
queued. The retained source plan describes the wrapper; it is not a proof of
these remaining obligations.

H6 constructed_node_calls remains strongest combined under its covered closed
construction, valid initial cache, original allocations, finite rounds and
empty inherited-payload conditions. The full goal stays ACTIVE and incomplete.

No Haskell source changes. FINDINGS retains the external repair index first.
All six recorded Haskell fixes are on imported main. Earlier proofs,
counterexamples, repairs, marked drafts and the optimized interned core remain.
This note precedes evidence creation and the authorized push.
