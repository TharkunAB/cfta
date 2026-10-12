# Full current guard pruning over specialized graphs

`NoConflictKnown.lean` proves that the source's count-based no-conflict test
implies an empty actual-identity ambiguity set. A non-leaf actual keeps its
own sparse representative. A leaf representative is a leaf. Each ambiguity
witness therefore gives two distinct representative/name values with the
same name. The source count is at least two, so both values cannot escape
the conflict filter. This proof uses the actual representative search and
count operation. It does not assume that conflicts detect ambiguity.

`FullGuardPrune.lean` connects the complete current Guard evaluator to
ObservationGraph's finite-plan specialization and PruneCandidates' source
check loop. The representation adapter converts graph label fields to the
evaluator's name/refinement pairs. It proves that the conversion commutes
with path lookup and preserves root shape.

The graph model retains signatures. `queryObservations` reconstructs their
required information. Refinement-only entries use an arbitrary unused name
and Mixed shape. Symbol entries retain their exact name, refinement, and
leafness. `signature_reads` proves that these observations supply every
current Guard read. Actual and formal positions always use symbol entries.
The arbitrary name cannot affect a conflict-free query. The preceding read
agreement theorem also relates this reconstructed view to the complete
observations retained by the Haskell candidate's first transition.

`view_decided_exact` proves equality between each decided conflict-free
variant query and complete public guard evaluation for every term accepted
by that variant. It uses the derived empty-ambiguity result. It does not
assume an exact sparse guard oracle or a complete solver.

`prune_exact` composes this result with actual graph specialization coverage
and the source candidate check loop. On every successful return, the union
of the returned graph fragments contains exactly the original graph terms
confirmed Yes by the complete current Guard evaluator. The proof covers
every Guard constructor, list connective, and nested substitution. Unknown
and error branches retain their source control behavior.

The restriction is explicit and executable: every generated variant's source
conflict list must be empty. It is not a generic preservation postcondition.
The unrestricted conflicting-fresh-name and ambiguous-alias transports remain
open, as documented in notes-source-guard-plan.md. The theorem uses the
proved graph representation. Concrete Haskell interner, binder, equality
narrowing, and cache adapters remain the separate PruneSchedule obligations.
The result is equality of the complete evaluator's confirmed term language;
logical interpretation additionally uses the explicit solver soundness
contract.

Validation: `lake build MicroCFTA.FullGuardPrune` builds both modules with the
pinned toolchain. There are no proof placeholders or new axioms.
