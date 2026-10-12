# Argument builders and transition arity

`GuardBuilders` models the standard recursive instances in
`Data.CFTA.Refinement.Guard`. A builder's function type fixes its number of
arguments. `arity_exact` proves that repeatedly supplying the source probe
cannot change this number. `guardArgumentCount_exact` includes the distinct
raw-guard case, which supplies no arity requirement.

`buildFrom` applies the builder at consecutive positions. Its list-application
theorem derives the complete ordered argument list. `supplied_path` connects
each list entry to the actual singleton child path. The construction theorem
applies to the guard, contract-formula, and measure-term instances through
their supplied argument constructor. It does not certify user-defined
typeclass instances that violate the standard recursion.

`atoms`, `targets`, and `indices` follow the source `contractReach` traversal.
They descend through `Not`, `And`, `Or`, and `Substitute`. They read only the
first child index of each `Holds` target. `indices_exact` proves that every
index comes from such a target and that none is omitted. `reach_within`
derives the maximum-index check from those individual bounds.

`transitionCheck` preserves both checks and their error order.
`transition_success` characterizes success exactly. The reported mismatch
retains the actual child count and the offending requirement.
`function_error_first` proves that function arity takes precedence over
contract reach. Raw `Same` and `Entails` paths impose no contract-specific
arity condition. Negation and substitution do not remove a Holds arity check.

These are construction rules. They are not a semantic emptiness test. For
example, a negated `Holds` at absent child 1 still fails this constructor's
arity check when there is only one child. The general guard evaluator has
its separate missing-position semantics. The kernel example preserves this
distinction and the exact reported arity.

This model uses nonnegative unbounded positions. Source `Natural` to `Int`
conversion and signed machine arity arithmetic require representable input
bounds. The signed-path validation modules describe negative positions, but
this module does not silently extend its results past the source word limit.
`ContractAssembly` proves the `contract` builder's conjunct flattening,
free-name selection, compact renumbering, and resulting arity gate. Whole
automaton validation remains the `RefinementValidation` result.

The pinned Lean target passes all five build jobs. No Haskell source changed.
