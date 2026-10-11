# Complete formula operations after the substitution repair

The current source repairs the quantified substitution defects found at `d7f7c11`. The earlier `FullSyntax` algorithm remains a historical regression model. The new modules model the repaired source and all current syntax constructors.

## Source behavior and repair

`Formula.substituteChecked` retains simultaneous replacement, first matching entries, identity-entry removal, and binder shadowing. A nullary `App name []` denotes the named value and accepts the same replacement as `Var name`. A nonempty `App name arguments` accepts a `Var` replacement for its head. A non-name head replacement returns `UnsupportedFunctionReplacement name replacement`. The existing `substitute` API unwraps success and raises a descriptive error on that unsupported case.

This boundary follows the syntax. `App` stores a `Name` as its head. It cannot represent applying an arbitrary function-valued `Ite`, cast, or other term. Silently ignoring such a replacement would not implement simultaneous substitution. The checked API exposes the failure. This repair does not add higher-order application syntax.

Binder preparation removes shadowed entries and computes the free names of the remaining replacement terms. Captured binders receive fresh names. Repeated occurrences of one bound name receive the same fresh name. This preserves the effect of the last binder in the list. Fresh targets avoid replacement free names, body free names, original binder names, and active replacement keys. The source uses unbounded `Integer` indices for its fresh stream.

The existing `Refinement/SubstitutionSpec.hs` now contains eight focused regressions. They cover the Z3 capture case, nullary application replacement, simultaneous function-head renaming, explicit unsupported replacement, shadowing, captured function binders, repeated binders, and duplicate identity entries. `repro/FormulaCapture.hs` checks the repaired closed formula and equal Z3 verdicts `No` and `No`.

## Complete substitution theorem

`FormulaSubstitution.lean` transcribes the checked algorithm and its error branch. `FormulaSemantics.lean` proves free-name extensionality for every constructor under arbitrary primitive interpretations. This includes both sorted quantifiers, function names, division, modulo, casts, and conditional terms.

`FormulaBinders.lean` derives the properties of actual binder preparation. It proves fresh-target exclusion, uniqueness of fresh targets, injectivity on original body and binder names, and assignment transport for prepared substitutions. The universal and existential transport theorems preserve binder order and sort domains. They support repeated binder names.

`FormulaCorrectness.term_semantics` and `formula_semantics` prove the recursive operations. `checked_semantics` covers the public checked API. For each successful result, its meaning in an environment equals the original formula's meaning under simultaneous replacement in that environment. Replacements are evaluated in the original environment. Identity entries are removed before lookup, as in the source.

The theorem has one application law: `apply value [] = value`. It has no no-capture, unique-binder, fragment-membership, or pre-assumed alpha-equivalence premise. Primitive arithmetic, casts, nonempty function application, and sort domains remain arbitrary. `checked_absent` derives that replacement keys absent from the free names cannot change the formula's meaning, even when their replacement terms cause binder renaming. `function_replacement_rejected` checks the unsupported nonempty-head case.

## Target lowering and sorts

`FormulaLowering.lean` transcribes all cases of `LiquidFixpoint.toFixpoint`, `termToFixpoint`, and `sortToFixpoint`. Its target types give separate value and predicate views of the emitted `Fixpoint.Expr` constructors. They do not claim to model every expression that Liquid Fixpoint accepts.

The target application tree follows `eApps`, a left fold of binary `EApp`. The function-sort tree follows `mkFFunc 0`, which builds right-nested `FFunc` arrows. These helper definitions were checked in the installed Liquid Fixpoint `0.9.6.3.7` source archive. A zero-argument function sort lowers to its result sort. `lower_raise` proves exact representation of every target sort. `normalizeSort_idempotent` proves the stability of the resulting source sort normalization.

`sourceModel` derives a source interpretation from target primitives. Function application folds the target binary application operation. Casts and binder domains use the actual lowered sort. `term_lower` and `formula_lower` prove semantics for every source constructor. `sourceModel_nullary` derives the substitution theorem's application law from the actual lowering. `checked_lower` composes successful checked substitution with target lowering.

The target model leaves the meaning of real arithmetic, division, modulo, casts, and function values explicit. It does not replace these operations with integer fixtures. It proves translation composition for their supplied meanings, including negative literals and zero divisors. It does not choose or certify the external SMT theory's behavior on undefined or ill-sorted terms. The source API exposes a raw AST and does not perform sort checking here.

## Full-syntax simplification

`FormulaSimplify.lean` follows the source's exact simplification cases. It simplifies Boolean structure and recognized atoms. It leaves quantifier bodies and arithmetic terms unchanged. The asymmetric conjunction and disjunction wrapper behavior remains intact.

`simplify_semantics` covers every source formula. It assumes six explicit primitive relation laws: equality, non-strict order reflexivity, disequality irreflexivity, and equality/disequality of distinct integer literals. It does not assume simplifier correctness as a premise. Sorting uses an arbitrary comparison parameter. Preservation holds for every comparison, so the semantic proof does not require an assumption that sorting has the desired result. Structural duplicate removal and conjunction membership are proved.

`FormulaOrder.lean` transcribes the complete derived comparison. It includes all constructor tags and the lexicographic order of fields, arguments, sorts, and binders. `sort_eq`, `term_eq`, and `formula_eq` prove that comparison equality is exactly structural equality. Thus comparison introduces no extra equality classes for duplicate removal. `FormulaOrder.simplify_semantics` instantiates the simplifier with that comparison. The model does not verify the Haskell ordered-set implementation or its internal balancing. It does not prove a separate full transitivity theorem for the transcribed comparison.

`conjunction_semantics`, `disjunction_semantics`, `implies_semantics`, and `iff_semantics` cover all exported smart constructors. `simplify_lower` composes simplification with target lowering under the same primitive relation laws.

## Validation and remaining boundary

`lake build MicroCFTA.FormulaOrder` checks all seven new modules with the pinned Lean toolchain. The strongest theorem dependencies contain only `propext`, `Quot.sound`, and `Classical.choice`. There are no project-specific axioms or `sorry` proofs. The final Nix check runs `cabal test microcfta:unit-tests --test-options=--match=formula`: all ten selected examples pass. The repaired `FormulaCapture.hs` probe also passes. Fourmolu formats all changed Haskell files.

These are source transcriptions with complete semantic proofs for their stated operations. They are not extraction or verification of the Haskell executable. The remaining boundary includes raw-AST sort validation, full comparison order laws and container implementation invariants, text/hash representation, the Liquid Fixpoint serializer, solver declarations and IO, and the external solver's primitive theory. Arbitrary higher-order term replacement cannot always succeed with the current named-head application syntax; the checked API reports that limit. `renderFormula` and `renderTerm` are presentation functions. The library does not export a parser or a rendering round-trip contract, and this model does not assign semantics to their output text.
