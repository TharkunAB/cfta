# Core formula correspondence

Current executable definitions use `__cfta_bound_` after PR #129.
The quoted historical result below retains its old `__microcfta_bound_` name.
Source paths below use the current `cfta` directory.

`MicroCFTA/CoreFormula.lean` models the integer fragment of `cfta/src/Data/CFTA/Formula.hs` from `55fe503`. `MicroCFTA/FullSyntax.lean` models the complete syntax after `9ad319d`, now included in `microcfta` at `d7f7c11`. The core fragment remains the syntax that the automata construct. It evaluates unbounded integers and conditional terms. It implements the source constructor order and the lexicographic comparison of fields.

The checked substitution theorem covers arbitrary formulas and terms. Replacements apply simultaneously. The implementation removes identity entries before it selects the first matching entry. For example, `[(x, Var x), (x, Lit 1)]` replaces `x` with `1`. Replacement terms do not receive the same substitution again.

The checked simplifier theorem preserves the truth value under every assignment. Its definition keeps the source branch order, tautology and contradiction tests, conjunction flattening, duplicate removal, sorting, and asymmetric disjunction rules. The conjunction and disjunction theorems give exactly the intersection and union of accepted assignments. The implication and equivalence theorems give their usual Boolean meanings.

The simplifier is not idempotent. For an atom `p` that neither detector recognizes, `Or [Bottom, p]` simplifies to `Or [p]`. The next simplification gives `p`. The proof records this behavior. Structural formula equality is not semantic equivalence.

The free-name proofs establish exact syntactic membership, absence of duplicates, and independence from values assigned to other names. The model represents the free-name set as a list. It does not model the iteration order or hashes of the Haskell hash set. Text rendering and Haskell runtime representation remain outside the proof.

`MicroCFTA/CoreLattice.lean` connects this complete syntax to `MicroCFTA/LatticeFormula.lean` and `MicroCFTA/LatticeLinear.lean`. The translation maps all six relations. Formula lists use the source traversal and right fold. Successful compilation gives exactly the zero-or-one indicator of the total core semantics. The simplifier and the compiler give the same score when both parses succeed.

The lattice backend accepts a restricted arithmetic fragment. It rejects every `Ite`, an unknown name, and a product with variable coefficients on both sides. A checked example describes exactly `x = 1` with `Ite Top (Lit 1) (Lit 2)`, but its lattice parse fails. This is a supported-fragment limit. It is not an unsound simplifier result. The lattice error model preserves the error category and name. It does not preserve the offending term payload of `NonLinearTerm`.

Validation: `lake build MicroCFTA.CoreLattice` builds both modules with the pinned Lean toolchain. The audited theorem dependencies contain only Lean's standard `propext`, `Quot.sound`, and `Classical.choice`. They contain no `sorryAx` or project-specific axiom. The source correspondence is an explicit transcription and composition of proofs. It is not extraction or verification of compiled Haskell code.

## Extended syntax and current source

`FullSyntax.ValueSort`, `Term`, and `Formula` include every current constructor. `Holds` gives proposition-valued semantics to quantifiers. `Interpretation Value` supplies sort domains, integer literals, arithmetic operations, relations, application, and casts. The model does not impose a type checker or certify a real-number algebra. It does not certify Liquid Fixpoint or Z3.

`integerModel` supplies exact integer arithmetic for the accepted lattice fragment. Its Boolean domain uses `0` and `1`. Its real and function sort domains are empty. A nullary application returns the named value. Other applications return zero, and a cast returns its input. Division and modulo use Lean's integer operations. These latter choices are interpretation parameters instantiated for the historical proof fixture. They are not claims about Liquid Fixpoint casts, real arithmetic, function interpretation, negative divisors, or division by zero. `signed_success_is_core` proves that every successful source lattice compilation excludes all these extended forms. Thus none of these fixture choices enters the lattice soundness and completeness theorem. The current target-induced interpretation in `FormulaLowering.sourceModel` models function application and sort lowering separately.

`embedFormula_holds` proves that the full syntax preserves the complete existing integer semantics. `signed_embed` proves that its lattice translation preserves the existing compiler result. `signed_success_is_core` derives an exact core formula from each successful full-syntax compilation. The source rejects `App`, `Div`, `Mod`, `Ite`, and `Cast` as `NonLinearTerm`. It rejects each quantifier as `UnsupportedFormula`. The model preserves these categories but omits the offending syntax payload in errors.

The historical substitution model includes shadowed-entry removal, capture detection, fresh-name allocation, and simultaneous replacement. `freshNames_length`, `freshNames_nodup`, and `freshNames_avoids` prove that its finite prefix of the fresh stream is sufficient, distinct, and outside the forbidden names. `prepareBinders_length` proves that historical binder preparation retains every binder. The repaired source uses unbounded `Integer` fresh-name indices, which match the Lean supply. Hash iteration order remains a representation boundary.

## Historical substitution defect and repair

The source at `d7f7c11` did not rename application heads when it renamed a binder. Use `Forall [(x, IntSort)] (Atom Eq (App x []) (Lit 0))` and replace the absent name `unused` with `Var x`. The old result binds `__microcfta_bound_1` but still uses `App x []`. The original formula is closed and false. The old result has free name `x` and is true under ambient `x = 0`. A nullary application translates to the named value, so the example uses only an integer quantifier. It does not require higher-order quantification.

`FullSyntax.capture_substitution`, `capture_freeNames`, and `substitution_not_sound` retain the exact historical result and semantic change. The repaired source replaces the nullary head and renames nonempty application heads when a replacement is a name. It rejects other nonempty function-head replacements through the new `substituteChecked` API. At `092b56d`, the total `substitute` wrapper retains that unsupported head and substitutes its arguments. `FormulaTotalSubstitution` proves agreement on checked success and records the semantic limit of the total fallback. Repeated binders now share one fresh name, so the last binder still shadows earlier occurrences. `lean/repro/FormulaCapture.hs` now checks the repaired result, absence of free names, and equal Z3 verdicts `No` and `No`.

`FormulaCorrectness.checked_semantics` proves complete successful substitution correctness for the repaired algorithm. It has no no-capture or unique-binder premise. `FormulaSimplify.simplify_semantics` proves full-syntax simplifier correctness under explicit primitive relation laws. `FormulaLowering.formula_lower` proves the complete source-to-target lowering under explicit target primitive semantics. See `notes-formula-correctness.md` for the theorem boundaries and source correspondence.
