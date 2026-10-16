# Main 6baa0e25 source refresh

Main `6baa0e25` is merged at `416f0f39`.
The refresh changes eleven source, test, and package files.
The equality, interned constructor, and Sized implementations are unchanged.
All earlier proofs, counterexamples, repairs, and marked drafts remain.

## Conditional measure evaluation

`Gen.Refinement.evaluateTerm` evaluates Lit, Neg, Add, Sub, Mul, and Ite.
It sends every other whole term unchanged to the supplied leaf callback.
It does not recursively evaluate unsupported application, division, modulo,
or cast syntax. Ite evaluates its condition, then only its selected branch.

`evaluateFormula` handles Top, Bottom, And, Or, Not, and all six integer
relations. And and Or traverse all Option results before the Boolean fold.
A missing later result remains missing after a decisive earlier Boolean.
Quantifiers return Nothing without evaluating their bodies.

`SourceCurrentMeasureEvaluation` follows these literal cases.
Mutual recursion proves soundness under integer interpretation laws and
agreement of successful leaf observations with the denotation.
The result equation observes the defined algorithm. It is not an assumed
correctness or completion oracle. Finite syntax and a total callback give
structural completion. Arbitrary Haskell callback termination stays separate.

The component also proves agreement for ite, smaller, larger, smart negate,
absolute value, and signum. These laws use unbounded Integer arithmetic.
Actual expression sorting and leaf-map extraction remain adapters.

## Conditional folding

`foldConditionals` visits And, Or, Not, and Atom formulas.
It leaves quantifier bodies unchanged. Its term worker visits Ite, Neg,
Add, Sub, and Mul. Other whole terms remain unchanged.

For Ite, the source tests the original condition with a callback that always
returns Nothing. A known condition folds only its selected branch.
An unknown condition folds the condition and both branches.
`SourceCurrentMeasureFolding` proves full denotation preservation by mutual
recursion under the integer laws. It also proves the corresponding existing
FormulaLowering interpretations. It assumes no fold-equivalence law.
SMT serialization, process execution, and solver correctness remain separate.

## Measure and derived-field diagnostics

Named measuredBy now evaluates the measure term directly from known named
child measures and singleton integer child points. Plain measuredNode
substitutes defining terms, folds conditionals, then extracts onlyPoint.
InexactMeasure retains the constructor, optional measure name, and child
positions. The concrete substitution, label-map, and extraction pipeline
still needs source correspondence.

childReads is a static syntax scan. It includes the condition and both Ite
branches. It also scans unsupported arithmetic and quantified bodies.
The missing-child list is not a minimal dynamic trace. An unsupported
operator can fail with no missing child position.

Derived-field checking rejects a read field only when its type has no
registered atom and none of its constructor alternatives has any measure.
This check does not establish the requested named measure for every
alternative. Later InexactMeasure remains necessary. Type discovery, SCC
construction, annotation binding, and diagnostic precedence remain frontend
proof targets. No independently verified source defect was found here.

## Validation

The pinned full Lean audit passes 2,220 jobs and checks 54,792 theorem
dependencies. Only permitted foundations and the existing unused-input
warning occur. Seventy-four public axiom probes and 43 kernel examples pass.

Strict Nix build passes all libraries, executables, tests, and benchmarks.
All six suites pass: 755 examples plus the golden suite.
Fourmolu passes eight changed Haskell files. Cabal-gild passes four packages.
No production source repair was added in this increment.

Evidence uses `/tmp/mcfta-memo-target-workers-*` and
`/tmp/mcfta-measure-choice-*`. The full-library goal remains active.
