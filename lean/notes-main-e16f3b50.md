# GHC normal-key fit filtering at main e16f3b50

Source `e16f3b50` is merged at `50f21a5f`. The source range from `2ca1644c`
changes ten files in cfta-ghc. It adds `Data.CFTA.GHC.NormalForm`. Core
automaton, equality, native, enumeration, template, and Sized bodies remain
unchanged. Full library scope remains active.

## Completed fit-filter source model

`SourceGhcFitNormalForms` follows actual streamFits acceptance branches.
Inputs are completed checked Walk fits. State retains literal seen-normal
membership, merged count, and explicit part-check/callback host effects.
Events retain the source call order.

A disabled filter bypasses normal lookup and passes dropsArgument=False.
Unknown normals insert no key and are delivered with dropsArgument=False.
A duplicate known key increments merged, continues, and calls neither
part checks nor the caller. A fresh key is inserted BEFORE both later
calls, including a callback that stops. No callback rolls this insertion
back. The drop flag is exactly a missing required leaf of a known normal.

The finite attempted-fit driver stops at the first False callback and
retains the exact undemanded suffix. Consumed fits equal delivered callbacks
plus merged fits. The concrete synthesize adapter records each callback
before its quota test. Only fits that do not come last count toward that
quota. Final output restores chronological order, stable-partitions the two
comesLast flags, and applies signed take. Nonpositive limits can record one
callback before stopping, but the returned list is empty.

Known completed key equality defines an explicit equivalence domain.
Unknown keys are outside it. This proof does not establish Haskell
contextual equality, normalization, or synthesis completeness.

## Normalization and GHC boundaries

The source evaluator and quotation have no reduction fuel. The sizeAtMost
20000 test bounds demanded output nodes. It does not bound work before
each node, Core translation, runtime, or termination. A finite-fuel
normalizer would not be this source function.

The source documents that pair eta is wrong for undefined. Equal normal
keys therefore do not imply general Haskell contextual equality with seq
or partial values. A semantic theorem needs the intended total/extensional
domain or the explicit completed-key quotient. No production repair is
included for this intentional source rule.

Core scoping, typing, erasure, constructor metadata, environment indexing,
unfolding lookup, actual Walk output, deadlines, Set/IORef operations,
exceptions, plugin rendering, and runtime forcing remain separate bridges.
normalFormsOf keeps the last successful duplicate candidate-text binding.
The typechecker leaf map keeps the first binding. Arbitrary public duplicate
labels need a coherence or uniqueness domain.

HoleFits can discard a fit already supplied by GHC after streamFits has
inserted its normal key. That fit can suppress a later equal-key fit.
The completed filter theorem makes no completeness claim for displayed fits.

## Validation

Required Nix strict build includes all packages, tests, and benchmarks with
-Werror. It passes. All six suites pass: 22 decision-model, 157 refinement,
316 unit, 18 GHC fit, and 210 generator examples, plus golden checks.
The total is 723 examples. Fourmolu passes all six changed Haskell files.
Cabal-gild passes all four active Cabal files.

The focused Lean filter build passes. All 22 public axiom probes and two
kernel fixtures pass. The aggregate audit passes 2,114 jobs and 52,819
dependency checks with only the permitted Lean foundations. Evidence uses
`/tmp/mcfta-normal-form-*`. Existing proofs, repairs, repros, and drafts remain.
