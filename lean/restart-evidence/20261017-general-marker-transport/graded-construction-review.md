# Graded actual construction

Status: PASS for the bounded component.

The production source is `lean/MicroCFTA/SourceCurrentConstrainedCapConstruction.lean`.
Its final SHA-256 is `fb01def2398ea4350ce869120bab16956ce245c54942041e0ccef2e71ce6bc25`.
It has 300 lines and six public declarations. No older source changes are part of this component.

## Input contract

`Typed`, `ManyTyped`, and `EdgesTyped` at lines 24, 33, and 39 are pure checks on literal syntax and its actual lexical environment. A variable checks only its selected complete value. A missing slot denotes Empty. Unions retain the current cap depth. Ordinary row children use depth minus one. The row guard must satisfy the local predicate only at depth zero.

A binder requires its body to pass the zero-depth check for every fresh reference prepended to the same captures. This check permits unused constrained captures. It does not permit a binder to use a constrained capture as a hereditary value. The input contract contains no returned value, future heap, future callback, completion, or result law.

## Actual producer

`build`, `buildMany`, and `buildEdges` at lines 143, 229, and 257 use the existing repaired fresh executor. They return the existing `HereditaryConstruction.Checked` contract. That contract retains `MuStored` at the exact complete or pending stopping state and certifies each actual successful result.

The node and union branches use actual earlier child returns and the existing physical verification theorem. Their literal constructor work derives the output cap from those same returned children. The row branch retains the complete original guard and actual ordered children.

The binder branch proves the actual Depth probe, actual fresh ordinary probe, and actual allocated-body callback at depth zero. Each actual result therefore has a hereditary annotation. The private request helper installs that candidate's conditional annotation law before complete first-writer readback. An earlier winner uses its own stored law and exact probe readback. A candidate's annotation does not certify a different earlier body.

The private checked-outcome and request helpers repeat the existing hereditary argument because those helpers are private in the older module. No older file was changed. No global hereditary heap premise was introduced.

## Validation

`graded-construction-direct-2.log` is the final strict absolute-path check. It exited zero and has zero bytes. All linters were enabled. Direct attempt 1 and its exact source are preserved. It failed only because the mutual `Typed` equations needed explicit unfolding.

`cap-construction-build.log` is the canonical exit-zero build. It completed 1083 jobs. Its warning belongs to the older `InternedFreshOrdinaryClosedCompletion.lean` dependency. The new production module has no warning.

`graded-construction-public-1.log` contains six imported axiom/full-signature pairs. Explicit names, proofs, universes, deep terms, and ten million printing steps were enabled. No error, warning, or `sorryAx` occurs.

`graded-construction-kernels-6.log` contains two clean imported pairs:

- `nested_typed` verifies a literal ordinary plan with two nested binders for an arbitrary mixed capture list. The subplans use only their actual fresh local references.
- `initial_mixed_nested` first constructs a false-guard ordinary capture from empty caches. It proves that this actual value has Cap 1 and is not hereditary. It derives the actual complete semantic context, depth heap, coverage, availability, and causal Mu store. It then independently constructs the second plan with two nested binders while that constrained capture remains unused. The same actual second result has Cap 1 and the same final heap has `MuStored`.

The second construction executes literal nested syntax. It is not a stored-encode shortcut that immediately returns a closed capture. The test supplies no completed result or future callback. Kernel attempts 1 through 5 and their exact sources remain preserved. Those failed probes contain diagnostic `sorryAx` placeholders; the final production and final imported logs contain none.

## Boundary

This theorem verifies all outcomes of the actual graded constructor. It does not assert that every arbitrary warm constructor call completes. The integration kernel constructs its two successful calls from the existing initial semantic completion theorem. The separate stored-substitution bridge can derive its own complete return from initial Ready.

This component does not close general mixed native intersection or general selected reduction. Native optional binding still needs the occurrence and warm-store arguments for its actual branch. There is no Haskell change.
