# Independent review of the changing-capture binder example

Frozen on 2026-10-18. Reviewed source: `SourceCurrentChangingCaptureBinderExample.lean`, SHA256 `a6db07351b2c948121f63ee62115057ff37fd567858f0d7efbfdd6de7417cd15`.

## Finding

No material proof or contract issue was found. This is a concrete positive example at one actual Ready reader. It does not prove the general changing-capture binder clause.

## Actual source and reader

Lines 24-51 define one closed source, an ordinary nullary capture `a`, a physically distinct raw closed unused-Mu capture `b`, and two outer used Mu values `x` and `y`. The same open source `expression` takes `a` or `b` as its external capture. Actual warm source calls at the final reader return `x` and `y` respectively. These equations are computed from the code, not supplied as input assumptions.

The source construction is a literal checked `build ... = .done ...` equation. `constructed` derives the initial Ready heap. The local `effect` theorem obtains every Mu unfolding from `StoredReconstruction.execute`, initial Ready, source availability, and the exact sparse self environment. Four outer/inner unfolds and one capture-wrapper unfold produce the final reader. Their actual `Keeps` receipts derive its Ready state and retain the initial captured values. There is no future completion callback, foreign reader, corrupted heap, or desired observation premise.

The private and public final statements retain initial source construction, Ready reader, base-to-reader Keeps, availability of both captures and both outer results, physical distinctness, both exact warm source calls, exact nested capture links, and used-local facts for both outer and both nested Mu values. The public call expressions are open source syntax. Their concrete returned outer values come from the closed source construction. This example does not establish preparation for arbitrary open resident Mu values.

## Simulation

The relation contains equality and five explicitly listed unordered pairs: captures, outer Mu values, outer unfolded nodes, nested Mu values, and nested unfolded nodes. This yields ten oriented non-equality cases. Equality uses the existing local reflexive clause.

The capture `b` unfolds to `a`. The forward capture clause transports literal observations through this actual reachability step. The reverse capture clause matches that step with the identity endpoint `a`. Each Mu clause uses the exact warm unfold equation to match its single epsilon successor. The ordinary clauses retain symbols, full Bool guards, and ordered child pairs. The outer recursive row pairs its self and nested child. The nested recursive row pairs its self, captured outer Mu, and corresponding external capture. Reverse rows reverse every child pair. No desired all-depth observation fact is used to construct these clauses.

`OpenPreorderSimulation.same` then derives all finite observations for both capture and outer-result pairs. `OpenObservationLanguage.directed` derives exact guarded finite-tree language for every Bool guard interpretation and term. Physical Empty agreement is not inferred or claimed by this public statement.

## Nonvacuity and limits

The explicit acceptance proof follows the actual outer unfolding to nullary row symbol 2 with true guard and empty children. It proves acceptance of `node 2 []` under the Bool-as-truth guard interpretation. Thus the language result is not obtained only because both accepted languages are empty. Both outer and both nested binders are used. Their corresponding nested values and outer values are physically distinct.

The finite relation is checked for this example. It is not a general source-generated relation, a general binder induction rule, an all-open-Mu support theorem, or a termination result. No Haskell defect is asserted.

## Evidence and counts

Selected strict: `changing-capture-direct-4`, exit 0 and literal zero-byte log. Selected canonical: `changing-capture-canonical-1`, exit 0, 611 jobs, warning-free. Selected full public group: `changing-capture-public-1`, one full declaration/proof/axiom report, all eight options, no omissions, and only the standard three axioms. The public theorem forwards a private checked witness with a byte-identical statement.

This review reuses these existing checks. It runs no new Lean build. It adds zero public, constructed, or auxiliary pairs and reuses one public pair. Root-owned failed attempts remain in the owner package. This review pins only the final selected receipts and frozen source dependencies. It does not pin mutable root helpers, peaks, or reports.
