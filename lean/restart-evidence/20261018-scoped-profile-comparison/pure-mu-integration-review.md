# Pure stored Mu profile integration

Date: 2026-10-18 19:09 CEST.

This evidence-only component adds one constructed theorem. It adds no production declaration. The selected strict source is `pure-mu-integration-direct-6.source.lean`, SHA256 `e6904994a17b6bc2366d78b3b62195866337bde8f8a86b3f0a14df4b61810fc5`. The full public group is `pure-mu-integration-public-1`, SHA256 `fb5ddad8c0273a726c9bce40a6f1ac89434a95c8451a8724aa8bee595cf063e1`.

The imported production modules are `SourceCurrentStoredProfilePlan` (SHA256 `2897df6cba129b087268d846e8e52af2c36760a7cb35a8037cb05ebb4837d49b`) and `SourceCurrentStoredMuProfileReduction` (SHA256 `2e63b1f530791ad85bf8f3a943f00d866c603d6585eae2f4a5ca52794aa310f9`). No production module is changed.

## Actual source and derived premises

The literal source is three nested raw binders ending at variable 2. It builds from the empty heap. The fixture checks the literal successful result and derives Ready and root availability from the source construction theorems. It selects the middle Mu through the original root's actual child relation. This selected Mu is OPEN and its original stored body is itself a raw Mu. The inner raw body refers to the outermost source binder. Thus the new plan calls process a nested stored Mu and retain the original outer reference.

The selected middle local and the nested local are unused. The outermost source binder is used. This is not a fixture for a general used-local binder comparison. The theorem does not claim a nonempty finite accepted language.

The candidate payload contract is proved locally for ALL outer profile assignments and ALL local profiles. The actual ordinary probe equals the stored body in this example. The original body's sole free name differs from both the selected reserved name and the selected ordinary name. `StoredProfileFunction.congr` therefore removes the two irrelevant local shadows. The fixture derives Correct; it does not receive it as a hypothesis.

## Production API use

The chosen outer assignment maps the actual outer reference to `some [101,102]`. It maps every other name to the opaque profile `none`. The target denotation is exactly the visible profile `some [101,102]` despite the original raw source constructor. The enclosing root is closed, and the fixture also invokes the literal `StoredProfileFunction.closed` shortcut for that original closed record.

The fixture invokes `StoredProfilePlan.recapture` with an enlarged capture list containing an extra Empty value. It derives capture availability from the actual stored body. It invokes `StoredProfilePlan.rebind` directly with the selected reserved reference and the later chosen marker. Both calls use the actual reader's coherent records. Constructor cases explicitly identify independent generated match functions; the proof does not infer these equations from matching printer text.

`StoredMuProfileReduction.fresh_marker` chooses a marker absent from the finite list of assigned ORIGINAL body leaves. This produces the exact leaf freshness premise for `open_denote` and `open_correct`. Both production reduction theorems are invoked on the actual selected payload. `open_correct` consumes the candidate Correct proved above. The exact result retains marker erasure and the ordinary name shadow. No future execution or desired profile result is supplied.

This component tests pure denotation, not actual substituted result construction. Its only literal execution premise is proved for the source build. It does not equate stored substitution of an open raw record with the original raw source syntax interpreter. It has no general publication, causal cache invariant, language, termination, or Haskell correspondence claim.

## Validation and retained attempts

Strict attempt 6 terminates with a literal zero-byte log. The one selected public theorem has the exact full statement of its private checked proof. The full group prints the complete public statement, the exact alias proof, and its axiom report. The hardened checker passes all eight settings, no omissions or printer failures, and only the standard permitted axioms. No auxiliary Claim hides the statement. The wrapper records 4 GiB effective memory.max/high, zero swap, 5 minutes, and pinned Lean 4.34.1. This component has no production canonical build of its own; it imports the already canonical production modules and kernel checks the standalone fixture.

Attempts 1–4 are failed local elaboration attempts. They are retained. Attempt 5 is a successful minimal source with two raw binders. It is unselected because attempt 6 adds a nested raw Mu to the stored body. No old or failed artifact is changed.

The component manifest has an explicit allowlist. It excludes the frozen scoped-input component, root mutable wrappers, global selections, baseline files, and documentation. No older component is changed.
