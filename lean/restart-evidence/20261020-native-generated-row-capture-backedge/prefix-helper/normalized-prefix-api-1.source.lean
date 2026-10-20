import Lean
set_option Elab.async false
open Lean Meta Elab Term in
/-- Retain a normalized value and the kernel-checked equality from its reduction. -/
elab "checked_cbv% " value:term : term => do
  let original ← instantiateMVars (← elabTerm value none)
  let (normalized, equality) ← match ← Lean.Meta.Tactic.Cbv.cbvEntry original with
    | .rfl .. => pure (original, ← mkEqRefl original)
    | .step normalized equality .. => pure (normalized, equality)
  let valueType ← inferType original
  let predicate ← withLocalDeclD `checkpoint valueType fun value => do
    mkLambdaFVars #[value] (← mkEq original value)
  mkAppOptM ``Subtype.mk #[some valueType, some predicate, some normalized, some equality]

private def first : { value : Nat // 2 + 3 = value } := checked_cbv% (2 + 3)
private def second : { value : Nat // first.val + 7 = value } := checked_cbv% (first.val + 7)
private theorem checkpoint_sound : 2 + 3 + 7 = second.val := by
  rw [first.property]
  exact second.property
#print axioms checkpoint_sound
