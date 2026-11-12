import MicroCFTA.SourceSynthesisProgramEnumerationRoles
import MicroCFTA.SourcePruningEnumerationAssimilation
import MicroCFTA.SourcePruningEnumerationIncomingNode
import MicroCFTA.EnumerationReferences

/-!
# Program roles through actual unmarked-slot finish actions

The finish actions write unmarked raw slots and update ancestry.
The supplied buckets avoid all marked Program classes.
No safety claim is made for the intermediate unassimilated state.
-/
namespace MicroCFTA.SourceSynthesisProgramRolesAssimilation
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationReferences
open InternedConstructorTemplates SourceSynthesisProgramEnumerationRoles
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "NativeHeap" => InternedConstructorTemplates.State Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
variable {valid : Constraint → Prop} {literal : String → Symbol}

private theorem same_fields (heap : NativeHeap) (before after : Core) (marked : Nat → Prop)
    (roles : ProgramSlots valid literal heap before marked)
    (counter : after.counter = before.counter) (forest : after.representatives = before.representatives)
    (values : after.values = before.values) :
    ProgramSlots valid literal heap after marked ∧
      ∀ uv, marked uv → EnumerationDriver.Protected uv before after := by
  have transported : ProgramSlots valid literal heap after marked := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro uv known
      rw [counter]
      exact roles.bounded uv known
    · intro uv known
      rw [forest]
      exact roles.roots uv known
    · intro uv known payload member sc listed same
      have old : payload ∈ before.values := by simpa only [values] using member
      exact roles.incoming uv known payload old sc listed (by simpa only [forest] using same)
    · intro uv known
      obtain ⟨payload, stored, role⟩ := roles.stored uv known
      exact ⟨payload, by simpa only [values] using stored, role⟩
  refine ⟨transported, ?_⟩
  intro uv known
  exact ⟨by rw [values], transported.roots uv known, fun _ => by rw [forest]⟩

private theorem write_roles (heap : NativeHeap) (before after : Core) (marked : Nat → Prop)
    (roles : ProgramSlots valid literal heap before marked) (slot : Nat) (payload : UVarValue Symbol)
    (unmarked : ¬marked slot)
    (avoids : ∀ uv, marked uv → InputsAllowed (fun target => ¬UnionFind.SameClass before.representatives uv target) (references payload))
    (actual : Success (setValue slot payload) before () after) :
    ProgramSlots valid literal heap after marked ∧
      ∀ uv, marked uv → EnumerationDriver.Protected uv before after := by
  have shape : after = {before with values := before.values.set slot payload} :=
    (EnumerationDriver.modify_success _ _ _).mp actual
  have stores : ∀ uv, marked uv → after.values[uv]? = before.values[uv]? := by
    intro uv known
    have different : slot ≠ uv := fun same => unmarked (same.symm ▸ known)
    simp only [shape, List.getElem?_set_ne different]
  have transported : ProgramSlots valid literal heap after marked := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro uv known
      simpa only [shape] using roles.bounded uv known
    · intro uv known
      simpa only [shape] using roles.roots uv known
    · intro uv known
      have allowed := setValue_allowed (fun target => ¬UnionFind.SameClass before.representatives uv target)
        slot payload before after (roles.incoming uv known) (avoids uv known) actual
      simpa only [IncomingAvoid, shape] using allowed
    · intro uv known
      obtain ⟨value, stored, role⟩ := roles.stored uv known
      exact ⟨value, (stores uv known).trans stored, role⟩
  exact ⟨transported, fun uv known => ⟨stores uv known, transported.roots uv known, fun _ => by simp only [shape]⟩⟩

private theorem assimilation_shape (source target handle : Nat) (leftScs rightScs : List Suspended)
    (result : Node) (before after : Core)
    (actual : Success (SourcePruningEnumerationAssimilation.finish source target handle leftScs rightScs result) before () after) :
    after = assimilated before target source (.unenumerated (some handle) (leftScs ++ rightScs)) := by
  cases result with
  | empty =>
      change Except.ok ((), after) ∈ ([] : List (Except EnumerationState.Error (Unit × Core))) at actual
      cases actual
  | reference _ | node _ _ _ _ | union _ _ _ _ | mu _ _ _ _ =>
      change Except.ok ((), after) ∈ [Except.ok ((), assimilated before target source (.unenumerated (some handle) (leftScs ++ rightScs)))] at actual
      have same := Except.ok.inj (List.mem_singleton.mp actual)
      exact congrArg Prod.snd same

private theorem incoming_shape (target handle : Nat) (leftScs rightScs : List Suspended)
    (result : Node) (before after : Core)
    (actual : Success (SourcePruningEnumerationIncomingNode.finish target handle leftScs rightScs result) before () after) :
    after = {before with
      values := before.values.set target (.unenumerated (some handle) (leftScs ++ rightScs))
      recursionAncestry := fun other => if other = target then
        (before.expansionAncestry ++ before.recursionAncestry target).eraseDups else before.recursionAncestry other} := by
  cases result with
  | empty =>
      change Except.ok ((), after) ∈ ([] : List (Except EnumerationState.Error (Unit × Core))) at actual
      cases actual
  | reference _ | node _ _ _ _ | union _ _ _ _ | mu _ _ _ _ =>
      change Except.ok ((), after) ∈ [Except.ok ((), {before with
        values := before.values.set target (.unenumerated (some handle) (leftScs ++ rightScs))
        recursionAncestry := fun other => if other = target then
          (before.expansionAncestry ++ before.recursionAncestry target).eraseDups else before.recursionAncestry other})] at actual
      have same := Except.ok.inj (List.mem_singleton.mp actual)
      exact congrArg Prod.snd same

/-- Both actual finish sites retain every marked Program root and its exact stored payload. -/
theorem finish_program_slots
    (heap : NativeHeap) (before : Core) (marked : Nat → Prop)
    (roles : ProgramSlots valid literal heap before marked)
    (target handle : Nat) (leftScs rightScs : List Suspended) (result : Node)
    (unmarkedTarget : ¬marked target)
    (avoids : ∀ uv, marked uv → Avoids before.representatives uv (leftScs ++ rightScs)) :
    (∀ source after, ¬marked source →
      Success (SourcePruningEnumerationAssimilation.finish source target handle leftScs rightScs result) before () after →
      after = assimilated before target source (.unenumerated (some handle) (leftScs ++ rightScs)) ∧
        ProgramSlots valid literal heap after marked ∧
        ∀ uv, marked uv → EnumerationDriver.Protected uv before after) ∧
    (∀ after,
      Success (SourcePruningEnumerationIncomingNode.finish target handle leftScs rightScs result) before () after →
      after = {before with
        values := before.values.set target (.unenumerated (some handle) (leftScs ++ rightScs))
        recursionAncestry := fun other => if other = target then
          (before.expansionAncestry ++ before.recursionAncestry target).eraseDups
          else before.recursionAncestry other} ∧
        ProgramSlots valid literal heap after marked ∧
        ∀ uv, marked uv → EnumerationDriver.Protected uv before after) := by
  let payload : UVarValue Symbol := .unenumerated (some handle) (leftScs ++ rightScs)
  let targeted : Core := {before with values := before.values.set target payload}
  have targetWrite : Success (setValue target payload) before () targeted :=
    (EnumerationDriver.modify_success _ _ _).mpr rfl
  obtain ⟨targetRoles, targetProtects⟩ := write_roles heap before targeted marked roles target payload unmarkedTarget avoids targetWrite
  constructor
  · intro source after unmarkedSource actual
    have shape := assimilation_shape source target handle leftScs rightScs result before after actual
    let cleared : Core := {targeted with values := targeted.values.set source .eliminated}
    have sourceWrite : Success (setValue source .eliminated) targeted () cleared :=
      (EnumerationDriver.modify_success _ _ _).mpr rfl
    obtain ⟨clearRoles, clearProtects⟩ := write_roles heap targeted cleared marked targetRoles source .eliminated unmarkedSource
      (by intro uv known sc member; cases member) sourceWrite
    obtain ⟨finalRoles, finalProtects⟩ := same_fields heap cleared (assimilated before target source payload) marked clearRoles rfl rfl rfl
    refine ⟨shape, ?_, ?_⟩
    · rw [shape]
      exact finalRoles
    · intro uv known
      rw [shape]
      exact ((targetProtects uv known).trans (clearProtects uv known)).trans (finalProtects uv known)
  · intro after actual
    have shape := incoming_shape target handle leftScs rightScs result before after actual
    let finished : Core := {before with
      values := before.values.set target payload
      recursionAncestry := fun other => if other = target then
        (before.expansionAncestry ++ before.recursionAncestry target).eraseDups else before.recursionAncestry other}
    obtain ⟨finalRoles, finalProtects⟩ := same_fields heap targeted finished marked targetRoles rfl rfl rfl
    refine ⟨shape, ?_, ?_⟩
    · rw [shape]
      exact finalRoles
    · intro uv known
      rw [shape]
      exact (targetProtects uv known).trans (finalProtects uv known)

end MicroCFTA.SourceSynthesisProgramRolesAssimilation
