import MicroCFTA.RecursiveCompleteRecord

/-!
# Ordinary application of complete recursive records

A plain Recursive record has no retained key-mass field. Its product uses
the disjunction of the two weight flags and requires both term callbacks.
The template keeps mass provenance for arbitrary mathematical environments.
The Plain invariant sets it to false in every plain source environment.
-/
namespace MicroCFTA.RecursivePlainApplication
open RecursiveJoinRuntime RecursiveRuntimeOrigins

/-- Plain source environments and bodies have no separate retained key mass. -/
def Plain (body : Template Key Root Symbol Value) : Prop :=
  ∀ roots, (∀ key, (roots key).massWeighted = false) → (body.metadata roots).massWeighted = false

/-- Application uses the source weight disjunction without join's mass promotion. -/
def metadata (functions arguments : Metadata) : Metadata :=
  ⟨functions.weighted || arguments.weighted,
    functions.massWeighted || arguments.massWeighted, functions.terms && arguments.terms⟩

/-- A plain product has precisely the fields stored by applyLanguages. -/
theorem metadata_plain (functions arguments : Metadata)
    (left : functions.massWeighted = false) (right : arguments.massWeighted = false) :
    metadata functions arguments =
      ⟨functions.weighted || arguments.weighted, false, functions.terms && arguments.terms⟩ := by
  simp [metadata, left, right]

/-- Primitive field provenance composes without promoting a retained mass. -/
def template [DecidableEq Symbol] (functions : Template Key Root Symbol (A → B))
    (arguments : Template Key Root Symbol A) : Template Key Root Symbol B where
  checked := RecursiveJoinBodyFields.ap functions.checked arguments.checked
  metadata := fun roots => metadata (functions.metadata roots) (arguments.metadata roots)
  inputs := functions.inputs ++ arguments.inputs
  provenance := by
    intro roots
    rcases functions.provenance roots with ⟨leftTerms, leftMass, leftWeighted⟩
    rcases arguments.provenance roots with ⟨rightTerms, rightMass, rightWeighted⟩
    refine ⟨?_, ?_, ?_⟩
    · simp only [metadata, List.map_append, List.all_append, leftTerms, rightTerms]
    · simp only [metadata, List.map_append, List.any_append, leftMass, rightMass]
    · change ((_ || _) || (_ || _)) = _
      rw [show (((functions.metadata roots).weighted || (arguments.metadata roots).weighted) ||
          ((functions.metadata roots).massWeighted || (arguments.metadata roots).massWeighted)) =
          (((functions.metadata roots).weighted || (functions.metadata roots).massWeighted) ||
          ((arguments.metadata roots).weighted || (arguments.metadata roots).massWeighted)) by
            simp only [Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]]
      simp only [List.map_append, List.any_append, leftWeighted, rightWeighted]

/-- Application preserves the plain source boundary under every rebuild. -/
theorem template_plain [DecidableEq Symbol] (functions : Template Key Root Symbol (A → B))
    (arguments : Template Key Root Symbol A) (left : Plain functions) (right : Plain arguments) :
    Plain (template functions arguments) := by
  intro roots plain
  simp [template, metadata, left roots plain, right roots plain]

/-- False product flags derive the local unweighted finite-input laws. -/
def runtime [DecidableEq Symbol] (functions : RecursiveRuntimeVerified.Body Key Root Symbol (A → B))
    (arguments : RecursiveRuntimeVerified.Body Key Root Symbol A) : RecursiveRuntimeVerified.Body Key Root Symbol B where
  template := template functions.template arguments.template
  ordinary := by
    intro unweighted mass
    have weights : (functions.template.metadata (fun _ => placeholder)).weighted = false ∧
        (arguments.template.metadata (fun _ => placeholder)).weighted = false := by
      simpa only [template, metadata, Bool.or_eq_false_iff] using unweighted
    have masses : (functions.template.metadata (fun _ => placeholder)).massWeighted = false ∧
        (arguments.template.metadata (fun _ => placeholder)).massWeighted = false := by
      simpa only [template, metadata, Bool.or_eq_false_iff] using mass
    exact ⟨functions.ordinary weights.1 masses.1, arguments.ordinary weights.2 masses.2⟩

/-- The complete record retains the invariant needed by ordinary application. -/
structure Body (Key Root Symbol Value : Type) where
  complete : RecursiveCompleteRecord.Body Key Root Symbol Value
  plain : Plain complete.runtime.template

/-- A completed source record enters the plain fragment through its actual mass-field law. -/
def source (body : RecursiveCompleteRecord.Body Key Root Symbol Value)
    (plain : Plain body.runtime.template) : Body Key Root Symbol Value := ⟨body, plain⟩

/-- Plain occurrences keep the mass-free field of their current recursive root. -/
def occurrence [DecidableEq Symbol] (callbacks : KeyedNaryFields.LeafCallbacks Symbol)
    (inspections : RecursiveJoinInspectionBody.LeafInspections Symbol) (key : Key) : Body Key Root Symbol Root :=
  ⟨RecursiveCompleteRecord.occurrence callbacks inspections key, fun _ plain => plain key⟩

/-- Maps preserve the same complete compiler and the plain source boundary. -/
def map (transform : Value → Result) (inner : Body Key Root Symbol Value) : Body Key Root Symbol Result :=
  ⟨RecursiveCompleteRecord.map transform inner.complete, inner.plain⟩

/-- Pay preserves plain runtime fields. -/
def pay [DecidableEq Symbol] (inner : Body Key Root Symbol Value) : Body Key Root Symbol Value :=
  ⟨RecursiveCompleteRecord.pay inner.complete, inner.plain⟩

/-- Labels preserve plain fields and the original occurrence metadata. -/
def label [DecidableEq Symbol] (symbol : Symbol) (inner : Body Key Root Symbol Value) : Body Key Root Symbol Value :=
  ⟨RecursiveCompleteRecord.label symbol inner.complete, inner.plain⟩

/-- Ordinary application constructs all fields from the same two plain records. -/
def ap [DecidableEq Symbol] (functions : Body Key Root Symbol (A → B)) (arguments : Body Key Root Symbol A) :
    Body Key Root Symbol B where
  complete := {
    runtime := runtime functions.complete.runtime arguments.complete.runtime
    support := RecursiveJoinSupportBody.ap functions.complete.support arguments.complete.support
    inspection := RecursiveJoinInspectionBody.ap functions.complete.inspection arguments.complete.inspection
    guards := RecursiveJoinGuards.ap functions.complete.guards arguments.complete.guards
    support_same := by
      change RecursiveJoinBodyFields.ap functions.complete.support.checked arguments.complete.support.checked = _
      rw [functions.complete.support_same, arguments.complete.support_same]
      rfl
    inspection_same := by
      change RecursiveJoinBodyFields.ap functions.complete.inspection.checked arguments.complete.inspection.checked = _
      rw [functions.complete.inspection_same, arguments.complete.inspection_same]
      rfl
    guards_same := by
      change RecursiveJoinBodyFields.ap functions.complete.guards.checked arguments.complete.guards.checked = _
      rw [functions.complete.guards_same, arguments.complete.guards_same]
      rfl }
  plain := template_plain _ _ functions.plain arguments.plain

/-- Ordinary choice has no key-mass promotion because each branch is plain. -/
def nary (count : Nat) (branches : Fin count → Body Key Root Symbol Value) : Body Key Root Symbol Value where
  complete := RecursiveCompleteRecord.nary count (fun index => (branches index).complete)
  plain := by
    intro roots plain
    change (List.ofFn fun index => ((branches index).complete.runtime.template.metadata roots)).any Metadata.massWeighted = false
    simp only [List.any_eq_false, List.mem_ofFn, forall_exists_index]
    intro fields index same
    subst fields
    simp [(branches index).plain roots plain]

/-- A successful application rebuild has exactly the plain source flags. -/
theorem ap_fields [DecidableEq Symbol] (functions : Body Key Root Symbol (A → B)) (arguments : Body Key Root Symbol A)
    (roots : Key → Metadata) (plain : ∀ key, (roots key).massWeighted = false) :
    ((ap functions arguments).complete.runtime.template.metadata roots) =
      ⟨(functions.complete.runtime.template.metadata roots).weighted ||
        (arguments.complete.runtime.template.metadata roots).weighted, false,
        (functions.complete.runtime.template.metadata roots).terms &&
        (arguments.complete.runtime.template.metadata roots).terms⟩ :=
  metadata_plain _ _ (functions.plain roots plain) (arguments.plain roots plain)

/-- Every public family theorem consumes the complete compiler of these same plain bodies. -/
def program (bodies : Key → Body Key Root Symbol Root) : Key → RecursiveCompleteRecord.Body Key Root Symbol Root :=
  fun key => (bodies key).complete

/-- Plain family assembly preserves the absence of a retained key-mass field. -/
theorem family_plain (keys : List Key) (bodies : Key → Body Key Root Symbol Root) (key : Key) :
    (memberMetadata keys (RecursiveRuntimeVerified.templates (fun key => (bodies key).complete.runtime)) key).massWeighted = false := by
  change (keys.map (fun key => (bodies key).complete.runtime.template.metadata (fun _ => placeholder))).any Metadata.massWeighted = false
  simp only [List.any_eq_false, List.mem_map, forall_exists_index]
  intro fields source same
  rcases same with ⟨_, rfl⟩
  simp [(bodies source).plain (fun _ => placeholder) (fun _ => rfl)]

/-- For plain families, the final weighted flag is exactly the disjunction of body flags. -/
theorem family_weighted (keys : List Key) (bodies : Key → Body Key Root Symbol Root) (key : Key) :
    (memberMetadata keys (RecursiveRuntimeVerified.templates (fun key => (bodies key).complete.runtime)) key).weighted =
      keys.any (fun source => ((bodies source).complete.runtime.template.metadata (fun _ => placeholder)).weighted) := by
  have noMass := family_plain keys bodies key
  change (keys.map (fun source => (bodies source).complete.runtime.template.metadata (fun _ => placeholder))).any Metadata.massWeighted = false at noMass
  change ((_ || _) : Bool) = _
  simp only [bodyMetadata, RecursiveRuntimeVerified.templates]
  rw [noMass]
  simp only [Bool.false_or, List.any_map, Function.comp_def]

end MicroCFTA.RecursivePlainApplication
