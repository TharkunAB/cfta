import MicroCFTA.InternedNestedMissReadback
import MicroCFTA.InternedNestedConstructionExamples

/-!
# An old unused body can differ from both normalized probes

The closed source expression constructs three nested smart binders. An
inner callback can capture both probe sentinels. Its own source variable
is unused. Root self filtering removes a different captured alternative
in each probe. Its fresh body is the earlier complete union of both.
-/
namespace MicroCFTA.InternedOldBodyProbeAliases
open Cache InternedConstructorTemplates InternedNestedConstruction InternedRecordCoherence
open InternedNodeIdentityFootprint InternedProbeProvenance
open InternedBinderProtocol (Reference NodeRef NodeKey)

/-- The innermost source callback returns only its two enclosing inputs. -/
def expression : Syntax Nat Unit := .binder true (.binder true (.binder true (.union [.var 1, .var 2])))

/-- The selected source request exchanges the two captured probe sentinels. -/
def selectedKey : NodeKey := .mu ⟨.ref (.uninterned 0), .ref .depth⟩

/-- Its fresh callback returns the earlier canonical union of both captured references. -/
def oldBody : Value Nat Unit := .union ⟨1, .union [.ref (.uninterned 0), .ref .depth]⟩
  [.reference (.uninterned 0), .reference .depth] 0 [.uninterned 0, .depth]

/-- The complete source run stores this exact Mu body and both different normalized probes. -/
theorem actual_record : (build expression [] empty).state.nodeRecords selectedKey =
    some (.mu ⟨2, selectedKey⟩ oldBody (.reference (.uninterned 0)) (.reference .depth)) := by
  cbv

/-- The source expression is closed under its actual three lexical binders. -/
theorem expression_scoped : Scoped 0 expression := by
  simp [expression, Scoped, ManyScoped]

/-- The closed program completes; this fixture is not a pending-readback counterexample. -/
theorem expression_complete : InternedNestedConstructionExamples.summary (build expression [] empty) =
    some (.empty, 0, [], 13, 0) := by cbv

/-- Neither probe sentinel contains an interned reservation identity. -/
theorem sentinel_absent (identity : Nat) :
    ¬ Occurs identity (Value.reference (Symbol := Nat) (Guard := Unit) .depth) ∧
      ¬ Occurs identity (Value.reference (Symbol := Nat) (Guard := Unit) (.uninterned 0)) := by
  constructor <;> intro occurrence <;> cases occurrence with
  | entry _ entry present _ => cases present
  | child _ child member _ => cases member

/-- Every identity in the returned body predates this Mu's actual reservation. -/
theorem body_old (identity : Nat) (occurrence : Occurs identity oldBody) : identity < 2 := by
  cases occurrence with
  | entry _ entry present same =>
      simp only [oldBody, entryOf, Option.some.injEq] at present
      subst entry
      simp only at same
      omega
  | child _ child member inside =>
      simp only [oldBody, children, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact False.elim ((sentinel_absent identity).2 inside)
      · exact False.elim ((sentinel_absent identity).1 inside)

/-- Smart cleanup returns the old body because the newly reserved local name is unused. -/
theorem cleanup_returns_old : finish true (.mu ⟨2, selectedKey⟩ oldBody
    (.reference (.uninterned 0)) (.reference .depth)) = oldBody := by
  simp [finish, cleanup, oldBody, Value.free]

/-- Old output alone cannot identify that output with either original normalized probe. -/
theorem body_differs_from_both : oldBody.referenceOf ≠ .ref (.uninterned 0) ∧ oldBody.referenceOf ≠ .ref .depth := by
  simp [oldBody, Value.referenceOf]

end MicroCFTA.InternedOldBodyProbeAliases
