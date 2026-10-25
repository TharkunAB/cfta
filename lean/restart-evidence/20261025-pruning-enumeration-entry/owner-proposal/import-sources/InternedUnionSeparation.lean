import MicroCFTA.InternedGateRank
import MicroCFTA.InternedProbeProvenance

/-!
# Source union separation after nested binder reconstruction

Identity deduplication retains one representative of every operand. Two
different surviving references therefore prevent singleton collapse.
Coherent cached depths also separate a binder from another binder whose
body retains the first one. The proofs read actual resident records.
-/
namespace MicroCFTA.InternedUnionSeparation
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshProbeKeys
open InternedBinderProtocol (NodeKey NodeRef Reference)

/-- Source deduplication retains the identity of every input member. -/
theorem distinctNodes_covers (values : List (Value Symbol Guard))
    (value : Value Symbol Guard) (member : value ∈ values) :
    ∃ kept ∈ distinctNodes values, kept.referenceOf = value.referenceOf := by
  cases values with
  | nil => simp at member
  | cons first rest =>
      by_cases same : value.referenceOf = first.referenceOf
      · exact ⟨first, by simp [distinctNodes], same.symm⟩
      · have inTail : value ∈ rest := by
          rcases List.mem_cons.mp member with equal | inTail
          · subst value; exact False.elim (same rfl)
          · exact inTail
        have retained : value ∈ rest.filter (fun other => other.referenceOf != first.referenceOf) := by
          simp [inTail, same]
        obtain ⟨kept, present, equal⟩ := distinctNodes_covers _ value retained
        exact ⟨kept, by simp [distinctNodes, present], equal⟩
termination_by values.length
decreasing_by
  have bounded := List.length_filter_le (fun other => other.referenceOf != first.referenceOf) rest
  simp_wf
  simp_all
  omega

/-- A singleton result means that every original operand has its one identity. -/
theorem singleton_all (values : List (Value Symbol Guard)) (kept : Value Symbol Guard)
    (single : distinctNodes values = [kept]) (value : Value Symbol Guard) (member : value ∈ values) :
    value.referenceOf = kept.referenceOf := by
  obtain ⟨selected, present, equal⟩ := distinctNodes_covers values value member
  have same : selected = kept := by simpa [single] using present
  simpa [same] using equal.symm

/-- Two surviving different references prevent the source singleton branch. -/
theorem separated_not_singleton (values : List (Value Symbol Guard))
    (first second : Value Symbol Guard) (left : first ∈ values) (right : second ∈ values)
    (different : first.referenceOf ≠ second.referenceOf) :
    ∀ kept, distinctNodes values ≠ [kept] := by
  intro kept single
  exact different ((singleton_all values kept single first left).trans
    (singleton_all values kept single second right).symm)

/-- The union's actual flattened members give a rank-zero result whenever
two of their source identities differ. -/
theorem separated_union_rank [DecidableEq (EdgeKey Symbol Guard)]
    (values : List (Value Symbol Guard)) (state : State Symbol Guard) (coherent : Coherent state)
    (first second : Value Symbol Guard) (left : first ∈ values.flatMap unionMembers)
    (right : second ∈ values.flatMap unionMembers)
    (different : first.referenceOf ≠ second.referenceOf) :
    InternedGateRank.headRank (run (makeUnion values) state).1 = 0 := by
  rw [InternedGateRank.makeUnion_rank values state coherent]
  have separated := separated_not_singleton _ first second left right different
  cases normalized : distinctNodes (values.flatMap unionMembers) with
  | nil => rfl
  | cons first rest =>
      cases rest with
      | nil => exact False.elim (separated first normalized)
      | cons => rfl

/-- Semantic children omit the two immutable Mu probes. Only the actual
stored body participates in source Mu-depth computation. -/
def semanticChildren : Value Symbol Guard → List (Value Symbol Guard)
  | .empty | .reference _ => []
  | .node _ edges _ _ => edges.flatMap EdgeValue.children
  | .union _ members _ _ => members
  | .mu _ body _ _ => [body]

/-- Every semantic child retains its complete resident record. -/
theorem child_available (state : State Symbol Guard) (value child : Value Symbol Guard)
    (available : Available state value) (member : child ∈ semanticChildren value) :
    Available state child := by
  apply available.children child
  cases value <;> simp_all [semanticChildren, children]

/-- Canonical cached metadata bounds the Mu depth of each semantic child. -/
theorem child_depth (state : State Symbol Guard) (coherent : Coherent state)
    (value child : Value Symbol Guard) (available : Available state value)
    (member : child ∈ semanticChildren value) : child.depth ≤ value.depth := by
  cases value with
  | empty | reference => simp [semanticChildren] at member
  | mu entry body depth ordinary =>
      have same : child = body := by simpa [semanticChildren] using member
      simp [same, Value.depth]
  | node entry edges depth free =>
      obtain ⟨actual, _, fields⟩ := coherent.nodes entry.key _ (available.resident entry rfl)
      have equal : depth = maximumDepth (edges.flatMap EdgeValue.children) := fields.2.2.1
      exact (maximumDepth_exact (edges.flatMap EdgeValue.children) depth).mp (Nat.le_of_eq equal.symm) child member
  | union entry members depth free =>
      obtain ⟨actual, _, fields⟩ := coherent.nodes entry.key _ (available.resident entry rfl)
      have equal : depth = maximumDepth members := fields.2.2.1
      exact (maximumDepth_exact members depth).mp (Nat.le_of_eq equal.symm) child member

/-- A finite stored semantic path can reach the original inserted value. -/
inductive Retains {Symbol Guard : Type} (needle : Value Symbol Guard) : Value Symbol Guard → Prop where
  | here : Retains needle needle
  | step {child value : Value Symbol Guard}
      (member : child ∈ semanticChildren value) (tail : Retains needle child) : Retains needle value

/-- Actual constructor and binder metadata bound every retained descendant. -/
theorem retained_depth (state : State Symbol Guard) (coherent : Coherent state)
    (needle value : Value Symbol Guard) (available : Available state value)
    (retained : Retains needle value) : needle.depth ≤ value.depth := by
  induction retained with
  | here => exact Nat.le_refl _
  | step member tail ih =>
      exact Nat.le_trans (ih (child_available state _ _ available member))
        (child_depth state coherent _ _ available member)

/-- Coherent source identities cannot hide different cached Mu depths. -/
theorem depth_separates (state : State Symbol Guard) (coherent : Coherent state)
    (first second : Value Symbol Guard) (left : Available state first) (right : Available state second)
    (different : first.depth ≠ second.depth) : first.referenceOf ≠ second.referenceOf := by
  intro equal
  have same := resident_reference_injective state coherent first second left.resident right.resident equal
  exact different (congrArg Value.depth same)

/-- A rebuilt nested binder that retains the outer binder is strictly deeper.
It cannot have the outer binder's canonical source identity. -/
theorem retained_binder_separates (state : State Symbol Guard) (coherent : Coherent state)
    (outer : Value Symbol Guard) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (outerAvailable : Available state outer)
    (rebuiltAvailable : Available state (.mu entry body depth ordinary))
    (retained : Retains outer body) :
    outer.referenceOf ≠ (Value.mu entry body depth ordinary).referenceOf := by
  have bodyAvailable := child_available state _ body rebuiltAvailable (by simp [semanticChildren])
  have bounded := retained_depth state coherent outer body bodyAvailable retained
  apply depth_separates state coherent outer _ outerAvailable rebuiltAvailable
  simp only [Value.depth]
  omega

/-- A union that retains both the inserted outer binder and a rebuilt binder
containing it cannot collapse to either binder during identity deduplication. -/
theorem retained_union_rank [DecidableEq (EdgeKey Symbol Guard)]
    (state : State Symbol Guard) (coherent : Coherent state) (values : List (Value Symbol Guard))
    (outer : Value Symbol Guard) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (outerAvailable : Available state outer)
    (rebuiltAvailable : Available state (.mu entry body depth ordinary))
    (retained : Retains outer body)
    (left : outer ∈ values.flatMap unionMembers)
    (right : Value.mu entry body depth ordinary ∈ values.flatMap unionMembers) :
    InternedGateRank.headRank (run (makeUnion values) state).1 = 0 :=
  separated_union_rank values state coherent outer _ left right
    (retained_binder_separates state coherent outer entry body depth ordinary
      outerAvailable rebuiltAvailable retained)

end MicroCFTA.InternedUnionSeparation
