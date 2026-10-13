import MicroCFTA.InternedFreeNameConstructors
import MicroCFTA.InternedObservedAbsence

/-!
# Exact constructor agreement after free-name erasure

The observation preserves emptiness and requires exact record equality
when the selected free name is absent. Dead node edges need only the
empty observation. Live edges and union operands supply exact equality.
-/
namespace MicroCFTA.InternedFreeAbsenceConstructors
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedFacts InternedNestedProvenance InternedStoredMuOrigins
open InternedOccurrenceObservations InternedFreshProbeKeys InternedEdgeResidency
open InternedBinderProtocol (Reference)

/-- Results preserve emptiness and agree exactly after the selected free name disappears. -/
def Related (name : Reference) (first second : Value Symbol Guard) : Prop :=
  (first.referenceOf = .empty ↔ second.referenceOf = .empty) ∧ (name ∉ first.free → first = second)

/-- Identical values satisfy the free-name observation. -/
theorem related_refl (name : Reference) (value : Value Symbol Guard) : Related name value value :=
  ⟨Iff.rfl, fun _ => rfl⟩

/-- Related ordered inputs agree on whether an empty child occurs. -/
theorem any_empty (name : Reference) (first second : List (Value Symbol Guard))
    (paired : Paired (Related name) first second) :
    first.any (fun child => child.referenceOf == .empty) = true ↔
      second.any (fun child => child.referenceOf == .empty) = true := by
  simpa only [List.any_eq_true, beq_iff_eq] using
    exists_iff paired (fun value => value.referenceOf = .empty) (fun value => value.referenceOf = .empty)
      (fun _ _ related => related.1)

/-- Related ordered inputs also agree on live-edge selection. -/
theorem all_live (name : Reference) (first second : List (Value Symbol Guard))
    (paired : Paired (Related name) first second) :
    first.any (fun child => child.referenceOf == .empty) = false ↔
      second.any (fun child => child.referenceOf == .empty) = false := by
  simpa only [List.any_eq_false, beq_iff_eq] using
    all_iff paired (fun value => value.referenceOf ≠ .empty) (fun value => value.referenceOf ≠ .empty)
      (fun _ _ related => not_congr related.1)

/-- Absence in each first operand identifies both ordered operand lists. -/
theorem paired_equal (name : Reference) (first second : List (Value Symbol Guard))
    (paired : Paired (Related name) first second) (absent : ∀ value ∈ first, name ∉ value.free) : first = second := by
  induction paired with
  | nil => rfl
  | @cons first second rest tail related paired ih =>
      rw [related.2 (absent first List.mem_cons_self), ih (fun value member => absent value (List.mem_cons_of_mem _ member))]

/-- Source edge metadata agrees while its children retain the free-name observation. -/
def EdgeRelated (name : Reference) (first second : EdgeValue Symbol Guard) : Prop :=
  first.entry.key.symbol = second.entry.key.symbol ∧ first.entry.key.constraint = second.entry.key.constraint ∧
    Paired (Related name) first.children second.children

/-- Equal live children identify the complete canonical edge in a common cache. -/
theorem edge_equal (name : Reference) (first second : EdgeValue Symbol Guard) (state : State Symbol Guard)
    (coherent : Coherent state) (left : EdgeResident state first) (right : EdgeResident state second)
    (related : EdgeRelated name first second) (absent : ∀ child ∈ first.children, name ∉ child.free) : first = second := by
  have sameChildren := paired_equal name first.children second.children related.2.2 absent
  have leftFields := (coherent.edges first.entry.key first left).2
  have rightFields := (coherent.edges second.entry.key second right).2
  have keys : first.entry.key = second.entry.key := by
    have refs := leftFields.2.symm.trans ((congrArg (List.map Value.referenceOf) sameChildren).trans rightFields.2)
    have symbols := related.1
    have guards := related.2.1
    cases firstKey : first.entry.key
    cases secondKey : second.entry.key
    simp_all
  unfold EdgeResident at left right
  rw [← keys] at right
  exact Option.some.inj (left.symm.trans right)

/-- Related dead edges disappear together, and selected edges with no free occurrence agree exactly. -/
theorem surviving_equal (name : Reference) (first second : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state)
    (left : ∀ edge ∈ first, EdgeResident state edge) (right : ∀ edge ∈ second, EdgeResident state edge)
    (paired : Paired (EdgeRelated name) first second)
    (absent : ∀ edge ∈ first, edge.children.any (fun child => child.referenceOf == .empty) = false →
      ∀ child ∈ edge.children, name ∉ child.free) : surviving first = surviving second := by
  induction paired with
  | nil => rfl
  | @cons first second rest tail related paired ih =>
      have tailSame := ih (fun edge member => left edge (List.mem_cons_of_mem _ member))
        (fun edge member => right edge (List.mem_cons_of_mem _ member))
        (fun edge member => absent edge (List.mem_cons_of_mem _ member))
      cases firstLive : first.children.any (fun child => child.referenceOf == .empty) with
      | false =>
          have secondLive := (all_live name first.children second.children related.2.2).mp firstLive
          have same := edge_equal name first second state coherent (left first List.mem_cons_self)
            (right second List.mem_cons_self) related (absent first List.mem_cons_self firstLive)
          simpa only [surviving, List.filter_cons, firstLive, secondLive, Bool.not_false, ↓reduceIte, same] using
            congrArg (second :: ·) tailSame
      | true =>
          have secondDead := (any_empty name first.children second.children related.2.2).mp firstLive
          simpa [surviving, firstLive, secondDead] using tailSame

/-- Actual node normalization preserves the free-name observation through live and discarded edges. -/
theorem makeNode_related [DecidableEq (EdgeKey Symbol Guard)] (name : Reference)
    (first second : List (EdgeValue Symbol Guard)) (left right common : State Symbol Guard)
    (ln : Normal left) (rn : Normal right) (coherent : Coherent common)
    (lr : ∀ edge ∈ first, EdgeResident left edge) (rr : ∀ edge ∈ second, EdgeResident right edge)
    (paired : Paired (EdgeRelated name) first second)
    (lg : Grows (run (makeNode first) left).2 common) (rg : Grows (run (makeNode second) right).2 common) :
    Related name (run (makeNode first) left).1 (run (makeNode second) right).1 := by
  constructor
  · rw [InternedEmptyNormalization.makeNode_empty_iff first left ln.facts.coherent ln.facts.linked lr,
      InternedEmptyNormalization.makeNode_empty_iff second right rn.facts.coherent rn.facts.linked rr]
    exact all_iff paired _ _ (fun a b related => any_empty name a.children b.children related.2.2)
  · intro absent
    have leftGrowth := grows_trans (InternedConstructorTemplates.run_correct (makeNode first) left ln.facts.coherent.valid).2 lg
    have rightGrowth := grows_trans (InternedConstructorTemplates.run_correct (makeNode second) right rn.facts.coherent.valid).2 rg
    have normalized := surviving_equal name first second common coherent
      (fun edge member => edge_grows left common leftGrowth edge (lr edge member))
      (fun edge member => edge_grows right common rightGrowth edge (rr edge member)) paired (by
        intro edge member live child included present
        exact absent ((InternedFreeNameConstructors.node_membership first left ln lr name).mpr
          ⟨edge, member, live, child, included, present⟩))
    have same : makeNode first = makeNode second := by unfold makeNode; rw [normalized]
    rw [← same] at rg ⊢
    exact InternedObservedAbsence.run_shared _ left right common ln.facts.coherent.valid rn.facts.coherent.valid lg rg

/-- Actual union normalization preserves exact agreement after the selected free name disappears. -/
theorem makeUnion_related [DecidableEq (EdgeKey Symbol Guard)] (name : Reference)
    (first second : List (Value Symbol Guard)) (left right common : State Symbol Guard)
    (ln : Normal left) (rn : Normal right) (li : Values left first) (ri : Values right second)
    (paired : Paired (Related name) first second)
    (lg : Grows (run (makeUnion first) left).2 common) (rg : Grows (run (makeUnion second) right).2 common) :
    Related name (run (makeUnion first) left).1 (run (makeUnion second) right).1 := by
  constructor
  · rw [InternedEmptyNormalization.makeUnion_empty_iff first left ln.facts.coherent ln.facts.linked ln.live ln.proper li,
      InternedEmptyNormalization.makeUnion_empty_iff second right rn.facts.coherent rn.facts.linked rn.live rn.proper ri]
    exact all_iff paired _ _ (fun _ _ related => related.1)
  · intro absent
    have same := paired_equal name first second paired (by
      intro value member present
      exact absent ((InternedFreeNameConstructors.union_membership first left ln li name).mpr ⟨value, member, present⟩))
    rw [← same] at rg ⊢
    exact InternedObservedAbsence.run_shared _ left right common ln.facts.coherent.valid rn.facts.coherent.valid lg rg

end MicroCFTA.InternedFreeAbsenceConstructors
