import MicroCFTA.SourceSynthesisUniverseRowTransform
import MicroCFTA.InternedNodeSetCongruence

/-!
# Physical normalization of transformed source rows

Resident rows with one transformed source key have one stored payload.
If the actual product contains every source self row, and every live product
row has such a source, both complete makeNode requests are equal. Duplicate
source rows and dead product rows do not change the normalized request.
-/
namespace MicroCFTA.SourceSynthesisUniverseCanonicalRows
open Cache Language InternedConstructorTemplates InternedNestedFacts
open InternedEdgeResidency
open EqualityLeafProjectionPhysical (dead)
open SourceSynthesisUniverseRowTransform (Readback)

variable {Symbol Guard : Type}

/-- One physical transformed key selects one complete resident edge payload. -/
theorem readback_unique (top : Guard) (uId : Nat)
    (source first second : EdgeValue Symbol Guard) (state : State Symbol Guard)
    (firstResident : EdgeResident state first) (secondResident : EdgeResident state second)
    (firstRead : Readback top uId source first) (secondRead : Readback top uId source second) :
    first = second := by
  have key : first.entry.key = second.entry.key := firstRead.2.trans secondRead.2.symm
  have storedFirst : state.edgeRecords first.entry.key = some first := firstResident
  have storedSecond : state.edgeRecords second.entry.key = some second := secondResident
  rw [key] at storedFirst
  exact Option.some.inj (storedFirst.symm.trans storedSecond)

private theorem aligned_member (top : Guard) (uId : Nat)
    {sources targets : List (EdgeValue Symbol Guard)}
    (aligned : All₂ (Readback top uId) sources targets) :
    ∀ source ∈ sources, ∃ target ∈ targets, Readback top uId source target := by
  induction aligned with
  | nil => intro source member; cases member
  | @cons source target sources targets own tail ih =>
      intro selected member
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨target, List.mem_cons_self, own⟩
      · obtain ⟨target, present, related⟩ := ih selected later
        exact ⟨target, List.mem_cons_of_mem _ present, related⟩

/-- Derived self-row coverage and live-row origins give the same complete canonical node request. -/
theorem makeNode_eq (top : Guard) (uId : Nat)
    (sources products targets : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state)
    (productResident : ∀ row ∈ products, EdgeResident state row)
    (targetResident : ∀ row ∈ targets, EdgeResident state row)
    (aligned : All₂ (Readback top uId) sources targets)
    (targetLive : ∀ row ∈ targets, dead row = false)
    (origins : ∀ row ∈ products, dead row = false →
      ∃ source ∈ sources, Readback top uId source row)
    (retained : ∀ row ∈ targets, row ∈ products) :
    makeNode products = makeNode targets := by
  apply InternedNodeSetCongruence.makeNode_same_members state facts.coherent products targets
    productResident targetResident
  intro row
  simp only [surviving, List.mem_filter, Bool.not_eq_true']
  change (row ∈ products ∧ dead row = false) ↔ (row ∈ targets ∧ dead row = false)
  constructor
  · rintro ⟨present, live⟩
    obtain ⟨source, included, productRead⟩ := origins row present live
    obtain ⟨target, selected, targetRead⟩ := aligned_member top uId aligned source included
    have same := readback_unique top uId source row target state
      (productResident row present) (targetResident target selected) productRead targetRead
    subst row
    exact ⟨selected, targetLive target selected⟩
  · rintro ⟨present, live⟩
    exact ⟨retained row present, live⟩

end MicroCFTA.SourceSynthesisUniverseCanonicalRows
