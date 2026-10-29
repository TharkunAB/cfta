import MicroCFTA.InternedMuDepthInventory
import MicroCFTA.InternedStoredPlanBinderDepthNormalization

/-!
# Available operands below the original Mu inventory limit

Available values retain every actual child and resident Mu record.
The original Mu-body bound therefore bounds each operand's open binder depth.
No bound on a future result or cached depth is an input.
-/
namespace MicroCFTA.InternedMuDepthAvailableBounds
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedStoredPlanBinderDepth
variable {Symbol Guard : Type}

/-- The original complete-Mu body bound covers every recursively available operand. -/
theorem value_le (state : State Symbol Guard) (limit : Nat)
    (bounded : InternedMuDepthInventory.Bounded state limit)
    (value : Value Symbol Guard) (available : Available state value) :
    valueDepth value ≤ limit := by
  induction available with
  | intro value resident _issued _children ih =>
      rw [valueDepth.eq_def]
      split
      · exact Nat.zero_le _
      · cases value with
        | empty | reference => exact Nat.zero_le _
        | node entry edges depth free =>
            change edgesDepth edges ≤ limit
            rw [edges_eq_many]
            exact (many_le_iff _ limit).mpr (fun child member => ih child member)
        | union entry members depth free =>
            change manyDepth members ≤ limit
            exact (many_le_iff members limit).mpr (fun child member => ih child member)
        | mu entry body depth ordinary =>
            change 1 + valueDepth body ≤ limit
            have inside := bounded entry.key entry body depth ordinary (resident entry rfl)
            omega

/-- Original source facts supply a finite common degree bound for all available operands. -/
theorem initial_value_le (state : State Symbol Guard) (facts : InternedNestedFacts.Facts state)
    (value : Value Symbol Guard) (available : Available state value) :
    valueDepth value ≤ maximumDepth (nodeInventory state) + 1 :=
  value_le state _ (InternedMuDepthInventory.initial_bounded state facts) value available

end MicroCFTA.InternedMuDepthAvailableBounds
