import MicroCFTA.InternedObservedAbsence
import MicroCFTA.InternedBoundaryFilter
import MicroCFTA.InternedFilterEmptiness

/-!
# Exact absence observations through normalized source probes

A probe filter removes only its supplied literal sentinel. When that
sentinel is allowed, every forbidden boundary survives the filter.
Exact ordinary observations therefore pass through actual normalization.
-/
namespace MicroCFTA.InternedObservedFilter
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedFacts InternedObservedAbsence InternedBoundaryAtoms InternedBoundaryFilter
open InternedLiveEdges InternedNonemptyRecords InternedUnionNonemptyMembers InternedFilterEmptiness
open InternedBinderProtocol (Reference NodeRef)

/-- Filtering an allowed probe sentinel cannot hide any forbidden source boundary. -/
theorem clear_before_filter [DecidableEq (EdgeKey Symbol Guard)] (forbidden : NodeRef → Prop)
    (name : Reference) (allowed : ¬ forbidden (.ref name)) (value : Value Symbol Guard)
    (state : State Symbol Guard) (facts : Facts state) (live : Live state) (available : Available state value)
    (clear : Clear forbidden (run (withoutSelfReference name value) state).1) : Clear forbidden value := by
  intro item member
  by_cases same : item = .ref name
  · exact same ▸ allowed
  · exact clear item ((filter_atom_iff name item value state facts.coherent facts.cached facts.linked live available same).mpr member)

/-- The same normalized source probe preserves emptiness and exact agreement when its sentinel is allowed. -/
theorem filter_related [DecidableEq (EdgeKey Symbol Guard)] (forbidden : NodeRef → Prop)
    (name : Reference) (allowed : ¬ forbidden (.ref name)) (first second : Value Symbol Guard)
    (left right common : State Symbol Guard) (lf : Facts left) (rf : Facts right)
    (ll : Live left) (rl : Live right) (ln : NonemptyRecords left) (rn : NonemptyRecords right)
    (lm : MembersNonempty left) (rm : MembersNonempty right)
    (la : Available left first) (ra : Available right second) (related : Related forbidden first second)
    (lg : Grows (run (withoutSelfReference name first) left).2 common)
    (rg : Grows (run (withoutSelfReference name second) right).2 common) :
    Related forbidden (run (withoutSelfReference name first) left).1 (run (withoutSelfReference name second) right).1 := by
  constructor
  · rw [filter_empty_iff name first left lf.coherent lf.linked ll ln lm la,
      filter_empty_iff name second right rf.coherent rf.linked rl rn rm ra]
    exact related.1
  · intro observed
    have clear := clear_before_filter forbidden name allowed first left lf ll la observed
    have same := related.2 clear
    rw [← same] at rg ⊢
    exact run_shared _ left right common lf.coherent.valid rf.coherent.valid lg rg

end MicroCFTA.InternedObservedFilter
