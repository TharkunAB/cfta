import MicroCFTA.SourceCurrentConstrainedCap
import MicroCFTA.SourceRecursiveIntersectionMaybeMu
import MicroCFTA.InternedUnionFilterFusion

/-!
# Normalized direct-union optional binders

A direct self-union alternative can be removed before every binder probe.
The other alternative is a closed ordinary record with arbitrary guards.
The finite producer requires an initially absent canonical binder key.
It retains the actual probe allocations and does not assume a result law.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapNormalizedBinder
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedFacts InternedNestedProvenance
open InternedNestedConstruction (Outcome work request finish)
open InternedBinderProtocol (Reference NodeKey)
open SourceCurrentConstrainedCap
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

/-- A root union names the selected pair directly and retains one closed ordinary alternative. -/
def body (old : Reference) (entry node : Interned NodeKey)
    (edges : List (EdgeValue Symbol Guard)) (level outerLevel : Nat) : Value Symbol Guard :=
  .union entry [.reference old, .node node edges level []] outerLevel [old]

private theorem selected (name : Reference) (node : Interned NodeKey)
    (edges : List (EdgeValue Symbol Guard)) (level : Nat) :
    distinctNodes (([.reference name, .node node edges level []] : List (Value Symbol Guard)).flatMap unionMembers) =
      [.reference name, .node node edges level []] := by
  simp [unionMembers, distinctNodes, Value.referenceOf]

private theorem normalized (name : Reference) (node : Interned NodeKey)
    (edges : List (EdgeValue Symbol Guard)) (level : Nat) (state : State Symbol Guard)
    (facts : Facts state) (ordinary : Available state (.node node edges level []))
    (reference : Available state (.reference name)) :
    let original := run (makeUnion [.reference name, .node node edges level []]) state
    run (withoutSelfReference name original.1) original.2 = (.node node edges level [], original.2) := by
  have available : Values state [.reference name, .node node edges level []] := by
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact reference
    · exact List.mem_singleton.mp member ▸ ordinary
  have deleted := InternedUnionFilterFusion.deleting name _ (.reference name) (.node node edges level []) []
    state facts available (selected name node edges level) (by simp)
  simpa [withoutSelfReference_members, Value.referenceOf, makeUnion, unionMembers, distinctNodes, run] using deleted

/-- Actual substitution and root filtering return the original ordinary alternative. -/
theorem callback (old name : Reference) (entry node : Interned NodeKey)
    (edges : List (EdgeValue Symbol Guard)) (level outerLevel : Nat)
    (state : State Symbol Guard) (facts : Facts state)
    (available : Available state (body old entry node edges level outerLevel))
    (reference : Available state (.reference name)) :
    SourceRecursiveIntersectionMaybeMu.callback old (body old entry node edges level outerLevel) name state =
      .done (.node node edges level []) (run (makeUnion [.reference name, .node node edges level []]) state).2 := by
  have ordinary := available.children (.node node edges level []) (by simp [body, children])
  rw [SourceRecursiveIntersectionMaybeMu.callback_eq old _ name state state facts available]
  have raw :
      InternedFreshOrdinaryFacts.callback
        (InternedStoredSubstitution.encode (InternedStoredSubstitution.leaves (body old entry node edges level outerLevel))
          [old] (body old entry node edges level outerLevel))
        (InternedStoredSubstitution.leaves (body old entry node edges level outerLevel)) name state =
      (work (makeUnion [.reference name, .node node edges level []]) state).bind
        (fun value after => work (withoutSelfReference name value) after) := by
    simp [InternedFreshOrdinaryFacts.callback, body, InternedStoredSubstitution.encode,
      InternedStoredSubstitution.encodeMany, InternedStoredSubstitution.leaves,
      InternedStoredSubstitution.manyLeaves, InternedStoredSubstitution.slot,
      InternedFreshOrdinaryConstruction.build, InternedFreshOrdinaryConstruction.buildMany,
      InternedNestedConstruction.Outcome.bind, Value.free, Value.referenceOf]
  rw [raw]
  simp only [work, Outcome.bind]
  rw [normalized name node edges level state facts ordinary reference]

end MicroCFTA.SourceCurrentConstrainedCapNormalizedBinder
