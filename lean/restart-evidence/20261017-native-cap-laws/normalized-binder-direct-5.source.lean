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
variable {Symbol Guard : Type}

/-- A root union names the selected pair directly and retains one closed ordinary alternative. -/
def body (old : Reference) (entry node : Interned NodeKey)
    (edges : List (EdgeValue Symbol Guard)) (level outerLevel : Nat) : Value Symbol Guard :=
  .union entry [.reference old, .node node edges level []] outerLevel [old]

private theorem selected (name : Reference) (node : Interned NodeKey)
    (edges : List (EdgeValue Symbol Guard)) (level : Nat) :
    distinctNodes (([.reference name, .node node edges level []] : List (Value Symbol Guard)).flatMap unionMembers) =
      [.reference name, .node node edges level []] := by
  simp [unionMembers, distinctNodes, Value.referenceOf]

variable [DecidableEq (EdgeKey Symbol Guard)]

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
      InternedStoredSubstitution.manyLeaves, InternedStoredSubstitution.slot, List.findIdx_cons,
      InternedFreshOrdinaryConstruction.build, InternedFreshOrdinaryConstruction.buildMany,
      InternedNestedConstruction.Outcome.bind, Value.free, Value.referenceOf]
  rw [raw]
  simp only [work, Outcome.bind]
  rw [normalized name node edges level state facts ordinary reference]

omit [DecidableEq (EdgeKey Symbol Guard)] in
open scoped Classical in
private theorem union_keeps_mu (name : Reference) (node : Interned NodeKey)
    (edges : List (EdgeValue Symbol Guard)) (level : Nat) (state : State Symbol Guard)
    (depth ordinary : Value Symbol Guard) :
    let after := (run (makeUnion [.reference name, .node node edges level []]) state).2
    after.nodes.table (muKey depth ordinary) = state.nodes.table (muKey depth ordinary) ∧
      after.nodeRecords (muKey depth ordinary) = state.nodeRecords (muKey depth ordinary) := by
  simp only [makeUnion, selected, ordinaryEdges, run, nodeStep]
  cases installed : state.nodes.table (.union [.ref name, .node node.identity]) <;>
    cases stored : state.nodeRecords (.union [.ref name, .node node.identity]) <;>
    simp [Cache.intern, Value.referenceOf, installed, stored, Cache.install, Cache.reserve, Cache.keepFirst, Cache.put, muKey]

private theorem callback_checked (old name : Reference) (entry node : Interned NodeKey)
    (edges : List (EdgeValue Symbol Guard)) (level outerLevel : Nat)
    (state : State Symbol Guard) (facts : Facts state)
    (available : Available state (body old entry node edges level outerLevel))
    (reference : Available state (.reference name)) :
    Verified state (SourceRecursiveIntersectionMaybeMu.callback old (body old entry node edges level outerLevel) name state)
      Available := by
  have ordinary := available.children (.node node edges level []) (by simp [body, children])
  have checked := union_verified [.reference name, .node node edges level []] state facts (by
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact reference
    · exact List.mem_singleton.mp member ▸ ordinary)
  rw [callback old name entry node edges level outerLevel state facts available reference]
  refine ⟨checked.facts, checked.growth, checked.history, ?_⟩
  intro value after same
  cases same
  exact checked.available _ ordinary

/-- An initially fresh binder key derives actual completion and the original alternative's cap. -/
theorem complete (annotation : Guard → Prop) (bound : Nat) (pair : Nat × Nat)
    (entry node : Interned NodeKey) (edges : List (EdgeValue Symbol Guard)) (level outerLevel : Nat)
    (state : State Symbol Guard) (facts : Facts state)
    (available : Available state (body (.intersection pair.1 pair.2) entry node edges level outerLevel))
    (bounded : SourceCurrentConstrainedCap.Cap annotation bound (.node node edges level []))
    (fresh : state.nodes.table (muKey (.node node edges level []) (.node node edges level [])) = none) :
    ∃ final,
      SourceRecursiveIntersectionMaybeMu.maybeMu pair
        (body (.intersection pair.1 pair.2) entry node edges level outerLevel) state =
        .done (.node node edges level []) final ∧
      Facts final ∧ Grows state final ∧ Extends state.nodes.issued final.nodes.issued ∧
      Available final (.node node edges level []) ∧
      SourceCurrentConstrainedCap.Cap annotation bound (.node node edges level []) := by
  let old := Reference.intersection pair.1 pair.2
  let value : Value Symbol Guard := .node node edges level []
  let source := body old entry node edges level outerLevel
  let key := muKey value value
  let afterDepth := (run (makeUnion [.reference .depth, value]) state).2
  have depthDone := callback old .depth entry node edges level outerLevel state facts available
    (depth_available state)
  have depthChecked := callback_checked old .depth entry node edges level outerLevel state facts available
    (depth_available state)
  have depthFacts : Facts afterDepth := by simpa only [depthDone, Outcome.state] using depthChecked.facts
  have depthAvailable : Available afterDepth source := by simpa only [depthDone, Outcome.state] using depthChecked.available _ available
  let name := Reference.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel value)
  let afterOrdinary := (run (makeUnion [.reference name, value]) afterDepth).2
  have ordinaryDone := callback old name entry node edges level outerLevel afterDepth depthFacts depthAvailable
    (ordinary_available afterDepth _)
  have ordinaryChecked := callback_checked old name entry node edges level outerLevel afterDepth depthFacts depthAvailable
    (ordinary_available afterDepth _)
  have ordinaryFacts : Facts afterOrdinary := by simpa only [ordinaryDone, Outcome.state] using ordinaryChecked.facts
  have ordinaryAvailable : Available afterOrdinary source := by simpa only [ordinaryDone, Outcome.state] using ordinaryChecked.available _ depthAvailable
  have depthKeys := union_keeps_mu .depth node edges level state value value
  have ordinaryKeys := union_keeps_mu name node edges level afterDepth value value
  have missing : afterOrdinary.nodes.table key = none := ordinaryKeys.1.trans (depthKeys.1.trans fresh)
  have initialMissing : state.nodeRecords key = none := by
    cases found : state.nodeRecords key with
    | none => rfl
    | some present =>
        obtain ⟨actual, installed, _⟩ := facts.coherent.nodes key present found
        rw [fresh] at installed
        cases installed
  have missingRecord : afterOrdinary.nodeRecords key = none := ordinaryKeys.2.trans (depthKeys.2.trans initialMissing)
  let reserved := Cache.intern afterOrdinary.nodes key
  let allocated : State Symbol Guard := {afterOrdinary with nodes := reserved.2}
  have allocatedFacts : Facts allocated := reserve_facts key afterOrdinary ordinaryFacts
  have allocatedAvailable : Available allocated source :=
    ordinaryAvailable.grows afterOrdinary allocated
      ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩
      (InternedFreshProbeKeys.intern_issued_extends afterOrdinary.nodes key ordinaryFacts.coherent.valid.2)
  have localAvailable : Available allocated (.reference (.interned reserved.1.identity)) :=
    (InternedConstructionProvenance.reserve_available key afterOrdinary ordinaryFacts.coherent ordinaryFacts.cached).2
  have bodyDone := callback old (.interned reserved.1.identity) entry node edges level outerLevel
    allocated allocatedFacts allocatedAvailable localAvailable
  let afterBody := (run (makeUnion [.reference (.interned reserved.1.identity), value]) allocated).2
  have bodyKeys := union_keeps_mu (.interned reserved.1.identity) node edges level allocated value value
  have bodyMissing : afterBody.nodeRecords key = none := bodyKeys.2.trans missingRecord
  let candidate := Value.mu reserved.1 value value value
  let final := {afterBody with nodeRecords := keepFirst afterBody.nodeRecords key candidate}
  have actual : SourceRecursiveIntersectionMaybeMu.maybeMu pair source state = .done value final := by
    have used : Reference.intersection pair.1 pair.2 ∈ source.free := by simp [source, body, old, Value.free]
    rw [SourceRecursiveIntersectionMaybeMu.maybeMu, ite_eq_left used]
    change SourceRecursiveIntersectionMaybeMu.construct old source state = _
    unfold SourceRecursiveIntersectionMaybeMu.construct
    rw [depthDone]
    simp only [Outcome.bind]
    rw [ordinaryDone]
    simp only [Outcome.bind]
    change request true value value (SourceRecursiveIntersectionMaybeMu.callback old source) afterOrdinary = _
    unfold request
    rw [missing]
    change (SourceRecursiveIntersectionMaybeMu.callback old source (.interned reserved.1.identity) allocated).bind _ = _
    rw [bodyDone]
    simp only [Outcome.bind]
    change .done (finish true ((keepFirst afterBody.nodeRecords key candidate key).getD candidate)) final = _
    simp only [keepFirst, bodyMissing, put, ↓reduceIte, Option.getD_some, finish, cleanup, candidate, value,
      Value.free, List.not_mem_nil, ↓reduceIte]
  have verified := SourceRecursiveIntersectionMaybeMu.verified pair source state facts available
  refine ⟨final, actual, ?_, ?_, ?_, verified.result value final actual, bounded⟩
  · simpa only [actual, Outcome.state] using verified.facts
  · simpa only [actual, Outcome.state] using verified.growth
  · simpa only [actual, Outcome.state] using verified.history

end MicroCFTA.SourceCurrentConstrainedCapNormalizedBinder
