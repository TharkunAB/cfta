import MicroCFTA.SourceCurrentNativeMuGrowthHistory
import MicroCFTA.SourceCurrentNativeMuPublicationCallbacks

/-!
# Selected Mu writers in a common later heap

A selected payload retains its actual first publication and callback paths.
The publication's final heap grows into the reader's heap. Earlier raw
callback heaps therefore also grow into that same heap.
-/
namespace MicroCFTA.SourceCurrentNativeMuGrowthWriters
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open SourceCurrentNativeMuPublication (Publication)
open SourceCurrentNativeMuGrowthHistory

/-- A selected writer retains its exact prefix, callbacks, and later cache growth. -/
def Written [DecidableEq (EdgeKey Symbol Guard)] (before after : State Symbol Guard)
    (key : NodeKey) (value : Value Symbol Guard) : Prop :=
  ∃ event : Publication (Symbol := Symbol) (Guard := Guard),
    key = event.key ∧ value = event.candidate ∧ event.afterBody.nodeRecords event.key = none ∧
    Nonempty (Path before event.before) ∧
    Nonempty (Path event.before event.afterDepth) ∧
    Nonempty (Path event.afterDepth event.cut) ∧
    Nonempty (Path event.allocated event.afterBody) ∧ Grows event.after after

/-- A preceding actual path preserves the selected publication and its later heap. -/
theorem Written.prepend [DecidableEq (EdgeKey Symbol Guard)]
    {before middle after : State Symbol Guard} {key : NodeKey} {value : Value Symbol Guard}
    (prefix : Path before middle) (written : Written middle after key value) : Written before after key value := by
  obtain ⟨event, key, value, missing, ⟨first⟩, depth, ordinary, body, growth⟩ := written
  exact ⟨event, key, value, missing, ⟨.trans prefix first⟩, depth, ordinary, body, growth⟩

/-- Later cache growth retains the same writer and every earlier callback heap. -/
theorem Written.later [DecidableEq (EdgeKey Symbol Guard)]
    {before middle after : State Symbol Guard} {key : NodeKey} {value : Value Symbol Guard}
    (written : Written before middle key value) (growth : Grows middle after) : Written before after key value := by
  obtain ⟨event, key, value, missing, first, depth, ordinary, body, earlier⟩ := written
  exact ⟨event, key, value, missing, first, depth, ordinary, body, grows_trans earlier growth⟩

/-- The stronger selected-writer receipt retains the earlier causal publication contract. -/
theorem Written.history [DecidableEq (EdgeKey Symbol Guard)]
    {before after : State Symbol Guard} {key : NodeKey} {value : Value Symbol Guard}
    (written : Written before after key value) : SourceCurrentNativeMuPublication.Written before key value := by
  obtain ⟨event, key, value, missing, ⟨first⟩, ⟨depth⟩, ⟨ordinary⟩, ⟨body⟩, _⟩ := written
  exact ⟨event, key, value, missing, ⟨first.history⟩, ⟨depth.history⟩, ⟨ordinary.history⟩, ⟨body.history⟩⟩

/-- A final Mu was present initially or has an actual writer whose heap reaches this reader. -/
theorem writers [DecidableEq (EdgeKey Symbol Guard)] {before after : State Symbol Guard}
    (path : Path before after) (key : NodeKey) (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard)
    (present : after.nodeRecords key = some (.mu entry body depth ordinary)) :
    before.nodeRecords key = some (.mu entry body depth ordinary) ∨
      Written before after key (.mu entry body depth ordinary) := by
  induction path with
  | refl => exact Or.inl present
  | retain before after old growth => exact Or.inl (old key entry body depth ordinary present)
  | trans first next firstIH nextIH =>
      rcases nextIH present with old | written
      · rcases firstIH old with initial | written
        · exact Or.inl initial
        · exact Or.inr (written.later next.growth)
      · exact Or.inr (written.prepend first)
  | publication event depthPath ordinaryPath bodyPath depthIH ordinaryIH bodyIH =>
      have reserve : Path event.cut event.allocated :=
        .retain event.cut event.allocated (fun _ _ _ _ _ found => found) (reserve_growth event)
      have cutGrowth : Grows event.cut event.after :=
        grows_trans (reserve_growth event) (grows_trans bodyPath.growth (publication_growth event))
      have depthGrowth : Grows event.afterDepth event.after := grows_trans ordinaryPath.growth cutGrowth
      have prior (old : event.afterBody.nodeRecords key = some (.mu entry body depth ordinary)) :
          event.before.nodeRecords key = some (.mu entry body depth ordinary) ∨
            Written event.before event.after key (.mu entry body depth ordinary) := by
        rcases bodyIH old with allocated | written
        · rcases ordinaryIH allocated with afterDepth | written
          · rcases depthIH afterDepth with initial | written
            · exact Or.inl initial
            · exact Or.inr (written.later depthGrowth)
          · exact Or.inr ((written.prepend depthPath).later cutGrowth)
        · exact Or.inr ((written.prepend (.trans (.trans depthPath ordinaryPath) reserve)).later
            (publication_growth event))
      rcases record_cases event.afterBody.nodeRecords event.key key event.candidate
        (.mu entry body depth ordinary) present with old | ⟨sameKey, sameValue⟩
      · exact prior old
      · cases firstWrite : event.afterBody.nodeRecords event.key with
        | none => exact Or.inr ⟨event, sameKey, sameValue, firstWrite, ⟨.refl event.before⟩,
            ⟨depthPath⟩, ⟨ordinaryPath⟩, ⟨bodyPath⟩, grows_refl event.after⟩
        | some previous =>
            apply prior
            change keepFirst event.afterBody.nodeRecords event.key event.candidate key =
              some (.mu entry body depth ordinary) at present
            simpa only [keepFirst, firstWrite] using present

/-- Empty initial caches supply a selected writer and its actual growth to the reader. -/
theorem from_empty [DecidableEq (EdgeKey Symbol Guard)] {after : State Symbol Guard}
    (path : Path empty after) (key : NodeKey) (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard)
    (present : after.nodeRecords key = some (.mu entry body depth ordinary)) :
    Written empty after key (.mu entry body depth ordinary) := by
  rcases writers path key entry body depth ordinary present with impossible | written
  · cases impossible
  · exact written

/-- Both literal raw callbacks of the selected writer reach one actual reader heap. -/
theorem Written.raw_callbacks [DecidableEq (EdgeKey Symbol Guard)]
    {before after : State Symbol Guard} {key : NodeKey} {value : Value Symbol Guard}
    (written : Written before after key value) :
    ∃ event : Publication (Symbol := Symbol) (Guard := Guard),
      key = event.key ∧ value = event.candidate ∧
      ∃ rawOrdinary ordinaryHeap rawBody bodyHeap,
        InternedFreshOrdinaryConstruction.build event.expression
          (.reference (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel event.depth)) :: event.environment)
          event.afterDepth = .done rawOrdinary ordinaryHeap ∧
        run (withoutSelfReference (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel event.depth))
          rawOrdinary) ordinaryHeap = (event.ordinary, event.cut) ∧
        InternedFreshOrdinaryConstruction.build event.expression
          (.reference (.interned event.entry.identity) :: event.environment) event.allocated = .done rawBody bodyHeap ∧
        run (withoutSelfReference (.interned event.entry.identity) rawBody) bodyHeap = (event.body, event.afterBody) ∧
        Grows ordinaryHeap after ∧ Grows bodyHeap after := by
  obtain ⟨event, sameKey, sameValue, _, _, _, _, _, growth⟩ := written
  obtain ⟨ordinary, ordinaryHeap, body, bodyHeap, ordinaryDone, ordinaryFilter, bodyDone, bodyFilter,
    ordinaryGrowth, bodyGrowth, _, _⟩ := SourceCurrentNativeMuPublicationCallbacks.raw_callbacks event
  have finalGrowth := grows_trans (publication_growth event) growth
  exact ⟨event, sameKey, sameValue, ordinary, ordinaryHeap, body, bodyHeap,
    ordinaryDone, ordinaryFilter, bodyDone, bodyFilter,
    grows_trans ordinaryGrowth finalGrowth, grows_trans bodyGrowth finalGrowth⟩

end MicroCFTA.SourceCurrentNativeMuGrowthWriters
