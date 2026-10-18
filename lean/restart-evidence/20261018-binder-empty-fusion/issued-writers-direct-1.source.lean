import MicroCFTA.SourceCurrentNativeMuIssuedHistory
import MicroCFTA.SourceCurrentNativeMuGrowthWriters
import MicroCFTA.SourceCurrentGeneratedHistoricalContext

/-!
# Selected writers retain unused issued captures

Actual issued-reference paths recover the selected earlier publication.
The writer-to-reader suffix retains every issued node name. Both original
callback contexts and adjacent source/filter calls then hold at the reader.
The old four-table growth and writer contracts remain unchanged.
-/
namespace MicroCFTA.SourceCurrentNativeMuIssuedWriters
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open SourceCurrentNativeMuPublication (Publication)
open SourceCurrentNativeMuIssuedHistory
open SourceCurrentNativeMuGrowthHistory (reserve_growth publication_growth)


private theorem reserve_issued [DecidableEq (EdgeKey Symbol Guard)]
    (event : Publication (Symbol := Symbol) (Guard := Guard)) :
    Extends event.cut.nodes.issued event.allocated.nodes.issued := by
  have cutContext := (SourceCurrentNativeMuPublicationCallbacks.contexts event).2.1
  exact InternedFreshProbeKeys.intern_issued_extends event.cut.nodes event.key cutContext.base.normal.facts.coherent.valid.2

/-- A selected writer retains its exact prefix, callbacks, and later cache growth. -/
def Written [DecidableEq (EdgeKey Symbol Guard)] (before after : State Symbol Guard)
    (key : NodeKey) (value : Value Symbol Guard) : Prop :=
  ∃ event : Publication (Symbol := Symbol) (Guard := Guard),
    key = event.key ∧ value = event.candidate ∧ event.afterBody.nodeRecords event.key = none ∧
    Nonempty (Path before event.before) ∧
    Nonempty (Path event.before event.afterDepth) ∧
    Nonempty (Path event.afterDepth event.cut) ∧
    Nonempty (Path event.allocated event.afterBody) ∧ Grows event.after after ∧ Extends event.after.nodes.issued after.nodes.issued

/-- A preceding actual path preserves the selected publication and its later heap. -/
theorem Written.prepend [DecidableEq (EdgeKey Symbol Guard)]
    {before middle after : State Symbol Guard} {key : NodeKey} {value : Value Symbol Guard}
    (earlier : Path before middle) (written : Written middle after key value) : Written before after key value := by
  obtain ⟨event, key, value, missing, ⟨first⟩, depth, ordinary, body, growth, issued⟩ := written
  exact ⟨event, key, value, missing, ⟨.trans earlier first⟩, depth, ordinary, body, growth, issued⟩

/-- Later cache growth retains the same writer and every earlier callback heap. -/
theorem Written.later [DecidableEq (EdgeKey Symbol Guard)]
    {before middle after : State Symbol Guard} {key : NodeKey} {value : Value Symbol Guard}
    (written : Written before middle key value) (growth : Grows middle after)
    (issued : Extends middle.nodes.issued after.nodes.issued) : Written before after key value := by
  obtain ⟨event, key, value, missing, first, depth, ordinary, body, earlier, earlierIssued⟩ := written
  exact ⟨event, key, value, missing, first, depth, ordinary, body, grows_trans earlier growth, extends_trans earlierIssued issued⟩

/-- The full issued-name receipt retains the earlier selected-writer growth witness. -/
theorem Written.forget [DecidableEq (EdgeKey Symbol Guard)]
    {before after : State Symbol Guard} {key : NodeKey} {value : Value Symbol Guard}
    (written : Written before after key value) : SourceCurrentNativeMuGrowthWriters.Written before after key value := by
  obtain ⟨event, key, value, missing, ⟨first⟩, ⟨depth⟩, ⟨ordinary⟩, ⟨body⟩, growth, _⟩ := written
  exact ⟨event,key,value,missing,⟨first.forget⟩,⟨depth.forget⟩,⟨ordinary.forget⟩,⟨body.forget⟩,growth⟩

/-- A final Mu was present initially or has an actual writer whose heap reaches this reader. -/
theorem writers [DecidableEq (EdgeKey Symbol Guard)] {before after : State Symbol Guard}
    (path : Path before after) (key : NodeKey) (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard)
    (present : after.nodeRecords key = some (.mu entry body depth ordinary)) :
    before.nodeRecords key = some (.mu entry body depth ordinary) ∨
      Written before after key (.mu entry body depth ordinary) := by
  induction path with
  | refl => exact Or.inl present
  | retain before after old _growth _issued => exact Or.inl (old key entry body depth ordinary present)
  | trans first next firstIH nextIH =>
      rcases nextIH present with old | written
      · rcases firstIH old with initial | written
        · exact Or.inl initial
        · exact Or.inr (written.later next.growth next.issued)
      · exact Or.inr (written.prepend first)
  | publication event depthPath ordinaryPath bodyPath depthIH ordinaryIH bodyIH =>
      have reserve : Path event.cut event.allocated :=
        .retain event.cut event.allocated (fun _ _ _ _ _ found => found) (reserve_growth event) (reserve_issued event)
      have cutGrowth : Grows event.cut event.after :=
        grows_trans (reserve_growth event) (grows_trans bodyPath.growth (publication_growth event) (extends_refl _))
      have depthGrowth : Grows event.afterDepth event.after := grows_trans ordinaryPath.growth cutGrowth
      have cutIssued : Extends event.cut.nodes.issued event.after.nodes.issued :=
        extends_trans (reserve_issued event) bodyPath.issued
      have depthIssued : Extends event.afterDepth.nodes.issued event.after.nodes.issued :=
        extends_trans ordinaryPath.issued cutIssued
      have prior (old : event.afterBody.nodeRecords key = some (.mu entry body depth ordinary)) :
          event.before.nodeRecords key = some (.mu entry body depth ordinary) ∨
            Written event.before event.after key (.mu entry body depth ordinary) := by
        rcases bodyIH old with allocated | written
        · rcases ordinaryIH allocated with afterDepth | written
          · rcases depthIH afterDepth with initial | written
            · exact Or.inl initial
            · exact Or.inr (written.later depthGrowth depthIssued)
          · exact Or.inr ((written.prepend depthPath).later cutGrowth cutIssued)
        · exact Or.inr ((written.prepend (.trans (.trans depthPath ordinaryPath) reserve)).later
            (publication_growth event) (extends_refl _))
      rcases record_cases event.afterBody.nodeRecords event.key key event.candidate
        (.mu entry body depth ordinary) present with old | ⟨sameKey, sameValue⟩
      · exact prior old
      · cases firstWrite : event.afterBody.nodeRecords event.key with
        | none => exact Or.inr ⟨event, sameKey, sameValue, firstWrite, ⟨.refl event.before⟩,
            ⟨depthPath⟩, ⟨ordinaryPath⟩, ⟨bodyPath⟩, grows_refl event.after, extends_refl _⟩
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

end MicroCFTA.SourceCurrentNativeMuIssuedWriters
