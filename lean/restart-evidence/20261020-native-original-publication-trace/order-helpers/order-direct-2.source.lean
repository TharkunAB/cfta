import MicroCFTA.SourceCurrentNativeMuIssuedWriters

namespace MicroCFTA.SourceCurrentNativeOriginalPublicationTrace
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedBinderProtocol (NodeKey)
open SourceCurrentNativeMuPublication (Publication)
open SourceCurrentNativeMuIssuedHistory (Path)
open SourceCurrentNativeMuGrowthHistory (reserve_growth publication_growth)
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

/-- Actual callback publications precede their containing completion. -/
def events {before after : State Symbol Guard} : Path before after → List (@Publication Symbol Guard _)
  | .refl _ | .retain _ _ _ _ _ => []
  | .trans first next => events first ++ events next
  | .publication event depth ordinary body => events depth ++ events ordinary ++ events body ++ [event]

private def WrittenIn (all : List (@Publication Symbol Guard _))
    (before after : State Symbol Guard) (key : NodeKey) (value : Value Symbol Guard) : Prop :=
  ∃ i : Nat, ∃ event : @Publication Symbol Guard _, all[i]? = some event ∧ key = event.key ∧ value = event.candidate ∧
    event.afterBody.nodeRecords event.key = none ∧
    Nonempty (Path before event.before) ∧
    Nonempty (Path event.before event.afterDepth) ∧
    Nonempty (Path event.afterDepth event.cut) ∧
    Nonempty (Path event.allocated event.afterBody) ∧
    Grows event.after after ∧ Extends event.after.nodes.issued after.nodes.issued

private theorem written_append {all : List (@Publication Symbol Guard _)}
    {before middle after : State Symbol Guard} {key : NodeKey} {value : Value Symbol Guard}
    (written : WrittenIn all before middle key value) (tail : List (@Publication Symbol Guard _))
    (growth : Grows middle after) (issued : Extends middle.nodes.issued after.nodes.issued) :
    WrittenIn (all ++ tail) before after key value := by
  obtain ⟨i,event,found,keySame,valueSame,missing,earlier,depth,ordinary,body,oldGrowth,oldIssued⟩ := written
  have bounded := (List.getElem?_eq_some_iff.mp found).1
  exact ⟨i,event,(List.getElem?_append_left bounded).trans found,keySame,valueSame,missing,
    earlier,depth,ordinary,body,grows_trans oldGrowth growth,extends_trans oldIssued issued⟩

private theorem written_prepend {all : List (@Publication Symbol Guard _)}
    {before middle after : State Symbol Guard} {key : NodeKey} {value : Value Symbol Guard}
    (earlierPath : Path before middle) (written : WrittenIn all middle after key value) :
    WrittenIn (events earlierPath ++ all) before after key value := by
  obtain ⟨i,event,found,keySame,valueSame,missing,⟨earlier⟩,depth,ordinary,body,growth,issued⟩ := written
  refine ⟨(events earlierPath).length + i,event,?_,keySame,valueSame,missing,
    ⟨.trans earlierPath earlier⟩,depth,ordinary,body,growth,issued⟩
  simpa only [List.getElem?_append_right (Nat.le_add_right _ _),Nat.add_sub_cancel_left] using found

private theorem reserve_issued (event : @Publication Symbol Guard _) :
    Extends event.cut.nodes.issued event.allocated.nodes.issued := by
  have context := (SourceCurrentNativeMuPublicationCallbacks.contexts event).2.1
  exact InternedFreshProbeKeys.intern_issued_extends event.cut.nodes event.key context.base.normal.facts.coherent.valid.2

private def reserve_path (event : @Publication Symbol Guard _) : Path event.cut event.allocated :=
  .retain _ _ (fun _ _ _ _ _ present => present) (reserve_growth event) (reserve_issued event)

private theorem writers_in {before after : State Symbol Guard}
    (path : Path before after) (key : NodeKey) (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard)
    (present : after.nodeRecords key = some (.mu entry body depth ordinary)) :
    before.nodeRecords key = some (.mu entry body depth ordinary) ∨
      WrittenIn (events path) before after key (.mu entry body depth ordinary) := by
  induction path with
  | refl => exact .inl present
  | retain before after old _growth _issued => exact .inl (old key entry body depth ordinary present)
  | trans first next firstIH nextIH =>
      rcases nextIH present with old | written
      · rcases firstIH old with initial | written
        · exact .inl initial
        · exact .inr (written_append written (events next) next.growth next.issued)
      · exact .inr (written_prepend first written)
  | publication event depthPath ordinaryPath bodyPath depthIH ordinaryIH bodyIH =>
      have cutGrowth : Grows event.cut event.after :=
        grows_trans (reserve_growth event) (grows_trans bodyPath.growth (publication_growth event))
      have depthGrowth : Grows event.afterDepth event.after := grows_trans ordinaryPath.growth cutGrowth
      have cutIssued : Extends event.cut.nodes.issued event.after.nodes.issued :=
        extends_trans (reserve_issued event) bodyPath.issued
      have depthIssued : Extends event.afterDepth.nodes.issued event.after.nodes.issued :=
        extends_trans ordinaryPath.issued cutIssued
      have prior (old : event.afterBody.nodeRecords key = some (.mu entry body depth ordinary)) :
          event.before.nodeRecords key = some (.mu entry body depth ordinary) ∨
            WrittenIn (events (.publication event depthPath ordinaryPath bodyPath))
              event.before event.after key (.mu entry body depth ordinary) := by
        rcases bodyIH old with allocated | written
        · rcases ordinaryIH allocated with afterDepth | written
          · rcases depthIH afterDepth with initial | written
            · exact .inl initial
            · exact .inr (by simpa only [events,List.append_assoc] using
                written_append written (events ordinaryPath ++ events bodyPath ++ [event]) depthGrowth depthIssued)
          · have later := written_append written (events bodyPath ++ [event]) cutGrowth cutIssued
            exact .inr (by simpa only [events,List.append_assoc] using written_prepend depthPath later)
        · have later := written_append written [event] (publication_growth event) (extends_refl _)
          have joined := written_prepend (.trans depthPath (.trans ordinaryPath (reserve_path event))) later
          exact .inr (by simpa only [events,List.nil_append,List.append_assoc] using joined)
      rcases record_cases event.afterBody.nodeRecords event.key key event.candidate
        (.mu entry body depth ordinary) present with old | ⟨sameKey,sameValue⟩
      · exact prior old
      · cases firstWrite : event.afterBody.nodeRecords event.key with
        | none =>
            refine .inr ⟨(events depthPath).length + (events ordinaryPath).length + (events bodyPath).length,
              event,?_,sameKey,sameValue,firstWrite,⟨.refl _⟩,⟨depthPath⟩,⟨ordinaryPath⟩,⟨bodyPath⟩,
              grows_refl _,extends_refl _⟩
            simpa only [events,List.length_append] using
              (List.getElem?_concat_length (l := events depthPath ++ events ordinaryPath ++ events bodyPath) (a := event))
        | some previous =>
            apply prior
            change keepFirst event.afterBody.nodeRecords event.key event.candidate key =
              some (.mu entry body depth ordinary) at present
            simpa only [keepFirst,firstWrite] using present

private theorem indexed_writers {before after : State Symbol Guard}
    (path : Path before after) (key : NodeKey) (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard)
    (present : after.nodeRecords key = some (.mu entry body depth ordinary)) :
    before.nodeRecords key = some (.mu entry body depth ordinary) ∨
      ∃ i : Nat, ∃ event : @Publication Symbol Guard _, (events path)[i]? = some event ∧ key = event.key ∧
        Value.mu entry body depth ordinary = event.candidate ∧ event.afterBody.nodeRecords event.key = none ∧
        Nonempty (Path before event.before) ∧ Nonempty (Path event.before event.afterDepth) ∧
        Nonempty (Path event.afterDepth event.cut) ∧ Nonempty (Path event.allocated event.afterBody) ∧
        Grows event.after after ∧ Extends event.after.nodes.issued after.nodes.issued :=
  writers_in path key entry body depth ordinary present

private theorem before_publication {before after : State Symbol Guard} (path : Path before after)
    (j : Nat) (outer : @Publication Symbol Guard _) (found : (events path)[j]? = some outer) :
    ∃ earlierPath : Path before outer.afterBody, ∃ tail : List (@Publication Symbol Guard _),
      events path = events earlierPath ++ tail ∧ (events earlierPath).length = j := by
  induction path generalizing j outer with
  | refl | retain => simp only [events,List.getElem?_nil] at found; cases found
  | trans first next firstIH nextIH =>
      by_cases left : j < (events first).length
      · have chosen : (events first)[j]? = some outer := by
          simpa only [events,List.getElem?_append_left left] using found
        obtain ⟨earlierPath,tail,same,length⟩ := firstIH j outer chosen
        exact ⟨earlierPath,tail ++ events next,by simp only [events,same,List.append_assoc],length⟩
      · have chosen : (events next)[j - (events first).length]? = some outer := by
          simpa only [events,List.append_assoc,List.getElem?_append_right (by omega)] using found
        obtain ⟨earlierPath,tail,same,length⟩ := nextIH _ outer chosen
        refine ⟨.trans first earlierPath,tail,?_,?_⟩
        · simp only [events,same,List.append_assoc]
        · simp only [events,List.length_append]
          omega
  | publication event depthPath ordinaryPath bodyPath depthIH ordinaryIH bodyIH =>
      by_cases inDepth : j < (events depthPath).length
      · have chosen : (events depthPath)[j]? = some outer := by
          simpa only [events,List.append_assoc,List.getElem?_append_left inDepth] using found
        obtain ⟨earlierPath,tail,same,length⟩ := depthIH j outer chosen
        exact ⟨earlierPath,tail ++ events ordinaryPath ++ events bodyPath ++ [event],
          by simp only [events,same,List.append_assoc],length⟩
      · have afterDepth : (events ordinaryPath ++ events bodyPath ++ [event])[j - (events depthPath).length]? = some outer := by
          simpa only [events,List.append_assoc,List.getElem?_append_right (by omega)] using found
        by_cases inOrdinary : j - (events depthPath).length < (events ordinaryPath).length
        · have chosen : (events ordinaryPath)[j - (events depthPath).length]? = some outer := by
            simpa only [List.append_assoc,List.getElem?_append_left inOrdinary] using afterDepth
          obtain ⟨earlierPath,tail,same,length⟩ := ordinaryIH _ outer chosen
          refine ⟨.trans depthPath earlierPath,tail ++ events bodyPath ++ [event],?_,?_⟩
          · simp only [events,same,List.append_assoc]
          · simp only [events,List.length_append]
            omega
        · have afterOrdinary : (events bodyPath ++ [event])[j - (events depthPath).length - (events ordinaryPath).length]? = some outer := by
            simpa only [List.append_assoc,List.getElem?_append_right (by omega)] using afterDepth
          by_cases inBody : j - (events depthPath).length - (events ordinaryPath).length < (events bodyPath).length
          · have chosen : (events bodyPath)[j - (events depthPath).length - (events ordinaryPath).length]? = some outer := by
              simpa only [List.append_assoc,List.getElem?_append_left inBody] using afterOrdinary
            obtain ⟨earlierPath,tail,same,length⟩ := bodyIH _ outer chosen
            refine ⟨.trans depthPath (.trans ordinaryPath (.trans (reserve_path event) earlierPath)),tail ++ [event],?_,?_⟩
            · simp only [events,reserve_path,same,List.nil_append,List.append_assoc]
            · simp only [events,reserve_path,List.length_append,List.length_nil]
              omega
          · have last : ([event] : List (@Publication Symbol Guard _))[j - (events depthPath).length -
                (events ordinaryPath).length - (events bodyPath).length]? = some outer := by
                simpa only [List.getElem?_append_right (by omega)] using afterOrdinary
            have bounded := (List.getElem?_eq_some_iff.mp last).1
            have zero : j - (events depthPath).length - (events ordinaryPath).length - (events bodyPath).length = 0 := by
              simp only [List.length_singleton] at bounded
              omega
            have sameEvent : event = outer := by simpa only [zero,List.getElem?_cons_zero,Option.some.injEq] using last
            subst outer
            refine ⟨.trans depthPath (.trans ordinaryPath (.trans (reserve_path event) bodyPath)),[event],?_,?_⟩
            · simp only [events,reserve_path,List.nil_append,List.append_assoc]
            · simp only [events,reserve_path,List.length_append,List.length_nil]
              omega

private theorem precompletion_writers {before after : State Symbol Guard}
    (path : Path before after) (j : Nat) (outer : @Publication Symbol Guard _)
    (found : (events path)[j]? = some outer)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (present : outer.afterBody.nodeRecords key = some (.mu entry body depth ordinary)) :
    before.nodeRecords key = some (.mu entry body depth ordinary) ∨
      ∃ i : Nat, ∃ earlier : @Publication Symbol Guard _, i < j ∧ (events path)[i]? = some earlier ∧ key = earlier.key ∧
        Value.mu entry body depth ordinary = earlier.candidate ∧ earlier.afterBody.nodeRecords earlier.key = none ∧
        Nonempty (Path before earlier.before) ∧ Nonempty (Path earlier.before earlier.afterDepth) ∧
        Nonempty (Path earlier.afterDepth earlier.cut) ∧ Nonempty (Path earlier.allocated earlier.afterBody) ∧
        Grows earlier.after outer.afterBody ∧ Extends earlier.after.nodes.issued outer.afterBody.nodes.issued := by
  obtain ⟨earlierPath,tail,same,length⟩ := before_publication path j outer found
  rcases indexed_writers earlierPath key entry body depth ordinary present with initial | written
  · exact .inl initial
  · obtain ⟨i,earlier,chosen,rest⟩ := written
    have bounded := (List.getElem?_eq_some_iff.mp chosen).1
    refine .inr ⟨i,earlier,by omega,?_,rest⟩
    rw [same,List.getElem?_append_left bounded]
    exact chosen

end MicroCFTA.SourceCurrentNativeOriginalPublicationTrace
