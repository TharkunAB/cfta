import MicroCFTA.SourceCurrentMemoMergeOrigins
import MicroCFTA.SourceCurrentMemoMergeNoReentry
import MicroCFTA.EqualityLeafProjectionPhysical

/-!
# Positive row origins of actual memo-aware Merge calls

Each completed memo entry retains its actual historical body and its entry
physical facts. A positive returned row keeps an indexed input row and its
full fields. Its children retain actual ordered recursive Merge calls.
This does not identify the returned children with the original children.
-/
namespace MicroCFTA.SourceCurrentMergePositiveRowOrigins
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentMemoMergeGraph
open SourceCurrentMemoMergeEffects (Effect Stored Certified Contract ValueReady EdgeReady)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type}
variable [symbolEq : DecidableEq Symbol] [edgeEq : DecidableEq (EdgeKey Symbol Guard)]

/-- A writer retains the literal body and the physical facts at its historical entry. -/
def Writer (clear : Guard → Bool) (top : Guard) (input output : Value Symbol Guard) : Prop :=
  ∃ before memo after saved, SemanticReady before ∧ CostHeap before ∧ Stored before memo ∧
    Available before input ∧ Run clear top (body top input) before memo output after saved

/-- Completed entries retain their exact physical keys and actual historical writers. -/
def Raw (clear : Guard → Bool) (top : Guard) (memo : Memo Symbol Guard) : Prop :=
  ∀ key entry, memo key = some entry → entry.original.referenceOf = key ∧
    Writer clear top entry.original entry.result

private theorem raw_remember {clear : Guard → Bool} {top : Guard} {memo : Memo Symbol Guard}
    (raw : Raw clear top memo) (input output : Value Symbol Guard) (writer : Writer clear top input output) :
    Raw clear top (remember memo input output) := by
  intro key entry found
  rcases InternedRecordCoherence.record_cases memo input.referenceOf key ⟨input,output⟩ entry found with old | ⟨same,equal⟩
  · exact raw key entry old
  · cases equal
    exact ⟨same.symm,writer⟩

private theorem run_raw {clear : Guard → Bool} {top : Guard} {code : Code Symbol Guard Output}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} {output : Output}
    (actual : Run clear top code before memo output after saved) :
    ∀ post, SemanticReady before → CostHeap before → Stored before memo → Raw clear top memo →
      Certified Contract clear code before post →
      Effect before after ∧ Stored after saved ∧ Raw clear top saved ∧ post after output := by
  induction actual using Run.rec
      (motive_2 := fun input before memo output after saved _ =>
        SemanticReady before → CostHeap before → Stored before memo → @Raw Symbol Guard symbolEq edgeEq clear top memo → Available before input →
          Effect before after ∧ Stored after saved ∧ @Raw Symbol Guard symbolEq edgeEq clear top saved ∧ Contract input before output after) with
  | pure value state memo =>
      intro post semantic costs stored raw checked
      exact ⟨SourceCurrentMemoMergeEffects.effect_refl _ semantic costs,stored,raw,checked⟩
  | work job state memo =>
      intro post _semantic _costs stored raw checked
      exact ⟨checked.1,stored.grows checked.1.keeps,raw,checked.2⟩
  | select fuel done =>
      intro post semantic costs stored raw checked
      have effects := SourceCurrentMergedHeapEffects.select_effect (fun _ => True) _ fuel _ _
        semantic costs checked.1 _ _ done
      have effect : Effect _ _ := ⟨effects.keeps,effects.semantic,effects.costs⟩
      exact ⟨effect,stored.grows effect.keeps,raw,checked.2.2 fuel _ _ done effect⟩
  | request _actual ih =>
      intro post semantic costs stored raw checked
      obtain ⟨effect,nextStored,nextRaw,returned⟩ := ih semantic costs stored raw checked.1
      exact ⟨effect,nextStored,nextRaw,checked.2 _ _ effect returned⟩
  | bind _first _later first later =>
      intro post semantic costs stored raw checked
      obtain ⟨middle,checkedFirst,checkedLater⟩ := checked
      obtain ⟨effect,middleStored,middleRaw,valid⟩ := first middle semantic costs stored raw checkedFirst
      obtain ⟨tail,finalStored,finalRaw,returned⟩ := later post effect.semantic effect.costs middleStored middleRaw
        (checkedLater _ _ effect valid)
      exact ⟨effect.trans tail,finalStored,finalRaw,returned⟩
  | hit found =>
      rename_i semantic costs stored raw available
      obtain ⟨same,result,closed⟩ := SourceCurrentMemoMergeEffects.hit_original semantic available stored found
      exact ⟨SourceCurrentMemoMergeEffects.effect_refl _ semantic costs,stored,raw,result,closed⟩
  | @miss memo input before candidate after current _absent actual ih =>
      rename_i semantic costs stored raw available
      obtain ⟨effect,nextStored,nextRaw,result,closed⟩ := ih _ semantic costs stored raw
        (SourceCurrentMemoMergeEffects.body_certified _ _ input before semantic costs available)
      have inputAvailable := effect.keeps.available input available
      have finalStored := SourceCurrentMemoMergeEffects.stored_remember nextStored input candidate inputAvailable result closed
      have finalRaw := raw_remember nextRaw input candidate ⟨before,memo,after,current,semantic,costs,stored,available,actual⟩
      obtain ⟨_same,winnerAvailable,winnerClosed⟩ := SourceCurrentMemoMergeEffects.hit_original
        effect.semantic inputAvailable finalStored (winner_found current input candidate)
      exact ⟨effect,finalStored,finalRaw,winnerAvailable,winnerClosed⟩

/-- A literal call preserves historical writers and identifies the actual warm or cold returned writer. -/
theorem call {clear : Guard → Bool} {top : Guard} {input output : Value Symbol Guard}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : Call clear top input before memo output after saved)
    (semantic : SemanticReady before) (costs : CostHeap before) (stored : Stored before memo)
    (raw : Raw clear top memo) (available : Available before input) :
    Raw clear top saved ∧ Writer clear top input output := by
  obtain ⟨effect,finalStored,finalRaw,_returned⟩ := run_raw (.request actual)
    (fun heap value => Contract input before value heap) semantic costs stored raw
    ⟨available,fun _ _ _ returned => returned⟩
  obtain ⟨entry,found,sameOutput⟩ := SourceCurrentMemoMergeOrigins.call_returned actual
  obtain ⟨sameInput,_available,_closed⟩ := SourceCurrentMemoMergeEffects.hit_original
    effect.semantic (effect.keeps.available input available) finalStored found
  exact ⟨finalRaw,by simpa only [sameInput,sameOutput] using (finalRaw _ _ found).2⟩

private theorem bind_parts {clear : Guard → Bool} {top : Guard} {first : Code Symbol Guard A}
    {next : A → Code Symbol Guard B} {before after : State Symbol Guard}
    {memo saved : Memo Symbol Guard} {output : B}
    (actual : Run clear top (.bind first next) before memo output after saved) :
    ∃ value middle current, Run clear top first before memo value middle current ∧
      Run clear top (next value) middle current output after saved := by
  cases actual with
  | bind first later => exact ⟨_,_,_,first,later⟩

private theorem map_member {clear : Guard → Bool} {top : Guard}
    (f : A → Code Symbol Guard B) (pre : State Symbol Guard → A → Prop)
    (post : State Symbol Guard → B → Prop)
    (preGrows : ∀ before after, Effect before after → ∀ input, pre before input → pre after input)
    (checked : ∀ input, ∀ before, SemanticReady before → CostHeap before → pre before input →
      Certified Contract clear (f input) before post)
    {inputs : List A} {outputs : List B} {before after : State Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : Run clear top (map f inputs) before memo outputs after saved)
    (semantic : SemanticReady before) (costs : CostHeap before) (stored : Stored before memo)
    (ready : ∀ input ∈ inputs, pre before input) {output : B} (member : output ∈ outputs) :
    ∃ input ∈ inputs, ∃ start current finish final, SemanticReady start ∧ CostHeap start ∧
      Stored start current ∧ pre start input ∧ Run clear top (f input) start current output finish final := by
  induction inputs generalizing outputs before memo with
  | nil =>
      obtain ⟨rfl,_⟩ := Run.pure_iff.mp actual
      cases member
  | cons input inputs ih =>
      obtain ⟨head,middle,current,first,rest⟩ := bind_parts actual
      obtain ⟨tail,last,completed,later,done⟩ := bind_parts rest
      obtain ⟨rfl,rfl,rfl⟩ := Run.pure_iff.mp done
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨input,List.mem_cons_self,before,memo,middle,current,semantic,costs,stored,
          ready input List.mem_cons_self,first⟩
      · obtain ⟨effect,middleStored,_headReady⟩ := SourceCurrentMemoMergeEffects.run_effects first post semantic costs stored
          (checked input before semantic costs (ready input List.mem_cons_self))
        obtain ⟨original,present,start,current,finish,final,known,costs,stored,admitted,called⟩ := ih later
          effect.semantic effect.costs middleStored
          (fun value member => preGrows before middle effect value (ready value (List.mem_cons_of_mem _ member))) member
        exact ⟨original,List.mem_cons_of_mem _ present,start,current,finish,final,known,costs,stored,admitted,called⟩

private theorem small_parts {clear : Guard → Bool} {top : Guard} {original output : EdgeValue Symbol Guard}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : Run clear top (small original) before memo output after saved)
    (semantic : SemanticReady before) (costs : CostHeap before) (stored : Stored before memo)
    (ready : EdgeReady before original) :
    output.entry.key.symbol = original.entry.key.symbol ∧ output.entry.key.constraint = original.entry.key.constraint ∧
      ∃ values middle current, Run clear top (map Code.request original.children) before memo values middle current ∧
        run (makeEdge original.entry.key.symbol original.entry.key.constraint values) middle = (output,after) ∧
        output.children = values := by
  obtain ⟨values,middle,current,children,made⟩ := bind_parts actual
  obtain ⟨rfl,rfl,rfl⟩ := Run.work_iff.mp made
  have inputs := semantic.ready.semantic.1.normal.facts.cached.edges original.entry.key _ ready.1
  have certified := SourceCurrentMemoMergeEffects.map_certified Contract clear Code.request ValueReady ValueReady
    (fun _ _ effect value => SourceCurrentMemoMergeEffects.value_grows effect value)
    (fun _ _ effect value => SourceCurrentMemoMergeEffects.value_grows effect value)
    original.children (fun value _ heap _ _ valid => SourceCurrentMemoMergeEffects.request_certified clear value heap valid)
    before semantic costs (fun value member => ⟨inputs value member,ready.2 value member⟩)
  obtain ⟨effect,_nextStored,available⟩ := SourceCurrentMemoMergeEffects.run_effects children _ semantic costs stored certified
  have facts := effect.semantic.ready.semantic.1.normal.facts
  have fields := MergedPhysicalGroupEdges.makeEdge_fields middle facts _ _ values
    (fun value member => (available value member).1)
  exact ⟨fields.1,fields.2.1,values,middle,current,children,rfl,fields.2.2⟩

end MicroCFTA.SourceCurrentMergePositiveRowOrigins
