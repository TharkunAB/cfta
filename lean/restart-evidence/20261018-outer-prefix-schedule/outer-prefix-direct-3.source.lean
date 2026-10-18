import MicroCFTA.SourceCurrentOuterInitialActual
import MicroCFTA.SourceCurrentOuterPrefixInvariants
import MicroCFTA.SourceCurrentOuterInitialFuel

/-!
# Initial resources at literal outer prefixes

Each completed sibling supplies its actual semantic and resource receipt.
The prefix proof retains the exact current seed and its source schedule.
No final outcome of the whole outer call is required.
-/
namespace MicroCFTA.SourceCurrentOuterInitialPrefix
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile Le Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentOuterCopiedWarmHit (Phase)
open SourceCurrentOuterExecutionAncestry (Step Reached)
open SourceCurrentOuterPrefixInvariants (Inputs)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Carrier" => SourceEqualityAnnotationHeap.Heap
local notation "Seed" => List Guard × Profile
local notation "caller" => SourceCurrentOuterActiveAncestry.caller
namespace Schedule
export SourceCurrentOuterInitialSchedule
  (parent rebuild node body rows descendants children walk parent_ge rebuild_ge node_ge body_ge
    rows_ge descendants_ge children_ge walk_ge parent_reserved)
end Schedule

/-- The current phase selects its initial pure resource schedule. -/
noncomputable def forecast (budget : Nat) (phase : Phase width) (seed : Seed) : Seed :=
  match phase with
  | .node fuel .. => Schedule.node fuel budget seed
  | .body fuel .. => Schedule.body fuel budget seed
  | .rows fuel .. => Schedule.rows fuel budget seed
  | .descendants fuel .. => Schedule.descendants fuel budget seed
  | .children fuel .. => Schedule.children fuel budget seed
  | .walk fuel .. => Schedule.walk fuel budget seed

/-- Every phase forecast retains its initial numeric bounds and guards. -/
theorem forecast_ge (budget : Nat) (phase : Phase width) (seed : Seed) :
    Le seed.2 (forecast budget phase seed).2 ∧ seed.1 ⊆ (forecast budget phase seed).1 := by
  cases phase with
  | node => exact Schedule.node_ge _ _ _
  | body => exact Schedule.body_ge _ _ _
  | rows => exact Schedule.rows_ge _ _ _
  | descendants => exact Schedule.descendants_ge _ _ _
  | children => exact Schedule.children_ge _ _ _
  | walk => exact Schedule.walk_ge _ _ _

/-- On a literal step, the phase pair determines the exact next resource seed. -/
noncomputable def StepSeed (budget : Nat) (first last : Phase width) (entry next : Seed) : Prop :=
  match first, last with
  | .rows (_+1) .., .descendants .. => next = Schedule.parent budget entry
  | .rows (fuel+1) .., .rows .. => next = Schedule.descendants fuel budget (Schedule.parent budget entry)
  | .walk (fuel+1) .., .walk .. => next = Schedule.node fuel budget entry
  | _, _ => next = entry

/-- Seed changes follow the same exact literal prefix proof. -/
inductive SeedTrace {g s r e p h m c n budget : Nat} :
    {first last : Phase width} → Reached g s r e p h m c n budget first last → Seed → Seed → Prop where
  /-- A zero-step prefix retains its initial seed. -/
  | refl (phase : Phase width) (seed : Seed) : SeedTrace (.refl phase) seed seed
  /-- One literal step retains the preceding exact seed changes. -/
  | snoc {first middle last : Phase width} {earlier : Reached g s r e p h m c n budget first middle}
      {step : Step g s r e p h m c n budget middle last} {entry current next : Seed}
      (past : SeedTrace earlier entry current) (change : StepSeed budget middle last current next) :
      SeedTrace (.snoc earlier step) entry next

private theorem step_need {g s r e p h m c n budget : Nat} {first last : Phase width}
    (actual : Step g s r e p h m c n budget first last) {entry next : Seed}
    (change : StepSeed budget first last entry next) :
    SourceCurrentOuterInitialFuel.phaseNeed budget last next ≤ SourceCurrentOuterInitialFuel.phaseNeed budget first entry := by
  cases actual with
  | node_evaluate =>
      dsimp only [StepSeed] at change
      subst next
      simp only [SourceCurrentOuterInitialFuel.phaseNeed,SourceCurrentOuterInitialFuel.nodeNeed]
  | body_rows =>
      dsimp only [StepSeed] at change
      subst next
      simp only [SourceCurrentOuterInitialFuel.phaseNeed,SourceCurrentOuterInitialFuel.bodyNeed]
  | rows_edge =>
      dsimp only [StepSeed] at change
      subst next
      exact SourceCurrentOuterInitialFuel.rows_descendants_le _ _ _
  | rows_tail =>
      dsimp only [StepSeed] at change
      subst next
      exact SourceCurrentOuterInitialFuel.rows_tail_le _ _ _
  | descendants_children =>
      dsimp only [StepSeed] at change
      subst next
      simp only [SourceCurrentOuterInitialFuel.phaseNeed,SourceCurrentOuterInitialFuel.descendantsNeed]
  | children_walk =>
      dsimp only [StepSeed] at change
      subst next
      simp only [SourceCurrentOuterInitialFuel.phaseNeed,SourceCurrentOuterInitialFuel.childrenNeed]
  | walk_head =>
      dsimp only [StepSeed] at change
      subst next
      exact SourceCurrentOuterInitialFuel.walk_node_le _ _ _
  | walk_tail =>
      dsimp only [StepSeed] at change
      subst next
      exact SourceCurrentOuterInitialFuel.walk_tail_le _ _ _

private theorem trace_need {g s r e p h m c n budget : Nat} {first last : Phase width}
    {actual : Reached g s r e p h m c n budget first last} {entry next : Seed}
    (trace : SeedTrace actual entry next) :
    SourceCurrentOuterInitialFuel.phaseNeed budget last next ≤ SourceCurrentOuterInitialFuel.phaseNeed budget first entry := by
  induction trace with
  | refl => exact Nat.le_refl _
  | snoc past change ih => exact (step_need _ change).trans ih

private def Below (first last : Seed) : Prop := Le first.2 last.2 ∧ first.1 ⊆ last.1

private theorem below_refl (seed : Seed) : Below seed seed := ⟨Le.refl _,fun _ member => member⟩

private theorem below_trans {first middle last : Seed} (one : Below first middle) (two : Below middle last) :
    Below first last := ⟨one.1.trans two.1,fun _ member => two.2 (one.2 member)⟩

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {bits : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

private theorem one_step {g s r e p h m c n budget : Nat} {first last : Phase (bits+2)}
    (actual : Step g s r e p h m c n budget first last)
    {inventory : Inventory} {memos : Memos} (seed : Seed)
    (initial : Context formulas solver inventory (caller first) memos)
    (frame : Frame formulas solver inventory (caller first).checked)
    (fits : Fits seed.2 (caller first).checked)
    (known : Carrier (fun guard => guard ∈ seed.1) (caller first).checked.native.machine.heap)
    (inputs : Inputs first) (room : Room bits (forecast budget first seed).2) :
    ∃ next final current, Post formulas solver next (caller first) (caller last) final ∧
      Frame formulas solver next (caller last).checked ∧ Fits current.2 (caller last).checked ∧
      Carrier (fun guard => guard ∈ current.1) (caller last).checked.native.machine.heap ∧ Inputs last ∧
      StepSeed budget first last seed current ∧ Below (forecast budget last current) (forecast budget first seed) := by
  cases actual with
  | node_evaluate started =>
      rename_i request before handle running owner fuel
      obtain ⟨context,ownerReady,_key,_cell⟩ := SourceCurrentAllocatedPartialCallSteps.node_start formulas solver
        initial inputs.1 inputs.2 started
      have components := beginNode_components request before
      rw [started] at components
      dsimp only at components
      obtain ⟨checked,merge,fourth,_⟩ := components
      exact ⟨inventory,memos,seed,Post.rebase initial checked merge fourth context.sound,
        (by simpa only [SourceCurrentOuterActiveAncestry.caller,checked] using frame),(by simpa only [SourceCurrentOuterActiveAncestry.caller,checked] using fits),
        (by simpa only [SourceCurrentOuterActiveAncestry.caller,checked] using known),⟨ownerReady.inherited,ownerReady.input⟩,rfl,
        (by simpa only [forecast,Schedule.node] using below_refl (Schedule.body fuel budget seed))⟩
  | body_rows shaped =>
      have resident := InternedEdgeResidency.resident_edges _
        initial.ready.semantic.ready.semantic.1.normal.facts.linked _ inputs.2.resident
      exact ⟨inventory,memos,seed,Post.refl initial,frame,fits,known,
        ⟨inputs.1,(by simpa only [shaped,InternedEdgeResidency.nodeEdges,SourceCurrentOuterActiveAncestry.caller,Edges] using resident)⟩,rfl,(by simpa only [forecast,Schedule.body,Below] using Schedule.rebuild_ge _)⟩
  | rows_edge done =>
      rename_i fuel inherited original before narrowed middle rest
      simp only [forecast,Schedule.rows] at room
      let current := Schedule.parent budget seed
      have parentRoom : Room bits current.2 := room.mono
        ((Schedule.descendants_ge fuel budget current).1.trans
          (Schedule.rows_ge fuel budget (Schedule.descendants fuel budget current)).1)
      obtain ⟨next,final,receipt,numeric,carrier⟩ := SourceCurrentOuterEdgeGuardAlphabet.edge_call
        formulas solver inventory budget seed.1 ⟨inherited,original⟩ before memos initial frame seed.2 fits known
        inputs.1 (inputs.2 _ List.mem_cons_self) (Schedule.parent_reserved bits budget seed parentRoom) done
      exact ⟨next,final,current,receipt.post,receipt.frame,numeric,carrier,
        ⟨inputs.1.grows receipt.post.effects.grows.constraint_growth,receipt.semantic.resident⟩,rfl,
        (by simpa only [forecast,Schedule.rows,Below,current] using Schedule.rows_ge fuel budget (Schedule.descendants fuel budget current))⟩
  | rows_tail edge children =>
      rename_i fuel inherited original before narrowed middle result after rest
      simp only [forecast,Schedule.rows] at room
      let parentSeed := Schedule.parent budget seed
      let current := Schedule.descendants fuel budget parentSeed
      have parentRoom : Room bits parentSeed.2 := room.mono
        ((Schedule.descendants_ge fuel budget parentSeed).1.trans (Schedule.rows_ge fuel budget current).1)
      obtain ⟨edgeInventory,edgeMemos,receipt,numeric,carrier⟩ := SourceCurrentOuterEdgeGuardAlphabet.edge_call
        formulas solver inventory budget seed.1 ⟨inherited,original⟩ before memos initial frame seed.2 fits known
        inputs.1 (inputs.2 _ List.mem_cons_self) (Schedule.parent_reserved bits budget seed parentRoom) edge
      have descendantRoom : Room bits current.2 := room.mono (Schedule.rows_ge fuel budget current).1
      obtain ⟨next,final,_graph,_reads,post,returned,numeric,carrier,_resident,_law⟩ :=
        SourceCurrentOuterInitialActual.descendants formulas solver fuel parentSeed receipt.post.context receipt.frame
          numeric carrier (inputs.1.grows receipt.post.effects.grows.constraint_growth) receipt.semantic.resident descendantRoom children
      have total := receipt.post.trans post
      exact ⟨next,final,current,total,returned,numeric,carrier,
        ⟨inputs.1.grows total.effects.grows.constraint_growth,fun row member =>
          InternedEdgeResidency.edge_grows _ _ total.effects.keeps.growth _
            (inputs.2 row (List.mem_cons_of_mem _ member))⟩,rfl,
        (by simpa only [forecast,Schedule.rows] using below_refl (Schedule.rows fuel budget current))⟩
  | descendants_children actual =>
      rename_i inherited combined before fuel edge
      obtain ⟨chosen,receipt,returned,numeric,post⟩ := SourceCurrentInheritedNumeric.resident_complete formulas solver
        inventory edge inherited before memos initial frame seed.2 fits (fun _ => inputs.2) (fun _ => inputs.1)
      have same := Option.some.inj (Except.ok.inj (receipt.actual.symm.trans actual))
      subst chosen
      have children := initial.ready.semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge inputs.2
      exact ⟨inventory,memos,seed,post,returned,numeric,known,
        ⟨receipt.combinedReady,fun value member => post.effects.keeps.available _ (children value member)⟩,
        rfl,(by simpa only [forecast,Schedule.descendants,Below] using Schedule.rebuild_ge _)⟩
  | children_walk _ =>
      exact ⟨inventory,memos,seed,Post.refl initial,frame,fits,known,inputs,rfl,
        (by simpa only [forecast,Schedule.children] using below_refl (Schedule.walk _ budget seed))⟩
  | walk_head =>
      rename_i fuel combined index value rest before
      obtain ⟨receipt,returned,numeric,post⟩ := SourceCurrentInheritedNumeric.descent formulas solver
        inventory before memos combined index initial frame seed.2 fits inputs.1
      exact ⟨inventory,memos,seed,post,returned,numeric,known,
        ⟨receipt.inherited,post.effects.keeps.available _ (inputs.2 _ List.mem_cons_self)⟩,rfl,
        (by simpa only [forecast,Schedule.walk,Below] using Schedule.walk_ge fuel budget (Schedule.node fuel budget seed))⟩
  | walk_tail done =>
      rename_i fuel before combined index value result middle rest
      simp only [forecast,Schedule.walk] at room
      obtain ⟨receipt,returned,numeric,post⟩ := SourceCurrentInheritedNumeric.descent formulas solver
        inventory before memos combined index initial frame seed.2 fits inputs.1
      let current := Schedule.node fuel budget seed
      have nodeRoom : Room bits current.2 := room.mono (Schedule.walk_ge fuel budget current).1
      obtain ⟨next,final,_graph,_reads,nodePost,nodeFrame,numeric,carrier,_available,_law⟩ :=
        SourceCurrentOuterInitialActual.node_call formulas solver fuel seed post.context returned numeric known
          receipt.inherited (post.effects.keeps.available _ (inputs.2 _ List.mem_cons_self)) nodeRoom done
      have total := post.trans nodePost
      exact ⟨next,final,current,total,nodeFrame,numeric,carrier,
        ⟨inputs.1.grows total.effects.grows.constraint_growth,fun child member =>
          total.effects.keeps.available _ (inputs.2 child (List.mem_cons_of_mem _ member))⟩,rfl,
        (by simpa only [forecast,Schedule.walk] using below_refl (Schedule.walk fuel budget current))⟩

private theorem prefixes {g s r e p h m c n budget : Nat} {first last : Phase (bits+2)}
    (actual : Reached g s r e p h m c n budget first last) :
    ∀ {inventory : Inventory} {memos : Memos} (seed : Seed),
    Context formulas solver inventory (caller first) memos →
    Frame formulas solver inventory (caller first).checked → Fits seed.2 (caller first).checked →
    Carrier (fun guard => guard ∈ seed.1) (caller first).checked.native.machine.heap →
    Inputs first → Room bits (forecast budget first seed).2 →
    ∃ next final current, Post formulas solver next (caller first) (caller last) final ∧
      Frame formulas solver next (caller last).checked ∧ Fits current.2 (caller last).checked ∧
      Carrier (fun guard => guard ∈ current.1) (caller last).checked.native.machine.heap ∧ Inputs last ∧
      SeedTrace actual seed current ∧ Below (forecast budget last current) (forecast budget first seed) := by
  induction actual with
  | refl phase =>
      intro inventory memos seed initial frame fits known inputs room
      exact ⟨inventory,memos,seed,Post.refl initial,frame,fits,known,inputs,.refl _ _,below_refl _⟩
  | snoc earlier step ih =>
      intro inventory memos seed initial frame fits known inputs room
      obtain ⟨middleInventory,middleMemos,middleSeed,past,middleFrame,middleFits,middleKnown,middleInputs,trace,below⟩ :=
        ih seed initial frame fits known inputs room
      obtain ⟨next,final,current,post,returned,numeric,carrier,currentInputs,change,lastBelow⟩ :=
        one_step formulas solver step middleSeed past.context middleFrame middleFits middleKnown middleInputs (room.mono below.1)
      exact ⟨next,final,current,past.trans post,returned,numeric,carrier,currentInputs,.snoc trace change,
        below_trans lastBelow below⟩

/-- An actual unfinished prefix derives its current semantic and initial scheduled resource facts. -/
theorem reached {g s r e p h m c n budget : Nat} {first last : Phase (bits+2)}
    {inventory : Inventory} {memos : Memos} (seed : Seed)
    (actual : Reached g s r e p h m c n budget first last)
    (initial : Context formulas solver inventory (caller first) memos)
    (frame : Frame formulas solver inventory (caller first).checked)
    (fits : Fits seed.2 (caller first).checked)
    (known : Carrier (fun guard => guard ∈ seed.1) (caller first).checked.native.machine.heap)
    (inputs : Inputs first) (room : Room bits (forecast budget first seed).2) :
    ∃ next final current, SeedTrace actual seed current ∧
      Post formulas solver next (caller first) (caller last) final ∧
      Frame formulas solver next (caller last).checked ∧ Fits current.2 (caller last).checked ∧
      Carrier (fun guard => guard ∈ current.1) (caller last).checked.native.machine.heap ∧ Inputs last ∧
      Le (forecast budget last current).2 (forecast budget first seed).2 ∧
      (forecast budget last current).1 ⊆ (forecast budget first seed).1 ∧
      Room bits (forecast budget last current).2 ∧
      Fits (forecast budget first seed).2 (caller last).checked ∧
      Carrier (fun guard => guard ∈ (forecast budget first seed).1) (caller last).checked.native.machine.heap ∧
      SourceCurrentOuterInitialFuel.phaseNeed budget last current ≤ SourceCurrentOuterInitialFuel.phaseNeed budget first seed := by
  obtain ⟨next,final,current,post,returned,numeric,carrier,currentInputs,trace,below⟩ :=
    prefixes formulas solver actual seed initial frame fits known inputs room
  have growing := forecast_ge budget last current
  exact ⟨next,final,current,trace,post,returned,numeric,carrier,currentInputs,below.1,below.2,room.mono below.1,
    numeric.mono (growing.1.trans below.1),fun key row found => below.2 (growing.2 (carrier key row found)),trace_need trace⟩

end MicroCFTA.SourceCurrentOuterInitialPrefix
