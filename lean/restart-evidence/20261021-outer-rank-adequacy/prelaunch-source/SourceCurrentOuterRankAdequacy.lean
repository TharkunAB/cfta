import MicroCFTA.SourceCurrentOuterDoneOrExhausted
import MicroCFTA.SourceCurrentOuterRankEnvelopeResources
import MicroCFTA.SourceCurrentOuterRankEnvelopeStages

namespace MicroCFTA.SourceCurrentOuterRankAdequacy
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialWorker
open SourceCurrentOuterCopiedWarmHit (Phase)
open SourceCurrentOuterExecutionAncestry (Reached)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room Le)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentOuterRankEnvelope (envelope)
open SourceCurrentInitialSelectionForecast (cover cover_ge cover_member maximum)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Seed" => List Guard × Profile
local notation "Out" => Nat × Nat × Seed
local notation "caller" => SourceCurrentOuterActiveAncestry.caller
local notation "phaseNeed" => SourceCurrentOuterInitialFuel.phaseNeed
local notation "runPhase" => SourceCurrentOuterActiveAncestry.run
local notation "descend" => SourceCurrentAllocatedPartialGraph.descend
local notation "prefixState" => SourceCurrentAllocatedPartialGraph.prefixState
local notation "rankCount" => SourceCurrentPositiveQuotientCount.count
local notation "massOf" => InternedValueMass.value

private noncomputable def images (budget count mass : Nat) (seed : Seed) : List Out :=
  (((List.range (count + 1)).flatMap fun a => (List.range (seed.2.mass + 1)).map fun b => (a,b)).filter
    (fun r => decide (r.1 < count ∨ (r.1 = count ∧ r.2 < mass)))).map
      fun r => envelope budget r.1 r.2 seed
private def fold (step : Out → Out) (n : Nat) (entry : Out) : Out :=
  (List.range n).foldl (fun acc _ => step acc) entry
private def slot (all : Seed → List Out) (acc : Out) : Out :=
  let xs := all acc.2.2
  (acc.1 + 1 + maximum (xs.map fun x => x.1), max acc.2.1 (maximum (xs.map fun x => x.2.1)),
    (acc.2.2.1 ++ xs.flatMap (fun x => x.2.2.1), cover (xs.map fun x => x.2.2.2) acc.2.2.2))
private noncomputable def row (budget : Nat) (all : Seed → List Out) (acc : Out) : Out :=
  let post := SourceCurrentOuterInitialSchedule.parent budget acc.2.2
  let walked := fold (slot all) post.2.mass (0,0,post)
  (acc.1 + 1 + walked.1,
    max acc.2.1 (max (SourceCurrentParentUniformEnvelope.fuel budget acc.2.2.1 acc.2.2.2) walked.2.1),
    SourceCurrentOuterInitialSchedule.rebuild walked.2.2)

private def Kept (first last : Seed) : Prop := Le first.2 last.2 ∧ first.1 ⊆ last.1
private theorem kept_trans {first middle last : Seed} (one : Kept first middle) (two : Kept middle last) :
    Kept first last := ⟨one.1.trans two.1, fun _ h => two.2 (one.2 h)⟩
private theorem fold_kept (step : Out → Out) (one : ∀ acc, Kept acc.2.2 (step acc).2.2)
    (n : Nat) (entry : Out) : Kept entry.2.2 (fold step n entry).2.2 := by
  have general (values : List Nat) (acc : Out) : Kept acc.2.2 (values.foldl (fun x _ => step x) acc).2.2 := by
    induction values generalizing acc with
    | nil => exact ⟨Le.refl _, fun _ h => h⟩
    | cons head tail ih => exact kept_trans (one acc) (ih (step acc))
  exact general _ _
private theorem fold_succ (step : Out → Out) (n : Nat) (entry : Out) :
    fold step (n+1) entry = step (fold step n entry) := by
  simp only [fold, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
private theorem prefix_kept (step : Out → Out) (one : ∀ acc, Kept acc.2.2 (step acc).2.2)
    {n k : Nat} (bound : k ≤ n) (entry : Out) : Kept (fold step k entry).2.2 (fold step n entry).2.2 := by
  have cut : fold step n entry = fold step (n-k) (fold step k entry) := by
    unfold fold
    conv =>
      lhs
      rw [show n = k + (n-k) by omega, List.range_add, List.foldl_append, List.foldl_map]
  rw [cut]
  exact fold_kept step one _ _
private theorem slot_kept (all : Seed → List Out) (acc : Out) : Kept acc.2.2 (slot all acc).2.2 :=
  ⟨cover_ge _ _, fun _ h => List.mem_append_left _ h⟩
private theorem image_kept (all : Seed → List Out) (acc value : Out) (member : value ∈ all acc.2.2) :
    Kept value.2.2 (slot all acc).2.2 := by
  refine ⟨cover_member _ (List.mem_map.mpr ⟨value,member,rfl⟩), ?_⟩
  intro guard present
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨value,member,present⟩)
private theorem image_member (budget count mass : Nat) (seed : Seed) (a b : Nat)
    (counts : a ≤ count) (masses : b ≤ seed.2.mass) (smaller : Prod.Lex Nat.lt Nat.lt (a,b) (count,mass)) :
    envelope budget a b seed ∈ images budget count mass seed := by
  apply List.mem_map.mpr
  refine ⟨(a,b), List.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
  · exact List.mem_flatMap.mpr ⟨a,List.mem_range.mpr (by omega),
      List.mem_map.mpr ⟨b,List.mem_range.mpr (by omega),rfl⟩⟩
  · simpa only [decide_eq_true_eq, Nat.lt_eq] using Prod.lex_def.mp smaller

private theorem same_request [DecidableEq (EdgeKey Symbol Guard)]
    {bits : Nat} {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {before : Caller (bits+2)} {memos : Memos}
    (initial : Context formulas solver inventory before memos) (first second : NodeRequest)
    (left : SourceCurrentOuterPrefixInvariants.NodeReady before first)
    (right : SourceCurrentOuterPrefixInvariants.NodeReady before second) (same : first.key = second.key) : first = second := by
  have inherited := SourceEqualityConstraintMemoAllocation.ready_eq_of_identity _
    initial.ready.good.operations.constraints first.inherited second.inherited left.1 right.1 (congrArg Prod.fst same)
  have values := InternedFreshProbeKeys.resident_reference_injective _
    initial.ready.semantic.ready.semantic.1.normal.facts.coherent first.value second.value
    left.2.resident right.2.resident (congrArg Prod.snd same)
  cases first
  cases second
  cases inherited
  cases values
  rfl

private theorem fold_work (step : Out → Out)
    (growth : ∀ acc, acc.1 + 1 ≤ (step acc).1) (n : Nat) (entry : Out) :
    entry.1 + n ≤ (fold step n entry).1 := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    rw [fold_succ]
    have one := growth (fold step n entry)
    omega
private theorem slot_work (all : Seed → List Out) (acc : Out) : acc.1 + 1 ≤ (slot all acc).1 := by
  dsimp only [slot]
  omega
private theorem row_work (budget : Nat) (all : Seed → List Out) (acc : Out) :
    acc.1 + 1 ≤ (row budget all acc).1 := by
  dsimp only [row]
  omega

variable {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

private theorem edge_not_exhausted {width : Nat} (fuel g s r e p h m c n budget : Nat)
    (request : EdgeRequest) (before after : Caller width) (limit : Limit) :
    edgeCall fuel g s r e p h m c n budget request before ≠ .failed (.exhausted limit) after := by
  intro failed
  generalize started : beginEdge request before = observation
  obtain ⟨handle,action,running⟩ := observation
  cases action with
  | ready value => simp only [edgeCall,started] at failed; cases failed
  | busy => simp only [edgeCall,started] at failed; cases failed
  | absent => simp only [edgeCall,started] at failed; cases failed
  | evaluate captured =>
    simp only [edgeCall,started] at failed
    cases parent : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget
        captured.value.entry.key.symbol captured.value.entry.key.constraint captured.inherited
        captured.value.children running.checked running.fourth running.merge with
    | done value checked fourth memo =>
      simp only [edgeBody,parent,Outcome.bind] at failed
      cases failed
    | failed fault checked fourth memo =>
      simp only [edgeBody,parent,Outcome.bind] at failed
      cases failed

theorem initial_node_call
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {g s r e p h m c n budget : Nat} {inventory : Inventory} {memos : Memos}
    {request : NodeRequest} {before : Caller (bits + 2)}
    (seed : List Guard × Profile) :
    let output := envelope budget
      (SourceCurrentPositiveQuotientCount.count (request.inherited.payload.getD []) request.value)
      (InternedValueMass.value request.value) seed
    let first : Phase (bits + 2) := .node output.1 request before
    let need := phaseNeed budget first seed
    ∀ (initial : Context formulas solver inventory before memos)
      (frame : Frame formulas solver inventory before.checked)
      (fits : Fits seed.2 before.checked)
      (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ seed.1)
        before.checked.native.machine.heap)
      (inputs : SourceCurrentOuterPrefixInvariants.Inputs first)
      (room : Room bits (SourceCurrentInitialSelectionForecast.cover [output.2.2.2]
        (SourceCurrentOuterInitialPrefix.forecast budget first seed).2))
      (normal : SourceCurrentRequiredUnionNormal.UnionNormal before.checked.native.machine.heap)
      (supported : SourceCurrentNativeRequestPositivePositions.Support
        before.checked.native.machine.heap before.checked.native)
      (causal : SourceCurrentNativeMuPublication.History empty before.checked.native.machine.heap)
      (merged : SourceCurrentConstrainedCapMemoMerge.Stored
        (fun guard : Guard => SourceMemoGate.plain guard = true) before.merge)
      (positiveMemo : SourceCurrentMergePositivePosition.Support before.merge)
      (origins : SourceCurrentResourceParentWriters.Origins formulas solver before)
      (stored : SourceCurrentOuterClosedInputs.NodeStored before)
      (closed : SourceCurrentOuterClosedInputs.InputsClosed first)
      (initialNodeIdle : ∀ chosen owner, before.nodeResults.cells chosen ≠ some ⟨owner, .evaluating⟩)
      (initialEdgeIdle : SourceCurrentOuterEdgeIdle.EdgeIdle before)
      (gBound : need ≤ g) (sBound : need ≤ s) (rBound : need ≤ r)
      (eBound : need ≤ e) (pBound : need ≤ p) (hBound : need ≤ h)
      (mBound : need ≤ m) (cBound : need ≤ c) (nBound : need ≤ n),
    ∃ result after, ∀ fuel, output.1 ≤ fuel →
      nodeCall fuel g s r e p h m c n budget request before = .done result after
 := by
  dsimp only
  intro initial frame fits known inputs room normal supported causal merged positiveMemo origins stored closed
    initialNodeIdle initialEdgeIdle gBound sBound rBound eBound pBound hBound mBound cBound nBound
  let output := envelope budget (rankCount (request.inherited.payload.getD []) request.value) (massOf request.value) seed
  let first : Phase (bits+2) := .node output.1 request before
  have rootRoom : Room bits (SourceCurrentOuterInitialPrefix.forecast budget first seed).2 :=
    room.mono (cover_ge _ _)
  have outputRoom : Room bits output.2.2.2 := room.mono (cover_member _ List.mem_cons_self)
  have classified := SourceCurrentOuterDoneOrExhausted.done_or_exhausted formulas solver (first := first) seed initial frame fits known
    inputs rootRoom normal supported causal merged positiveMemo origins stored closed initialNodeIdle initialEdgeIdle
    gBound sBound rBound eBound pBound hBound mBound cBound nBound
  have resources {phase : Phase (bits+2)} (cut : Reached g s r e p h m c n budget first phase) :=
    SourceCurrentOuterInitialPrefix.reached formulas solver seed cut initial frame fits known inputs rootRoom
  have only_exhausted {phase : Phase (bits+2)} {fault : Fault (bits+2)} {after : Caller (bits+2)}
      (cut : Reached g s r e p h m c n budget first phase)
      (failed : runPhase g s r e p h m c n budget phase = .failed fault after) :
      ∃ limit, fault = .exhausted limit := by
    have lifted := cut.failed failed
    rcases classified with ⟨finished,done⟩ | ⟨limit,failedAfter,exhausted⟩
    · rw [lifted] at done
      cases done
    · rw [lifted] at exhausted
      cases exhausted
      exact ⟨limit,rfl⟩
  have widen {one two : Seed} {state : SourceEqualityNativeDemand.State (bits+2)}
      (below : Kept one two) (numeric : Fits one.2 state)
      (carrier : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ one.1) state.native.machine.heap) :
      Fits two.2 state ∧ SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ two.1) state.native.machine.heap :=
    ⟨numeric.mono below.1, fun key edge found => below.2 (carrier key edge found)⟩
  have progress : ∀ rank : Nat × Nat, ∀ (fuel : Nat) (candidate : NodeRequest)
      (start : Caller (bits+2)) (entrySeed : Seed),
      (rankCount (candidate.inherited.payload.getD []) candidate.value, massOf candidate.value) = rank →
      Reached g s r e p h m c n budget first (.node fuel candidate start) →
      Fits entrySeed.2 start.checked →
      SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ entrySeed.1) start.checked.native.machine.heap →
      Room bits (envelope budget rank.1 rank.2 entrySeed).2.2.2 →
      (envelope budget rank.1 rank.2 entrySeed).1 ≤ fuel →
      ∃ result after, nodeCall fuel g s r e p h m c n budget candidate start = .done result after := by
    intro rank
    refine (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf.induction rank ?_
    intro rank ih fuel candidate start entrySeed ranked past currentFits currentKnown currentRoom enough
    rcases rank with ⟨count,mass⟩
    obtain ⟨_iv,_ms,_old,_trace,post,_fr,_ff,_kk,ready,_below,_alphabet,_room,_rest⟩ := resources past
    dsimp only [SourceCurrentOuterPrefixInvariants.Inputs, SourceCurrentOuterPrefixInvariants.NodeReady] at ready
    generalize started : beginNode candidate start = observation
    obtain ⟨handle,action,running⟩ := observation
    cases action with
    | ready value => exact ⟨value,running,by simp only [nodeCall,started]⟩
    | busy =>
      have failed : runPhase g s r e p h m c n budget (.node fuel candidate start) =
          .failed (.nodeMemo handle .busy) running := by
        simp only [SourceCurrentOuterActiveAncestry.run,nodeCall,started,Outcome.bind]
      obtain ⟨limit,bad⟩ := only_exhausted past failed
      cases bad
    | absent =>
      have failed : runPhase g s r e p h m c n budget (.node fuel candidate start) =
          .failed (.nodeMemo handle .absent) running := by
        simp only [SourceCurrentOuterActiveAncestry.run,nodeCall,started,Outcome.bind]
      obtain ⟨limit,bad⟩ := only_exhausted past failed
      cases bad
    | evaluate captured =>
      obtain ⟨bodyContext,owner,key,_cell⟩ :=
        SourceCurrentAllocatedPartialCallSteps.node_start formulas solver post.context ready.1 ready.2 started
      have checked := (beginNode_components candidate start).1
      rw [started] at checked
      dsimp only at checked
      have requested : SourceCurrentOuterPrefixInvariants.NodeReady running candidate := by
        simpa only [SourceCurrentOuterPrefixInvariants.NodeReady,checked] using ready
      have same := same_request bodyContext captured candidate ⟨owner.inherited,owner.input⟩ requested key
      subst captured
      have bodyPast := past.snoc (.node_evaluate started)
      have runningFits : Fits entrySeed.2 running.checked := by simpa only [checked] using currentFits
      have runningKnown : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ entrySeed.1)
          running.checked.native.machine.heap := by simpa only [checked] using currentKnown
      have bodyProgress : ∃ result after, nodeBody fuel g s r e p h m c n budget candidate running = .done result after := by
        rcases candidate with ⟨inherited,value⟩
        cases value with
        | empty => exact ⟨.empty,running,rfl⟩
        | union entry members depth free => exact ⟨.union entry members depth free,running,rfl⟩
        | reference name =>
          have failed : runPhase g s r e p h m c n budget
              (.body fuel ⟨inherited,.reference name⟩ running) = .failed (.unexpectedReference name) running := rfl
          obtain ⟨limit,bad⟩ := only_exhausted bodyPast failed
          cases bad
        | mu entry body depth ordinary =>
          exact ⟨cleanup (.mu entry body depth ordinary),running,
            SourceCurrentMuReconstructionEffects.node_body fuel g s r e p h m c n budget entry body depth ordinary
              inherited running bodyContext.ready.good bodyContext.probes owner.input⟩
        | node entry originals depth free =>
          have massSame := congrArg Prod.snd ranked
          have rowLength : originals.length ≤ mass := by
            simp only [InternedValueMass.value] at massSame
            rw [InternedValueMass.edges_eq_length_sum] at massSame
            omega
          have positive := (SourceCurrentOuterRankEnvelope.retains budget count mass entrySeed).1
          cases fuel with
          | zero => omega
          | succ bodyFuel =>
            let all := images budget count mass
            let rowStep := row budget all
            let rowSeed := fun j => (fold rowStep j (0,0,entrySeed)).2.2
            have rowsProgress : ∀ rowFuel j values start,
                rowFuel + j + 1 = bodyFuel + 1 → j + values.length ≤ mass →
                Reached g s r e p h m c n budget
                  (.body (bodyFuel+1) ⟨inherited,.node entry originals depth free⟩ running)
                  (.rows rowFuel inherited values start) →
                Fits (rowSeed j).2 start.checked →
                SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ (rowSeed j).1) start.checked.native.machine.heap →
                ∃ output finish, rows rowFuel g s r e p h m c n budget inherited values start = .done output finish := by
              intro rowFuel j values
              induction values generalizing rowFuel j with
              | nil => intro start _ _ _ _ _; exact ⟨[],start,rfl⟩
              | cons original rest tailRows =>
                intro start position bound inside numeric carrier
                have rowBound : j < mass := by simp only [List.length_cons] at bound; omega
                cases rowFuel with
                | zero => omega
                | succ rowFuel =>
                  let prior := fold rowStep j (0,0,entrySeed)
                  let parentSeed := SourceCurrentOuterInitialSchedule.parent budget prior.2.2
                  let slots := slot all
                  let slotSeed := fun k => (fold slots k (0,0,parentSeed)).2.2
                  let fullSlots := slotSeed parentSeed.2.mass
                  have stage := SourceCurrentOuterRankEnvelopeStages.stage_bounds budget count mass entrySeed j rowBound
                  have parentProgress : ∃ parented afterParent,
                      edgeCall rowFuel g s r e p h m c n budget ⟨inherited,original⟩ start = .done parented afterParent := by
                    cases observed : edgeCall rowFuel g s r e p h m c n budget ⟨inherited,original⟩ start with
                    | done parented afterParent => exact ⟨parented,afterParent,observed⟩
                    | failed fault after =>
                      have failed : runPhase g s r e p h m c n budget
                          (.rows (rowFuel+1) inherited (original::rest) start) = .failed fault after := by
                        simp only [SourceCurrentOuterActiveAncestry.run,rows,observed,Outcome.bind]
                      obtain ⟨limit,same⟩ := only_exhausted (bodyPast.trans inside) failed
                      subst fault
                      exact False.elim (edge_not_exhausted rowFuel g s r e p h m c n budget
                        ⟨inherited,original⟩ start after limit observed)
                  obtain ⟨parented,afterParent,parentDone⟩ := parentProgress
                  obtain ⟨rowIv,rowMs,_rowOld,_t,rowPost,rowFrame,_nf,_nk,rowInputs,_b,_a,_r,_⟩ :=
                    resources (bodyPast.trans inside)
                  obtain ⟨parentIv,parentMs,parentReceipt,parentFits,parentKnown⟩ :=
                    SourceCurrentOuterEdgeGuardAlphabet.edge_call formulas solver rowIv budget prior.2.2.1
                      ⟨inherited,original⟩ start rowMs rowPost.context rowFrame prior.2.2.2 numeric carrier
                      rowInputs.1 (rowInputs.2 original List.mem_cons_self)
                      (SourceCurrentOuterInitialSchedule.parent_reserved bits budget prior.2.2 (currentRoom.mono stage.2.1)) parentDone
                  have inheritedAfter := rowInputs.1.grows parentReceipt.post.effects.grows.constraint_growth
                  obtain ⟨combined,prefixReceipt,_prefixFrame,prefixFits,prefixPost⟩ :=
                    SourceCurrentInheritedNumeric.resident_complete formulas solver parentIv parented inherited afterParent parentMs
                      parentReceipt.post.context parentReceipt.frame parentSeed.2 parentFits
                      (fun _ => parentReceipt.semantic.resident) (fun _ => inheritedAfter)
                  have combinedAt := prefixReceipt.actual
                  have childInside := (inside.snoc (.rows_edge parentDone)).snoc (.descendants_children combinedAt)
                  have prefixKnown := (SourceCurrentOuterConstructorBounds.prefix_state parentSeed.1 parentSeed.2
                    afterParent parented inherited parentFits parentKnown).2.1
                  have childMass := SourceCurrentAllocatedNativePhysicalMass.resident_children
                    afterParent.checked.native.machine.heap parentFits.stored parented parentReceipt.semantic.resident
                  have widthBound : parented.children.length < parentSeed.2.mass := childMass.2.1
                  have childrenProgress : ∃ results finish,
                      SourceCurrentAllocatedPartialWorker.children rowFuel g s r e p h m c n budget combined parented.children
                        (prefixState afterParent parented inherited) = .done results finish ∧
                      Fits fullSlots.2 finish.checked ∧ SourceEqualityAnnotationHeap.Heap
                        (fun guard => guard ∈ fullSlots.1) finish.checked.native.machine.heap := by
                    cases combined with
                    | contradiction =>
                      have padded := widen (fold_kept slots (slot_kept all) _ _) prefixFits prefixKnown
                      exact ⟨EqualityLeafProjectionRuntimeEmpty.erase parented.children,_,rfl,padded.1,padded.2⟩
                    | live identity records =>
                      have walks : ∀ walkFuel index values start,
                          walkFuel + index = rowFuel → index + values.length ≤ parentSeed.2.mass →
                          (∀ value ∈ values, massOf value < parentSeed.2.mass) →
                          Reached g s r e p h m c n budget
                            (.body (bodyFuel+1) ⟨inherited,.node entry originals depth free⟩ running)
                            (.walk walkFuel (.live identity records) index values start) →
                          Fits (slotSeed index).2 start.checked →
                          SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ (slotSeed index).1)
                            start.checked.native.machine.heap →
                          ∃ results finish, walk walkFuel g s r e p h m c n budget (.live identity records) index values start =
                            .done results finish ∧ Fits fullSlots.2 finish.checked ∧ SourceEqualityAnnotationHeap.Heap
                              (fun guard => guard ∈ fullSlots.1) finish.checked.native.machine.heap := by
                        intro walkFuel index values
                        induction values generalizing walkFuel index with
                        | nil =>
                          intro start _ bound _ _ numeric carrier
                          have padded := widen (prefix_kept slots (slot_kept all) (by simpa using bound) _) numeric carrier
                          exact ⟨[],start,rfl,padded.1,padded.2⟩
                        | cons value rest tailWalk =>
                          intro start walkPosition bound masses inside numeric carrier
                          have slotBound : index < parentSeed.2.mass := by simp only [List.length_cons] at bound; omega
                          have nextStage := stage.2.2.2 (index+1) (by omega)
                          have priorWork := fold_work rowStep (row_work budget all) j (0,0,entrySeed)
                          have nextWork := fold_work slots (slot_work all) (index+1) (0,0,parentSeed)
                          have prefixWork := nextStage.1
                          change prior.1 + (fold slots (index+1) (0,0,parentSeed)).1 + 2 ≤
                            (envelope budget count mass entrySeed).1 at prefixWork
                          cases walkFuel with
                          | zero => omega
                          | succ walkFuel =>
                            let current := slotSeed index
                            let childRequest : NodeRequest := ⟨(descend start (.live identity records) index).1,value⟩
                            let childBefore := (descend start (.live identity records) index).2
                            let a := rankCount (childRequest.inherited.payload.getD []) value
                            let b := massOf value
                            have childPath := inside.snoc .walk_head
                            have smaller := SourceCurrentOlderOwnerLineage.body_rank_lt formulas solver seed
                              initial frame fits known inputs rootRoom normal supported causal merged positiveMemo origins bodyPast childPath
                            change Prod.Lex Nat.lt Nat.lt (a,b) _ at smaller
                            rw [ranked] at smaller
                            have counts : a ≤ count := by
                              rcases Prod.lex_def.mp smaller with less | ⟨equal,_⟩
                              · exact Nat.le_of_lt less
                              · exact Nat.le_of_eq equal
                            have massBound : b ≤ current.2.mass := by
                              have valueBound := masses value List.mem_cons_self
                              have base := (fold_kept slots (slot_kept all) index (0,0,parentSeed)).1.2.2.2
                              change parentSeed.2.mass ≤ current.2.mass at base
                              omega
                            obtain ⟨_work,_lower,_profile,_alphabet,candidates⟩ := stage.2.2.2 index (by omega)
                            have selected := candidates a b slotBound counts massBound smaller
                            have childRoom : Room bits (envelope budget a b current).2.2.2 := currentRoom.mono selected.2.2.1
                            have childEnough : (envelope budget a b current).1 ≤ walkFuel := by
                              have work := selected.1
                              change (envelope budget a b current).1 + 3 + j + index ≤
                                (envelope budget count mass entrySeed).1 at work
                              omega
                            have descent := SourceCurrentOuterConstructorBounds.descend current.1 current.2 start
                              (.live identity records) index numeric carrier
                            obtain ⟨headValue,middle,headDone⟩ := ih (a,b) smaller walkFuel childRequest childBefore current rfl
                              (bodyPast.trans childPath) descent.1 descent.2.1 childRoom childEnough
                            have childReturned := SourceCurrentOuterRankEnvelopeResources.node_call formulas solver seed
                              initial frame fits known inputs rootRoom normal supported causal merged positiveMemo origins current
                              (bodyPast.trans childPath) descent.1 descent.2.1 childRoom headDone
                            have member := image_member budget count mass current a b counts massBound smaller
                            have next := widen (image_kept all (fold slots index (0,0,parentSeed))
                              (envelope budget a b current) member) childReturned.1 childReturned.2
                            have nextSlot : Fits (slotSeed (index+1)).2 middle.checked ∧ SourceEqualityAnnotationHeap.Heap
                                (fun guard => guard ∈ (slotSeed (index+1)).1) middle.checked.native.machine.heap := by
                              simpa only [slotSeed,fold_succ,slots] using next
                            obtain ⟨tailValues,finish,tailDone,finalFits,finalKnown⟩ :=
                              tailWalk walkFuel (index+1) middle (by omega)
                                (by simp only [List.length_cons] at bound; omega)
                                (fun value member => masses value (List.mem_cons_of_mem _ member))
                                (inside.snoc (.walk_tail headDone)) nextSlot.1 nextSlot.2
                            exact ⟨headValue::tailValues,finish,by simp only [walk,headDone,tailDone,Outcome.bind],finalFits,finalKnown⟩
                      obtain ⟨results,finish,done,numeric,carrier⟩ := walks rowFuel 0 parented.children _ (by omega)
                        (by simpa only [Nat.zero_add] using Nat.le_of_lt widthBound) childMass.2.2
                        (childInside.snoc (.children_walk (by intro impossible; cases impossible))) prefixFits prefixKnown
                      exact ⟨results,finish,by simpa only [SourceCurrentAllocatedPartialWorker.children] using done,numeric,carrier⟩
                  obtain ⟨childrenResult,childEnd,childDone,childrenFit,childrenKnown⟩ := childrenProgress
                  obtain ⟨childIv,childMs,childOld,_t,childPost,childFrame,oldFits,oldKnown,childInputs,_b,_a,childRoom,_⟩ :=
                    resources (bodyPast.trans childInside)
                  obtain ⟨next,_final,childGraph,_reads,childPost,childFrame,_nf,_nk,childAvailable,_law⟩ :=
                    SourceCurrentOuterInitialActual.children formulas solver rowFuel childOld childPost.context childFrame
                      oldFits oldKnown childInputs.1 childInputs.2 childRoom childDone
                  have prefixResident := InternedEdgeResidency.edge_grows _ _
                    prefixPost.effects.keeps.growth parented parentReceipt.semantic.resident
                  have sourceResident := InternedEdgeResidency.edge_grows _ _ childPost.effects.keeps.growth parented prefixResident
                  obtain ⟨_built,_frame,builtFits,builtKnown⟩ := SourceCurrentOuterRebuildGuardAlphabet.edge fullSlots.1
                    formulas solver next fullSlots.2 parented childrenResult childEnd.checked childFrame
                    childrenFit childrenKnown sourceResident childAvailable childGraph.length
                  let rebuilt := SourceCurrentAllocatedRawRebuild.edge parented childrenResult childEnd.checked
                  let afterEdge := advance childEnd rebuilt.2 childEnd.fourth childEnd.merge
                  have descDone : descendants rowFuel g s r e p h m c n budget inherited parented afterParent =
                      .done rebuilt.1 afterEdge := by
                    simp only [descendants,combinedAt,childDone,Outcome.bind]
                  have nextFits : Fits (rowSeed (j+1)).2 afterEdge.checked := by
                    simpa only [afterEdge,rebuilt,rowSeed,fold_succ,rowStep,row,prior,fullSlots,slotSeed,slots,parentSeed,
                      SourceCurrentAllocatedPartialState.advance,SourceCurrentOuterInitialSchedule.rebuild] using builtFits
                  have nextKnown : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ (rowSeed (j+1)).1)
                      afterEdge.checked.native.machine.heap := by
                    simpa only [afterEdge,rebuilt,rowSeed,fold_succ,rowStep,row,prior,fullSlots,slotSeed,slots,parentSeed,
                      SourceCurrentAllocatedPartialState.advance,SourceCurrentOuterInitialSchedule.rebuild] using builtKnown
                  obtain ⟨restResults,finish,tailDone⟩ := tailRows rowFuel (j+1) afterEdge (by omega)
                    (by simp only [List.length_cons] at bound; omega)
                    (inside.snoc (.rows_tail parentDone descDone)) nextFits nextKnown
                  exact ⟨rebuilt.1::restResults,finish,by simp only [rows,parentDone,descDone,tailDone,Outcome.bind]⟩
            have rowInside : Reached g s r e p h m c n budget
                (.body (bodyFuel+1) ⟨inherited,.node entry originals depth free⟩ running)
                (.rows bodyFuel inherited originals running) := (Reached.refl _).snoc (.body_rows rfl)
            obtain ⟨results,rowEnd,rowsDone⟩ := rowsProgress bodyFuel 0 originals running (by omega)
              (by simpa only [Nat.zero_add] using rowLength) rowInside runningFits runningKnown
            let rebuilt := SourceCurrentAllocatedRawRebuild.modify (.node entry originals depth free) originals results rowEnd.checked
            exact ⟨rebuilt.1,advance rowEnd rebuilt.2 rowEnd.fourth rowEnd.merge,by simp only [nodeBody,rowsDone,Outcome.bind]⟩
      obtain ⟨result,after,bodyDone⟩ := bodyProgress
      exact ⟨result,finishNode handle result after,by simp only [nodeCall,started,bodyDone,Outcome.bind]⟩
  obtain ⟨result,after,done⟩ := progress
    (rankCount (request.inherited.payload.getD []) request.value,massOf request.value)
    output.1 request before seed rfl (Reached.refl first) fits known outputRoom (Nat.le_refl _)
  refine ⟨result,after,?_⟩
  intro fuel enough
  exact SourceCurrentAllocatedPartialWorkerStability.nodeCall_done_stable done enough
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)

end MicroCFTA.SourceCurrentOuterRankAdequacy
