import MicroCFTA.SourceCurrentStoredReconstructionPath
import MicroCFTA.SourceCurrentNativeMuIssuedHistory
import MicroCFTA.SourceCurrentNativeMuIssuedWriters
import MicroCFTA.SourceCurrentRecursiveHeadMuChildContexts
import MicroCFTA.SourceCurrentRequiredHeapEffects
import MicroCFTA.SourceEqualityProjectionCosts

/-!
# Issued-name paths through actual Head execution

Actual stored builds and ordinary effects retain all issued node names.
The complete Head path supplies stronger writers for its selected Mu call.
Initial empty-to-entry paths remain explicit. Arbitrary cache growth or
physical publication History does not imply an issued-name Path.
-/
namespace MicroCFTA.SourceCurrentHeadIssuedHistory
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open InternedNestedConstruction (Outcome)
open InternedStoredSubstitution (leaves input encode Replacements inputs_available)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityProjectionRead SourceEqualityProjectionUnion SourceEqualityProjectionGraph
open SourceEqualityRequiredGraph
open SourceCurrentNativeMuIssuedHistory (Path)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Every actual unfolding derives an issued-name path at its stopping state. -/
theorem unfold (value : Value Symbol Guard) (before : State Symbol Guard)
    (ready : Ready before) (available : Available before value) :
    Nonempty (Path before (InternedFreshOrdinaryStoredSubstitution.unfold value before).state) := by
  cases value with
  | empty | reference | node | union => exact ⟨.refl before⟩
  | mu entry body depth ordinary =>
    let environment := fun name => if name = InternedBinderProtocol.Reference.interned entry.identity
      then some (Value.mu entry body depth ordinary) else none
    have bodyAvailable : Available before body := available.children body (by simp [children])
    have replacements : Replacements before environment := by
      intro name value found
      dsimp only [environment] at found
      split at found
      · cases found; exact available
      · cases found
    have context : SourceCurrentConstrainedCapSourceHistory.Context before ((leaves body).map (input environment)) :=
      ⟨⟨ready.semantic.1.normal,inputs_available body environment before bodyAvailable replacements,
        ready.semantic.1.profiles,ready.semantic.1.freeNames⟩,ready.semantic.2⟩
    exact SourceCurrentNativeMuIssuedHistory.build_path (encode (leaves body) [] body) _ before context

private theorem collect (fuel : Nat) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (seen : List Nat)
    (pending : List (Value Symbol Guard)) (available : Values before pending) :
    Nonempty (Path before (MergedFreshOrdinaryExposure.collect fuel before seen pending).state) := by
  induction fuel generalizing before seen pending with
  | zero => cases pending <;> exact ⟨.refl before⟩
  | succ fuel ih =>
    cases pending with
    | nil => exact ⟨.refl before⟩
    | cons value rest =>
      have own := available value List.mem_cons_self
      have tail : Values before rest := fun value member => available value (List.mem_cons_of_mem _ member)
      cases value with
      | empty => exact ih before semantic costs seen rest tail
      | reference => exact ⟨.refl before⟩
      | node entry edges depth free =>
        simpa only [MergedFreshOrdinaryExposure.collect,SourceEqualityAnnotationExposure.prepend_state] using
          ih before semantic costs seen rest tail
      | union entry members depth free =>
        by_cases visited : entry.identity ∈ seen
        · simpa only [MergedFreshOrdinaryExposure.collect,ite_eq_left visited] using ih before semantic costs seen rest tail
        · have next : Values before (members ++ rest) := by
            intro value member
            rcases List.mem_append.mp member with first | later
            · exact own.children value first
            · exact tail value later
          simpa only [MergedFreshOrdinaryExposure.collect,ite_eq_right visited] using
            ih before semantic costs (entry.identity :: seen) (members ++ rest) next
      | mu entry body depth ordinary =>
        by_cases visited : entry.identity ∈ seen
        · simpa only [MergedFreshOrdinaryExposure.collect,ite_eq_left visited] using ih before semantic costs seen rest tail
        · obtain ⟨value,after,done,kept,afterSemantic,valueAvailable,_⟩ :=
            SourceEqualityOpenOrdinaryHead.unfold_complete (.mu entry body depth ordinary) before semantic own
          obtain ⟨first⟩ := unfold (.mu entry body depth ordinary) before semantic.ready own
          have actualFirst : Path before after := by simpa only [done,Outcome.state] using first
          have afterCosts : CostHeap after := by
            simpa only [done,Outcome.state] using InternedFreshOrdinaryStoredSubstitution.unfold_cost_heap
              (.mu entry body depth ordinary) before semantic.ready.semantic.1 semantic.ready.semantic.2 costs own
          have next : Values after (value :: rest) := by
            intro value member
            rcases List.mem_cons.mp member with rfl | later
            · exact valueAvailable
            · exact kept.available value (tail value later)
          obtain ⟨last⟩ := ih after afterSemantic afterCosts (entry.identity :: seen) (value :: rest) next
          exact ⟨by simpa only [MergedFreshOrdinaryExposure.collect,ite_eq_right visited,done] using Path.trans actualFirst last⟩

private theorem nodeEdges (fuel : Nat) (value : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value) :
    Nonempty (Path before (MergedFreshOrdinaryExposure.nodeEdges fuel value before).state) := by
  have fallback (current : State Symbol Guard) (currentSemantic : SemanticReady current) (currentCosts : CostHeap current)
      (root : Value Symbol Guard) (rootAvailable : Available current root) :
      Nonempty (Path current (MergedFreshOrdinaryExposure.collect fuel current [] [root]).canonical.state) := by
    rw [SourceEqualityAnnotationExposure.canonical_state]
    exact collect fuel current currentSemantic currentCosts [] [root]
      (by intro child member; simpa only [List.mem_singleton.mp member] using rootAvailable)
  cases value with
  | empty | reference | node => exact ⟨.refl before⟩
  | union => exact fallback before semantic costs _ available
  | mu entry body depth ordinary =>
    obtain ⟨result,after,done,kept,afterSemantic,_resultAvailable,_⟩ :=
      SourceEqualityOpenOrdinaryHead.unfold_complete (.mu entry body depth ordinary) before semantic available
    obtain ⟨first⟩ := unfold (.mu entry body depth ordinary) before semantic.ready available
    have actualFirst : Path before after := by simpa only [done,Outcome.state] using first
    have afterCosts : CostHeap after := by
      simpa only [done,Outcome.state] using InternedFreshOrdinaryStoredSubstitution.unfold_cost_heap
        (.mu entry body depth ordinary) before semantic.ready.semantic.1 semantic.ready.semantic.2 costs available
    obtain ⟨last⟩ := fallback after afterSemantic afterCosts (.mu entry body depth ordinary) (kept.available _ available)
    cases result with
    | node => exact ⟨by simpa only [MergedFreshOrdinaryExposure.nodeEdges,done,MergedSourceExposure.Result.state] using actualFirst⟩
    | empty | reference | union | mu =>
      exact ⟨by simpa only [MergedFreshOrdinaryExposure.nodeEdges,done] using Path.trans actualFirst last⟩

/-- A successful actual row read retains its actual issued-name path. -/
theorem read {value : Value Symbol Guard} {before after : State Symbol Guard} {edges : List (EdgeValue Symbol Guard)}
    (actual : Read value before edges after) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Available before value) : Nonempty (Path before after) := by
  cases actual with
  | done fuel completed =>
    simpa only [completed,MergedSourceExposure.Result.state] using nodeEdges fuel value before semantic costs available

/-- An actual Head composes row exposure and its issued-name node effect. -/
theorem head {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : SourceEqualityRequiredHead.Head value before result after) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Available before value) : Nonempty (Path before after) := by
  cases actual with
  | read fuel edges middle exposed rebuilt =>
    obtain ⟨first⟩ := read (.done fuel exposed) semantic costs available
    have last : Path middle after := by
      have old := InternedShallowHeap.makeNode_noNewMu edges middle
      rw [rebuilt] at old
      have effects := SourceEqualityProjectionCosts.read_effects (.done fuel exposed) semantic costs available
      have valid := effects.2.1.ready.semantic.1.normal.facts.coherent.valid
      have growth := (InternedConstructorTemplates.run_correct (makeNode edges) middle valid).2
      have issued := run_issued_extends (makeNode edges) middle valid
      rw [rebuilt] at growth issued
      exact .retain middle after old growth issued
    exact ⟨.trans first last⟩

/-- The same selected Head child retains an issued-name writer for its actual stored Mu. -/
theorem head_child (value : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value)
    (closed : value.free = []) (result : Value Symbol Guard) (after : State Symbol Guard)
    (actual : SourceEqualityRequiredHead.Head value before result after) (initial : Path empty before)
    (position : Nat) (row : EdgeValue Symbol Guard)
    (selected : (InternedEdgeResidency.nodeEdges result)[position]? = some row)
    (index : Nat) (child : Value Symbol Guard) (childSelected : row.children[index]? = some child) :
    SourceCurrentLiteralRootParts.Row value row ∨
      ∃ (entry : Interned InternedBinderProtocol.NodeKey) (body depth ordinary : Value Symbol Guard)
          (first second : State Symbol Guard) (returned : Value Symbol Guard)
          (terminal : State Symbol Guard) (terminalValue : Value Symbol Guard),
        SourceCurrentRecursiveHeadChainRows.Chain before value first (.mu entry body depth ordinary) ∧
        InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) first = .done returned second ∧
        SourceCurrentRecursiveHeadMuChildContexts.Suffix second returned terminal terminalValue ∧ Keeps terminal after ∧
        SourceCurrentLiteralRootParts.Row returned row ∧
        SourceCurrentNativeMuIssuedWriters.Written empty after entry.key (.mu entry body depth ordinary) ∧
        SourceCurrentStoredMuUnfoldChildContexts.Child body first second row index child := by
  obtain ⟨later⟩ := head actual semantic costs available
  let whole : Path empty after := .trans initial later
  have lineage := SourceCurrentRecursiveHeadMuChildContexts.head_child value before semantic.ready available
    closed result after actual whole.forget.history position row selected index child childSelected
  rcases lineage with literal | ⟨entry,body,depth,ordinary,first,second,returned,terminal,terminalValue,
    earlierBranch,called,suffix,last,literal,_physical,context⟩
  · exact .inl literal
  · have known := earlierBranch.verified
    obtain ⟨callPath⟩ := unfold (.mu entry body depth ordinary) first known.1.ready known.2.1
    have callGrowth : Grows first second := by simpa only [called,Outcome.state] using callPath.growth
    have present := known.2.1.resident entry rfl
    have finalGrowth := grows_trans callGrowth (grows_trans suffix.keeps.growth last.growth)
    have resident := finalGrowth.nodeRecords entry.key _ present
    have writer := SourceCurrentNativeMuIssuedWriters.from_empty whole entry.key entry body depth ordinary resident
    exact .inr ⟨entry,body,depth,ordinary,first,second,returned,terminal,terminalValue,
      earlierBranch,called,suffix,last,literal,writer,context⟩

end MicroCFTA.SourceCurrentHeadIssuedHistory
