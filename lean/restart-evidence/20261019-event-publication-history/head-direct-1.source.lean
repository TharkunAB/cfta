import MicroCFTA.SourceCurrentStoredReconstructionPath
import MicroCFTA.SourceCurrentRequiredHeapEffects
import MicroCFTA.SourceEqualityProjectionCosts

/-!
# Publication histories through actual required and projection calls

Each actual stored unfolding derives its source publication history.
The ordered readers compose these histories at their exact return heaps.
Ordinary constructor effects add no Mu record. Successful graph calls
retain their literal histories without a language or future-call premise.
-/
namespace MicroCFTA.SourceCurrentRequiredPublicationHistory
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open InternedNestedConstruction (Outcome)
open InternedStoredSubstitution (leaves input encode Replacements inputs_available)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityProjectionRead SourceEqualityProjectionUnion SourceEqualityProjectionGraph
open SourceEqualityRequiredGraph
open SourceCurrentNativeMuPublication (History)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Every actual unfolding has its own publication history, including pending outcomes. -/
theorem unfold (value : Value Symbol Guard) (before : State Symbol Guard)
    (ready : Ready before) (available : Available before value) :
    Nonempty (History before (InternedFreshOrdinaryStoredSubstitution.unfold value before).state) := by
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
    exact SourceCurrentNativeMuPublication.build_history (encode (leaves body) [] body) _ before context

private theorem collect (fuel : Nat) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (seen : List Nat)
    (pending : List (Value Symbol Guard)) (available : Values before pending) :
    Nonempty (History before (MergedFreshOrdinaryExposure.collect fuel before seen pending).state) := by
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
          have actualFirst : History before after := by simpa only [done,Outcome.state] using first
          have afterCosts : CostHeap after := by
            simpa only [done,Outcome.state] using InternedFreshOrdinaryStoredSubstitution.unfold_cost_heap
              (.mu entry body depth ordinary) before semantic.ready.semantic.1 semantic.ready.semantic.2 costs own
          have next : Values after (value :: rest) := by
            intro value member
            rcases List.mem_cons.mp member with rfl | later
            · exact valueAvailable
            · exact kept.available value (tail value later)
          obtain ⟨last⟩ := ih after afterSemantic afterCosts (entry.identity :: seen) (value :: rest) next
          exact ⟨by simpa only [MergedFreshOrdinaryExposure.collect,ite_eq_right visited,done] using History.trans actualFirst last⟩

private theorem nodeEdges (fuel : Nat) (value : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value) :
    Nonempty (History before (MergedFreshOrdinaryExposure.nodeEdges fuel value before).state) := by
  have fallback (current : State Symbol Guard) (currentSemantic : SemanticReady current) (currentCosts : CostHeap current)
      (root : Value Symbol Guard) (rootAvailable : Available current root) :
      Nonempty (History current (MergedFreshOrdinaryExposure.collect fuel current [] [root]).canonical.state) := by
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
    have actualFirst : History before after := by simpa only [done,Outcome.state] using first
    have afterCosts : CostHeap after := by
      simpa only [done,Outcome.state] using InternedFreshOrdinaryStoredSubstitution.unfold_cost_heap
        (.mu entry body depth ordinary) before semantic.ready.semantic.1 semantic.ready.semantic.2 costs available
    obtain ⟨last⟩ := fallback after afterSemantic afterCosts (.mu entry body depth ordinary) (kept.available _ available)
    cases result with
    | node => exact ⟨by simpa only [MergedFreshOrdinaryExposure.nodeEdges,done,MergedSourceExposure.Result.state] using actualFirst⟩
    | empty | reference | union | mu =>
      exact ⟨by simpa only [MergedFreshOrdinaryExposure.nodeEdges,done] using History.trans actualFirst last⟩

/-- A successful actual row read extends the physical publication history. -/
theorem read {value : Value Symbol Guard} {before after : State Symbol Guard} {edges : List (EdgeValue Symbol Guard)}
    (actual : Read value before edges after) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Available before value) : Nonempty (History before after) := by
  cases actual with
  | done fuel completed =>
    simpa only [completed,MergedSourceExposure.Result.state] using nodeEdges fuel value before semantic costs available

/-- An actual Head composes row exposure with its literal no-new-Mu node constructor. -/
theorem head {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : SourceEqualityRequiredHead.Head value before result after) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Available before value) : Nonempty (History before after) := by
  cases actual with
  | read fuel edges middle exposed rebuilt =>
    obtain ⟨first⟩ := read (.done fuel exposed) semantic costs available
    have last : History middle after := by
      have old := InternedShallowHeap.makeNode_noNewMu edges middle
      rw [rebuilt] at old
      exact .retain middle after old
    exact ⟨.trans first last⟩

/-- Ordered actual reads compose histories at each exact returned heap. -/
theorem readAll {values : List (Value Symbol Guard)} {before after : State Symbol Guard} {edges : List (EdgeValue Symbol Guard)}
    (actual : ReadAll values before edges after) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Values before values) : Nonempty (History before after) := by
  induction actual with
  | nil => exact ⟨.refl _⟩
  | cons first rest ih =>
    obtain ⟨initial⟩ := read first semantic costs (available _ List.mem_cons_self)
    have effects := SourceEqualityProjectionCosts.read_effects first semantic costs (available _ List.mem_cons_self)
    obtain ⟨later⟩ := ih effects.2.1 effects.2.2.1
      (fun value member => effects.1.available value (available value (List.mem_cons_of_mem _ member)))
    exact ⟨.trans initial later⟩

/-- An actual source union retains its ordered reads and literal final node constructor. -/
theorem union {values : List (Value Symbol Guard)} {before after : State Symbol Guard} {result : Value Symbol Guard}
    (actual : Union values before result after) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Values before values) : Nonempty (History before after) := by
  cases actual with
  | node reads built =>
    obtain ⟨first⟩ := readAll reads semantic costs available
    have old := InternedShallowHeap.makeNode_noNewMu _ _
    rw [built] at old
    exact ⟨.trans first (.retain _ _ old)⟩

end MicroCFTA.SourceCurrentRequiredPublicationHistory
