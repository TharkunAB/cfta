import MicroCFTA.SourceSecondaryGateReplay
import MicroCFTA.SourceEqualityProjectionRead

/-!
# Actual head completion after a false secondary gate

A completed false gate supplies a finite chain of actual warm Mu unfolds.
The source worklist still starts at the original value. It retains its
identity tests and canonical row order. Closed leaves use the existing cold
worklist theorem. These results establish completion and cache effects.
They do not establish a language law or closed head children.
-/
namespace MicroCFTA.SourceSecondaryGateHead
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues)
open MergedFreshOrdinaryExposure
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityRequiredHead
open InternedFreshOrdinaryStatefulGateTrace EqualityNormalize

/-- A finite warm head chain records actual unfolds and ordinary or closed stopping points. -/
inductive WarmHead [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard) :
    Value Symbol Guard → Prop where
  | empty : WarmHead state .empty
  | ordinary : WarmHead state (.node entry edges depth free)
  | closed (closed : value.free = []) : WarmHead state value
  | unfold (actual : InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) state =
      .done next state) (rest : WarmHead state next) : WarmHead state (.mu entry body depth ordinary)

private theorem warm_of_trace [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {path : Path} {value : Value Symbol Guard}
    {before final : State Symbol Guard} {answer : Bool}
    (trace : NodeTrace unconstrained path value before answer final) :
    answer = false → SemanticReady before → Available before value →
      ∀ target, Grows final target → WarmHead target value := by
  induction trace using NodeTrace.rec
      (motive_2 := fun _ _ _ _ _ _ _ => True)
      (motive_3 := fun _ _ _ _ _ _ _ => True) with
  | empty => intro _ _ _ _ _; exact .empty
  | reference => intro impossible; cases impossible
  | union members => intro impossible; cases impossible
  | finite fast => intro _ _ _ _ _; exact .ordinary
  | endpoint slow => intro _ _ _ _ _; exact .ordinary
  | branches slow trace ih => intro _ _ _ _ _; exact .ordinary
  | constrained blocked => intro impossible; cases impossible
  | closed plain closed => intro _ _ _ _ _; exact .closed (List.isEmpty_iff.mp closed)
  | unfold plain opened actual trace ih =>
      intro answer semantic available target growth
      obtain ⟨result, middle, done, _, middleSemantic, resultAvailable, _⟩ :=
        SourceEqualityOpenOrdinaryHead.unfold_complete _ _ semantic available
      obtain ⟨sameValue, sameState⟩ := Outcome.done.inj (done.symm.trans actual)
      cases sameValue
      cases sameState
      have tail := SourceSecondaryGateReplay.node_replay _ _ _ _ _ _ trace middleSemantic resultAvailable
      exact .unfold
        (InternedFreshOrdinaryStoredSubstitution.unfold_replay _ _ target _ _
          semantic.ready.semantic.1.normal.facts.coherent.valid actual (grows_trans tail.2.1.growth growth))
        (ih answer middleSemantic resultAvailable target growth)
  | missing absent => trivial
  | present found trace ih => trivial
  | nil => trivial
  | stop head ih => trivial
  | next head tail headIH tailIH => trivial

/-- A false actual gate supplies its finite warm head chain above its completed final cache. -/
theorem warm_head [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {path : Path} {value : Value Symbol Guard}
    {before final : State Symbol Guard}
    (trace : NodeTrace unconstrained path value before false final)
    (semantic : SemanticReady before) (available : Available before value)
    (target : State Symbol Guard) (growth : Grows final target) : WarmHead target value :=
  warm_of_trace trace rfl semantic available target growth

private theorem closed_collect_complete [DecidableEq (EdgeKey Symbol Guard)]
    (value : Value Symbol Guard) (state : State Symbol Guard) (semantic : SemanticReady state)
    (available : Available state value) (closed : value.free = []) (seen : List Nat) :
    ∃ fuel edges after, collect fuel state seen [value] = .done edges after ∧ Keeps state after ∧
      SemanticReady after ∧ Edges after edges := by
  have inputs : Values state [value] := by intro other member; simpa only [List.mem_singleton.mp member] using available
  have closedInputs : ClosedValues [value] := by intro other member; simpa only [List.mem_singleton.mp member] using closed
  obtain ⟨fuel, edges, after, done, depth, _⟩ := MergedFreshOrdinaryColdTermination.collect_complete
    (maximumDepth (nodeInventory state) + 1) state semantic.ready.semantic semantic.ready.covered
    semantic.ready.depth (InternedMuDepthInventory.initial_bounded state semantic.ready.semantic.1.normal.facts)
    seen [value] inputs closedInputs
  have checked := MergedFreshOrdinaryColdEffects.collect_verified fuel state semantic.ready.semantic
    semantic.ready.covered seen [value] inputs closedInputs
  have ready : Ready after := ⟨by simpa only [done, MergedSourceExposure.Result.state] using checked.semantic,
    by simpa only [done, MergedSourceExposure.Result.state] using checked.covered, depth⟩
  refine ⟨fuel, edges, after, done, ⟨ready, ?_, ?_⟩, ⟨ready, ?_, ?_⟩, checked.edges edges after done⟩
  · simpa only [done, MergedSourceExposure.Result.state] using checked.growth
  · simpa only [done, MergedSourceExposure.Result.state] using checked.history
  · simpa only [done, MergedSourceExposure.Result.state] using
      MergedFreshOrdinaryGuardedEffects.collect_heap fuel state semantic.ready.semantic semantic.ready.covered
        semantic.guarded seen [value] inputs closedInputs
  · simpa only [done, MergedSourceExposure.Result.state] using
      MergedFreshOrdinaryBudgetEffects.collect_heap fuel state semantic.ready.semantic semantic.ready.covered
        semantic.budget seen [value] inputs closedInputs

private theorem unfolded_available [DecidableEq (EdgeKey Symbol Guard)]
    {value next : Value Symbol Guard} {state : State Symbol Guard} (semantic : SemanticReady state)
    (available : Available state value)
    (actual : InternedFreshOrdinaryStoredSubstitution.unfold value state = .done next state) : Available state next := by
  obtain ⟨result, after, done, _, _, resultAvailable, _⟩ :=
    SourceEqualityOpenOrdinaryHead.unfold_complete value state semantic available
  obtain ⟨sameValue, sameState⟩ := Outcome.done.inj (done.symm.trans actual)
  cases sameValue
  cases sameState
  exact resultAvailable

/-- The actual worklist completes for a warm head chain with any original visited identities. -/
theorem collect_complete [DecidableEq (EdgeKey Symbol Guard)]
    {state : State Symbol Guard} {value : Value Symbol Guard} (support : WarmHead state value)
    (semantic : SemanticReady state) (available : Available state value) (seen : List Nat) :
    ∃ fuel edges after, collect fuel state seen [value] = .done edges after ∧ Keeps state after ∧
      SemanticReady after ∧ Edges after edges := by
  revert seen available semantic
  induction support with
  | empty =>
      intro semantic _ seen
      exact ⟨1, [], _, rfl, pure_keeps _ semantic.ready, semantic, by simp [Edges]⟩
  | ordinary =>
      intro semantic available seen
      exact ⟨1, _, _, by simp only [collect, MergedSourceExposure.Result.prepend, List.append_nil,
          InternedEdgeResidency.nodeEdges],
        pure_keeps _ semantic.ready, semantic,
        InternedEdgeResidency.resident_edges _ semantic.ready.semantic.1.normal.facts.linked _ available.resident⟩
  | closed closed =>
      intro semantic available seen
      exact closed_collect_complete _ _ semantic available closed seen
  | @unfold entry body depth ordinary next actual rest ih =>
      intro semantic available seen
      by_cases visited : entry.identity ∈ seen
      · exact ⟨1, [], _, by simp only [collect, ite_eq_left visited],
          pure_keeps _ semantic.ready, semantic, by simp [Edges]⟩
      · obtain ⟨fuel, edges, after, done, kept, ready, resident⟩ :=
          ih semantic (unfolded_available semantic available actual) (entry.identity :: seen)
        exact ⟨fuel + 1, edges, after, by simpa only [collect, ite_eq_right visited, actual] using done,
          kept, ready, resident⟩

/-- Both actual nodeEdges branches complete for a finite warm head chain. -/
theorem warm_nodeEdges_complete [DecidableEq (EdgeKey Symbol Guard)]
    {state : State Symbol Guard} {value : Value Symbol Guard} (support : WarmHead state value)
    (semantic : SemanticReady state) (available : Available state value) :
    ∃ fuel edges after, nodeEdges fuel value state = .done edges after ∧ Keeps state after ∧
      SemanticReady after ∧ Edges after edges := by
  cases support with
  | empty => exact ⟨0, [], _, rfl, pure_keeps _ semantic.ready, semantic, by simp [Edges]⟩
  | ordinary =>
      exact ⟨0, _, _, rfl, pure_keeps _ semantic.ready, semantic,
        InternedEdgeResidency.resident_edges _ semantic.ready.semantic.1.normal.facts.linked _ available.resident⟩
  | closed closed =>
      obtain ⟨edges, after, read, kept, ready, resident, _⟩ :=
        SourceEqualityProjectionRead.complete _ _ semantic available closed
      cases read with
      | done fuel actual => exact ⟨fuel, edges, after, actual, kept, ready, resident⟩
  | @unfold entry body depth ordinary next actual rest =>
      have resultAvailable := unfolded_available semantic available actual
      obtain ⟨fuel, edges, after, done, kept, ready, resident⟩ :=
        collect_complete (.unfold actual rest) semantic available []
      have fallback : (collect fuel state [] [.mu entry body depth ordinary]).canonical =
          .done (canonicalEdges edges) after := by rw [done]; rfl
      cases next with
      | node entry edges depth free =>
          exact ⟨0, edges, state, by simp only [nodeEdges, actual], pure_keeps _ semantic.ready, semantic,
            InternedEdgeResidency.resident_edges _ semantic.ready.semantic.1.normal.facts.linked _ resultAvailable.resident⟩
      | empty | reference | union | mu =>
          exact ⟨fuel, canonicalEdges edges, after, by simpa only [nodeEdges, actual] using fallback,
            kept, ready, fun edge member => resident edge (canonicalEdges_member edges edge member)⟩

/-- A false completed gate derives the actual nodeEdges read in a later retained constructor cache. -/
theorem nodeEdges_complete [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {path : Path} {value : Value Symbol Guard}
    {before final : State Symbol Guard}
    (trace : NodeTrace unconstrained path value before false final)
    (semantic : SemanticReady before) (available : Available before value)
    (caller : State Symbol Guard) (callerSemantic : SemanticReady caller) (callerAvailable : Available caller value)
    (growth : Grows final caller) :
    ∃ fuel edges after, nodeEdges fuel value caller = .done edges after ∧ Keeps caller after ∧
      SemanticReady after ∧ Edges after edges :=
  warm_nodeEdges_complete (warm_head trace semantic available caller growth) callerSemantic callerAvailable

/-- A false completed gate derives finite actual head reconstruction without whole-value closedness. -/
theorem head_complete [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {path : Path} {value : Value Symbol Guard}
    {before final : State Symbol Guard}
    (trace : NodeTrace unconstrained path value before false final)
    (semantic : SemanticReady before) (available : Available before value)
    (caller : State Symbol Guard) (callerSemantic : SemanticReady caller) (callerAvailable : Available caller value)
    (growth : Grows final caller) :
    ∃ result after, Head value caller result after ∧ Keeps caller after ∧
      SemanticReady after ∧ Available after result ∧ Ordinary result := by
  obtain ⟨fuel, edges, middle, actual, kept, ready, resident⟩ :=
    nodeEdges_complete trace semantic available caller callerSemantic callerAvailable growth
  have rebuilt := SourceEqualityOpenOrdinaryHead.node edges middle ready resident
  exact ⟨_, _, .read fuel edges middle actual rfl, kept.trans rebuilt.1, rebuilt.2⟩

/-- Every actual completed head agrees with the head derived from the false gate. -/
theorem head_verified [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {path : Path} {value result : Value Symbol Guard}
    {before final caller after : State Symbol Guard}
    (gate : NodeTrace unconstrained path value before false final)
    (semantic : SemanticReady before) (available : Available before value)
    (callerSemantic : SemanticReady caller) (callerAvailable : Available caller value) (growth : Grows final caller)
    (actual : Head value caller result after) :
    Keeps caller after ∧ SemanticReady after ∧ Available after result ∧ Ordinary result := by
  obtain ⟨value, state, head, kept, ready, resident, ordinary⟩ :=
    head_complete gate semantic available caller callerSemantic callerAvailable growth
  obtain ⟨sameValue, sameState⟩ := head.unique actual
  cases sameValue
  cases sameState
  exact ⟨kept, ready, resident, ordinary⟩

end MicroCFTA.SourceSecondaryGateHead
