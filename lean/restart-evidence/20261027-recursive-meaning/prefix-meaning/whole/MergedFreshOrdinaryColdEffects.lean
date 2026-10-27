import MicroCFTA.MergedFreshOrdinaryExposure
import MicroCFTA.InternedFreshOrdinaryUnfoldCompletion
import MicroCFTA.SourceRecursiveIntersectionSemanticHeap

/-!
# General repaired cold-reader effects

Every bounded read of closed available records retains the complete semantic
cache and payload coverage. It returns resident edges with closed children,
or it exhausts the proof bound. It cannot return a pending constructor or an
unresolved reference. Unfolding can add Mu records. Finite completion of the
whole traversal remains a separate obligation.
-/
namespace MicroCFTA.MergedFreshOrdinaryColdEffects
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open InternedEdgeResidency (edge_grows resident_edges)
open MergedSourceExposure (Result)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open MergedFreshOrdinaryExposure

/-- The exact reader outcome keeps complete caches and excludes source failures. -/
structure Verified (before : State Symbol Guard) (result : Result Symbol Guard) : Prop where
  semantic : SemanticHeap result.state
  covered : Covered [] result.state
  growth : Grows before result.state
  history : Extends before.nodes.issued result.state.nodes.issued
  edges : ∀ values after, result = .done values after → Edges after values
  closed : ∀ values after, result = .done values after → ClosedEdges values
  outcome : match result with
    | .done .. | .exhausted .. => True
    | .pending .. | .unresolved .. => False

/-- A finished edge list retains its exact cache and closed children. -/
theorem done_verified (state : State Symbol Guard) (semantic : SemanticHeap state)
    (covered : Covered [] state) (edges : List (EdgeValue Symbol Guard))
    (resident : Edges state edges) (closed : ClosedEdges edges) : Verified state (.done edges state) :=
  ⟨semantic, covered, grows_refl _, extends_refl _, (by intro _ _ same; cases same; exact resident),
    (by intro _ _ same; cases same; exact closed), True.intro⟩

/-- An exhausted bound retains every cache invariant. -/
theorem exhausted_verified (state : State Symbol Guard) (semantic : SemanticHeap state)
    (covered : Covered [] state) : Verified state (.exhausted state) :=
  ⟨semantic, covered, grows_refl _, extends_refl _, (by intro _ _ same; cases same),
    (by intro _ _ same; cases same), True.intro⟩

/-- Earlier unfolding effects compose with the exact remaining reader outcome. -/
theorem Verified.extend {before middle : State Symbol Guard} {result : Result Symbol Guard}
    (verified : Verified middle result) (growth : Grows before middle)
    (history : Extends before.nodes.issued middle.nodes.issued) : Verified before result :=
  ⟨verified.semantic, verified.covered, grows_trans growth verified.growth,
    extends_trans history verified.history, verified.edges, verified.closed, (by cases result <;> exact verified.outcome)⟩

/-- Every earlier input remains available after the actual reader effects. -/
theorem Verified.available {before : State Symbol Guard} {result : Result Symbol Guard}
    (verified : Verified before result) (value : Value Symbol Guard) (available : Available before value) :
    Available result.state value := available.grows _ _ verified.growth verified.history

/-- Prepending earlier resident edges retains their closed children after later effects. -/
theorem Verified.prepend {state : State Symbol Guard} {result : Result Symbol Guard}
    (verified : Verified state result) (edges : List (EdgeValue Symbol Guard))
    (resident : Edges state edges) (closed : ClosedEdges edges) : Verified state (result.prepend edges) := by
  cases result with
  | unresolved | pending | exhausted => exact verified
  | done values after =>
      refine ⟨verified.semantic, verified.covered, verified.growth, verified.history, ?_, ?_, True.intro⟩
      · intro output final same
        cases same
        intro edge member
        rcases List.mem_append.mp member with first | later
        · exact edge_grows state after verified.growth edge (resident edge first)
        · exact verified.edges values after rfl edge later
      · intro output final same
        cases same
        intro edge member
        rcases List.mem_append.mp member with first | later
        · exact closed edge first
        · exact verified.closed values after rfl edge later

/-- Canonical edge ordering preserves the same cache and closed resident children. -/
theorem Verified.canonical {state : State Symbol Guard} {result : Result Symbol Guard}
    (verified : Verified state result) : Verified state result.canonical := by
  cases result with
  | unresolved | pending | exhausted => exact verified
  | done values after =>
      refine ⟨verified.semantic, verified.covered, verified.growth, verified.history, ?_, ?_, True.intro⟩
      · intro output final same
        cases same
        exact fun edge member => verified.edges values after rfl edge (canonicalEdges_member values edge member)
      · intro output final same
        cases same
        exact fun edge member => verified.closed values after rfl edge (canonicalEdges_member values edge member)

/-- Every bounded repaired worklist retains complete semantic caches and closed edge children. -/
theorem collect_verified [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (state : State Symbol Guard)
    (semantic : SemanticHeap state) (covered : Covered [] state) (seen : List Nat)
    (pending : List (Value Symbol Guard)) (inputs : Values state pending) (closed : ClosedValues pending) :
    Verified state (collect fuel state seen pending) := by
  induction fuel generalizing state seen pending with
  | zero =>
      cases pending with
      | nil => exact done_verified state semantic covered [] (by simp [Edges]) (by simp [ClosedEdges])
      | cons => exact exhausted_verified state semantic covered
  | succ fuel ih =>
      cases pending with
      | nil => exact done_verified state semantic covered [] (by simp [Edges]) (by simp [ClosedEdges])
      | cons value rest =>
          have available := inputs value List.mem_cons_self
          have valueClosed := closed value List.mem_cons_self
          have restInputs : Values state rest := fun child member => inputs child (List.mem_cons_of_mem _ member)
          have restClosed : ClosedValues rest := fun child member => closed child (List.mem_cons_of_mem _ member)
          have facts := semantic.1.normal.facts
          cases value with
          | empty => exact ih state semantic covered seen rest restInputs restClosed
          | reference name => simp [Value.free] at valueClosed
          | node entry edges depth free =>
              exact (ih state semantic covered seen rest restInputs restClosed).prepend edges
                (resident_edges state facts.linked (.node entry edges depth free) available.resident)
                (MergedColdReaderClosed.node_children_closed state facts entry edges depth free available valueClosed)
          | union entry members depth free =>
              by_cases visited : entry.identity ∈ seen
              · simpa only [collect, ite_eq_left visited] using ih state semantic covered seen rest restInputs restClosed
              · have nextInputs : Values state (members ++ rest) := by
                  intro child member
                  rcases List.mem_append.mp member with first | later
                  · exact available.children child first
                  · exact restInputs child later
                have nextClosed : ClosedValues (members ++ rest) := by
                  intro child member
                  rcases List.mem_append.mp member with first | later
                  · exact MergedColdReaderClosed.union_members_closed state facts entry members depth free available valueClosed child first
                  · exact restClosed child later
                simpa only [collect, ite_eq_right visited] using
                  ih state semantic covered (entry.identity :: seen) (members ++ rest) nextInputs nextClosed
          | mu entry body depth ordinary =>
              by_cases visited : entry.identity ∈ seen
              · simpa only [collect, ite_eq_left visited] using ih state semantic covered seen rest restInputs restClosed
              · obtain ⟨result, after, done, context, heap, finalCovered, resultAvailable, growth, history⟩ :=
                  InternedFreshOrdinaryStoredSubstitution.unfold_complete_decoded (.mu entry body depth ordinary)
                    state semantic.1 available semantic.2 covered
                have resultClosed := InternedFreshOrdinaryStoredSubstitution.unfold_closed (.mu entry body depth ordinary)
                  state semantic.1 available valueClosed result after done
                have nextInputs : Values after (result :: rest) := by
                  intro child member
                  rcases List.mem_cons.mp member with rfl | member
                  · exact resultAvailable
                  · exact (restInputs child member).grows state after growth history
                have nextClosed : ClosedValues (result :: rest) := by
                  intro child member
                  rcases List.mem_cons.mp member with rfl | member
                  · exact resultClosed
                  · exact restClosed child member
                have next := (ih after ⟨context, heap⟩ finalCovered (entry.identity :: seen)
                  (result :: rest) nextInputs nextClosed).extend growth history
                simpa only [collect, ite_eq_right visited, done] using next

/-- Direct and closure reader paths retain the same complete cache invariants without preparation. -/
theorem nodeEdges_verified [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (value : Value Symbol Guard)
    (state : State Symbol Guard) (semantic : SemanticHeap state) (covered : Covered [] state)
    (available : Available state value) (closed : value.free = []) :
    Verified state (nodeEdges fuel value state) := by
  have fallback (current : State Symbol Guard) (currentSemantic : SemanticHeap current)
      (currentCovered : Covered [] current) (root : Value Symbol Guard)
      (rootAvailable : Available current root) (rootClosed : root.free = []) :
      Verified current (collect fuel current [] [root]).canonical :=
    (collect_verified fuel current currentSemantic currentCovered [] [root]
      (by intro value member; simpa only [List.mem_singleton.mp member] using rootAvailable)
      (by intro value member; simpa only [List.mem_singleton.mp member] using rootClosed)).canonical
  have ordinary (current : State Symbol Guard) (currentSemantic : SemanticHeap current)
      (currentCovered : Covered [] current) (entry : Interned InternedBinderProtocol.NodeKey)
      (edges : List (EdgeValue Symbol Guard)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
      (resident : Available current (.node entry edges depth free)) (valueClosed : free = []) :
      Verified current (.done edges current) :=
    done_verified current currentSemantic currentCovered edges
      (resident_edges current currentSemantic.1.normal.facts.linked (.node entry edges depth free) resident.resident)
      (MergedColdReaderClosed.node_children_closed current currentSemantic.1.normal.facts entry edges depth free resident valueClosed)
  cases value with
  | empty | reference => exact done_verified state semantic covered [] (by simp [Edges]) (by simp [ClosedEdges])
  | node entry edges depth free => exact ordinary state semantic covered entry edges depth free available closed
  | union entry members depth free => exact fallback state semantic covered _ available closed
  | mu entry body depth ordinaryShape =>
      obtain ⟨result, after, done, context, heap, finalCovered, resultAvailable, growth, history⟩ :=
        InternedFreshOrdinaryStoredSubstitution.unfold_complete_decoded (.mu entry body depth ordinaryShape)
          state semantic.1 available semantic.2 covered
      have rootAvailable := available.grows state after growth history
      have closure := (fallback after ⟨context, heap⟩ finalCovered _ rootAvailable closed).extend growth history
      have resultClosed := InternedFreshOrdinaryStoredSubstitution.unfold_closed (.mu entry body depth ordinaryShape)
        state semantic.1 available closed result after done
      cases result with
      | node entry edges depth free =>
          simpa only [nodeEdges, done] using
            (ordinary after ⟨context, heap⟩ finalCovered entry edges depth free resultAvailable resultClosed).extend growth history
      | empty | reference | union | mu => simpa only [nodeEdges, done] using closure

end MicroCFTA.MergedFreshOrdinaryColdEffects
