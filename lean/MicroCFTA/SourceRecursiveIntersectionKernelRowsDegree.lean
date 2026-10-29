import MicroCFTA.SourceRecursiveIntersectionKernelEdgeWalkDegree
import MicroCFTA.InternedStoredPlanBinderDepthNormalization

/-!
# Degree through the actual ordered source row walk

Each row uses the smaller runtime-fuel node hypothesis.
The walk passes the actual reached heap to the next row.
Canonical node construction retains the maximum child degree.
-/
namespace MicroCFTA.SourceRecursiveIntersectionKernel
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionInputView SourceRecursiveIntersectionNative IntersectSchedule
open SourceRecursiveIntersectionCode InternedNestedFacts InternedStoredPlanBinderDepth
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)

/-- Ordered row returns bound the actual canonical node result. -/
theorem rows_degree
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (sourceFacts : Facts source)
    (holds : Guard → Language.Term Symbol → Bool) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (limit fuel : Nat)
    (nodeIH : ∀ (request : NodeRequest Symbol Guard) (_scope : NodeScope source request)
      (complete : Completes (view source holds) (nodeSemantic request))
      (state after : Machine Symbol Guard) (_valid : Valid state) (_ready : NodeReady state request)
      (_growth : Grows source state.heap) (_history : Extends source.nodes.issued state.heap.nodes.issued)
      (_semantic : SemanticHeap state.heap) (_opened : InternedOpenDepthReadback.Heap state.heap)
      (value : Value Symbol Guard),
      execute emptyGuard conjoin fuel request.domain request.left request.right state = .done value after →
      SemanticHeap after.heap ∧ InternedOpenDepthReadback.Heap after.heap ∧
        valueDepth value ≤ limit + requiredFuel (view source holds) (nodeSemantic request) complete)
    (bound : Nat) (domain : Interned DomainKey) (left right : List (EdgeValue Symbol Guard))
    (rowBounds : ∀ rows ∈ pairs left right, EdgeBelow source holds bound ⟨domain, rows.1, rows.2⟩)
    (state after : Machine Symbol Guard) (valid : Valid state) (known : Domain state domain)
    (leftResident : ∀ row ∈ left, EdgeResident state.heap row)
    (rightResident : ∀ row ∈ right, EdgeResident state.heap row)
    (growth : Grows source state.heap) (history : Extends source.nodes.issued state.heap.nodes.issued)
    (semantic : SemanticHeap state.heap) (opened : InternedOpenDepthReadback.Heap state.heap)
    (value : Value Symbol Guard)
    (done : node emptyGuard conjoin (execute emptyGuard conjoin fuel domain) left right state = .done value after) :
    SemanticHeap after.heap ∧ InternedOpenDepthReadback.Heap after.heap ∧ valueDepth value ≤ limit + bound := by
  have traceBound (requests : List (EdgeValue Symbol Guard × EdgeValue Symbol Guard))
      (first : Machine Symbol Guard) (values : List (EdgeValue Symbol Guard)) (last : Machine Symbol Guard)
      (trace : WalkTrace (fun rows => edge emptyGuard conjoin (execute emptyGuard conjoin fuel domain) rows.1 rows.2)
        requests first values last) :
      (∀ rows ∈ requests, EdgeBelow source holds bound ⟨domain, rows.1, rows.2⟩) →
      Valid first → Domain first domain →
      (∀ rows ∈ requests, EdgeResident first.heap rows.1 ∧ EdgeResident first.heap rows.2) →
      Grows source first.heap → Extends source.nodes.issued first.heap.nodes.issued →
      SemanticHeap first.heap → InternedOpenDepthReadback.Heap first.heap →
      SemanticHeap last.heap ∧ InternedOpenDepthReadback.Heap last.heap ∧ edgesDepth values ≤ limit + bound := by
    induction trace with
    | nil current =>
        intro _ _ _ _ _ _ currentSemantic currentOpened
        exact ⟨currentSemantic, currentOpened, by simpa only [edgesDepth] using Nat.zero_le (limit + bound)⟩
    | cons rows requests current firstValue middle values last returned _rest ih =>
        intro bounded currentValid currentKnown inputs currentGrowth currentHistory currentSemantic currentOpened
        obtain ⟨rowScope, rowComplete, rowLess⟩ := bounded rows (by simp)
        have resident := inputs rows (by simp)
        obtain ⟨middleSemantic, middleOpened, firstDegree⟩ := edge_result_degree source sourceFacts holds
          emptyGuard conjoin limit fuel nodeIH ⟨domain, rows.1, rows.2⟩ rowScope rowComplete current middle
          currentValid ⟨currentKnown, resident⟩ currentGrowth currentHistory currentSemantic currentOpened firstValue returned
        have checked := edge_checked emptyGuard conjoin (execute emptyGuard conjoin fuel)
          (execute_checked emptyGuard conjoin fuel) domain rows.1 rows.2 current currentValid currentKnown resident.1 resident.2
        have middleValid : Valid middle := by simpa only [returned, Result.state] using checked.valid
        have extension : Extension current middle := by simpa only [returned, Result.state] using checked.extension
        have middleInputs : ∀ pair ∈ requests, EdgeResident middle.heap pair.1 ∧ EdgeResident middle.heap pair.2 := by
          intro pair member
          have earlier := inputs pair (by simp [member])
          exact ⟨edge_grows _ _ extension.heap _ earlier.1, edge_grows _ _ extension.heap _ earlier.2⟩
        obtain ⟨lastSemantic, lastOpened, restDegree⟩ := ih
          (fun pair member => bounded pair (by simp [member])) middleValid (currentKnown.grows _ extension) middleInputs
          (grows_trans currentGrowth extension.heap) (extends_trans currentHistory extension.history)
          middleSemantic middleOpened
        refine ⟨lastSemantic, lastOpened, ?_⟩
        cases firstValue with
        | mk entry children =>
            simpa only [edgesDepth, EdgeValue.children] using
              Nat.max_le.mpr ⟨Nat.le_trans firstDegree (Nat.add_le_add_left (Nat.le_of_lt rowLess) limit), restDegree⟩
  have inputs : ∀ rows ∈ pairs left right, EdgeResident state.heap rows.1 ∧ EdgeResident state.heap rows.2 := by
    intro rows member
    obtain ⟨first, second, _⟩ := (pairs_member left right rows).mp member
    exact ⟨leftResident rows.1 first, rightResident rows.2 second⟩
  have checked := rows_checked emptyGuard conjoin (execute emptyGuard conjoin fuel)
    (execute_checked emptyGuard conjoin fuel) domain left right state valid known leftResident rightResident
  simp only [node] at done
  cases walked : walk (fun rows => edge emptyGuard conjoin (execute emptyGuard conjoin fuel domain) rows.1 rows.2)
      (pairs left right) state with
  | failed failure middle => simp only [walked, Result.bind] at done; cases done
  | done rows middle =>
      have middleValid : Valid middle := by simpa only [walked, Result.state] using checked.valid
      have resident := checked.result rows middle walked
      obtain ⟨middleSemantic, middleOpened, rowsDegree⟩ := traceBound _ state rows middle
        ((walk_done_iff _ _ _ _ _).mp walked) rowBounds valid known inputs growth history semantic opened
      simp only [walked, Result.bind] at done
      obtain ⟨sameValue, sameAfter⟩ := work_done _ middle value after done
      rw [sameAfter, sameValue]
      refine ⟨SourceRecursiveIntersectionSemanticHeap.node rows middle.heap middleSemantic resident,
        SourceRecursiveIntersectionOpenDepthEffects.node rows middle.heap middleOpened, ?_⟩
      apply makeNode_le rows middle.heap middleValid.1.coherent middleValid.1.linked resident (limit + bound)
      rw [edges_eq_many] at rowsDegree
      exact (many_le_iff _ _).mp rowsDegree

end MicroCFTA.SourceRecursiveIntersectionKernel
