import MicroCFTA.SourceRecursiveIntersectionNativeWalkLower
import MicroCFTA.SourceRecursiveIntersectionNativeReturnDegreeFacts

namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionInputView SourceRecursiveIntersectionCode IntersectSchedule
open InternedStoredPlanBinderDepthProgress
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceRecursiveIntersectionKernel (pairs pairs_member)

/-- Actual row prefixes retain the original parent bound through completed edge calls. -/
theorem rows_prefix_lower
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : InternedNestedFacts.Facts source)
    (limit : Nat) (sourceBounded : InternedMuDepthInventory.Bounded source limit)
    (holds : Guard → Language.Term Symbol → Bool) (width : Nat)
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (bound : Nat)
    (edgeIH : ∀ (request : EdgeRequest Symbol Guard), EdgeBelow source holds bound request →
      ∀ (current : SourceRecursiveIntersectionThunks.State width Symbol Guard),
      SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin current → EdgeReady current.machine request →
      Grows source current.machine.heap → Extends source.nodes.issued current.machine.heap.nodes.issued →
      SemanticHeap current.machine.heap → InternedOpenDepthReadback.Heap current.machine.heap →
      WordRanges emptyGuard conjoin (.edge request .pure) current →
      ∀ fuel, Lower current.machine.heap (limit + bound)
        (execute emptyGuard conjoin fuel (.edge request .pure) current).state.machine.heap)
    (domain : Interned DomainKey) (left right : List (EdgeValue Symbol Guard))
    (rowBounds : ∀ rows ∈ pairs left right, EdgeBelow source holds bound ⟨domain, rows.1, rows.2⟩)
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state)
    (known : SourceRecursiveIntersectionKernel.Domain state.machine domain)
    (leftResident : ∀ row ∈ left, EdgeResident state.machine.heap row)
    (rightResident : ∀ row ∈ right, EdgeResident state.machine.heap row)
    (growth : Grows source state.machine.heap) (history : Extends source.nodes.issued state.machine.heap.nodes.issued)
    (semantic : SemanticHeap state.machine.heap) (opened : InternedOpenDepthReadback.Heap state.machine.heap)
    (ranges : WordRanges emptyGuard conjoin (compileRows domain left right) state) (fuel : Nat) :
    Lower state.machine.heap (limit + bound)
      (execute emptyGuard conjoin fuel (compileRows domain left right) state).state.machine.heap := by
  let requests := pairs left right
  let call (rows : EdgeValue Symbol Guard × EdgeValue Symbol Guard) := requestEdge domain rows.1 rows.2
  let invariant (current : SourceRecursiveIntersectionThunks.State width Symbol Guard) : Prop :=
    SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin current ∧
    SourceRecursiveIntersectionKernel.Domain current.machine domain ∧
    (∀ rows ∈ requests, EdgeResident current.machine.heap rows.1 ∧ EdgeResident current.machine.heap rows.2) ∧
    Grows source current.machine.heap ∧ Extends source.nodes.issued current.machine.heap.nodes.issued ∧
    SemanticHeap current.machine.heap ∧ InternedOpenDepthReadback.Heap current.machine.heap
  have limited : ∀ rows ∈ requests, ∀ current, invariant current →
      WordRanges emptyGuard conjoin (call rows) current →
      ∀ inner, Lower current.machine.heap (limit + bound)
        (execute emptyGuard conjoin inner (call rows) current).state.machine.heap := by
    intro rows present current currentKnown callRanges inner
    obtain ⟨currentValid, currentDomain, currentRows, currentGrowth, currentHistory, currentSemantic, currentOpened⟩ := currentKnown
    exact edgeIH ⟨domain, rows.1, rows.2⟩ (rowBounds rows present) current currentValid
      ⟨currentDomain, currentRows rows present⟩ currentGrowth currentHistory currentSemantic currentOpened callRanges inner
  have preserved : ∀ rows ∈ requests, ∀ current, invariant current →
      WordRanges emptyGuard conjoin (call rows) current →
      ∀ inner value after, execute emptyGuard conjoin inner (call rows) current = .done value after → invariant after := by
    intro rows present current currentKnown callRanges inner value after completed
    obtain ⟨scope, complete, _below⟩ := rowBounds rows present
    obtain ⟨currentValid, currentDomain, currentRows, currentGrowth, currentHistory, currentSemantic, currentOpened⟩ := currentKnown
    obtain ⟨afterValid, extension, _resident, afterSemantic, afterOpened, _degree⟩ :=
      edge_return_degree_facts source facts limit sourceBounded holds width emptyGuard conjoin inner
        ⟨domain, rows.1, rows.2⟩ scope complete current after currentValid ⟨currentDomain, currentRows rows present⟩
        currentGrowth currentHistory currentSemantic currentOpened callRanges value completed
    exact ⟨afterValid, currentDomain.grows domain extension,
      (fun rows included => ⟨edge_grows _ _ extension.heap _ (currentRows rows included).1,
        edge_grows _ _ extension.heap _ (currentRows rows included).2⟩),
      grows_trans currentGrowth extension.heap, extends_trans currentHistory extension.history, afterSemantic, afterOpened⟩
  have initialRows : ∀ rows ∈ requests, EdgeResident state.machine.heap rows.1 ∧ EdgeResident state.machine.heap rows.2 := by
    intro rows present
    obtain ⟨first, second, _⟩ := (pairs_member left right rows).mp present
    exact ⟨leftResident rows.1 first, rightResident rows.2 second⟩
  change WordRanges emptyGuard conjoin ((walk call requests).bind fun rows => .work (makeNode rows) .pure) state at ranges
  change Lower state.machine.heap (limit + bound)
    (execute emptyGuard conjoin fuel ((walk call requests).bind fun rows => .work (makeNode rows) .pure) state).state.machine.heap
  have walkRanges := ranges.before_bind emptyGuard conjoin (walk call requests) (fun rows => .work (makeNode rows) .pure) state
  apply execute_bind_lower emptyGuard conjoin fuel (walk call requests) (fun rows => .work (makeNode rows) .pure) state (limit + bound)
  · exact walk_prefix_lower emptyGuard conjoin call invariant (limit + bound) requests limited preserved state
      ⟨valid, known, initialRows, growth, history, semantic, opened⟩ walkRanges
  · intro _ rows after _ outer
    exact work_lower emptyGuard conjoin outer (makeNode rows) after (limit + bound)
      (InternedShallowHeap.makeNode_noNewMu rows after.machine.heap)

end MicroCFTA.SourceRecursiveIntersectionNative
