import MicroCFTA.SourceCurrentReaderFiniteUnionStep

set_option linter.all true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.ReaderUnionKernels
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedBinderProtocol (NodeKey Reference)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentReaderFiniteOrdinaryStep (RelatedAt)
open SourceCurrentFiniteObservationExecution (AlignedAt)
open SourceCurrentOpenObservations (Same)
open InternedStoredSubstitution (Environment Replacements)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedNestedProvenance (Values)

private def value (outcome : Outcome Nat Bool (Value Nat Bool)) :=
  match outcome with | .done result _ => result | .pending .. => .empty
private def nodeKey : Value Nat Bool → NodeKey
  | .node entry .. | .union entry .. | .mu entry .. => entry.key
  | _ => .node []
private def unary (symbol : Nat) (guard : Bool) : Syntax Nat Bool := .node [.mk symbol guard [.var 0]]
private def expressions : List (Syntax Nat Bool) := [unary 1 false,unary 2 true]
private def body : Syntax Nat Bool := .union expressions
private def source : Syntax Nat Bool := .node [.mk 9 false [.binder false body,.node [.mk 3 false []]]]
private def built := build source [] empty
private def root := value built
private def initial := built.state
private def bound := (children root)[0]?.getD .empty
private def boundId : Nat := match bound with | .mu entry .. => entry.identity | _ => 0
private def own : Reference := .interned boundId
private def replacement := (children root)[1]?.getD .empty
private def raw := value (build body [.reference own] initial)
private def rawMember := value (build (unary 1 false) [.reference own] initial)
private def environment : Environment Nat Bool := fun name => if name = own then some replacement else none
private def first := execute raw environment initial
private def reader := first.state
private def result := value first
private def memberCall := execute rawMember environment reader
private def memberResult := value memberCall
private def memberAfter := memberCall.state

private theorem source_done : build source [] empty = .done root initial := by cbv
private theorem initial_ready : Ready initial := SourceEqualityRequiredCache.constructed source root initial source_done
private theorem raw_available : Available initial raw :=
  initial_ready.semantic.1.normal.facts.cached.nodes (nodeKey raw) raw (by cbv)
private theorem member_available : Available initial rawMember :=
  initial_ready.semantic.1.normal.facts.cached.nodes (nodeKey rawMember) rawMember (by cbv)
private theorem replacement_available : Available initial replacement :=
  initial_ready.semantic.1.normal.facts.cached.nodes (nodeKey replacement) replacement (by cbv)
private theorem reference_available : Available initial (.reference own) := by
  apply InternedProbeProvenance.reference_available
  intro identity member
  have same : identity = boundId := by
    simpa only [own,Value.free,List.mem_singleton,Reference.interned.injEq] using member
  subst identity
  exact ⟨nodeKey bound,by cbv⟩
private theorem replacements : Replacements initial environment := by
  intro name output found
  simp only [environment] at found
  split at found
  · cases found; exact replacement_available
  · cases found
private theorem first_done : execute raw environment initial = .done result reader := by cbv
private theorem kept : Keeps initial reader := by
  obtain ⟨output,after,done,effect,_available,_history⟩ :=
    SourceCurrentStoredReconstruction.execute raw environment initial initial_ready raw_available replacements
  obtain ⟨rfl,rfl⟩ := Outcome.done.inj (done.symm.trans first_done)
  exact effect
private theorem raw_warm : build body [.reference own] reader = .done raw reader := by cbv
private theorem stored_warm : execute raw environment reader = .done result reader := by cbv
private theorem member_raw_warm : build (unary 1 false) [.reference own] reader = .done rawMember reader := by cbv
private theorem member_done : execute rawMember environment reader = .done memberResult memberAfter := by cbv
private theorem cold : memberAfter.nodes.next = reader.nodes.next + 1 := by cbv
private theorem reader_changed : reader.nodes.next = initial.nodes.next + 1 := by cbv
private theorem result_fields : (InternedEdgeResidency.nodeEdges result).map
    (fun row => (row.entry.key.symbol,row.entry.key.constraint,row.children)) =
      [(1,false,[replacement]),(2,true,[replacement])] := by cbv
private theorem used :
    match bound with
    | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true
    | _ => False := by cbv

private theorem unary_aligned (symbol : Nat) (guard : Bool) (depth : Nat)
    (view common : State Nat Bool) : AlignedAt depth view common (unary symbol guard) := by
  intro leftInputs rightInputs firstMap secondMap paired ready firstInputs secondInputs
    firstReplacements secondReplacements rawFirst rawSecond firstRaw secondRaw left right firstDone secondDone
  have matched := SourceCurrentFiniteObservationExecution.ordinary [.mk symbol guard [.var 0]] depth view common
    (by
      intro rowIndex actualSymbol actualGuard originals rowFound childIndex child childFound _smaller
      have equal := List.mem_singleton.mp (List.mem_of_getElem? rowFound)
      cases equal
      have equalChild := List.mem_singleton.mp (List.mem_of_getElem? childFound)
      subst child
      exact SourceCurrentFiniteObservationExecution.reference depth view common 0)
    leftInputs rightInputs firstMap secondMap paired ready firstInputs secondInputs
    firstReplacements secondReplacements rawFirst rawSecond firstRaw secondRaw left right firstDone secondDone
  exact ⟨matched.1,matched.2.lower⟩

private theorem aligned : AlignedAt 2 initial reader body := by
  apply SourceCurrentReaderFiniteUnionStep.union expressions 2 initial
  intro index child found _smaller common
  have included : child = unary 1 false ∨ child = unary 2 true := by
    simpa only [expressions,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using List.mem_of_getElem? found
  rcases included with rfl | rfl
  · exact unary_aligned 1 false 2 initial common
  · exact unary_aligned 2 true 2 initial common

private theorem related : RelatedAt 2 initial result result := by
  have inputs : Values reader [.reference own] := by
    intro input member
    obtain rfl := List.mem_singleton.mp member
    exact kept.available _ reference_available
  have env : Replacements reader environment := fun name output found => kept.available output (replacements name output found)
  apply aligned [.reference own] [.reference own] environment environment ?_ kept.ready inputs inputs env env
    raw raw raw_warm raw_warm result result stored_warm stored_warm
  exact .cons ⟨Iff.rfl,Same.refl 2 initial [_]⟩ .nil

private theorem witness :
    build source [] empty = .done root initial ∧ Ready initial ∧
    (match bound with
      | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true
      | _ => False) ∧
    build body [.reference own] reader = .done raw reader ∧
    execute raw environment reader = .done result reader ∧
    build (unary 1 false) [.reference own] reader = .done rawMember reader ∧
    execute rawMember environment reader = .done memberResult memberAfter ∧
    memberAfter.nodes.next = reader.nodes.next + 1 ∧ memberAfter ≠ reader ∧
    Keeps initial reader ∧ reader.nodes.next = initial.nodes.next + 1 ∧
    (InternedEdgeResidency.nodeEdges result).map (fun row => (row.entry.key.symbol,row.entry.key.constraint,row.children)) =
      [(1,false,[replacement]),(2,true,[replacement])] ∧ RelatedAt 2 initial result result := by
  refine ⟨source_done,initial_ready,used,raw_warm,stored_warm,member_raw_warm,member_done,cold,?_,kept,reader_changed,result_fields,related⟩
  intro same
  have equal := congrArg (fun heap : State Nat Bool => heap.nodes.next) same
  rw [cold] at equal
  omega

/-- A warm merged source uses the finite union step while an original subgroup still allocates. -/
theorem warm_parent_cold_subgroup :
    build source [] empty = .done root initial ∧ Ready initial ∧
    (match bound with
      | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true
      | _ => False) ∧
    build body [.reference own] reader = .done raw reader ∧
    execute raw environment reader = .done result reader ∧
    build (unary 1 false) [.reference own] reader = .done rawMember reader ∧
    execute rawMember environment reader = .done memberResult memberAfter ∧
    memberAfter.nodes.next = reader.nodes.next + 1 ∧ memberAfter ≠ reader ∧
    Keeps initial reader ∧ reader.nodes.next = initial.nodes.next + 1 ∧
    (InternedEdgeResidency.nodeEdges result).map (fun row => (row.entry.key.symbol,row.entry.key.constraint,row.children)) =
      [(1,false,[replacement]),(2,true,[replacement])] ∧ RelatedAt 2 initial result result := witness
end MicroCFTA.ReaderUnionKernels
