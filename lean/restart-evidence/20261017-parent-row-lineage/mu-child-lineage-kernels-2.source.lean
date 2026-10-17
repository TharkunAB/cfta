import MicroCFTA.SourceCurrentStoredMuChildLineage

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.MuChildLineageKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction
open InternedFreshOrdinaryContext
open InternedFreshOrdinaryLiveInputs
open InternedStoredSubstitution (Environment Replacements)
open InternedFreshOrdinaryStoredSubstitution (execute)
open SourceEqualityRequiredCache (Ready Keeps)

private def leafSource : Syntax Nat Bool := .node [.mk 3 true []]
private def leafBuilt := build leafSource [] empty
private def leaf := match leafBuilt with | .done value _ => value | .pending .. => .empty
private def base := leafBuilt.state
private def expression : Syntax Nat Bool := .binder true (.node [.mk 8 false [.var 0,.var 2]])
private def inputs : List (Sum (Value Nat Bool) Unit) := [.inr (),.inl (.reference (.uninterned 42))]
private def first := build expression (inputs.map (input (fun _ => .uninterned 0))) base
private def rawFirst := match first with | .done value _ => value | .pending .. => .empty
private def firstHeap := first.state
private def second := build expression (inputs.map (input (fun _ => .uninterned 9))) firstHeap
private def rawSecond := match second with | .done value _ => value | .pending .. => .empty
private def common := second.state
private def isMu : Value Nat Bool → Bool
  | .mu .. => true
  | _ => false
private def firstEnvironment : Environment Nat Bool :=
  fun name => if name = .uninterned 42 then some leaf else none
private def secondEnvironment : Environment Nat Bool :=
  fun name => if name = .uninterned 55 then some (.reference .depth) else firstEnvironment name

private theorem leafActual : leafBuilt = .done leaf base := by cbv
private theorem firstActual : first = .done rawFirst firstHeap := by cbv
private theorem secondActual : second = .done rawSecond common := by cbv
private theorem baseReady : Ready base := SourceEqualityRequiredCache.constructed leafSource leaf base leafActual

private theorem sourceReady (source : Syntax Nat Bool) (environment : List (Value Nat Bool))
    (before : State Nat Bool) (ready : Ready before)
    (available : InternedNestedProvenance.Values before environment)
    (value : Value Nat Bool) (after : State Nat Bool)
    (actual : build source environment before = .done value after) : Ready after := by
  have context := SourceRecursiveIntersectionSemanticHeap.context before ready.semantic environment available
  refine ⟨?_,
    InternedFreshOrdinaryCoverage.build_covered source environment before
      ready.semantic.1.normal.facts.coherent.valid ready.covered value after actual,?_⟩
  · simpa only [actual,Outcome.state] using SourceRecursiveIntersectionSemanticHeap.source source environment before ready.semantic available
  · simpa only [actual,Outcome.state] using (InternedOpenDepthExecution.build_depth source environment before context ready.semantic.2 ready.depth).heap

private theorem firstInputs : InternedNestedProvenance.Values base (inputs.map (input (fun _ => .uninterned 0))) := by
  intro value member
  simp only [inputs,List.map_cons,List.map_nil,input,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl <;> exact InternedNestedProvenance.ordinary_available _ _
private theorem firstReady : Ready firstHeap := sourceReady expression _ base baseReady firstInputs rawFirst firstHeap firstActual
private theorem secondInputs : InternedNestedProvenance.Values firstHeap (inputs.map (input (fun _ => .uninterned 9))) := by
  intro value member
  simp only [inputs,List.map_cons,List.map_nil,input,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl <;> exact InternedNestedProvenance.ordinary_available _ _
private theorem commonReady : Ready common := sourceReady expression _ firstHeap firstReady secondInputs rawSecond common secondActual

/-- Initial source data yields identical sequential nested-Mu reconstructions under distinct outer maps. -/
theorem independent_nested_used_mu :
    first = .done rawFirst firstHeap ∧ second = .done rawSecond common ∧
    firstEnvironment ≠ secondEnvironment ∧
    ∃ result resultHeap, rawFirst = rawSecond ∧
      execute rawFirst firstEnvironment common = .done result resultHeap ∧
      execute rawSecond secondEnvironment resultHeap = .done result resultHeap ∧
      execute rawFirst firstEnvironment resultHeap = .done result resultHeap ∧
      Keeps common resultHeap ∧ Available resultHeap result ∧
      Nonempty (SourceCurrentNativeMuPublication.History common resultHeap) ∧
      isMu result = true := by
  have firstChecked := InternedFreshOrdinaryFacts.build_verified expression _ base baseReady.semantic.1.normal.facts firstInputs
  have secondChecked := InternedFreshOrdinaryFacts.build_verified expression _ firstHeap firstReady.semantic.1.normal.facts secondInputs
  have rawAvailable : Available common rawFirst :=
    secondChecked.available rawFirst (firstChecked.result rawFirst firstHeap firstActual)
  have leafAvailable : Available common leaf := by
    have initial := (InternedFreshOrdinaryFacts.build_verified leafSource [] empty InternedNestedFacts.empty_facts
      (by intro value member; cases member)).result leaf base leafActual
    exact secondChecked.available leaf (firstChecked.available leaf initial)
  have replacements : Replacements common firstEnvironment := by
    intro name value found
    dsimp only [firstEnvironment] at found
    split at found
    · cases found; exact leafAvailable
    · cases found
  have inactive : ∀ atom, Sum.inr atom ∉ SourceCurrentNativeNormalizationInputs.support expression inputs := by
    intro atom
    cases atom
    have support_eq : SourceCurrentNativeNormalizationInputs.support expression inputs = [.inl (.uninterned 42)] := by cbv
    rw [support_eq,List.mem_singleton]
    intro impossible
    cases impossible
  have compatible : ∀ name, Sum.inl name ∈ SourceCurrentNativeNormalizationInputs.support expression inputs →
      firstEnvironment name = secondEnvironment name := by
    intro name member
    have support_eq : SourceCurrentNativeNormalizationInputs.support expression inputs = [.inl (.uninterned 42)] := by cbv
    have same : name = .uninterned 42 := by
      simpa only [support_eq,List.mem_singleton,Sum.inl.injEq] using member
    subst name
    rfl
  obtain ⟨result,resultHeap,same,done,other,replay,kept,available,history⟩ :=
    SourceCurrentStoredMuChildLineage.independent expression inputs (fun _ => .uninterned 0) (fun _ => .uninterned 9)
      base firstHeap firstHeap common common
      (SourceRecursiveIntersectionSemanticHeap.context base baseReady.semantic _ firstInputs)
      (SourceRecursiveIntersectionSemanticHeap.context firstHeap firstReady.semantic _ secondInputs)
      rawFirst rawSecond firstActual secondActual secondChecked.growth (grows_refl _)
      inactive firstEnvironment secondEnvironment compatible commonReady rawAvailable replacements
  have retained : isMu result = true := by
    have known : (match execute rawFirst firstEnvironment common with | .done value _ => isMu value | _ => false) = true := by cbv
    simpa only [done] using known
  refine ⟨firstActual,secondActual,?_,result,resultHeap,same,done,other,replay,kept,available,history,retained⟩
  intro equal
  have different := congrFun equal (.uninterned 55)
  cases different

end MicroCFTA.MuChildLineageKernels
