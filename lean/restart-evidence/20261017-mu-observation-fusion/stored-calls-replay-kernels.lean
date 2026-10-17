import MicroCFTA.SourceCurrentStoredCallsReplay
import MicroCFTA.SourceCurrentStoredReconstruction
import MicroCFTA.SourceRecursiveIntersectionSemanticHeap
import MicroCFTA.InternedOpenDepthExecution

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000

namespace MicroCFTA.StoredCallsReplayKernels
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedBinderProtocol (Reference)
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentStoredSubstitutionCalls (Calls)
open SourceCurrentStoredCallsReplay
open Language

private def expression : Syntax Nat Bool := .node [.mk 9 false
  [.node [.mk 1 false []],
   .binder false (.node [.mk 0 false [.var 0, .binder false (.var 2)]])]]
private def inputs : List (Value Nat Bool) := [.reference (.uninterned 0)]
private def children : Value Nat Bool → List (Value Nat Bool)
  | .node _ (.mk _ values :: _) _ _ => values
  | _ => []
private def built := build expression inputs empty
private def source : Value Nat Bool := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def replacement : Value Nat Bool := (children source)[0]?.getD Value.empty
private def outer : Value Nat Bool := (children source)[1]?.getD Value.empty
private def originals := [outer,replacement,outer]
private def environment : InternedStoredSubstitution.Environment Nat Bool :=
  fun name => if name = Reference.uninterned 0 then some replacement else none
private def nested : Value Nat Bool := match outer with
  | .mu _ body _ _ => (children body)[1]?.getD Value.empty
  | _ => .empty
private def used : Value Nat Bool → Bool
  | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary
  | _ => false
private theorem built_done : built = .done source heap := by cbv
private theorem empty_ready : Ready (empty : State Nat Bool) :=
  SourceEqualityRequiredCache.constructed .empty .empty empty (by rw [build])
private theorem inputs_available : Values (empty : State Nat Bool) inputs := by
  intro value member
  simp only [inputs,List.mem_cons,List.not_mem_nil,or_false] at member
  subst value
  apply reference_available
  all_goals intro identity impossible; simp [Value.free] at impossible

private theorem source_ready : Ready heap := by
  let context := SourceRecursiveIntersectionSemanticHeap.context empty empty_ready.semantic inputs inputs_available
  have actual : build expression inputs empty = .done source heap := built_done
  refine ⟨?_,?_,?_⟩
  · simpa only [actual,Outcome.state] using
      SourceRecursiveIntersectionSemanticHeap.source expression inputs empty empty_ready.semantic inputs_available
  · exact InternedFreshOrdinaryCoverage.build_covered expression inputs empty context.normal.facts.coherent.valid
      empty_ready.covered source heap built_done
  · simpa only [actual,Outcome.state] using
      (InternedOpenDepthExecution.build_depth expression inputs empty context empty_ready.semantic.2 empty_ready.depth).heap

private theorem source_available : Available heap source :=
  (InternedFreshOrdinaryFacts.build_verified expression inputs empty empty_ready.semantic.1.normal.facts inputs_available).result
    source heap built_done

private theorem child_available (state : State Nat Bool) (value : Value Nat Bool) (available : Available state value) :
    Values state (children value) := by
  cases value <;> try (intro child impossible; cases impossible)
  case node entry rows level free =>
    cases rows with
    | nil => intro child impossible; cases impossible
    | cons row rest =>
        cases row with
        | mk edge values =>
            intro child member
            exact available.children child (List.mem_flatMap.mpr ⟨.mk edge values,List.mem_cons_self,member⟩)
private theorem replacement_available : Available heap replacement := by
  apply child_available heap source source_available replacement
  exact List.mem_of_getElem? (show (children source)[0]? = some replacement by cbv)
private theorem outer_available : Available heap outer := by
  apply child_available heap source source_available outer
  exact List.mem_of_getElem? (show (children source)[1]? = some outer by cbv)
private theorem originals_available : Values heap originals := by
  intro value member
  simp only [originals,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact outer_available
  · exact replacement_available
  · exact outer_available
private theorem replacements : InternedStoredSubstitution.Replacements heap environment := by
  intro name value found
  simp only [environment] at found
  split at found
  · cases found; exact replacement_available
  · cases found

private theorem complete_calls (values : List (Value Nat Bool)) (before : State Nat Bool) (ready : Ready before)
    (available : Values before values) (provided : InternedStoredSubstitution.Replacements before environment) :
    ∃ outputs after, Calls environment values before outputs after ∧ Keeps before after ∧ Values after outputs := by
  induction values generalizing before with
  | nil => exact ⟨[],before,.nil before,SourceEqualityRequiredCache.pure_keeps before ready,
      fun _ impossible => False.elim (List.not_mem_nil impossible)⟩
  | cons value rest ih =>
      obtain ⟨output,middle,called,keeps,result,_⟩ := SourceCurrentStoredReconstruction.execute value environment before
        ready (available value List.mem_cons_self) provided
      obtain ⟨outputs,after,remaining,tail,results⟩ := ih middle keeps.ready
        (fun item member => keeps.available item (available item (List.mem_cons_of_mem _ member)))
        (fun name item found => keeps.available item (provided name item found))
      refine ⟨output::outputs,after,.cons value rest before middle after output outputs called remaining,keeps.trans tail,?_⟩
      intro item member
      rcases List.mem_cons.mp member with rfl | later
      · exact tail.available _ result
      · exact results item later

private theorem repeated {outputs : List (Value Nat Bool)} (common : State Nat Bool)
    (warm : All₂ (fun original output => execute original environment common = .done output common) originals outputs) :
    ∃ first second, outputs = [first,second,first] := by
  change All₂ (fun original output => execute original environment common = .done output common)
    [outer,replacement,outer] outputs at warm
  cases warm with
  | cons first rest =>
    cases rest with
    | cons second tail =>
      cases tail with
      | cons third last =>
        cases last
        have same := (Outcome.done.inj (first.symm.trans third)).1
        cases same
        exact ⟨_,_,rfl⟩

/-- Initial actual nested source data produces two sequences and exact common-heap replay for each repeated member. -/
theorem actual_repeated_replay :
    build expression inputs empty = .done source heap ∧ Ready heap ∧ Values heap originals ∧
    InternedStoredSubstitution.Replacements heap environment ∧ used outer = true ∧ nested.free ≠ [] ∧
    ∃ left middle right after,
      Calls environment originals heap left middle ∧ Calls environment originals middle right after ∧
      Keeps heap middle ∧ Keeps middle after ∧ left = right ∧
      All₂ (fun original output => execute original environment after = .done output after) originals left ∧
      ∃ first second, left = [first,second,first] := by
  have valid := source_ready.semantic.1.normal.facts.coherent.valid
  obtain ⟨left,middle,first,firstKept,firstValues⟩ :=
    complete_calls originals heap source_ready originals_available replacements
  have middleValid := (correct first valid).1
  obtain ⟨right,after,second,secondKept,secondValues⟩ := complete_calls originals middle firstKept.ready
    (fun value member => firstKept.available value (originals_available value member))
    (fun name value found => firstKept.available value (replacements name value found))
  have equal := same first second after valid middleValid secondKept.growth (grows_refl after)
  have warm := replay first after valid secondKept.growth
  refine ⟨built_done,source_ready,originals_available,replacements,?_,?_,left,middle,right,after,
    first,second,firstKept,secondKept,equal,warm,repeated after warm⟩
  · cbv
  · cbv; simp

#check @actual_repeated_replay
#print axioms actual_repeated_replay
end MicroCFTA.StoredCallsReplayKernels
