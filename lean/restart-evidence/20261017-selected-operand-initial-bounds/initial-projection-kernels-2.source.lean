import MicroCFTA.SourceCurrentProjectionNumeric
import MicroCFTA.SourceEqualityProjectionAPI
import MicroCFTA.InternedFreshOrdinaryCosts

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.fullNames true
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

namespace MicroCFTA.InitialProjectionIntegration
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceEqualityProjectionGraph (Forest)
open SourceEqualityProjectionPathDomain (ForestClosed)
open SourceCurrentMemoMergeResourceControl (Fits)
open SourceCurrentProjectionInitialResources (forestBound)
open SourceCurrentProjectionNumeric (workFuel readFuel)
open SourceEqualityProjectionWorker (project forest)

private def expression : InternedNestedConstruction.Syntax Nat Bool :=
  .union [.binder false (.node [.mk 0 true [.var 0], .mk 1 true []]), .node [.mk 3 false []]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def input : Value Nat Bool := match built with | .done value _ => value | .pending .. => .empty
private def source := built.state
private def observed := project 12 8 [0, 0] input source
private def output : Value Nat Bool := match observed with | .done value _ => value | _ => .empty
private def after := match observed with | .done _ state => state | _ => source
private def resource := SourceCurrentMemoMergeResourceControl.initialBound source.nodes.next source.edges.next
  (InternedValueMassHeap.initialBound source)
private def proper : List Int := [0, 0, 0]
private def mixed : List (Value Nat Bool) := [input, .reference .depth]

private theorem constructed : built = .done input source := by cbv
private theorem semantic : SemanticReady source := SourceEqualityRequiredSemanticCache.constructed expression input source constructed
private theorem costs : InternedFreshOrdinaryCostHeap.Heap source := InternedFreshOrdinaryCosts.closed_heap expression
private theorem available : Available source input := (InternedFreshOrdinaryFacts.closed_verified expression).result input source constructed
private theorem closed : input.free = [] := by cbv
private theorem initial : Fits resource source := SourceCurrentMemoMergeResourceControl.initial source
  (InternedValueMassHeap.initialBound source) (InternedValueMassHeap.initial source semantic.ready.semantic.1.normal.facts)
private theorem singleton_available : Values source [input] := by
  intro value member
  exact List.mem_singleton.mp member ▸ available
private theorem singleton_domain : ForestClosed proper [input] := by
  intro value found
  have same : input = value := Option.some.inj found
  subst value
  cbv
private theorem literal : observed = .done output after := by cbv
private theorem forest_literal : forest 12 8 proper [input] source = .done output after := literal

/-- Initial source construction produces the complete allocating recursive path at computed fuels. -/
theorem recursive_initial :
    built = .done input source ∧
      (match input with | .union _ members _ _ => ∃ member ∈ members, (match member with | .mu .. => True | _ => False) | _ => False) ∧
      project 12 8 [0, 0] input source = .done output after ∧
      source.nodes.next < after.nodes.next ∧ source.edges.next < after.edges.next ∧
      Forest proper [input] source output after ∧
      forest (workFuel proper) (readFuel proper 1 resource) proper [input] source = .done output after ∧
      Fits (forestBound proper 1 resource) after ∧
      InternedValueMass.value output ≤ forestBound proper 1 resource ∧
      ∀ workExtra readExtra,
        forest (workFuel proper + workExtra) (readFuel proper 1 resource + readExtra)
          proper [input] source = .done output after := by
  obtain ⟨result, final, actual, done, _keeps, _ready, _costs, _available, _closed, fits, mass, stable⟩ :=
    SourceCurrentProjectionNumeric.complete proper [input] source resource semantic costs singleton_available singleton_domain initial
  have concrete := SourceEqualityProjectionWorkerSound.forest_graph 12 8 proper [input] source output after forest_literal
  obtain ⟨rfl, rfl⟩ := SourceEqualityProjectionAPI.forest_unique actual concrete
  exact ⟨constructed, by cbv; exact ⟨_, List.mem_cons_self, True.intro⟩, literal,
    by cbv, by cbv, actual, done, fits, mass, stable⟩

private theorem mixed_available : Values source mixed := by
  intro value member
  rcases List.mem_cons.mp member with rfl | member
  · exact available
  · exact List.mem_singleton.mp member ▸ InternedNestedProvenance.depth_available source
private theorem mixed_domain : ForestClosed proper mixed := by
  intro value found
  have same : input = value := Option.some.inj found
  subst value
  cbv

/-- Proper forest projection ignores an unrelated open reference and constructs its own exact return. -/
theorem selected_beside_open :
    ForestClosed proper mixed ∧ ¬MergedColdReaderClosedInputs.ClosedValues mixed ∧
      Forest proper mixed source output after ∧
      forest (workFuel proper) (readFuel proper 2 resource) proper mixed source = .done output after ∧
      Fits (forestBound proper 2 resource) after ∧ Available after output ∧ output.free = [] := by
  obtain ⟨result, final, actual, done, _keeps, _ready, _costs, resultAvailable, resultClosed, fits, _mass, _stable⟩ :=
    SourceCurrentProjectionNumeric.complete proper mixed source resource semantic costs mixed_available mixed_domain initial
  have concrete := SourceEqualityProjectionWorkerSound.forest_graph 12 8 proper mixed source output after forest_literal
  obtain ⟨rfl, rfl⟩ := SourceEqualityProjectionAPI.forest_unique actual concrete
  refine ⟨mixed_domain, ?_, actual, done, fits, resultAvailable, resultClosed⟩
  intro impossible
  have bad := impossible (.reference .depth) (by simp [mixed])
  cases bad

private theorem missing_complete (index : Int)
    (absent : SourceEqualityProjectionGraph.select mixed index = none) :
    Forest [index] mixed source .empty source ∧
      forest (workFuel [index]) (readFuel [index] 2 resource) [index] mixed source = .done .empty source ∧
      Fits (forestBound [index] 2 resource) source := by
  have domain : ForestClosed [index] mixed := by
    intro value found
    rw [absent] at found
    cases found
  obtain ⟨result, final, actual, done, _keeps, _ready, _costs, _available, _closed, fits, _mass, _stable⟩ :=
    SourceCurrentProjectionNumeric.complete [index] mixed source resource semantic costs mixed_available domain initial
  have expected : Forest [index] mixed source .empty source := .missing absent
  obtain ⟨rfl, rfl⟩ := SourceEqualityProjectionAPI.forest_unique actual expected
  exact ⟨actual, done, fits⟩

/-- Negative and absent positive forest positions use the initial endpoint and keep the complete heap. -/
theorem signed_missing :
    Forest [-1] mixed source .empty source ∧
      forest (workFuel [-1]) (readFuel [-1] 2 resource) [-1] mixed source = .done .empty source ∧
      Fits (forestBound [-1] 2 resource) source ∧
      Forest [99] mixed source .empty source ∧
      forest (workFuel [99]) (readFuel [99] 2 resource) [99] mixed source = .done .empty source ∧
      Fits (forestBound [99] 2 resource) source := by
  have negative := missing_complete (-1) rfl
  have positive := missing_complete 99 rfl
  exact ⟨negative.1, negative.2.1, negative.2.2, positive.1, positive.2.1, positive.2.2⟩

private def rootObserved := forest 12 8 [] [input, input] source
private def rootOutput : Value Nat Bool := match rootObserved with | .done value _ => value | _ => .empty
private def rootAfter := match rootObserved with | .done _ state => state | _ => source
private def rootBound := forestBound [] 2 resource
private theorem root_literal : rootObserved = .done rootOutput rootAfter := by cbv
private theorem duplicate_available : Values source [input, input] := by
  intro value member
  rcases List.mem_cons.mp member with rfl | member
  · exact available
  · exact List.mem_singleton.mp member ▸ available
private theorem duplicate_domain : ForestClosed [] [input, input] := by
  intro value member
  rcases List.mem_cons.mp member with rfl | member
  · exact closed
  · exact List.mem_singleton.mp member ▸ closed

/-- Duplicate root operands retain exact union language and support an own warm second call. -/
theorem root_duplicates_warm :
    ∃ _first : Forest [] [input, input] source rootOutput rootAfter,
      forest (workFuel []) (readFuel [] 2 resource) [] [input, input] source = .done rootOutput rootAfter ∧
      Fits rootBound rootAfter ∧
      (∀ holds ambient term, InternedGuardedLanguage.meaning holds ambient rootOutput term ↔
        InternedGuardedLanguage.meaning holds ambient input term) ∧
      ∃ _warm : Forest [] [input, input] rootAfter rootOutput rootAfter,
        forest (workFuel []) (readFuel [] 2 rootBound) [] [input, input] rootAfter = .done rootOutput rootAfter ∧
        Fits (forestBound [] 2 rootBound) rootAfter := by
  obtain ⟨result, final, actual, done, keeps, ready, afterCosts, _available, _closed, fits, _mass, _stable⟩ :=
    SourceCurrentProjectionNumeric.complete [] [input, input] source resource semantic costs duplicate_available duplicate_domain initial
  have concrete := SourceEqualityProjectionWorkerSound.forest_graph 12 8 [] [input, input] source rootOutput rootAfter root_literal
  obtain ⟨rfl, rfl⟩ := SourceEqualityProjectionAPI.forest_unique actual concrete
  have currentAvailable : Values rootAfter [input, input] := fun value member => keeps.available value (duplicate_available value member)
  obtain ⟨second, final, warm, warmed, _keeps, _ready, _costs, _available, _closed, warmFits, _mass, _stable⟩ :=
    SourceCurrentProjectionNumeric.complete [] [input, input] rootAfter rootBound ready afterCosts currentAvailable duplicate_domain fits
  have warmLiteral : forest 12 8 [] [input, input] rootAfter = .done rootOutput rootAfter := by cbv
  have warmConcrete := SourceEqualityProjectionWorkerSound.forest_graph 12 8 [] [input, input] rootAfter rootOutput rootAfter warmLiteral
  obtain ⟨rfl, rfl⟩ := SourceEqualityProjectionAPI.forest_unique warm warmConcrete
  refine ⟨actual, done, fits, ?_, warm, warmed, warmFits⟩
  intro holds ambient term
  simpa using SourceEqualityProjectionAPI.forest_root actual semantic duplicate_available duplicate_domain holds ambient term

end MicroCFTA.InitialProjectionIntegration

#print axioms MicroCFTA.InitialProjectionIntegration.recursive_initial
#check @MicroCFTA.InitialProjectionIntegration.recursive_initial
#print axioms MicroCFTA.InitialProjectionIntegration.selected_beside_open
#check @MicroCFTA.InitialProjectionIntegration.selected_beside_open
#print axioms MicroCFTA.InitialProjectionIntegration.signed_missing
#check @MicroCFTA.InitialProjectionIntegration.signed_missing
#print axioms MicroCFTA.InitialProjectionIntegration.root_duplicates_warm
#check @MicroCFTA.InitialProjectionIntegration.root_duplicates_warm
