import MicroCFTA.SourceCurrentConstrainedCapProjection
import MicroCFTA.InternedFreshOrdinarySourceFreeNames

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 200

namespace MicroCFTA.ConstrainedCapProjectionKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open InternedNestedProvenance (Values Edges)
open SourceEqualityAnnotationLanguage SourceEqualityAnnotationConstruction
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityProjectionGraph
open SourceCurrentHereditaryConstruction (MuStored)
open SourceCurrentConstrainedCap (Cap Edge)
variable {Symbol Guard : Type}

/-- Actual recursive construction and an arbitrary bad guard supply their own finite endpoint. -/
theorem constructed_bad_shell_endpoint [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) (symbol : Symbol) (good bad : Guard) (goodValid : valid good) (badInvalid : ¬valid bad) :
    ∃ recursive initial row edgeHeap shell before result after,
      InternedFreshOrdinaryConstruction.build (.binder false (.node [.mk symbol good [.var 0]])) [] empty =
        .done recursive initial ∧
      run (makeEdge symbol bad [recursive]) initial = (row, edgeHeap) ∧
      run (makeNode [row]) edgeHeap = (shell, before) ∧
      row.entry.key.constraint = bad ∧ ¬valid row.entry.key.constraint ∧
      Cap valid 1 shell ∧
      Project [0, 0] shell before result after ∧
      MuStored valid after ∧ Annotated valid result ∧ Keeps before after ∧
      SemanticReady after ∧ Available after result ∧ result.free = [] ∧
      SourceEqualityRequiredWorkerComplete.StableRun
        (fun fuel readFuel => SourceEqualityProjectionWorker.project fuel readFuel [0, 0] shell before) result after := by
  let expression : Syntax Symbol Guard := .binder false (.node [.mk symbol good [.var 0]])
  have allowed : Allowed valid expression := by
    simp [expression, Allowed, EdgesAllowed, ManyAllowed, goodValid]
  obtain ⟨recursive, initial, built, stored, annotated⟩ := SourceCurrentHereditaryConstruction.closed valid expression allowed
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression recursive initial built
  have available := (InternedFreshOrdinaryFacts.closed_verified expression).result recursive initial built
  have closed := InternedFreshOrdinarySourceFreeNames.closed_free_empty expression recursive initial built
  let row := (run (makeEdge symbol bad [recursive]) initial).1
  let edgeHeap := (run (makeEdge symbol bad [recursive]) initial).2
  have inputs : Values initial [recursive] := by
    intro value member
    exact (List.mem_singleton.mp member) ▸ available
  have edgePhysical := SourceEqualityRequiredCache.edge symbol bad [recursive] initial semantic.ready inputs
  have edgeSemantic := SourceEqualityRequiredSemanticCache.edge symbol bad [recursive] initial semantic inputs
  have rowResident : Edges edgeHeap [row] := by
    intro edge member
    exact (List.mem_singleton.mp member) ▸ edgePhysical.2.1
  have rowClosed : MergedColdReaderClosedInputs.ClosedEdges [row] := by
    intro edge member
    cases List.mem_singleton.mp member
    change MergedColdReaderClosedInputs.ClosedValues row.children
    rw [show row.children = [recursive] from edgePhysical.2.2]
    intro value present
    exact (List.mem_singleton.mp present) ▸ closed
  have rowBound : Edge valid 1 row := SourceCurrentConstrainedCap.makeEdge valid 1 symbol bad [recursive] initial
    semantic.ready.semantic.1.normal.facts.coherent semantic.ready.semantic.1.normal.facts.cached inputs
    (by omega) (by intro value member; exact (List.mem_singleton.mp member) ▸ Cap.plain 0 annotated)
  let shell := (run (makeNode [row]) edgeHeap).1
  let before := (run (makeNode [row]) edgeHeap).2
  have shellPhysical := SourceEqualityRequiredCache.node [row] edgeHeap edgeSemantic.ready rowResident rowClosed
  have shellSemantic := SourceEqualityRequiredSemanticCache.node [row] edgeHeap edgeSemantic rowResident rowClosed
  have shellBound : Cap valid 1 shell := SourceCurrentConstrainedCap.makeNode valid 1 [row] edgeHeap
    edgeSemantic.ready.semantic.1.normal.facts.coherent edgeSemantic.ready.semantic.1.normal.facts.linked rowResident
    (by intro edge member; exact (List.mem_singleton.mp member) ▸ rowBound)
  have edgeStored : MuStored valid edgeHeap := stored.makeEdge symbol bad [recursive]
  have shellStored : MuStored valid before := edgeStored.makeNode [row]
  obtain ⟨result, after, actual, kept, resultSemantic, resultAvailable, resultClosed, resultStored, resultAnnotated⟩ :=
    SourceCurrentConstrainedCapProjection.complete_endpoint valid 1 [0, 0] shell before shellSemantic shellPhysical.2.1
      shellPhysical.2.2.1 shellStored shellBound (by decide)
  have key := InternedOrdinaryAbsenceReplay.makeEdge_key symbol bad [recursive] initial semantic.ready.semantic.1.normal.facts.coherent
  have constraint : row.entry.key.constraint = bad := by
    simpa only [row] using congrArg EdgeKey.constraint key
  exact ⟨recursive, initial, row, edgeHeap, shell, before, result, after, built, rfl, rfl,
    constraint, constraint ▸ badInvalid, shellBound, actual, resultStored, resultAnnotated, kept,
    resultSemantic, resultAvailable, resultClosed, SourceEqualityProjectionWorkerComplete.node_stable actual⟩

/-- A forest's root selector consumes no constraint depth; its next child selector consumes one. -/
theorem forest_offset [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    (value : Value Symbol Guard) (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Available before value) (closed : value.free = []) (stored : MuStored valid before)
    (bounded : Cap valid 1 value) :
    ∃ selected middle result after,
      Forest [0] [value] before selected middle ∧ Cap valid 1 selected ∧
      Forest [0, 0] [value] middle result after ∧ MuStored valid after ∧ Annotated valid result ∧
      Keeps before after ∧ Available after result ∧ result.free = [] := by
  obtain ⟨selected, middle, first, firstKeeps, firstSemantic, _, _, middleStored, selectedBound⟩ :=
    SourceCurrentConstrainedCapProjection.forest_complete valid 1 [0] [value] before semantic
      (by intro child member; exact (List.mem_singleton.mp member) ▸ available)
      (by intro child member; exact (List.mem_singleton.mp member) ▸ closed) stored
      (by intro child member; exact (List.mem_singleton.mp member) ▸ bounded)
  obtain ⟨result, after, second, secondKeeps, _, resultAvailable, resultClosed, resultStored, resultBound⟩ :=
    SourceCurrentConstrainedCapProjection.forest_complete valid 1 [0, 0] [value] middle firstSemantic
      (by intro child member; exact firstKeeps.available child ((List.mem_singleton.mp member) ▸ available))
      (by intro child member; exact (List.mem_singleton.mp member) ▸ closed) middleStored
      (by intro child member; exact (List.mem_singleton.mp member) ▸ bounded)
  exact ⟨selected, middle, result, after, first, selectedBound, second, resultStored,
    resultBound.annotated rfl, firstKeeps.trans secondKeeps, resultAvailable, resultClosed⟩

#print axioms constructed_bad_shell_endpoint
#check @constructed_bad_shell_endpoint
#print axioms forest_offset
#check @forest_offset
end MicroCFTA.ConstrainedCapProjectionKernels
