import MicroCFTA.SourceCurrentNativeBinderReaderRows
import MicroCFTA.SourceCurrentStoredMuLexicalInputs
import MicroCFTA.SourceCurrentStoredSubstitutionOrigins
import MicroCFTA.SourceCurrentPublicationFilterSource

/-!
# Ordinary rows through actual stored Mu substitution

An open stored Mu executes its original body under the actual local binding.
Each physical ordinary result row occurs in that body's raw result.
The local binding shadows only the original binder name. Nested Mu values
remain in scope. Literal row occurrence does not unfold a retained Mu.
-/
namespace MicroCFTA.SourceCurrentStoredMuRowOrigins
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Outcome)
open InternedFreshOrdinaryConstruction (build ordinaryLevel)
open InternedFreshOrdinaryFacts (callback)
open InternedStoredSubstitution (Environment Replacements leaves input encode)
open InternedFreshOrdinaryStoredSubstitution (execute)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentStoredMuLexicalInputs (shadow)
open SourceCurrentNativeMuPublication (History)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open InternedBinderProtocol (NodeKey Reference)

/-- Each physical row retains its exact original body execution and the actual binder readback. -/
def Rows [DecidableEq (EdgeKey Symbol Guard)] (entry : Interned NodeKey) (body : Value Symbol Guard)
    (captures : List (Value Symbol Guard)) (environment : Environment Symbol Guard)
    (before : State Symbol Guard) (value : Value Symbol Guard) (after reader : State Symbol Guard) : Prop :=
  ∀ (rowIndex : Nat) (row : EdgeValue Symbol Guard), (nodeEdges value)[rowIndex]? = some row →
    (body.free.filter (· != .interned entry.identity)).isEmpty = false ∧
    ∃ depth afterDepth raw middle,
      callback (encode captures [.interned entry.identity] body) (captures.map (input environment))
        .depth before = .done depth afterDepth ∧
      execute body (shadow (.interned entry.identity)
        (.reference (.uninterned (ordinaryLevel depth))) environment) afterDepth = .done raw middle ∧
      Available afterDepth body ∧
      Replacements afterDepth (shadow (.interned entry.identity)
        (.reference (.uninterned (ordinaryLevel depth))) environment) ∧
      SourceCurrentLiteralRootParts.Row raw row ∧
      SourceCurrentNativeBinderReaderRows.Rows (encode captures [.interned entry.identity] body)
        (captures.map (input environment)) before value after reader rowIndex row

private theorem closed [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (environment : Environment Symbol Guard) (before : State Symbol Guard) (noFree : value.free = []) :
    execute value environment before = .done value before := by
  unfold execute
  have captured : leaves value = [value] := by
    rw [leaves.eq_def]
    simp only [noFree, List.isEmpty_nil, ite_true]
  rw [captured]
  have encoded : encode [value] [] value = .var 0 := by
    rw [encode.eq_def]
    simp [noFree, InternedStoredSubstitution.slot]
  rw [encoded]
  simpa only [List.map_cons, List.map_nil, build, List.getElem?_cons_zero, Option.getD_some] using
    congrArg (fun result => (Outcome.done result before : Outcome Symbol Guard (Value Symbol Guard)))
      (InternedStoredSubstitutionScope.input_closed value environment noFree)

private theorem literal_row (value : Value Symbol Guard) (rowIndex : Nat) (row : EdgeValue Symbol Guard)
    (selected : (nodeEdges value)[rowIndex]? = some row) : SourceCurrentLiteralRootParts.Row value row := by
  cases value with
  | node entry rows level free => exact .node (List.mem_of_getElem? selected)
  | empty | reference | union | mu => simp only [nodeEdges, List.getElem?_nil] at selected; cases selected

/-- Actual stored Mu substitution derives an original-body call for each physical result row. -/
theorem mu [DecidableEq (EdgeKey Symbol Guard)] (entry : Interned NodeKey) (body : Value Symbol Guard)
    (depth ordinary : Value Symbol Guard) (environment : Environment Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticHeap before)
    (available : Available before (.mu entry body depth ordinary)) (replacements : Replacements before environment)
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (actual : execute (.mu entry body depth ordinary) environment before = .done value after)
    (reader : State Symbol Guard) (history : History empty reader) (growth : Grows after reader) :
    Rows entry body (leaves (.mu entry body depth ordinary)) environment before value after reader := by
  intro rowIndex row selected
  by_cases noFree : (Value.mu entry body depth ordinary).free = []
  · rw [closed (.mu entry body depth ordinary) environment before noFree] at actual
    have same := Outcome.done.inj actual
    rw [← same.1] at selected
    simp only [nodeEdges, List.getElem?_nil] at selected
    cases selected
  · have opened : (Value.mu entry body depth ordinary).free.isEmpty = false := by
      simpa only [List.isEmpty_eq_false_iff] using noFree
    let captures := leaves (.mu entry body depth ordinary)
    let expression := encode captures [.interned entry.identity] body
    let inputs := captures.map (input environment)
    have compiled : encode captures [] (.mu entry body depth ordinary) = .binder true expression := by
      rw [encode.eq_def]
      simp only [opened, Bool.false_eq_true, ite_false]
    have inputAvailable := InternedStoredSubstitution.inputs_available _ environment before available replacements
    have context : Context before inputs := ⟨SourceRecursiveIntersectionSemanticHeap.context before semantic
      inputs inputAvailable, semantic.2⟩
    change build (encode captures [] (.mu entry body depth ordinary)) inputs before = .done value after at actual
    rw [compiled] at actual
    have rows := SourceCurrentNativeBinderReaderRows.binder_row expression inputs before context value after actual
      reader history growth rowIndex row selected
    obtain ⟨currentDepth,afterDepth,currentOrdinary,cut,raw,middle,winner,storedBody,
      depthDone,ordinaryDone,requestDone,rawDone,filtered,depthContext,cutContext,finalContext,rawContext,rawAvailable,
      depthGrowth,depthIssued,rawStepGrowth,rawStepIssued,rawGrowth,rawIssued,beforeRawGrowth,beforeRawIssued,
      beforeAfterGrowth,beforeAfterIssued,present,readerCell,returned,correct,unused,sameBody,selfAbsent,bodyRow,
      erased,origins,rawOrigins⟩ := rows
    have bodyAvailable : Available before body := available.children body (by simp [children])
    have covered : ∀ leaf ∈ leaves body, leaf ∈ captures := by
      intro leaf member
      simpa only [captures, leaves.eq_def, opened, Bool.false_eq_true, ite_false] using member
    have bodyCall := SourceCurrentStoredMuLexicalInputs.build_shadow captures body (.interned entry.identity)
      (.reference (.uninterned (ordinaryLevel currentDepth))) environment before afterDepth semantic.1.normal.facts.coherent
      (InternedStoredSubstitution.leaves_available _ before available) bodyAvailable covered
    have executed : execute body (shadow (.interned entry.identity)
        (.reference (.uninterned (ordinaryLevel currentDepth))) environment) afterDepth = .done raw middle := by
      rw [← bodyCall]
      exact rawDone
    have bodyLater := bodyAvailable.grows before afterDepth depthGrowth depthIssued
    have replacementsLater := SourceCurrentStoredMuLexicalInputs.replacements (.interned entry.identity)
      (.reference (.uninterned (ordinaryLevel currentDepth))) environment before afterDepth replacements
      depthGrowth depthIssued (InternedNestedProvenance.ordinary_available afterDepth (ordinaryLevel currentDepth))
    have preserved := SourceCurrentPublicationFilterSource.filtered_row middle rawContext.base.normal
      (.uninterned (ordinaryLevel currentDepth)) raw rawAvailable row
    rw [filtered] at preserved
    have rawRow : SourceCurrentLiteralRootParts.Row raw row :=
      preserved.mp (erased ▸ literal_row value rowIndex row selected)
    refine ⟨opened,currentDepth,afterDepth,raw,middle,depthDone,executed,bodyLater,replacementsLater,rawRow,?_⟩
    exact ⟨currentDepth,afterDepth,currentOrdinary,cut,raw,middle,winner,storedBody,
      depthDone,ordinaryDone,requestDone,rawDone,filtered,depthContext,cutContext,finalContext,rawContext,rawAvailable,
      depthGrowth,depthIssued,rawStepGrowth,rawStepIssued,rawGrowth,rawIssued,beforeRawGrowth,beforeRawIssued,
      beforeAfterGrowth,beforeAfterIssued,present,readerCell,returned,correct,unused,sameBody,selfAbsent,bodyRow,
      erased,origins,rawOrigins⟩

/-- Initial semantic inputs construct the stored Mu return and its original-body row calls. -/
theorem mu_complete [DecidableEq (EdgeKey Symbol Guard)] (entry : Interned NodeKey) (body : Value Symbol Guard)
    (depth ordinary : Value Symbol Guard) (environment : Environment Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticHeap before) (covered : Covered [] before)
    (available : Available before (.mu entry body depth ordinary)) (replacements : Replacements before environment)
    (history : History empty before) :
    ∃ value after, execute (.mu entry body depth ordinary) environment before = .done value after ∧
      SemanticHeap after ∧ Covered [] after ∧ Available after value ∧
      Nonempty (History before after) ∧ Nonempty (History empty after) ∧
      Rows entry body (leaves (.mu entry body depth ordinary)) environment before value after after := by
  obtain ⟨value,after,actual,context,depthHeap,retained,output,_,_⟩ :=
    InternedFreshOrdinaryStoredSubstitution.execute_complete_decoded _ environment before semantic.1
      available replacements semantic.2 covered
  have initialContext := SourceRecursiveIntersectionSemanticHeap.context before semantic
    ((leaves (.mu entry body depth ordinary)).map (input environment))
    (InternedStoredSubstitution.inputs_available _ environment before available replacements)
  have emitted := SourceCurrentNativeMuPublication.build_history
    (encode (leaves (.mu entry body depth ordinary)) [] (.mu entry body depth ordinary))
    ((leaves (.mu entry body depth ordinary)).map (input environment)) before ⟨initialContext,semantic.2⟩
  change Nonempty (History before (execute (.mu entry body depth ordinary) environment before).state) at emitted
  rw [actual,Outcome.state] at emitted
  obtain ⟨segment⟩ := emitted
  have finalHistory := history.trans segment
  exact ⟨value,after,actual,⟨context,depthHeap⟩,retained,output,⟨segment⟩,⟨finalHistory⟩,
    mu entry body depth ordinary environment before semantic available replacements value after actual
      after finalHistory (grows_refl after)⟩

end MicroCFTA.SourceCurrentStoredMuRowOrigins
