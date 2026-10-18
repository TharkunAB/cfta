import MicroCFTA.SourceCurrentStoredLiteralRowLineage
import MicroCFTA.SourceCurrentNativeConstructReaderReadback

/-!
# Original stored rows of actual native smart construction

A selected ordinary return retains an original body row and its full fields.
Rebuilt children retain their actual ordered stored calls.
-/
namespace MicroCFTA.SourceCurrentNativeConstructSourceRows
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Outcome)
open InternedStoredSubstitution (leaves encode Replacements)
open InternedStoredSubstitutionRebind (replacement)
open InternedBinderProtocol (Reference)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceCurrentNativeMuPublication (History)
open SourceCurrentStoredSubstitutionCalls (Calls)
open SourceCurrentStoredLiteralRowLineage (RowAt)

/-- Actual smart construction retains an original indexed body row and its ordered child calls. -/
theorem construct [DecidableEq (EdgeKey Symbol Guard)] (old : Reference) (body : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticHeap before) (available : Available before body)
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (actual : SourceRecursiveIntersectionMaybeMu.construct old body before = .done value after)
    (reader : State Symbol Guard) (history : History empty reader) (growth : Grows after reader)
    (index : Nat) (row : EdgeValue Symbol Guard) (selected : (nodeEdges value)[index]? = some row) :
    ∃ original, RowAt body original ∧ row.entry.key.symbol = original.entry.key.symbol ∧
      row.entry.key.constraint = original.entry.key.constraint ∧ row.children.length = original.children.length ∧
      (row = original ∨ ∃ lexical current next, Calls lexical original.children current row.children next) := by
  obtain ⟨depth,afterDepth,ordinary,cut,raw,middle,_entry,_storedBody,depthDone,_ordinaryDone,_requestDone,
    rawDone,filtered,normal,rawAvailable,rawGrowth,_rawIssued,_present,_readerCell,_returned,_correct,
    _unused,_sameBody,_selfAbsent,_bodyRow,erased,_origins,_positive⟩ :=
    SourceCurrentNativeConstructReaderReadback.construct_row old body before semantic available value after actual
      reader history growth index row selected
  have context : Context before (leaves body) :=
    ⟨SourceRecursiveIntersectionSemanticHeap.context before semantic (leaves body)
      (InternedStoredSubstitution.leaves_available body before available),semantic.2⟩
  have callbacks : SourceRecursiveIntersectionMaybeMu.callback old body =
      InternedFreshOrdinaryFacts.callback (encode (leaves body) [old] body) (leaves body) := by
    funext name state
    exact SourceRecursiveIntersectionMaybeMu.callback_eq old body name before state semantic.1.normal.facts available
  have depthActual : InternedFreshOrdinaryFacts.callback (encode (leaves body) [old] body)
      (leaves body) .depth before = .done depth afterDepth := by
    simpa only [callbacks] using depthDone
  have depthContext : Context afterDepth (leaves body) := by
    simpa only [depthActual,Outcome.state] using context.callback (encode (leaves body) [old] body)
      .depth (InternedNestedProvenance.depth_available before)
  have depthChecked := InternedFreshOrdinaryFacts.callback_verified (encode (leaves body) [old] body)
    (leaves body) .depth before context.base.normal.facts
    (context.local .depth (InternedNestedProvenance.depth_available before)).base.inputs
  have depthGrowth : Grows before afterDepth := by
    simpa only [depthActual,Outcome.state] using depthChecked.growth
  have depthIssued : Extends before.nodes.issued afterDepth.nodes.issued := by
    simpa only [depthActual,Outcome.state] using depthChecked.history
  have laterSemantic : SemanticHeap afterDepth :=
    ⟨⟨depthContext.base.normal,(by intro child member; cases member),depthContext.base.profiles,
      depthContext.base.freeNames⟩,depthContext.depth⟩
  have laterAvailable := available.grows before afterDepth depthGrowth depthIssued
  let name := InternedBinderProtocol.Reference.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)
  have replacements : Replacements afterDepth (replacement old (.reference name)) := by
    intro chosen output found
    by_cases same : chosen = old
    · have equal : .reference name = output := by simpa only [replacement,same,ite_true,Option.some.injEq] using found
      rw [← equal]
      exact InternedNestedProvenance.ordinary_available afterDepth _
    · simp only [replacement,same,ite_false] at found
      cases found
  have literal : SourceCurrentLiteralRootParts.Row value row := by
    cases value with
    | node => exact .node (List.mem_of_getElem? selected)
    | empty | reference | union | mu => simp only [nodeEdges,List.getElem?_nil] at selected; cases selected
  have preserved := SourceCurrentPublicationFilterSource.filtered_row middle normal name raw rawAvailable row
  rw [filtered] at preserved
  have rawRow := preserved.mp (erased ▸ literal)
  have origin := SourceCurrentStoredLiteralRowLineage.execute_row body (replacement old (.reference name))
    afterDepth laterSemantic laterAvailable replacements raw middle rawDone reader history
    (grows_trans rawGrowth growth) row rawRow
  apply SourceCurrentStoredLiteralRowLineage.source_row origin
  intro chosen output found part
  by_cases same : chosen = old
  · have equal : .reference name = output := by simpa only [replacement,same,ite_true,Option.some.injEq] using found
    rw [← equal] at part
    cases part
  · simp only [replacement,same,ite_false] at found
    cases found

end MicroCFTA.SourceCurrentNativeConstructSourceRows
