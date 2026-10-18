import MicroCFTA.SourceCurrentStoredSubstitutionOrigins
import MicroCFTA.SourceCurrentNativeQueryRowOrigins
import MicroCFTA.MergedFreshOrdinaryExposureOrigins
import MicroCFTA.MergedFreshOrdinaryGraphOrigins
import MicroCFTA.SourceEqualityRequiredHead

/-!
# Actual recursive Head rows and stored-body reconstruction

Initial ready inputs construct the complete Head and its first stored Mu
unfolding. Every selected Head row has an origin in that literal returned
record at the final reader. Node and union stored bodies derive their own
ordered reconstruction receipts. Nested Mu bodies remain explicit.
-/
namespace MicroCFTA.SourceCurrentRecursiveHeadRowOrigins
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Outcome)
open InternedNestedProvenance (Values)
open InternedStoredSubstitution (Environment Replacements leaves)
open InternedFreshOrdinaryStoredSubstitution (execute unfold)
open SourceCurrentStoredSubstitutionOrigins (NodeRows UnionRows)
open SourceEqualityRequiredCache (Ready Keeps Ordinary)
open SourceEqualityRequiredHead (Head)
open MergedFreshOrdinaryGraph (Origin)
open InternedBinderProtocol (NodeKey Reference)

/-- Source node and union bodies retain closed identity or their actual open row calls. -/
def BodyRows [DecidableEq (EdgeKey Symbol Guard)] (body : Value Symbol Guard)
    (environment : Environment Symbol Guard) (before : State Symbol Guard)
    (value : Value Symbol Guard) (after : State Symbol Guard) : Prop :=
  match body with
  | .node entry rows level free =>
      (free = [] ∧ value = .node entry rows level free ∧ after = before) ∨
      (free.isEmpty = false ∧ NodeRows (leaves body) environment rows before value after)
  | .union entry members level free =>
      (free = [] ∧ value = .union entry members level free ∧ after = before) ∨
      (free.isEmpty = false ∧ UnionRows environment members before value after)
  | .empty | .reference .. | .mu .. => True

/-- The actual Mu executor replaces only this stored record's original own name. -/
def selfEnvironment (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) : Environment Symbol Guard :=
  fun name => if name = .interned entry.identity then some (.mu entry body depth ordinary) else none

private theorem body_rows [DecidableEq (EdgeKey Symbol Guard)] (body : Value Symbol Guard)
    (environment : Environment Symbol Guard) (before : State Symbol Guard) (ready : Ready before)
    (available : Available before body) (replacements : Replacements before environment)
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (actual : execute body environment before = .done value after) : BodyRows body environment before value after := by
  cases body with
  | empty | reference | mu => trivial
  | node entry rows level free =>
      obtain ⟨result,final,done,_,_,_,_,description⟩ := SourceCurrentStoredSubstitutionOrigins.node_complete
        entry rows level free environment before ready.semantic ready.covered available replacements
      obtain ⟨rfl,rfl⟩ := Outcome.done.inj (done.symm.trans actual)
      exact description
  | union entry members level free =>
      obtain ⟨result,final,done,_,_,_,_,description⟩ := SourceCurrentStoredSubstitutionOrigins.union_complete
        entry members level free environment before ready.semantic ready.covered available replacements
      obtain ⟨rfl,rfl⟩ := Outcome.done.inj (done.symm.trans actual)
      exact description

private theorem first_growth [DecidableEq (EdgeKey Symbol Guard)]
    (entry : Interned NodeKey) (body depth ordinary result : Value Symbol Guard)
    (before middle : State Symbol Guard) (valid : Valid before)
    (actual : unfold (.mu entry body depth ordinary) before = .done result middle)
    (fuel : Nat) (rows : List (EdgeValue Symbol Guard)) (cut : State Symbol Guard)
    (read : MergedFreshOrdinaryExposure.nodeEdges fuel (.mu entry body depth ordinary) before = .done rows cut) :
    Grows middle cut := by
  have checked := unfold_correct (.mu entry body depth ordinary) before valid
  have middleValid : Valid middle := by simpa only [actual,Outcome.state] using checked.1
  cases result with
  | node own edges level free =>
      have same : middle = cut := by
        simpa only [MergedFreshOrdinaryExposure.nodeEdges,actual,MergedSourceExposure.Result.done.injEq] using
          (show _ = _ from read) |>.2
      subst cut
      exact grows_refl _
  | empty | reference | union | mu =>
      have growth := (MergedFreshOrdinaryColdReplay.collect_correct fuel middle middleValid [] [.mu entry body depth ordinary]).2
      have atCut := read
      simp only [MergedFreshOrdinaryExposure.nodeEdges,actual] at atCut
      have same : (MergedFreshOrdinaryExposure.collect fuel middle [] [.mu entry body depth ordinary]).state = cut := by
        rw [← MergedPreparedReaderEffects.canonical_state]
        rw [atCut]
        rfl
      rw [same] at growth
      exact growth

/-- A selected Mu Head retains its actual first body call and every row's final-reader origin. -/
def MuRows [DecidableEq (EdgeKey Symbol Guard)] (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) (before : State Symbol Guard)
    (unfolded : Value Symbol Guard) (middle : State Symbol Guard)
    (result : Value Symbol Guard) (after : State Symbol Guard) : Prop :=
  execute body (selfEnvironment entry body depth ordinary) before = .done unfolded middle ∧
    BodyRows body (selfEnvironment entry body depth ordinary) before unfolded middle ∧
    Grows middle after ∧
    unfold (.mu entry body depth ordinary) after = .done unfolded after ∧
    ∀ index row, (nodeEdges result)[index]? = some row → Origin after [unfolded] row

/-- All Head branches retain their literal row sources; nested Mu reconstruction is explicit. -/
def HeadRows [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (before : State Symbol Guard) (result : Value Symbol Guard) (after : State Symbol Guard) : Prop :=
  match value with
  | .mu entry body depth ordinary => ∃ unfolded middle, MuRows entry body depth ordinary before unfolded middle result after
  | .union _ members _ _ =>
      ∀ index row, (nodeEdges result)[index]? = some row →
        ∃ memberIndex member, members[memberIndex]? = some member ∧ Origin after [member] row
  | .node _ rows _ _ => ∀ index row, (nodeEdges result)[index]? = some row → ∃ sourceIndex, rows[sourceIndex]? = some row
  | .empty | .reference .. => nodeEdges result = []

/-- Initial ready closed data constructs its Head, source row indices, and actual Mu reconstruction. -/
theorem complete [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (before : State Symbol Guard) (ready : Ready before) (available : Available before value)
    (closed : value.free = []) :
    ∃ result after, Head value before result after ∧ Keeps before after ∧ Available after result ∧
      result.free = [] ∧ Ordinary result ∧ HeadRows value before result after := by
  obtain ⟨fuel,rows,cut,read,semantic,covered,depth,growth,issued,resident,closedRows,_⟩ :=
    MergedFreshOrdinaryColdTermination.read_closed value before ready.semantic ready.covered ready.depth available closed
  let made := run (makeNode rows) cut
  have first : Keeps before cut := ⟨⟨semantic,covered,depth⟩,growth,issued⟩
  have last := SourceEqualityRequiredCache.node rows cut first.ready resident closedRows
  have rowsSelected : ∀ index row, (nodeEdges made.1)[index]? = some row → row ∈ rows := by
    intro index row selected
    have normalized := EqualityLeafProjectionPhysical.makeNode_edges rows cut semantic.1.normal.facts.coherent
      semantic.1.normal.facts.linked resident
    change (nodeEdges (run (makeNode rows) cut).1)[index]? = some row at selected
    rw [normalized] at selected
    exact (List.mem_filter.mp (canonicalEdges_member _ row (List.mem_of_getElem? selected))).1
  have origins : ∀ index row, (nodeEdges made.1)[index]? = some row → Origin made.2 [value] row := by
    intro index row selected
    exact MergedFreshOrdinaryExposureOrigins.nodeEdges_origins fuel value before ready.semantic ready.covered available
      rows cut read made.2 last.1.growth row (rowsSelected index row selected)
  refine ⟨made.1,made.2,.read fuel rows cut read rfl,first.trans last.1,last.2.1,last.2.2.1,last.2.2.2,?_⟩
  cases value with
  | node entry originals level free =>
      cases read
      intro index row selected
      exact List.mem_iff_getElem?.mp (rowsSelected index row selected)
  | empty | reference =>
      cases read
      rfl
  | union entry members level free =>
      intro index row selected
      have memberOrigin := (MergedFreshOrdinaryGraph.origin_union made.2 entry members level free row).mp
        (origins index row selected)
      obtain ⟨member,present,origin⟩ := memberOrigin
      obtain ⟨memberIndex,found⟩ := List.mem_iff_getElem?.mp present
      exact ⟨memberIndex,member,found,origin⟩
  | mu entry body depth ordinary =>
      obtain ⟨unfolded,middle,actual,_,_,_,_,_,_⟩ := unfold_complete_decoded (.mu entry body depth ordinary)
        before ready.semantic.1 available ready.semantic.2 ready.covered
      have replacements : Replacements before (selfEnvironment entry body depth ordinary) := by
        intro name replacement found
        dsimp only [selfEnvironment] at found
        split at found
        · cases found; exact available
        · cases found
      have bodyAvailable : Available before body := available.children body (by simp [children])
      have description := body_rows body (selfEnvironment entry body depth ordinary) before ready bodyAvailable replacements
        unfolded middle actual
      have firstGrows := first_growth entry body depth ordinary unfolded before middle
        ready.semantic.1.normal.facts.coherent.valid actual fuel rows cut read
      have totalGrowth := grows_trans firstGrows last.1.growth
      have replay := unfold_replay (.mu entry body depth ordinary) before made.2 unfolded middle
        ready.semantic.1.normal.facts.coherent.valid actual totalGrowth
      refine ⟨unfolded,middle,actual,description,totalGrowth,replay,?_⟩
      intro index row selected
      exact (MergedFreshOrdinaryGraph.origin_unfold made.2 entry body depth ordinary unfolded made.2 replay row).mp
        (origins index row selected)

end MicroCFTA.SourceCurrentRecursiveHeadRowOrigins
