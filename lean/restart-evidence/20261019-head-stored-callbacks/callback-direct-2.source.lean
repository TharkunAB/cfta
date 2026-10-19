import MicroCFTA.SourceCurrentHeadIssuedHistory
import MicroCFTA.SourceCurrentLiteralFilterParts

/-!
# Structural child contexts at the actual stored callback

Self filtering retains structural rows, including rows beneath opaque Mu
atoms. A selected stored writer then supplies its actual raw source build
and lexical context at the final Head reader. The raw callback can contain
captured values. No original syntax ancestry or global size bound is inferred.
-/
namespace MicroCFTA.SourceCurrentStoredCallbackChildContexts
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedFreshOrdinaryConstruction (build)
open InternedNestedConstruction (Outcome)
open InternedBinderProtocol (NodeKey Reference)
open SourceCurrentLiteralRootParts (Literal Row)
open SourceCurrentStoredLiteralRowLineage (RowAt)
open SourceCurrentStoredMuUnfoldChildContexts (Child)
open SourceCurrentNativeMuPublication (Publication)
open SourceCurrentNativeMuIssuedWriters (Written)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentConstrainedCapSourceHistory (Context)

private theorem literal_row {value : Value Symbol Guard} {row : EdgeValue Symbol Guard}
    (part : Row value row) : RowAt value row := by
  induction part with
  | node member =>
      obtain ⟨index,found⟩ := List.mem_iff_getElem?.mp member
      exact .node (index := index) found
  | union member _ ih =>
      obtain ⟨index,found⟩ := List.mem_iff_getElem?.mp member
      exact .union (index := index) found ih

private theorem atom_row {value root : Value Symbol Guard}
    {row : EdgeValue Symbol Guard} (atom : Literal value root)
    (part : RowAt root row) : RowAt value row := by
  induction atom with
  | reference | mu => exact part
  | union member _ ih =>
      obtain ⟨index,found⟩ := List.mem_iff_getElem?.mp member
      exact .union (index := index) found ih

private theorem row_parts {value : Value Symbol Guard} {row : EdgeValue Symbol Guard}
    (part : RowAt value row) : Row value row ∨
      ∃ entry body depth ordinary, Literal value (.mu entry body depth ordinary) ∧ RowAt body row := by
  induction part with
  | node found => exact .inl (.node (List.mem_of_getElem? found))
  | union found _ ih =>
      rcases ih with literal | ⟨entry,body,depth,ordinary,atom,inside⟩
      · exact .inl (.union (List.mem_of_getElem? found) literal)
      · exact .inr ⟨entry,body,depth,ordinary,.union (List.mem_of_getElem? found) atom,inside⟩
  | mu part => exact .inr ⟨_,_,_,_,.mu _ _ _ _,part⟩

/-- Actual self filtering preserves each structural row, including rows beneath stored Mu bodies. -/
theorem filter_row [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (normal : InternedStoredMuOrigins.Normal state) (own : Reference) (raw : Value Symbol Guard)
    (available : Available state raw) (row : EdgeValue Symbol Guard) :
    RowAt (run (withoutSelfReference own raw) state).1 row ↔ RowAt raw row := by
  have rows := SourceCurrentLiteralFilterParts.row state normal own raw available row
  have atoms (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) :
      Literal (run (withoutSelfReference own raw) state).1 (.mu entry body depth ordinary) ↔
        Literal raw (.mu entry body depth ordinary) := by
    rw [SourceCurrentLiteralFilterParts.literal state normal own raw available]
    exact and_iff_left (.inr (by intro impossible; cases impossible))
  constructor
  · intro part
    rcases row_parts part with literal | ⟨entry,body,depth,ordinary,atom,inside⟩
    · exact literal_row (rows.mp literal)
    · exact atom_row ((atoms entry body depth ordinary).mp atom) (.mu inside)
  · intro part
    rcases row_parts part with literal | ⟨entry,body,depth,ordinary,atom,inside⟩
    · exact literal_row (rows.mpr literal)
    · exact atom_row ((atoms entry body depth ordinary).mpr atom) (.mu inside)

/-- A filtered child keeps its exact original row, index and call in the raw callback value. -/
theorem filter_child [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (normal : InternedStoredMuOrigins.Normal state) (own : Reference) (raw : Value Symbol Guard)
    (available : Available state raw) {before after : State Symbol Guard}
    {row : EdgeValue Symbol Guard} {index : Nat} {child : Value Symbol Guard}
    (part : Child (run (withoutSelfReference own raw) state).1 before after row index child) :
    Child raw before after row index child := by
  obtain ⟨original,origin,symbol,guard,arity,originalChild,selected,_smaller,calls⟩ := part
  have origin := (filter_row state normal own raw available original).mp origin
  exact ⟨original,origin,symbol,guard,arity,originalChild,selected,
    origin.child_smaller originalChild (List.mem_of_getElem? selected),calls⟩

/-- The selected writer supplies its actual raw callback and the same supported indexed child. -/
theorem written_child [DecidableEq (EdgeKey Symbol Guard)]
    {reader before after : State Symbol Guard} {key : NodeKey} {entry : Interned NodeKey}
    {body depth ordinary : Value Symbol Guard} {row : EdgeValue Symbol Guard} {index : Nat}
    {child : Value Symbol Guard} (written : Written empty reader key (.mu entry body depth ordinary))
    (ready : Ready reader) (part : Child body before after row index child) :
    ∃ (event : Publication (Symbol := Symbol) (Guard := Guard))
        (raw : Value Symbol Guard) (bodyHeap : State Symbol Guard),
      key = event.key ∧ entry = event.entry ∧ body = event.body ∧ depth = event.depth ∧ ordinary = event.ordinary ∧
      build event.expression (.reference (.interned event.entry.identity) :: event.environment)
        event.allocated = .done raw bodyHeap ∧
      run (withoutSelfReference (.interned event.entry.identity) raw) bodyHeap = (event.body,event.afterBody) ∧
      Context reader (.reference (.interned event.entry.identity) :: event.environment) ∧
      Keeps bodyHeap reader ∧ Available reader raw ∧
      build event.expression (.reference (.interned event.entry.identity) :: event.environment)
        reader = .done raw reader ∧
      run (withoutSelfReference (.interned event.entry.identity) raw) reader = (event.body,reader) ∧
      Child raw before after row index child := by
  obtain ⟨event,keySame,valueSame,_rawOrdinary,_ordinaryHeap,raw,bodyHeap,
    _ordinaryBuild,_ordinaryFilter,bodyBuild,bodyFilter,_ordinaryContext,bodyContext,
    _ordinaryKept,bodyKept,_ordinaryAvailable,rawAvailable,_ordinaryWarm,_ordinaryFilterWarm,bodyWarm,filterWarm⟩ :=
    written.raw_contexts ready
  change Value.mu entry body depth ordinary = Value.mu event.entry event.body event.depth event.ordinary at valueSame
  obtain ⟨entrySame,bodySame,depthSame,ordinarySame⟩ := Value.mu.inj valueSame
  have filtered : Child (run (withoutSelfReference (.interned event.entry.identity) raw) reader).1
      before after row index child := by simpa only [filterWarm,←bodySame] using part
  have rawPart := filter_child reader ready.semantic.1.normal (.interned event.entry.identity) raw rawAvailable filtered
  exact ⟨event,raw,bodyHeap,keySame,entrySame,bodySame,depthSame,ordinarySame,
    bodyBuild,bodyFilter,bodyContext,bodyKept,rawAvailable,bodyWarm,filterWarm,rawPart⟩

/-- An actual selected Head child retains its stored writer's raw source callback at the final reader. -/
theorem head_child [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : InternedFreshOrdinaryCostHeap.Heap before)
    (available : Available before value) (closed : value.free = []) (result : Value Symbol Guard)
    (after : State Symbol Guard) (actual : SourceEqualityRequiredHead.Head value before result after)
    (initial : SourceCurrentNativeMuIssuedHistory.Path empty before) (position : Nat) (row : EdgeValue Symbol Guard)
    (selected : (InternedEdgeResidency.nodeEdges result)[position]? = some row)
    (index : Nat) (child : Value Symbol Guard) (childSelected : row.children[index]? = some child) :
    Row value row ∨
      ∃ (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
          (first second : State Symbol Guard) (returned : Value Symbol Guard)
          (terminal : State Symbol Guard) (terminalValue : Value Symbol Guard),
        SourceCurrentRecursiveHeadChainRows.Chain before value first (.mu entry body depth ordinary) ∧
        InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) first = .done returned second ∧
        SourceCurrentRecursiveHeadMuChildContexts.Suffix second returned terminal terminalValue ∧ Keeps terminal after ∧
        Row returned row ∧ Written empty after entry.key (.mu entry body depth ordinary) ∧
        Child body first second row index child ∧
        ∃ (event : Publication (Symbol := Symbol) (Guard := Guard))
            (raw : Value Symbol Guard) (bodyHeap : State Symbol Guard),
          entry.key = event.key ∧ entry = event.entry ∧ body = event.body ∧ depth = event.depth ∧ ordinary = event.ordinary ∧
          build event.expression (.reference (.interned event.entry.identity) :: event.environment)
            event.allocated = .done raw bodyHeap ∧
          run (withoutSelfReference (.interned event.entry.identity) raw) bodyHeap = (event.body,event.afterBody) ∧
          Context after (.reference (.interned event.entry.identity) :: event.environment) ∧
          Keeps bodyHeap after ∧ Available after raw ∧
          build event.expression (.reference (.interned event.entry.identity) :: event.environment)
            after = .done raw after ∧
          run (withoutSelfReference (.interned event.entry.identity) raw) after = (event.body,after) ∧
          Child raw first second row index child := by
  have lineage := SourceCurrentHeadIssuedHistory.head_child value before semantic costs available closed result after
    actual initial position row selected index child childSelected
  rcases lineage with literal | ⟨entry,body,depth,ordinary,first,second,returned,terminal,terminalValue,
    earlierBranch,called,suffix,last,literal,writer,part⟩
  · exact .inl literal
  · have ready := (SourceEqualityProjectionCosts.head_effects actual semantic costs available).2.1.ready
    exact .inr ⟨entry,body,depth,ordinary,first,second,returned,terminal,terminalValue,
      earlierBranch,called,suffix,last,literal,writer,part,written_child writer ready part⟩

end MicroCFTA.SourceCurrentStoredCallbackChildContexts
