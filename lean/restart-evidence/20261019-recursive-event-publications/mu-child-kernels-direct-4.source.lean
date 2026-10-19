import MicroCFTA.SourceCurrentStoredMuUnfoldChildContexts
import MicroCFTA.SourceCurrentRequiredPublicationHistory

set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.StoredMuUnfoldChildKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryStoredSubstitution (execute unfold)
open SourceEqualityRequiredCache (Ready)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceCurrentNativeMuPublication (History Written)
open SourceCurrentStoredLiteralRowLineage (RowAt)
open SourceCurrentStoredMuUnfoldChildContexts (Child)
local notation "Node" => Value Nat Bool
local notation "Row" => EdgeValue Nat Bool
local notation "Heap" => State Nat Bool

private def expression : Syntax Nat Bool :=
  .binder false (.node [.mk 7 false [.binder false (.node [.mk 8 false [.var 1,.var 0]])]])
private def constructed := build expression [] empty
private def value : Node := match constructed with | .done result _ => result | .pending .. => .empty
private def before : Heap := constructed.state
private def entry := match value with | .mu entry _ _ _ => entry | _ => (Cache.intern (empty : Heap).nodes .empty).1
private def body : Node := match value with | .mu _ body _ _ => body | _ => .empty
private def depth : Node := match value with | .mu _ _ depth _ => depth | _ => .empty
private def ordinary : Node := match value with | .mu _ _ _ ordinary => ordinary | _ => .empty
private def exposed := unfold value before
private def output : Node := match exposed with | .done result _ => result | .pending .. => .empty
private def after : Heap := exposed.state
private def row : Row := (nodeEdges output)[0]?.getD (run (makeEdge 0 false []) before).1
private def sourceRow : Row := (nodeEdges body)[0]?.getD row
private def child : Node := row.children[0]?.getD .empty
private def sourceChild : Node := sourceRow.children[0]?.getD .empty
private def bodyEntry := match body with | .node entry _ _ _ => entry | _ => entry
private def outputEntry := match output with | .node entry _ _ _ => entry | _ => entry
private noncomputable def mass (value : Node) : Nat :=
  @sizeOf Node (@Value._sizeOf_inst Nat Bool (instSizeOfDefault Nat) (instSizeOfDefault Bool)) value

private theorem built : constructed = .done value before := by cbv
private theorem shape : value = .mu entry body depth ordinary := by cbv
private theorem done : exposed = .done output after := by cbv
private theorem selected : (nodeEdges output)[0]? = some row ∧ row.children[0]? = some child := by cbv
private theorem source_selected : sourceRow.children[0]? = some sourceChild := by cbv
private theorem body_node : body = .node bodyEntry [sourceRow] body.depth body.free := by cbv
private theorem output_node : output = .node outputEntry [row] output.depth output.free := by cbv
private theorem used : InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true ∧
    (match sourceChild with | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true | _ => False) ∧
    (match child with | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true | _ => False) := by cbv
private theorem changed : child ≠ sourceChild := by
  intro same
  have refs := congrArg Value.referenceOf same
  cbv at refs
  cases refs

private theorem unique_row (original : Row) (origin : RowAt body original) : original = sourceRow := by
  rw [body_node] at origin
  cases origin with
  | node found =>
      have member := List.mem_of_getElem? found
      simpa only [List.mem_singleton] using member

private theorem ready : Ready before := SourceEqualityRequiredCache.constructed expression value before built
private theorem available : Available before value :=
  (InternedFreshOrdinaryFacts.closed_verified expression).result value before built
private noncomputable def initial_history : History empty before :=
  SourceCurrentNativeMuPublication.closed_history expression

private theorem checked_witness :
    constructed = .done value before ∧ value = .mu entry body depth ordinary ∧
    SemanticHeap before ∧ Available before value ∧
    exposed = .done output after ∧ (nodeEdges output)[0]? = some row ∧
    row.children[0]? = some child ∧ sourceRow.children[0]? = some sourceChild ∧
    InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true ∧
    (match sourceChild with | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true | _ => False) ∧
    (match child with | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true | _ => False) ∧
    child ≠ sourceChild ∧ Nonempty (History empty after) ∧ Written empty entry.key value ∧
    Child body before after row 0 child ∧
    ∃ lexical current next,
      SemanticHeap current ∧ Available current sourceChild ∧
      InternedStoredSubstitution.Replacements current lexical ∧
      execute sourceChild lexical current = .done child next ∧
      Grows before current ∧ Extends before.nodes.issued current.nodes.issued ∧
      Grows next after ∧ Extends next.nodes.issued after.nodes.issued ∧
      mass sourceChild < mass body := by
  have actual : unfold value before = .done output after := done
  obtain ⟨interval⟩ := SourceCurrentRequiredPublicationHistory.unfold value before ready available
  have interval : History before after := by simpa only [actual,InternedNestedConstruction.Outcome.state] using interval
  have history : History empty after := .trans initial_history interval
  have muAvailable : Available before (.mu entry body depth ordinary) := shape ▸ available
  have muActual : unfold (.mu entry body depth ordinary) before = .done output after := by
    rw [←shape]
    exact actual
  have literal : SourceCurrentLiteralRootParts.Row output row := by
    rw [output_node]
    exact .node (by simp)
  obtain ⟨writer,anchored⟩ := SourceCurrentStoredMuUnfoldChildContexts.unfold_child entry body depth ordinary
    before ready.semantic muAvailable output after muActual after history (grows_refl _) row literal 0 child selected.2
  have support : ∃ lexical current next,
      SemanticHeap current ∧ Available current sourceChild ∧
      InternedStoredSubstitution.Replacements current lexical ∧
      execute sourceChild lexical current = .done child next ∧
      Grows before current ∧ Extends before.nodes.issued current.nodes.issued ∧
      Grows next after ∧ Extends next.nodes.issued after.nodes.issued ∧
      mass sourceChild < mass body := by
    obtain ⟨original,origin,_symbol,_guard,_arity,originalChild,found,smaller,calls⟩ := anchored
    have sameRow := unique_row original origin
    subst original
    have sameChild : originalChild = sourceChild := Option.some.inj (found.symm.trans source_selected)
    subst originalChild
    rcases calls with same | ⟨lexical,current,next,semantic,resident,replacements,called,earlier,earlierIssued,later,laterIssued⟩
    · exact (changed same).elim
    · exact ⟨lexical,current,next,semantic,resident,replacements,called,earlier,earlierIssued,later,laterIssued,smaller⟩
  exact ⟨built,shape,ready.semantic,available,done,selected.1,selected.2,source_selected,used.1,used.2.1,used.2.2,
    changed,⟨history⟩,by simpa only [←shape] using writer,anchored,support⟩

/-- Actual nested used-Mu unfolding changes its child and derives the supported nonidentity child call. -/
theorem nested_used_child :
    constructed = .done value before ∧ value = .mu entry body depth ordinary ∧
    SemanticHeap before ∧ Available before value ∧
    exposed = .done output after ∧ (nodeEdges output)[0]? = some row ∧
    row.children[0]? = some child ∧ sourceRow.children[0]? = some sourceChild ∧
    InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true ∧
    (match sourceChild with | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true | _ => False) ∧
    (match child with | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true | _ => False) ∧
    child ≠ sourceChild ∧ Nonempty (History empty after) ∧ Written empty entry.key value ∧
    Child body before after row 0 child ∧
    ∃ lexical current next,
      SemanticHeap current ∧ Available current sourceChild ∧
      InternedStoredSubstitution.Replacements current lexical ∧
      execute sourceChild lexical current = .done child next ∧
      Grows before current ∧ Extends before.nodes.issued current.nodes.issued ∧
      Grows next after ∧ Extends next.nodes.issued after.nodes.issued ∧
      mass sourceChild < mass body := checked_witness

end MicroCFTA.StoredMuUnfoldChildKernels
