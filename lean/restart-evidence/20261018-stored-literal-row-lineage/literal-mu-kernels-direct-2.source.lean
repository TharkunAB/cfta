import MicroCFTA.SourceCurrentStoredMuLexicalInputs
import MicroCFTA.SourceCurrentStoredMuLiteralRows

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace MicroCFTA.LiteralMuKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency InternedRecordCoherence
open InternedNestedConstruction (Syntax Outcome)
open InternedStoredSubstitution (Environment Replacements)
open InternedFreshOrdinaryStoredSubstitution (execute)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceCurrentNativeMuPublication (History)
open InternedBinderProtocol (Reference NodeKey)
local notation "Heap" => State Nat Unit

private def external : Reference := .intersection 0 1
private def other : Reference := .intersection 2 3
private def captures : List (Value Nat Unit) := [.reference external,.reference other]
private def inner : Syntax Nat Unit := .binder true (.node [.mk 9 () [.var 0,.var 2]])
private def expression : Syntax Nat Unit := .binder true (.union [
  .node [.mk 8 () [.var 0,.var 1,inner]], .node [.mk 7 () []], .var 2])
private def source := InternedFreshOrdinaryConstruction.build expression captures (empty : Heap)
private def original : Value Nat Unit := match source with
  | .done value _ => value
  | .pending _ _ => .empty
private def before : Heap := source.state
private def entry : Interned NodeKey := match original with
  | .mu entry _ _ _ => entry
  | _ => ⟨0,.empty⟩
private def body : Value Nat Unit := match original with
  | .mu _ body _ _ => body
  | _ => .empty
private def depth : Value Nat Unit := match original with
  | .mu _ _ depth _ => depth
  | _ => .empty
private def ordinary : Value Nat Unit := match original with
  | .mu _ _ _ ordinary => ordinary
  | _ => .empty
private def environment : Environment Nat Unit :=
  fun name => if name = external then some .empty else none
private def substituted := execute original environment before
private def result : Value Nat Unit := match substituted with
  | .done value _ => value
  | .pending _ _ => .empty
private def after : Heap := substituted.state
private def member : Value Nat Unit := (unionMembers result)[0]?.getD .empty
private def row : EdgeValue Nat Unit := (nodeEdges member)[0]?.getD (run (makeEdge 7 () []) (empty : Heap)).1
private def isMu : Value Nat Unit → Bool
  | .mu .. => true
  | _ => false
private def nested : Bool := (unionMembers body).any fun value =>
  (nodeEdges value).any fun edge => edge.children.any fun child => isMu child && !child.free.isEmpty

private theorem source_done : source = .done original before := by cbv
private theorem stored_mu : original = .mu entry body depth ordinary := by cbv
private theorem open_original : external ∈ original.free := by cbv; exact List.mem_cons_self
private theorem nested_body : nested = true := by cbv
private theorem substitute_done : substituted = .done result after := by cbv
private theorem selected_member : (unionMembers result)[0]? = some member := by cbv
private theorem selected_row : (nodeEdges member)[0]? = some row := by cbv
private theorem no_physical_row : nodeEdges result = [] := by cbv
private theorem physical_row (value : Value Nat Unit) (index : Nat) (selected : (nodeEdges value)[index]? = some row) :
    SourceCurrentLiteralRootParts.Row value row := by
  cases value with
  | node entry rows level free => exact .node (List.mem_of_getElem? selected)
  | empty | reference | union | mu => simp only [nodeEdges,List.getElem?_nil] at selected; cases selected
private theorem literal_row : SourceCurrentLiteralRootParts.Row result row := by
  have shape : ∃ entry level free, result = .union entry (unionMembers result) level free := by
    cbv
    exact ⟨_,_,_,rfl⟩
  obtain ⟨entry,level,free,shape⟩ := shape
  rw [shape]
  exact .union (List.mem_of_getElem? selected_member) (physical_row member 0 selected_row)
private theorem row_fields : row.entry.key.symbol = 7 ∧ row.entry.key.constraint = () ∧ row.children = [] := by
  constructor
  · cbv
  · exact ⟨rfl,by cbv⟩

private theorem initial_context : SourceCurrentConstrainedCapSourceHistory.Context (empty : Heap) captures := by
  refine ⟨SourceRecursiveIntersectionSemanticHeap.context empty SourceRecursiveIntersectionSemanticHeap.empty_heap
    captures ?_,InternedFreshOrdinaryDepthHeap.empty_heap⟩
  intro child member
  simp only [captures,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  all_goals
    apply reference_available
    intro identity impossible
    simp only [external,other,Value.free,List.mem_singleton] at impossible
    cases impossible

private theorem initial_semantic : SemanticHeap before := by
  have context := initial_context.build expression
  refine ⟨⟨context.base.normal,?_,context.base.profiles,context.base.freeNames⟩,context.depth⟩
  intro child member
  cases member

private theorem initial_covered : Covered [] before :=
  InternedFreshOrdinaryCoverage.build_covered expression captures empty empty_valid empty_correct.2
    original before source_done

private theorem original_available : Available before original :=
  (InternedFreshOrdinaryFacts.build_verified expression captures empty
    initial_context.base.normal.facts initial_context.base.inputs).result original before source_done

private theorem initial_replacements : Replacements before environment := by
  intro name value found
  dsimp only [environment] at found
  split at found
  · cases found
    exact empty_available before
  · cases found

private noncomputable def initial_history : History (empty : Heap) before :=
  Classical.choice (SourceCurrentNativeMuPublication.build_history expression captures empty initial_context)


/-- The mixed union return retains an actual original-body row call and both intermediate growth histories. -/
private theorem checked :
    source = .done original before ∧ original = .mu entry body depth ordinary ∧
    external ∈ original.free ∧ nested = true ∧ SemanticHeap before ∧ Covered [] before ∧
    Available before original ∧ Replacements before environment ∧ Nonempty (History (empty : Heap) before) ∧
    execute original environment before = .done result after ∧ Nonempty (History (empty : Heap) after) ∧
    nodeEdges result = [] ∧ SourceCurrentLiteralRootParts.Row result row ∧
    row.entry.key.symbol = 7 ∧ row.entry.key.constraint = () ∧ row.children = [] ∧
    ∃ currentDepth afterDepth raw middle,
      InternedFreshOrdinaryFacts.callback
        (InternedStoredSubstitution.encode (InternedStoredSubstitution.leaves original) [.interned entry.identity] body)
        ((InternedStoredSubstitution.leaves original).map (InternedStoredSubstitution.input environment))
        .depth before = .done currentDepth afterDepth ∧
      execute body (SourceCurrentStoredMuLexicalInputs.shadow (.interned entry.identity)
        (.reference (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel currentDepth))) environment)
        afterDepth = .done raw middle ∧
      SemanticHeap afterDepth ∧ Available afterDepth body ∧
      Replacements afterDepth (SourceCurrentStoredMuLexicalInputs.shadow (.interned entry.identity)
        (.reference (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel currentDepth))) environment) ∧
      Grows afterDepth middle ∧ Extends afterDepth.nodes.issued middle.nodes.issued ∧
      Grows middle after ∧ Extends middle.nodes.issued after.nodes.issued ∧ SourceCurrentLiteralRootParts.Row raw row := by
  have initialAvailable : Available before (.mu entry body depth ordinary) := stored_mu ▸ original_available
  obtain ⟨produced,final,actual,_semantic,_covered,_available,_localHistory,history,_rows⟩ :=
    SourceCurrentStoredMuRowOrigins.mu_complete entry body depth ordinary environment before initial_semantic
      initial_covered initialAvailable initial_replacements initial_history
  have observed : execute (.mu entry body depth ordinary) environment before = .done result after := by
    rw [← stored_mu]
    exact substitute_done
  obtain ⟨rfl,rfl⟩ := Outcome.done.inj (actual.symm.trans observed)
  obtain ⟨afterHistory⟩ := history
  have origins := SourceCurrentStoredMuLiteralRows.mu entry body depth ordinary environment before initial_semantic
    initialAvailable initial_replacements result after observed after afterHistory (grows_refl after) row literal_row
  refine ⟨source_done,stored_mu,open_original,nested_body,initial_semantic,initial_covered,
    original_available,initial_replacements,⟨initial_history⟩,substitute_done,⟨afterHistory⟩,
    no_physical_row,literal_row,row_fields.1,row_fields.2.1,row_fields.2.2,?_⟩
  simpa only [stored_mu] using origins

/-- Actual open nested Mu reconstruction returns a mixed union with an original-body literal row. -/
theorem mixed_union_row :
    source = .done original before ∧ original = .mu entry body depth ordinary ∧
    external ∈ original.free ∧ nested = true ∧ SemanticHeap before ∧ Covered [] before ∧
    Available before original ∧ Replacements before environment ∧ Nonempty (History (empty : Heap) before) ∧
    execute original environment before = .done result after ∧ Nonempty (History (empty : Heap) after) ∧
    nodeEdges result = [] ∧ SourceCurrentLiteralRootParts.Row result row ∧
    row.entry.key.symbol = 7 ∧ row.entry.key.constraint = () ∧ row.children = [] ∧
    ∃ currentDepth afterDepth raw middle,
      InternedFreshOrdinaryFacts.callback
        (InternedStoredSubstitution.encode (InternedStoredSubstitution.leaves original) [.interned entry.identity] body)
        ((InternedStoredSubstitution.leaves original).map (InternedStoredSubstitution.input environment))
        .depth before = .done currentDepth afterDepth ∧
      execute body (SourceCurrentStoredMuLexicalInputs.shadow (.interned entry.identity)
        (.reference (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel currentDepth))) environment)
        afterDepth = .done raw middle ∧
      SemanticHeap afterDepth ∧ Available afterDepth body ∧
      Replacements afterDepth (SourceCurrentStoredMuLexicalInputs.shadow (.interned entry.identity)
        (.reference (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel currentDepth))) environment) ∧
      Grows afterDepth middle ∧ Extends afterDepth.nodes.issued middle.nodes.issued ∧
      Grows middle after ∧ Extends middle.nodes.issued after.nodes.issued ∧ SourceCurrentLiteralRootParts.Row raw row := checked

end MicroCFTA.LiteralMuKernels
