import MicroCFTA.SourceCurrentStoredMuLexicalInputs
import MicroCFTA.SourceCurrentStoredMuRowOrigins

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace MicroCFTA.StoredMuKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency InternedRecordCoherence
open InternedNestedConstruction (Syntax Outcome)
open InternedStoredSubstitution (Environment Replacements)
open InternedFreshOrdinaryStoredSubstitution (execute)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceCurrentNativeMuPublication (History)
open InternedBinderProtocol (Reference NodeKey)
local notation "Heap" => State Nat Unit

private def external : Reference := .intersection 0 1
private def captures : List (Value Nat Unit) := [.reference external]
private def inner : Syntax Nat Unit := .binder true (.node [.mk 9 () [.var 0,.var 2]])
private def expression : Syntax Nat Unit := .binder true (.union [
  .node [.mk 8 () [.var 0,.var 1,inner]], .node [.mk 7 () []]])
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
private def row : EdgeValue Nat Unit := (nodeEdges result)[0]?.getD (run (makeEdge 7 () []) (empty : Heap)).1
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
private theorem selected_row : (nodeEdges result)[0]? = some row := by cbv
private theorem row_fields : row.entry.key.symbol = 7 ∧ row.entry.key.constraint = () ∧ row.children = [] := by
  constructor
  · cbv
  · exact ⟨rfl,by cbv⟩

private theorem capture_available : Available (empty : Heap) (.reference external) := by
  apply reference_available
  intro identity impossible
  simp only [external,Value.free,List.mem_singleton] at impossible
  cases impossible

private theorem initial_context : SourceCurrentConstrainedCapSourceHistory.Context (empty : Heap) captures := by
  refine ⟨SourceRecursiveIntersectionSemanticHeap.context empty SourceRecursiveIntersectionSemanticHeap.empty_heap
    captures ?_,InternedFreshOrdinaryDepthHeap.empty_heap⟩
  intro child member
  have same : child = .reference external := by simpa only [captures,List.mem_singleton] using member
  subst child
  exact capture_available

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

/-- An actual open stored Mu loses a recursive alternative and retains its original-body row call. -/
private theorem checked :
    source = .done original before ∧ original = .mu entry body depth ordinary ∧
    external ∈ original.free ∧ nested = true ∧ SemanticHeap before ∧ Covered [] before ∧
    Available before original ∧ Replacements before environment ∧ Nonempty (History (empty : Heap) before) ∧
    execute original environment before = .done result after ∧
    SemanticHeap after ∧ Covered [] after ∧ Available after result ∧
    Nonempty (History before after) ∧ Nonempty (History (empty : Heap) after) ∧
    (nodeEdges result)[0]? = some row ∧ row.entry.key.symbol = 7 ∧ row.entry.key.constraint = () ∧
    row.children = [] ∧ result.free = [] ∧
    SourceCurrentStoredMuRowOrigins.Rows entry body (InternedStoredSubstitution.leaves original)
      environment before result after after := by
  have initialAvailable : Available before (.mu entry body depth ordinary) := stored_mu ▸ original_available
  obtain ⟨produced,final,actual,semantic,covered,available,localHistory,history,rows⟩ :=
    SourceCurrentStoredMuRowOrigins.mu_complete entry body depth ordinary environment before initial_semantic
      initial_covered initialAvailable initial_replacements initial_history
  have observed : execute (.mu entry body depth ordinary) environment before = .done result after := by
    rw [← stored_mu]
    exact substitute_done
  obtain ⟨rfl,rfl⟩ := Outcome.done.inj (actual.symm.trans observed)
  refine ⟨source_done,stored_mu,open_original,nested_body,initial_semantic,initial_covered,
    original_available,initial_replacements,⟨initial_history⟩,substitute_done,semantic,covered,available,
    localHistory,history,selected_row,row_fields.1,row_fields.2.1,row_fields.2.2,?_,?_⟩
  · cbv
  · simpa only [stored_mu] using rows

/-- Source-built nested Mu substitution returns an ordinary row with actual original-body provenance. -/
theorem open_stored_mu_row :
    source = .done original before ∧ original = .mu entry body depth ordinary ∧
    external ∈ original.free ∧ nested = true ∧ SemanticHeap before ∧ Covered [] before ∧
    Available before original ∧ Replacements before environment ∧ Nonempty (History (empty : Heap) before) ∧
    execute original environment before = .done result after ∧
    SemanticHeap after ∧ Covered [] after ∧ Available after result ∧
    Nonempty (History before after) ∧ Nonempty (History (empty : Heap) after) ∧
    (nodeEdges result)[0]? = some row ∧ row.entry.key.symbol = 7 ∧ row.entry.key.constraint = () ∧
    row.children = [] ∧ result.free = [] ∧
    SourceCurrentStoredMuRowOrigins.Rows entry body (InternedStoredSubstitution.leaves original)
      environment before result after after := checked

end MicroCFTA.StoredMuKernels

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000

#check @MicroCFTA.StoredMuKernels.open_stored_mu_row
#print MicroCFTA.StoredMuKernels.open_stored_mu_row
#print axioms MicroCFTA.StoredMuKernels.open_stored_mu_row
