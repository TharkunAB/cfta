import MicroCFTA.SourceCurrentStoredLiteralRowLineage
import MicroCFTA.InternedStoredLeafShape
import MicroCFTA.InternedStoredSubstitutionScope
import MicroCFTA.SourceCurrentRecursiveHeadRowOrigins

/-!
# Exact native self-substitution capture slots

A row-bearing mapped leaf is the same closed leaf or the complete Mu that
replaces the selected own reference. Every other reference stays literal.
-/
namespace MicroCFTA.SourceCurrentNativeSelfCaptureSlots
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedStoredSubstitution (leaves input slot)
open InternedBinderProtocol (NodeKey)
open SourceCurrentRecursiveHeadRowOrigins (selfEnvironment)
open SourceCurrentStoredLiteralRowLineage (RowAt)

/-- A row-bearing mapped lookup retains the exact closed leaf or exact complete self Mu at that slot. -/
theorem lookup (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (index : Nat) (captured : Value Symbol Guard)
    (found : ((leaves body).map (input (selfEnvironment entry body depth ordinary)))[index]? = some captured)
    (row : EdgeValue Symbol Guard) (inside : RowAt captured row) :
    (∃ leaf, (leaves body)[index]? = some leaf ∧ leaf.free = [] ∧ captured = leaf ∧ RowAt leaf row) ∨
    ((leaves body)[index]? = some (.reference (.interned entry.identity)) ∧
      captured = .mu entry body depth ordinary) := by
  cases selected : (leaves body)[index]? with
  | none =>
      simp only [List.getElem?_map,selected,Option.map_none] at found
      cases found
  | some leaf =>
      have mapped : input (selfEnvironment entry body depth ordinary) leaf = captured := by
        simpa only [List.getElem?_map,selected,Option.map_some,Option.some.injEq] using found
      rcases InternedStoredLeafShape.leaves_shape body leaf (List.mem_of_getElem? selected) with closed | ⟨name,rfl⟩
      · have same : captured = leaf := mapped.symm.trans
          (InternedStoredSubstitutionScope.input_closed leaf _ closed)
        exact .inl ⟨leaf,rfl,closed,same,same ▸ inside⟩
      · by_cases own : name = .interned entry.identity
        · refine .inr ⟨by simp only [own],?_⟩
          simpa only [input,selfEnvironment,own,ite_true,Option.getD_some] using mapped.symm
        · have same : captured = .reference name := by
            simpa only [input,selfEnvironment,own,ite_false,Option.getD_none] using mapped.symm
          rw [same] at inside
          cases inside

/-- Canonical identity lookup gives the same split when its coherent available source premises hold. -/
theorem canonical_slot (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state)
    (available : InternedNestedProvenance.Values state (leaves body))
    (leaf : Value Symbol Guard) (member : leaf ∈ leaves body)
    (row : EdgeValue Symbol Guard)
    (inside : RowAt (input (selfEnvironment entry body depth ordinary) leaf) row) :
    (∃ original, (leaves body)[slot (leaves body) leaf]? = some original ∧ original.free = [] ∧
      input (selfEnvironment entry body depth ordinary) leaf = original ∧ RowAt original row) ∨
    ((leaves body)[slot (leaves body) leaf]? = some (.reference (.interned entry.identity)) ∧
      input (selfEnvironment entry body depth ordinary) leaf = .mu entry body depth ordinary) := by
  have selected := InternedStoredSubstitutionScope.slot_lookup (leaves body) leaf state coherent available member
  have found : ((leaves body).map (input (selfEnvironment entry body depth ordinary)))[slot (leaves body) leaf]? =
      some (input (selfEnvironment entry body depth ordinary) leaf) := by
    simp only [List.getElem?_map,selected,Option.map_some]
  exact lookup entry body depth ordinary (slot (leaves body) leaf)
    (input (selfEnvironment entry body depth ordinary) leaf) found row inside

end MicroCFTA.SourceCurrentNativeSelfCaptureSlots

/-!
# Actual self capture and closed leaf

The source builds the used Mu x. node7[node17[],x]. Its actual body plan
captures a closed ordinary leaf and the literal own reference. The mapped
self input is the complete selected Mu, not a bare binder name.
-/
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 50000000
namespace MicroCFTA.NativeSelfCaptureSlotsKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence InternedEdgeResidency
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryStoredSubstitution (unfold)
open InternedStoredSubstitution (leaves input slot)
open SourceCurrentRecursiveHeadRowOrigins (selfEnvironment)
open SourceCurrentStoredLiteralRowLineage (RowAt)
open SourceCurrentNativeSelfCaptureSlots (lookup canonical_slot)
local notation "Node" => Value Nat Bool
local notation "Row" => EdgeValue Nat Bool
local notation "Heap" => State Nat Bool

private def expression : Syntax Nat Bool :=
  .binder false (.node [.mk 7 false [.node [.mk 17 true []],.var 0]])
private def built := build expression [] (empty : Heap)
private def value : Node := match built with | .done result _ => result | .pending .. => .empty
private def before : Heap := built.state
private def entry := match value with
  | .mu entry _ _ _ => entry
  | _ => (Cache.intern (empty : Heap).nodes .empty).1
private def body : Node := match value with | .mu _ body _ _ => body | _ => .empty
private def depth : Node := match value with | .mu _ _ depth _ => depth | _ => .empty
private def ordinary : Node := match value with | .mu _ _ _ ordinary => ordinary | _ => .empty
private def leaf : Node := (leaves body)[0]?.getD .empty
private def leafRow : Row := (nodeEdges leaf)[0]?.getD (run (makeEdge 0 false []) (empty : Heap)).1
private def bodyRow : Row := (nodeEdges body)[0]?.getD leafRow
private def called := unfold value before
private def result : Node := match called with | .done result _ => result | .pending .. => .empty
private def after : Heap := called.state

private theorem built_done : build expression [] (empty : Heap) = .done value before := by cbv
private theorem value_shape : value = .mu entry body depth ordinary := by cbv
private theorem used : InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true := by cbv
private theorem leaves_exact : leaves body = [leaf,.reference (.interned entry.identity)] := by cbv
private theorem leaf_closed : leaf.free = [] := by cbv
private theorem leaf_at_zero : (leaves body)[0]? = some leaf := by rw [leaves_exact]; rfl
private theorem own_at_one : (leaves body)[1]? = some (.reference (.interned entry.identity)) := by rw [leaves_exact]; rfl
private theorem mapped_zero : ((leaves body).map (input (selfEnvironment entry body depth ordinary)))[0]? = some leaf := by cbv
private theorem mapped_one : ((leaves body).map (input (selfEnvironment entry body depth ordinary)))[1]? = some value := by cbv
private theorem canonical_zero : slot (leaves body) leaf = 0 := by cbv
private theorem selected : before.nodeRecords (muKey depth ordinary) = some value := by cbv
private theorem unfold_done : unfold value before = .done result after := by cbv
private theorem leaf_inside : RowAt leaf leafRow := by
  cbv
  exact .node (index := 0) rfl
private theorem self_inside : RowAt value bodyRow := by
  cbv
  exact .mu (.node (index := 0) rfl)
private theorem ready : SourceEqualityRequiredCache.Ready before :=
  SourceEqualityRequiredCache.constructed expression value before built_done
private theorem available : Available before value :=
  (InternedFreshOrdinaryFacts.closed_verified expression).result value before built_done
private theorem body_available : Available before body := by
  have actual : Available before (.mu entry body depth ordinary) := value_shape ▸ available
  exact actual.children body (by simp [InternedProbeProvenance.children])
private theorem leaves_available : InternedNestedProvenance.Values before (leaves body) :=
  InternedStoredSubstitution.leaves_available body before body_available

private theorem closed_case :
    ∃ original, (leaves body)[0]? = some original ∧ original.free = [] ∧ leaf = original ∧ RowAt original leafRow := by
  have input_same : input (selfEnvironment entry body depth ordinary) leaf = leaf :=
    InternedStoredSubstitutionScope.input_closed leaf _ leaf_closed
  have mapped_inside : RowAt (input (selfEnvironment entry body depth ordinary) leaf) leafRow := by
    rw [input_same]
    exact leaf_inside
  have classified := canonical_slot entry body depth ordinary before ready.semantic.1.normal.facts.coherent
    leaves_available leaf (List.mem_of_getElem? leaf_at_zero) leafRow mapped_inside
  rw [canonical_zero,input_same] at classified
  rcases classified with retained | own
  · exact retained
  · have same : leaf = .reference (.interned entry.identity) := Option.some.inj (leaf_at_zero.symm.trans own.1)
    have impossible := leaf_inside
    rw [same] at impossible
    cases impossible

private theorem self_case :
    (leaves body)[1]? = some (.reference (.interned entry.identity)) ∧ value = .mu entry body depth ordinary := by
  have classified := lookup entry body depth ordinary 1 value mapped_one bodyRow self_inside
  rcases classified with ⟨original,found,closed,_same,_inside⟩ | own
  · have same : original = .reference (.interned entry.identity) := Option.some.inj (found.symm.trans own_at_one)
    rw [same] at closed
    simp only [Value.free,List.cons_ne_nil] at closed
  · exact own

private theorem checked_witness :
    build expression [] (empty : Heap) = .done value before ∧
    value = .mu entry body depth ordinary ∧
    InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true ∧
    before.nodeRecords (muKey depth ordinary) = some value ∧
    SourceEqualityRequiredCache.Ready before ∧ Available before value ∧
    InternedNestedProvenance.Values before (leaves body) ∧
    leaves body = [leaf,.reference (.interned entry.identity)] ∧
    ((leaves body).map (input (selfEnvironment entry body depth ordinary)))[0]? = some leaf ∧
    ((leaves body).map (input (selfEnvironment entry body depth ordinary)))[1]? = some value ∧
    slot (leaves body) leaf = 0 ∧
    unfold value before = .done result after ∧ RowAt leaf leafRow ∧ RowAt value bodyRow ∧
    (∃ original, (leaves body)[0]? = some original ∧ original.free = [] ∧ leaf = original ∧ RowAt original leafRow) ∧
    ((leaves body)[1]? = some (.reference (.interned entry.identity)) ∧ value = .mu entry body depth ordinary) :=
  ⟨built_done,value_shape,used,selected,ready,available,leaves_available,leaves_exact,
    mapped_zero,mapped_one,canonical_zero,unfold_done,leaf_inside,self_inside,closed_case,self_case⟩

/-- A source-built used Mu exercises the closed-leaf and complete-self arms at their exact native slots. -/
theorem closed_and_self :
    build expression [] (empty : Heap) = .done value before ∧
    value = .mu entry body depth ordinary ∧
    InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true ∧
    before.nodeRecords (muKey depth ordinary) = some value ∧
    SourceEqualityRequiredCache.Ready before ∧ Available before value ∧
    InternedNestedProvenance.Values before (leaves body) ∧
    leaves body = [leaf,.reference (.interned entry.identity)] ∧
    ((leaves body).map (input (selfEnvironment entry body depth ordinary)))[0]? = some leaf ∧
    ((leaves body).map (input (selfEnvironment entry body depth ordinary)))[1]? = some value ∧
    slot (leaves body) leaf = 0 ∧
    unfold value before = .done result after ∧ RowAt leaf leafRow ∧ RowAt value bodyRow ∧
    (∃ original, (leaves body)[0]? = some original ∧ original.free = [] ∧ leaf = original ∧ RowAt original leafRow) ∧
    ((leaves body)[1]? = some (.reference (.interned entry.identity)) ∧ value = .mu entry body depth ordinary) := checked_witness

end MicroCFTA.NativeSelfCaptureSlotsKernels

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.NativeSelfCaptureSlotsKernels.closed_and_self
#print MicroCFTA.NativeSelfCaptureSlotsKernels.closed_and_self
#print axioms MicroCFTA.NativeSelfCaptureSlotsKernels.closed_and_self
