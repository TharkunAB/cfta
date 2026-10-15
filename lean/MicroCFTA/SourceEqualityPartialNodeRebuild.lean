import MicroCFTA.SourceEqualityInheritedRowsProofs

/-!
# Literal modifyNode reconstruction after actual row traversal

Source edge equality compares interned identities. Equal ordered identities
return the original node. Coherence and residency derive equality of complete
row payloads on that branch. Changed rows use the actual node constructor.
-/
namespace MicroCFTA.SourceEqualityPartialNodeRebuild
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Edges)
open MergedColdReaderClosedInputs (ClosedEdges)
open SourceEqualityClassFoldGraph SourceEqualityNativeScoped SourceEqualityRequiredCache
open SourceEqualityAnnotationHeap (Heap)

/-- The source fast path compares ordered interned edge identities before constructing a node. -/
def modify [DecidableEq (EdgeKey Symbol Guard)] (original : Value Symbol Guard)
    (oldRows newRows : List (EdgeValue Symbol Guard)) (before : NativeState width Symbol Guard) :
    Value Symbol Guard × NativeState width Symbol Guard :=
  if newRows.map (fun edge => edge.entry.identity) = oldRows.map (fun edge => edge.entry.identity) then (original, before)
  else
    let built := run (makeNode newRows) before.machine.heap
    (built.1, advanceHeap before built.2)

/-- The stored ordinary node selects exactly the public union of its complete source rows. -/
theorem node_meaning (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (entry : Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Guard)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (term : Term Symbol) :
    InternedGuardedLanguage.meaning holds ambient (.node entry edges depth free) term ↔
      ∃ edge ∈ edges, InternedGuardedLanguage.edgeMeaning holds ambient edge term := by
  rw [InternedGuardedLanguage.meaning]
  constructor
  · rintro ⟨⟨edge, included⟩, accepted⟩; exact ⟨edge, included, accepted⟩
  · rintro ⟨edge, included, accepted⟩; exact ⟨⟨edge, included⟩, accepted⟩

/-- Both actual reconstruction branches derive physical scope and the complete public row-union meaning. -/
theorem verified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (entry : Interned InternedBinderProtocol.NodeKey) (oldRows newRows : List (EdgeValue Symbol Guard))
    (depth : Nat) (free : List InternedBinderProtocol.Reference) (before : NativeState width Symbol Guard)
    (ready : IdleReady emptyGuard conjoin before) (available : Available before.machine.heap (.node entry oldRows depth free))
    (closed : (Value.node entry oldRows depth free).free = []) (resident : Edges before.machine.heap newRows)
    (newClosed : ClosedEdges newRows) (heap : Heap annotation before.machine.heap)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol) :
    let built := modify (.node entry oldRows depth free) oldRows newRows before
    IdleReady emptyGuard conjoin built.2 ∧ Keeps before.machine.heap built.2.machine.heap ∧
      Available built.2.machine.heap built.1 ∧ built.1.free = [] ∧ Heap annotation built.2.machine.heap ∧
      ∀ term, InternedGuardedLanguage.meaning holds ambient built.1 term ↔
        ∃ edge ∈ newRows, InternedGuardedLanguage.edgeMeaning holds ambient edge term := by
  have facts := ready.semantic.ready.semantic.1.normal.facts
  unfold modify
  dsimp only
  split
  · rename_i same
    have oldResident := resident_edges before.machine.heap facts.linked _ available.resident
    have equal := edge_lists_equal before.machine.heap facts.coherent newRows oldRows resident oldResident same
    exact ⟨ready, pure_keeps _ ready.semantic.ready, available, closed, heap,
      fun term => equal ▸ node_meaning holds ambient entry oldRows depth free term⟩
  · have built := SourceEqualityRequiredCache.node newRows before.machine.heap ready.semantic.ready resident newClosed
    have semantic := SourceEqualityRequiredSemanticCache.node newRows before.machine.heap ready.semantic resident newClosed
    have afterHeap := SourceEqualityAnnotationHeap.run annotation _ (SourceEqualityAnnotationHeap.makeNode annotation newRows) before.machine.heap heap
    refine ⟨ready.advance _ built.1 semantic, built.1, built.2.1, built.2.2.1, afterHeap, ?_⟩
    intro term
    apply (InternedGuardedLanguage.makeNode_exact before.machine.heap facts holds ambient newRows resident term).trans
    apply exists_congr
    intro edge
    exact and_congr_right fun _ => (InternedGuardedLanguage.edgeMeaning_all holds ambient edge term).symm

end MicroCFTA.SourceEqualityPartialNodeRebuild
