import MicroCFTA.InternedFreshOrdinaryStoredSubstitution
import MicroCFTA.InternedStoredSubstitutionRebind
import MicroCFTA.InternedFreshOrdinarySourceFreeNames
import MicroCFTA.InternedFreshOrdinaryDepthHeap

/-!
# Physical rebinding can remove an original raw inner Mu

The closed outer source uses its local below an ordinary edge.
Its raw inner Mu uses the outer local and ignores its own local.
Stored substitution rebuilds that open inner Mu with smart cleanup.
The rebuilt value therefore differs from the original ordinary probe.
This example concerns physical equality, not runtime termination.
-/
namespace MicroCFTA.SourceCurrentStoredRebindBoundary
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction
open InternedBinderProtocol (NodeKey)

private def source : Syntax Nat Bool :=
  .binder false (.node [.mk 0 false [.var 0, .binder false (.node [.mk 1 true [.var 1]])]])

private def built := build source [] empty
private def root : Value Nat Bool := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state

private def fields : Value Nat Bool → Interned NodeKey × Value Nat Bool × Value Nat Bool × Value Nat Bool
  | .mu entry body depth ordinary => (entry, body, depth, ordinary)
  | _ => (⟨0, .node []⟩, .empty, .empty, .empty)

private def entry := (fields root).1
private def body := (fields root).2.1
private def depth := (fields root).2.2.1
private def ordinary := (fields root).2.2.2
private def own : InternedBinderProtocol.Reference := .interned entry.identity
private def argument : InternedBinderProtocol.Reference := .uninterned (ordinaryLevel depth)
private def rebound := InternedFreshOrdinaryStoredSubstitution.execute body
  (InternedStoredSubstitutionRebind.replacement own (.reference argument)) heap
private def result : Value Nat Bool := match rebound with | .done value _ => value | .pending .. => .empty
private def after := rebound.state
private def secondChild (value : Value Nat Bool) : Value Nat Bool :=
  ((children value)[1]?).getD .empty

private theorem actual : built = .done root heap := by cbv
private theorem root_shape : root = .mu entry body depth ordinary := by cbv
private theorem rebound_done : rebound = .done result after := by cbv

/-- An actual closed used outer Mu refutes physical recovery of its ordinary probe by stored self rebinding. -/
private theorem witness_proof :
    ∃ expression : Syntax Nat Bool, ∃ sourceHeap : State Nat Bool,
      ∃ actualEntry : Interned NodeKey, ∃ actualBody actualDepth actualOrdinary : Value Nat Bool,
      ∃ rebuilt : Value Nat Bool, ∃ finalHeap : State Nat Bool,
        build expression [] empty = .done (.mu actualEntry actualBody actualDepth actualOrdinary) sourceHeap ∧
        InternedNestedFacts.Facts sourceHeap ∧
        Available sourceHeap (.mu actualEntry actualBody actualDepth actualOrdinary) ∧
        (Value.mu actualEntry actualBody actualDepth actualOrdinary).free = [] ∧
        sourceHeap.nodeRecords (muKey actualDepth actualOrdinary) =
          some (.mu actualEntry actualBody actualDepth actualOrdinary) ∧
        InternedFreshOrdinaryDepthHeap.usesLocal actualDepth actualOrdinary = true ∧
        InternedFreshOrdinaryStoredSubstitution.execute actualBody
          (InternedStoredSubstitutionRebind.replacement (.interned actualEntry.identity)
            (.reference (.uninterned (ordinaryLevel actualDepth)))) sourceHeap = .done rebuilt finalHeap ∧
        rebuilt ≠ actualOrdinary ∧
        (∃ innerEntry innerBody innerDepth innerOrdinary,
          secondChild actualOrdinary = .mu innerEntry innerBody innerDepth innerOrdinary ∧
          InternedFreshOrdinaryDepthHeap.usesLocal innerDepth innerOrdinary = false) ∧
        (∃ rebuiltEntry rows cachedDepth free,
          secondChild rebuilt = .node rebuiltEntry rows cachedDepth free) := by
  have checked := InternedFreshOrdinaryFacts.closed_verified source
  have available := checked.result root heap actual
  have facts : InternedNestedFacts.Facts heap := by
    simpa only [built, heap, actual, Outcome.state] using checked.facts
  refine ⟨source, heap, entry, body, depth, ordinary, result, after, ?_, facts, ?_,
    ?_, ?_, ?_, rebound_done, ?_, ?_, ?_⟩
  · simpa only [built, ← root_shape] using actual
  · simpa only [← root_shape] using available
  · exact InternedFreshOrdinarySourceFreeNames.closed_free_empty source _ _
      (by simpa only [built, ← root_shape] using actual)
  · cbv
  · cbv
  · intro same
    have childrenSame := congrArg secondChild same
    cbv at childrenSame
    cases childrenSame
  · exact ⟨_, _, _, _, by cbv, by cbv⟩
  · exact ⟨_, _, _, _, by cbv⟩

/-- An actual closed used outer Mu refutes physical recovery of its ordinary probe by stored self rebinding. -/
theorem witness :
    ∃ expression : Syntax Nat Bool, ∃ sourceHeap : State Nat Bool,
      ∃ actualEntry : Interned NodeKey, ∃ actualBody actualDepth actualOrdinary : Value Nat Bool,
      ∃ rebuilt : Value Nat Bool, ∃ finalHeap : State Nat Bool,
        build expression [] empty = .done (.mu actualEntry actualBody actualDepth actualOrdinary) sourceHeap ∧
        InternedNestedFacts.Facts sourceHeap ∧
        Available sourceHeap (.mu actualEntry actualBody actualDepth actualOrdinary) ∧
        (Value.mu actualEntry actualBody actualDepth actualOrdinary).free = [] ∧
        sourceHeap.nodeRecords (muKey actualDepth actualOrdinary) =
          some (.mu actualEntry actualBody actualDepth actualOrdinary) ∧
        InternedFreshOrdinaryDepthHeap.usesLocal actualDepth actualOrdinary = true ∧
        InternedFreshOrdinaryStoredSubstitution.execute actualBody
          (InternedStoredSubstitutionRebind.replacement (.interned actualEntry.identity)
            (.reference (.uninterned (ordinaryLevel actualDepth)))) sourceHeap = .done rebuilt finalHeap ∧
        rebuilt ≠ actualOrdinary ∧
        (∃ innerEntry innerBody innerDepth innerOrdinary,
          secondChild actualOrdinary = .mu innerEntry innerBody innerDepth innerOrdinary ∧
          InternedFreshOrdinaryDepthHeap.usesLocal innerDepth innerOrdinary = false) ∧
        (∃ rebuiltEntry rows cachedDepth free,
          secondChild rebuilt = .node rebuiltEntry rows cachedDepth free) := witness_proof

end MicroCFTA.SourceCurrentStoredRebindBoundary
