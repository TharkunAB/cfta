import MicroCFTA.SourceRecursiveIntersectionReplayMu

/-!
# Completed full recursive caller replay

Every completed guarded source call reuses its exact original value after
constructor and domain growth. Replay leaves the entire later machine
unchanged. Larger bounds retain this same completed observation.
-/
namespace MicroCFTA.SourceRecursiveIntersectionKernel
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain

/-- Full source control replays actual completed child and constructor effects. -/
theorem onNode_replay [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (replay : Replays call) (domain : Interned DomainKey) (left right : Value Symbol Guard)
    (before after : Machine Symbol Guard) (valid : Valid before) (known : Domain before domain)
    (leftAvailable : Available before.heap left) (rightAvailable : Available before.heap right)
    (value : Value Symbol Guard) (final : Machine Symbol Guard)
    (done : onNode emptyGuard conjoin call domain left right before = .done value final) (growth : Extension final after) :
    onNode emptyGuard conjoin call domain left right after = .done value after := by
  cases selected : SourceRecursiveIntersectionControl.decision domain.key left right with
  | empty | self | repeated =>
      simp only [onNode, selected] at done ⊢
      cases done
      rfl
  | unsupported =>
      simp only [onNode, selected] at done
      cases done
  | reset =>
      simp only [onNode, selected] at done ⊢
      exact replay _ left right before after value final valid (empty_domain before) leftAvailable rightAvailable done growth
  | swap =>
      simp only [onNode, selected] at done ⊢
      exact replay domain right left before after value final valid known rightAvailable leftAvailable done growth
  | bothMu | leftMu | rightMu =>
      simp only [onNode, selected] at done ⊢
      exact mu_replay call calls replay domain left right before after valid known leftAvailable rightAvailable value final done growth
  | leftUnion =>
      simp only [onNode, selected] at done ⊢
      cases left <;> try cases done
      rename_i entry members depth free
      exact union_replay call calls replay domain members right true before after valid known rightAvailable
        (fun member present => leftAvailable.children member (by simpa only [children] using present)) value final done growth
  | rightUnion =>
      simp only [onNode, selected] at done ⊢
      cases right <;> try cases done
      rename_i entry members depth free
      exact union_replay call calls replay domain members left false before after valid known leftAvailable
        (fun member present => rightAvailable.children member (by simpa only [children] using present)) value final done growth
  | leftReference =>
      simp only [onNode, selected] at done ⊢
      cases left <;> try cases done
      rename_i name
      cases name <;> try cases done
      exact reference_replay call calls replay domain _ right true before after valid known rightAvailable value final done growth
  | rightReference =>
      simp only [onNode, selected] at done ⊢
      cases right <;> try cases done
      rename_i name
      cases name <;> try cases done
      exact reference_replay call calls replay domain _ left false before after valid known leftAvailable value final done growth
  | ordinary =>
      simp only [onNode, selected] at done ⊢
      cases left <;> cases right <;> try cases done
      rename_i first firstEdges firstDepth firstFree second secondEdges secondDepth secondFree
      exact node_replay emptyGuard conjoin call calls replay domain firstEdges secondEdges before after valid known
        (fun edge member => valid.1.linked first.key _ (leftAvailable.resident first rfl) edge member)
        (fun edge member => valid.1.linked second.key _ (rightAvailable.resident second rfl) edge member)
        value final done growth

/-- Actual completed guarded recursive execution replays without new physical or domain allocation. -/
theorem execute_replay [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel : Nat) : Replays (execute (Symbol := Symbol) emptyGuard conjoin fuel) := by
  induction fuel with
  | zero =>
      intro domain left right before after value final valid known leftAvailable rightAvailable done growth
      simp only [execute] at done
      cases done
  | succ fuel ih =>
      intro domain left right before after value final valid known leftAvailable rightAvailable done growth
      simp only [execute] at done ⊢
      exact onNode_replay emptyGuard conjoin _ (execute_checked emptyGuard conjoin fuel) ih domain left right before after
        valid known leftAvailable rightAvailable value final done growth

/-- Completed source executions replay identically at every larger bound after later source effects. -/
theorem execute_larger_replay [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel extra : Nat) (domain : Interned DomainKey) (left right : Value Symbol Guard) (before after : Machine Symbol Guard)
    (valid : Valid before) (known : Domain before domain) (leftAvailable : Available before.heap left) (rightAvailable : Available before.heap right)
    (value : Value Symbol Guard) (final : Machine Symbol Guard)
    (done : execute emptyGuard conjoin fuel domain left right before = .done value final) (growth : Extension final after) :
    execute emptyGuard conjoin (fuel + extra) domain left right after = .done value after := by
  have repeated := execute_replay emptyGuard conjoin fuel domain left right before after value final valid known leftAvailable rightAvailable done growth
  rw [execute_stable emptyGuard conjoin fuel extra domain left right after (by rw [repeated]; trivial), repeated]

end MicroCFTA.SourceRecursiveIntersectionKernel
