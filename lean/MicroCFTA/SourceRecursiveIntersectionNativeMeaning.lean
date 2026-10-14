import MicroCFTA.SourceRecursiveIntersectionNativeSourceCalls

/-!
# Stable physical meaning of native source code

Finite source meanings retain complete returned machines at every larger
recursive kernel bound. Exact compiler equations convert completed body
meanings into concrete node and edge executions. Sequencing combines child
bounds without assuming callback purity.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode

/-- Interpret explicit source code with the bounded guarded kernel at every recursive request. -/
def meaning [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel : Nat) (code : Code Symbol Guard A) (state : Machine Symbol Guard) : Result Symbol Guard A :=
  interpret (fun request => SourceRecursiveIntersectionKernel.execute emptyGuard conjoin fuel request.domain request.left request.right)
    (fun request => SourceRecursiveIntersectionKernel.edge emptyGuard conjoin
      (SourceRecursiveIntersectionKernel.execute emptyGuard conjoin fuel request.domain) request.left request.right) code state

/-- A completed source meaning has a finite stable recursive bound and exact physical effects. -/
def Meaning [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (code : Code Symbol Guard A) (state : Machine Symbol Guard) (value : A) (after : Machine Symbol Guard) : Prop :=
  ∃ fuel, ∀ extra, meaning emptyGuard conjoin (fuel + extra) code state = .done value after

/-- A completed compiled node body derives an actual guarded node execution at a finite stable bound. -/
theorem Meaning.node_body [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {request : NodeRequest Symbol Guard} {state after : Machine Symbol Guard} {value : Value Symbol Guard}
    (body : Meaning emptyGuard conjoin (compileNode request) state value after) :
    ∃ fuel, ∀ extra, SourceRecursiveIntersectionKernel.execute emptyGuard conjoin (fuel + extra)
      request.domain request.left request.right state = .done value after := by
  obtain ⟨fuel, completed⟩ := body
  refine ⟨fuel + 1, ?_⟩
  intro extra
  rw [Nat.add_right_comm fuel 1 extra]
  change onNode emptyGuard conjoin (SourceRecursiveIntersectionKernel.execute emptyGuard conjoin (fuel + extra))
    request.domain request.left request.right state = .done value after
  exact (compileNode_exact
    (fun request => SourceRecursiveIntersectionKernel.execute emptyGuard conjoin (fuel + extra) request.domain request.left request.right)
    emptyGuard conjoin request state).symm.trans (completed extra)

/-- A completed compiled edge body derives the actual guarded edge worker at a finite stable child bound. -/
theorem Meaning.edge_body [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {request : EdgeRequest Symbol Guard} {state after : Machine Symbol Guard} {value : EdgeValue Symbol Guard}
    (body : Meaning emptyGuard conjoin (compileEdge emptyGuard conjoin request) state value after) :
    ∃ fuel, ∀ extra, SourceRecursiveIntersectionKernel.edge emptyGuard conjoin
      (SourceRecursiveIntersectionKernel.execute emptyGuard conjoin (fuel + extra) request.domain) request.left request.right state = .done value after := by
  obtain ⟨fuel, completed⟩ := body
  refine ⟨fuel, ?_⟩
  intro extra
  exact (compileEdge_exact
    (fun request => SourceRecursiveIntersectionKernel.execute emptyGuard conjoin (fuel + extra) request.domain request.left request.right)
    (fun request => SourceRecursiveIntersectionKernel.edge emptyGuard conjoin
      (SourceRecursiveIntersectionKernel.execute emptyGuard conjoin (fuel + extra) request.domain) request.left request.right)
    emptyGuard conjoin request state).symm.trans (completed extra)

/-- A concrete stable node execution composes with the original stable source continuation. -/
theorem Meaning.node [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {request : NodeRequest Symbol Guard} {next : Value Symbol Guard → Code Symbol Guard A}
    {state middle after : Machine Symbol Guard} {value : Value Symbol Guard} {result : A}
    (call : ∃ fuel, ∀ extra, SourceRecursiveIntersectionKernel.execute emptyGuard conjoin (fuel + extra)
      request.domain request.left request.right state = .done value middle)
    (tail : Meaning emptyGuard conjoin (next value) middle result after) : Meaning emptyGuard conjoin (.node request next) state result after := by
  obtain ⟨first, executed⟩ := call
  obtain ⟨second, continued⟩ := tail
  refine ⟨first + second, ?_⟩
  intro extra
  change (SourceRecursiveIntersectionKernel.execute emptyGuard conjoin ((first + second) + extra)
    request.domain request.left request.right state).bind
      (fun value current => meaning emptyGuard conjoin ((first + second) + extra) (next value) current) = .done result after
  rw [Nat.add_assoc, executed (second + extra)]
  change meaning emptyGuard conjoin (first + (second + extra)) (next value) middle = .done result after
  simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using continued (first + extra)

/-- A concrete stable row execution composes with its original stable source continuation. -/
theorem Meaning.edge [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {request : EdgeRequest Symbol Guard} {next : EdgeValue Symbol Guard → Code Symbol Guard A}
    {state middle after : Machine Symbol Guard} {value : EdgeValue Symbol Guard} {result : A}
    (call : ∃ fuel, ∀ extra, SourceRecursiveIntersectionKernel.edge emptyGuard conjoin
      (SourceRecursiveIntersectionKernel.execute emptyGuard conjoin (fuel + extra) request.domain) request.left request.right state = .done value middle)
    (tail : Meaning emptyGuard conjoin (next value) middle result after) : Meaning emptyGuard conjoin (.edge request next) state result after := by
  obtain ⟨first, executed⟩ := call
  obtain ⟨second, continued⟩ := tail
  refine ⟨first + second, ?_⟩
  intro extra
  change (SourceRecursiveIntersectionKernel.edge emptyGuard conjoin
    (SourceRecursiveIntersectionKernel.execute emptyGuard conjoin ((first + second) + extra) request.domain)
      request.left request.right state).bind
      (fun value current => meaning emptyGuard conjoin ((first + second) + extra) (next value) current) = .done result after
  rw [Nat.add_assoc, executed (second + extra)]
  change meaning emptyGuard conjoin (first + (second + extra)) (next value) middle = .done result after
  simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using continued (first + extra)

end MicroCFTA.SourceRecursiveIntersectionNative
