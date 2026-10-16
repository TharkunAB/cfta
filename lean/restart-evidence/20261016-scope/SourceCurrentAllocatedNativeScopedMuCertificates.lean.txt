import MicroCFTA.SourceCurrentAllocatedNativeScopedCode
import MicroCFTA.SourceRecursiveIntersectionResultScope
import MicroCFTA.SourceRecursiveIntersectionKernelCalls
import MicroCFTA.SourceRecursiveIntersectionCompileMuBounds

/-!
# Local scope certificates for source Mu and reference code

Actual domain entry adds the current pair to the child scope. Actual binder
completion removes that pair. Reference code keeps the same domain scope.
These certificates do not assume successful recursive execution.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeScopedMuCertificates
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceCurrentAllocatedNativeScopedCode
open SourceRecursiveIntersectionResultScope (Scope)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Actual optional-binder completion removes its pair from the incoming child scope. -/
theorem optional_scope [DecidableEq (EdgeKey Symbol Guard)]
    (pairs : List (Nat × Nat)) (pair : Nat × Nat) (body value : Value Symbol Guard)
    (before after : Machine Symbol Guard)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before.heap)
    (available : Available before.heap body) (scope : Scope (pair :: pairs) body)
    (done : construction (SourceRecursiveIntersectionMaybeMu.maybeMu pair body before.heap) before = .done value after) :
    Scope pairs value := by
  cases actual : SourceRecursiveIntersectionMaybeMu.maybeMu pair body before.heap with
  | pending => simp only [actual, construction] at done; cases done
  | done result heap =>
      have same := Result.done.inj (by simpa only [actual, construction] using done)
      rcases same.1 with rfl
      exact SourceRecursiveIntersectionResultScope.optionalBinder pairs pair body before.heap
        semantic.ready.semantic.1 available scope result heap actual

/-- Actual Mu entry and the exact child scope certify the source optional-binder continuation. -/
theorem mu_certified [DecidableEq (EdgeKey Symbol Guard)]
    (request : NodeRequest Symbol Guard) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (ready : NodeReady state request) :
    Certified (compileMu request.domain request.left request.right) state
      (fun _ value => Scope request.domain.key.seen value) := by
  cases first : SourceRecursiveIntersectionControl.identity request.left <;>
    cases second : SourceRecursiveIntersectionControl.identity request.right <;>
    simp only [compileMu, first, second]
  all_goals try trivial
  rename_i firstName secondName
  let actual := SourceRecursiveIntersectionEnvironment.enter state.domains request.domain.key
    request.left request.right firstName secondName
  have entered := SourceRecursiveIntersectionKernel.entered state valid request.domain ready.1
    request.left request.right ready.2.1 ready.2.2 firstName secondName
  have key := SourceRecursiveIntersectionSchedule.entered_key state.domains valid.2 request.domain.key
    request.left request.right firstName secondName
  refine ⟨entered.1, entered.2.1, ?_⟩
  intro body middle _ _ semantic available scope value after done _ _ _
  apply optional_scope request.domain.key.seen (SourceRecursiveIntersectionControl.pair firstName secondName)
    body value middle after semantic available ?_ done
  apply SourceRecursiveIntersectionResultScope.weaken actual.1.key.seen _ ?_ body scope
  intro pair member
  rw [key] at member
  exact List.mem_cons.mpr ((SourceRecursiveIntersectionDomain.extend_seen _ _ _ pair).mp member)

/-- Actual left reference readback preserves the next request's same-domain scope. -/
theorem left_reference [DecidableEq (EdgeKey Symbol Guard)] (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (name : Nat)
    (other : Value Symbol Guard) (state : Machine Symbol Guard) :
    Certified (compileReference domain name other true) state (fun _ value => Scope domain.key.seen value) := by
  unfold compileReference
  split
  · simp only [Certified]
    cases SourcePreparedSharedRows.read state.heap name with
    | none => trivial
    | some bound => intro value after _ _ _ _ scope; exact scope
  · trivial

/-- Actual right reference readback keeps operand order and the same domain scope. -/
theorem right_reference [DecidableEq (EdgeKey Symbol Guard)] (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (name : Nat)
    (other : Value Symbol Guard) (state : Machine Symbol Guard) :
    Certified (compileReference domain name other false) state (fun _ value => Scope domain.key.seen value) := by
  unfold compileReference
  split
  · simp only [Certified]
    cases SourcePreparedSharedRows.read state.heap name with
    | none => trivial
    | some bound => intro value after _ _ _ _ scope; exact scope
  · trivial

end MicroCFTA.SourceCurrentAllocatedNativeScopedMuCertificates
