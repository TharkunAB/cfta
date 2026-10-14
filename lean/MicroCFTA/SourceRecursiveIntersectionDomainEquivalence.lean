import MicroCFTA.IntersectDomainEquivalence
import MicroCFTA.SourceRecursiveIntersectionSchedule
import MicroCFTA.SourceRecursiveIntersectionEnvironment

/-!
# Exact execution under canonical source-domain allocation

The physical source sorts and deduplicates its domain. The semantic schedule
uses overwrite lists. Their actual lookups and cutoff sets give identical
execution at every finite bound, including all failures and copied syntax.
-/
namespace MicroCFTA.SourceRecursiveIntersectionSchedule
open IntersectSchedule IntersectionFlatMemoKeyDomain

/-- Canonical source extension retains every observation of the semantic overwrite extension. -/
theorem extend_domain_equivalent (source : DomainKey) (bound : List Nat) (key : Pair) :
    DomainEquivalent (domain (SourceRecursiveIntersectionDomain.extend source bound key))
      (IntersectSchedule.extend (domain source) (bound.map (fun name => (name, Input.mu name))) key) := by
  constructor
  · exact extend_lookup source bound key
  · intro next
    change (next ∈ (SourceRecursiveIntersectionDomain.extend source bound key).seen) ↔ next ∈ key :: source.seen
    simp only [SourceRecursiveIntersectionDomain.extend_seen, List.mem_cons]

/-- Actual canonical source-domain extension has the exact semantic node execution. -/
theorem run_canonical_extend [DecidableEq Symbol] (view : View Symbol) (fuel : Nat) (source : DomainKey)
    (bound : List Nat) (key : Pair) (left right : Input) :
    run view fuel (domain (SourceRecursiveIntersectionDomain.extend source bound key)) left right =
      run view fuel (IntersectSchedule.extend (domain source) (bound.map (fun name => (name, Input.mu name))) key) left right :=
  run_domain_equivalent view fuel _ _ (extend_domain_equivalent source bound key) left right

/-- Actual domain allocation returns the exact canonical extension key. -/
theorem entered_key (cache : Cache.State DomainKey) (valid : Cache.Valid cache) (source : DomainKey)
    (left right : InternedConstructorTemplates.Value Symbol Guard) (first second : Nat) :
    (SourceRecursiveIntersectionEnvironment.enter cache source left right first second).1.key =
      SourceRecursiveIntersectionDomain.extend source
        ((SourceRecursiveIntersectionEnvironment.bindings left right).map Prod.fst) (SourceRecursiveIntersectionControl.pair first second) :=
  (IntersectionEmptyDomain.make_correct cache valid _).2.1

/-- Actual allocated Mu domains retain every semantic overwrite observation for the original operands. -/
theorem entered_domain_equivalent (cache : Cache.State DomainKey) (valid : Cache.Valid cache) (source : DomainKey)
    (left right : InternedConstructorTemplates.Value Symbol Guard) (first second : Input)
    (leftInput : IntersectionFlatMemoKey.input left.referenceOf = some first)
    (rightInput : IntersectionFlatMemoKey.input right.referenceOf = some second)
    (leftId rightId : Nat)
    (leftIdentity : SourceRecursiveIntersectionControl.identity left = some leftId)
    (rightIdentity : SourceRecursiveIntersectionControl.identity right = some rightId) :
    DomainEquivalent (domain (SourceRecursiveIntersectionEnvironment.enter cache source left right leftId rightId).1.key)
      (IntersectSchedule.extend (domain source)
        ((SourceRecursiveIntersectionEnvironment.muNames first ++ SourceRecursiveIntersectionEnvironment.muNames second).map
          (fun name => (name, Input.mu name))) (pair first second)) := by
  rw [entered_key cache valid source left right leftId rightId]
  have bindings : (SourceRecursiveIntersectionEnvironment.bindings left right).map Prod.fst =
      SourceRecursiveIntersectionEnvironment.muNames first ++ SourceRecursiveIntersectionEnvironment.muNames second := by
    simp only [SourceRecursiveIntersectionEnvironment.bindings, List.map_append,
      SourceRecursiveIntersectionEnvironment.binder_encoded left first leftInput,
      SourceRecursiveIntersectionEnvironment.binder_encoded right second rightInput]
  rw [bindings, pair_encoded left right first second leftInput rightInput leftId rightId leftIdentity rightIdentity]
  exact extend_domain_equivalent source _ _

end MicroCFTA.SourceRecursiveIntersectionSchedule
