import MicroCFTA.SourceSynthesisUniverseBodyReferenceControl
import MicroCFTA.SourceRecursiveIntersectionReplayEffects

/-!
# Actual universe domains replay after later source effects

The first and second domain allocations retain their original raw cache
entries. Later source extensions preserve those entries. Both allocations
therefore return their original shifted domain identities and leave the
later domain cache unchanged. The constructor heap can grow independently.
No cache hit, lookup result, or future successful request is assumed.
-/
namespace MicroCFTA.SourceSynthesisUniverseDomainReplay
open Cache InternedConstructorTemplates InternedBinderProtocol
open SourceRecursiveIntersectionKernel
open SourceSynthesisUniverseBodyReferenceControl (first first_valid second secondState)

variable {Symbol Guard : Type}

/-- The actual second allocation retains the raw entries of the first allocation. -/
theorem first_domains_second (u b : Interned NodeKey) (rows : List (EdgeValue Symbol Guard))
    (depth ordinary : Value Symbol Guard) (original : Machine Symbol Guard) :
    Extends (first u b rows depth ordinary original).2.table
      (second u b rows depth ordinary original).2.table :=
  make_domain_grows _ _

/-- The original first allocation replays after any extension of the actual second machine. -/
theorem first_replay (u b : Interned NodeKey) (rows : List (EdgeValue Symbol Guard))
    (depth ordinary : Value Symbol Guard) (original after : Machine Symbol Guard)
    (valid : Cache.Valid original.domains)
    (growth : Extension (secondState u b rows depth ordinary original) after) :
    first u b rows depth ordinary after = ((first u b rows depth ordinary original).1, after.domains) := by
  have domains : Extends (first u b rows depth ordinary original).2.table after.domains.table :=
    extends_trans (first_domains_second u b rows depth ordinary original) growth.domains
  exact make_domain_replay original.domains after.domains _ valid domains

/-- Replaying both real allocations returns the original second domain without further cache effects. -/
theorem second_replay (u b : Interned NodeKey) (rows : List (EdgeValue Symbol Guard))
    (depth ordinary : Value Symbol Guard) (original after : Machine Symbol Guard)
    (valid : Cache.Valid original.domains)
    (growth : Extension (secondState u b rows depth ordinary original) after) :
    second u b rows depth ordinary after = ((second u b rows depth ordinary original).1, after.domains) := by
  unfold second
  rw [first_replay u b rows depth ordinary original after valid growth]
  exact make_domain_replay (first u b rows depth ordinary original).2 after.domains _
    (first_valid u b rows depth ordinary original valid) growth.domains

/-- The actual second-machine reconstruction is the identity on every later source extension. -/
theorem secondState_replay (u b : Interned NodeKey) (rows : List (EdgeValue Symbol Guard))
    (depth ordinary : Value Symbol Guard) (original after : Machine Symbol Guard)
    (valid : Cache.Valid original.domains)
    (growth : Extension (secondState u b rows depth ordinary original) after) :
    secondState u b rows depth ordinary after = after := by
  simp only [secondState, second_replay u b rows depth ordinary original after valid growth]

end MicroCFTA.SourceSynthesisUniverseDomainReplay
