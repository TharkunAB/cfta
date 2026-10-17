import MicroCFTA.SourceCurrentConstrainedCapPathExposure

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
set_option pp.fullNames true

namespace CapPathExposureChecks
open MicroCFTA
open InternedConstructorTemplates InternedProbeProvenance SourceEqualityAnnotationLanguage
open SourceEqualityRequiredCache SourceEqualityRequiredHead SourceCurrentConstrainedCapPaths
open SourceCurrentHereditaryConstruction (MuStored)
variable {Symbol Guard : Type}

/-- Initial support constructs a finite actual Head before its returned mask is derived. -/
theorem own_head [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (index : Int) (path : List Int)
    (value : Value Symbol Guard) (before : State Symbol Guard) (ready : Ready before)
    (available : Available before value) (closed : value.free = []) (stored : MuStored valid before)
    (supported : Supported valid (index :: path) value) :
    ∃ result after, Head value before result after ∧ Keeps before after ∧ Available after result ∧
      result.free = [] ∧ Ordinary result ∧ MuStored valid after ∧ Supported valid (index :: path) result := by
  obtain ⟨result, after, actual, keeps, resident, resultClosed, ordinary⟩ := complete value before ready available closed
  have localResult := SourceCurrentConstrainedCapPathExposure.head valid index path actual ready available closed supported stored
  exact ⟨result, after, actual, keeps, resident, resultClosed, ordinary, localResult⟩

/-- The second own Head uses the first literal result, cache and derived causal store. -/
theorem two_heads [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (index : Int) (path : List Int)
    (value : Value Symbol Guard) (before : State Symbol Guard) (ready : Ready before)
    (available : Available before value) (closed : value.free = []) (stored : MuStored valid before)
    (supported : Supported valid (index :: path) value) :
    ∃ first middle second after, Head value before first middle ∧ Head first middle second after ∧
      Keeps before after ∧ MuStored valid after ∧ Supported valid (index :: path) second := by
  obtain ⟨first, middle, firstHead, firstKeeps, firstAvailable, firstClosed, _, middleStored, firstMask⟩ :=
    own_head valid index path value before ready available closed stored supported
  obtain ⟨second, after, secondHead, secondKeeps, _, _, _, afterStored, secondMask⟩ :=
    own_head valid index path first middle firstKeeps.ready firstAvailable firstClosed middleStored firstMask
  exact ⟨first, middle, second, after, firstHead, secondHead, firstKeeps.trans secondKeeps, afterStored, secondMask⟩

/-- Initial union alternatives construct their actual exposure at the unchanged signed path. -/
theorem own_union_head [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (index : Int) (path : List Int)
    (entry) (members : List (Value Symbol Guard)) (depth free) (before : State Symbol Guard) (ready : Ready before)
    (available : Available before (.union entry members depth free))
    (closed : (Value.union entry members depth free : Value Symbol Guard).free = []) (stored : MuStored valid before)
    (supported : ∀ value ∈ members, Supported valid (index :: path) value) :
    ∃ result after, Head (.union entry members depth free) before result after ∧ Keeps before after ∧
      MuStored valid after ∧ Supported valid (index :: path) result := by
  obtain ⟨result, after, actual, kept, _, _, _, finalStored, mask⟩ := own_head valid index path
    (.union entry members depth free) before ready available closed stored (.union _ entry members depth free supported)
  exact ⟨result, after, actual, kept, finalStored, mask⟩

end CapPathExposureChecks

#print axioms CapPathExposureChecks.own_head
#check @CapPathExposureChecks.own_head
#print axioms CapPathExposureChecks.two_heads
#check @CapPathExposureChecks.two_heads
#print axioms CapPathExposureChecks.own_union_head
#check @CapPathExposureChecks.own_union_head
