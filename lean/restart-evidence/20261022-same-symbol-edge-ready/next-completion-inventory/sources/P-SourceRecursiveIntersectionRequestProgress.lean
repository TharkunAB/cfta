import MicroCFTA.IntersectImmediateCalls
import MicroCFTA.SourceRecursiveIntersectionInputExact
import MicroCFTA.SourceRecursiveIntersectionDomainEquivalence

/-!
# Progress from actual physical recursive branch selection

Original physical payloads supply their complete codecs and cached
closedness. Every recursive request of the actual selected branch has a
strictly smaller least successful semantic bound. Canonical allocation
retains the same child measure.
-/
namespace MicroCFTA.SourceRecursiveIntersectionRequestProgress
open Cache Binding BinderLanguage InternedConstructorTemplates InternedProbeProvenance
open InternedFreshProbeKeys InternedBinderProtocol InternedNestedFacts IntersectSchedule
open SourceRecursiveIntersectionInputView SourceRecursiveIntersectionSchedule IntersectionFlatMemoKeyDomain

/-- Actual physical branch children inherit finite successful execution at the preceding parent bound. -/
theorem physical_child_success [DecidableEq Symbol] (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (holds : Guard → Language.Term Symbol → Bool) (source : DomainKey) (left right : Value Symbol Guard)
    (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available state left) (rightAvailable : Available state right)
    (fuel : Nat) (result : Shape (Payload Symbol))
    (done : run (view state holds) (fuel + 1) (domain source) (inputOf left) (inputOf right) = .ok result)
    (child : Call Symbol) (member : child ∈ branchCalls (view state holds) (domain source) (inputOf left) (inputOf right)
      (SourceRecursiveIntersectionControl.decision source left right)) :
    ∃ output, IntersectSchedule.execute (view state holds) fuel child = .ok output := by
  apply branch_child_success (view state holds) fuel (domain source) (inputOf left) (inputOf right) _ result ?_ child member
  rw [SourceRecursiveIntersectionInputView.physical_step state facts holds fuel source left right leftOriginal rightOriginal leftAvailable rightAvailable]
  exact congrArg some done

/-- Every request of the actual physical branch strictly decreases the request's least semantic bound. -/
theorem physical_child_requiredFuel [DecidableEq Symbol] (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (holds : Guard → Language.Term Symbol → Bool) (source : DomainKey) (left right : Value Symbol Guard)
    (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available state left) (rightAvailable : Available state right)
    (complete : Completes (view state holds) (.node (domain source) (inputOf left) (inputOf right)))
    (child : Call Symbol) (member : child ∈ branchCalls (view state holds) (domain source) (inputOf left) (inputOf right)
      (SourceRecursiveIntersectionControl.decision source left right)) :
    ∃ childComplete : Completes (view state holds) child,
      requiredFuel (view state holds) child childComplete <
        requiredFuel (view state holds) (.node (domain source) (inputOf left) (inputOf right)) complete := by
  let parent : Call Symbol := Call.node (domain source) (inputOf left) (inputOf right)
  obtain ⟨result, done⟩ := requiredFuel_success (view state holds) parent complete
  have positive := requiredFuel_positive (view state holds) parent complete
  have predecessor : requiredFuel (view state holds) parent complete - 1 + 1 = requiredFuel (view state holds) parent complete := by omega
  rw [← predecessor] at done
  obtain ⟨output, childDone⟩ := physical_child_success state facts holds source left right leftOriginal rightOriginal
    leftAvailable rightAvailable _ result done child member
  exact requiredFuel_child (view state holds) parent child complete output childDone

/-- Canonical allocated source Mu domains retain the exact required fuel of their semantic overwrite child. -/
theorem entered_requiredFuel [DecidableEq Symbol] (view : View Symbol) (cache : Cache.State DomainKey) (valid : Cache.Valid cache)
    (source : DomainKey) (left right : Value Symbol Guard) (first second : Input)
    (leftInput : IntersectionFlatMemoKey.input left.referenceOf = some first)
    (rightInput : IntersectionFlatMemoKey.input right.referenceOf = some second)
    (leftId rightId : Nat)
    (leftIdentity : SourceRecursiveIntersectionControl.identity left = some leftId)
    (rightIdentity : SourceRecursiveIntersectionControl.identity right = some rightId)
    (firstChild secondChild : Input)
    (semantic : Completes view (.node (extend (domain source)
      ((SourceRecursiveIntersectionEnvironment.muNames first ++ SourceRecursiveIntersectionEnvironment.muNames second).map
        (fun name => (name, Input.mu name))) (pair first second)) firstChild secondChild)) :
    ∃ physical : Completes view (.node (domain (SourceRecursiveIntersectionEnvironment.enter cache source left right leftId rightId).1.key) firstChild secondChild),
      requiredFuel view (.node (domain (SourceRecursiveIntersectionEnvironment.enter cache source left right leftId rightId).1.key) firstChild secondChild) physical =
        requiredFuel view (.node (extend (domain source)
          ((SourceRecursiveIntersectionEnvironment.muNames first ++ SourceRecursiveIntersectionEnvironment.muNames second).map
            (fun name => (name, Input.mu name))) (pair first second)) firstChild secondChild) semantic := by
  have equivalent := entered_domain_equivalent cache valid source left right first second leftInput rightInput
    leftId rightId leftIdentity rightIdentity
  have physical : Completes view (.node (domain (SourceRecursiveIntersectionEnvironment.enter cache source left right leftId rightId).1.key) firstChild secondChild) := by
    obtain ⟨fuel, result, done⟩ := semantic
    exact ⟨fuel, result, (run_domain_equivalent view fuel _ _ equivalent firstChild secondChild).trans done⟩
  exact ⟨physical, requiredFuel_domain view _ _ equivalent firstChild secondChild physical semantic⟩

/-- Actual closed original physical roots derive the initial successful semantic request certificate. -/
theorem initial_complete [DecidableEq Symbol] (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (holds : Guard → Language.Term Symbol → Bool) (left right : Value Symbol Guard)
    (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available state left) (rightAvailable : Available state right)
    (leftClosed : left.free = []) (rightClosed : right.free = []) :
    Completes (view state holds) (.node (domain IntersectionEmptyDomain.emptyKey) (inputOf left) (inputOf right)) := by
  obtain ⟨fuel, result, completed, _⟩ := source_schedule_total state facts holds left right leftOriginal rightOriginal
    leftAvailable rightAvailable leftClosed rightClosed
  exact ⟨fuel, result, completed fuel (Nat.le_refl _)⟩

end MicroCFTA.SourceRecursiveIntersectionRequestProgress
