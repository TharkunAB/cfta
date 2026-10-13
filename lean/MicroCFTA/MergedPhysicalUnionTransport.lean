import MicroCFTA.MergedPhysicalLanguage

/-!
# Physical languages through later cache growth

Prepared recursive reads replay with their original result. Every finite
accepting run therefore keeps the same language after cache growth. The
proof uses actual available records and the exact unfolding computation.
-/
namespace MicroCFTA.MergedPhysicalUnionTransport
open InternedConstructorTemplates InternedProbeProvenance InternedNestedProvenance
open MergedPhysicalWarmup MergedPhysicalComparison MergedPhysicalMergeContext MergedPhysicalLanguage
open Language

/-- Prepared successors retain their exact records after arbitrary cache growth. -/
theorem successors_stable [DecidableEq (EdgeKey Symbol Guard)]
    (before after : InternedConstructorTemplates.State Symbol Guard)
    (outputs : List (Value Symbol Guard)) (context : Context before outputs)
    (growth : Grows before after) (value : Value Symbol Guard) (available : Available before value) :
    successors after value = successors before value := by
  cases value with
  | empty | reference | node | union => rfl
  | mu entry body depth ordinary =>
      obtain ⟨result, _, done⟩ := context.ready entry body depth ordinary available
      have replay := unfold_replay _ before after result before context.facts.coherent.valid done growth
      simp only [successors, done, replay]

/-- Every prepared successor is already available in the original cache. -/
theorem successors_available [DecidableEq (EdgeKey Symbol Guard)]
    (state : InternedConstructorTemplates.State Symbol Guard)
    (outputs : List (Value Symbol Guard)) (context : Context state outputs)
    (value : Value Symbol Guard) (available : Available state value) :
    Values state (successors state value) := by
  intro next member
  cases value with
  | empty | reference | node => simp [successors] at member
  | union entry members depth free => exact available.children next member
  | mu entry body depth ordinary =>
      obtain ⟨result, retained, done⟩ := context.ready entry body depth ordinary available
      have same : next = result := by simpa only [successors, done, List.mem_singleton] using member
      rw [same]
      exact context.retained result retained

/-- Constructor rows keep the available children of their complete source record. -/
theorem constructor_available (state : InternedConstructorTemplates.State Symbol Guard)
    (value : Value Symbol Guard) (available : Available state value)
    (meaning : Guard → Term Symbol → Bool) (edge : Edge (Value Symbol Guard) Symbol)
    (member : edge ∈ constructorRows meaning value) : Values state edge.children := by
  cases value with
  | empty | reference | union | mu => simp [constructorRows] at member
  | node entry edges depth free =>
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      intro child included
      exact available.children child (List.mem_flatMap.mpr ⟨original, present, included⟩)

/-- Equal successor reads on the original available records transport a finite accepting run. -/
theorem accepts_transfer [DecidableEq (EdgeKey Symbol Guard)]
    (base left right : InternedConstructorTemplates.State Symbol Guard)
    (meaning : Guard → Term Symbol → Bool)
    (same : ∀ value, Available base value → successors left value = successors right value)
    (closed : ∀ value, Available base value → Values base (successors left value))
    (value : Value Symbol Guard) (term : Term Symbol)
    (accepted : EpsilonUnion.Accepts (graph left meaning) value term) :
    Available base value → EpsilonUnion.Accepts (graph right meaning) value term := by
  induction accepted using EpsilonUnion.Accepts.rec
    (motive_2 := fun values terms _ => Values base values → All₂ (EpsilonUnion.Accepts (graph right meaning)) values terms) with
  | @reference root target term member accepted ih =>
      intro available
      exact .reference (by simpa only [graph, ← same root available] using member)
        (ih (closed root available target member))
  | @node root edge terms member subtrees guard ih =>
      intro available
      exact .node edge terms member (ih (constructor_available base root available meaning edge member)) guard
  | nil => exact .nil
  | @cons q term qs terms head tail ihHead ihTail =>
      rename_i available
      exact .cons (ihHead (available q List.mem_cons_self))
        (ihTail (fun child member => available child (List.mem_cons_of_mem _ member)))

/-- A prepared available record has the same finite language in the actual later cache. -/
theorem accepts_stable [DecidableEq (EdgeKey Symbol Guard)]
    (before after : InternedConstructorTemplates.State Symbol Guard)
    (outputs : List (Value Symbol Guard)) (context : Context before outputs)
    (growth : Grows before after) (meaning : Guard → Term Symbol → Bool)
    (value : Value Symbol Guard) (available : Available before value) (term : Term Symbol) :
    EpsilonUnion.Accepts (graph after meaning) value term ↔
      EpsilonUnion.Accepts (graph before meaning) value term := by
  have same := successors_stable before after outputs context growth
  have closed := successors_available before outputs context
  constructor
  · intro accepted
    exact accepts_transfer before after before meaning same
      (fun value available => by rw [same value available]; exact closed value available) value term accepted available
  · intro accepted
    exact accepts_transfer before before after meaning (fun value available => (same value available).symm)
      closed value term accepted available

end MicroCFTA.MergedPhysicalUnionTransport
