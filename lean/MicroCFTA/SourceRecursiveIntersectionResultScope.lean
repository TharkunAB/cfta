import MicroCFTA.SourceRecursiveIntersectionMaybeMuFreeSupport
import MicroCFTA.SourceRecursiveIntersectionKernelReadback
import MicroCFTA.SourceRecursiveIntersectionSemanticHeap

/-!
# Recursive result names belong to the incoming seen pairs

Ordinary constructors retain only their actual child names. An optional
binder removes its selected pair from the body's possible names. These
local laws retain actual constructor readback and complete source contexts.
-/
namespace MicroCFTA.SourceRecursiveIntersectionResultScope
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol (Reference)
open SourceRecursiveIntersectionControl

/-- Every free name is an intersection reference from the specified recursive pair set. -/
def Scope (pairs : List (Nat × Nat)) (value : Value Symbol Guard) : Prop :=
  ∀ name ∈ value.free, ∃ pair ∈ pairs, name = .intersection pair.1 pair.2

/-- Every actual ordered edge child has the same possible recursive pair names. -/
def EdgeScope (pairs : List (Nat × Nat)) (edge : EdgeValue Symbol Guard) : Prop :=
  ∀ child ∈ edge.children, Scope pairs child

/-- A closed result has no free-name obligation for any incoming pair set. -/
theorem closed (pairs : List (Nat × Nat)) (value : Value Symbol Guard) (free : value.free = []) : Scope pairs value := by
  intro name member
  rw [free] at member
  cases member

/-- Empty incoming scope forces an actual result's cached free-name list to be empty. -/
theorem empty_scope (value : Value Symbol Guard) (scope : Scope [] value) : value.free = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro name member
  obtain ⟨pair, impossible, _⟩ := scope name member
  cases impossible

/-- Enlarging the incoming pair set retains the same result scope. -/
theorem weaken (first second : List (Nat × Nat)) (included : ∀ pair ∈ first, pair ∈ second)
    (value : Value Symbol Guard) (scope : Scope first value) : Scope second value := by
  intro name member
  obtain ⟨pair, present, same⟩ := scope name member
  exact ⟨pair, included pair present, same⟩

/-- The actual repeated-pair leaf has precisely the allowed intersection name. -/
theorem repeated (pairs : List (Nat × Nat)) (pair : Nat × Nat) (member : pair ∈ pairs) :
    Scope pairs (repeatedValue (Symbol := Symbol) (Guard := Guard) pair) := by
  intro name included
  simp only [repeatedValue, Value.free, List.mem_singleton] at included
  exact ⟨pair, member, included⟩

/-- Actual optional-binder completion removes the newly inserted pair from result scope. -/
theorem optionalBinder [DecidableEq (EdgeKey Symbol Guard)] (pairs : List (Nat × Nat)) (pair : Nat × Nat)
    (body : Value Symbol Guard) (state : State Symbol Guard) (context : InternedFreshOrdinaryContext.Context state captures)
    (available : Available state body) (bodyScope : Scope (pair :: pairs) body)
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (done : SourceRecursiveIntersectionMaybeMu.maybeMu pair body state = .done value after) : Scope pairs value := by
  intro name member
  have support := SourceRecursiveIntersectionMaybeMu.free_support pair body state context available value after done name member
  obtain ⟨original, present, same⟩ := bodyScope name support.1
  rcases List.mem_cons.mp present with equal | old
  · subst original
    exact False.elim (support.2 same)
  · exact ⟨original, old, same⟩

/-- Actual edge readback retains the scopes of its original ordered children. -/
theorem edge [DecidableEq (EdgeKey Symbol Guard)] (pairs : List (Nat × Nat)) (symbol : Symbol) (guard : Guard)
    (values : List (Value Symbol Guard)) (state : State Symbol Guard) (facts : InternedNestedFacts.Facts state)
    (available : ∀ value ∈ values, Available state value) (scope : ∀ value ∈ values, Scope pairs value) :
    EdgeScope pairs (run (makeEdge symbol guard values) state).1 := by
  rw [EdgeScope, InternedShallowValues.makeEdge_children symbol guard values state facts.coherent facts.cached available]
  exact scope

/-- Actual node normalization retains only names from surviving original edge children. -/
theorem node [DecidableEq (EdgeKey Symbol Guard)] (pairs : List (Nat × Nat)) (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (facts : InternedNestedFacts.Facts state)
    (resident : ∀ edge ∈ edges, EdgeResident state edge) (scope : ∀ edge ∈ edges, EdgeScope pairs edge) :
    Scope pairs (run (makeNode edges) state).1 := by
  intro name member
  rw [InternedNormalizationFree.makeNode_free edges state facts.coherent facts.linked resident, childFree_member] at member
  obtain ⟨child, included, named⟩ := member
  obtain ⟨edge, selected, inside⟩ := List.mem_flatMap.mp included
  have original := (List.mem_filter.mp (canonicalEdges_member _ edge selected)).1
  exact scope edge original child inside name named

/-- Actual union normalization retains only names from its available original operands. -/
theorem union [DecidableEq (EdgeKey Symbol Guard)] (pairs : List (Nat × Nat)) (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (normal : InternedStoredMuOrigins.Normal state)
    (available : ∀ value ∈ values, Available state value) (scope : ∀ value ∈ values, Scope pairs value) :
    Scope pairs (run (makeUnion values) state).1 := by
  intro name member
  obtain ⟨value, included, named⟩ := (InternedNormalizationFree.makeUnion_free values state normal.facts.coherent normal.facts.cached
    normal.facts.linked normal.live available name).mp member
  exact scope value included name named

/-- The source self branch can return only a value with an empty cached free-name list. -/
theorem self_closed (domain : IntersectionFlatMemoKeyDomain.DomainKey) (left right : Value Symbol Guard)
    (selected : decision domain left right = .self) : left.free = [] := by
  unfold decision at selected
  split at selected
  · cases selected
  · split at selected
    · cases selected
    · split at selected
      · rename_i same
        simp only [closedSelf, Bool.and_eq_true] at same
        exact List.isEmpty_iff.mp same.2
      · split at selected
        · cases selected
        · split at selected
          · split at selected
            · cases selected
            · cases left <;> cases right <;> simp only [payload] at selected <;> cases selected
          · cases selected

/-- The source repeated-pair branch returns a pair already present in the incoming domain. -/
theorem repeated_seen (domain : IntersectionFlatMemoKeyDomain.DomainKey) (left right : Value Symbol Guard) (pair : Nat × Nat)
    (selected : decision domain left right = .repeated pair) : pair ∈ domain.seen := by
  unfold decision at selected
  split at selected
  · cases selected
  · split at selected
    · cases selected
    · split at selected
      · cases selected
      · split at selected
        · cases selected
        · split at selected
          · split at selected
            · cases selected
              assumption
            · cases left <;> cases right <;> simp only [payload] at selected <;> cases selected
          · cases selected

end MicroCFTA.SourceRecursiveIntersectionResultScope
