import MicroCFTA.InternedSourceCrushInventory

/-!
# Physical reachability and visited-fold summaries

The semantic graph follows source children and stops at bare references.
Each summary records reached identities, closure of fresh records, and
the exact local checks for newly visited records. Canonical coherence
identifies complete immutable records with the same node identity.
-/
namespace MicroCFTA.InternedSourceCrush
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedBinderProtocol (NodeKey)
open InternedEdgeResidency (nodeEdges)

/-- Source traversal children exclude both stored Mu probes. -/
def sourceChildren : Value Symbol Guard → List (Value Symbol Guard)
  | .empty | .reference _ => []
  | .node _ edges _ _ => edges.flatMap EdgeValue.children
  | .union _ members _ _ => members
  | .mu _ body _ _ => [body]

/-- The source local Boolean checks only the current ordinary record's edges. -/
def localPlain (plain : Guard → Bool) (value : Value Symbol Guard) : Bool :=
  (nodeEdges value).all fun edge => plain edge.entry.key.constraint

/-- Physical descendants follow source bodies, ordinary children, and union members. -/
inductive Reaches (roots : List (Value Symbol Guard)) : Value Symbol Guard → Prop where
  | root (value : Value Symbol Guard) (member : value ∈ roots) : Reaches roots value
  | child (parent child : Value Symbol Guard) (reached : Reaches roots parent)
      (member : child ∈ sourceChildren parent) : Reaches roots child

/-- Replacing starting roots by reached roots preserves every physical descendant. -/
theorem Reaches.mono (included : ∀ value ∈ roots, Reaches target value) (reached : Reaches roots value) :
    Reaches target value := by
  induction reached with
  | root value member => exact included value member
  | child parent child reached member ih => exact .child parent child ih member

/-- A canonical newly visited identity satisfies a property of its complete available record. -/
def Added (state : State Symbol Guard) (before after : List Nat) (property : Value Symbol Guard → Prop) : Prop :=
  ∀ value entry, Available state value → entryOf value = some entry → entry.identity ∈ after → entry.identity ∉ before → property value

/-- Predicate implication transports newly visited complete-record properties. -/
theorem Added.mono (added : Added state before after property)
    (implies : ∀ value, property value → later value) : Added state before after later :=
  fun value entry available field member fresh => implies value (added value entry available field member fresh)

/-- Consecutive visited-set extensions compose newly visited record properties. -/
theorem Added.trans (first : Added state before middle property) (second : Added state middle after property) : Added state before after property := by
  intro value entry available field member fresh
  by_cases earlier : entry.identity ∈ middle
  · exact first value entry available field earlier fresh
  · exact second value entry available field member earlier

/-- Restricting fresh records to a larger initial visited set preserves each local property. -/
theorem Added.restrict (added : Added state before after property) (growth : before ⊆ middle) :
    Added state middle after property := by
  intro value entry available field member fresh
  exact added value entry available field member (fun old => fresh (growth old))

/-- A completed fresh record has every immediate source child identity in the final visited set. -/
def ClosedAt (seen : List Nat) (value : Value Symbol Guard) : Prop :=
  ∀ child ∈ sourceChildren value, ∀ entry, entryOf child = some entry → entry.identity ∈ seen

/-- Later visited sets preserve every completed record's source-child coverage. -/
theorem ClosedAt.grows (closed : ClosedAt before value) (growth : before ⊆ after) : ClosedAt after value :=
  fun child member entry field => growth (closed child member entry field)

/-- The complete fold summary keeps exact roots, fresh closure, origin, and Boolean checks. -/
structure Summary (plain : Guard → Bool) (state : State Symbol Guard)
    (roots : List (Value Symbol Guard)) (seen : List Nat) (result : Bool × List Nat) : Prop where
  entered : ∀ value ∈ roots, ∀ entry, entryOf value = some entry → entry.identity ∈ result.2
  closed : Added state seen result.2 (ClosedAt result.2)
  origins : Added state seen result.2 (Reaches roots)
  checked : result.1 = true ↔ Added state seen result.2 (fun value => localPlain plain value = true)

/-- Empty input lists require no new record check. -/
theorem nil_summary (plain : Guard → Bool) (state : State Symbol Guard) (seen : List Nat) :
    Summary plain state [] seen (true, seen) := by
  refine ⟨by simp, ?_, ?_, ?_⟩
  · intro value entry available field member fresh; exact False.elim (fresh member)
  · intro value entry available field member fresh; exact False.elim (fresh member)
  · exact ⟨fun _ value entry available field member fresh => False.elim (fresh member), fun _ => rfl⟩

/-- Empty records and bare references contribute no canonical node or local constraint. -/
theorem primitive_summary (plain : Guard → Bool) (state : State Symbol Guard) (value : Value Symbol Guard)
    (seen : List Nat) (primitive : entryOf value = none) : Summary plain state [value] seen (true, seen) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro other member entry field
    have same : other = value := List.mem_singleton.mp member
    subst other
    rw [primitive] at field
    cases field
  · intro value entry available field member fresh; exact False.elim (fresh member)
  · intro value entry available field member fresh; exact False.elim (fresh member)
  · exact ⟨fun _ value entry available field member fresh => False.elim (fresh member), fun _ => rfl⟩

/-- A previously visited root inserts nothing and performs no new local check. -/
theorem seen_summary (plain : Guard → Bool) (state : State Symbol Guard) (value : Value Symbol Guard)
    (entry : Interned NodeKey) (field : entryOf value = some entry) (seen : List Nat) (visited : entry.identity ∈ seen) :
    Summary plain state [value] seen (true, seen) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro other member actual otherField
    have same : other = value := List.mem_singleton.mp member
    subst other
    have equal := Option.some.inj (field.symm.trans otherField)
    exact equal ▸ visited
  · intro value entry available field member fresh; exact False.elim (fresh member)
  · intro value entry available field member fresh; exact False.elim (fresh member)
  · exact ⟨fun _ value entry available field member fresh => False.elim (fresh member), fun _ => rfl⟩

/-- Sequential child scans compose complete summaries in their exact returned visited sets. -/
theorem sequence_summary (plain : Guard → Bool) (state : State Symbol Guard)
    (firstRoots secondRoots : List (Value Symbol Guard)) (seen : List Nat) (first second : Bool × List Nat)
    (head : Summary plain state firstRoots seen first) (tail : Summary plain state secondRoots first.2 second)
    (headGrowth : seen ⊆ first.2) (tailGrowth : first.2 ⊆ second.2) :
    Summary plain state (firstRoots ++ secondRoots) seen (first.1 && second.1, second.2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro value member entry field
    rcases List.mem_append.mp member with left | right
    · exact tailGrowth (head.entered value left entry field)
    · exact tail.entered value right entry field
  · exact (head.closed.mono (fun value closed => closed.grows tailGrowth)).trans tail.closed
  · refine Added.trans (property := Reaches (firstRoots ++ secondRoots)) (head.origins.mono ?_) (tail.origins.mono ?_)
    · intro value reached
      exact reached.mono (fun value member => .root value (List.mem_append_left _ member))
    · intro value reached
      exact reached.mono (fun value member => .root value (List.mem_append_right _ member))
  · rw [Bool.and_eq_true, head.checked, tail.checked]
    constructor
    · rintro ⟨first, second⟩; exact first.trans second
    · intro all
      refine ⟨?_, all.restrict headGrowth⟩
      intro value entry available field member fresh
      exact all value entry available field (tailGrowth member) fresh

end MicroCFTA.InternedSourceCrush
