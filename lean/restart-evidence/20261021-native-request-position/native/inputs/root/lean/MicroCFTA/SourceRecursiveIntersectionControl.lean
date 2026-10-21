import MicroCFTA.SourceRecursiveIntersectionDomain

/-!
# Physical recursive intersection guard order

The control reader uses the actual stored source payloads. It preserves
empty, reset, self, swap, and repeated-pair precedence before Mu, union,
reference, and ordinary payload branches. Unsupported placeholders remain
separate from missing bound-identity lookup.
-/
namespace MicroCFTA.SourceRecursiveIntersectionControl
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedFreshProbeKeys InternedBinderProtocol
open IntersectionFlatMemoKeyDomain

/-- The actual source constructor tags used before identity comparison. -/
def tag : Value Symbol Guard → Nat
  | .empty => 0
  | .node .. => 1
  | .mu .. => 2
  | .union .. => 3
  | .reference .. => 4

/-- Source same-kind comparison retains complete reference tags. -/
def compareValue (left right : Value Symbol Guard) : Ordering :=
  (compare (tag left) (tag right)).then
    (match left, right with
    | .node first .., .node second .. | .mu first .., .mu second .. | .union first .., .union second .. =>
        compare first.identity second.identity
    | .reference first, .reference second => compare first second
    | _, _ => .eq)

/-- Physical operand ordering includes every recursive and union branch. -/
def greater (left right : Value Symbol Guard) : Bool := (compareValue left right).isGT

/-- Only complete nodes and actual RecInt leaves have source node identities. -/
def identity : Value Symbol Guard → Option Nat
  | .node entry .. | .mu entry .. | .union entry .. => some entry.identity
  | .reference (.interned name) => some name
  | _ => none

/-- IntersectId independently orders the actual identities of its two operands. -/
def pair (left right : Nat) : Nat × Nat := (min left right, max left right)

/-- Literal EmptyNode is rejected before either nodeIdentity is forced. -/
def hasEmpty (left right : Value Symbol Guard) : Bool :=
  left.referenceOf == .empty || right.referenceOf == .empty

/-- Closed calls reset a nonempty free environment before the self shortcut. -/
def reset (domain : DomainKey) (left right : Value Symbol Guard) : Bool :=
  left.free.isEmpty && right.free.isEmpty && !domain.free.isEmpty

/-- Canonical source equality and stored closedness select the existing payload. -/
def closedSelf (left right : Value Symbol Guard) : Bool :=
  left.referenceOf == right.referenceOf && left.free.isEmpty

/-- Each source branch remains distinct, including unresolved input placeholders. -/
inductive Branch where
  | empty | reset | self | swap
  | repeated (key : Nat × Nat)
  | bothMu | leftMu | rightMu | leftUnion | rightUnion | leftReference | rightReference | ordinary
  | unsupported
  deriving DecidableEq, Repr

/-- Select the recursive payload only after all preceding source guards fail. -/
def payload (left right : Value Symbol Guard) : Branch :=
  match left, right with
  | .mu .., .mu .. => .bothMu
  | .mu .., _ => .leftMu
  | _, .mu .. => .rightMu
  | .union .., _ => .leftUnion
  | _, .union .. => .rightUnion
  | .reference .., _ => .leftReference
  | _, .reference .. => .rightReference
  | .node .., .node .. => .ordinary
  | _, _ => .unsupported

/-- Read the exact physical source guard order and recursive payload branch. -/
def decision (domain : DomainKey) (left right : Value Symbol Guard) : Branch :=
  if hasEmpty left right then .empty
  else if reset domain left right then .reset
  else if closedSelf left right then .self
  else if greater left right then .swap
  else match identity left, identity right with
  | some first, some second =>
      if pair first second ∈ domain.seen then .repeated (pair first second)
      else payload left right
  | _, _ => .unsupported

/-- The repeated-pair branch returns the actual source RecIntersect placeholder. -/
def repeatedValue (key : Nat × Nat) : Value Symbol Guard := .reference (.intersection key.1 key.2)

/-- Physical source equality identifies the complete self result at a coherent cache. -/
theorem self_record (state : State Symbol Guard) (facts : Facts state)
    (left right : Value Symbol Guard) (leftAvailable : Available state left) (rightAvailable : Available state right)
    (same : closedSelf left right = true) : left = right := by
  have equal : left.referenceOf = right.referenceOf := by
    simp only [closedSelf, Bool.and_eq_true, beq_iff_eq] at same
    exact same.1
  exact resident_reference_injective state facts.coherent left right leftAvailable.resident rightAvailable.resident equal

/-- Empty rejection precedes every domain and recursive payload read. -/
theorem empty_first (domain : DomainKey) (left right : Value Symbol Guard) (empty : hasEmpty left right = true) :
    decision domain left right = .empty := by simp only [decision, empty, ite_true]

/-- Reset precedes self, ordering, and repeated-pair cutoff. -/
theorem reset_first (domain : DomainKey) (left right : Value Symbol Guard) (empty : hasEmpty left right = false)
    (restart : reset domain left right = true) : decision domain left right = .reset := by
  simp [decision, empty, restart]

/-- Closed self reuse precedes ordering and all recursive requests. -/
theorem self_first (domain : DomainKey) (left right : Value Symbol Guard) (empty : hasEmpty left right = false)
    (restart : reset domain left right = false) (same : closedSelf left right = true) :
    decision domain left right = .self := by simp [decision, empty, restart, same]

/-- Source operand sorting precedes repeated-pair cutoff. -/
theorem swap_first (domain : DomainKey) (left right : Value Symbol Guard) (empty : hasEmpty left right = false)
    (restart : reset domain left right = false) (same : closedSelf left right = false) (swap : greater left right = true) :
    decision domain left right = .swap := by simp [decision, empty, restart, same, swap]

/-- A repeated actual pair is selected before Mu exposure, union expansion, and free lookup. -/
theorem repeated_first (domain : DomainKey) (left right : Value Symbol Guard)
    (empty : hasEmpty left right = false) (restart : reset domain left right = false)
    (same : closedSelf left right = false) (swap : greater left right = false)
    (first second : Nat) (leftId : identity left = some first) (rightId : identity right = some second)
    (seen : pair first second ∈ domain.seen) : decision domain left right = .repeated (pair first second) := by
  simp [decision, empty, restart, same, swap, leftId, rightId, seen]

/-- Recursive cutoff names retain independent canonical operand identity order. -/
theorem repeated_symmetric (left right : Nat) :
    repeatedValue (Symbol := Symbol) (Guard := Guard) (pair left right) = repeatedValue (pair right left) := by
  simp only [pair, Nat.min_comm, Nat.max_comm]

/-- Source RecIntersect placeholders bypass the native node memo table. -/
theorem repeated_unmemoized (key : Nat × Nat) :
    IntersectionFlatMemoKey.input (repeatedValue (Symbol := Symbol) (Guard := Guard) key).referenceOf = none := rfl

end MicroCFTA.SourceRecursiveIntersectionControl
