import MicroCFTA.SourceRecursiveIntersectionDomainInventory
import MicroCFTA.SourceRecursiveIntersectionRequestScope
import MicroCFTA.SourceRecursiveIntersectionNativeCapacity

/-!
# Domain and request keys from one original source heap

The initial issued node range supplies binder names and operand pairs.
Actual Mu entry stays inside its finite canonical domain inventory.
Request word checks use original operand counters. They do not bound
constructor results or later heap supplies.
-/
namespace MicroCFTA.SourceRecursiveIntersectionSourceInventory
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionDomainInventory
variable {Symbol Guard : Type}

/-- The initial issued range contains every available original binder identity. -/
def names (source : InternedConstructorTemplates.State Symbol Guard) : List Nat :=
  List.range source.nodes.next

/-- The initial range supplies every independently sorted source operand pair. -/
def pairs (source : InternedConstructorTemplates.State Symbol Guard) : List (Nat × Nat) :=
  (names source).flatMap fun left => (names source).map (SourceRecursiveIntersectionControl.pair left)

/-- All canonical domains use subsets of the initial identities and pairs. -/
def domains (source : InternedConstructorTemplates.State Symbol Guard) : List DomainKey :=
  inventory (names source) (pairs source)

/-- An actual available identity belongs to the initial issued range. -/
theorem identity_mem (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (value : Value Symbol Guard) (available : Available source value) (identity : Nat)
    (selected : SourceRecursiveIntersectionControl.identity value = some identity) : identity ∈ names source := by
  apply List.mem_range.mpr
  cases value with
  | empty => cases selected
  | node entry edges depth free | mu entry edges depth free | union entry edges depth free =>
      cases selected
      exact IntersectionFlatMemoKeyPhysical.entry_bounded source facts _ available entry rfl
  | reference reference =>
      cases reference with
      | interned name =>
          cases selected
          exact IntersectionFlatMemoKeyPhysical.reference_bounded source facts name available
      | uninterned | depth | intersection | state => cases selected

/-- Each actual sorted pair of initial identities belongs to the finite pair carrier. -/
theorem pair_mem (source : InternedConstructorTemplates.State Symbol Guard) (left right : Nat)
    (first : left ∈ names source) (second : right ∈ names source) :
    SourceRecursiveIntersectionControl.pair left right ∈ pairs source := by
  exact List.mem_flatMap.mpr ⟨left, first, List.mem_map.mpr ⟨right, second, rfl⟩⟩

/-- Actual complete source operands supply their remembered recursive pair. -/
theorem operand_pair_mem (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (left right : Value Symbol Guard) (leftAvailable : Available source left) (rightAvailable : Available source right)
    (first second : Nat) (leftId : SourceRecursiveIntersectionControl.identity left = some first)
    (rightId : SourceRecursiveIntersectionControl.identity right = some second) :
    SourceRecursiveIntersectionControl.pair first second ∈ pairs source :=
  pair_mem source first second (identity_mem source facts left leftAvailable first leftId)
    (identity_mem source facts right rightAvailable second rightId)

/-- Every Mu binding added by the source has an initial issued identity. -/
theorem binding_mem (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (left right : Value Symbol Guard) (leftAvailable : Available source left) (rightAvailable : Available source right)
    (binding : Nat × Value Symbol Guard) (member : binding ∈ SourceRecursiveIntersectionEnvironment.bindings left right) :
    binding.1 ∈ names source := by
  obtain ⟨entry, body, depth, ordinary, same, available⟩ :=
    SourceRecursiveIntersectionEnvironment.bindings_available source left right leftAvailable rightAvailable binding member
  rw [same]
  exact identity_mem source facts (.mu entry body depth ordinary) available entry.identity rfl

/-- The complete actual Mu binding list uses only initial names. -/
theorem bound_names (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (left right : Value Symbol Guard) (leftAvailable : Available source left) (rightAvailable : Available source right) :
    ∀ name ∈ (SourceRecursiveIntersectionEnvironment.bindings left right).map Prod.fst, name ∈ names source := by
  intro name member
  obtain ⟨binding, member, rfl⟩ := List.mem_map.mp member
  exact binding_mem source facts left right leftAvailable rightAvailable binding member

/-- Actual source Mu extension retains membership in the initial domain inventory. -/
theorem extend_mem (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (key : DomainKey) (member : key ∈ domains source)
    (left right : Value Symbol Guard) (leftAvailable : Available source left) (rightAvailable : Available source right)
    (first second : Nat) (leftId : SourceRecursiveIntersectionControl.identity left = some first)
    (rightId : SourceRecursiveIntersectionControl.identity right = some second) :
    SourceRecursiveIntersectionDomain.extend key ((SourceRecursiveIntersectionEnvironment.bindings left right).map Prod.fst)
      (SourceRecursiveIntersectionControl.pair first second) ∈ domains source :=
  SourceRecursiveIntersectionDomainInventory.extend_mem member _ _
    (bound_names source facts left right leftAvailable rightAvailable)
    (operand_pair_mem source facts left right leftAvailable rightAvailable first second leftId rightId)

/-- The reserved empty domain is included before any query executes. -/
theorem empty_mem (source : InternedConstructorTemplates.State Symbol Guard) :
    IntersectionEmptyDomain.emptyKey ∈ domains source :=
  SourceRecursiveIntersectionDomainInventory.empty_mem _ _

/-- The finite pair carrier has the square of the original issued range length. -/
theorem pairs_length (source : InternedConstructorTemplates.State Symbol Guard) :
    (pairs source).length = source.nodes.next * source.nodes.next := by
  have length (values : List Nat) :
      (values.flatMap fun left => (names source).map (SourceRecursiveIntersectionControl.pair left)).length =
        values.length * (names source).length := by
    induction values with
    | nil => simp
    | cons head tail ih => simp [ih, Nat.add_mul, Nat.add_comm]
  simpa [pairs, names] using length (names source)

/-- The initial heap computes a conservative finite domain budget. -/
theorem domains_length (source : InternedConstructorTemplates.State Symbol Guard) :
    (domains source).length = 2 ^ (source.nodes.next + source.nodes.next * source.nodes.next) := by
  rw [domains, inventory_length, pairs_length]
  simp [names]

/-- Literal domain allocation returns exactly an inventory key from actual original operands. -/
theorem entered_mem (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (cache : Cache.State DomainKey) (valid : Cache.Valid cache)
    (domain : Interned DomainKey) (member : domain.key ∈ domains source)
    (left right : Value Symbol Guard) (leftAvailable : Available source left) (rightAvailable : Available source right)
    (first second : Nat) (leftId : SourceRecursiveIntersectionControl.identity left = some first)
    (rightId : SourceRecursiveIntersectionControl.identity right = some second) :
    (SourceRecursiveIntersectionEnvironment.enter cache domain.key left right first second).1.key ∈ domains source := by
  have checked := (IntersectionEmptyDomain.make_correct cache valid
    (SourceRecursiveIntersectionDomain.extend domain.key
      ((SourceRecursiveIntersectionEnvironment.bindings left right).map Prod.fst)
      (SourceRecursiveIntersectionControl.pair first second))).2.1
  rw [show (SourceRecursiveIntersectionEnvironment.enter cache domain.key left right first second).1.key = _ from checked]
  exact extend_mem source facts domain.key member left right leftAvailable rightAvailable first second leftId rightId

/-- Original node operands use the initial tagged-key supply at any bounded domain identity. -/
theorem node_key_safe (bits : Nat) (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (nodes : source.nodes.next < 2 ^ bits) (request : NodeRequest Symbol Guard) (scope : NodeScope source request)
    (domain : request.domain.identity < 2 ^ (bits + 1)) (key : Triple (bits + 2))
    (memoized : SourceRecursiveIntersectionMemo.requestKey (bits + 2) request.domain request.left request.right = some key) :
    SourceRecursiveIntersectionMemo.KeySafe (bits + 2) request.domain request.left request.right := by
  cases first : IntersectionFlatMemoKey.input request.left.referenceOf with
  | none => simp [SourceRecursiveIntersectionMemo.requestKey, sourceKey, IntersectionFlatMemoKey.key, first] at memoized
  | some left =>
      cases second : IntersectionFlatMemoKey.input request.right.referenceOf with
      | none => simp [SourceRecursiveIntersectionMemo.requestKey, sourceKey, IntersectionFlatMemoKey.key, second] at memoized
      | some right =>
          refine ⟨by omega, ?_, left, right, first, second, ?_, ?_⟩
          · simpa only [show bits + 2 - 1 = bits + 1 from by omega] using domain
          · exact IntersectionFlatMemoKeyPhysical.available_safe bits source facts nodes request.left scope.leftAvailable left first
          · exact IntersectionFlatMemoKeyPhysical.available_safe bits source facts nodes request.right scope.rightAvailable right second

/-- Original resident row identities use the initial edge supply at any bounded domain identity. -/
theorem edge_key_safe (bits : Nat) (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (edges : source.edges.next ≤ 2 ^ (bits + 2)) (request : EdgeRequest Symbol Guard) (scope : EdgeScope source request)
    (domain : request.domain.identity < 2 ^ (bits + 1)) :
    SourceRecursiveIntersectionEdgeMemo.KeySafe (bits + 2) request.domain request.left request.right := by
  have bounded (edge : EdgeValue Symbol Guard) (resident : EdgeResident source edge) : edge.entry.identity < source.edges.next := by
    have stored := (facts.coherent.edges edge.entry.key edge resident).1
    exact facts.coherent.valid.1.1 edge.entry.identity edge.entry.key
      ((facts.coherent.valid.1.2 edge.entry.key edge.entry stored).2)
  refine ⟨by omega, ?_, Nat.lt_of_lt_of_le (bounded request.left scope.leftResident) edges,
    Nat.lt_of_lt_of_le (bounded request.right scope.rightResident) edges⟩
  simpa only [show bits + 2 - 1 = bits + 1 from by omega] using domain

end MicroCFTA.SourceRecursiveIntersectionSourceInventory
