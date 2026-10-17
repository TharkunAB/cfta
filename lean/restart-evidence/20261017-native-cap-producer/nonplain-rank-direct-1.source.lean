import MicroCFTA.SourceCurrentConstrainedCapNativeScope

/-!
# Structural descent outside hereditary native operands

The rank is zero on hereditary values. Otherwise it is the complete stored
record size. Ordinary child and union-member requests decrease this rank
when the selected parent is not hereditary. Local source Mu reads have
rank zero. This proof-only measure does not assert query completion.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapNonplainRank
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceEqualityAnnotationLanguage
open SourceCurrentConstrainedCap (Cap)
open SourceCurrentHereditaryNativeScope (Bindings)
variable {Symbol Guard : Type}

/-- Only nonhereditary stored records contribute structural size. -/
noncomputable def rank (annotation : Guard → Prop) (value : Value Symbol Guard) : Nat := by
  classical
  exact if Annotated annotation value then 0 else sizeOf value

/-- An ordered request adds the two original operand ranks. -/
noncomputable def pairRank (annotation : Guard → Prop) (left right : Value Symbol Guard) : Nat :=
  rank annotation left + rank annotation right

/-- Every complete stored record has positive structural size. -/
theorem size_positive (value : Value Symbol Guard) : 0 < sizeOf value := by
  cases value <;> simp only [Value.empty.sizeOf_spec, Value.reference.sizeOf_spec, Value.node.sizeOf_spec,
    Value.union.sizeOf_spec, Value.mu.sizeOf_spec] <;> omega

/-- A rank of zero is exactly the local hereditary annotation predicate. -/
theorem rank_zero_iff (annotation : Guard → Prop) (value : Value Symbol Guard) :
    rank annotation value = 0 ↔ Annotated annotation value := by
  classical
  by_cases annotated : Annotated annotation value
  · simp only [rank, if_pos annotated, annotated, iff_true]
  · have positive := size_positive value
    simp only [rank, if_neg annotated]
    exact ⟨fun zero => by omega, fun impossible => (annotated impossible).elim⟩

/-- A nonhereditary operand retains its complete original structural size. -/
theorem rank_of_nonplain (annotation : Guard → Prop) (value : Value Symbol Guard)
    (nonplain : ¬ Annotated annotation value) : rank annotation value = sizeOf value := by
  classical
  simp only [rank, if_neg nonplain]

/-- Rank never exceeds the original complete record size. -/
theorem rank_le_size (annotation : Guard → Prop) (value : Value Symbol Guard) : rank annotation value ≤ sizeOf value := by
  classical
  by_cases annotated : Annotated annotation value <;> simp [rank, annotated]

private theorem child_size {parent : Value Symbol Guard} {edge : EdgeValue Symbol Guard}
    (selected : edge ∈ nodeEdges parent) {child : Value Symbol Guard} (member : child ∈ edge.children) :
    sizeOf child < sizeOf parent := by
  cases parent <;> simp only [nodeEdges] at selected <;> try contradiction
  case node entry edges depth free =>
    have outer := List.sizeOf_lt_of_mem selected
    cases edge with
    | mk edgeEntry children =>
        have inner := List.sizeOf_lt_of_mem member
        simp only [Value.node.sizeOf_spec, EdgeValue.mk.sizeOf_spec, EdgeValue.children] at *
        omega

/-- An actual ordinary child is strictly lower when its parent is nonhereditary. -/
theorem child_lt (annotation : Guard → Prop) (parent : Value Symbol Guard)
    (nonplain : ¬ Annotated annotation parent) (edge : EdgeValue Symbol Guard)
    (selected : edge ∈ nodeEdges parent) (child : Value Symbol Guard) (member : child ∈ edge.children) :
    rank annotation child < rank annotation parent := by
  rw [rank_of_nonplain annotation parent nonplain]
  exact Nat.lt_of_le_of_lt (rank_le_size annotation child) (child_size selected member)

/-- Every actual ordinary child is nonincreasing, including hereditary parent regions. -/
theorem child_le (annotation : Guard → Prop) (parent : Value Symbol Guard) (edge : EdgeValue Symbol Guard)
    (selected : edge ∈ nodeEdges parent) (child : Value Symbol Guard) (member : child ∈ edge.children) :
    rank annotation child ≤ rank annotation parent := by
  classical
  by_cases annotated : Annotated annotation parent
  · have inherited := (SourceCurrentHereditaryConstructors.node_edge annotated edge selected).2 child member
    rw [(rank_zero_iff annotation parent).mpr annotated, (rank_zero_iff annotation child).mpr inherited]
  · exact Nat.le_of_lt (child_lt annotation parent annotated edge selected child member)

private theorem member_size (entry : Interned NodeKey) (members : List (Value Symbol Guard)) (depth : Nat)
    (free : List Reference) (child : Value Symbol Guard) (member : child ∈ members) :
    sizeOf child < sizeOf (Value.union entry members depth free) := by
  have inside := List.sizeOf_lt_of_mem member
  simp only [Value.union.sizeOf_spec]
  omega

/-- A selected union member is strictly lower when that stored union is nonhereditary. -/
theorem union_member_lt (annotation : Guard → Prop) (entry : Interned NodeKey)
    (members : List (Value Symbol Guard)) (depth : Nat) (free : List Reference)
    (nonplain : ¬ Annotated annotation (.union entry members depth free))
    (child : Value Symbol Guard) (member : child ∈ members) :
    rank annotation child < rank annotation (.union entry members depth free) := by
  rw [rank_of_nonplain annotation _ nonplain]
  exact Nat.lt_of_le_of_lt (rank_le_size annotation child) (member_size entry members depth free child member)

/-- Every stored union member is nonincreasing at its original request. -/
theorem union_member_le (annotation : Guard → Prop) (entry : Interned NodeKey)
    (members : List (Value Symbol Guard)) (depth : Nat) (free : List Reference)
    (child : Value Symbol Guard) (member : child ∈ members) :
    rank annotation child ≤ rank annotation (.union entry members depth free) := by
  classical
  by_cases annotated : Annotated annotation (.union entry members depth free)
  · have inherited := SourceCurrentHereditaryConstructors.union_member annotation _ annotated child member
    rw [(rank_zero_iff annotation _).mpr annotated, (rank_zero_iff annotation child).mpr inherited]
  · exact Nat.le_of_lt (union_member_lt annotation entry members depth free annotated child member)

/-- Actual source body projection does not increase the original operand rank. -/
theorem body_le (annotation : Guard → Prop) (value : Value Symbol Guard) :
    rank annotation (SourceRecursiveIntersectionKernel.body value) ≤ rank annotation value := by
  classical
  cases value with
  | mu entry body depth ordinary =>
      by_cases annotated : Annotated annotation (.mu entry body depth ordinary)
      · have inherited := SourceCurrentHereditaryNativeScope.body_annotated annotation _ annotated
        rw [(rank_zero_iff annotation _).mpr annotated, (rank_zero_iff annotation _).mpr inherited]
      · rw [rank_of_nonplain annotation _ annotated]
        have smaller := rank_le_size annotation body
        simp only [SourceRecursiveIntersectionKernel.body, Value.mu.sizeOf_spec]
        omega
  | empty | reference | node | union => exact Nat.le_refl _

/-- A capped source Mu and its actual stored body both have rank zero. -/
theorem capped_mu_zero (annotation : Guard → Prop) (depth : Nat) (entry) (body level ordinary : Value Symbol Guard)
    (bounded : Cap annotation depth (.mu entry body level ordinary)) :
    rank annotation (.mu entry body level ordinary) = 0 ∧ rank annotation body = 0 := by
  have annotated := SourceCurrentConstrainedCapNativeScope.mu_annotated bounded
  exact ⟨(rank_zero_iff annotation _).mpr annotated,
    (rank_zero_iff annotation _).mpr (SourceCurrentHereditaryNativeScope.body_annotated annotation _ annotated)⟩

/-- Swapping the complete ordered request preserves its rank. -/
theorem pair_swap (annotation : Guard → Prop) (left right : Value Symbol Guard) :
    pairRank annotation left right = pairRank annotation right left := Nat.add_comm _ _

/-- Actual body callbacks do not increase the combined original operand rank. -/
theorem body_pair_le (annotation : Guard → Prop) (left right : Value Symbol Guard) :
    pairRank annotation (SourceRecursiveIntersectionKernel.body left) (SourceRecursiveIntersectionKernel.body right) ≤
      pairRank annotation left right := Nat.add_le_add (body_le annotation left) (body_le annotation right)

/-- Zipped ordinary child requests decrease when either complete parent is nonhereditary. -/
theorem zip_pair_lt (annotation : Guard → Prop) (left right : Value Symbol Guard)
    (nonplain : ¬ Annotated annotation left ∨ ¬ Annotated annotation right)
    (first second : EdgeValue Symbol Guard) (firstMember : first ∈ nodeEdges left) (secondMember : second ∈ nodeEdges right)
    (children : Value Symbol Guard × Value Symbol Guard) (member : children ∈ first.children.zip second.children) :
    pairRank annotation children.1 children.2 < pairRank annotation left right := by
  have inside := List.of_mem_zip member
  have leftBound := child_le annotation left first firstMember children.1 inside.1
  have rightBound := child_le annotation right second secondMember children.2 inside.2
  rcases nonplain with firstNonplain | secondNonplain
  · have strict := child_lt annotation left firstNonplain first firstMember children.1 inside.1
    exact Nat.add_lt_add_of_lt_of_le strict rightBound
  · have strict := child_lt annotation right secondNonplain second secondMember children.2 inside.2
    exact Nat.add_lt_add_of_le_of_lt leftBound strict

/-- A left-union callback strictly decreases at each actual member of a nonhereditary union. -/
theorem left_union_pair_lt (annotation : Guard → Prop) (entry : Interned NodeKey)
    (members : List (Value Symbol Guard)) (depth : Nat) (free : List Reference)
    (nonplain : ¬ Annotated annotation (.union entry members depth free))
    (child : Value Symbol Guard) (member : child ∈ members) (right : Value Symbol Guard) :
    pairRank annotation child right < pairRank annotation (.union entry members depth free) right :=
  Nat.add_lt_add_right (union_member_lt annotation entry members depth free nonplain child member) _

/-- A right-union callback strictly decreases at each actual member of a nonhereditary union. -/
theorem right_union_pair_lt (annotation : Guard → Prop) (left : Value Symbol Guard) (entry : Interned NodeKey)
    (members : List (Value Symbol Guard)) (depth : Nat) (free : List Reference)
    (nonplain : ¬ Annotated annotation (.union entry members depth free))
    (child : Value Symbol Guard) (member : child ∈ members) :
    pairRank annotation left child < pairRank annotation left (.union entry members depth free) :=
  Nat.add_lt_add_left (union_member_lt annotation entry members depth free nonplain child member) _

/-- Replacing a hereditary source reference by its hereditary bound value preserves the pair rank. -/
theorem hereditary_left_eq (annotation : Guard → Prop) (first second right : Value Symbol Guard)
    (firstAnnotated : Annotated annotation first) (secondAnnotated : Annotated annotation second) :
    pairRank annotation first right = pairRank annotation second right := by
  simp only [pairRank, (rank_zero_iff annotation first).mpr firstAnnotated, (rank_zero_iff annotation second).mpr secondAnnotated]

/-- Every legitimate local bound-name read returns rank zero at the exact current source record. -/
theorem binding_read_zero (annotation : Guard → Prop) (source current : State Symbol Guard)
    (facts : InternedNestedFacts.Facts current) (growth : Grows source current)
    (history : Extends source.nodes.issued current.nodes.issued) (domain : DomainKey)
    (known : Bindings annotation source domain) (name : Nat) (member : name ∈ SourceRecursiveIntersectionDomain.names domain) :
    ∃ value, SourcePreparedSharedRows.read current name = some value ∧ Available source value ∧ Available current value ∧
      value.referenceOf = .mu name ∧ rank annotation value = 0 := by
  obtain ⟨value, found, original, available, named, annotated⟩ := known.read annotation source current facts growth history domain name member
  exact ⟨value, found, original, available, named, (rank_zero_iff annotation value).mpr annotated⟩

end MicroCFTA.SourceCurrentConstrainedCapNonplainRank
