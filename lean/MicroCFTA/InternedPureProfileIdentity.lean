import MicroCFTA.InternedRootProfileReflection

/-!
# Ordered pure profiles determine normalized source records

A pure normalized union contains only literal references. Its ordered
profile determines its complete canonical record in a common state.
Set-equivalent profiles do not determine identity: source union keys
retain the order of first occurrence.
-/
namespace MicroCFTA.InternedPureProfileIdentity
open Cache InternedConstructorTemplates InternedRootProfile InternedRootProfileReflection
open InternedRootProfileNode InternedStoredMuOrigins InternedProbeProvenance
open InternedRecordCoherence InternedUnionNormalForm InternedUnionNonemptyMembers
open InternedNestedConstruction InternedNestedProvenance InternedFreshProbeKeys
open InternedBinderProtocol (Reference NodeKey)

/-- A normalized pure union contains exactly its ordered literal references. -/
theorem union_members (state : State Symbol Guard) (normal : Normal state)
    (entry : Interned NodeKey) (members : List (Value Symbol Guard)) (depth : Nat) (free : List Reference)
    (available : Available state (.union entry members depth free))
    (names : List Reference) (pure : profile (.union entry members depth free) = some names) :
    members = names.map Value.reference := by
  have combined : many members = some names := by simpa only [profile] using pure
  have only : ∀ child ∈ members, ∃ name, child = .reference name := by
    intro child included
    have atomic := resident_flat state normal.flat _ available.resident child included
    have nonempty := resident_membersNonempty state normal.members _ available.resident child included
    obtain ⟨refs, childPure⟩ := member_pure members names combined child included
    cases child with
    | empty => simp [MemberNonempty, Value.referenceOf] at nonempty
    | reference name => exact ⟨name, rfl⟩
    | node | mu => simp [profile] at childPure
    | union => exact False.elim atomic
  clear pure available
  induction members generalizing names with
  | nil => simpa [many] using combined.symm
  | cons first rest ih =>
      obtain ⟨name, rfl⟩ := only first List.mem_cons_self
      cases found : many rest with
      | none => simp [many, profile, found, combine] at combined
      | some refs =>
          have namesSame : name :: refs = names := by
            simpa [many, profile, found, combine] using combined
          rw [← namesSame, List.map_cons]
          congr 1
          exact ih refs found (fun child included => only child (List.mem_cons_of_mem _ included))

/-- Equal ordered pure profiles identify the same complete normalized value in a common source state. -/
theorem ordered_identity (state : State Symbol Guard) (normal : Normal state)
    (first second : Value Symbol Guard) (firstAvailable : Available state first)
    (secondAvailable : Available state second) (names : List Reference)
    (firstPure : profile first = some names) (secondPure : profile second = some names) : first = second := by
  cases first with
  | empty =>
      have namesEmpty : names = [] := by simpa [profile] using firstPure.symm
      exact ((profile_empty_iff second state normal.proper secondAvailable).mp (namesEmpty ▸ secondPure)).symm
  | reference name =>
      have namesSingle : names = [name] := by simpa [profile] using firstPure.symm
      have single : Single name ((profile second).getD []) := by simp [secondPure, namesSingle, Single]
      exact ((profile_single_iff second state normal secondAvailable name).mp single).symm
  | node | mu => simp [profile] at firstPure
  | union firstEntry firstMembers firstDepth firstFree =>
      cases second with
      | empty =>
          have namesEmpty : names = [] := by simpa [profile] using secondPure.symm
          exact (profile_empty_iff _ state normal.proper firstAvailable).mp (namesEmpty ▸ firstPure)
      | reference name =>
          have namesSingle : names = [name] := by simpa [profile] using secondPure.symm
          have single : Single name ((profile (.union firstEntry firstMembers firstDepth firstFree)).getD []) := by
            simp [firstPure, namesSingle, Single]
          exact (profile_single_iff _ state normal firstAvailable name).mp single
      | node | mu => simp [profile] at secondPure
      | union secondEntry secondMembers secondDepth secondFree =>
          have firstMembersSame := union_members state normal firstEntry firstMembers firstDepth firstFree firstAvailable names firstPure
          have secondMembersSame := union_members state normal secondEntry secondMembers secondDepth secondFree secondAvailable names secondPure
          have firstStored := firstAvailable.resident firstEntry rfl
          have secondStored := secondAvailable.resident secondEntry rfl
          obtain ⟨_, _, firstFields⟩ := normal.facts.coherent.nodes firstEntry.key _ firstStored
          obtain ⟨_, _, secondFields⟩ := normal.facts.coherent.nodes secondEntry.key _ secondStored
          have firstKey : firstEntry.key = .union (firstMembers.map Value.referenceOf) := firstFields.2.1
          have secondKey : secondEntry.key = .union (secondMembers.map Value.referenceOf) := secondFields.2.1
          have sameKey : firstEntry.key = secondEntry.key := by rw [firstKey, secondKey, firstMembersSame, secondMembersSame]
          rw [sameKey] at firstStored
          exact Option.some.inj (firstStored.symm.trans secondStored)

/-- The first source union preserves the first literal-reference order. -/
def forward : Value Unit Unit × State Unit Unit :=
  run (makeUnion [.reference .depth, .reference (.uninterned 0)]) empty

/-- A reversed source union is built in the exact state returned by the first union. -/
def reverse : Value Unit Unit × State Unit Unit :=
  run (makeUnion [.reference (.uninterned 0), .reference .depth]) forward.2

/-- Both ordered unions have the same nonempty set of pure root references. -/
theorem reversed_equivalent :
    profile forward.1 = some [.depth, .uninterned 0] ∧
    profile reverse.1 = some [.uninterned 0, .depth] ∧
    Equivalent (profile forward.1) (profile reverse.1) := by
  constructor
  · cbv
  constructor
  · cbv
  constructor
  · cbv; simp
  · intro name
    have first : profile forward.1 = some [Reference.depth, .uninterned 0] := by cbv
    have second : profile reverse.1 = some [Reference.uninterned 0, .depth] := by cbv
    rw [first, second]
    change name ∈ [Reference.depth, .uninterned 0] ↔ name ∈ [Reference.uninterned 0, .depth]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    exact or_comm

/-- The source's ordered union keys allocate distinct identities despite equivalent pure profiles. -/
theorem reversed_distinct :
    forward.1.referenceOf = .union 0 ∧ reverse.1.referenceOf = .union 1 ∧
    forward.1.referenceOf ≠ reverse.1.referenceOf := by cbv; simp

/-- Both counterexample records are available in one source-derived normalized state. -/
theorem reversed_available :
    Normal reverse.2 ∧ Available reverse.2 forward.1 ∧ Available reverse.2 reverse.1 := by
  let environment : List (Value Unit Unit) := [.reference .depth, .reference (.uninterned 0)]
  have inputs : ∀ state : State Unit Unit, Values state environment := by
    intro state value member
    rcases List.mem_cons.mp member with rfl | member
    · exact depth_available state
    · rcases List.mem_cons.mp member with rfl | member
      · exact ordinary_available state 0
      · cases member
  have firstDone : build (.union [.var 0, .var 1]) environment empty = .done forward.1 forward.2 := by cbv
  have firstNormal : Normal forward.2 := by
    simpa only [firstDone, Outcome.state] using
      build_normal (.union [.var 0, .var 1]) environment empty empty_normal (inputs empty)
  have firstAvailable := (build_verified (.union [.var 0, .var 1]) environment empty
    empty_normal.facts (inputs empty)).result _ _ firstDone
  have secondDone : build (.union [.var 1, .var 0]) environment forward.2 = .done reverse.1 reverse.2 := by cbv
  have secondVerified := build_verified (.union [.var 1, .var 0]) environment forward.2 firstNormal.facts (inputs forward.2)
  refine ⟨?_, ?_, secondVerified.result _ _ secondDone⟩
  · simpa only [secondDone, Outcome.state] using
      build_normal (.union [.var 1, .var 0]) environment forward.2 firstNormal (inputs forward.2)
  · simpa only [secondDone, Outcome.state] using secondVerified.available forward.1 firstAvailable

end MicroCFTA.InternedPureProfileIdentity
