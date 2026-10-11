import MicroCFTA.EqualityArray

/-!
# In-range source parent-array accesses

The initialized path index is a finite interval. Each read, recursive lookup,
compression write, and root link remains in that interval. Physical arrays
must implement these functional reads and writes.
-/
namespace MicroCFTA.ArrayUnionFind

/-- Every allocated array cell points to another allocated cell. -/
def Bounded (parents : Parents) (size : Nat) : Prop :=
  ∀ index, index < size → parents index < size

/-- Singleton initialization has valid pointers even for an empty array. -/
theorem initialized_bounded (size : Nat) : Bounded id size := fun _ within => within

/-- A write of an allocated root preserves all array pointer bounds. -/
theorem write_bounded (parents : Parents) (size index value : Nat) (bounded : Bounded parents size)
    (allocated : value < size) : Bounded (write parents index value) size := by
  intro other within
  by_cases same : other = index
  · simpa [write, same] using allocated
  · simpa [write, same] using bounded other within

/-- A complete path-compressing find returns an allocated root and preserves array bounds. -/
theorem find_bounded (fuel : Nat) (parents : Parents) (size index root : Nat) (after : Parents)
    (bounded : Bounded parents size) (within : index < size)
    (success : find fuel parents index = some (root, after)) :
    root < size ∧ Bounded after size := by
  induction fuel generalizing parents index root after with
  | zero => simp [find] at success
  | succ fuel ih =>
      by_cases same : parents index = index
      · have equal : (index, parents) = (root, after) := by simpa [find, same] using success
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
        exact ⟨within, bounded⟩
      · cases recursive : find fuel parents (parents index) with
        | none => simp [find, same, recursive] at success
        | some result =>
            rcases result with ⟨representative, next⟩
            obtain ⟨rootWithin, nextBounded⟩ := ih parents (parents index) representative next bounded
              (bounded index within) recursive
            have equal : (representative, write next index representative) = (root, after) := by
              simpa [find, same, recursive] using success
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
            exact ⟨rootWithin, write_bounded next size index representative nextBounded rootWithin⟩

/-- Both roots and the final unweighted link remain inside the allocated array. -/
theorem union_bounded (leftFuel rightFuel : Nat) (parents : Parents) (size left right : Nat)
    (bounded : Bounded parents size) (leftWithin : left < size) (rightWithin : right < size)
    (after : Parents) (success : union leftFuel rightFuel parents left right = some after) : Bounded after size := by
  cases first : find leftFuel parents left with
  | none => simp [union, first] at success
  | some result =>
      rcases result with ⟨leftRoot, next⟩
      obtain ⟨leftRootWithin, nextBounded⟩ := find_bounded leftFuel parents size left leftRoot next bounded leftWithin first
      cases second : find rightFuel next right with
      | none => simp [union, first, second] at success
      | some result =>
          rcases result with ⟨rightRoot, final⟩
          obtain ⟨rightRootWithin, finalBounded⟩ := find_bounded rightFuel next size right rightRoot final nextBounded rightWithin second
          by_cases same : leftRoot = rightRoot
          · have equal : final = after := by simpa [union, first, second, same] using success
            subst after; exact finalBounded
          · have equal : write final leftRoot rightRoot = after := by simpa [union, first, second, same] using success
            subst after; exact write_bounded final size leftRoot rightRoot finalBounded rightRootWithin

/-- All complete class-union iterations preserve allocated array pointers. -/
theorem merge_bounded (pairs : List (Nat × Nat)) (fuel size : Nat) (before after : Parents)
    (bounded : Bounded before size) (inputs : ∀ pair ∈ pairs, pair.1 < size ∧ pair.2 < size)
    (success : EqualityArray.mergeArrays fuel pairs before = some after) : Bounded after size := by
  induction pairs generalizing before with
  | nil => cases success; exact bounded
  | cons pair rest ih =>
      rcases pair with ⟨left, right⟩
      cases first : union fuel fuel before left right with
      | none => simp [EqualityArray.mergeArrays, first] at success
      | some next =>
          have allocated := inputs (left, right) (by simp)
          have remaining : EqualityArray.mergeArrays fuel rest next = some after := by
            simpa [EqualityArray.mergeArrays, first] using success
          exact ih next (union_bounded fuel fuel before size left right bounded allocated.1 allocated.2 next first)
            (fun pair present => inputs pair (by simp [present])) remaining

/-- Readback emits only allocated indexes and roots and retains bounded pointers. -/
theorem readback_bounded (members : List Nat) (fuel size : Nat) (before after : Parents)
    (entries : List (Nat × Nat)) (bounded : Bounded before size)
    (inputs : ∀ member ∈ members, member < size)
    (success : EqualityArray.readArrays fuel members before = some (entries, after)) :
    Bounded after size ∧ ∀ entry ∈ entries, entry.1 < size ∧ entry.2 < size := by
  induction members generalizing before entries after with
  | nil =>
      have equal : ([], before) = (entries, after) := Option.some.inj success
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
      exact ⟨bounded, by simp⟩
  | cons member rest ih =>
      cases first : find fuel before member with
      | none => simp [EqualityArray.readArrays, first] at success
      | some result =>
          rcases result with ⟨root, next⟩
          have memberWithin := inputs member (by simp)
          obtain ⟨rootWithin, nextBounded⟩ := find_bounded fuel before size member root next bounded memberWithin first
          cases remaining : EqualityArray.readArrays fuel rest next with
          | none => simp [EqualityArray.readArrays, first, remaining] at success
          | some result =>
              rcases result with ⟨tail, output⟩
              have equal : ((root, member) :: tail, output) = (entries, after) := by
                simpa [EqualityArray.readArrays, first, remaining] using success
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
              obtain ⟨outputBounded, tailBounds⟩ := ih next output tail nextBounded
                (fun index present => inputs index (by simp [present])) remaining
              exact ⟨outputBounded, fun entry present => by
                rcases List.mem_cons.mp present with rfl | present
                · exact ⟨rootWithin, memberWithin⟩
                · exact tailBounds entry present⟩

end MicroCFTA.ArrayUnionFind
