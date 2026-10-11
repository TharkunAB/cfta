import MicroCFTA.ArrayUnionFind
import MicroCFTA.EqualityNormalize

/-!
# Equality completion's sequence of array unions

The source unions the first path of each class with every remaining path.
The driver below uses the exact unweighted parent-array worker. Fuel bounds
are proof instrumentation; every finite input has sufficient bounds.
-/
namespace MicroCFTA.EqualityArray
open UnionFind

/-- Larger bounds preserve a completed unweighted union and all compression writes. -/
theorem union_more (forest : Forest) (left right smallLeft smallRight large : Nat) (output : Forest)
    (leftBound : smallLeft ≤ large) (rightBound : smallRight ≤ large)
    (success : ArrayUnionFind.unionLeft smallLeft smallRight forest left right = some output) :
    ArrayUnionFind.unionLeft large large forest left right = some output := by
  cases first : findRoot smallLeft forest left with
  | none => simp [ArrayUnionFind.unionLeft, first] at success
  | some found =>
      cases second : findRoot smallRight found.forest right with
      | none => simp [ArrayUnionFind.unionLeft, first, second] at success
      | some next =>
          have firstLarge : findRoot large forest left = some found := by
            simpa [Nat.add_sub_of_le leftBound] using findRoot_moreFuel smallLeft (large - smallLeft) forest left found first
          have secondLarge : findRoot large found.forest right = some next := by
            simpa [Nat.add_sub_of_le rightBound] using findRoot_moreFuel smallRight (large - smallRight) found.forest right next second
          simpa [ArrayUnionFind.unionLeft, firstLarge, secondLarge] using
            (show (if found.representative = next.representative then some next.forest
              else some (link next.forest found.representative next.representative found.size next.size)) = some output from
                by simpa [ArrayUnionFind.unionLeft, first, second] using success)

/-- Execute the complete left-to-right sequence of source union calls. -/
def mergePairs (fuel : Nat) : List (Nat × Nat) → Forest → Option Forest
  | [], forest => some forest
  | (left, right) :: rest, forest => do
      let next ← ArrayUnionFind.unionLeft fuel fuel forest left right
      mergePairs fuel rest next

/-- Exact parent-array execution of the same source call sequence. -/
def mergeArrays (fuel : Nat) : List (Nat × Nat) → ArrayUnionFind.Parents → Option ArrayUnionFind.Parents
  | [], parents => some parents
  | (left, right) :: rest, parents => do
      let next ← ArrayUnionFind.union fuel fuel parents left right
      mergeArrays fuel rest next

/-- Each successful union preserves exactly the required assignment equations. -/
theorem union_satisfies (forest : Forest) (valid : Total forest) (fuel left right : Nat) (output : Forest)
    (success : ArrayUnionFind.unionLeft fuel fuel forest left right = some output) (assignment : Nat → Value) :
    Satisfies output assignment ↔ Satisfies forest assignment ∧ assignment left = assignment right := by
  obtain ⟨afterValid, classes⟩ := ArrayUnionFind.unionLeft_correct valid success
  constructor
  · intro after
    constructor
    · intro x y connected; exact after x y ((classes x y).mpr (Or.inl connected))
    · obtain ⟨lr, ls, lp⟩ := valid left
      obtain ⟨rr, rs, rp⟩ := valid right
      exact after left right ((classes left right).mpr
        (Or.inr (Or.inl ⟨⟨lr, ls, lp, lp⟩, ⟨rr, rs, rp, rp⟩⟩)))
  · rintro ⟨before, equality⟩ x y connected
    rcases (classes x y).mp connected with direct | ⟨xl, yr⟩ | ⟨xr, yl⟩
    · exact before x y direct
    · exact (before x left xl).trans (equality.trans (before y right yr).symm)
    · exact (before x right xr).trans (equality.symm.trans (before y left yl).symm)

/-- The whole source union sequence retains termination and exactly its equations. -/
theorem mergePairs_correct (pairs : List (Nat × Nat)) (forest : Forest) (valid : Total forest)
    (fuel : Nat) (output : Forest) (success : mergePairs fuel pairs forest = some output) :
    Total output ∧ ∀ assignment : Nat → Value,
      Satisfies output assignment ↔ Satisfies forest assignment ∧
        ∀ pair ∈ pairs, assignment pair.1 = assignment pair.2 := by
  induction pairs generalizing forest with
  | nil =>
      have equal : forest = output := Option.some.inj success
      subst output
      exact ⟨valid, fun assignment => by simp⟩
  | cons pair rest ih =>
      rcases pair with ⟨left, right⟩
      cases first : ArrayUnionFind.unionLeft fuel fuel forest left right with
      | none => simp [mergePairs, first] at success
      | some next =>
          have remaining : mergePairs fuel rest next = some output := by simpa [mergePairs, first] using success
          obtain ⟨afterValid, semantics⟩ := ih next (ArrayUnionFind.unionLeft_correct valid first).1 remaining
          refine ⟨afterValid, ?_⟩
          intro assignment
          rw [semantics, union_satisfies forest valid fuel left right next first assignment]
          simp [and_assoc]

/-- The sequence of ghost operations refines every actual array read and write. -/
theorem mergeArrays_refines (pairs : List (Nat × Nat)) (forest : Forest) (valid : Total forest)
    (fuel : Nat) (output : Forest) (success : mergePairs fuel pairs forest = some output) :
    mergeArrays fuel pairs (ArrayUnionFind.erase forest) = some (ArrayUnionFind.erase output) := by
  induction pairs generalizing forest with
  | nil => cases success; rfl
  | cons pair rest ih =>
      rcases pair with ⟨left, right⟩
      cases first : ArrayUnionFind.unionLeft fuel fuel forest left right with
      | none => simp [mergePairs, first] at success
      | some next =>
          have remaining : mergePairs fuel rest next = some output := by simpa [mergePairs, first] using success
          have exact := ArrayUnionFind.union_refines forest valid fuel fuel left right next first
          simpa [mergeArrays, exact] using ih next (ArrayUnionFind.unionLeft_correct valid first).1 remaining

/-- Additional execution fuel preserves the entire successful compression trace. -/
theorem mergePairs_more (pairs : List (Nat × Nat)) (forest : Forest) (small large : Nat)
    (bound : small ≤ large) (output : Forest) (success : mergePairs small pairs forest = some output) :
    mergePairs large pairs forest = some output := by
  induction pairs generalizing forest with
  | nil => exact success
  | cons pair rest ih =>
      rcases pair with ⟨left, right⟩
      cases first : ArrayUnionFind.unionLeft small small forest left right with
      | none => simp [mergePairs, first] at success
      | some next =>
          have remaining : mergePairs small rest next = some output := by simpa [mergePairs, first] using success
          have extended := union_more forest left right small small large next bound bound first
          simpa [mergePairs, extended] using ih next remaining

/-- Every finite class union sequence has a sufficient common execution bound. -/
theorem mergePairs_terminates (pairs : List (Nat × Nat)) (forest : Forest) (valid : Total forest) :
    ∃ fuel output, mergePairs fuel pairs forest = some output := by
  induction pairs generalizing forest with
  | nil => exact ⟨0, forest, rfl⟩
  | cons pair rest ih =>
      rcases pair with ⟨left, right⟩
      obtain ⟨leftFuel, rightFuel, next, first⟩ := ArrayUnionFind.unionLeft_terminates forest valid left right
      obtain ⟨tailFuel, output, remaining⟩ := ih next (ArrayUnionFind.unionLeft_correct valid first).1
      let fuel := leftFuel + rightFuel + tailFuel
      have extended := union_more forest left right leftFuel rightFuel fuel next (by omega) (by omega) first
      have tail := mergePairs_more rest next tailFuel fuel (by omega) output remaining
      exact ⟨fuel, output, by simpa [mergePairs, extended] using tail⟩

/-- Source class traversal forms a star with the first member as its center. -/
def classPairs : List Nat → List (Nat × Nat)
  | [] => []
  | first :: rest => rest.map (fun other => (first, other))

/-- Star equations are exactly pairwise equality throughout the original class. -/
theorem classPairs_exact (members : List Nat) (assignment : Nat → Value) :
    (∀ pair ∈ classPairs members, assignment pair.1 = assignment pair.2) ↔
      ∀ left ∈ members, ∀ right ∈ members, assignment left = assignment right := by
  cases members with
  | nil => simp [classPairs]
  | cons first rest =>
      simp only [classPairs, List.forall_mem_map]
      constructor
      · intro star left leftMember right rightMember
        have fromFirst : ∀ member ∈ first :: rest, assignment first = assignment member := by
          intro member present
          rcases List.mem_cons.mp present with rfl | present
          · rfl
          · exact star member present
        exact (fromFirst left leftMember).symm.trans (fromFirst right rightMember)
      · intro all member present
        exact all first (by simp) member (by simp [present])

/-- The complete source class loop has exactly the original equality meaning. -/
theorem complete_equations (classes : List (List Nat)) (fuel : Nat) (output : Forest)
    (success : mergePairs fuel (classes.flatMap classPairs) (withInitialValues classes.flatten) = some output)
    (assignment : Nat → Value) :
    Satisfies output assignment ↔
      ∀ members ∈ classes, ∀ left ∈ members, ∀ right ∈ members, assignment left = assignment right := by
  have semantics := (mergePairs_correct (classes.flatMap classPairs) _ (initial_total _) fuel output success).2 assignment
  rw [semantics]
  simp only [initial_satisfies, true_and, List.forall_mem_flatMap, classPairs_exact]

/-- Source readback compresses each listed member and retains its representative. -/
def readAll (fuel : Nat) : List Nat → Forest → Option (List (Nat × Nat) × Forest)
  | [], forest => some ([], forest)
  | index :: rest, forest => do
      let found ← findRoot fuel forest index
      let (entries, after) ← readAll fuel rest found.forest
      pure ((found.representative, index) :: entries, after)

/-- Readback preserves the partition and lists exactly every requested member and its root. -/
theorem readAll_correct (members : List Nat) (forest : Forest) (valid : Total forest)
    (fuel : Nat) (entries : List (Nat × Nat)) (after : Forest)
    (success : readAll fuel members forest = some (entries, after)) :
    Total after ∧ (∀ x y, SameClass after x y ↔ SameClass forest x y) ∧
      ∀ root index, (root, index) ∈ entries ↔ index ∈ members ∧ ∃ size, Reaches forest index root size := by
  induction members generalizing forest entries after with
  | nil =>
      have equal : ([], forest) = (entries, after) := Option.some.inj success
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
      exact ⟨valid, fun _ _ => Iff.rfl, by simp⟩
  | cons index rest ih =>
      cases first : findRoot fuel forest index with
      | none => simp [readAll, first] at success
      | some found =>
          cases remaining : readAll fuel rest found.forest with
          | none => simp [readAll, first, remaining] at success
          | some result =>
              rcases result with ⟨tail, output⟩
              have same : ((found.representative, index) :: tail, output) = (entries, after) := by
                simpa [readAll, first, remaining] using success
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
              obtain ⟨afterValid, classes, listed⟩ := ih found.forest (findRoot_total valid first) tail output remaining
              refine ⟨afterValid, fun x y => (classes x y).trans (findRoot_classes valid first x y), ?_⟩
              intro root member
              constructor
              · intro present
                rcases List.mem_cons.mp present with equal | present
                · obtain ⟨sameRoot, sameIndex⟩ := Prod.mk.inj equal
                  subst root; subst member
                  exact ⟨by simp, found.size, (findRoot_correct _ _ _ _ first).1⟩
                · obtain ⟨memberRest, size, path⟩ := (listed root member).mp present
                  exact ⟨by simp [memberRest], size, (findRoot_reaches_iff valid first member root size).mp path⟩
              · rintro ⟨memberList, size, path⟩
                rcases List.mem_cons.mp memberList with same | memberRest
                · subst member
                  have sameRoot := (reaches_unique path (findRoot_correct _ _ _ _ first).1).1
                  simp [sameRoot]
                · exact List.mem_cons_of_mem _ ((listed root member).mpr
                    ⟨memberRest, size, (findRoot_reaches_iff valid first member root size).mpr path⟩)

/-- Group every recorded member by its representative, as in `Map.fromListWith`. -/
def groups (entries : List (Nat × Nat)) : List (List Nat) :=
  (entries.map Prod.fst).eraseDups.map fun root =>
    (entries.filter fun entry => entry.1 == root).map Prod.snd

/-- Group membership is exactly membership in one representative bucket. -/
theorem groups_pair (entries : List (Nat × Nat)) (left right : Nat) :
    (∃ group ∈ groups entries, left ∈ group ∧ right ∈ group) ↔
      ∃ root, (root, left) ∈ entries ∧ (root, right) ∈ entries := by
  have bucket : ∀ root index, index ∈ (entries.filter fun entry => entry.1 == root).map Prod.snd ↔ (root, index) ∈ entries := by
    intro root index
    simp only [List.mem_map, List.mem_filter, beq_iff_eq]
    constructor
    · rintro ⟨⟨key, value⟩, ⟨member, same⟩, equal⟩
      dsimp only at same equal
      subst key; subst value; exact member
    · intro member; exact ⟨(root, index), ⟨member, rfl⟩, rfl⟩
  simp only [groups, List.mem_map, List.mem_eraseDups]
  constructor
  · rintro ⟨group, ⟨root, rootMember, rfl⟩, leftMember, rightMember⟩
    exact ⟨root, (bucket root left).mp leftMember, (bucket root right).mp rightMember⟩
  · rintro ⟨root, leftMember, rightMember⟩
    exact ⟨_, ⟨root, ⟨(root, left), leftMember, rfl⟩, rfl⟩,
      (bucket root left).mpr leftMember, (bucket root right).mpr rightMember⟩

/-- The concrete source readback and grouping represent exactly its final partition. -/
theorem grouped_partition (members : List Nat) (forest : Forest) (valid : Total forest)
    (fuel : Nat) (entries : List (Nat × Nat)) (after : Forest)
    (success : readAll fuel members forest = some (entries, after)) (left right : Nat) :
    (∃ group ∈ groups entries, left ∈ group ∧ right ∈ group) ↔
      left ∈ members ∧ right ∈ members ∧ SameClass forest left right := by
  have listed := (readAll_correct members forest valid fuel entries after success).2.2
  rw [groups_pair]
  constructor
  · rintro ⟨root, first, second⟩
    obtain ⟨leftMember, leftSize, leftPath⟩ := (listed root left).mp first
    obtain ⟨rightMember, rightSize, rightPath⟩ := (listed root right).mp second
    exact ⟨leftMember, rightMember, (sameClass_iff_roots leftPath rightPath).mpr rfl⟩
  · rintro ⟨leftMember, rightMember, root, size, leftPath, rightPath⟩
    exact ⟨root, (listed root left).mpr ⟨leftMember, size, leftPath⟩,
      (listed root right).mpr ⟨rightMember, size, rightPath⟩⟩

/-- Independent equivalence closure of the input class equations. -/
inductive Connected (classes : List (List Nat)) : Nat → Nat → Prop where
  | refl (index : Nat) : Connected classes index index
  | related (members : List Nat) (present : members ∈ classes) (left right : Nat)
      (leftMember : left ∈ members) (rightMember : right ∈ members) : Connected classes left right
  | symm : Connected classes left right → Connected classes right left
  | trans : Connected classes left middle → Connected classes middle right → Connected classes left right

/-- Every total forest relates each variable to itself. -/
theorem sameClass_refl (forest : Forest) (valid : Total forest) (index : Nat) : SameClass forest index index := by
  obtain ⟨root, size, path⟩ := valid index
  exact ⟨root, size, path, path⟩

/-- A class indicator assignment is constant on every class of a total forest. -/
theorem sameClass_assignment (forest : Forest) (left : Nat) : Satisfies forest (fun right => SameClass forest left right) := by
  intro x y related
  apply propext
  exact ⟨fun first => sameClass_trans first related, fun second => sameClass_trans second (sameClass_symm related)⟩

/-- The complete array union loop computes exactly the independent connected relation. -/
theorem complete_connected (classes : List (List Nat)) (fuel : Nat) (output : Forest)
    (success : mergePairs fuel (classes.flatMap classPairs) (withInitialValues classes.flatten) = some output)
    (left right : Nat) : SameClass output left right ↔ Connected classes left right := by
  have valid := (mergePairs_correct (Value := Nat) (classes.flatMap classPairs) _ (initial_total _) fuel output success).1
  have direct : ∀ members ∈ classes, ∀ x ∈ members, ∀ y ∈ members, SameClass output x y := by
    intro members present x xMember y yMember
    have equations := (complete_equations classes fuel output success (fun z => SameClass output x z)).mp
      (sameClass_assignment output x)
    exact (equations members present x xMember y yMember) ▸ sameClass_refl output valid x
  constructor
  · intro related
    let assignment := fun index => Connected classes left index
    have equations : ∀ members ∈ classes, ∀ x ∈ members, ∀ y ∈ members, assignment x = assignment y := by
      intro members present x xMember y yMember
      apply propext
      exact ⟨fun before => .trans before (.related members present x y xMember yMember),
        fun before => .trans before (.related members present y x yMember xMember)⟩
    have assignmentSat := (complete_equations classes fuel output success assignment).mpr equations
    have equal : Connected classes left left = Connected classes left right := assignmentSat left right related
    exact Eq.mp equal (Connected.refl left)
  · intro connected
    induction connected with
    | refl index => exact sameClass_refl output valid index
    | related members present x y xMember yMember => exact direct members present x xMember y yMember
    | symm _ ih => exact sameClass_symm ih
    | trans _ _ ih ihtail => exact sameClass_trans ih ihtail

/-- A nontrivial connected pair has both ends in the original input domain. -/
theorem connected_members (classes : List (List Nat)) (left right : Nat) (connected : Connected classes left right) :
    left = right ∨ (left ∈ classes.flatten ∧ right ∈ classes.flatten) := by
  induction connected with
  | refl => exact Or.inl rfl
  | related members present left right leftMember rightMember =>
      exact Or.inr ⟨List.mem_flatten.mpr ⟨members, present, leftMember⟩,
        List.mem_flatten.mpr ⟨members, present, rightMember⟩⟩
  | symm _ ih => rcases ih with same | members; exact Or.inl same.symm; exact Or.inr members.symm
  | trans _ _ ih ihtail =>
      rcases ih with same | members
      · subst_vars; exact ihtail
      · rcases ihtail with same | later
        · subst_vars; exact Or.inr members
        · exact Or.inr ⟨members.1, later.2⟩

/-- Full source union, representative readback, and grouping preserve exactly the class equations. -/
theorem complete_groups_exact (classes : List (List Nat)) (mergeFuel readFuel : Nat)
    (forest after : Forest) (entries : List (Nat × Nat))
    (merged : mergePairs mergeFuel (classes.flatMap classPairs) (withInitialValues classes.flatten) = some forest)
    (readback : readAll readFuel classes.flatten.eraseDups forest = some (entries, after))
    (assignment : Nat → Value) :
    (∀ group ∈ groups entries, ∀ left ∈ group, ∀ right ∈ group, assignment left = assignment right) ↔
      ∀ members ∈ classes, ∀ left ∈ members, ∀ right ∈ members, assignment left = assignment right := by
  have valid := (mergePairs_correct (Value := Value) (classes.flatMap classPairs) _ (initial_total _) mergeFuel forest merged).1
  have grouped := grouped_partition classes.flatten.eraseDups forest valid readFuel entries after readback
  rw [← complete_equations classes mergeFuel forest merged assignment]
  constructor
  · intro output left right related
    rcases connected_members classes left right ((complete_connected classes mergeFuel forest merged left right).mp related) with same | members
    · rw [same]
    · obtain ⟨group, present, leftMember, rightMember⟩ := (grouped left right).mpr
        ⟨by simpa using members.1, by simpa using members.2, related⟩
      exact output group present left leftMember right rightMember
  · intro accepted group present left leftMember right rightMember
    exact accepted left right ((grouped left right).mp ⟨group, present, leftMember, rightMember⟩).2.2

/-- More fuel preserves the whole representative readback sequence. -/
theorem readAll_more (members : List Nat) (forest : Forest) (small large : Nat) (bound : small ≤ large)
    (entries : List (Nat × Nat)) (after : Forest)
    (success : readAll small members forest = some (entries, after)) :
    readAll large members forest = some (entries, after) := by
  induction members generalizing forest entries after with
  | nil => exact success
  | cons index rest ih =>
      cases first : findRoot small forest index with
      | none => simp [readAll, first] at success
      | some found =>
          cases remaining : readAll small rest found.forest with
          | none => simp [readAll, first, remaining] at success
          | some result =>
              rcases result with ⟨tail, output⟩
              have firstLarge : findRoot large forest index = some found := by
                simpa [Nat.add_sub_of_le bound] using findRoot_moreFuel small (large - small) forest index found first
              have tailLarge := ih found.forest tail output remaining
              simpa [readAll, firstLarge, tailLarge] using
                (show some ((found.representative, index) :: tail, output) = some (entries, after) from
                  by simpa [readAll, first, remaining] using success)

/-- Every finite source readback has a sufficient execution bound. -/
theorem readAll_terminates (members : List Nat) (forest : Forest) (valid : Total forest) :
    ∃ fuel entries after, readAll fuel members forest = some (entries, after) := by
  induction members generalizing forest with
  | nil => exact ⟨0, [], forest, rfl⟩
  | cons index rest ih =>
      obtain ⟨root, size, path⟩ := valid index
      obtain ⟨firstFuel, found, first⟩ := findRoot_terminates path
      obtain ⟨tailFuel, entries, after, remaining⟩ := ih found.forest (findRoot_total valid first)
      have firstLarge := findRoot_moreFuel firstFuel tailFuel forest index found first
      have tailLarge := readAll_more rest found.forest tailFuel (firstFuel + tailFuel) (by omega) entries after remaining
      exact ⟨firstFuel + tailFuel, (found.representative, index) :: entries, after,
        by simp [readAll, firstLarge, tailLarge]⟩

/-- The complete finite source algorithm terminates and retains precisely its original equations. -/
def readArrays (fuel : Nat) : List Nat → ArrayUnionFind.Parents → Option (List (Nat × Nat) × ArrayUnionFind.Parents)
  | [], parents => some ([], parents)
  | index :: rest, parents => do
      let (root, compressed) ← ArrayUnionFind.find fuel parents index
      let (entries, after) ← readArrays fuel rest compressed
      pure ((root, index) :: entries, after)

/-- The complete readback sequence refines the source parent-array execution. -/
theorem readArrays_refines (members : List Nat) (forest : Forest) (valid : Total forest)
    (fuel : Nat) (entries : List (Nat × Nat)) (after : Forest)
    (success : readAll fuel members forest = some (entries, after)) :
    readArrays fuel members (ArrayUnionFind.erase forest) = some (entries, ArrayUnionFind.erase after) := by
  induction members generalizing forest entries after with
  | nil => cases success; rfl
  | cons index rest ih =>
      cases first : findRoot fuel forest index with
      | none => simp [readAll, first] at success
      | some found =>
          cases remaining : readAll fuel rest found.forest with
          | none => simp [readAll, first, remaining] at success
          | some result =>
              rcases result with ⟨tail, output⟩
              have equal : ((found.representative, index) :: tail, output) = (entries, after) := by
                simpa [readAll, first, remaining] using success
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
              have firstRun := ArrayUnionFind.find_refines fuel forest valid index found first
              have tailRun := ih found.forest (findRoot_total valid first) tail output remaining
              simp [readArrays, firstRun, tailRun]

/-- The complete finite source algorithm terminates and retains precisely its original equations. -/
theorem complete_terminates_exact (classes : List (List Nat)) :
    ∃ mergeFuel readFuel forest entries after,
      mergeArrays mergeFuel (classes.flatMap classPairs) id = some (ArrayUnionFind.erase forest) ∧
      readArrays readFuel classes.flatten.eraseDups (ArrayUnionFind.erase forest) = some (entries, ArrayUnionFind.erase after) ∧
      ∀ assignment : Nat → Value,
        (∀ group ∈ groups entries, ∀ left ∈ group, ∀ right ∈ group, assignment left = assignment right) ↔
          ∀ members ∈ classes, ∀ left ∈ members, ∀ right ∈ members, assignment left = assignment right := by
  obtain ⟨mergeFuel, forest, merged⟩ := mergePairs_terminates (classes.flatMap classPairs)
    (withInitialValues classes.flatten) (initial_total _)
  have valid := (mergePairs_correct (Value := Value) _ _ (initial_total _) mergeFuel forest merged).1
  obtain ⟨readFuel, entries, after, readback⟩ := readAll_terminates classes.flatten.eraseDups forest valid
  refine ⟨mergeFuel, readFuel, forest, entries, after, ?_,
    readArrays_refines classes.flatten.eraseDups forest valid readFuel entries after readback,
    complete_groups_exact classes mergeFuel readFuel forest after entries merged readback⟩
  simpa only [ArrayUnionFind.initial_array] using
    mergeArrays_refines (classes.flatMap classPairs) (withInitialValues classes.flatten) (initial_total _) mergeFuel forest merged

end MicroCFTA.EqualityArray
