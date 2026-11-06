import MicroCFTA.UnionFind

namespace MicroCFTA.UnionFindSupport

open MicroCFTA.UnionFind

/-- The forest has no stored entries at or above `bound`. -/
def SupportedBelow (bound : Nat) (forest : Forest) : Prop :=
  ∀ key, bound ≤ key → forest key = none

/-- The empty forest has no stored entries. -/
theorem supportedBelow_empty : SupportedBelow 0 (fun _ => none) := by
  intro key _
  rfl

/-- One write preserves a bound computed from the old bound and the key. -/
theorem supportedBelow_write {bound : Nat} {forest : Forest}
    (h : SupportedBelow bound forest) (key : Nat) (entry : Option Entry) :
    SupportedBelow (max bound (key + 1))
      (fun index => if index = key then entry else forest index) := by
  intro index hindex
  have hne : index ≠ key := by omega
  simpa [hne] using h index (Nat.le_trans (Nat.le_max_left _ _) hindex)

/-- An actual write preserves the computed support bound. -/
theorem supportedBelow_put {bound : Nat} {forest : Forest}
    (supported : SupportedBelow bound forest) (key : Nat) (entry : Entry) :
    SupportedBelow (max bound (key + 1)) (put forest key entry) := by
  intro index beyond
  have unequal : index ≠ key := by omega
  simpa [put, unequal, Ne.symm unequal] using
    supported index (Nat.le_trans (Nat.le_max_left _ _) beyond)

/-- Compute an exclusive bound for the listed variables. -/
def initialBound : List Nat → Nat
  | [] => 0
  | key :: rest => max (key + 1) (initialBound rest)

/-- Each listed variable is below the computed bound. -/
theorem lt_initialBound_of_mem (variables : List Nat) :
    ∀ key, key ∈ variables → key < initialBound variables := by
  induction variables with
  | nil =>
      intro key member
      cases member
  | cons first rest inductionHypothesis =>
      intro key member
      cases member with
      | head =>
          exact Nat.lt_of_lt_of_le (Nat.lt_succ_self first) (Nat.le_max_left _ _)
      | tail _ member =>
          exact Nat.lt_of_lt_of_le (inductionHypothesis key member) (Nat.le_max_right _ _)

/-- Initialization has a bound computed from its input list. -/
theorem supportedBelow_withInitialValues (variables : List Nat) :
    SupportedBelow (initialBound variables) (withInitialValues variables) := by
  intro key beyond
  have absent : key ∉ variables := by
    intro member
    have small := lt_initialBound_of_mem variables key member
    omega
  simp [withInitialValues, absent]

/-- A write below the bound preserves that bound. -/
theorem supportedBelow_put_of_lt {bound : Nat} {forest : Forest}
    (supported : SupportedBelow bound forest) (key : Nat)
    (below : key < bound) (entry : Entry) :
    SupportedBelow bound (put forest key entry) := by
  intro index beyond
  have unequal : index ≠ key := by omega
  simpa [put, unequal, Ne.symm unequal] using supported index beyond

/-- Every stored parent identity is below the bound. -/
def ParentsBelow (bound : Nat) (forest : Forest) : Prop :=
  ∀ key parent, forest key = some (.parent parent) → parent < bound

/-- Initialization stores no parent references. -/
theorem parentsBelow_withInitialValues (variables : List Nat) :
    ParentsBelow (initialBound variables) (withInitialValues variables) := by
  intro key parent stored
  simp only [withInitialValues] at stored
  split at stored <;> cases stored

/-- Writing a root preserves the parent bound. -/
theorem parentsBelow_put_root {bound : Nat} {forest : Forest}
    (bounded : ParentsBelow bound forest) (key size : Nat) :
    ParentsBelow bound (put forest key (.root size)) := by
  intro index parent stored
  by_cases equal : index = key
  · subst index
    simp [put] at stored
  · apply bounded index parent
    simpa [put, equal, Ne.symm equal] using stored

/-- Writing a bounded parent preserves the parent bound. -/
theorem parentsBelow_put_parent {bound : Nat} {forest : Forest}
    (bounded : ParentsBelow bound forest) (key target : Nat)
    (below : target < bound) :
    ParentsBelow bound (put forest key (.parent target)) := by
  intro index parent stored
  by_cases equal : index = key
  · subst index
    have same : target = parent := by simpa [put] using stored
    rw [← same]
    exact below
  · apply bounded index parent
    simpa [put, equal, Ne.symm equal] using stored


/-- A successful bounded search preserves both internal bounds. -/
theorem findRoot_preserves_bounds
    (bound fuel : Nat) (forest : Forest) (key : Nat)
    (supported : SupportedBelow bound forest)
    (parents : ParentsBelow bound forest) (below : key < bound) :
    ∀ result : Result, findRoot fuel forest key = some result →
      SupportedBelow bound result.forest ∧
      ParentsBelow bound result.forest ∧ result.representative < bound := by
  induction fuel generalizing forest key with
  | zero =>
      intro result observed
      change none = some result at observed
      cases observed
  | succ fuel ih =>
      intro result observed
      cases stored : forest key with
      | none =>
          have newSupport := supportedBelow_put_of_lt supported key below (.root 1)
          have newParents := parentsBelow_put_root parents key 1
          simp only [findRoot, stored] at observed
          change some _ = some result at observed
          injection observed with same
          cases same
          exact ⟨newSupport, newParents, below⟩
      | some entry =>
          cases entry with
          | root size =>
              simp only [findRoot, stored] at observed
              change some _ = some result at observed
              injection observed with same
              cases same
              exact ⟨supported, parents, below⟩
          | parent next =>
              have nextBelow := parents key next stored
              cases recursive : findRoot fuel forest next with
              | none =>
                  simp only [findRoot, stored, recursive] at observed
                  change none = some result at observed
                  cases observed
              | some found =>
                  obtain ⟨foundSupport, foundParents, representativeBelow⟩ :=
                    ih (forest := forest) (key := next)
                      supported parents nextBelow found recursive
                  have newSupport := supportedBelow_put_of_lt
                    foundSupport key below (.parent found.representative)
                  have newParents := parentsBelow_put_parent
                    foundParents key found.representative representativeBelow
                  simp only [findRoot, stored, recursive] at observed
                  change some _ = some result at observed
                  injection observed with same
                  cases same
                  exact ⟨newSupport, newParents, representativeBelow⟩


/-- Linking bounded identities preserves both internal bounds. -/
theorem link_preserves_bounds
    (bound : Nat) (forest : Forest)
    (supported : SupportedBelow bound forest)
    (parents : ParentsBelow bound forest)
    (loser winner loserSize winnerSize : Nat)
    (loserBelow : loser < bound) (winnerBelow : winner < bound) :
    SupportedBelow bound (link forest loser winner loserSize winnerSize) ∧
    ParentsBelow bound (link forest loser winner loserSize winnerSize) := by
  have loserSupport := supportedBelow_put_of_lt
    supported loser loserBelow (.parent winner)
  have loserParents := parentsBelow_put_parent
    parents loser winner winnerBelow
  have winnerSupport := supportedBelow_put_of_lt
    loserSupport winner winnerBelow (.root (loserSize + winnerSize))
  have winnerParents := parentsBelow_put_root
    loserParents winner (loserSize + winnerSize)
  constructor
  · simpa only [link] using winnerSupport
  · simpa only [link] using winnerParents

/-- A successful union preserves both internal bounds. -/
theorem union_preserves_bounds
    (bound leftFuel rightFuel : Nat) (forest : Forest) (left right : Nat)
    (supported : SupportedBelow bound forest)
    (parents : ParentsBelow bound forest)
    (leftBelow : left < bound) (rightBelow : right < bound) :
    ∀ nextForest : Forest,
      union leftFuel rightFuel forest left right = some nextForest →
      SupportedBelow bound nextForest ∧ ParentsBelow bound nextForest := by
  intro nextForest observed
  cases firstRun : findRoot leftFuel forest left with
  | none =>
      simp [union, firstRun] at observed
  | some first =>
      obtain ⟨firstSupport, firstParents, firstRepresentativeBelow⟩ :=
        findRoot_preserves_bounds bound leftFuel forest left
          supported parents leftBelow first firstRun
      cases secondRun : findRoot rightFuel first.forest right with
      | none =>
          simp [union, firstRun, secondRun] at observed
      | some second =>
          obtain ⟨secondSupport, secondParents, secondRepresentativeBelow⟩ :=
            findRoot_preserves_bounds bound rightFuel first.forest right
              firstSupport firstParents rightBelow second secondRun
          by_cases same : first.representative = second.representative
          · have returned : second.forest = nextForest := by
              simpa [union, firstRun, secondRun, same] using observed
            rw [← returned]
            exact ⟨secondSupport, secondParents⟩
          · by_cases smaller : first.size < second.size
            · have linked := link_preserves_bounds bound second.forest
                secondSupport secondParents first.representative
                second.representative first.size second.size
                firstRepresentativeBelow secondRepresentativeBelow
              have returned :
                  link second.forest first.representative second.representative
                    first.size second.size = nextForest := by
                simpa [union, firstRun, secondRun, same, smaller] using observed
              rw [← returned]
              exact linked
            · have linked := link_preserves_bounds bound second.forest
                secondSupport secondParents second.representative
                first.representative second.size first.size
                secondRepresentativeBelow firstRepresentativeBelow
              have returned :
                  link second.forest second.representative first.representative
                    second.size first.size = nextForest := by
                simpa [union, firstRun, secondRun, same, smaller] using observed
              rw [← returned]
              exact linked


/-- A larger bound preserves storage support. -/
theorem supportedBelow_mono {lower upper : Nat} {forest : Forest}
    (supported : SupportedBelow lower forest) (larger : lower ≤ upper) :
    SupportedBelow upper forest := by
  intro key beyond
  exact supported key (Nat.le_trans larger beyond)

/-- A larger bound preserves the parent bound. -/
theorem parentsBelow_mono {lower upper : Nat} {forest : Forest}
    (bounded : ParentsBelow lower forest) (larger : lower ≤ upper) :
    ParentsBelow upper forest := by
  intro key parent stored
  exact Nat.lt_of_lt_of_le (bounded key parent stored) larger


/-- A successful query has a bound computed from its queried identity. -/
theorem findRoot_grows_bound
    (bound fuel : Nat) (forest : Forest) (key : Nat)
    (supported : SupportedBelow bound forest)
    (parents : ParentsBelow bound forest) :
    ∀ result : Result, findRoot fuel forest key = some result →
      SupportedBelow (max bound (key + 1)) result.forest ∧
      ParentsBelow (max bound (key + 1)) result.forest ∧
      result.representative < max bound (key + 1) := by
  exact findRoot_preserves_bounds (max bound (key + 1)) fuel forest key
    (supportedBelow_mono supported (Nat.le_max_left _ _))
    (parentsBelow_mono parents (Nat.le_max_left _ _))
    (Nat.lt_of_lt_of_le (Nat.lt_succ_self key) (Nat.le_max_right _ _))

/-- A successful union has a bound computed from both queried identities. -/
theorem union_grows_bound
    (bound leftFuel rightFuel : Nat) (forest : Forest) (left right : Nat)
    (supported : SupportedBelow bound forest)
    (parents : ParentsBelow bound forest) :
    ∀ nextForest : Forest,
      union leftFuel rightFuel forest left right = some nextForest →
      SupportedBelow (max bound (max (left + 1) (right + 1))) nextForest ∧
      ParentsBelow (max bound (max (left + 1) (right + 1))) nextForest := by
  exact union_preserves_bounds
    (max bound (max (left + 1) (right + 1))) leftFuel rightFuel forest left right
    (supportedBelow_mono supported (Nat.le_max_left _ _))
    (parentsBelow_mono parents (Nat.le_max_left _ _))
    (Nat.lt_of_lt_of_le (Nat.lt_succ_self left)
      (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)))
    (Nat.lt_of_lt_of_le (Nat.lt_succ_self right)
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)))

/-- A distinct list of bounded identities has bounded length. -/
theorem length_le_bound_of_nodup (bound : Nat) (keys : List Nat)
    (distinct : keys.Nodup) (small : ∀ key, key ∈ keys → key < bound) :
    keys.length ≤ bound := by
  have included : keys ⊆ List.range bound := by
    intro key member
    exact List.mem_range.mpr (small key member)
  calc
    keys.length ≤ (List.range bound).length := distinct.length_le_of_subset included
    _ = bound := by simp

/-- Count parent frames before a terminal root. -/
inductive ParentDepth (forest : Forest) : Nat → Nat → Prop where
  | root (key size : Nat)
      (lookup : MicroCFTA.UnionFind.read forest key = .root size) :
      ParentDepth forest key 0
  | step (key next depth : Nat)
      (lookup : MicroCFTA.UnionFind.read forest key = .parent next)
      (tail : ParentDepth forest next depth) : ParentDepth forest key (depth + 1)

/-- Each finite path has a count of its parent frames. -/
theorem reaches_has_parentDepth
    (path : Reaches forest key representative size) :
    ∃ depth, ParentDepth forest key depth := by
  induction path with
  | root lookup => exact ⟨0, ParentDepth.root _ _ lookup⟩
  | parent lookup tail ih =>
      obtain ⟨depth, counted⟩ := ih
      exact ⟨depth + 1, ParentDepth.step _ _ _ lookup counted⟩

/-- A parent read identifies a stored parent entry. -/
theorem raw_parent_of_read
    (lookup : MicroCFTA.UnionFind.read forest key = .parent next) :
    forest key = some (Entry.parent next) := by
  cases actual : forest key with
  | none => simp [MicroCFTA.UnionFind.read, actual] at lookup
  | some entry =>
      have entryIsParent : entry = Entry.parent next := by
        simpa [MicroCFTA.UnionFind.read, actual] using lookup
      simp [entryIsParent]

/-- A counted path succeeds with one fuel unit per frame and terminal root. -/
theorem parentDepth_executes (path : ParentDepth forest key depth) :
    ∃ found, findRoot (depth + 1) forest key = some found := by
  induction path with
  | root key size lookup =>
      cases stored : forest key with
      | none => simp [findRoot, stored]
      | some entry =>
          have entryIsRoot : entry = Entry.root size := by
            simpa [MicroCFTA.UnionFind.read, stored] using lookup
          subst entry
          simp [findRoot, stored]
  | step key next depth lookup tail ih =>
      obtain ⟨found, run⟩ := ih
      have stored := raw_parent_of_read lookup
      generalize remaining : depth + 1 = remainingFuel at run ⊢
      simp [findRoot, stored, run]

/-- A deterministic search path has one parent depth. -/
theorem parentDepth_unique
    (first : ParentDepth forest key firstDepth)
    (second : ParentDepth forest key secondDepth) : firstDepth = secondDepth := by
  induction first generalizing secondDepth with
  | root key size firstLookup =>
      exact match second with
        | .root _ _ _ => rfl
        | .step _ _ _ secondLookup _ => by
            have impossible := firstLookup.symm.trans secondLookup
            cases impossible
  | step key next depth firstLookup tail ih =>
      exact match second with
        | .root _ _ secondLookup => by
            have impossible := firstLookup.symm.trans secondLookup
            cases impossible
        | .step _ otherNext otherDepth secondLookup otherTail => by
            have sameNext : next = otherNext := by
              have sameEntries : Entry.parent next = Entry.parent otherNext :=
                firstLookup.symm.trans secondLookup
              cases sameEntries
              rfl
            subst otherNext
            exact congrArg Nat.succ (ih (secondDepth := otherDepth) otherTail)

/-- Parent frames form a distinct list of stored keys. -/
theorem parentDepth_keys (path : ParentDepth forest key depth) :
    ∃ keys : List Nat,
      keys.length = depth ∧ keys.Nodup ∧
      (∀ member, member ∈ keys → ∃ next, forest member = some (Entry.parent next)) ∧
      (∀ member, member ∈ keys →
        ∃ suffixDepth, suffixDepth ≤ depth ∧ ParentDepth forest member suffixDepth) := by
  induction path with
  | root key size lookup =>
      refine ⟨[], rfl, ?_, ?_, ?_⟩
      · simp
      · intro member included
        cases included
      · intro member included
        cases included
  | step key next depth lookup tail ih =>
      obtain ⟨keys, length, distinct, stored, suffix⟩ := ih
      have keyNotMember : key ∉ keys := by
        intro included
        obtain ⟨suffixDepth, smaller, counted⟩ := suffix key included
        have sameDepth : depth + 1 = suffixDepth :=
          parentDepth_unique (ParentDepth.step key next depth lookup tail) counted
        omega
      refine ⟨key :: keys, ?_, ?_, ?_, ?_⟩
      · simp [length]
      · exact List.nodup_cons.mpr ⟨keyNotMember, distinct⟩
      · intro member included
        rcases List.mem_cons.mp included with equal | later
        · subst member
          exact ⟨next, raw_parent_of_read lookup⟩
        · exact stored member later
      · intro member included
        rcases List.mem_cons.mp included with equal | later
        · subst member
          exact ⟨depth + 1, Nat.le_refl _, ParentDepth.step key next depth lookup tail⟩
        · obtain ⟨suffixDepth, smaller, counted⟩ := suffix member later
          exact ⟨suffixDepth, Nat.le_trans smaller (Nat.le_succ depth), counted⟩

/-- Finite storage support bounds the number of parent frames. -/
theorem parentDepth_le_bound (supported : SupportedBelow bound forest)
    (path : ParentDepth forest key depth) : depth ≤ bound := by
  obtain ⟨keys, length, distinct, stored, _⟩ := parentDepth_keys path
  have small : ∀ member, member ∈ keys → member < bound := by
    intro member included
    obtain ⟨next, present⟩ := stored member included
    by_cases inside : member < bound
    · exact inside
    · have absent := supported member (Nat.le_of_not_gt inside)
      rw [present] at absent
      cases absent
  have bounded := length_le_bound_of_nodup bound keys distinct small
  omega

/-- One computed fuel succeeds for every query in a total supported forest. -/
theorem findRoot_uniformFuel (supported : SupportedBelow bound forest)
    (total : Total forest) (key : Nat) :
    ∃ found, findRoot (bound + 1) forest key = some found := by
  obtain ⟨representative, size, path⟩ := total key
  obtain ⟨depth, counted⟩ := reaches_has_parentDepth path
  have bounded := parentDepth_le_bound supported counted
  obtain ⟨found, run⟩ := parentDepth_executes counted
  refine ⟨found, ?_⟩
  have sameFuel : (depth + 1) + (bound - depth) = bound + 1 := by omega
  simpa only [sameFuel] using
    (findRoot_moreFuel (depth + 1) (bound - depth) forest key found run)


/-- Initialization supplies a common fuel for every query. -/
theorem findRoot_initial_uniformFuel (variables : List Nat) (key : Nat) :
    ∃ found, findRoot (initialBound variables + 1)
      (withInitialValues variables) key = some found := by
  have initializedTotal : Total (withInitialValues variables) :=
    MicroCFTA.UnionFind.initial_total variables
  exact findRoot_uniformFuel (supportedBelow_withInitialValues variables)
    initializedTotal key

/-- A computed common fuel makes both searches in union succeed. -/
theorem union_uniformFuel (bound : Nat) (forest : Forest) (left right : Nat)
    (supported : SupportedBelow bound forest) (parents : ParentsBelow bound forest)
    (total : Total forest) :
    let grown := max bound (max (left + 1) (right + 1))
    ∃ nextForest, union (grown + 1) (grown + 1) forest left right = some nextForest ∧
      SupportedBelow grown nextForest ∧ ParentsBelow grown nextForest := by
  let grown := max bound (max (left + 1) (right + 1))
  have support : SupportedBelow grown forest :=
    supportedBelow_mono supported (Nat.le_max_left _ _)
  have parentBound : ParentsBelow grown forest :=
    parentsBelow_mono parents (Nat.le_max_left _ _)
  have leftBelow : left < grown :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self left)
      (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
  have rightBelow : right < grown :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self right)
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
  obtain ⟨first, firstRun⟩ := findRoot_uniformFuel support total left
  obtain ⟨firstSupport, _, _⟩ := findRoot_preserves_bounds grown (grown + 1)
    forest left support parentBound leftBelow first firstRun
  have firstTotal : Total first.forest :=
    MicroCFTA.UnionFind.findRoot_total total firstRun
  obtain ⟨second, secondRun⟩ := findRoot_uniformFuel firstSupport firstTotal right
  have successful : ∃ nextForest,
      union (grown + 1) (grown + 1) forest left right = some nextForest := by
    by_cases same : first.representative = second.representative
    · simp [union, firstRun, secondRun, same]
    · by_cases smaller : first.size < second.size
      · simp [union, firstRun, secondRun, same, smaller]
      · simp [union, firstRun, secondRun, same, smaller]
  obtain ⟨nextForest, run⟩ := successful
  have bounds := union_preserves_bounds grown (grown + 1) (grown + 1)
    forest left right support parentBound leftBelow rightBelow nextForest run
  exact ⟨nextForest, run, bounds⟩

/-- Initial union succeeds with fuel computed from the input identities. -/
theorem union_initial_uniformFuel (variables : List Nat) (left right : Nat) :
    let grown := max (initialBound variables) (max (left + 1) (right + 1))
    ∃ nextForest, union (grown + 1) (grown + 1) (withInitialValues variables)
      left right = some nextForest ∧
      SupportedBelow grown nextForest ∧ ParentsBelow grown nextForest := by
  have initializedTotal : Total (withInitialValues variables) :=
    MicroCFTA.UnionFind.initial_total variables
  exact union_uniformFuel (initialBound variables) (withInitialValues variables)
    left right (supportedBelow_withInitialValues variables)
    (parentsBelow_withInitialValues variables) initializedTotal

end MicroCFTA.UnionFindSupport
