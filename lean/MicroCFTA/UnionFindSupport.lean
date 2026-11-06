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

end MicroCFTA.UnionFindSupport
