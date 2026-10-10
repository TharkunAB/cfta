import MicroCFTA.EqualityTermination

/-!
# Finite models for saturated path equalities

The model is the finite prefix tree of the recorded path set. Missing children
below an existing child index are leaves. Every node uses one supplied symbol.
At a source fixed point, equivalent endpoints have the same suffix set. Their
model subtrees are therefore equal.
-/

namespace MicroCFTA.EqualityModel
open MicroCFTA.Language MicroCFTA.EqualityNormalize MicroCFTA.EqualitySaturation MicroCFTA.EqualityTermination

/-- The maximum value of a finite list under a natural-valued measurement. -/
def maxOn (measure : α → Nat) (values : List α) : Nat := (values.map measure).foldr Nat.max 0

/-- The maximum is bounded exactly when every member is bounded. -/
theorem maxOn_le (measure : α → Nat) (values : List α) (bound : Nat) :
    maxOn measure values ≤ bound ↔ ∀ value ∈ values, measure value ≤ bound := by
  induction values with
  | nil => simp [maxOn]
  | cons value rest ih =>
      simp [maxOn, Nat.max_le]
      exact fun _ => ih

/-- Every finite-list member is bounded by the maximum. -/
theorem le_maxOn (measure : α → Nat) (values : List α) (value : α) (member : value ∈ values) :
    measure value ≤ maxOn measure values := (maxOn_le measure values _).mp (Nat.le_refl _) value member

/-- Maximum measurement depends only on set membership. -/
theorem maxOn_ext (measure : α → Nat) (first second : List α) (same : ∀ value, value ∈ first ↔ value ∈ second) :
    maxOn measure first = maxOn measure second := by
  apply Nat.le_antisymm
  · apply (maxOn_le measure first _).mpr
    intro value member
    exact le_maxOn measure second value ((same value).mp member)
  · apply (maxOn_le measure second _).mpr
    intro value member
    exact le_maxOn measure first value ((same value).mpr member)

/-- The longest recorded path controls construction recursion. -/
def depth (paths : Class) : Nat := maxOn List.length paths

/-- A nonempty path requires its first child index plus one. -/
def firstArity : List Nat → Nat
  | [] => 0
  | index :: _ => index + 1

/-- The root arity includes every requested first child index. -/
def arity (paths : Class) : Nat := maxOn firstArity paths

/-- Each child group has smaller maximum depth when a nonempty path exists. -/
theorem tails_depth (paths : Class) (index : Nat) (positive : depth paths ≠ 0) :
    depth (MicroCFTA.EqualityTrie.tailsAt index paths) < depth paths := by
  have bounded : depth (MicroCFTA.EqualityTrie.tailsAt index paths) ≤ depth paths - 1 := by
    apply (maxOn_le List.length _ _).mpr
    intro suffix member
    have original := (MicroCFTA.EqualityTrie.mem_tailsAt index paths suffix).mp member
    have bound := le_maxOn List.length paths (index :: suffix) original
    change (index :: suffix).length ≤ depth paths at bound
    simp only [List.length_cons] at bound
    omega
  omega

/-- A recorded child path is inside the constructed node's arity. -/
theorem member_arity (paths : Class) (index : Nat) (suffix : List Nat) (member : index :: suffix ∈ paths) : index < arity paths := by
  have bound := le_maxOn firstArity paths (index :: suffix) member
  change index + 1 ≤ arity paths at bound
  omega

/-- Build a finite tree that contains exactly the requested branches and their necessary padding. -/
def tree (symbol : Symbol) (paths : Class) : Term Symbol :=
  if _zero : depth paths = 0 then .node symbol []
  else .node symbol ((List.range (arity paths)).map (fun index => tree symbol (MicroCFTA.EqualityTrie.tailsAt index paths)))
termination_by depth paths
decreasing_by exact tails_depth paths index _zero

/-- Tree construction ignores duplicate paths and their enumeration order. -/
theorem tree_ext (symbol : Symbol) (first second : Class) (same : ∀ path, path ∈ first ↔ path ∈ second) :
    tree symbol first = tree symbol second := by
  have sameDepth : depth first = depth second := maxOn_ext List.length first second same
  have sameArity : arity first = arity second := maxOn_ext firstArity first second same
  by_cases zero : depth first = 0
  · simp [tree, zero, ← sameDepth]
  · have otherPositive : depth second ≠ 0 := by simpa [← sameDepth] using zero
    rw [tree, tree]
    simp only [zero, otherPositive, ↓reduceDIte, ← sameArity]
    apply congrArg (Term.node symbol)
    apply List.map_congr_left
    intro index member
    exact tree_ext symbol _ _ (fun suffix =>
      (MicroCFTA.EqualityTrie.mem_tailsAt index first suffix).trans
        ((same (index :: suffix)).trans (MicroCFTA.EqualityTrie.mem_tailsAt index second suffix).symm))
termination_by depth first
decreasing_by exact tails_depth first index zero

/-- Follow a finite path through the recorded-path set. -/
def suffixSet : List Nat → Class → Class
  | [], paths => paths
  | index :: rest, paths => suffixSet rest (MicroCFTA.EqualityTrie.tailsAt index paths)

/-- Suffix-set membership is precisely recorded-path extension. -/
theorem mem_suffixSet (base suffix : List Nat) (paths : Class) :
    suffix ∈ suffixSet base paths ↔ base ++ suffix ∈ paths := by
  induction base generalizing paths with
  | nil => rfl
  | cons index rest ih =>
      rw [suffixSet, ih, MicroCFTA.EqualityTrie.mem_tailsAt]
      rfl

/-- At a requested child, the model contains exactly the recursive group tree. -/
theorem tree_child (symbol : Symbol) (paths : Class) (index : Nat) (suffix : List Nat)
    (requested : index :: suffix ∈ paths) :
    (tree symbol paths).atPath [index] = some (tree symbol (MicroCFTA.EqualityTrie.tailsAt index paths)) := by
  have positive : depth paths ≠ 0 := by
    have bound := le_maxOn List.length paths (index :: suffix) requested
    change (index :: suffix).length ≤ depth paths at bound
    simp only [List.length_cons] at bound
    omega
  have indexBound := member_arity paths index suffix requested
  rw [tree]
  simp only [positive, ↓reduceDIte, Term.atPath]
  simp [indexBound]

/-- Following a recorded path reaches the model built from its exact suffix set. -/
theorem tree_atPath (symbol : Symbol) (paths : Class) (base suffix : List Nat)
    (requested : base ++ suffix ∈ paths) :
    (tree symbol paths).atPath base = some (tree symbol (suffixSet base paths)) := by
  induction base generalizing paths with
  | nil => rfl
  | cons index rest ih =>
      have rootChild := tree_child symbol paths index (rest ++ suffix) requested
      have childRequested : rest ++ suffix ∈ MicroCFTA.EqualityTrie.tailsAt index paths :=
        (MicroCFTA.EqualityTrie.mem_tailsAt _ _ _).mpr requested
      have recursive := ih _ childRequested
      have composed := atPath_append (tree symbol paths) [index] rest
      rw [rootChild] at composed
      simpa [suffixSet, recursive] using composed

/-- Saturation makes the recorded suffix sets equal at every pair of class members. -/
theorem fixedPoint_suffixes (classes : Constraints) (fixed : congruenceStep classes = some classes)
    (paths : Class) (member : paths ∈ classes) (left right : List Nat) (leftMember : left ∈ paths) (rightMember : right ∈ paths)
    (suffix : List Nat) : left ++ suffix ∈ members classes ↔ right ++ suffix ∈ members classes := by
  have forward : ∀ first ∈ paths, ∀ second ∈ paths,
      first ++ suffix ∈ members classes → second ++ suffix ∈ members classes := by
    intro first firstMember second secondMember recorded
    have equal : inSame classes first second = true := (inSame_correct _ _ _).mpr ⟨paths, member, firstMember, secondMember⟩
    have propagated := step_suffix classes classes first second suffix equal recorded fixed
    obtain ⟨component, componentMember, _, present⟩ := (inSame_correct _ _ _).mp propagated
    exact (mem_members _ _).mpr ⟨component, componentMember, present⟩
  exact ⟨forward left leftMember right rightMember, forward right rightMember left leftMember⟩

/-- The finite prefix-tree model satisfies every class at a source fixed point. -/
theorem fixedPoint_model (symbol : Symbol) (classes : Constraints) (fixed : congruenceStep classes = some classes) :
    Satisfies (tree symbol (members classes)) classes := by
  intro paths member left leftMember right rightMember _
  have leftRecorded : left ++ [] ∈ members classes := by simpa using (mem_members _ _).mpr ⟨paths, member, leftMember⟩
  have rightRecorded : right ++ [] ∈ members classes := by simpa using (mem_members _ _).mpr ⟨paths, member, rightMember⟩
  have atLeft := tree_atPath symbol (members classes) left [] leftRecorded
  have atRight := tree_atPath symbol (members classes) right [] rightRecorded
  have sameTrees : tree symbol (suffixSet left (members classes)) = tree symbol (suffixSet right (members classes)) := by
    apply tree_ext
    intro suffix
    rw [mem_suffixSet, mem_suffixSet]
    exact fixedPoint_suffixes classes fixed paths member left right leftMember rightMember suffix
  exact ⟨tree symbol (suffixSet left (members classes)), atLeft, atRight.trans (congrArg some sameTrees.symm)⟩

/-- Every successful normalized result has a finite model over any supplied node symbol. -/
theorem normalized_has_model (symbol : Symbol) (fuel : Nat) (original output : Constraints)
    (success : mkEqConstraints fuel original = .normalized output) :
    ∃ term : Term Symbol, Satisfies term original := by
  obtain ⟨_, _, _, fixed⟩ := mkEqConstraints_invariants fuel original output success
  have finished : mkEqConstraints fuel original ≠ .timeout := by simp [success]
  refine ⟨tree symbol (members output), ?_⟩
  have equivalent := mkEqConstraints_correct (tree symbol (members output)) fuel original finished
  rw [success] at equivalent
  exact equivalent.mp (fixedPoint_model symbol output fixed)

/-- Prefix contradiction is complete: total normalization rejects precisely the inputs with no finite model. -/
theorem contradiction_iff_no_model (symbol : Symbol) (classes : Constraints) :
    mkEqConstraints (normalizationBound classes) classes = .contradiction ↔
      ¬ ∃ term : Term Symbol, Satisfies term classes := by
  constructor
  · intro rejected
    rintro ⟨term, satisfied⟩
    have equivalent := mkEqConstraints_total_correct term classes
    rw [rejected] at equivalent
    exact equivalent.mpr satisfied
  · intro impossible
    rcases mkEqConstraints_total_cases classes with rejected | ⟨output, success, _⟩
    · exact rejected
    · exact False.elim (impossible (normalized_has_model symbol (normalizationBound classes) classes output success))

end MicroCFTA.EqualityModel
