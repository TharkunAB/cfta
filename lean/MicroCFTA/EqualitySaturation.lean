import MicroCFTA.EqualityNormalize

/-!
# Equality trie descent and saturation progress

The trie scan follows `pathTrieHasAtLeastTwoPaths`. Its accumulator records
whether an earlier branch contains a path. Descent removes only classes that
have fewer than two distinct suffix paths.
-/

namespace MicroCFTA.EqualitySaturation
open MicroCFTA.Language
open MicroCFTA.EqualityTrie
open MicroCFTA.EqualityNormalize

mutual
  /-- Check whether a trie contains a terminal on any branch. -/
  def hasAnyPath : Trie → Bool
    | .empty => false
    | .terminal => true
    | .branch children => anyChildren children
  /-- Scan the finite child map for a represented path. -/
  def anyChildren : List (Nat × Trie) → Bool
    | [] => false
    | (_, child) :: rest => hasAnyPath child || anyChildren rest
end

mutual
  /-- Count only enough terminals to decide whether a second path is present. -/
  def hasTwoFrom (seenOne : Bool) : Trie → Bool
    | .empty => false
    | .terminal => seenOne
    | .branch children => twoChildren seenOne children
  /-- Continue the source short-circuit scan through the indexed children. -/
  def twoChildren (seenOne : Bool) : List (Nat × Trie) → Bool
    | [] => false
    | (_, child) :: rest =>
        if hasTwoFrom seenOne child then true
        else if hasAnyPath child then seenOne || twoChildren true rest
        else twoChildren seenOne rest
end

/-- The exported behavior of the source's two-path predicate. -/
def pathTrieHasAtLeastTwoPaths (trie : Trie) : Bool := hasTwoFrom false trie

mutual
  /-- Terminal reachability is exact, including malformed empty branches. -/
  theorem hasAnyPath_correct (trie : Trie) :
      hasAnyPath trie = true ↔ 0 < (fromPathTrie trie).length := by
    cases trie with
    | empty => simp [hasAnyPath, fromPathTrie]
    | terminal => simp [hasAnyPath, fromPathTrie]
    | branch children => exact anyChildren_correct children
  /-- A branch contains a path exactly when its path list is nonempty. -/
  theorem anyChildren_correct (children : List (Nat × Trie)) :
      anyChildren children = true ↔ 0 < (fromChildren children).length := by
    cases children with
    | nil => simp [anyChildren, fromChildren]
    | cons entry rest =>
        obtain ⟨index, child⟩ := entry
        simp only [anyChildren, Bool.or_eq_true, hasAnyPath_correct, anyChildren_correct,
          fromChildren, List.length_append, List.length_map]
        omega
end

mutual
  /-- The source Boolean accumulator adds one previously seen terminal. -/
  theorem hasTwoFrom_correct (seenOne : Bool) (trie : Trie) :
      hasTwoFrom seenOne trie = true ↔ (if seenOne then 1 else 0) + (fromPathTrie trie).length ≥ 2 := by
    cases trie with
    | empty => cases seenOne <;> simp [hasTwoFrom, fromPathTrie]
    | terminal => cases seenOne <;> simp [hasTwoFrom, fromPathTrie]
    | branch children => exact twoChildren_correct seenOne children
  /-- Short-circuit child scanning returns precisely the two-terminal threshold. -/
  theorem twoChildren_correct (seenOne : Bool) (children : List (Nat × Trie)) :
      twoChildren seenOne children = true ↔ (if seenOne then 1 else 0) + (fromChildren children).length ≥ 2 := by
    cases children with
    | nil => cases seenOne <;> simp [twoChildren, fromChildren]
    | cons entry rest =>
        obtain ⟨index, child⟩ := entry
        have childTwo := hasTwoFrom_correct seenOne child
        have childAny := hasAnyPath_correct child
        have restOriginal := twoChildren_correct seenOne rest
        have restSeen := twoChildren_correct true rest
        cases foundTwo : hasTwoFrom seenOne child <;> cases foundAny : hasAnyPath child <;> cases seenOne <;>
          simp_all [twoChildren, fromChildren] <;> omega

end

/-- The source cardinality helper is exact for represented paths. -/
theorem pathTrieHasAtLeastTwoPaths_correct (trie : Trie) :
    pathTrieHasAtLeastTwoPaths trie = true ↔ 2 ≤ (fromPathTrie trie).length := by
  simpa [pathTrieHasAtLeastTwoPaths] using hasTwoFrom_correct false trie


/-- A distinct path list has two members exactly when its PCS class is nontrivial. -/
theorem nontrivial_length (paths : List (List Nat)) (unique : paths.Nodup) :
    Nontrivial paths ↔ 2 ≤ paths.length := by
  cases paths with
  | nil => simp [Nontrivial]
  | cons first rest =>
      cases rest with
      | nil => simp [Nontrivial]
      | cons second rest =>
          have distinct : first ≠ second := by
            intro same
            subst second
            exact (List.nodup_cons.mp unique).1 (by simp)
          constructor
          · intro _; simp
          · intro _; exact ⟨first, by simp, second, by simp, distinct⟩

/-- The structural scan decides exactly whether a valid trie denotes a nontrivial PCS class. -/
theorem pathTrieHasAtLeastTwoPaths_nontrivial (trie : Trie) (valid : Valid trie) :
    pathTrieHasAtLeastTwoPaths trie = true ↔ Nontrivial (fromPathTrie trie) :=
  (pathTrieHasAtLeastTwoPaths_correct trie).trans
    (nontrivial_length _ (supported_nodup _ (fromPathTrie_supported trie valid))).symm

/-- The source descent helper retains exactly tries with two remaining suffix paths. -/
def descendNontrivial (index : Nat) (trie : Trie) : Option Trie :=
  let descended := pathTrieDescend trie index
  if pathTrieHasAtLeastTwoPaths descended then some descended else none

/-- Descend a source class list through its trie representations. -/
def descendTries (index : Nat) (tries : List Trie) : List Trie := tries.filterMap (descendNontrivial index)

/-- Source trie descent has the same PCS meaning as direct path-class descent. -/
theorem descendTries_correct (term : Term Symbol) (index : Nat) (tries : List Trie)
    (valid : ∀ trie ∈ tries, Valid trie) :
    Satisfies term ((descendTries index tries).map fromPathTrie) ↔
      Satisfies term (eqConstraintsDescend index (tries.map fromPathTrie)) := by
  rw [eqConstraintsDescend_exact]
  simp only [List.forall_mem_map]
  constructor
  · intro satisfied trie member left leftMember right rightMember different
    have atLeft := (descend_exact trie (valid trie member) index left).mpr leftMember
    have atRight := (descend_exact trie (valid trie member) index right).mpr rightMember
    have nontrivial : Nontrivial (fromPathTrie (pathTrieDescend trie index)) :=
      ⟨left, atLeft, right, atRight, different⟩
    have keep := (pathTrieHasAtLeastTwoPaths_nontrivial _ (descend_valid trie (valid trie member) index)).mpr nontrivial
    have selected : pathTrieDescend trie index ∈ descendTries index tries :=
      List.mem_filterMap.mpr ⟨trie, member, by simp [descendNontrivial, keep]⟩
    exact satisfied _ (List.mem_map.mpr ⟨pathTrieDescend trie index, selected, rfl⟩) left atLeft right atRight different
  · intro satisfied paths member left leftMember right rightMember different
    obtain ⟨descended, descendedMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨trie, trieMember, selected⟩ := List.mem_filterMap.mp descendedMember
    dsimp only [descendNontrivial] at selected
    split at selected
    next kept =>
      have same : descended = pathTrieDescend trie index := Option.some.inj selected.symm
      subst descended
      exact satisfied trie trieMember left ((descend_exact trie (valid trie trieMember) index left).mp leftMember)
        right ((descend_exact trie (valid trie trieMember) index right).mp rightMember) different
    next discarded => simp at selected

/-- Source descent retains valid ascending maps for lazy set reconstruction. -/
theorem descendTries_invariants (index : Nat) (tries : List Trie)
    (valid : ∀ trie ∈ tries, Valid trie) (ordered : ∀ trie ∈ tries, Ascending trie)
    (descended : Trie) (member : descended ∈ descendTries index tries) :
    Valid descended ∧ Ascending descended ∧ (fromPathTrie descended).Nodup ∧
      (fromPathTrie descended).Pairwise (List.Lex (· < ·)) ∧ Nontrivial (fromPathTrie descended) := by
  obtain ⟨trie, trieMember, selected⟩ := List.mem_filterMap.mp member
  dsimp only [descendNontrivial] at selected
  split at selected
  next kept =>
    have same : descended = pathTrieDescend trie index := Option.some.inj selected.symm
    subst descended
    have validChild := descend_valid trie (valid trie trieMember) index
    have sortedChild := descend_ascending trie (ordered trie trieMember) index
    exact ⟨validChild, sortedChild, supported_nodup _ (fromPathTrie_supported _ validChild),
      fromPathTrie_increasing _ sortedChild, (pathTrieHasAtLeastTwoPaths_nontrivial _ validChild).mp kept⟩
  next discarded => simp at selected


/-- The canonical component invariants maintained between source saturation steps. -/
def NormalState (classes : Constraints) : Prop :=
  Active classes ∧ classes.Pairwise (fun left right => overlap left right = false) ∧
    classes.Pairwise (· ≤ ·) ∧ ∀ paths ∈ classes, canonicalClass paths = paths

/-- Completion establishes the canonical component invariants. -/
theorem complete_normal (classes : Constraints) (active : Active classes) : NormalState (complete classes) :=
  ⟨complete_active classes active, complete_disjoint classes, canonicalize_ordered _, canonicalize_members _⟩

/-- A successful step maintains canonical components. -/
theorem step_normal (classes output : Constraints) (active : Active classes)
    (success : congruenceStep classes = some output) : NormalState output := by
  dsimp only [congruenceStep] at success
  split at success
  next contradiction => simp at success
  next consistent =>
    have same : output = complete (addCongruences classes) := Option.some.inj success.symm
    subst output
    exact complete_normal _ (addCongruences_active classes active)

/-- A successful step retains every old component within a new component. -/
theorem step_covers (classes output : Constraints) (success : congruenceStep classes = some output) : Covers classes output := by
  dsimp only [congruenceStep] at success
  split at success
  next contradiction => simp at success
  next consistent =>
    have same : output = complete (addCongruences classes) := Option.some.inj success.symm
    subst output
    intro paths member
    exact complete_covers _ paths (List.mem_append_left _ member)

/-- Direct same-component lookup on canonical class lists. -/
def inSame (classes : Constraints) (left right : List Nat) : Bool :=
  classes.any (fun paths => decide (left ∈ paths) && decide (right ∈ paths))

/-- Direct component lookup has its literal membership meaning. -/
theorem inSame_correct (classes : Constraints) (left right : List Nat) :
    inSame classes left right = true ↔ ∃ paths ∈ classes, left ∈ paths ∧ right ∈ paths := by
  simp [inSame, List.any_eq_true]

/-- Disjoint class lists already contain their full connectivity closure. -/
theorem normal_connected (classes : Constraints) (normal : NormalState classes) (left right : List Nat) :
    inSame classes left right = true ↔ Connected classes left right := by
  rw [inSame_correct]
  constructor
  · rintro ⟨paths, member, first, second⟩
    exact .edge paths member first second
  · intro connected
    induction connected with
    | edge paths member first second => exact ⟨paths, member, first, second⟩
    | @trans left middle right first second leftIH rightIH =>
        obtain ⟨firstClass, firstMember, leftMember, pivotFirst⟩ := leftIH
        obtain ⟨secondClass, secondMember, pivotSecond, rightMember⟩ := rightIH
        have same := components_equal classes normal.2.1 firstClass secondClass firstMember secondMember middle pivotFirst pivotSecond
        subst secondClass
        exact ⟨firstClass, firstMember, leftMember, rightMember⟩

/-- Equal same-component relations determine equal canonical states. -/
theorem normal_ext (first second : Constraints) (firstNormal : NormalState first) (secondNormal : NormalState second)
    (same : ∀ left right, inSame first left right = inSame second left right) : first = second := by
  apply canonical_partition_unique first first second firstNormal.1 secondNormal.1
    firstNormal.2.1 secondNormal.2.1 firstNormal.2.2.1 secondNormal.2.2.1 firstNormal.2.2.2 secondNormal.2.2.2
  · intro left right
    exact (inSame_correct first left right).symm.trans (normal_connected first firstNormal left right)
  · intro left right
    rw [← inSame_correct, ← same left right]
    exact normal_connected first firstNormal left right

/-- Class containment makes same-component lookup monotone. -/
theorem inSame_mono (first second : Constraints) (covers : Covers first second) (left right : List Nat)
    (before : inSame first left right = true) : inSame second left right = true := by
  obtain ⟨paths, member, firstMember, secondMember⟩ := (inSame_correct _ _ _).mp before
  obtain ⟨component, componentMember, included⟩ := covers paths member
  exact (inSame_correct _ _ _).mpr ⟨component, componentMember, included left firstMember, included right secondMember⟩

/-- Enumerate the existing paths of length at most the supplied bound. -/
def boundedPaths : Nat → Term Symbol → List (List Nat)
  | 0, _ => [[]]
  | fuel + 1, .node _ children => [] :: children.zipIdx.flatMap (fun entry =>
      (boundedPaths fuel entry.1).map (entry.2 :: ·))

/-- Bounded path enumeration is exact. -/
theorem boundedPaths_correct (fuel : Nat) (term : Term Symbol) (path : List Nat) :
    path ∈ boundedPaths fuel term ↔ (∃ value, term.atPath path = some value) ∧ path.length ≤ fuel := by
  induction fuel generalizing term path with
  | zero => cases path <;> simp [boundedPaths, Term.atPath]
  | succ fuel ih =>
      cases term with
      | node symbol children =>
          cases path with
          | nil => simp [boundedPaths, Term.atPath]
          | cons index suffix =>
              simp only [boundedPaths, List.mem_cons, List.cons_ne_nil, false_or, List.mem_flatMap, List.mem_map]
              constructor
              · rintro ⟨⟨child, key⟩, selected, tail, member, equal⟩
                have same := List.cons.inj equal
                have keySame : key = index := same.1
                have tailSame : tail = suffix := same.2
                subst key
                subst tail
                have found := List.mem_zipIdx_iff_getElem?.mp selected
                obtain ⟨⟨value, atSuffix⟩, short⟩ := (ih child suffix).mp member
                exact ⟨⟨value, by simpa [Term.atPath, found] using atSuffix⟩, by simpa using Nat.succ_le_succ short⟩
              · rintro ⟨⟨value, found⟩, bound⟩
                obtain ⟨child, atChild, atSuffix⟩ := Option.bind_eq_some_iff.mp found
                refine ⟨(child, index), List.mem_zipIdx_iff_getElem?.mpr atChild, suffix, ?_, rfl⟩
                exact (ih child suffix).mpr ⟨⟨value, atSuffix⟩, by simpa using Nat.le_of_succ_le_succ bound⟩

/-- Every valid path of a finite term lies in this explicit finite domain. -/
def termPaths (term : Term Symbol) : List (List Nat) := boundedPaths term.height term

/-- Term height makes path enumeration complete without an external bound. -/
theorem termPaths_correct (term : Term Symbol) (path : List Nat) :
    path ∈ termPaths term ↔ ∃ value, term.atPath path = some value := by
  rw [termPaths, boundedPaths_correct]
  constructor
  · exact And.left
  · rintro ⟨value, found⟩
    have heightBound := atPath_height_bound term value path found
    exact ⟨⟨value, found⟩, by omega⟩

/-- All recorded paths of a state lie in a finite domain. -/
def Within (domain : List (List Nat)) (classes : Constraints) : Prop :=
  ∀ path ∈ members classes, path ∈ domain

/-- A satisfying finite tree bounds every recorded path of an active state. -/
theorem satisfied_within (term : Term Symbol) (classes : Constraints) (active : Active classes)
    (satisfied : Satisfies term classes) : Within (termPaths term) classes := by
  intro path member
  exact (termPaths_correct term path).mpr (member_exists term classes active satisfied path member)

/-- Ordered pairs of paths provide a finite bound on relation growth. -/
def pathPairs (domain : List (List Nat)) : List (List Nat × List Nat) :=
  domain.flatMap (fun left => domain.map (left, ·))

/-- Pair enumeration contains precisely both domain members. -/
theorem mem_pathPairs (domain : List (List Nat)) (left right : List Nat) :
    (left, right) ∈ pathPairs domain ↔ left ∈ domain ∧ right ∈ domain := by
  simp [pathPairs]

/-- Count the finite domain pairs already identified by the state. -/
def relationCount (domain : List (List Nat)) (classes : Constraints) : Nat :=
  (pathPairs domain).countP (fun pair => inSame classes pair.1 pair.2)

/-- No state can identify more pairs than the finite pair domain contains. -/
theorem relationCount_bound (domain : List (List Nat)) (classes : Constraints) :
    relationCount domain classes ≤ (pathPairs domain).length := List.countP_le_length


/-- Pointwise predicate growth cannot decrease a finite occurrence count. -/
theorem countP_mono (first second : α → Bool) (values : List α)
    (monotone : ∀ value ∈ values, first value = true → second value = true) :
    values.countP first ≤ values.countP second := by
  induction values with
  | nil => simp
  | cons value rest ih =>
      have atHead := monotone value (by simp)
      have atTail := ih (fun item member => monotone item (by simp [member]))
      cases firstHead : first value <;> cases secondHead : second value <;> simp_all <;> omega

/-- One newly true list member makes a monotone finite count strictly increase. -/
theorem countP_strict (first second : α → Bool) (values : List α)
    (monotone : ∀ value ∈ values, first value = true → second value = true)
    (fresh : ∃ value ∈ values, first value = false ∧ second value = true) :
    values.countP first < values.countP second := by
  induction values with
  | nil => simp at fresh
  | cons head rest ih =>
      obtain ⟨value, member, absent, present⟩ := fresh
      rcases List.mem_cons.mp member with same | member
      · subst value
        have tailBound := countP_mono first second rest (fun value member => monotone value (by simp [member]))
        simp [absent, present]
        omega
      · have tailStrict := ih (fun value member => monotone value (by simp [member])) ⟨value, member, absent, present⟩
        have headBound := monotone head (by simp)
        cases firstHead : first head <;> cases secondHead : second head <;> simp_all <;> omega

/-- A nonstationary canonical step must add a pair inside any finite domain containing its output. -/
theorem changed_pair (domain : List (List Nat)) (first second : Constraints)
    (firstNormal : NormalState first) (secondNormal : NormalState second) (covers : Covers first second)
    (within : Within domain second) (changed : second ≠ first) :
    ∃ pair ∈ pathPairs domain, inSame first pair.1 pair.2 = false ∧ inSame second pair.1 pair.2 = true := by
  apply Classical.byContradiction
  intro noFresh
  have same : ∀ left right, inSame first left right = inSame second left right := by
    intro left right
    apply Bool.eq_iff_iff.mpr
    constructor
    · exact inSame_mono first second covers left right
    · intro after
      obtain ⟨paths, member, leftMember, rightMember⟩ := (inSame_correct second left right).mp after
      have pairMember : (left, right) ∈ pathPairs domain := (mem_pathPairs domain left right).mpr
        ⟨within left ((mem_members _ _).mpr ⟨paths, member, leftMember⟩),
          within right ((mem_members _ _).mpr ⟨paths, member, rightMember⟩)⟩
      cases before : inSame first left right with
      | true => rfl
      | false => exact False.elim (noFresh ⟨(left, right), pairMember, before, after⟩)
  exact changed (normal_ext first second firstNormal secondNormal same).symm

/-- Every nonstationary step increases the finite-domain relation count. -/
theorem relationCount_strict (domain : List (List Nat)) (first second : Constraints)
    (firstNormal : NormalState first) (secondNormal : NormalState second) (covers : Covers first second)
    (within : Within domain second) (changed : second ≠ first) :
    relationCount domain first < relationCount domain second :=
  countP_strict _ _ _ (fun pair _ => inSame_mono first second covers pair.1 pair.2)
    (changed_pair domain first second firstNormal secondNormal covers within changed)

/-- A finite model bounds how many strict relation-growth steps can occur. -/
theorem fixMaybe_finishes_with_model (term : Term Symbol) (fuel : Nat) (classes : Constraints)
    (normal : NormalState classes) (satisfied : Satisfies term classes)
    (enough : (pathPairs (termPaths term)).length - relationCount (termPaths term) classes + 1 ≤ fuel) :
    fixMaybe fuel classes ≠ .timeout := by
  induction fuel generalizing classes with
  | zero => omega
  | succ fuel ih =>
      cases stepped : congruenceStep classes with
      | none => simp [fixMaybe, stepped]
      | some next =>
          by_cases stable : next = classes
          · simp [fixMaybe, stepped, stable]
          · have nextNormal := step_normal classes next normal.1 stepped
            have nextSatisfied : Satisfies term next := by
              have equivalent := congruenceStep_correct term classes normal.1
              rw [stepped] at equivalent
              exact equivalent.mpr satisfied
            have growth := relationCount_strict (termPaths term) classes next normal nextNormal
              (step_covers classes next stepped) (satisfied_within term next nextNormal.1 nextSatisfied) stable
            have currentBound := relationCount_bound (termPaths term) classes
            have nextBound := relationCount_bound (termPaths term) next
            have finishes := ih next nextNormal nextSatisfied (by omega)
            simpa [fixMaybe, stepped, stable] using finishes

/-- A model-independent execution bound can be computed from one finite satisfying tree. -/
def modelBound (term : Term Symbol) : Nat := (pathPairs (termPaths term)).length + 1

/-- Every satisfiable input PCS finishes normalization without an assumed execution bound. -/
theorem mkEqConstraints_terminates_for_model (term : Term Symbol) (classes : Constraints)
    (satisfied : Satisfies term classes) :
    mkEqConstraints (modelBound term) classes ≠ .timeout := by
  have normal := complete_normal (prepare classes) (prepare_active classes)
  have prepared : Satisfies term (complete (prepare classes)) :=
    (complete_correct term _).mpr ((prepare_correct term classes).mpr satisfied)
  exact fixMaybe_finishes_with_model term (modelBound term) _ normal prepared (by unfold modelBound; omega)

/-- A satisfiable input normalizes to a successful equivalent constraint set. -/
theorem mkEqConstraints_satisfiable_completeness (term : Term Symbol) (classes : Constraints)
    (satisfied : Satisfies term classes) :
    ∃ output, mkEqConstraints (modelBound term) classes = .normalized output ∧
      ∀ other : Term Symbol, Satisfies other output ↔ Satisfies other classes := by
  have finished := mkEqConstraints_terminates_for_model term classes satisfied
  have model := (mkEqConstraints_correct term (modelBound term) classes finished).mpr satisfied
  cases result : mkEqConstraints (modelBound term) classes with
  | timeout => exact False.elim (finished result)
  | contradiction => simp [result, RunSat] at model
  | normalized output =>
      refine ⟨output, rfl, ?_⟩
      intro other
      have equivalent := mkEqConstraints_correct other (modelBound term) classes finished
      simpa [result, RunSat] using equivalent

end MicroCFTA.EqualitySaturation
