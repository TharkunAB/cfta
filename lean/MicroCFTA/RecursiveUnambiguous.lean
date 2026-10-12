import MicroCFTA.AutomatonAmbiguity
import MicroCFTA.TablePosition

/-!
# The cyclic source gate derives unique size classes

Child products have no repeated forest. Different size splits cannot produce
the same forest. Disjoint source alternatives then give distinct terms in
each exact node-count class, including recursive state graphs.
-/
namespace MicroCFTA.RecursiveUnambiguous
open Language RecursiveSize SizedRank

/-- The source child-product constructor has a unique prefix and final child. -/
theorem snoc_unique (first second : List Value) (left right : Value)
    (same : first ++ [left] = second ++ [right]) : first = second ∧ left = right := by
  have pieces := List.append_inj' same (by simp)
  exact ⟨pieces.1, List.cons.inj pieces.2 |>.1⟩

/-- One fixed size split preserves uniqueness of the prefix-major Cartesian product. -/
theorem product_nodup (prefixes : List (List Value)) (children : List Value)
    (prefixUnique : prefixes.Nodup) (childUnique : children.Nodup) :
    (prefixes.flatMap (fun built => children.map (fun child => built ++ [child]))).Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro built _
    apply List.pairwise_map.mpr
    apply childUnique.imp
    intro left right different same
    exact different (snoc_unique built built left right same).2
  · apply prefixUnique.imp
    intro first second different left leftMember right rightMember same
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp leftMember
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp rightMember
    exact different (snoc_unique first second a b same).1

/-- Prefix node count separates every distinct size split in the actual convolution. -/
theorem extendForests_nodup (prefixes : Nat → List (List (Term Symbol)))
    (children : Nat → List (Term Symbol)) (size : Nat)
    (prefixUnique : ∀ part, part ≤ size → (prefixes part).Nodup)
    (prefixSize : ∀ part, part ≤ size → ∀ built ∈ prefixes part, forestSize built = part)
    (childUnique : ∀ part, part ≤ size → (children part).Nodup) :
    (extendForests prefixes children size).Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro part member
    have within : part ≤ size := by have := List.mem_range.mp member; omega
    exact product_nodup _ _ (prefixUnique part within) (childUnique (size - part) (by omega))
  · apply (List.nodup_range (n := size + 1)).imp_of_mem
    intro first second firstMember secondMember different left leftMember right rightMember same
    obtain ⟨a, aMember, x, xMember, leftSame⟩ :=
      (by simpa only [List.mem_flatMap, List.mem_map] using leftMember :
        ∃ a ∈ prefixes first, ∃ x ∈ children (size - first), a ++ [x] = left)
    obtain ⟨b, bMember, y, yMember, rightSame⟩ :=
      (by simpa only [List.mem_flatMap, List.mem_map] using rightMember :
        ∃ b ∈ prefixes second, ∃ y ∈ children (size - second), b ++ [y] = right)
    have samePrefix := (snoc_unique a b x y (leftSame.trans (same.trans rightSame.symm))).1
    have firstSize := prefixSize first (by have := List.mem_range.mp firstMember; omega) a aMember
    have secondSize := prefixSize second (by have := List.mem_range.mp secondMember; omega) b bMember
    exact different (firstSize.symm.trans ((congrArg forestSize samePrefix).trans secondSize))

/-- The actual convolution retains the exact total node count. -/
theorem extendForests_size (prefixes : Nat → List (List (Term Symbol)))
    (children : Nat → List (Term Symbol)) (size : Nat)
    (prefixSize : ∀ part, part ≤ size → ∀ built ∈ prefixes part, forestSize built = part)
    (childSize : ∀ part, part ≤ size → ∀ child ∈ children part, nodeSize child = part)
    (built : List (Term Symbol)) (member : built ∈ extendForests prefixes children size) :
    forestSize built = size := by
  obtain ⟨part, partMember, builtPrefix, prefixMember, child, childMember, same⟩ :=
    (by simpa only [extendForests, List.mem_flatMap, List.mem_map] using member :
      ∃ part ∈ List.range (size + 1), ∃ builtPrefix ∈ prefixes part,
        ∃ child ∈ children (size - part), builtPrefix ++ [child] = built)
  subst built
  have within : part ≤ size := by have := List.mem_range.mp partMember; omega
  rw [forestSize_snoc, prefixSize part within builtPrefix prefixMember,
    childSize (size - part) (by omega) child childMember]
  omega

/-- Every source forest fold is unique and exactly sized when its child classes are. -/
theorem forests_unique (children : Nat → State → List (Term Symbol)) (states : List State)
    (bound : Nat)
    (childClasses : ∀ state ∈ states, ∀ size, size ≤ bound →
      (children size state).Nodup ∧ ∀ term ∈ children size state, nodeSize term = size) :
    ∀ size, size ≤ bound → (forests children states size).Nodup ∧
      ∀ terms ∈ forests children states size, forestSize terms = size := by
  induction states using snoc_induction with
  | empty =>
      intro size _
      simp only [forests, List.foldl_nil, emptyForests]
      split
      · rename_i zero
        simp [zero, forestSize]
      · simp
  | step states state ih =>
      have before := ih (fun child member => childClasses child (List.mem_append_left _ member))
      have last := childClasses state (by simp)
      intro size within
      rw [forests_snoc]
      refine ⟨extendForests_nodup _ _ size (fun part small => (before part (by omega)).1)
        (fun part small => (before part (by omega)).2) (fun part small => (last part (by omega)).1), ?_⟩
      exact extendForests_size _ _ size (fun part small => (before part (by omega)).2)
        (fun part small => (last part (by omega)).2)

/-- A local row gate, rather than a desired whole-language premise. -/
def DisjointRows (automaton : Automaton State Symbol) (state : State) : Prop :=
  (automaton state).Pairwise (fun first second => ∀ term,
    AutomatonAmbiguity.EdgeLanguage (Accepts automaton) first term →
      ¬AutomatonAmbiguity.EdgeLanguage (Accepts automaton) second term)

/-- Local disjointness on any child-closed scope derives exact-size term uniqueness. -/
theorem enumerate_nodup (automaton : Automaton State Symbol) (plain : Decoder.Plain automaton)
    (scope : State → Prop)
    (closed : ∀ state, scope state → ∀ edge ∈ automaton state, ∀ child ∈ edge.children, scope child)
    (separate : ∀ state, scope state → DisjointRows automaton state)
    (size : Nat) (state : State) (inside : scope state) :
    (RecursiveSize.enumerate automaton size state).Nodup := by
  induction size using Nat.strongRecOn generalizing state with
  | ind size ih =>
      cases size with
      | zero => simp [enumerate_zero]
      | succ budget =>
          let children := fun childSize childState =>
            if _smaller : childSize ≤ budget then RecursiveSize.enumerate automaton childSize childState else []
          let outputs := fun edge : Edge State Symbol =>
            (forests children edge.children budget).map (Term.node edge.label)
          have childExact : ∀ childSize, childSize ≤ budget → ∀ childState child,
              child ∈ children childSize childState ↔ Accepts automaton childState child ∧ nodeSize child = childSize := by
            intro childSize smaller childState child
            simp only [children, dite_eq_left smaller]
            exact mem_enumerate_iff automaton plain childSize childState child
          have sound : ∀ edge ∈ automaton state, ∀ term ∈ outputs edge,
              AutomatonAmbiguity.EdgeLanguage (Accepts automaton) edge term := by
            intro edge member term produced
            obtain ⟨terms, forestMember, rfl⟩ := List.mem_map.mp produced
            have exact := (mem_forests_iff (Accepts automaton) children budget childExact
              edge.children budget (Nat.le_refl _) terms).mp forestMember
            exact ⟨terms, rfl, exact.1, plain state edge member _⟩
          have unique : ∀ edge ∈ automaton state, (outputs edge).Nodup := by
            intro edge member
            apply List.pairwise_map.mpr
            have forestUnique := (forests_unique children edge.children budget (by
              intro child childMember childSize smaller
              simp only [children, dite_eq_left smaller]
              exact ⟨ih childSize (by omega) child (closed state inside edge member child childMember),
                fun term termMember => ((mem_enumerate_iff automaton plain childSize child term).mp termMember).2⟩)
              budget (Nat.le_refl _)).1
            apply forestUnique.imp
            intro first second different same
            exact different (Term.node.inj same).2
          rw [RecursiveSize.enumerate]
          change ((automaton state).flatMap outputs).Nodup
          apply List.pairwise_flatMap.mpr
          refine ⟨unique, ?_⟩
          apply (separate state inside).imp_of_mem
          intro first second firstMember secondMember disjoint a aMember b bMember same
          subst b
          exact disjoint a (sound first firstMember a aMember) (sound second secondMember a bMember)

/-- The source gate at each row discharges SizedRank.Unambiguous for cyclic graphs. -/
theorem unambiguous [DecidableEq Symbol] (automaton : Automaton State Symbol)
    (plain : Decoder.Plain automaton) (test : State → State → Bool)
    (covers : ∀ first second term, Accepts automaton first term → Accepts automaton second term → test first second = true)
    (gate : ∀ state, AutomatonAmbiguity.ambiguous test (automaton state) = false) :
    SizedRank.Unambiguous automaton := by
  intro state size
  exact enumerate_nodup automaton plain (fun _ => True) (by simp)
    (fun state _ => AutomatonAmbiguity.compact_disjoint _ test covers _ (gate state)) size state trivial

/-- Computed minimum-size intersection tests supply the complete source gate interface. -/
theorem minimum_gate_unambiguous [DecidableEq State] [DecidableEq Symbol]
    (automaton : Automaton State Symbol) (plain : Decoder.Plain automaton)
    (pairs : List (State × State)) (complete : ∀ pair, pair ∈ pairs)
    (gate : ∀ state, AutomatonAmbiguity.ambiguous (fun left right =>
      AutomatonAmbiguity.productiveRows (Language.intersect automaton automaton) pairs complete (left, right))
        (automaton state) = false) : SizedRank.Unambiguous automaton :=
  unambiguous automaton plain _ (AutomatonAmbiguity.table_test_covers automaton pairs complete) gate

/-- Checking only reachable rows is sufficient for every descendant's exact size class. -/
theorem reachable_enumerate_nodup [DecidableEq Symbol] (automaton : Automaton State Symbol)
    (plain : Decoder.Plain automaton) (test : State → State → Bool)
    (covers : ∀ first second term, Accepts automaton first term → Accepts automaton second term → test first second = true)
    (root : State)
    (gate : ∀ state, Productivity.Reachable (Productivity.successors automaton) [root] state →
      AutomatonAmbiguity.ambiguous test (automaton state) = false)
    (state : State) (reached : Productivity.Reachable (Productivity.successors automaton) [root] state) (size : Nat) :
    (RecursiveSize.enumerate automaton size state).Nodup :=
  enumerate_nodup automaton plain (Productivity.Reachable (Productivity.successors automaton) [root])
    (fun _ reached _ member _ child => Productivity.reachable_child automaton [root] reached member child)
    (fun state reached => AutomatonAmbiguity.compact_disjoint _ test covers _ (gate state reached)) size state reached

/-- Unique exact-size classes are also disjoint across different node counts. -/
theorem bounded_nodup (automaton : Automaton State Symbol) (plain : Decoder.Plain automaton)
    (state : State) (bound : Nat)
    (unique : ∀ size, size ≤ bound → (RecursiveSize.enumerate automaton size state).Nodup) :
    (enumerateAtMost automaton bound state).Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro size member
    exact unique size (by have := List.mem_range.mp member; omega)
  · apply (List.nodup_range (n := bound + 1)).imp
    intro first second different left leftMember right rightMember same
    subst right
    have firstSize := ((mem_enumerate_iff automaton plain first state left).mp leftMember).2
    have secondSize := ((mem_enumerate_iff automaton plain second state left).mp rightMember).2
    exact different (firstSize.symm.trans secondSize)

/-- An actual decoder result records the exact class and its valid rank. -/
theorem replay_valid (automaton : Automaton State Symbol) (plain : Decoder.Plain automaton)
    (state : State) (position : Position) (term : Term Symbol)
    (selected : replayPosition automaton state position = some term) :
    position.size = nodeSize term ∧ position.rank < countAt automaton position.size state := by
  rw [replayPosition, decode_compileAt] at selected
  have exact := (mem_enumerate_iff automaton plain position.size state term).mp (List.mem_of_getElem? selected)
  exact ⟨exact.2.symm, by rw [countAt_correct]; exact (List.getElem?_eq_some_iff.mp selected).1⟩

/-- Every exact size class uses the full and only valid source count interval. -/
theorem replay_total (automaton : Automaton State Symbol) (state : State) (size rank : Nat) :
    (∃ term, replayPosition automaton state ⟨size, rank⟩ = some term) ↔ rank < countAt automaton size state := by
  rw [replayPosition, decode_compileAt, countAt_correct]
  constructor
  · rintro ⟨term, selected⟩
    exact (List.getElem?_eq_some_iff.mp selected).1
  · intro within
    exact ⟨_, List.getElem?_eq_getElem within⟩

/-- The actual bottom-up inverse rejects precisely nonmembers, across every finite size. -/
theorem positionsOf_reject [DecidableEq Symbol] (automaton : Automaton State Symbol)
    (plain : Decoder.Plain automaton) (state : State) (term : Term Symbol) :
    TablePosition.positionsOf automaton term state = none ↔ ¬Accepts automaton state term := by
  constructor
  · intro rejected accepted
    obtain ⟨position, found⟩ := TablePosition.positionsOf_complete automaton term state accepted
    rw [rejected] at found
    cases found
  · intro absent
    cases found : TablePosition.positionsOf automaton term state with
    | none => rfl
    | some position => exact False.elim (absent ((TablePosition.positionsOf_correct automaton plain term state).mp ⟨position, found⟩))

/-- Root-local class uniqueness gives the bottom-up inverse, without a global scope premise. -/
theorem positionsOf_inverse [DecidableEq Symbol] (automaton : Automaton State Symbol)
    (plain : Decoder.Plain automaton) (state : State)
    (unique : ∀ size, (RecursiveSize.enumerate automaton size state).Nodup)
    (position : Position) (term : Term Symbol) :
    TablePosition.positionsOf automaton term state = some position ↔ replayPosition automaton state position = some term := by
  constructor
  · exact TablePosition.positionsOf_replay automaton term state position
  · intro selected
    have selectedAt := selected
    rw [replayPosition, decode_compileAt] at selectedAt
    have accepted := ((mem_enumerate_iff automaton plain position.size state term).mp (List.mem_of_getElem? selectedAt)).1
    obtain ⟨found, ranked⟩ := TablePosition.positionsOf_complete automaton term state accepted
    have replayed := TablePosition.positionsOf_replay automaton term state found ranked
    have sameSize : found.size = position.size :=
      (replay_valid automaton plain state found term replayed).1.trans (replay_valid automaton plain state position term selected).1.symm
    rw [replayPosition, decode_compileAt, sameSize] at replayed
    have sameRank := (unique position.size).eq_of_getElem?_eq
      (List.getElem?_eq_some_iff.mp replayed).1 (replayed.trans selectedAt.symm)
    have same : found = position := by cases found; cases position; simp_all
    simpa only [same] using ranked

/-- Exact source class counts are the counts of distinct accepted terms. -/
def classIndex (automaton : Automaton State Symbol) (plain : Decoder.Plain automaton)
    (state : State) (size : Nat) (unique : (RecursiveSize.enumerate automaton size state).Nodup) :
    DistinctRank.Index (fun term => Accepts automaton state term ∧ nodeSize term = size) where
  members := RecursiveSize.enumerate automaton size state
  nodup := unique
  exact := mem_enumerate_iff automaton plain size state

/-- The distinct class cardinality is the actual source convolution count. -/
theorem classIndex_count (automaton : Automaton State Symbol) (plain : Decoder.Plain automaton)
    (state : State) (size : Nat) (unique : (RecursiveSize.enumerate automaton size state).Nodup) :
    (classIndex automaton plain state size unique).count = countAt automaton size state :=
  (countAt_correct automaton size state).symm

/-- Decode each bounded size class through the actual counted mixed-radix plan. -/
def selectAtMost (automaton : Automaton State Symbol) (state : State) (bound rank : Nat) : Option (Term Symbol) :=
  Decoder.decode (Decoder.normalize (compileAtMost automaton bound state)) rank

/-- The bounded inverse uses bottom-up positions and arithmetic class offsets. -/
def rankAtMost [DecidableEq Symbol] (automaton : Automaton State Symbol) (state : State) (bound : Nat)
    (term : Term Symbol) : Option Nat := do
  let position ← TablePosition.positionsOf automaton term state
  if position.size ≤ bound then some (classOffset automaton position.size state + position.rank) else none

/-- The actual bounded selector has exactly the contiguous source count interval. -/
theorem selectAtMost_total (automaton : Automaton State Symbol) (state : State) (bound rank : Nat) :
    (∃ term, selectAtMost automaton state bound rank = some term) ↔ rank < countAtMost automaton bound state := by
  rw [selectAtMost, decode_compileAtMost, countAtMost_correct]
  constructor
  · rintro ⟨term, selected⟩
    exact (List.getElem?_eq_some_iff.mp selected).1
  · intro within
    exact ⟨_, List.getElem?_eq_getElem within⟩

/-- Bounded decoding has exactly the bounded accepted language. -/
theorem selectAtMost_language (automaton : Automaton State Symbol) (plain : Decoder.Plain automaton)
    (state : State) (bound : Nat) (term : Term Symbol) :
    (∃ rank, selectAtMost automaton state bound rank = some term) ↔
      Accepts automaton state term ∧ nodeSize term ≤ bound := by
  simp only [selectAtMost, decode_compileAtMost]
  rw [← mem_enumerateAtMost_iff automaton plain bound state]
  constructor
  · rintro ⟨rank, found⟩; exact List.mem_of_getElem? found
  · intro member
    obtain ⟨rank, within, found⟩ := List.mem_iff_getElem.mp member
    exact ⟨rank, by simpa only [List.getElem?_eq_getElem within] using congrArg some found⟩

/-- Bottom-up bounded ranking and the counted decoder are mutual inverses. -/
theorem rankAtMost_inverse [DecidableEq Symbol] (automaton : Automaton State Symbol)
    (plain : Decoder.Plain automaton) (state : State) (bound : Nat)
    (unique : ∀ size, size ≤ bound → (RecursiveSize.enumerate automaton size state).Nodup)
    (rank : Nat) (term : Term Symbol) :
    rankAtMost automaton state bound term = some rank ↔ selectAtMost automaton state bound rank = some term := by
  constructor
  · intro ranked
    obtain ⟨position, computed, rankFound⟩ := Option.bind_eq_some_iff.mp ranked
    split at rankFound
    · rename_i within
      have same : classOffset automaton position.size state + position.rank = rank := Option.some.inj rankFound
      subst rank
      exact TablePosition.positionsOf_sizeMajor_replay automaton plain term state position bound computed within
    · cases rankFound
  · intro selected
    obtain ⟨accepted, fits⟩ := (selectAtMost_language automaton plain state bound term).mp ⟨rank, selected⟩
    obtain ⟨position, computed⟩ := TablePosition.positionsOf_complete automaton term state accepted
    have actual := (TablePosition.positionsOf_valid automaton plain term state position computed).1
    have within : position.size ≤ bound := by omega
    have replayed := TablePosition.positionsOf_sizeMajor_replay automaton plain term state position bound computed within
    have original := selected
    rw [selectAtMost, decode_compileAtMost] at original
    rw [decode_compileAtMost] at replayed
    have same := (bounded_nodup automaton plain state bound unique).eq_of_getElem?_eq
      (List.getElem?_eq_some_iff.mp replayed).1 (replayed.trans original.symm)
    simp [rankAtMost, computed, within, same]

/-- A rejected inverse is exactly a term outside the bounded language. -/
theorem rankAtMost_reject [DecidableEq Symbol] (automaton : Automaton State Symbol)
    (plain : Decoder.Plain automaton) (state : State) (bound : Nat)
    (unique : ∀ size, size ≤ bound → (RecursiveSize.enumerate automaton size state).Nodup) (term : Term Symbol) :
    rankAtMost automaton state bound term = none ↔ ¬(Accepts automaton state term ∧ nodeSize term ≤ bound) := by
  constructor
  · intro rejected accepted
    obtain ⟨rank, selected⟩ := (selectAtMost_language automaton plain state bound term).mpr accepted
    have found := (rankAtMost_inverse automaton plain state bound unique rank term).mpr selected
    rw [rejected] at found
    cases found
  · intro absent
    cases found : rankAtMost automaton state bound term with
    | none => rfl
    | some rank =>
        exact False.elim (absent ((selectAtMost_language automaton plain state bound term).mp
          ⟨rank, (rankAtMost_inverse automaton plain state bound unique rank term).mp found⟩))

/-- The same-pass inverse proves that distinct bounded ranks select distinct terms. -/
theorem selectAtMost_injective [DecidableEq Symbol] (automaton : Automaton State Symbol)
    (plain : Decoder.Plain automaton) (state : State) (bound : Nat)
    (unique : ∀ size, size ≤ bound → (RecursiveSize.enumerate automaton size state).Nodup)
    (first second : Nat) (term : Term Symbol)
    (a : selectAtMost automaton state bound first = some term)
    (b : selectAtMost automaton state bound second = some term) : first = second :=
  Option.some.inj (((rankAtMost_inverse automaton plain state bound unique first term).mpr a).symm.trans
    ((rankAtMost_inverse automaton plain state bound unique second term).mpr b))

/-- The finite bounded language has a distinct reference index in the source decoder order. -/
def boundedIndex (automaton : Automaton State Symbol) (plain : Decoder.Plain automaton)
    (state : State) (bound : Nat)
    (unique : ∀ size, size ≤ bound → (RecursiveSize.enumerate automaton size state).Nodup) :
    DistinctRank.Index (fun term => Accepts automaton state term ∧ nodeSize term ≤ bound) where
  members := enumerateAtMost automaton bound state
  nodup := bounded_nodup automaton plain state bound unique
  exact := mem_enumerateAtMost_iff automaton plain bound state

/-- The distinct bounded index count is exactly the source sum of class counts. -/
theorem boundedIndex_count (automaton : Automaton State Symbol) (plain : Decoder.Plain automaton)
    (state : State) (bound : Nat)
    (unique : ∀ size, size ≤ bound → (RecursiveSize.enumerate automaton size state).Nodup) :
    (boundedIndex automaton plain state bound unique).count = countAtMost automaton bound state :=
  (countAtMost_correct automaton bound state).symm

/-- The actual minimum-size gate gives both public inverse laws and distinct bounded indexes. -/
theorem minimum_gate_api [DecidableEq State] [DecidableEq Symbol]
    (automaton : Automaton State Symbol) (plain : Decoder.Plain automaton)
    (pairs : List (State × State)) (complete : ∀ pair, pair ∈ pairs)
    (gate : ∀ state, AutomatonAmbiguity.ambiguous (fun left right =>
      AutomatonAmbiguity.productiveRows (Language.intersect automaton automaton) pairs complete (left, right))
        (automaton state) = false) :
    (∀ state position term, TablePosition.positionsOf automaton term state = some position ↔
      replayPosition automaton state position = some term) ∧
    (∀ state bound rank, (∃ term, selectAtMost automaton state bound rank = some term) ↔
      rank < countAtMost automaton bound state) ∧
    (∀ state bound rank term, rankAtMost automaton state bound term = some rank ↔
      selectAtMost automaton state bound rank = some term) ∧
    (∀ state bound term, rankAtMost automaton state bound term = none ↔
      ¬(Accepts automaton state term ∧ nodeSize term ≤ bound)) := by
  have unique := minimum_gate_unambiguous automaton plain pairs complete gate
  exact ⟨fun state => positionsOf_inverse automaton plain state (unique state),
    selectAtMost_total automaton,
    fun state bound => rankAtMost_inverse automaton plain state bound (fun size _ => unique state size),
    fun state bound => rankAtMost_reject automaton plain state bound (fun size _ => unique state size)⟩

/-- A recursive binary grammar exercises several nonempty forest size splits. -/
def binaryGrammar : Automaton Unit Nat := fun _ =>
  [⟨0, [], fun _ => true⟩, ⟨1, [(), ()], fun _ => true⟩]

def leaf : Term Nat := .node 0 []
def branch (left right : Term Nat) : Term Nat := .node 1 [left, right]

example : countAt binaryGrammar 7 () = 5 := by cbv
example : countAtMost binaryGrammar 5 () = 4 := by cbv
example : rankAtMost binaryGrammar () 5 (branch leaf (branch leaf leaf)) = some 2 := by cbv
example : rankAtMost binaryGrammar () 5 (branch (branch leaf leaf) leaf) = some 3 := by cbv
example : rankAtMost binaryGrammar () 4 (branch (branch leaf leaf) leaf) = none := by cbv
example : rankAtMost binaryGrammar () 8 (.node 1 [leaf]) = none := by cbv

/-- The local gate proves every class of the infinite binary language distinct. -/
theorem binary_unambiguous : SizedRank.Unambiguous binaryGrammar := by
  apply unambiguous binaryGrammar (by intro state edge member term; simp [binaryGrammar] at member; rcases member with rfl | rfl <;> rfl)
    (fun _ _ => true) (by simp)
  intro state
  cbv

/-- Repeated unproductive recursive alternatives still have no repeated finite term. -/
def emptyCycle : Automaton Unit Nat := fun _ =>
  [⟨1, [()], fun _ => true⟩, ⟨1, [()], fun _ => true⟩]

theorem unitPairs_complete (pair : Unit × Unit) : pair ∈ [((), ())] := by
  rcases pair with ⟨⟨⟩, ⟨⟩⟩
  simp

example : countAt emptyCycle 7 () = 0 := by cbv
example : AutomatonAmbiguity.ambiguous (fun left right =>
    AutomatonAmbiguity.productiveRows (Language.intersect emptyCycle emptyCycle)
      [((), ())] unitPairs_complete (left, right)) (emptyCycle ()) = false := by cbv

end MicroCFTA.RecursiveUnambiguous
