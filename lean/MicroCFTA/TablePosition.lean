import MicroCFTA.SizedRank

/-!
# Bottom-up term positions

The worker computes one state-position table for each child term. It looks up
child states in those tables, combines the positions from left to right, and
adds the counts of preceding transitions. A later successful transition
replaces an earlier one, as in `Map.fromList`.

The finite function tables model map lookup and overwrite. Concrete map
storage and candidate dispatch by symbol and arity are separate refinements.
-/

namespace MicroCFTA.TablePosition

open Language RecursiveSize SizedRank

/-- Reserve one node for the transition root. -/
def rooted (values : Nat → List α) : Nat → List α
  | 0 => []
  | size + 1 => values size

/-- Rooted child prefixes use the same left-to-right product order. -/
def rootForests (children : Nat → State → List (Term Symbol)) (states : List State) :
    Nat → List (List (Term Symbol)) :=
  states.foldl (fun prefixes state => extendForests prefixes (fun size => children size state))
    (rooted emptyForests)

/-- Adding children commutes with reserving a root node. -/
theorem extendForests_rooted (prefixes : Nat → List (List (Term Symbol)))
    (children : Nat → List (Term Symbol)) :
    extendForests (rooted prefixes) children = rooted (extendForests prefixes children) := by
  funext size
  cases size with
  | zero => simp [extendForests, rooted]
  | succ size =>
      simp only [extendForests, List.range_succ_eq_map, List.flatMap_cons, rooted,
        List.flatMap_nil, List.nil_append, List.flatMap_map, Nat.succ_sub_succ_eq_sub]

/-- Each rooted prefix is the ordinary child forest with its size shifted by one. -/
theorem rootForests_eq (children : Nat → State → List (Term Symbol)) (states : List State) :
    rootForests children states = rooted (forests children states) := by
  induction states using snoc_induction with
  | empty => rfl
  | step states state ih =>
      simp only [rootForests, List.foldl_append, List.foldl_cons, List.foldl_nil] at ⊢ ih
      rw [ih, forests_snoc, extendForests_rooted]

/-- An appended child adds one product to a rooted prefix. -/
theorem rootForests_snoc (children : Nat → State → List (Term Symbol))
    (states : List State) (state : State) :
    rootForests children (states ++ [state]) =
      extendForests (rootForests children states) (fun size => children size state) := by
  simp [rootForests, List.foldl_append]

/-- Equal branch lists give equal ordered concatenations. -/
theorem flatMap_congr (items : List α) (left right : α → List β)
    (same : ∀ item, item ∈ items → left item = right item) :
    items.flatMap left = items.flatMap right := by
  rw [List.flatMap_def, List.flatMap_def]
  exact congrArg List.flatten (List.map_congr_left same)

/-- Product enumeration reads only input sizes at most its result size. -/
theorem extendForests_congr (left right : Nat → List (List (Term Symbol)))
    (children children' : Nat → List (Term Symbol)) (bound : Nat)
    (sameLeft : ∀ size, size ≤ bound → left size = right size)
    (sameChildren : ∀ size, size ≤ bound → children size = children' size)
    (size : Nat) (within : size ≤ bound) :
    extendForests left children size = extendForests right children' size := by
  apply flatMap_congr
  intro prefixSize member
  have fits := List.mem_range.mp member
  rw [sameLeft prefixSize (by omega), sameChildren (size - prefixSize) (by omega)]

/-- Every child-prefix enumeration reads only child sizes within its own bound. -/
theorem forests_congr (left right : Nat → State → List (Term Symbol)) (bound : Nat)
    (same : ∀ size, size ≤ bound → ∀ state, left size state = right size state)
    (states : List State) (size : Nat) (within : size ≤ bound) :
    forests left states size = forests right states size := by
  induction states using snoc_induction generalizing size with
  | empty => rfl
  | step states state ih =>
      rw [forests_snoc, forests_snoc]
      exact extendForests_congr _ _ _ _ bound ih (fun size h => same size h state) size within

/-- Exact-size enumeration satisfies the ordinary uncapped transition recurrence. -/
theorem enumerate_rootForests (automaton : Automaton State Symbol) (size : Nat) (state : State) :
    RecursiveSize.enumerate automaton size state =
      (automaton state).flatMap fun edge =>
        (rootForests (RecursiveSize.enumerate automaton) edge.children size).map (Term.node edge.label) := by
  cases size with
  | zero =>
      rw [enumerate_zero]
      simp [rootForests_eq, rooted]
  | succ size =>
      rw [RecursiveSize.enumerate]
      apply flatMap_congr
      intro edge _
      rw [rootForests_eq]
      change _ = (forests (RecursiveSize.enumerate automaton) edge.children size).map _
      congr 1
      exact forests_congr _ _ size (fun childSize smaller child => by simp [smaller])
        edge.children size (Nat.le_refl _)

/-- Count a child prefix together with its root node. -/
def prefixCount (counts : Nat → State → Nat) (states : List State) : Nat → Nat
  | 0 => 0
  | size + 1 => forestCounts counts states size

/-- Rooted-prefix counts are the lengths of their ordered run lists. -/
theorem length_rootForests (children : Nat → State → List (Term Symbol))
    (states : List State) (size : Nat) :
    (rootForests children states size).length =
      prefixCount (fun size state => (children size state).length) states size := by
  rw [rootForests_eq]
  cases size with
  | zero => rfl
  | succ size => exact length_forests children states size

/-- Look up one child state in each already-computed child table. -/
def lookupChildren : List State → List (State → Option Position) → Option (List Position)
  | [], [] => some []
  | state :: states, table :: tables => do
      let position ← table state
      let rest ← lookupChildren states tables
      pure (position :: rest)
  | _, _ => none

/-- Combine child positions with the rooted prefix counts used by `stateTable`. -/
def positionChildren (counts : Nat → State → Nat) :
    List State → Position → List State → List Position → Option Position
  | _, built, [], [] => some built
  | before, built, state :: states, position :: positions =>
      positionChildren counts (before ++ [state])
        (productPosition (prefixCount counts before) (fun size => counts size state) built position)
        states positions
  | _, _, _, _ => none

/-- Child states, terms, and positions have the same order and exact replay relation. -/
inductive Positioned (children : Nat → State → List (Term Symbol)) :
    List State → List (Term Symbol) → List Position → Prop where
  | nil : Positioned children [] [] []
  | cons : (children position.size state)[position.rank]? = some term →
      Positioned children states terms positions →
      Positioned children (state :: states) (term :: terms) (position :: positions)

/-- One product step replays an extended child forest at its computed position. -/
theorem extend_position_replay (children : Nat → State → List (Term Symbol))
    (counts : Nat → State → Nat) (exactCounts : ∀ size state, counts size state = (children size state).length)
    (before : List State) (state : State) (built child : Position) (terms : List (Term Symbol))
    (term : Term Symbol)
    (builtReplay : (rootForests children before built.size)[built.rank]? = some terms)
    (childReplay : (children child.size state)[child.rank]? = some term) :
    let next := productPosition (prefixCount counts before) (fun size => counts size state) built child
    (rootForests children (before ++ [state]) next.size)[next.rank]? = some (terms ++ [term]) := by
  have countSame : counts = fun size state => (children size state).length := by
    funext size state
    exact exactCounts size state
  subst counts
  have builtValid := (List.getElem?_eq_some_iff.mp builtReplay).1
  have childValid := (List.getElem?_eq_some_iff.mp childReplay).1
  have replay := productPosition_replay
    (fun size => (rootForests children before size).map (fun built child => built ++ [child]))
    (fun size => children size state) built child (by simpa using builtValid) childValid
  simp only [List.length_map, length_rootForests] at replay
  dsimp only
  rw [rootForests_snoc, productPosition_size]
  change _ = _ at replay
  have sameProduct (size : Nat) :
      Decoder.applyValues ((rootForests children before size).map
        (fun built child => built ++ [child])) (children (built.size + child.size - size) state) =
      (rootForests children before size).flatMap (fun prefixTerms =>
        (children (built.size + child.size - size) state).map (fun childTerm => prefixTerms ++ [childTerm])) := by
    simp only [Decoder.applyValues, List.flatMap_map]
  simp only [sameProduct] at replay
  unfold extendForests
  rw [replay]
  simp only [List.getElem?_map, builtReplay, childReplay, Option.map_some, Option.bind_some]

/-- The left fold returns a valid position for the complete ordered child forest. -/
theorem positionChildren_replay (children : Nat → State → List (Term Symbol))
    (counts : Nat → State → Nat) (exactCounts : ∀ size state, counts size state = (children size state).length)
    (states : List State) (terms : List (Term Symbol)) (positions : List Position)
    (positioned : Positioned children states terms positions)
    (before : List State) (built : Position) (earlier : List (Term Symbol))
    (builtReplay : (rootForests children before built.size)[built.rank]? = some earlier) :
    ∃ result, positionChildren counts before built states positions = some result ∧
      (rootForests children (before ++ states) result.size)[result.rank]? = some (earlier ++ terms) := by
  induction positioned generalizing before built earlier with
  | nil => exact ⟨built, rfl, by simpa using builtReplay⟩
  | @cons state term states terms positions position childReplay rest ih =>
      let next := productPosition (prefixCount counts before) (fun size => counts size state) built position
      have nextReplay := extend_position_replay children counts exactCounts before state built position
        earlier term builtReplay childReplay
      obtain ⟨result, computed, replay⟩ := ih (before ++ [state]) next (earlier ++ [term]) nextReplay
      refine ⟨result, computed, ?_⟩
      simpa only [List.append_assoc, List.singleton_append] using replay

/-- Correct child tables return only positions that replay their child term. -/
def TablesSound (automaton : Automaton State Symbol) (tables : List (State → Option Position))
    (terms : List (Term Symbol)) : Prop :=
  All₂ (fun table term => ∀ state position, table state = some position →
    replayPosition automaton state position = some term) tables terms

/-- Ordered child lookup preserves the child tables' replay invariant. -/
theorem lookupChildren_sound (automaton : Automaton State Symbol)
    (tables : List (State → Option Position)) (terms : List (Term Symbol))
    (sound : TablesSound automaton tables terms) (states : List State) (positions : List Position)
    (found : lookupChildren states tables = some positions) :
    Positioned (RecursiveSize.enumerate automaton) states terms positions := by
  induction sound generalizing states positions with
  | nil =>
      cases states with
      | nil => have same : [] = positions := by simpa [lookupChildren] using found
               subst positions; exact .nil
      | cons state states => cases found
  | @cons table term tables terms correct rest ih =>
      cases states with
      | nil => cases found
      | cons state states =>
          cases head : table state with
          | none => simp [lookupChildren, head] at found
          | some position =>
              cases tail : lookupChildren states tables with
              | none => simp [lookupChildren, head, tail] at found
              | some positions' =>
                  have same : position :: positions' = positions := by
                    simpa [lookupChildren, head, tail] using found
                  subst positions
                  have replay := correct state position head
                  rw [replayPosition, decode_compileAt] at replay
                  exact .cons replay (ih states positions' tail)

/-- Correct child tables contain a position for every accepted child state. -/
def TablesComplete (automaton : Automaton State Symbol) (tables : List (State → Option Position))
    (terms : List (Term Symbol)) : Prop :=
  All₂ (fun table term => ∀ state, Accepts automaton state term →
    ∃ position, table state = some position) tables terms

/-- Accepted children all have successful lookups in complete child tables. -/
theorem lookupChildren_complete (automaton : Automaton State Symbol)
    (tables : List (State → Option Position)) (terms : List (Term Symbol))
    (complete : TablesComplete automaton tables terms) (states : List State)
    (accepted : All₂ (Accepts automaton) states terms) :
    ∃ positions, lookupChildren states tables = some positions := by
  induction complete generalizing states with
  | nil => cases accepted; exact ⟨[], rfl⟩
  | cons head rest ih =>
      cases accepted with
      | cons accepted acceptedRest =>
          obtain ⟨position, found⟩ := head _ accepted
          obtain ⟨positions, foundRest⟩ := ih _ acceptedRest
          exact ⟨position :: positions, by simp [lookupChildren, found, foundRest]⟩

/-- The exact-size run list of one transition includes its root and all child products. -/
def edgeValues (automaton : Automaton State Symbol) (edge : Edge State Symbol) (size : Nat) :
    List (Term Symbol) :=
  (rootForests (RecursiveSize.enumerate automaton) edge.children size).map (Term.node edge.label)

/-- Count one transition by the shared child-size counts and the rooted prefix recurrence. -/
def edgeCount (automaton : Automaton State Symbol) (edge : Edge State Symbol) (size : Nat) : Nat :=
  prefixCount (countAt automaton) edge.children size

/-- Transition counts are derived from the exact ordered transition run list. -/
theorem edgeCount_correct (automaton : Automaton State Symbol) (edge : Edge State Symbol) (size : Nat) :
    edgeCount automaton edge size = (edgeValues automaton edge size).length := by
  have same : countAt automaton = fun size state => (RecursiveSize.enumerate automaton size state).length := by
    funext size state
    exact countAt_correct automaton size state
  simp only [edgeCount, edgeValues, List.length_map, length_rootForests, same]

/-- Compute one matching transition's position from the already-computed child tables. -/
def edgePosition [DecidableEq Symbol] (automaton : Automaton State Symbol) (symbol : Symbol)
    (tables : List (State → Option Position)) (edge : Edge State Symbol) : Option Position :=
  if edge.label = symbol then do
    let positions ← lookupChildren edge.children tables
    positionChildren (countAt automaton) [] ⟨1, 0⟩ edge.children positions
  else none

/-- Every successful transition position replays the given complete term. -/
theorem edgePosition_sound [DecidableEq Symbol] (automaton : Automaton State Symbol) (symbol : Symbol)
    (tables : List (State → Option Position)) (terms : List (Term Symbol))
    (sound : TablesSound automaton tables terms) (edge : Edge State Symbol) (position : Position)
    (found : edgePosition automaton symbol tables edge = some position) :
    (edgeValues automaton edge position.size)[position.rank]? = some (.node symbol terms) := by
  unfold edgePosition at found
  split at found
  next sameLabel =>
    cases lookedUp : lookupChildren edge.children tables with
    | none => simp [lookedUp] at found
    | some positions =>
        have computed : positionChildren (countAt automaton) [] ⟨1, 0⟩ edge.children positions = some position :=
          by simpa [lookedUp] using found
        have positioned := lookupChildren_sound automaton tables terms sound edge.children positions lookedUp
        obtain ⟨result, computed', replay⟩ := positionChildren_replay
          (RecursiveSize.enumerate automaton) (countAt automaton) (countAt_correct automaton)
          edge.children terms positions positioned [] ⟨1, 0⟩ [] (by simp [rootForests, rooted, emptyForests])
        have same : result = position := Option.some.inj (computed'.symm.trans computed)
        subst result
        simp only [List.nil_append] at replay
        simp only [edgeValues, List.getElem?_map, replay, Option.map_some, sameLabel]
  next different => cases found

/-- A matching transition with accepted children gets a position from complete child tables. -/
theorem edgePosition_complete [DecidableEq Symbol] (automaton : Automaton State Symbol) (symbol : Symbol)
    (tables : List (State → Option Position)) (terms : List (Term Symbol))
    (sound : TablesSound automaton tables terms) (complete : TablesComplete automaton tables terms)
    (edge : Edge State Symbol) (sameLabel : edge.label = symbol)
    (accepted : All₂ (Accepts automaton) edge.children terms) :
    ∃ position, edgePosition automaton symbol tables edge = some position := by
  obtain ⟨positions, found⟩ := lookupChildren_complete automaton tables terms complete edge.children accepted
  have positioned := lookupChildren_sound automaton tables terms sound edge.children positions found
  obtain ⟨position, computed, _⟩ := positionChildren_replay
    (RecursiveSize.enumerate automaton) (countAt automaton) (countAt_correct automaton)
    edge.children terms positions positioned [] ⟨1, 0⟩ [] (by simp [rootForests, rooted, emptyForests])
  exact ⟨position, by simp [edgePosition, sameLabel, found, computed]⟩

/-- Select the last successful transition and add all earlier same-size transition counts. -/
def rowPosition [DecidableEq Symbol] (automaton : Automaton State Symbol) (symbol : Symbol)
    (tables : List (State → Option Position)) : List (Edge State Symbol) → Option Position
  | [] => none
  | edge :: edges =>
      match rowPosition automaton symbol tables edges with
      | some position => some ⟨position.size, edgeCount automaton edge position.size + position.rank⟩
      | none => edgePosition automaton symbol tables edge

/-- The selected row position replays the term in transition order. -/
theorem rowPosition_sound [DecidableEq Symbol] (automaton : Automaton State Symbol) (symbol : Symbol)
    (tables : List (State → Option Position)) (terms : List (Term Symbol))
    (sound : TablesSound automaton tables terms) (edges : List (Edge State Symbol)) (position : Position)
    (found : rowPosition automaton symbol tables edges = some position) :
    (edges.flatMap (fun edge => edgeValues automaton edge position.size))[position.rank]? =
      some (.node symbol terms) := by
  induction edges generalizing position with
  | nil => cases found
  | cons edge edges ih =>
      cases tail : rowPosition automaton symbol tables edges with
      | none =>
          have first : edgePosition automaton symbol tables edge = some position := by
            simpa [rowPosition, tail] using found
          have replay := edgePosition_sound automaton symbol tables terms sound edge position first
          have valid := (List.getElem?_eq_some_iff.mp replay).1
          rw [List.flatMap_cons, List.getElem?_append_left valid]
          exact replay
      | some part =>
          have same : (⟨part.size, edgeCount automaton edge part.size + part.rank⟩ : Position) = position :=
            by simpa [rowPosition, tail] using found
          subst position
          have replay := ih part tail
          simp only [List.flatMap_cons, edgeCount_correct]
          rw [List.getElem?_append_right (by omega)]
          simpa only [Nat.add_sub_cancel_left] using replay

/-- Any successful transition makes its complete row succeed. -/
theorem rowPosition_complete [DecidableEq Symbol] (automaton : Automaton State Symbol) (symbol : Symbol)
    (tables : List (State → Option Position)) (edges : List (Edge State Symbol)) (edge : Edge State Symbol)
    (member : edge ∈ edges) (position : Position)
    (found : edgePosition automaton symbol tables edge = some position) :
    ∃ result, rowPosition automaton symbol tables edges = some result := by
  induction edges with
  | nil => simp at member
  | cons first edges ih =>
      cases tail : rowPosition automaton symbol tables edges with
      | some part => exact ⟨⟨part.size, edgeCount automaton first part.size + part.rank⟩, by simp [rowPosition, tail]⟩
      | none =>
          rcases List.mem_cons.mp member with same | member
          · subst edge
            exact ⟨position, by simp [rowPosition, tail, found]⟩
          · obtain ⟨result, computed⟩ := ih member
            rw [tail] at computed
            cases computed

/-- Compute child tables once and rank matching transitions in each state row. -/
def positionsOf [DecidableEq Symbol] (automaton : Automaton State Symbol) :
    Term Symbol → State → Option Position
  | .node symbol terms =>
      let childTables := terms.map (positionsOf automaton)
      fun state => rowPosition automaton symbol childTables (automaton state)

/-- Every bottom-up position decodes to the requested term. -/
theorem positionsOf_replay [DecidableEq Symbol] (automaton : Automaton State Symbol)
    (term : Term Symbol) (state : State) (position : Position)
    (found : positionsOf automaton term state = some position) :
    replayPosition automaton state position = some term := by
  induction term using Term.rec
    (motive_2 := fun terms => TablesSound automaton (terms.map (positionsOf automaton)) terms)
    generalizing state position with
  | node symbol terms ih =>
      rw [positionsOf] at found
      have replay := rowPosition_sound automaton symbol (terms.map (positionsOf automaton)) terms ih
        (automaton state) position found
      rw [replayPosition, decode_compileAt, enumerate_rootForests]
      exact replay
  | nil => exact .nil
  | cons term terms ih ihs => exact .cons ih ihs

/-- Computing a child table preserves the ordered child replay invariant. -/
theorem childTables_sound [DecidableEq Symbol] (automaton : Automaton State Symbol)
    (terms : List (Term Symbol)) :
    TablesSound automaton (terms.map (positionsOf automaton)) terms := by
  induction terms with
  | nil => exact .nil
  | cons term terms ih => exact .cons (positionsOf_replay automaton term) ih

/-- Accepted terms always receive a bottom-up position. -/
theorem positionsOf_complete [DecidableEq Symbol] (automaton : Automaton State Symbol)
    (term : Term Symbol) (state : State) (accepted : Accepts automaton state term) :
    ∃ position, positionsOf automaton term state = some position := by
  induction term using Term.rec
    (motive_2 := fun terms => TablesComplete automaton (terms.map (positionsOf automaton)) terms)
    generalizing state with
  | node symbol terms ih =>
      obtain ⟨edge, member, label, children, _⟩ := (accepts_node_iff automaton state symbol terms).mp accepted
      have sound := childTables_sound automaton terms
      obtain ⟨position, found⟩ := edgePosition_complete automaton symbol
        (terms.map (positionsOf automaton)) terms sound ih edge label children
      rw [positionsOf]
      exact rowPosition_complete automaton symbol (terms.map (positionsOf automaton))
        (automaton state) edge member position found
  | nil => exact .nil
  | cons term terms ih ihs => exact .cons ih ihs

/-- Bottom-up rank lookup succeeds exactly for accepted terms of plain automata. -/
theorem positionsOf_correct [DecidableEq Symbol] (automaton : Automaton State Symbol)
    (plain : Decoder.Plain automaton) (term : Term Symbol) (state : State) :
    (∃ position, positionsOf automaton term state = some position) ↔ Accepts automaton state term := by
  constructor
  · rintro ⟨position, found⟩
    have replay := positionsOf_replay automaton term state position found
    rw [replayPosition, decode_compileAt] at replay
    exact ((RecursiveSize.mem_enumerate_iff automaton plain position.size state term).mp
      (List.mem_of_getElem? replay)).1
  · exact positionsOf_complete automaton term state

/-- Under unambiguity, the bottom-up worker equals the independent reference rank search. -/
theorem positionsOf_eq_termPosition [DecidableEq Symbol] (automaton : Automaton State Symbol)
    (plain : Decoder.Plain automaton) (unambiguous : Unambiguous automaton)
    (term : Term Symbol) (state : State) :
    positionsOf automaton term state = termPosition automaton state term := by
  cases computed : positionsOf automaton term state with
  | some position =>
      exact (termPosition_of_replay automaton plain unambiguous state position term
        (positionsOf_replay automaton term state position computed)).symm
  | none =>
      cases reference : termPosition automaton state term with
      | none => rfl
      | some position =>
          have accepted := (termPosition_exists_iff automaton plain state term).mp ⟨position, reference⟩
          obtain ⟨result, found⟩ := positionsOf_complete automaton term state accepted
          rw [computed] at found
          cases found

/-- For unambiguous rows, decoding and bottom-up ranking are mutual inverses. -/
theorem positionsOf_of_replay [DecidableEq Symbol] (automaton : Automaton State Symbol)
    (plain : Decoder.Plain automaton) (unambiguous : Unambiguous automaton)
    (term : Term Symbol) (state : State) (position : Position)
    (replayed : replayPosition automaton state position = some term) :
    positionsOf automaton term state = some position := by
  rw [positionsOf_eq_termPosition automaton plain unambiguous]
  exact termPosition_of_replay automaton plain unambiguous state position term replayed

/-- Successful child lookup requires exactly one table per child state. -/
theorem lookupChildren_length (states : List State) (tables : List (State → Option Position))
    (positions : List Position) (found : lookupChildren states tables = some positions) :
    states.length = tables.length := by
  induction states generalizing tables positions with
  | nil => cases tables with
      | nil => rfl
      | cons table tables => cases found
  | cons state states ih =>
      cases tables with
      | nil => cases found
      | cons table tables =>
          cases head : table state with
          | none => simp [lookupChildren, head] at found
          | some position =>
              cases tail : lookupChildren states tables with
              | none => simp [lookupChildren, head, tail] at found
              | some rest => simpa using ih tables rest tail

/-- The symbol-and-arity candidate filter removes only transitions that cannot return a position. -/
theorem edgePosition_filtered [DecidableEq Symbol] (automaton : Automaton State Symbol)
    (symbol : Symbol) (tables : List (State → Option Position)) (edge : Edge State Symbol)
    (mismatch : edge.label ≠ symbol ∨ edge.children.length ≠ tables.length) :
    edgePosition automaton symbol tables edge = none := by
  rcases mismatch with symbolMismatch | arityMismatch
  · simp [edgePosition, symbolMismatch]
  · have missing : lookupChildren edge.children tables = none := by
      cases found : lookupChildren edge.children tables with
      | none => rfl
      | some positions => exact False.elim (arityMismatch (lookupChildren_length _ _ positions found))
    simp [edgePosition, missing]

/-- List all successful transition candidates in their original branch order. -/
def rowCandidates [DecidableEq Symbol] (automaton : Automaton State Symbol) (symbol : Symbol)
    (tables : List (State → Option Position)) : List (Edge State Symbol) → List Position
  | [] => []
  | edge :: edges =>
      (edgePosition automaton symbol tables edge).toList ++
        (rowCandidates automaton symbol tables edges).map (fun position =>
          ⟨position.size, edgeCount automaton edge position.size + position.rank⟩)

/-- Add the size-class counts of an ordered prefix of transition branches. -/
def offsetRows (automaton : Automaton State Symbol) (before : List (Edge State Symbol))
    (position : Position) : Position :=
  ⟨position.size, (before.map (fun edge => edgeCount automaton edge position.size)).sum + position.rank⟩

/-- Splitting the candidate list preserves every preceding transition's rank offset. -/
theorem rowCandidates_append [DecidableEq Symbol] (automaton : Automaton State Symbol) (symbol : Symbol)
    (tables : List (State → Option Position)) (before after : List (Edge State Symbol)) :
    rowCandidates automaton symbol tables (before ++ after) =
      rowCandidates automaton symbol tables before ++
        (rowCandidates automaton symbol tables after).map (offsetRows automaton before) := by
  induction before with
  | nil =>
      have same : offsetRows automaton [] = id := by funext position; cases position; simp [offsetRows]
      simp [rowCandidates, same]
  | cons edge before ih =>
      simp only [List.cons_append, rowCandidates, ih, List.map_append, List.append_assoc,
        List.map_map, Function.comp_def, offsetRows]
      congr 2
      apply List.map_congr_left
      intro position _
      simp [offsetRows, Nat.add_assoc]

/-- A branch after a transition prefix uses exactly `choicePosition`'s offset. -/
theorem offsetRows_choicePosition (automaton : Automaton State Symbol)
    (before after : List (Edge State Symbol)) (position : Position) :
    (offsetRows automaton before position).rank =
      choicePosition ((before ++ after).map (fun edge => edgeCount automaton edge position.size))
        before.length position.rank := by
  simp [offsetRows, choicePosition]

/-- Repeated insertion at one map key retains the last candidate. -/
def lastWrite (positions : List Position) : Option Position :=
  positions.foldl (fun _ position => some position) none

/-- The map-overwrite fold returns exactly the last listed value. -/
theorem lastWrite_correct (positions : List Position) : lastWrite positions = positions.getLast? := by
  induction positions using snoc_induction with
  | empty => rfl
  | step positions position ih => simp [lastWrite, List.foldl_append, List.getLast?_append]

/-- Row lookup equals repeated map insertion of every successful candidate. -/
theorem rowPosition_lastWrite [DecidableEq Symbol] (automaton : Automaton State Symbol) (symbol : Symbol)
    (tables : List (State → Option Position)) (edges : List (Edge State Symbol)) :
    rowPosition automaton symbol tables edges = lastWrite (rowCandidates automaton symbol tables edges) := by
  rw [lastWrite_correct]
  induction edges with
  | nil => rfl
  | cons edge edges ih =>
      rw [rowCandidates, List.getLast?_append, List.getLast?_map, ← ih]
      cases tail : rowPosition automaton symbol tables edges <;>
        cases first : edgePosition automaton symbol tables edge <;>
        simp [rowPosition, tail, first]

/-- Every returned position uses the term's actual size and a valid run rank. -/
theorem positionsOf_valid [DecidableEq Symbol] (automaton : Automaton State Symbol)
    (plain : Decoder.Plain automaton) (term : Term Symbol) (state : State) (position : Position)
    (found : positionsOf automaton term state = some position) :
    position.size = nodeSize term ∧ position.rank < countAt automaton position.size state := by
  have replay := positionsOf_replay automaton term state position found
  rw [replayPosition, decode_compileAt] at replay
  have sized := (RecursiveSize.mem_enumerate_iff automaton plain position.size state term).mp
    (List.mem_of_getElem? replay)
  exact ⟨sized.2.symm, by rw [countAt_correct]; exact (List.getElem?_eq_some_iff.mp replay).1⟩

/-- Bottom-up term positions replay at the same global size-major offsets. -/
theorem positionsOf_sizeMajor_replay [DecidableEq Symbol] (automaton : Automaton State Symbol)
    (plain : Decoder.Plain automaton) (term : Term Symbol) (state : State) (position : Position)
    (bound : Nat) (found : positionsOf automaton term state = some position) (within : position.size ≤ bound) :
    Decoder.decode (Decoder.normalize (compileAtMost automaton bound state))
      (classOffset automaton position.size state + position.rank) = some term := by
  rw [sizeMajor_rank_replay automaton bound position.size state position.rank within
    (positionsOf_valid automaton plain term state position found).2]
  exact positionsOf_replay automaton term state position found

end MicroCFTA.TablePosition




