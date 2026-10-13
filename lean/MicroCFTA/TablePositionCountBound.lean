import MicroCFTA.TablePosition

/-!
# Finite count dependencies of bottom-up ranking

The rank worker reads a count callback. Replacing that callback outside the
input term's node-count bound cannot change the result. This includes failed
lookups and counts of earlier transitions that do not accept the term.
-/
namespace MicroCFTA.TablePositionCountBound
open Language RecursiveSize SizedRank TablePosition

variable {State Symbol : Type}

/-- The source transition worker with its count reads supplied explicitly. -/
def edge [DecidableEq Symbol] (counts : Nat → State → Nat) (symbol : Symbol)
    (tables : List (State → Option Position)) (transition : Edge State Symbol) : Option Position :=
  if transition.label = symbol then do
    let positions ← lookupChildren transition.children tables
    positionChildren counts [] ⟨1, 0⟩ transition.children positions
  else none

/-- The source row worker retains last-write selection and all earlier offsets. -/
def row [DecidableEq Symbol] (counts : Nat → State → Nat) (symbol : Symbol)
    (tables : List (State → Option Position)) : List (Edge State Symbol) → Option Position
  | [] => none
  | transition :: rest =>
      match row counts symbol tables rest with
      | some position => some ⟨position.size, prefixCount counts transition.children position.size + position.rank⟩
      | none => edge counts symbol tables transition

/-- Bottom-up ranking computes each child table before its parent table. -/
def positions [DecidableEq Symbol] (A : Automaton State Symbol) (counts : Nat → State → Nat) :
    Term Symbol → State → Option Position
  | .node symbol children =>
      let tables := children.map (positions A counts)
      fun state => row counts symbol tables (A state)

/-- Supplying actual counts retains the exact source row computation. -/
theorem row_actual [DecidableEq Symbol] (A : Automaton State Symbol) (symbol : Symbol)
    (tables : List (State → Option Position)) (transitions : List (Edge State Symbol)) :
    row (countAt A) symbol tables transitions = rowPosition A symbol tables transitions := by
  induction transitions with
  | nil => rfl
  | cons transition rest ih => simp only [row, rowPosition, ih, edgeCount, edge, edgePosition]; rfl

/-- The explicit count callback preserves the complete original bottom-up worker. -/
theorem positions_actual [DecidableEq Symbol] (A : Automaton State Symbol) (term : Term Symbol) :
    positions A (countAt A) term = positionsOf A term := by
  induction term using Term.rec
    (motive_2 := fun children => children.map (positions A (countAt A)) = children.map (positionsOf A)) with
  | node symbol children ih => simp only [positions, positionsOf, ih, row_actual]
  | nil => rfl
  | cons child children ih ihs => simp only [List.map_cons, ih, ihs]

/-- A child table can return only its child's node count as the size. -/
def TablesSized (tables : List (State → Option Position)) (terms : List (Term Symbol)) : Prop :=
  All₂ (fun table term => ∀ state position, table state = some position → position.size = nodeSize term) tables terms

/-- Ordered child lookup retains the sum of the actual child node counts. -/
theorem lookup_sizes (tables : List (State → Option Position)) (terms : List (Term Symbol))
    (sized : TablesSized tables terms) (states : List State) (found : List Position)
    (done : lookupChildren states tables = some found) :
    (found.map Position.size).sum = forestSize terms := by
  induction sized generalizing states found with
  | nil =>
      cases states with
      | nil => have same : [] = found := Option.some.inj done; subst found; rfl
      | cons state states => cases done
  | @cons table term tables terms head rest ih =>
      cases states with
      | nil => cases done
      | cons state states =>
          cases first : table state with
          | none => simp [lookupChildren, first] at done
          | some position =>
              cases later : lookupChildren states tables with
              | none => simp [lookupChildren, first, later] at done
              | some remaining =>
                  have same : position :: remaining = found := by simpa [lookupChildren, first, later] using done
                  subst found
                  simp only [List.map_cons, List.sum_cons, head state position first,
                    ih states remaining later, forestSize, List.foldr_cons]

/-- Product accumulation changes size only by addition, independently of count values. -/
theorem children_size (counts : Nat → State → Nat) (before : List State) (built : Position)
    (states : List State) (found : List Position) (result : Position)
    (done : positionChildren counts before built states found = some result) :
    result.size = built.size + (found.map Position.size).sum := by
  induction states generalizing before built found with
  | nil => cases found with
      | nil => have same := Option.some.inj done; subst result; simp
      | cons position remaining => cases done
  | cons state states ih =>
      cases found with
      | nil => cases done
      | cons position remaining =>
          have same := ih (before ++ [state])
            (productPosition (prefixCount counts before) (fun size => counts size state) built position)
            remaining done
          simpa only [productPosition_size, List.map_cons, List.sum_cons, Nat.add_assoc] using same

/-- A successful transition always returns the actual input term size. -/
theorem edge_size [DecidableEq Symbol] (counts : Nat → State → Nat) (symbol : Symbol)
    (tables : List (State → Option Position)) (terms : List (Term Symbol))
    (sized : TablesSized tables terms) (transition : Edge State Symbol) (result : Position)
    (done : edge counts symbol tables transition = some result) : result.size = nodeSize (.node symbol terms) := by
  unfold edge at done
  split at done
  · cases found : lookupChildren transition.children tables with
    | none => simp [found] at done
    | some positions =>
        have computed : positionChildren counts [] ⟨1, 0⟩ transition.children positions = some result := by
          simpa [found] using done
        have same := children_size counts [] ⟨1, 0⟩ transition.children positions result computed
        rw [lookup_sizes tables terms sized transition.children positions found] at same
        simpa only [nodeSize, forestSize, Nat.add_comm] using same
  · cases done

/-- Last-write selection and earlier offsets preserve the input term size. -/
theorem row_size [DecidableEq Symbol] (counts : Nat → State → Nat) (symbol : Symbol)
    (tables : List (State → Option Position)) (terms : List (Term Symbol))
    (sized : TablesSized tables terms) (transitions : List (Edge State Symbol)) (result : Position)
    (done : row counts symbol tables transitions = some result) : result.size = nodeSize (.node symbol terms) := by
  induction transitions generalizing result with
  | nil => cases done
  | cons transition rest ih =>
      cases tail : row counts symbol tables rest with
      | none => exact edge_size counts symbol tables terms sized transition result (by simpa [row, tail] using done)
      | some position =>
          have same : (⟨position.size, prefixCount counts transition.children position.size + position.rank⟩ : Position) = result := by
            simpa [row, tail] using done
          rw [← same]
          exact ih position tail

/-- Even arbitrary count replies cannot change a returned position's node count. -/
theorem positions_size [DecidableEq Symbol] (A : Automaton State Symbol) (counts : Nat → State → Nat)
    (term : Term Symbol) (state : State) (result : Position)
    (done : positions A counts term state = some result) : result.size = nodeSize term := by
  induction term using Term.rec
    (motive_2 := fun terms => TablesSized (terms.map (positions A counts)) terms) generalizing state result with
  | node symbol terms ih =>
      rw [positions] at done
      exact row_size counts symbol _ terms ih (A state) result done
  | nil => exact .nil
  | cons term terms ih ihs => exact .cons ih ihs

/-- Rooted prefix counts read no child count above the prefix's size. -/
theorem prefix_congr (left right : Nat → State → Nat) (bound : Nat)
    (same : ∀ size, size ≤ bound → ∀ state, left size state = right size state)
    (states : List State) (size : Nat) (within : size ≤ bound) :
    prefixCount left states size = prefixCount right states size := by
  cases size with
  | zero => rfl
  | succ size => exact forestCounts_congr left right bound same states size (by omega)

/-- Mixed-radix rank arithmetic reads counts only through the combined size. -/
theorem product_congr (left right : Nat → State → Nat) (bound : Nat)
    (same : ∀ size, size ≤ bound → ∀ state, left size state = right size state)
    (before : List State) (state : State) (built child : Position) (within : built.size + child.size ≤ bound) :
    productPosition (prefixCount left before) (fun size => left size state) built child =
      productPosition (prefixCount right before) (fun size => right size state) built child := by
  have sumSame : ((List.range built.size).map (fun split =>
      prefixCount left before split * left (built.size + child.size - split) state)).sum =
      ((List.range built.size).map (fun split =>
      prefixCount right before split * right (built.size + child.size - split) state)).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro split member
    have fits := List.mem_range.mp member
    rw [prefix_congr left right bound same before split (by omega), same _ (by omega)]
  simp only [productPosition, sumSame, same child.size (by omega)]

/-- Finite product accumulation never reads a count above its final size. -/
theorem children_congr (left right : Nat → State → Nat) (bound : Nat)
    (same : ∀ size, size ≤ bound → ∀ state, left size state = right size state)
    (before : List State) (built : Position) (states : List State) (found : List Position)
    (within : built.size + (found.map Position.size).sum ≤ bound) :
    positionChildren left before built states found = positionChildren right before built states found := by
  induction states generalizing before built found with
  | nil => cases found <;> rfl
  | cons state states ih =>
      cases found with
      | nil => rfl
      | cons position remaining =>
          simp only [List.map_cons, List.sum_cons] at within
          simp only [positionChildren]
          rw [product_congr left right bound same before state built position (by omega)]
          exact ih _ _ remaining (by simpa only [productPosition_size, Nat.add_assoc] using within)

/-- Equal bounded counts preserve matching, failed child lookup, and transition ranks. -/
theorem edge_congr [DecidableEq Symbol] (left right : Nat → State → Nat) (bound : Nat)
    (same : ∀ size, size ≤ bound → ∀ state, left size state = right size state)
    (symbol : Symbol) (tables : List (State → Option Position)) (terms : List (Term Symbol))
    (sized : TablesSized tables terms) (within : nodeSize (.node symbol terms) ≤ bound)
    (transition : Edge State Symbol) : edge left symbol tables transition = edge right symbol tables transition := by
  unfold edge
  split
  · cases found : lookupChildren transition.children tables with
    | none => simp
    | some positions =>
        change positionChildren left [] ⟨1, 0⟩ transition.children positions =
          positionChildren right [] ⟨1, 0⟩ transition.children positions
        apply children_congr left right bound same
        rw [lookup_sizes tables terms sized transition.children positions found]
        simpa only [nodeSize, forestSize, Nat.add_comm] using within
  · rfl

/-- Every earlier transition offset also reads only the input term's bounded counts. -/
theorem row_congr [DecidableEq Symbol] (left right : Nat → State → Nat) (bound : Nat)
    (same : ∀ size, size ≤ bound → ∀ state, left size state = right size state)
    (symbol : Symbol) (tables : List (State → Option Position)) (terms : List (Term Symbol))
    (sized : TablesSized tables terms) (within : nodeSize (.node symbol terms) ≤ bound)
    (transitions : List (Edge State Symbol)) : row left symbol tables transitions = row right symbol tables transitions := by
  induction transitions with
  | nil => rfl
  | cons transition rest ih =>
      simp only [row, ih]
      cases tail : row right symbol tables rest with
      | none => exact edge_congr left right bound same symbol tables terms sized within transition
      | some position =>
          change some (⟨position.size, prefixCount left transition.children position.size + position.rank⟩ : Position) =
            some (⟨position.size, prefixCount right transition.children position.size + position.rank⟩ : Position)
          rw [prefix_congr left right bound same transition.children position.size
            (by rw [row_size right symbol tables terms sized rest position tail]; exact within)]

/-- Ranking a finite term depends only on counts through its node-count size. -/
theorem positions_congr [DecidableEq Symbol] (A : Automaton State Symbol)
    (left right : Nat → State → Nat) (bound : Nat)
    (same : ∀ size, size ≤ bound → ∀ state, left size state = right size state)
    (term : Term Symbol) (within : nodeSize term ≤ bound) : positions A left term = positions A right term := by
  induction term using Term.rec
    (motive_2 := fun terms => forestSize terms ≤ bound →
      terms.map (positions A left) = terms.map (positions A right)) with
  | node symbol terms ih =>
      have smaller : forestSize terms ≤ bound := by
        have sizeBound : forestSize terms + 1 ≤ bound := by simpa only [nodeSize, forestSize] using within
        omega
      funext state
      simp only [positions, ih smaller]
      apply row_congr left right bound same symbol _ terms _ within
      have sized : ∀ terms : List (Term Symbol), TablesSized (terms.map (positions A right)) terms := by
        intro terms
        induction terms with
        | nil => exact .nil
        | cons term terms ih => exact .cons (positions_size A right term) ih
      exact sized terms
  | nil => rfl
  | cons term terms ih ihs =>
      rename_i sizeBound
      have sum : nodeSize term + forestSize terms ≤ bound := sizeBound
      simp only [List.map_cons, ih (by omega), ihs (by omega)]

end MicroCFTA.TablePositionCountBound
