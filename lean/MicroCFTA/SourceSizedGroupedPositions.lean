import MicroCFTA.SourceSizedGroupedRowUnique
import MicroCFTA.TablePosition

/-!
# Source group positions and prefix products

The equality branch of termPositions scales each representative child's size.
It then folds productPosition over the same ordered group prefixes used by
stateTable. This file connects that literal fold to the checked row classes.
The child positions are local induction inputs. Native count fields, recursive
child maps, candidate dispatch and final table overwrite remain separate.
-/
namespace MicroCFTA.SourceSizedGroupedPositions
open Language RecursiveSize SizedRank SourceSizedGroupedChainOrder

variable {State Symbol : Type}

/-- The source scaledRank changes a size and retains its class rank. -/
def scalePosition (factor : Nat) (position : Position) : Position :=
  ⟨factor * position.size, position.rank⟩

/-- A scaled representative position replays the same child term. -/
theorem scalePosition_replay (inner : Nat → List Value) (factor : Nat)
    (positive : 0 < factor) (position : Position) (value : Value)
    (found : (inner position.size)[position.rank]? = some value) :
    (scaled factor inner (scalePosition factor position).size)[(scalePosition factor position).rank]? =
      some value := by
  by_cases one : factor = 1
  · subst factor
    simpa [scaled, scalePosition] using found
  · simpa [scaled, scalePosition, one, Nat.mul_mod, Nat.mul_div_cancel_left _ positive] using found

/-- Read the actual first child of a nonempty group and scale its position. -/
theorem groupPosition_replay (classAt : State → Nat → List (Term Symbol))
    (children : List State) (first : Nat) (rest : List Nat) (child : State)
    (read : children[first]? = some child) (position : Position) (term : Term Symbol)
    (found : (classAt child position.size)[position.rank]? = some term) :
    (groupClass classAt children (first :: rest)
      (scalePosition (first :: rest).length position).size)[position.rank]? = some term := by
  simp only [groupClass, read]
  exact scalePosition_replay (classAt child) _ (by simp) position term found

/-- Count a paid group prefix by source convolution over its child class counts. -/
def prefixCounts (classAt : State → Nat → List (Term Symbol)) (children : List State)
    (groups : List (List Nat)) : Nat → Nat :=
  TablePosition.prefixCount (fun size group => (groupClass classAt children group size).length) groups

/-- The source product fold stops when either zipped operand list ends. -/
def foldGroups (counts : Nat → List Nat → Nat) :
    List (List Nat) → Position → List (List Nat) → List Position → Position
  | _, built, [], _ => built
  | _, built, _, [] => built
  | before, built, group :: groups, position :: positions =>
      foldGroups counts (before ++ [group])
        (productPosition (TablePosition.prefixCount counts before) (fun size => counts size group)
          built position) groups positions

/-- Equal source operand lengths give the checked child-position fold. -/
theorem foldGroups_checked (counts : Nat → List Nat → Nat)
    (before : List (List Nat)) (built : Position) (groups : List (List Nat))
    (positions : List Position) (length : groups.length = positions.length) :
    TablePosition.positionChildren counts before built groups positions =
      some (foldGroups counts before built groups positions) := by
  induction groups generalizing before built positions with
  | nil =>
      have empty : positions = [] := List.length_eq_zero_iff.mp length.symm
      subst positions
      rfl
  | cons group groups ih =>
      cases positions with
      | nil => simp at length
      | cons position positions =>
          exact ih (before ++ [group])
            (productPosition (TablePosition.prefixCount counts before) (fun size => counts size group)
              built position) positions (by simpa using length)

private theorem paid_seed :
    (TablePosition.rooted (emptyForests : Nat → List (List (Term Symbol)))) = seed := by
  funext size
  cases size with
  | zero => rfl
  | succ size => cases size <;> rfl

/-- Group prefixes are the actual paid source left fold. -/
theorem rootForests_eq (classAt : State → Nat → List (Term Symbol))
    (children : List State) (groups : List (List Nat)) :
    TablePosition.rootForests (fun size group => groupClass classAt children group size) groups =
      groups.foldl (fun built group => extendForests built (groupClass classAt children group)) seed := by
  unfold TablePosition.rootForests
  rw [paid_seed]

/-- Numeric prefix counts equal the lengths of the actual ordered group products. -/
theorem prefixCounts_exact (classAt : State → Nat → List (Term Symbol))
    (children : List State) (groups : List (List Nat)) (size : Nat) :
    prefixCounts classAt children groups size =
      (groups.foldl (fun built group => extendForests built (groupClass classAt children group)) seed size).length := by
  rw [← rootForests_eq]
  exact (TablePosition.length_rootForests _ groups size).symm

/-- Replayed group children give the same selection at the computed source product rank. -/
theorem foldGroups_replay (classAt : State → Nat → List (Term Symbol))
    (children : List State) (groups : List (List Nat))
    (selected : List (Term Symbol)) (positions : List Position)
    (positioned : TablePosition.Positioned
      (fun size group => groupClass classAt children group size) groups selected positions) :
    let position := foldGroups (fun size group => (groupClass classAt children group size).length)
      [] ⟨1, 0⟩ groups positions
    (groups.foldl (fun built group => extendForests built (groupClass classAt children group))
      seed position.size)[position.rank]? = some selected := by
  have lengths : groups.length = positions.length := by
    induction positioned with
    | nil => rfl
    | cons _ _ ih => exact congrArg Nat.succ ih
  obtain ⟨position, computed, replay⟩ := TablePosition.positionChildren_replay
    (fun size group => groupClass classAt children group size)
    (fun size group => (groupClass classAt children group size).length)
    (fun _ _ => rfl) groups selected positions positioned [] ⟨1, 0⟩ []
    (by simp [TablePosition.rootForests, TablePosition.rooted, emptyForests])
  rw [foldGroups_checked _ [] ⟨1, 0⟩ groups positions lengths] at computed
  have same := Option.some.inj computed
  subst position
  simpa only [List.nil_append, rootForests_eq] using replay

/-- The actual source group-product rank replays the assembled transition term. -/
theorem rowPosition_replay (classAt : State → Nat → List (Term Symbol))
    (symbol : Symbol) (children : List State) (classes : List (List Nat))
    (selected : List (Term Symbol)) (positions : List Position)
    (positioned : TablePosition.Positioned
      (fun size group => groupClass classAt children group size)
      (CompactGroups.childGroups children.length classes) selected positions) :
    let groups := CompactGroups.childGroups children.length classes
    let position := foldGroups (fun size group => (groupClass classAt children group size).length)
      [] ⟨1, 0⟩ groups positions
    (rowClass classAt symbol children classes position.size)[position.rank]? =
      some (assemble symbol children.length groups selected) := by
  have replay := foldGroups_replay classAt children _ selected positions positioned
  dsimp only at replay ⊢
  unfold rowClass
  dsimp only
  rw [List.getElem?_map, replay]
  rfl

end MicroCFTA.SourceSizedGroupedPositions
