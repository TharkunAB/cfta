import MicroCFTA.SourceSizedGroupedPositions
import MicroCFTA.SourceSizedGroupedIndex

/-!
# Cached source prefixes in grouped transition ranking

The source caches scanl consumeChild seed for each transition. Ranking zips
those prefixes with child indexes and child positions. The zip stops at its
shortest input. Each productPosition reads the actual count fields.

The independent row classes specify replay. They do not construct the prefix
indexes or their counts. Recursive child field correctness and child position
replay remain internal induction inputs. Native map storage and the complete
bottom-up candidate worker remain separate.
-/
namespace MicroCFTA.SourceSizedGroupedRankPrefixes
open Language RecursiveSize SizedRank
open RecursiveJoinFields (ValueIndex)
open SourceSizedGroupedIndex SourceSizedGroupedChainOrder

variable {State Symbol Key Result : Type}

/-- Cache the literal source scan of the paid constructor and child indexes. -/
def prefixes (build : List (Term Symbol) → Result)
    (indexes : Key → ValueIndex (Term Symbol)) (children : List Key) :
    List (ValueIndex (List (Term Symbol) → Result)) :=
  (children.map indexes).scanl consumeChild (payIndex (constantIndex build))

/-- Each child adds one cached prefix after the initial paid constructor. -/
theorem prefixes_length (build : List (Term Symbol) → Result)
    (indexes : Key → ValueIndex (Term Symbol)) (children : List Key) :
    (prefixes build indexes children).length = children.length + 1 := by
  simp [prefixes]

/-- The final cached prefix is the independently constructed full row fold. -/
theorem prefixes_last (build : List (Term Symbol) → Result)
    (indexes : Key → ValueIndex (Term Symbol)) (children : List Key) :
    (prefixes build indexes children).getLast? = some (foldedIndex build indexes children) := by
  simp only [prefixes, List.getLast?_scanl, List.foldl_map, foldedIndex]

private theorem paid_forests (classes : Key → Nat → List (Term Symbol))
    (children : List Key) :
    children.foldl (fun built child => extendForests built (classes child)) seed =
      TablePosition.rootForests (fun size child => classes child size) children := by
  have same : (seed : Nat → List (List (Term Symbol))) = TablePosition.rooted emptyForests := by
    funext size
    cases size with
    | zero => rfl
    | succ size => cases size <;> rfl
  simp only [TablePosition.rootForests, same]

/-- Cached prefix count fields are the rooted convolution used by ranking. -/
theorem prefix_counts (build : List (Term Symbol) → Result)
    (indexes : Key → ValueIndex (Term Symbol)) (classes : Key → Nat → List (Term Symbol))
    (correct : ∀ key, Correct (indexes key) (classes key)) (children : List Key) (size : Nat) :
    (foldedIndex build indexes children).counts size =
      TablePosition.prefixCount (fun size key => (classes key size).length) children size := by
  have exactCounts := (folded_correct build indexes classes correct children).counts size
  simp only [List.length_map] at exactCounts
  rw [paid_forests] at exactCounts
  exact exactCounts.trans (TablePosition.length_rootForests _ children size)

/-- Fold the literal three-way source zip over cached prefixes and child positions. -/
def positionFold : List (ValueIndex (List (Term Symbol) → Result)) →
    List (ValueIndex (Term Symbol)) → List Position → Position → Position
  | prefixIndex :: prefixes, child :: children, position :: positions, built =>
      positionFold prefixes children positions (productPosition prefixIndex.counts child.counts built position)
  | _, _, _, built => built

private theorem folded_snoc (build : List (Term Symbol) → Result)
    (indexes : Key → ValueIndex (Term Symbol)) (before : List Key) (child : Key) :
    consumeChild (foldedIndex build indexes before) (indexes child) =
      foldedIndex build indexes (before ++ [child]) := by
  simp [foldedIndex]

/-- Actual cached count fields give the same product ranks as the checked group recurrence. -/
theorem positionFold_eq (build : List (Term Symbol) → Result)
    (indexes : List Nat → ValueIndex (Term Symbol))
    (classes : List Nat → Nat → List (Term Symbol))
    (correct : ∀ group, Correct (indexes group) (classes group))
    (groups : List (List Nat)) (positions : List Position)
    (before : List (List Nat)) (built : Position) :
    positionFold ((groups.map indexes).scanl consumeChild (foldedIndex build indexes before))
      (groups.map indexes) positions built =
        SourceSizedGroupedPositions.foldGroups (fun size group => (classes group size).length)
          before built groups positions := by
  induction groups generalizing positions before built with
  | nil => rfl
  | cons group groups ih =>
      cases positions with
      | nil => simp only [List.map_cons, List.scanl_cons, positionFold, SourceSizedGroupedPositions.foldGroups]
      | cons position positions =>
          have prefixSame : (foldedIndex build indexes before).counts =
              TablePosition.prefixCount (fun size key => (classes key size).length) before :=
            funext (prefix_counts build indexes classes correct before)
          have childSame : (indexes group).counts = fun size => (classes group size).length :=
            funext (correct group).counts
          simp only [List.map_cons, List.scanl_cons, positionFold,
            SourceSizedGroupedPositions.foldGroups, folded_snoc]
          rw [prefixSame, childSame]
          exact ih positions (before ++ [group]) _

/-- Rank a transition with its cached prefixes and the same source child-index list. -/
def position (build : List (Term Symbol) → Result)
    (indexes : List Nat → ValueIndex (Term Symbol))
    (groups : List (List Nat)) (positions : List Position) : Position :=
  positionFold (prefixes build indexes groups) (groups.map indexes) positions ⟨1, 0⟩

/-- The initial cached source fold agrees with the checked paid group-position fold. -/
theorem position_eq (build : List (Term Symbol) → Result)
    (indexes : List Nat → ValueIndex (Term Symbol))
    (classes : List Nat → Nat → List (Term Symbol))
    (correct : ∀ group, Correct (indexes group) (classes group))
    (groups : List (List Nat)) (positions : List Position) :
    position build indexes groups positions =
      SourceSizedGroupedPositions.foldGroups (fun size group => (classes group size).length)
        [] ⟨1, 0⟩ groups positions :=
  positionFold_eq build indexes classes correct groups positions [] ⟨1, 0⟩

/-- Read each group index from its first original child and keep the actual cached prefix counts. -/
def groupedPosition (indexes : State → ValueIndex (Term Symbol))
    (symbol : Symbol) (children : List State) (classes : List (List Nat))
    (positions : List Position) : Position :=
  let groups := CompactGroups.childGroups children.length classes
  position (assemble symbol children.length groups) (groupIndex indexes children) groups positions

/-- Ranking with actual source prefix fields replays the assembled grouped transition. -/
theorem groupedPosition_replay (indexes : State → ValueIndex (Term Symbol))
    (classAt : State → Nat → List (Term Symbol))
    (correct : ∀ state, Correct (indexes state) (classAt state))
    (symbol : Symbol) (children : List State) (classes : List (List Nat))
    (selected : List (Term Symbol)) (positions : List Position)
    (positioned : TablePosition.Positioned
      (fun size group => groupClass classAt children group size)
      (CompactGroups.childGroups children.length classes) selected positions) :
    let result := groupedPosition indexes symbol children classes positions
    (rowClass classAt symbol children classes result.size)[result.rank]? =
      some (assemble symbol children.length (CompactGroups.childGroups children.length classes) selected) := by
  unfold groupedPosition
  rw [position_eq _ _ _ (group_correct indexes classAt correct children)]
  exact SourceSizedGroupedPositions.rowPosition_replay classAt symbol children classes selected positions positioned

end MicroCFTA.SourceSizedGroupedRankPrefixes
