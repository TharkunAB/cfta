import MicroCFTA.SourceSizedGroupedRankLeaders
import MicroCFTA.SourceSizedGroupedPlain

/-!
# Source transition candidates and both position branches

The symbol and arity bucket filters candidates before child lookup. Equal
lengths make the checked lookup equal to the source zipWithM. The ordinary
branch uses every child position. The constrained branch uses group leaders.
Both branches read the cached prefix count fields.

These laws connect the candidate value operation to independent classes.
The recursive child tables and native candidate-map storage remain separate.
-/
namespace MicroCFTA.SourceSizedGroupedRankCandidates
open Language RecursiveSize SizedRank SourceSizedDecided
open RecursiveJoinFields (ValueIndex)
open SourceSizedGroupedIndex SourceSizedGroupedChainOrder

variable {State Symbol Result : Type}

private theorem checked_fold (build : List (Term Symbol) → Result)
    (indexes : State → ValueIndex (Term Symbol)) (classAt : State → Nat → List (Term Symbol))
    (correct : ∀ state, Correct (indexes state) (classAt state))
    (children : List State) (positions : List Position) (before : List State) (built : Position)
    (length : children.length = positions.length) :
    TablePosition.positionChildren (fun size state => (classAt state size).length)
      before built children positions =
        some (SourceSizedGroupedRankPrefixes.positionFold
          ((children.map indexes).scanl consumeChild (foldedIndex build indexes before))
          (children.map indexes) positions built) := by
  induction children generalizing positions before built with
  | nil =>
      have empty : positions = [] := List.length_eq_zero_iff.mp length.symm
      subst positions
      rfl
  | cons child children ih =>
      cases positions with
      | nil => simp at length
      | cons position positions =>
          have prefixSame : (foldedIndex build indexes before).counts =
              TablePosition.prefixCount (fun size state => (classAt state size).length) before :=
            funext (SourceSizedGroupedRankPrefixes.prefix_counts build indexes classAt correct before)
          have childSame : (indexes child).counts = fun size => (classAt child size).length :=
            funext (correct child).counts
          have next : consumeChild (foldedIndex build indexes before) (indexes child) =
              foldedIndex build indexes (before ++ [child]) := by simp [foldedIndex]
          simp only [List.map_cons, List.scanl_cons, SourceSizedGroupedRankPrefixes.positionFold,
            TablePosition.positionChildren, next]
          rw [prefixSame, childSame]
          exact ih positions (before ++ [child]) _ (by simpa using length)

/-- The ordinary source position fold reads every child and its actual cached prefix. -/
def plainPosition (indexes : State → ValueIndex (Term Symbol))
    (symbol : Symbol) (children : List State) (positions : List Position) : Position :=
  SourceSizedGroupedRankPrefixes.positionFold
    (SourceSizedGroupedRankPrefixes.prefixes (Term.node symbol) indexes children)
    (children.map indexes) positions ⟨1, 0⟩

/-- The empty-annotation branch replays the original term in the same grouped class order. -/
theorem plainPosition_replay (indexes : State → ValueIndex (Term Symbol))
    (classAt : State → Nat → List (Term Symbol))
    (correct : ∀ state, Correct (indexes state) (classAt state))
    (symbol : Symbol) (children : List State) (values : List (Term Symbol)) (positions : List Position)
    (positioned : TablePosition.Positioned (fun size state => classAt state size) children values positions) :
    let result := plainPosition indexes symbol children positions
    (rowClass classAt symbol children [] result.size)[result.rank]? = some (.node symbol values) := by
  have length := (SourceSizedGroupedRankLeaders.positioned_lengths classAt children values positions positioned).2
  have source := checked_fold (Term.node symbol) indexes classAt correct children positions [] ⟨1, 0⟩ length
  obtain ⟨result, computed, replay⟩ := TablePosition.positionChildren_replay
    (fun size state => classAt state size) (fun size state => (classAt state size).length)
    (fun _ _ => rfl) children values positions positioned [] ⟨1, 0⟩ []
    (by simp [TablePosition.rootForests, TablePosition.rooted, emptyForests])
  have same : result = plainPosition indexes symbol children positions :=
    Option.some.inj (computed.symm.trans source)
  subst result
  dsimp only
  rw [SourceSizedGroupedPlain.rowClass_nil_eq]
  have paid : children.foldl (fun built child => extendForests built (classAt child)) seed =
      TablePosition.rootForests (fun size state => classAt state size) children := by
    have initial : (seed : Nat → List (List (Term Symbol))) = TablePosition.rooted emptyForests := by
      funext size
      cases size with
      | zero => rfl
      | succ size => cases size <;> rfl
    simp only [TablePosition.rootForests, initial]
  rw [paid, List.getElem?_map]
  simpa only [List.nil_append, Option.map_some] using congrArg (Option.map (Term.node symbol)) replay

/-- The source checks equal children only in its nonempty-annotation branch. -/
def transitionPosition [DecidableEq Symbol] (indexes : State → ValueIndex (Term Symbol))
    (row : Row State Symbol (List (List Nat))) (values : List (Term Symbol))
    (positions : List Position) : Option Position :=
  if row.constraint = [] then some (plainPosition indexes row.label row.children positions)
  else if SourceSizedConjunctionSemantics.holds row.constraint (.node row.label values) then
    some (SourceSizedGroupedRankPrefixes.groupedPosition indexes row.label row.children row.constraint
      (SourceSizedGroupedRankLeaders.leaderPositions positions
        (CompactGroups.childGroups row.children.length row.constraint)))
  else none

/-- Both literal source branches replay the original transition term. -/
theorem transitionPosition_replay [DecidableEq Symbol]
    (indexes : State → ValueIndex (Term Symbol)) (classAt : State → Nat → List (Term Symbol))
    (correct : ∀ state, Correct (indexes state) (classAt state))
    (row : Row State Symbol (List (List Nat)))
    (valid : CompactGroups.ValidClasses row.children.length row.constraint)
    (values : List (Term Symbol)) (positions : List Position)
    (positioned : TablePosition.Positioned (fun size state => classAt state size) row.children values positions)
    (result : Position) (found : transitionPosition indexes row values positions = some result) :
    (rowClass classAt row.label row.children row.constraint result.size)[result.rank]? =
      some (.node row.label values) := by
  by_cases plain : row.constraint = []
  · have same : plainPosition indexes row.label row.children positions = result := by
      apply Option.some.inj
      simpa only [transitionPosition, plain, ite_true] using found
    subst result
    rw [plain]
    exact plainPosition_replay indexes classAt correct row.label row.children values positions positioned
  · by_cases held : SourceSizedConjunctionSemantics.holds row.constraint (.node row.label values) = true
    · have same : SourceSizedGroupedRankPrefixes.groupedPosition indexes row.label row.children row.constraint
          (SourceSizedGroupedRankLeaders.leaderPositions positions
            (CompactGroups.childGroups row.children.length row.constraint)) = result := by
        apply Option.some.inj
        simpa only [transitionPosition, plain, ite_false, held, ite_true] using found
      subst result
      exact SourceSizedGroupedRankLeaders.transition_replay indexes classAt correct row.label row.children
        row.constraint valid values positions positioned held
    · simp [transitionPosition, plain, held] at found

/-- Correct child tables retain replay at every stored state-position pair. -/
def TablesSound (classAt : State → Nat → List (Term Symbol))
    (tables : List (State → Option Position)) (values : List (Term Symbol)) : Prop :=
  All₂ (fun table term => ∀ state position, table state = some position →
    (classAt state position.size)[position.rank]? = some term) tables values

/-- Ordered child lookup keeps all state, term and position associations. -/
theorem lookupChildren_positioned (classAt : State → Nat → List (Term Symbol))
    (tables : List (State → Option Position)) (values : List (Term Symbol))
    (sound : TablesSound classAt tables values) (children : List State) (positions : List Position)
    (found : TablePosition.lookupChildren children tables = some positions) :
    TablePosition.Positioned (fun size state => classAt state size) children values positions := by
  induction sound generalizing children positions with
  | nil =>
      cases children with
      | nil => have same : [] = positions := by simpa [TablePosition.lookupChildren] using found
               subst positions; exact .nil
      | cons child children => cases found
  | @cons table term tables terms correct rest ih =>
      cases children with
      | nil => cases found
      | cons child children =>
          cases read : table child with
          | none => simp [TablePosition.lookupChildren, read] at found
          | some position =>
              cases tail : TablePosition.lookupChildren children tables with
              | none => simp [TablePosition.lookupChildren, read, tail] at found
              | some positions' =>
                  have same : position :: positions' = positions := by
                    simpa [TablePosition.lookupChildren, read, tail] using found
                  subst positions
                  exact .cons (correct child position read) (ih children positions' tail)

/-- Select the source symbol-and-arity bucket before the child map lookups. -/
def candidate [DecidableEq Symbol] (indexes : State → ValueIndex (Term Symbol))
    (row : Row State Symbol (List (List Nat))) (symbol : Symbol) (values : List (Term Symbol))
    (tables : List (State → Option Position)) : Option Position :=
  if row.label = symbol ∧ row.children.length = values.length then do
    let positions ← TablePosition.lookupChildren row.children tables
    transitionPosition indexes row values positions
  else none

/-- A successful actual transition candidate replays its complete input term. -/
theorem candidate_replay [DecidableEq Symbol]
    (indexes : State → ValueIndex (Term Symbol)) (classAt : State → Nat → List (Term Symbol))
    (correct : ∀ state, Correct (indexes state) (classAt state))
    (row : Row State Symbol (List (List Nat)))
    (valid : CompactGroups.ValidClasses row.children.length row.constraint)
    (symbol : Symbol) (values : List (Term Symbol)) (tables : List (State → Option Position))
    (sound : TablesSound classAt tables values) (result : Position)
    (found : candidate indexes row symbol values tables = some result) :
    (rowClass classAt row.label row.children row.constraint result.size)[result.rank]? =
      some (.node symbol values) := by
  unfold candidate at found
  split at found
  next matched =>
    obtain ⟨positions, lookedUp, computed⟩ := Option.bind_eq_some_iff.mp found
    have replay := transitionPosition_replay indexes classAt correct row valid values positions
      (lookupChildren_positioned classAt tables values sound row.children positions lookedUp) result computed
    simpa only [matched.1] using replay
  next => cases found

end MicroCFTA.SourceSizedGroupedRankCandidates
