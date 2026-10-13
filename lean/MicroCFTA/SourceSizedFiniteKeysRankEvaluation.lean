import MicroCFTA.TablePositionFiniteEvaluation
import MicroCFTA.SourceSizedFiniteKeysDispatchApi

/-!
# Finite optimized inverse queries on original map keys

The optimized dispatch branch has a finite bottom-up rank computation for
every finite input term. The count inventory uses the original canonical
rows and actual finite map keys. Its result equals the public rank query.
Both signed inverse laws hold for this finite result.
-/
namespace MicroCFTA.SourceSizedFiniteKeysRankEvaluation
open Language RecursiveSize SizedRank SourceSizedDecided SourceSizedFiniteKeys SourceSizedDispatcher
open SourceSizedFiniteKeysDispatch SourceDenseRows TablePositionFiniteEvaluation
open SourceObservations SourceSymbolicIndex

variable {State Symbol Payload : Type} [DecidableEq State] [Ord State]
  [DecidableEq Symbol] [Ord Symbol] [Std.TransOrd Symbol] [Std.LawfulEqOrd Symbol]
  (table : SourceSizedFiniteKeys.Table State Symbol Payload) (root : State)
  (valid : FTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
    .ok (interpreted table (fun _ _ => true)))

/-- The complete finite count inventory for one original-state rank query. -/
noncomputable def rankCounts (term : Term Symbol) : List ((Nat × State) × Nat) :=
  counts (ordinaryRows (nativeSorted table root valid)) (keys table) (nodeSize term)

/-- The explicit finite state-position map of the original optimized query. -/
noncomputable def rankTable (term : Term Symbol) : List (State × Option Position) :=
  evaluate (ordinaryRows (nativeSorted table root valid)) (rankCounts table root valid term) (keys table) term

omit [Std.TransOrd Symbol] [Std.LawfulEqOrd Symbol] in
/-- Every original-key rank query has finite count derivations and exact finite map readback. -/
theorem raw_finite (term : Term Symbol) :
    CountsEvaluation (ordinaryRows (nativeSorted table root valid)) (rankCounts table root valid term) ∧
      positionLookup (rankTable table root valid term) =
        TablePosition.positionsOf (ordinaryRows (nativeSorted table root valid)) term :=
  finite_rank _ (keys table) (sorted_supported table root valid (fun _ _ => true)) term

variable {Formula : Type} [DecidableEq Formula] [Ord (Label Formula)]
  [Std.TransOrd (Label Formula)] [Std.LawfulEqOrd (Label Formula)]

/-- The finite optimized inverse is the actual public query and has both signed inverse laws. -/
theorem native_rank_laws
    (table : SourceSizedFiniteKeys.Table State (Label Formula) (Constraint Formula)) (root : State)
    (valid : FTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (passed : (plainCheck (lookup table) (keys table) && unambiguous table root valid) = true)
    (api : Api (Label Formula)) (success : nativeSized table root valid = .ok api)
    (term : Term (Label Formula)) :
    CountsEvaluation (ordinaryRows (nativeSorted table root valid)) (rankCounts table root valid term) ∧
      positionLookup (rankTable table root valid term) root = api.rank term ∧
      (∀ size rank, (positionLookup (rankTable table root valid term) root).map
        (fun position => (Int.ofNat position.size, Int.ofNat position.rank)) = some (size, rank) ↔
          api.unrank size rank = some term) := by
  have publicSuccess := success
  rw [nativeSized_eq table root valid] at publicSuccess
  unfold nativeSized at success
  rw [ite_eq_left passed] at success
  have same : optimizedApi (ordinaryRows (nativeSorted table root valid)) root = api := Except.ok.inj success
  obtain ⟨finite, exactMap⟩ := raw_finite table root valid term
  have exactRank : positionLookup (rankTable table root valid term) root = api.rank term := by
    rw [exactMap, ← same]
    rfl
  refine ⟨finite, exactRank, ?_⟩
  intro size rank
  rw [exactRank]
  exact SourceSizedPreprocessing.publicSized_signed_inverses (input table root valid) api publicSuccess size rank term

end MicroCFTA.SourceSizedFiniteKeysRankEvaluation
