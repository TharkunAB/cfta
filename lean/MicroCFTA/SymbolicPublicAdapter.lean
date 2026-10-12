import MicroCFTA.SymbolicCacheIndependence

/-!
# The public on-demand symbolic ranked adapter

`symbolicRanked` counts once and passes the count to `fromIndexedOnDemand`.
That constructor rejects nonpositive counts. Successful objects retain a
shared count snapshot. Public unranking checks negative ranks before the
upper bound. Inverse ranking reads the snapshot directly. Execution errors
below are the explicit bounds of the executable proof port.
-/
namespace MicroCFTA.SymbolicPublicAdapter
open Language SymbolicDriver

/-- Public ranked failures and explicit execution-bound failures remain distinct. -/
inductive Error where
  | emptyRanked
  | negativeRank (rank : Int)
  | outOfRange (rank : Int) (count : Nat)
  | execution (cause : SymbolicDriver.Error)
  deriving DecidableEq, Repr

/-- An on-demand source retains its original root, cardinality, and initial shared counts. -/
structure Compiled (Symbol : Type) where
  root : Nat
  count : Nat
  cache : Counts Symbol

/-- Count the graph once and perform the actual on-demand nonempty-source check. -/
def compile [DecidableEq Symbol] [Ord Symbol] (graph : Graph Symbol) (fuel root : Nat) : Except Error (Compiled Symbol) := do
  let (total, cache) ← (countNode graph fuel root {}).mapError Error.execution
  if total ≤ 0 then throw .emptyRanked else pure ⟨root, total.toNat, cache⟩

/-- Public range checks precede the actual selected-term query on the shared snapshot. -/
def select [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (fuel : Nat) (compiled : Compiled Symbol) (rank : Int) :
    Except Error (Term Symbol × Counts Symbol) :=
  if rank < 0 then .error (.negativeRank rank)
  else if (compiled.count : Int) ≤ rank then .error (.outOfRange rank compiled.count)
  else ((selectAt graph order fuel compiled.root [] rank compiled.cache).map
    (fun (result, cache) => (result.1, cache))).mapError Error.execution

/-- The inverse uses the same compiled graph and count snapshot. -/
def inverse [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (fuel : Nat) (compiled : Compiled Symbol) (term : Term Symbol) :
    Except Error (Option Int × Counts Symbol) :=
  ((rankAt graph order fuel compiled.root [] term 0 compiled.cache).map
    (fun (result, cache) => (result.map Prod.snd, cache))).mapError Error.execution

/-- Successful compilation records the exact nonempty language and a valid shared cache. -/
def Valid (meaning : FiniteMeaning graph) (invariant : Counts Symbol → Prop) (compiled : Compiled Symbol) : Prop :=
  compiled.count = (meaning.terms compiled.root).length ∧ 0 < compiled.count ∧ invariant compiled.cache

/-- Source compilation cannot return an empty or incorrectly counted ranked object. -/
theorem compile_valid [DecidableEq Symbol] [Ord Symbol] (graph : Graph Symbol) (meaning : FiniteMeaning graph)
    (invariant : Counts Symbol → Prop) (empty : invariant {})
    (sound : CountSound graph (fun node => (meaning.terms node).length) invariant)
    (fuel root : Nat) (compiled : Compiled Symbol) (success : compile graph fuel root = .ok compiled) :
    compiled.root = root ∧ Valid meaning invariant compiled := by
  cases counted : countNode graph fuel root {} with
  | error error => simp only [compile, counted, Except.mapError, Bind.bind, Except.bind] at success; cases success
  | ok pair =>
    rcases pair with ⟨count, cache⟩
    have correct := sound fuel root {} count cache empty counted
    simp only [compile, counted, Except.mapError, Bind.bind, Except.bind] at success
    split at success
    next nonpositive => cases success
    next positive =>
      cases success
      refine ⟨rfl, ?_, ?_, correct.2⟩
      · simp only [correct.1, Int.toNat_natCast]
      · change 0 < count.toNat
        omega

/-- Exact zero cardinality produces the source `EmptyRanked` error. -/
theorem compile_zero [DecidableEq Symbol] [Ord Symbol] (graph : Graph Symbol) (fuel root : Nat) (cache : Counts Symbol)
    (counted : countNode graph fuel root {} = .ok (0, cache)) : compile graph fuel root = .error .emptyRanked := by
  simp [compile, counted, Except.mapError]
  rfl

/-- Every semantically empty graph eventually takes the public empty-ranked branch. -/
theorem compile_empty_eventual [DecidableEq Symbol] [Ord Symbol] (graph : Graph Symbol) (meaning : FiniteMeaning graph)
    (invariant : Counts Symbol → Prop) (empty : invariant {})
    (sound : CountSound graph (fun node => (meaning.terms node).length) invariant)
    (countTotal : ∀ node state, Eventually (fun fuel => countNode graph fuel node) state)
    (root : Nat) (noTerms : meaning.terms root = []) :
    ∃ bound, ∀ fuel, bound ≤ fuel → compile graph fuel root = .error .emptyRanked := by
  obtain ⟨bound, cache, _, counted⟩ := count_eventual_exact graph meaning invariant sound countTotal root {} empty
  refine ⟨bound, ?_⟩
  intro fuel enough
  exact compile_zero graph fuel root cache (by simpa only [noTerms, List.length_nil, Int.natCast_zero] using counted fuel enough)

/-- Every nonempty graph eventually constructs its exact on-demand index and shared snapshot. -/
theorem compile_nonempty_eventual [DecidableEq Symbol] [Ord Symbol] (graph : Graph Symbol) (meaning : FiniteMeaning graph)
    (invariant : Counts Symbol → Prop) (empty : invariant {})
    (sound : CountSound graph (fun node => (meaning.terms node).length) invariant)
    (countTotal : ∀ node state, Eventually (fun fuel => countNode graph fuel node) state)
    (root : Nat) (nonempty : meaning.terms root ≠ []) :
    ∃ bound compiled, compiled.root = root ∧ Valid meaning invariant compiled ∧
      ∀ fuel, bound ≤ fuel → compile graph fuel root = .ok compiled := by
  obtain ⟨bound, cache, safe, counted⟩ := count_eventual_exact graph meaning invariant sound countTotal root {} empty
  have positive := List.length_pos_iff.mpr nonempty
  have nonpositive : ¬((meaning.terms root).length : Int) ≤ 0 := by omega
  refine ⟨bound, ⟨root, (meaning.terms root).length, cache⟩, rfl, ⟨rfl, positive, safe⟩, ?_⟩
  intro fuel enough
  simp only [compile, counted fuel enough, Except.mapError, Bind.bind, Except.bind, nonpositive, ↓reduceIte,
    Int.toNat_natCast]
  rfl

/-- Negative rank rejection occurs without evaluating the selected-term callback. -/
theorem select_negative [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (fuel : Nat) (compiled : Compiled Symbol) (rank : Int)
    (negative : rank < 0) : select graph order fuel compiled rank = .error (.negativeRank rank) := by
  simp [select, negative]

/-- An upper-bound failure is also checked before the selected-term callback. -/
theorem select_outOfRange [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (fuel : Nat) (compiled : Compiled Symbol) (rank : Int)
    (nonnegative : 0 ≤ rank) (tooLarge : (compiled.count : Int) ≤ rank) :
    select graph order fuel compiled rank = .error (.outOfRange rank compiled.count) := by
  simp [select, show ¬rank < 0 by omega, tooLarge]

/-- Every successful public decode is accepted and retains a valid shared cache. -/
theorem select_sound [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph)
    (invariant : Counts Symbol → Prop) (sound : CountSound graph (fun node => (meaning.terms node).length) invariant)
    (fuel : Nat) (compiled : Compiled Symbol) (valid : Valid meaning invariant compiled)
    (rank : Int) (term : Term Symbol) (cache : Counts Symbol)
    (success : select graph order fuel compiled rank = .ok (term, cache)) :
    0 ≤ rank ∧ rank < (compiled.count : Int) ∧ term ∈ meaning.terms compiled.root ∧ invariant cache := by
  unfold select at success
  split at success
  next negative => cases success
  next nonnegative =>
    split at success
    next tooLarge => cases success
    next inRange =>
      cases selected : selectAt graph order fuel compiled.root [] rank compiled.cache with
      | error error => simp only [selected, Except.map, Except.mapError] at success; cases success
      | ok pair =>
        rcases pair with ⟨⟨chosen, final, suffix⟩, after⟩
        simp only [selected, Except.map, Except.mapError, Except.ok.injEq, Prod.mk.injEq] at success
        rcases success with ⟨rfl, rfl⟩
        have checked := selected_root_exact graph order meaning invariant sound fuel compiled.root rank compiled.cache after
          chosen final suffix valid.2.2 (by omega) (by rw [← valid.1]; omega) selected
        exact ⟨by omega, by omega, checked.1, checked.2.2.2⟩

/-- Selection and inverse callbacks are exact inverses from the same compiled snapshot. -/
theorem select_inverse [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph)
    (invariant : Counts Symbol → Prop) (sound : CountSound graph (fun node => (meaning.terms node).length) invariant)
    (fuel : Nat) (compiled : Compiled Symbol) (valid : Valid meaning invariant compiled)
    (rank : Int) (term : Term Symbol) (cache : Counts Symbol)
    (success : select graph order fuel compiled rank = .ok (term, cache)) :
    inverse graph order fuel compiled term = .ok (some rank, cache) := by
  unfold select at success
  split at success
  next negative => cases success
  next nonnegative =>
    split at success
    next tooLarge => cases success
    next inRange =>
      cases selected : selectAt graph order fuel compiled.root [] rank compiled.cache with
      | error error => simp only [selected, Except.map, Except.mapError] at success; cases success
      | ok pair =>
        rcases pair with ⟨⟨chosen, final, suffix⟩, after⟩
        simp only [selected, Except.map, Except.mapError, Except.ok.injEq, Prod.mk.injEq] at success
        rcases success with ⟨rfl, rfl⟩
        have checked := selected_root_exact graph order meaning invariant sound fuel compiled.root rank compiled.cache after
          chosen final suffix valid.2.2 (by omega) (by rw [← valid.1]; omega) selected
        have ranked := ((decoder_inverse_mutual graph order fuel).1 compiled.root [] rank compiled.cache
          chosen final suffix after (by omega) selected).2 0
        simp only [checked.2.2.1, Int.zero_add, Int.sub_zero] at ranked
        simp [inverse, ranked, Except.map, Except.mapError]

/-- The successful compiled inverse never assigns an index to a nonmember. -/
theorem inverse_sound [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph)
    (invariant : Counts Symbol → Prop) (sound : CountSound graph (fun node => (meaning.terms node).length) invariant)
    (fuel : Nat) (compiled : Compiled Symbol) (valid : Valid meaning invariant compiled)
    (term : Term Symbol) (rank : Int) (cache : Counts Symbol)
    (success : inverse graph order fuel compiled term = .ok (some rank, cache)) :
    term ∈ meaning.terms compiled.root ∧ invariant cache := by
  cases ranked : rankAt graph order fuel compiled.root [] term 0 compiled.cache with
  | error error => simp only [inverse, ranked, Except.map, Except.mapError] at success; cases success
  | ok pair =>
    rcases pair with ⟨result, after⟩
    cases result with
    | none => simp only [inverse, ranked, Except.map, Except.mapError] at success; cases success
    | some pair =>
      rcases pair with ⟨final, value⟩
      simp only [inverse, ranked, Except.map, Except.mapError, Option.map_some, Except.ok.injEq, Prod.mk.injEq,
        Option.some.injEq] at success
      rcases success with ⟨rfl, rfl⟩
      have nonempty : meaning.terms compiled.root ≠ [] := by
        have positive := valid.2.1
        rw [valid.1] at positive
        exact List.ne_nil_of_length_pos positive
      have result := (ranking_meaning_mutual graph order meaning invariant sound fuel).1
        compiled.root [] term 0 compiled.cache final value after valid.2.2 nonempty (fun whole _ => ⟨whole, rfl⟩) ranked
      obtain ⟨whole, accepted⟩ := List.exists_mem_of_ne_nil _ result.2.2.1
      have same : whole = term := Option.some.inj (result.2.2.2 whole accepted)
      exact ⟨by simpa only [same] using result.2.1 whole accepted, result.1⟩

/-- Every valid compiled rank eventually returns an accepted term and a valid shared snapshot. -/
theorem select_eventual [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph)
    (invariant : Counts Symbol → Prop) (sound : CountSound graph (fun node => (meaning.terms node).length) invariant)
    (countTotal : ∀ node state, Eventually (fun fuel => countNode graph fuel node) state)
    (coverage : ConstructorCoverage graph order meaning) (compiled : Compiled Symbol) (valid : Valid meaning invariant compiled)
    (rank : Int) (nonnegative : 0 ≤ rank) (inRange : rank < (compiled.count : Int)) :
    ∃ bound term cache, term ∈ meaning.terms compiled.root ∧ invariant cache ∧
      ∀ fuel, bound ≤ fuel → select graph order fuel compiled rank = .ok (term, cache) := by
  have bounded : SubtreeHeight meaning compiled.root [] (forestHeight (meaning.terms compiled.root)) := by
    intro whole member part located
    have same := Option.some.inj located
    subst part
    exact height_le_forestHeight _ whole member
  obtain ⟨bound, ⟨term, final, suffix⟩, cache, selected⟩ := selectAt_eventual graph order meaning invariant sound countTotal coverage
    (forestHeight (meaning.terms compiled.root)) compiled.root [] rank compiled.cache valid.2.2 nonnegative
    (by rw [← valid.1]; exact inRange) (fun whole _ => ⟨whole, rfl⟩) bounded
  dsimp only at selected
  have checked := selected_root_exact graph order meaning invariant sound bound compiled.root rank compiled.cache cache
    term final suffix valid.2.2 nonnegative (by rw [← valid.1]; exact inRange) (selected bound (Nat.le_refl _))
  refine ⟨bound, term, cache, checked.1, checked.2.2.2, ?_⟩
  intro fuel enough
  simp [select, show ¬rank < 0 by omega, show ¬(compiled.count : Int) ≤ rank by omega,
    selected fuel enough, Except.map, Except.mapError]

/-- The compiled inverse terminates for every finite input and preserves its shared count cache. -/
theorem inverse_eventual [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph)
    (invariant : Counts Symbol → Prop) (sound : CountSound graph (fun node => (meaning.terms node).length) invariant)
    (countTotal : ∀ node state, Eventually (fun fuel => countNode graph fuel node) state)
    (coverage : ConstructorCoverage graph order meaning) (compiled : Compiled Symbol) (valid : Valid meaning invariant compiled)
    (term : Term Symbol) :
    ∃ bound answer cache, invariant cache ∧ ∀ fuel, bound ≤ fuel → inverse graph order fuel compiled term = .ok (answer, cache) := by
  obtain ⟨bound, result, cache, ranked⟩ := rankAt_eventual graph order meaning invariant sound countTotal coverage
    term compiled.root [] 0 compiled.cache valid.2.2
  dsimp only at ranked
  have safe := (ranking_preserves graph order (fun node => (meaning.terms node).length) invariant sound bound).1
    compiled.root [] term 0 compiled.cache result cache valid.2.2 (ranked bound (Nat.le_refl _))
  refine ⟨bound, result.map Prod.snd, cache, safe, ?_⟩
  intro fuel enough
  simp [inverse, ranked fuel enough, Except.map, Except.mapError]

/-- Reading the shared compiled snapshot gives the same inverse answer as the verified empty-cache wrapper. -/
theorem inverse_agrees [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph)
    (invariant : Counts Symbol → Prop) (empty : invariant {})
    (sound : CountSound graph (fun node => (meaning.terms node).length) invariant)
    (fuel : Nat) (compiled : Compiled Symbol) (valid : Valid meaning invariant compiled) (term : Term Symbol)
    (reference answer : Option Int) (cache : Counts Symbol)
    (referenceRun : rankOf graph order fuel compiled.root term = .ok reference)
    (success : inverse graph order fuel compiled term = .ok (answer, cache)) : answer = reference := by
  cases counted : countNode graph fuel compiled.root {} with
  | error error => simp only [rankOf, counted, Bind.bind, Except.bind] at referenceRun; cases referenceRun
  | ok pair =>
    rcases pair with ⟨count, middle⟩
    have safe := (sound fuel compiled.root {} count middle empty counted).2
    cases first : rankAt graph order fuel compiled.root [] term 0 middle with
    | error error => simp only [rankOf, counted, first, Bind.bind, Except.bind] at referenceRun; cases referenceRun
    | ok pair =>
      rcases pair with ⟨firstAnswer, firstCache⟩
      cases second : rankAt graph order fuel compiled.root [] term 0 compiled.cache with
      | error error => simp only [inverse, second, Except.map, Except.mapError] at success; cases success
      | ok pair =>
        rcases pair with ⟨secondAnswer, secondCache⟩
        have same := ((ranking_cacheLaw graph order (fun node => (meaning.terms node).length) invariant sound fuel).1
          compiled.root [] term 0).observes compiled.cache middle secondAnswer firstAnswer secondCache firstCache
          valid.2.2 safe second first
        simp only [rankOf, counted, first, Bind.bind, Except.bind, Pure.pure, Except.pure, Except.ok.injEq] at referenceRun
        simp only [inverse, second, Except.map, Except.mapError, Except.ok.injEq, Prod.mk.injEq] at success
        exact success.1.symm.trans ((congrArg (Option.map Prod.snd) same).trans referenceRun)

/-- Actual shared-cache selection agrees with the verified public decoder on every completed call. -/
theorem select_agrees [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph)
    (invariant : Counts Symbol → Prop) (empty : invariant {})
    (sound : CountSound graph (fun node => (meaning.terms node).length) invariant)
    (fuel : Nat) (compiled : Compiled Symbol) (valid : Valid meaning invariant compiled) (rank : Int)
    (reference answer : Term Symbol) (cache : Counts Symbol)
    (referenceRun : unrank graph order fuel compiled.root rank = .ok reference)
    (success : select graph order fuel compiled rank = .ok (answer, cache)) : answer = reference := by
  cases counted : countNode graph fuel compiled.root {} with
  | error error => simp only [unrank, counted, Bind.bind, Except.bind] at referenceRun; cases referenceRun
  | ok pair =>
    rcases pair with ⟨count, middle⟩
    have safe := (sound fuel compiled.root {} count middle empty counted).2
    simp only [unrank, counted, Bind.bind, Except.bind] at referenceRun
    split at referenceRun
    next invalid => cases referenceRun
    next checked =>
      cases first : selectAt graph order fuel compiled.root [] rank middle with
      | error error => simp only [first] at referenceRun; cases referenceRun
      | ok pair =>
        rcases pair with ⟨firstAnswer, firstCache⟩
        unfold select at success
        split at success
        next negative => cases success
        next nonnegative =>
          split at success
          next tooLarge => cases success
          next inRange =>
            cases second : selectAt graph order fuel compiled.root [] rank compiled.cache with
            | error error => simp only [second, Except.map, Except.mapError] at success; cases success
            | ok pair =>
              rcases pair with ⟨secondAnswer, secondCache⟩
              have same := ((selection_cacheLaw graph order (fun node => (meaning.terms node).length) invariant sound fuel).1
                compiled.root [] rank).observes compiled.cache middle secondAnswer firstAnswer secondCache firstCache
                valid.2.2 safe second first
              simp only [first, Pure.pure, Except.pure, Except.ok.injEq] at referenceRun
              simp only [second, Except.map, Except.mapError, Except.ok.injEq, Prod.mk.injEq] at success
              exact success.1.symm.trans ((congrArg Prod.fst same).trans referenceRun)

/-- The actual shared-cache inverse eventually rejects every nonmember of a compiled source. -/
theorem inverse_eventually_rejects [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph)
    (invariant : Counts Symbol → Prop) (empty : invariant {})
    (sound : CountSound graph (fun node => (meaning.terms node).length) invariant)
    (countTotal : ∀ node state, Eventually (fun fuel => countNode graph fuel node) state)
    (coverage : ConstructorCoverage graph order meaning) (rootExact : RootProjectionExact graph meaning)
    (compiled : Compiled Symbol) (valid : Valid meaning invariant compiled)
    (term : Term Symbol) (absent : term ∉ meaning.terms compiled.root) :
    ∃ bound cache, invariant cache ∧ ∀ fuel, bound ≤ fuel → inverse graph order fuel compiled term = .ok (none, cache) := by
  obtain ⟨sourceBound, answer, cache, safe, actual⟩ := inverse_eventual graph order meaning invariant sound countTotal coverage compiled valid term
  obtain ⟨referenceBound, reference⟩ := rankOf_eventually_rejects graph order meaning invariant empty sound countTotal coverage
    rootExact compiled.root term absent
  have same := inverse_agrees graph order meaning invariant empty sound (max sourceBound referenceBound) compiled valid term none answer cache
    (reference _ (Nat.le_max_right _ _)) (actual _ (Nat.le_max_left _ _))
  exact ⟨sourceBound, cache, safe, fun fuel enough => by simpa only [same] using actual fuel enough⟩

end MicroCFTA.SymbolicPublicAdapter
