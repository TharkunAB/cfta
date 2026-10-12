import MicroCFTA.RecursiveNaryCandidates

/-!
# Source equations for the terminating n-ary inverse

A body requests only forests no taller than its input forest. Each private
recursive root reduces that height. Additional fuel therefore changes no
candidate row, including false flags and their original order.
-/
namespace MicroCFTA.RecursiveNaryCausality
open Language GeneratorCombinators IntegerTermViews SizedRank
open RecursiveCallbackTermination RecursiveCallbackTables
open RecursiveNaryFields RecursiveNaryInverse

/-- Equal counts and equal callbacks for all requests below one height. -/
def Agree (limit : Nat) (left right : Finite Symbol) : Prop :=
  left.counts = right.counts ∧ ∀ view wanted, forestHeight wanted ≤ limit →
    left.positions view wanted = right.positions view wanted

/-- The two local expressions have the same source operations and related leaves. -/
inductive Related (limit : Nat) : Recipe Symbol → Recipe Symbol → Prop where
  | finite (left right : Finite Symbol) : Agree limit left right → Related limit (.finite left) (.finite right)
  | occurrence : Related limit .occurrence .occurrence
  | map : Related limit left right → Related limit (.map left) (.map right)
  | pay : Related limit left right → Related limit (.pay left) (.pay right)
  | choice : Related limit al ar → Related limit bl br → Related limit (.choice al bl) (.choice ar br)
  | ap : Related limit fl fr → Related limit al ar → Related limit (.ap fl al) (.ap fr ar)
  | label (symbol : Symbol) : Related limit left right → Related limit (.label symbol left) (.label symbol right)

/-- Related local expressions use exactly the same source count functions. -/
theorem counts_same {left right : Recipe Symbol} (same : Related limit left right) :
    counts (fun _ => 0) left = counts (fun _ => 0) right := by
  induction same with
  | finite left right same => exact same.1
  | occurrence => rfl
  | map _ ih => exact ih
  | pay _ ih | label _ _ ih => funext size; cases size <;> simp [counts, ih]
  | choice _ _ ihl ihr => funext size; simp [counts, ihl, ihr]
  | ap _ _ ihf iha => funext size; simp [counts, ihf, iha]

/-- Local callback operations read only requests below their input forest height. -/
theorem callbacks_same [DecidableEq Symbol] {left right : Recipe Symbol} (same : Related limit left right)
    (view : View) (wanted : List (EngineTerm Symbol)) (bound : forestHeight wanted ≤ limit) :
    RecursiveCallbackTermination.positions (fun _ => 0) RecursiveFieldCombinators.emptyBody left view wanted =
      RecursiveCallbackTermination.positions (fun _ => 0) RecursiveFieldCombinators.emptyBody right view wanted := by
  induction same generalizing view wanted with
  | finite left right same => simpa only [RecursiveCallbackTermination.positions] using same.2 view wanted bound
  | occurrence => rfl
  | map same ih => simp only [RecursiveCallbackTermination.positions]; exact ih view wanted bound
  | pay same ih => simp only [RecursiveCallbackTermination.positions]; rw [ih view wanted bound]
  | @choice al ar bl br first second ihl ihr =>
      have lc := counts_same first
      have rc := counts_same second
      cases view with
      | labelled => simp only [RecursiveCallbackTermination.positions]; rw [ihl _ _ bound, ihr _ _ bound, lc, rc]
      | whole | spine =>
          conv =>
            lhs
            rw [RecursiveCallbackTermination.positions.eq_def]
          conv =>
            rhs
            rw [RecursiveCallbackTermination.positions.eq_def]
          dsimp only
          split
          · rename_i child
            rw [ihl .whole [child] (by simp_all [forestHeight, Term.height]; omega)]
          · rename_i child
            rw [ihr .whole [child] (by simp_all [forestHeight, Term.height]; omega), lc, rc]
          · rfl
  | @ap fl fr al ar first second ihf iha =>
      have fc := counts_same first
      have ac := counts_same second
      cases view with
      | whole =>
          conv =>
            lhs
            rw [RecursiveCallbackTermination.positions.eq_def]
          conv =>
            rhs
            rw [RecursiveCallbackTermination.positions.eq_def]
          dsimp only
          split
          · rename_i function argument
            rw [ihf .whole [function] (by simp_all [forestHeight, Term.height]; omega),
              iha .whole [argument] (by simp_all [forestHeight, Term.height]; omega), fc, ac]
          · rfl
      | spine | labelled =>
          conv =>
            lhs
            rw [RecursiveCallbackTermination.positions.eq_def]
          conv =>
            rhs
            rw [RecursiveCallbackTermination.positions.eq_def]
          dsimp only
          split
          · rfl
          · rename_i argument found
            have small : forestHeight ([argument] : List (EngineTerm Symbol)) ≤ limit := by
              have within := last_height wanted argument found
              simpa only [forestHeight, List.foldr_cons, List.foldr_nil, Nat.max_zero] using Nat.le_trans within bound
            rw [ihf .spine wanted.dropLast (Nat.le_trans (dropLast_height wanted) bound), iha .whole [argument] small, fc, ac]
  | label symbol same ih =>
      conv =>
        lhs
        rw [RecursiveCallbackTermination.positions.eq_def]
      conv =>
        rhs
        rw [RecursiveCallbackTermination.positions.eq_def]
      dsimp only
      split
      · rename_i found children
        split
        · rw [ih .labelled children (by simp_all [forestHeight, Term.height]; omega)]
        · rfl
      · rfl

/-- The local field constructor preserves restricted callback agreement. -/
theorem local_fields [DecidableEq Symbol] {left right : Recipe Symbol} (same : Related limit left right) :
    Agree limit (RecursiveFieldCombinators.field left) (RecursiveFieldCombinators.field right) :=
  ⟨counts_same same, callbacks_same same⟩

/-- Pairwise field agreement preserves the complete list of source count functions. -/
theorem child_counts {left right : List (Finite Symbol)} (same : RecursiveRankMass.Related (Agree limit) left right) :
    RecursiveNaryChoice.childCounts left = RecursiveNaryChoice.childCounts right := by
  induction same with
  | nil => rfl
  | cons fields remaining ih => simp only [RecursiveNaryChoice.childCounts, List.map_cons] at *; rw [fields.1, ih]

/-- Pairwise related lists have the same length and the same valid branch numbers. -/
theorem related_length (same : RecursiveRankMass.Related relation left right) : left.length = right.length := by
  induction same with
  | nil => rfl
  | cons fields remaining ih => simp [ih]

/-- A branch lookup retains the corresponding child relation. -/
theorem related_lookup {relation : α → β → Prop} {left : List α} {right : List β} (same : RecursiveRankMass.Related relation left right) (branch : Nat) :
    match left[branch]?, right[branch]? with
    | some a, some b => relation a b
    | none, none => True
    | _, _ => False := by
  induction same generalizing branch with
  | nil => simp
  | cons fields remaining ih => cases branch with
      | zero => exact fields
      | succ branch => exact ih branch

/-- Branch adaptation reads only the requested child view. -/
theorem branch_rows {left right : List (Finite Symbol)} (same : RecursiveRankMass.Related (Agree limit) left right)
    (branch : Nat) (view : View) (wanted : List (EngineTerm Symbol)) (bound : forestHeight wanted ≤ limit) :
    RecursiveNaryChoice.branchRows left branch view wanted = RecursiveNaryChoice.branchRows right branch view wanted := by
  have related := related_lookup same branch
  have counts := child_counts same
  cases first : left[branch]? with
  | none =>
      cases second : right[branch]? with
      | none => simp [RecursiveNaryChoice.branchRows, first, second]
      | some child => simp [first, second] at related
  | some child =>
      cases second : right[branch]? with
      | none => simp [first, second] at related
      | some other =>
          simp only [first, second] at related
          simp only [RecursiveNaryChoice.branchRows, first, second]
          rw [related.2 view wanted bound]
          simp only [RecursiveNaryChoice.offset, counts]

/-- Whole choice requests read a strictly smaller child forest. -/
theorem whole_rows {left right : List (Finite Symbol)} (same : RecursiveRankMass.Related (Agree limit) left right)
    (wanted : List (EngineTerm Symbol)) (bound : forestHeight wanted ≤ limit) :
    RecursiveNaryChoice.wholeRows left wanted = RecursiveNaryChoice.wholeRows right wanted := by
  unfold RecursiveNaryChoice.wholeRows
  split
  · rename_i branch child
    exact branch_rows same branch .whole [child] (by simp_all [forestHeight, Term.height]; omega)
  · rfl

/-- A flat source choice preserves every row and checked flag below the request bound. -/
theorem choice_fields {left right : List (Finite Symbol)} (same : RecursiveRankMass.Related (Agree limit) left right) :
    Agree limit (RecursiveNaryChoice.field left) (RecursiveNaryChoice.field right) := by
  constructor
  · funext size
    have counts := congrArg (List.map fun (count : Nat → Nat) => count size) (child_counts same)
    simpa only [RecursiveNaryChoice.field, RecursiveNaryChoice.count, RecursiveNaryChoice.childCounts,
      List.map_map, Function.comp_def] using congrArg List.sum counts
  · intro view wanted bound
    cases view with
    | whole | spine => simp only [RecursiveNaryChoice.field, RecursiveNaryChoice.positions]; rw [whole_rows same wanted bound]
    | labelled =>
        simp only [RecursiveNaryChoice.field, RecursiveNaryChoice.positions, RecursiveNaryChoice.labelledRows]
        rw [related_length same]
        congr 1
        apply congrArg List.flatten
        apply List.map_congr_left
        intro branch _
        exact branch_rows same branch .labelled wanted bound

/-- Typed body compilation preserves restricted root callback agreement. -/
theorem compiled_agree [DecidableEq Symbol] (callbacks : LeafCallbacks Symbol)
    (same : Agree limit left right) (recipe : Body Root Symbol Value) :
    Agree limit (compile callbacks left recipe) (compile callbacks right recipe) := by
  induction recipe with
  | finite source => exact ⟨rfl, fun _ _ _ => rfl⟩
  | occurrence => exact same
  | map transform inner ih => exact ih
  | pay inner ih => exact local_fields (.pay (.finite _ _ ih))
  | label symbol inner ih => exact local_fields (.label symbol (.finite _ _ ih))
  | ap functions arguments ihf iha => exact local_fields (.ap (.finite _ _ ihf) (.finite _ _ iha))
  | choice count branches ih =>
      apply choice_fields
      have related : ∀ keys : List (Fin count), RecursiveRankMass.Related (Agree limit)
          (keys.map fun index => compile callbacks left (branches index))
          (keys.map fun index => compile callbacks right (branches index)) := by
        intro keys
        induction keys with
        | nil => exact .nil
        | cons key rest tail => exact .cons (ih key) tail
      simpa only [List.map_ofFn, Function.comp_def, id_eq] using related (List.ofFn id)

/-- A height-zero forest cannot contain a complete private recursive root. -/
theorem unwrap_zero (wanted : List (EngineTerm Symbol)) (bound : forestHeight wanted ≤ 0) :
    unwrap wanted = none := by
  cases found : unwrap wanted with
  | none => rfl
  | some child =>
      have same := (unwrap_some wanted child).mp found
      subst wanted
      simp [forestHeight, Term.height] at bound

/-- Once fuel covers the input forest, every source row and flag is stable. -/
theorem fuel_stable [DecidableEq Symbol] (callbacks : LeafCallbacks Symbol) (body : Body Root Symbol Root)
    (first second : Nat) (view : View) (wanted : List (EngineTerm Symbol))
    (firstEnough : forestHeight wanted ≤ first) (secondEnough : forestHeight wanted ≤ second) :
    fuelPositions callbacks body first view wanted = fuelPositions callbacks body second view wanted := by
  induction first generalizing second view wanted with
  | zero =>
      have absent := unwrap_zero wanted firstEnough
      cases second <;> simp [fuelPositions, absent]
  | succ first ih =>
      cases second with
      | zero =>
          have absent := unwrap_zero wanted secondEnough
          simp [fuelPositions, absent]
      | succ second =>
          cases found : unwrap wanted with
          | none => simp [fuelPositions, found]
          | some child =>
              have same := (unwrap_some wanted child).mp found
              subst wanted
              have smallFirst : forestHeight ([child] : List (EngineTerm Symbol)) ≤ first := by
                simp_all [forestHeight, Term.height]
              have smallSecond : forestHeight ([child] : List (EngineTerm Symbol)) ≤ second := by
                simp_all [forestHeight, Term.height]
              have roots : Agree (forestHeight [child])
                  (rootField body (fuelPositions callbacks body first))
                  (rootField body (fuelPositions callbacks body second)) := by
                refine ⟨rfl, ?_⟩
                intro childView requested small
                exact ih second childView requested (Nat.le_trans small smallFirst) (Nat.le_trans small smallSecond)
              exact (compiled_agree callbacks roots body).2 .whole [child] (Nat.le_refl _)

/-- The terminating inverse satisfies the source callback equation with no fuel parameter. -/
theorem positions_equation [DecidableEq Symbol] (callbacks : LeafCallbacks Symbol) (body : Body Root Symbol Root)
    (view : View) (wanted : List (EngineTerm Symbol)) :
    RecursiveNaryInverse.positions callbacks body view wanted =
      match unwrap wanted with
      | none => []
      | some child => (compile callbacks (rootField body (RecursiveNaryInverse.positions callbacks body)) body).positions .whole [child] := by
  cases found : unwrap wanted with
  | none =>
      change fuelPositions callbacks body (forestHeight wanted) view wanted = _
      cases height : forestHeight wanted <;> simp [fuelPositions, found]
  | some child =>
      have same := (unwrap_some wanted child).mp found
      subst wanted
      have roots : Agree child.height
          (rootField body (fuelPositions callbacks body child.height))
          (rootField body (RecursiveNaryInverse.positions callbacks body)) := by
        refine ⟨rfl, ?_⟩
        intro childView requested small
        exact fuel_stable callbacks body child.height (forestHeight requested) childView requested small (Nat.le_refl _)
      have step := (compiled_agree callbacks roots body).2 .whole [child]
        (by simp [forestHeight])
      simpa only [RecursiveNaryInverse.positions, forestHeight, Term.height, List.foldr_cons,
        List.foldr_nil, Nat.max_zero, fuelPositions, unwrap] using step

/-- A complete recursive term enters the original body callback in every view. -/
theorem positions_root [DecidableEq Symbol] (callbacks : LeafCallbacks Symbol) (body : Body Root Symbol Root)
    (view : View) (child : EngineTerm Symbol) :
    RecursiveNaryInverse.positions callbacks body view [.node .recursion [child]] =
      (compile callbacks (rootField body (RecursiveNaryInverse.positions callbacks body)) body).positions .whole [child] := by
  rw [positions_equation]
  rfl

/-- A malformed recursive view produces no source candidate rows. -/
theorem positions_rejects [DecidableEq Symbol] (callbacks : LeafCallbacks Symbol) (body : Body Root Symbol Root)
    (view : View) (wanted : List (EngineTerm Symbol)) (absent : unwrap wanted = none) :
    RecursiveNaryInverse.positions callbacks body view wanted = [] := by
  rw [positions_equation, absent]

end MicroCFTA.RecursiveNaryCausality
