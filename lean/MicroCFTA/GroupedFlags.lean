import MicroCFTA.OccurrenceGuard
import MicroCFTA.Productivity

/-!
# Closed occurrence flags of a recursive key family

`recurGrouped.closedIndexes` rebuilds the fixed key family with each key's
previous occurrence flags and its settled minimum. The three token sets
propagate monotonically through standard metadata operations. A finite key
and token domain therefore makes the equality-stopping loop terminate.
-/

namespace MicroCFTA.GroupedFlags
open MinimumSize Productivity

/-- The source keeps size-unguarded, termless, and used token sets separately. -/
inductive Kind where
  | unguarded | termless | used
  deriving DecidableEq, Repr

/-- A finite key/token/flag position in the source metadata table. -/
abbrev Slot (Key Token : Type) := Key × Token × Kind

/-- Standard metadata operations with explicit fixed source flags. -/
inductive Expression (Key Token : Type) where
  | source (minimum : Option Nat) (flags : Token → Kind → Bool)
  | occurrence (key : Key)
  | map (inner : Expression Key Token)
  | pay (inner : Expression Key Token)
  | constructor (inner : Expression Key Token)
  | choice (left right : Expression Key Token)
  | product (left right : Expression Key Token)

/-- Each occurrence receives its settled minimum independently of the changing flag table. -/
def minimum : Expression Key Token → (Key → Option Nat) → Option Nat
  | .source value _, _ => value
  | .occurrence key, settled => settled key
  | .map inner, settled => minimum inner settled
  | .pay inner, settled | .constructor inner, settled => (minimum inner settled).map (· + 1)
  | .choice left right, settled => best (minimum left settled) (minimum right settled)
  | .product left right, settled => RecursionProbe.productMinimum (minimum left settled) (minimum right settled)

/-- Evaluate the actual three occurrence-set operations at one token. -/
def evaluate : Expression Key Token → (Key → Option Nat) → (Slot Key Token → Bool) → Token → Kind → Bool
  | .source _ flags, _, _, token, kind => flags token kind
  | .occurrence key, _, previous, token, kind => previous (key, token, kind)
  | .map inner, settled, previous, token, kind => evaluate inner settled previous token kind
  | .pay inner, settled, previous, token, kind => match kind with
    | .unguarded => false
    | .termless | .used => evaluate inner settled previous token kind
  | .constructor inner, settled, previous, token, kind => match kind with
    | .unguarded | .termless => false
    | .used => evaluate inner settled previous token kind
  | .choice left right, settled, previous, token, kind =>
      evaluate left settled previous token kind || evaluate right settled previous token kind
  | .product left right, settled, previous, token, kind => match kind with
    | .unguarded =>
        (decide (minimum right settled = some 0) && evaluate left settled previous token .unguarded) ||
        (decide (minimum left settled = some 0) && evaluate right settled previous token .unguarded)
    | .termless => false
    | .used => evaluate left settled previous token .used || evaluate right settled previous token .used

/-- Adding prior flags cannot remove any flag produced by a standard body expression. -/
theorem evaluate_monotone (expression : Expression Key Token) (settled : Key → Option Nat)
    (before after : Slot Key Token → Bool) (included : Included before after) (token : Token) (kind : Kind) :
    evaluate expression settled before token kind = true → evaluate expression settled after token kind = true := by
  induction expression generalizing kind with
  | source minimum flags => exact id
  | occurrence key => exact included (key, token, kind)
  | map inner ih => exact ih kind
  | pay inner ih => cases kind <;> simp only [evaluate] <;> first | exact ih _ | exact id
  | constructor inner ih => cases kind <;> simp only [evaluate] <;> first | exact ih _ | exact id
  | choice left right ihl ihr =>
      simp only [evaluate, Bool.or_eq_true_iff]
      exact fun accepted => accepted.elim (fun h => Or.inl (ihl kind h)) (fun h => Or.inr (ihr kind h))
  | product left right ihl ihr =>
      cases kind with
      | termless => exact id
      | used =>
          simp only [evaluate, Bool.or_eq_true_iff]
          exact fun accepted => accepted.elim (fun h => Or.inl (ihl .used h)) (fun h => Or.inr (ihr .used h))
      | unguarded =>
          simp only [evaluate, Bool.or_eq_true_iff, Bool.and_eq_true_iff]
          exact fun accepted => accepted.elim (fun h => Or.inl ⟨h.1, ihl .unguarded h.2⟩)
            (fun h => Or.inr ⟨h.1, ihr .unguarded h.2⟩)

/-- One fixed-key body rebuild reads the preceding flag table. -/
def step (program : Key → Expression Key Token) (settled : Key → Option Nat)
    (previous : Slot Key Token → Bool) : Slot Key Token → Bool :=
  fun (key, token, kind) => evaluate (program key) settled previous token kind

/-- The concrete body rebuild preserves inclusion of every token set. -/
theorem step_monotone (program : Key → Expression Key Token) (settled : Key → Option Nat) :
    Monotone (step program settled) := by
  intro before after included slot
  exact evaluate_monotone (program slot.1) settled before after included slot.2.1 slot.2.2

/-- The complete finite slot domain compares all three flags at every key and enclosing token. -/
def slots (keys : List Key) (tokens : List Token) : List (Slot Key Token) :=
  keys.flatMap fun key => tokens.flatMap fun token => [(.unguarded : Kind), .termless, .used].map fun kind => (key, token, kind)

/-- Complete key and token lists give a complete flag-table comparison domain. -/
theorem slots_complete (keys : List Key) (tokens : List Token)
    (allKeys : ∀ key, key ∈ keys) (allTokens : ∀ token, token ∈ tokens) : ∀ slot, slot ∈ slots keys tokens := by
  rintro ⟨key, token, kind⟩
  simp only [slots, List.mem_flatMap, List.mem_map]
  refine ⟨key, allKeys key, token, allTokens token, kind, ?_, rfl⟩
  cases kind <;> simp

/-- Compare the source's occurrence sets extensionally over the complete finite domain. -/
def same (domain : List (Slot Key Token)) (left right : Slot Key Token → Bool) : Bool :=
  domain.all (fun slot => left slot == right slot)

/-- Equality of all finite flags is equality of the whole occurrence table. -/
theorem same_correct (domain : List (Slot Key Token)) (complete : ∀ slot, slot ∈ domain)
    (left right : Slot Key Token → Bool) : same domain left right = true ↔ left = right := by
  constructor
  · intro equal
    funext slot
    exact of_decide_eq_true (List.all_eq_true.mp equal slot (complete slot))
  · intro equal
    subst right
    simp [same]

/-- The source's equality-stopping loop terminates because each changed pass adds a flag. -/
def converge (domain : List (Slot Key Token)) (complete : ∀ slot, slot ∈ domain)
    (program : Key → Expression Key Token) (settled : Key → Option Nat)
    (known : Slot Key Token → Bool) (growing : Included known (step program settled known)) : Slot Key Token → Bool :=
  let built := step program settled known
  if _stable : same domain built known = true then built
  else converge domain complete program settled built (step_monotone program settled known built growing)
termination_by domain.length - domain.countP known
decreasing_by
  have different : known ≠ step program settled known := by
    intro equal
    exact _stable ((same_correct domain complete _ _).mpr equal.symm)
  have strict := count_strict_of_ne domain complete known (step program settled known) growing different
  have bounded := List.countP_le_length (p := step program settled known) (l := domain)
  omega

/-- The actual loop returns a table stable under one complete body rebuild. -/
theorem converge_fixed (domain : List (Slot Key Token)) (complete : ∀ slot, slot ∈ domain)
    (program : Key → Expression Key Token) (settled : Key → Option Nat)
    (known : Slot Key Token → Bool) (growing : Included known (step program settled known)) :
    step program settled (converge domain complete program settled known growing) =
      converge domain complete program settled known growing := by
  induction known, growing using converge.induct domain complete program settled with
  | case1 known growing built stable =>
      dsimp only [built] at stable
      have fixed := (same_correct domain complete _ _).mp stable
      rw [converge.eq_def]
      simp only [dite_eq_left stable]
      rw [fixed]
      exact fixed
  | case2 known growing built unstable ih =>
      dsimp only [built] at unstable
      rw [converge.eq_def]
      simpa only [dite_eq_right unstable] using ih

/-- Starting with no outer flags computes the source's closed occurrence table. -/
def close (keys : List Key) (tokens : List Token) (allKeys : ∀ key, key ∈ keys) (allTokens : ∀ token, token ∈ tokens)
    (program : Key → Expression Key Token) (settled : Key → Option Nat) : Slot Key Token → Bool :=
  converge (slots keys tokens) (slots_complete keys tokens allKeys allTokens) program settled (fun _ => false)
    (by intro slot present; contradiction)

/-- Every enclosing occurrence propagated by the final body remains present in the closed key table. -/
theorem close_fixed (keys : List Key) (tokens : List Token) (allKeys : ∀ key, key ∈ keys) (allTokens : ∀ token, token ∈ tokens)
    (program : Key → Expression Key Token) (settled : Key → Option Nat) :
    step program settled (close keys tokens allKeys allTokens program settled) =
      close keys tokens allKeys allTokens program settled :=
  converge_fixed _ _ _ _ _ _

/-- Convergence remains inside every closed table that includes its initial flags. -/
theorem converge_least (domain : List (Slot Key Token)) (complete : ∀ slot, slot ∈ domain)
    (program : Key → Expression Key Token) (settled : Key → Option Nat)
    (upper known : Slot Key Token → Bool) (growing : Included known (step program settled known))
    (bounded : Included known upper) (closed : Included (step program settled upper) upper) :
    Included (converge domain complete program settled known growing) upper := by
  induction known, growing using converge.induct domain complete program settled with
  | case1 known growing built stable =>
      dsimp only [built] at stable
      rw [converge.eq_def]
      simp only [dite_eq_left stable]
      exact fun slot member => closed slot (step_monotone program settled known upper bounded slot member)
  | case2 known growing built unstable ih =>
      dsimp only [built] at unstable
      rw [converge.eq_def]
      simp only [dite_eq_right unstable]
      exact ih (fun slot member => closed slot (step_monotone program settled known upper bounded slot member))

/-- The closed table is the least solution, so stable but unsupported outer flags are not invented. -/
theorem close_least (keys : List Key) (tokens : List Token) (allKeys : ∀ key, key ∈ keys) (allTokens : ∀ token, token ∈ tokens)
    (program : Key → Expression Key Token) (settled : Key → Option Nat) (upper : Slot Key Token → Bool)
    (fixed : step program settled upper = upper) : Included (close keys tokens allKeys allTokens program settled) upper := by
  apply converge_least
  · intro slot present
    contradiction
  · intro slot present
    simpa only [fixed] using present

/-- An independent finite derivation records which source operation transmits an enclosing token flag. -/
inductive Derives (program : Key → Expression Key Token) (settled : Key → Option Nat) : Expression Key Token → Token → Kind → Prop where
  | source (minimum : Option Nat) (flags : Token → Kind → Bool) (token : Token) (kind : Kind)
      (present : flags token kind = true) : Derives program settled (.source minimum flags) token kind
  | occurrence (key : Key) (token : Token) (kind : Kind) (inner : Derives program settled (program key) token kind) :
      Derives program settled (.occurrence key) token kind
  | map (inner : Expression Key Token) (token : Token) (kind : Kind) (child : Derives program settled inner token kind) :
      Derives program settled (.map inner) token kind
  | payTermless (inner : Expression Key Token) (token : Token) (child : Derives program settled inner token .termless) :
      Derives program settled (.pay inner) token .termless
  | payUsed (inner : Expression Key Token) (token : Token) (child : Derives program settled inner token .used) :
      Derives program settled (.pay inner) token .used
  | constructorUsed (inner : Expression Key Token) (token : Token) (child : Derives program settled inner token .used) :
      Derives program settled (.constructor inner) token .used
  | left (left right : Expression Key Token) (token : Token) (kind : Kind) (child : Derives program settled left token kind) :
      Derives program settled (.choice left right) token kind
  | right (left right : Expression Key Token) (token : Token) (kind : Kind) (child : Derives program settled right token kind) :
      Derives program settled (.choice left right) token kind
  | productUsedLeft (left right : Expression Key Token) (token : Token) (child : Derives program settled left token .used) :
      Derives program settled (.product left right) token .used
  | productUsedRight (left right : Expression Key Token) (token : Token) (child : Derives program settled right token .used) :
      Derives program settled (.product left right) token .used
  | productUnguardedLeft (left right : Expression Key Token) (token : Token)
      (zero : minimum right settled = some 0) (child : Derives program settled left token .unguarded) :
      Derives program settled (.product left right) token .unguarded
  | productUnguardedRight (left right : Expression Key Token) (token : Token)
      (zero : minimum left settled = some 0) (child : Derives program settled right token .unguarded) :
      Derives program settled (.product left right) token .unguarded

/-- Every stored flag has a finite source propagation derivation. -/
def Sound (program : Key → Expression Key Token) (settled : Key → Option Nat) (known : Slot Key Token → Bool) : Prop :=
  ∀ slot, known slot = true → Derives program settled (program slot.1) slot.2.1 slot.2.2

/-- Body evaluation constructs a propagation derivation for each reported flag. -/
theorem evaluate_sound (program : Key → Expression Key Token) (settled : Key → Option Nat)
    (known : Slot Key Token → Bool) (sound : Sound program settled known)
    (expression : Expression Key Token) (token : Token) (kind : Kind)
    (present : evaluate expression settled known token kind = true) : Derives program settled expression token kind := by
  induction expression generalizing kind with
  | source minimum flags => exact .source minimum flags token kind present
  | occurrence key => exact .occurrence key token kind (sound (key, token, kind) present)
  | map inner ih => exact .map inner token kind (ih kind present)
  | pay inner ih =>
      cases kind with
      | unguarded => simp [evaluate] at present
      | termless => exact .payTermless inner token (ih .termless present)
      | used => exact .payUsed inner token (ih .used present)
  | constructor inner ih =>
      cases kind with
      | unguarded | termless => simp [evaluate] at present
      | used => exact .constructorUsed inner token (ih .used present)
  | choice left right ihl ihr =>
      rcases Bool.or_eq_true_iff.mp present with first | second
      · exact .left left right token kind (ihl kind first)
      · exact .right left right token kind (ihr kind second)
  | product left right ihl ihr =>
      cases kind with
      | termless => simp [evaluate] at present
      | used =>
          rcases Bool.or_eq_true_iff.mp present with first | second
          · exact .productUsedLeft left right token (ihl .used first)
          · exact .productUsedRight left right token (ihr .used second)
      | unguarded =>
          rcases Bool.or_eq_true_iff.mp present with first | second
          · have pair := Bool.and_eq_true_iff.mp first
            exact .productUnguardedLeft left right token (of_decide_eq_true pair.1) (ihl .unguarded pair.2)
          · have pair := Bool.and_eq_true_iff.mp second
            exact .productUnguardedRight left right token (of_decide_eq_true pair.1) (ihr .unguarded pair.2)

/-- A complete body rebuild preserves sound propagation witnesses. -/
theorem step_sound (program : Key → Expression Key Token) (settled : Key → Option Nat)
    (known : Slot Key Token → Bool) (sound : Sound program settled known) : Sound program settled (step program settled known) := by
  intro slot present
  exact evaluate_sound program settled known sound (program slot.1) slot.2.1 slot.2.2 present

/-- Equality-stopping convergence retains a propagation witness for every result flag. -/
theorem converge_sound (domain : List (Slot Key Token)) (complete : ∀ slot, slot ∈ domain)
    (program : Key → Expression Key Token) (settled : Key → Option Nat)
    (known : Slot Key Token → Bool) (growing : Included known (step program settled known))
    (sound : Sound program settled known) : Sound program settled (converge domain complete program settled known growing) := by
  induction known, growing using converge.induct domain complete program settled with
  | case1 known growing built stable =>
      dsimp only [built] at stable
      rw [converge.eq_def]
      simp only [dite_eq_left stable]
      exact step_sound program settled known sound
  | case2 known growing built unstable ih =>
      dsimp only [built] at unstable
      rw [converge.eq_def]
      simp only [dite_eq_right unstable]
      exact ih (step_sound program settled known sound)

/-- At a stable table, every finite propagation derivation appears in the computed flags. -/
theorem evaluate_complete (program : Key → Expression Key Token) (settled : Key → Option Nat)
    (known : Slot Key Token → Bool) (fixed : step program settled known = known)
    (expression : Expression Key Token) (token : Token) (kind : Kind)
    (derived : Derives program settled expression token kind) : evaluate expression settled known token kind = true := by
  induction derived with
  | source minimum flags token kind present => exact present
  | occurrence key token kind inner ih =>
      have same := congrFun fixed (key, token, kind)
      change known (key, token, kind) = true
      change evaluate (program key) settled known token kind = known (key, token, kind) at same
      exact same ▸ ih
  | map inner token kind child ih => exact ih
  | payTermless inner token child ih | payUsed inner token child ih | constructorUsed inner token child ih => exact ih
  | left left right token kind child ih => exact Bool.or_eq_true_iff.mpr (Or.inl ih)
  | right left right token kind child ih => exact Bool.or_eq_true_iff.mpr (Or.inr ih)
  | productUsedLeft left right token child ih => exact Bool.or_eq_true_iff.mpr (Or.inl ih)
  | productUsedRight left right token child ih => exact Bool.or_eq_true_iff.mpr (Or.inr ih)
  | productUnguardedLeft left right token zero child ih => simp [evaluate, zero, ih]
  | productUnguardedRight left right token zero child ih => simp [evaluate, zero, ih]

/-- Closing the family retains exactly the source's finite enclosing-token propagation derivations. -/
theorem close_exact (keys : List Key) (tokens : List Token) (allKeys : ∀ key, key ∈ keys) (allTokens : ∀ token, token ∈ tokens)
    (program : Key → Expression Key Token) (settled : Key → Option Nat) (key : Key) (token : Token) (kind : Kind) :
    close keys tokens allKeys allTokens program settled (key, token, kind) = true ↔
      Derives program settled (program key) token kind := by
  constructor
  · intro present
    have sound : Sound program settled (fun _ => false) := by intro slot found; contradiction
    exact converge_sound _ _ program settled _ _ sound (key, token, kind) present
  · intro derived
    have fixed := close_fixed keys tokens allKeys allTokens program settled
    have member := evaluate_complete program settled _ fixed (program key) token kind derived
    have same := congrFun fixed (key, token, kind)
    exact same ▸ member

end MicroCFTA.GroupedFlags
