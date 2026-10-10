import MicroCFTA.LatticePolynomial
import MicroCFTA.Lattice

/-!
# Binomial coefficients and the Bernoulli recurrence

This file implements the coefficient construction used by `faulhaber` in
`Data.CFTA.Refinement.Lattice`. Indices and exponents are natural numbers.
The production representation uses nonnegative `Int` values at these sites.
-/

namespace MicroCFTA.Faulhaber

local instance : Std.Associative (α := Rat) (· * ·) := ⟨Rat.mul_assoc⟩
local instance : Std.Commutative (α := Rat) (· * ·) := ⟨Rat.mul_comm⟩
local instance : Std.Associative (α := Rat) (· + ·) := ⟨Rat.add_assoc⟩
local instance : Std.Commutative (α := Rat) (· + ·) := ⟨Rat.add_comm⟩

@[simp] theorem cast_one : ((1 : Nat) : Rat) = 1 := rfl

/-- Sum the terms with indices from zero to `count - 1`. -/
def sum : Nat → (Nat → Rat) → Rat
  | 0, _ => 0
  | count + 1, term => sum count term + term count

@[simp] theorem sum_zero (term : Nat → Rat) : sum 0 term = 0 := rfl
@[simp] theorem sum_succ (count : Nat) (term : Nat → Rat) :
    sum (count + 1) term = sum count term + term count := rfl

theorem sum_congr {count : Nat} {left right : Nat → Rat}
    (same : ∀ index, index < count → left index = right index) :
    sum count left = sum count right := by
  induction count with
  | zero => rfl
  | succ count ih => rw [sum_succ, sum_succ, ih (fun i hi => same i (by omega)), same count (by omega)]

@[simp] theorem sum_of_zero (count : Nat) : sum count (fun _ => 0) = 0 := by
  induction count with
  | zero => rfl
  | succ count ih => simp [ih, Rat.add_zero]

theorem sum_add (count : Nat) (left right : Nat → Rat) :
    sum count (fun index => left index + right index) = sum count left + sum count right := by
  induction count with
  | zero => simp [Rat.add_zero]
  | succ count ih => simp only [sum_succ, ih]; ac_rfl

theorem sum_mul_left (count : Nat) (factor : Rat) (term : Nat → Rat) :
    sum count (fun index => factor * term index) = factor * sum count term := by
  induction count with
  | zero => simp
  | succ count ih => simp only [sum_succ, ih, Rat.mul_add]

theorem sum_mul_right (count : Nat) (term : Nat → Rat) (factor : Rat) :
    sum count (fun index => term index * factor) = sum count term * factor := by
  simpa only [Rat.mul_comm] using sum_mul_left count factor term

/-- Separate the first term instead of the last term. -/
theorem sum_head (count : Nat) (term : Nat → Rat) :
    sum (count + 1) term = term 0 + sum count (fun index => term (index + 1)) := by
  induction count with
  | zero => simp [Rat.zero_add, Rat.add_zero]
  | succ count ih => simp only [sum_succ] at ih ⊢; rw [ih]; ac_rfl

/-- The factorial of a natural number. -/
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

@[simp] theorem factorial_zero : factorial 0 = 1 := rfl
@[simp] theorem factorial_succ (n : Nat) : factorial (n + 1) = (n + 1) * factorial n := rfl

theorem factorial_positive (n : Nat) : 0 < factorial n := by
  induction n with
  | zero => decide
  | succ n ih => exact Nat.mul_pos (by omega) ih

/-- Pascal's recurrence, with zero coefficients above the diagonal. -/
def choose : Nat → Nat → Nat
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 => choose n k + choose n (k + 1)

@[simp] theorem choose_zero (n : Nat) : choose n 0 = 1 := by cases n <;> rfl
@[simp] theorem choose_succ_succ (n k : Nat) :
    choose (n + 1) (k + 1) = choose n k + choose n (k + 1) := rfl

theorem choose_above {n k : Nat} (above : n < k) : choose n k = 0 := by
  induction n generalizing k with
  | zero => cases k <;> simp_all [choose]
  | succ n ih =>
    cases k with
    | zero => omega
    | succ k => rw [choose_succ_succ, ih (by omega), ih (by omega)]

@[simp] theorem choose_self (n : Nat) : choose n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [choose_succ_succ, ih, choose_above (by omega), Nat.add_zero]

@[simp] theorem choose_one (n : Nat) : choose n 1 = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [choose_succ_succ, choose_zero, ih]; omega

/-- The factorial identity also proves integrality of the coefficient formula. -/
theorem choose_factorial (n k : Nat) (hk : k ≤ n) :
    choose n k * factorial k * factorial (n - k) = factorial n := by
  induction n generalizing k with
  | zero =>
    have : k = 0 := by omega
    subst k
    decide
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k =>
      by_cases equal : k = n
      · subst k; rw [choose_self, Nat.sub_self]; simp
      · have hkn : k < n := by omega
        have h₁ := ih k (by omega)
        have h₂ := ih (k + 1) (by omega)
        have index : n + 1 - (k + 1) = n - k := by omega
        have step : n - k = (n - (k + 1)) + 1 := by omega
        rw [choose_succ_succ, index, Nat.add_mul, Nat.add_mul]
        rw [factorial_succ]
        have first : choose n k * ((k + 1) * factorial k) * factorial (n - k) =
            (k + 1) * factorial n := by rw [← h₁]; ac_rfl
        have second : choose n (k + 1) * ((k + 1) * factorial k) * factorial (n - k) =
            (n - k) * factorial n := by
          have factorStep : factorial (n - k) = (n - k) * factorial (n - (k + 1)) := by
            conv => lhs; rw [step, factorial_succ]
            rw [← step]
          rw [factorStep, ← factorial_succ, ← h₂]
          ac_rfl
        rw [first, second, ← Nat.add_mul]
        have indices : k + 1 + (n - k) = n + 1 := by omega
        rw [indices, factorial_succ]

/-- Product of `count` consecutive positive factors after `start`. -/
def rising (start : Nat) : Nat → Nat
  | 0 => 1
  | count + 1 => rising start count * (start + count + 1)

theorem rising_factorial (start count : Nat) :
    rising start count * factorial start = factorial (start + count) := by
  induction count with
  | zero => simp [rising]
  | succ count ih =>
    change (rising start count * (start + count + 1)) * factorial start = _
    rw [show start + (count + 1) = (start + count) + 1 by omega, factorial_succ, ← ih]
    ac_rfl

/-- The product quotient used by the Haskell implementation. -/
def productChoose (total chosen : Nat) : Nat :=
  rising (total - chosen) chosen / factorial chosen

/-- The recursive product equals the source's consecutive-factor list. -/
theorem rising_eq_range_product (start count : Nat) :
    ((List.range count).map (fun k => start + k + 1)).prod = rising start count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ih]
    simp [rising]

/-- The denominator product is exactly `1 * ... * count`. -/
theorem factorial_eq_range_product (count : Nat) :
    ((List.range count).map (fun k => k + 1)).prod = factorial count := by
  have product := rising_eq_range_product 0 count
  simp only [Nat.zero_add] at product
  rw [product]
  simpa using rising_factorial 0 count

/-- The source's numerator and denominator are these explicit finite products. -/
theorem productChoose_eq_range_products (n k : Nat) :
    productChoose n k =
      ((List.range k).map (fun i => n - k + i + 1)).prod /
        ((List.range k).map (fun i => i + 1)).prod := by
  rw [rising_eq_range_product, factorial_eq_range_product]
  rfl

/-- Pascal coefficients equal the implemented product quotient in its valid domain. -/
theorem choose_eq_productChoose (n k : Nat) (hk : k ≤ n) :
    choose n k = productChoose n k := by
  have fact := choose_factorial n k hk
  have rise := rising_factorial (n - k) k
  rw [Nat.sub_add_cancel hk] at rise
  have cancelled : choose n k * factorial k = rising (n - k) k :=
    Nat.mul_right_cancel (factorial_positive _) (fact.trans rise.symm)
  unfold productChoose
  rw [← cancelled, Nat.mul_div_cancel _ (factorial_positive k)]

/-- Adding a zero last term does not change a sum. -/
theorem sum_last_zero (count : Nat) (term : Nat → Rat) (last : term count = 0) :
    sum (count + 1) term = sum count term := by rw [sum_succ, last, Rat.add_zero]

/-- The binomial theorem for arbitrary rational arguments and every degree. -/
theorem binomial_theorem (n : Nat) (x y : Rat) :
    (x + y) ^ n = sum (n + 1) (fun k => (choose n k : Rat) * x ^ k * y ^ (n - k)) := by
  induction n with
  | zero => simp [sum, choose, Rat.zero_add]
  | succ n ih =>
    let term := fun k => (choose n k : Rat) * x ^ k * y ^ (n - k)
    have first : sum (n + 1) (fun k => (choose n k : Rat) * x ^ (k + 1) * y ^ (n - k)) =
        x * sum (n + 1) term := by
      rw [← sum_mul_left]
      apply sum_congr
      intro k hk
      simp only [Rat.pow_succ, term]
      ac_rfl
    have last : (choose n (n + 1) : Rat) * x ^ (n + 1) * y ^ (n - n) = 0 := by
      rw [choose_above (by omega)]; simp
    have second : y ^ (n + 1) + sum (n + 1)
        (fun k => (choose n (k + 1) : Rat) * x ^ (k + 1) * y ^ (n - k)) =
        y * sum (n + 1) term := by
      rw [sum_last_zero n _ last, sum_head n term, Rat.mul_add]
      have head : y * term 0 = y ^ (n + 1) := by
        simp only [term, choose_zero, cast_one, Rat.pow_zero, Rat.mul_one,
          Rat.one_mul, Nat.sub_zero, Rat.pow_succ]
        rw [Rat.mul_comm]
      rw [head, ← sum_mul_left]
      congr 1
      apply sum_congr
      intro k hk
      have hn : n - k = (n - (k + 1)) + 1 := by omega
      rw [hn]
      dsimp [term]
      simp only [Rat.pow_succ]
      ac_rfl
    rw [sum_head (n + 1)]
    simp only [choose_zero, cast_one, Rat.pow_zero, Rat.mul_one, Rat.one_mul, Nat.sub_zero]
    have expand : sum (n + 1)
        (fun k => (choose (n + 1) (k + 1) : Rat) * x ^ (k + 1) * y ^ (n + 1 - (k + 1))) =
        sum (n + 1) (fun k => (choose n k : Rat) * x ^ (k + 1) * y ^ (n - k)) +
        sum (n + 1) (fun k => (choose n (k + 1) : Rat) * x ^ (k + 1) * y ^ (n - k)) := by
      rw [← sum_add]
      apply sum_congr
      intro k hk
      rw [choose_succ_succ, Rat.natCast_add, show n + 1 - (k + 1) = n - k by omega,
        Rat.add_mul, Rat.add_mul]
    rw [expand, first]
    have combine : y ^ (n + 1) + (x * sum (n + 1) term +
        sum (n + 1) (fun k => (choose n (k + 1) : Rat) * x ^ (k + 1) * y ^ (n - k))) =
        (x + y) * sum (n + 1) term := by
      rw [Rat.add_mul, ← second]
      ac_rfl
    rw [combine]
    change (x + y) ^ (n + 1) = (x + y) * sum (n + 1) _
    rw [← ih, Rat.pow_succ, Rat.mul_comm]

/-- Exchange a triangular sum with its diagonal decomposition. -/
theorem sum_triangle (n : Nat) (term : Nat → Nat → Rat) :
    sum (n + 1) (fun i => sum (n + 1 - i) (fun j => term i j)) =
      sum (n + 1) (fun k => sum (k + 1) (fun i => term i (k - i))) := by
  induction n with
  | zero => simp [sum, Rat.zero_add]
  | succ n ih =>
    rw [sum_succ (n + 1), sum_succ (n + 1)]
    have splitInner : sum (n + 1) (fun i => sum (n + 1 + 1 - i) (fun j => term i j)) =
        sum (n + 1) (fun i => sum (n + 1 - i) (fun j => term i j)) +
        sum (n + 1) (fun i => term i (n + 1 - i)) := by
      rw [← sum_add]
      apply sum_congr
      intro i hi
      rw [show n + 1 + 1 - i = (n + 1 - i) + 1 by omega, sum_succ]
    rw [splitInner, ih, sum_succ (n + 1)]
    have indices : n + 1 + 1 - (n + 1) = 1 := by omega
    rw [indices]
    simp only [sum, Nat.sub_self, Rat.zero_add]
    ac_rfl

/-- Finite convolution of coefficient sequences. -/
def convolution (left right : Nat → Rat) (n : Nat) : Rat :=
  sum (n + 1) (fun k => left k * right (n - k))

theorem convolution_assoc (a b c : Nat → Rat) (n : Nat) :
    convolution (convolution a b) c n = convolution a (convolution b c) n := by
  unfold convolution
  have left : sum (n + 1) (fun k => sum (k + 1) (fun i => a i * b (k - i)) * c (n - k)) =
      sum (n + 1) (fun k => sum (k + 1) (fun i => a i * b (k - i) * c (n - k))) := by
    apply sum_congr
    intro k hk
    rw [sum_mul_right]
  rw [left]
  have diagonal : sum (n + 1) (fun k => sum (k + 1) (fun i => a i * b (k - i) * c (n - k))) =
      sum (n + 1) (fun k => sum (k + 1) (fun i => a i * b (k - i) * c (n - i - (k - i)))) := by
    apply sum_congr
    intro k hk
    apply sum_congr
    intro i hi
    rw [show n - i - (k - i) = n - k by omega]
  rw [diagonal, ← sum_triangle n (fun i j => a i * b j * c (n - i - j))]
  apply sum_congr
  intro i hi
  rw [show n + 1 - i = n - i + 1 by omega, ← sum_mul_left]
  apply sum_congr
  intro j hj
  rw [Rat.mul_assoc]

/-- Reverse the order of a finite sum. -/
theorem sum_reverse (n : Nat) (term : Nat → Rat) :
    sum (n + 1) (fun k => term (n - k)) = sum (n + 1) term := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sum_head (n + 1), sum_succ (n + 1)]
    simp only [Nat.sub_zero]
    have tails : sum (n + 1) (fun k => term (n + 1 - (k + 1))) = sum (n + 1) term := by
      rw [← ih]
      apply sum_congr
      intro k hk
      congr 1
      omega
    rw [tails, Rat.add_comm]

theorem convolution_comm (a b : Nat → Rat) (n : Nat) :
    convolution a b n = convolution b a n := by
  unfold convolution
  rw [← sum_reverse n (fun k => b k * a (n - k))]
  apply sum_congr
  intro k hk
  rw [show n - (n - k) = k by omega, Rat.mul_comm]

/-- The coefficient sequence for the constant polynomial one. -/
def unitSequence (n : Nat) : Rat := if n = 0 then 1 else 0

theorem convolution_unit_left (a : Nat → Rat) (n : Nat) :
    convolution unitSequence a n = a n := by
  unfold convolution
  rw [sum_head]
  simp only [unitSequence, ↓reduceIte, Rat.one_mul, Nat.sub_zero]
  have zeroTail : sum n (fun k => (if k + 1 = 0 then 1 else 0) * a (n - (k + 1))) = 0 := by
    simp [Rat.zero_mul]
  rw [zeroTail, Rat.add_zero]

theorem convolution_unit_right (a : Nat → Rat) (n : Nat) :
    convolution a unitSequence n = a n := by rw [convolution_comm, convolution_unit_left]

/-- Cancel a nonzero rational factor without a field tactic. -/
theorem cancel_right {left right factor : Rat} (hf : factor ≠ 0)
    (same : left * factor = right * factor) : left = right := by
  have divided := congrArg (fun value => value * factor⁻¹) same
  simpa only [Rat.mul_assoc, Rat.mul_inv_cancel factor hf, Rat.mul_one] using divided

/-- Rational factorials are nonzero at every natural index. -/
theorem factorial_nonzero (n : Nat) : (factorial n : Rat) ≠ 0 := by
  intro hz
  have hn := (Rat.natCast_eq_zero_iff).mp hz
  exact Nat.ne_of_gt (factorial_positive n) hn

/-- The factorial ratio of a binomial coefficient. -/
theorem choose_div_factorial (n k : Nat) (hk : k ≤ n) :
    (choose n k : Rat) / (factorial n : Rat) =
      (factorial k : Rat)⁻¹ * (factorial (n - k) : Rat)⁻¹ := by
  apply cancel_right (factorial_nonzero n)
  rw [Rat.div_mul_cancel (factorial_nonzero n)]
  have fact := congrArg (fun value : Nat => (value : Rat)) (choose_factorial n k hk)
  simp only [Rat.natCast_mul] at fact
  rw [← fact]
  have a := Rat.inv_mul_cancel (factorial k : Rat) (factorial_nonzero k)
  have b := Rat.inv_mul_cancel (factorial (n - k) : Rat) (factorial_nonzero (n - k))
  grind

/-- Divided powers separate factorial denominators from coefficient convolution. -/
def dividedPower (x : Rat) (n : Nat) : Rat := x ^ n / (factorial n : Rat)

/-- The binomial theorem in divided-power coordinates. -/
theorem dividedPower_add (x y : Rat) (n : Nat) :
    dividedPower (x + y) n = convolution (dividedPower x) (dividedPower y) n := by
  unfold dividedPower convolution
  rw [binomial_theorem, Rat.div_def, ← sum_mul_right]
  apply sum_congr
  intro k hk
  have coeff := choose_div_factorial n k (by omega)
  simp only [Rat.div_def] at coeff ⊢
  rw [show (choose n k : Rat) * x ^ k * y ^ (n - k) * (factorial n : Rat)⁻¹ =
      ((choose n k : Rat) * (factorial n : Rat)⁻¹) * x ^ k * y ^ (n - k) by ac_rfl, coeff]
  ac_rfl

/-- A finite sum exposes a proof that every recursive index is smaller. -/
def sumFin : (count : Nat) → (Fin count → Rat) → Rat
  | 0, _ => 0
  | count + 1, term => sumFin count (fun index => term index.castSucc) + term ⟨count, by omega⟩

theorem sumFin_eq (count : Nat) (term : Nat → Rat) :
    sumFin count (fun index => term index.val) = sum count term := by
  induction count with
  | zero => rfl
  | succ count ih => simpa only [sumFin, Fin.val_castSucc, sum_succ] using congrArg (· + term count) ih

/-- The direct triangular recurrence in `bernoulliNumbers`. -/
def bernoulli (n : Nat) : Rat :=
  if n = 0 then 1 else
    -(sumFin n (fun k => (productChoose (n + 1) k.val : Rat) * bernoulli k.val)) / ((n + 1 : Nat) : Rat)
termination_by n

@[simp] theorem bernoulli_zero : bernoulli 0 = 1 := by rw [bernoulli]; decide

/-- The recursive call uses exactly the earlier coefficients from the source. -/
theorem bernoulli_recurrence (n : Nat) :
    bernoulli (n + 1) =
      -sum (n + 1) (fun k => (choose (n + 2) k : Rat) * bernoulli k) / ((n + 2 : Nat) : Rat) := by
  rw [bernoulli]
  simp only [Nat.succ_ne_zero, ↓reduceIte]
  rw [sumFin_eq (n + 1) (fun k => (productChoose (n + 2) k : Rat) * bernoulli k)]
  congr 2
  apply sum_congr
  intro k hk
  rw [choose_eq_productChoose (n + 2) k (by omega)]

@[simp] theorem choose_penultimate (n : Nat) : choose (n + 1) n = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [choose_succ_succ, ih, choose_self]

/-- Bernoulli's sum recurrence follows from the implemented division. -/
theorem bernoulli_sum (n : Nat) :
    sum (n + 1) (fun k => (choose (n + 1) k : Rat) * bernoulli k) = unitSequence n := by
  cases n with
  | zero => simp [sum, unitSequence, Rat.zero_add]
  | succ n =>
    rw [sum_succ, choose_penultimate, bernoulli_recurrence]
    have nonzero : ((n + 2 : Nat) : Rat) ≠ 0 := by
      intro h
      have := Rat.natCast_eq_zero_iff.mp h
      omega
    rw [Rat.mul_comm _ (-sum (n + 1) _ / _), Rat.div_mul_cancel nonzero, Rat.add_neg_cancel]
    simp [unitSequence]

/-- Bernoulli coefficients expressed in divided-power coordinates. -/
def bernoulliScaled (n : Nat) : Rat := bernoulli n / (factorial n : Rat)

/-- The coefficient sequence of `(exp t - 1) / t`. -/
def integralExp (n : Nat) : Rat := (factorial (n + 1) : Rat)⁻¹

/-- The Bernoulli recurrence makes the two coefficient sequences inverse. -/
theorem bernoulli_inverse (n : Nat) :
    convolution bernoulliScaled integralExp n = unitSequence n := by
  unfold convolution bernoulliScaled integralExp
  have terms : sum (n + 1)
      (fun k => bernoulli k / (factorial k : Rat) * (factorial (n - k + 1) : Rat)⁻¹) =
      sum (n + 1) (fun k => (choose (n + 1) k : Rat) * bernoulli k) /
        (factorial (n + 1) : Rat) := by
    rw [Rat.div_def, ← sum_mul_right]
    apply sum_congr
    intro k hk
    have ratio := choose_div_factorial (n + 1) k (by omega)
    rw [show n + 1 - k = n - k + 1 by omega] at ratio
    simp only [Rat.div_def] at ratio ⊢
    rw [show (choose (n + 1) k : Rat) * bernoulli k * (factorial (n + 1) : Rat)⁻¹ =
      ((choose (n + 1) k : Rat) * (factorial (n + 1) : Rat)⁻¹) * bernoulli k by ac_rfl, ratio]
    ac_rfl
  rw [terms, bernoulli_sum]
  cases n with
  | zero => simp [unitSequence, factorial, Rat.div_def]; decide +kernel
  | succ n => simp [unitSequence, Rat.div_def]

/-- Shift a sequence by one coefficient and insert a zero constant. -/
def shift (term : Nat → Rat) : Nat → Rat
  | 0 => 0
  | n + 1 => term n

theorem convolution_add_right (a b c : Nat → Rat) (n : Nat) :
    convolution a (fun k => b k + c k) n = convolution a b n + convolution a c n := by
  unfold convolution
  rw [← sum_add]
  apply sum_congr
  intro k hk
  rw [Rat.mul_add]

theorem convolution_shift (a b : Nat → Rat) (n : Nat) :
    convolution a (shift b) n = shift (convolution a b) n := by
  cases n with
  | zero => simp [convolution, sum, shift, Rat.zero_add]
  | succ n =>
    unfold convolution
    rw [sum_succ]
    simp only [Nat.sub_self, shift, Rat.mul_zero, Rat.add_zero]
    apply sum_congr
    intro k hk
    rw [show n + 1 - k = (n - k) + 1 by omega]

@[simp] theorem rational_one_pow (n : Nat) : (1 : Rat) ^ n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Rat.pow_succ, ih, Rat.mul_one]

/-- The exponential sequence is one plus the shifted exponential integral. -/
theorem dividedPower_one (n : Nat) :
    dividedPower 1 n = unitSequence n + shift integralExp n := by
  cases n with
  | zero => simp [dividedPower, unitSequence, shift, Rat.add_zero, Rat.div_def]; decide +kernel
  | succ n => simp [dividedPower, unitSequence, shift, integralExp, Rat.div_def, Rat.zero_add]

/-- Translate the Bernoulli sequence by one in coefficient space. -/
theorem bernoulli_translate (n : Nat) :
    convolution bernoulliScaled (dividedPower 1) n =
      bernoulliScaled n + shift unitSequence n := by
  have expand : dividedPower 1 = fun k => unitSequence k + shift integralExp k :=
    funext dividedPower_one
  rw [expand, convolution_add_right, convolution_unit_right, convolution_shift]
  have inverse : convolution bernoulliScaled integralExp = unitSequence := funext bernoulli_inverse
  rw [inverse]

/-- Bernoulli polynomials in divided-power coordinates. -/
def bernoulliPolynomial (n : Nat) (x : Rat) : Rat :=
  convolution bernoulliScaled (dividedPower x) n

/-- Translation follows from the proved recurrence for every degree. -/
theorem bernoulliPolynomial_step (n : Nat) (x : Rat) :
    bernoulliPolynomial (n + 1) (x + 1) =
      bernoulliPolynomial (n + 1) x + dividedPower x n := by
  unfold bernoulliPolynomial
  have binomial : dividedPower (x + 1) = convolution (dividedPower 1) (dividedPower x) := by
    funext k
    rw [dividedPower_add, convolution_comm]
  rw [binomial, ← convolution_assoc]
  have translate : convolution bernoulliScaled (dividedPower 1) =
      fun k => bernoulliScaled k + shift unitSequence k := funext bernoulli_translate
  rw [translate, convolution_comm, convolution_add_right, convolution_shift, shift,
    convolution_unit_right, convolution_comm]

/-- Faulhaber coefficients before the source changes `B₁` to positive one half. -/
def faulhaberMinus (power : Nat) (x : Rat) : Rat :=
  sum (power + 1) (fun k =>
    ((choose (power + 1) k : Rat) * bernoulli k / ((power + 1 : Nat) : Rat)) * x ^ (power + 1 - k))

/-- Convert source coefficients to divided-power coefficients. -/
theorem faulhaber_coefficient (power k : Nat) (hk : k ≤ power + 1) :
    (choose (power + 1) k : Rat) * bernoulli k / ((power + 1 : Nat) : Rat) =
      (factorial power : Rat) * bernoulliScaled k * (factorial (power + 1 - k) : Rat)⁻¹ := by
  have nonzero : ((power + 1 : Nat) : Rat) ≠ 0 := by
    intro h
    have := Rat.natCast_eq_zero_iff.mp h
    omega
  apply cancel_right nonzero
  rw [Rat.div_mul_cancel nonzero]
  have ratio := choose_div_factorial (power + 1) k hk
  have cancelled := congrArg (fun value => value * (factorial (power + 1) : Rat)) ratio
  rw [Rat.div_mul_cancel (factorial_nonzero _)] at cancelled
  rw [cancelled]
  simp only [bernoulliScaled, Rat.div_def, factorial_succ, Rat.natCast_mul]
  ac_rfl

/-- The omitted final coefficient is constant in the argument. -/
theorem faulhaberMinus_as_bernoulli (power : Nat) (x : Rat) :
    faulhaberMinus power x + (factorial power : Rat) * bernoulliScaled (power + 1) =
      (factorial power : Rat) * bernoulliPolynomial (power + 1) x := by
  unfold bernoulliPolynomial convolution
  rw [sum_succ, Rat.mul_add]
  have last : bernoulliScaled (power + 1) * dividedPower x (power + 1 - (power + 1)) =
      bernoulliScaled (power + 1) := by
    simp [dividedPower, Rat.div_def]
    have one : (1 : Rat)⁻¹ = 1 := by decide +kernel
    rw [one, Rat.mul_one]
  rw [last]
  congr 1
  unfold faulhaberMinus
  rw [← sum_mul_left]
  apply sum_congr
  intro k hk
  rw [faulhaber_coefficient power k (by omega)]
  simp only [dividedPower, Rat.div_def]
  ac_rfl

/-- The ordinary-sign Faulhaber polynomial has the forward finite difference. -/
theorem faulhaberMinus_step (power : Nat) (x : Rat) :
    faulhaberMinus power (x + 1) = faulhaberMinus power x + x ^ power := by
  have left := faulhaberMinus_as_bernoulli power (x + 1)
  have right := faulhaberMinus_as_bernoulli power x
  rw [bernoulliPolynomial_step, Rat.mul_add] at left
  have cancelled : (factorial power : Rat) * dividedPower x power = x ^ power := by
    unfold dividedPower
    rw [Rat.mul_comm, Rat.div_mul_cancel (factorial_nonzero power)]
  rw [cancelled, ← right] at left
  grind

@[simp] theorem rational_inv_one : (1 : Rat)⁻¹ = 1 := by decide +kernel

@[simp] theorem bernoulli_one : bernoulli 1 = -(1 / 2) := by
  rw [show 1 = 0 + 1 by rfl, bernoulli_recurrence]
  simp only [sum, bernoulli_zero, choose_zero]
  decide +kernel

/-- The source changes only the coefficient with index one. -/
def bernoulliPlus (n : Nat) : Rat := if n = 1 then 1 / 2 else bernoulli n

theorem bernoulliPlus_eq (n : Nat) :
    bernoulliPlus n = bernoulli n + (if n = 1 then 1 else 0) := by
  unfold bernoulliPlus
  by_cases hn : n = 1
  · subst n; rw [bernoulli_one]; decide +kernel
  · simp only [hn, ↓reduceIte, Rat.add_zero]

/-- The scalar expression evaluated by the production Faulhaber construction. -/
def faulhaber (power : Nat) (x : Rat) : Rat :=
  sum (power + 1) (fun k =>
    ((choose (power + 1) k : Rat) * bernoulliPlus k / ((power + 1 : Nat) : Rat)) * x ^ (power + 1 - k))

/-- A finite sum with one potentially nonzero term. -/
theorem sum_single (count selected : Nat) (value : Rat) :
    sum count (fun k => if k = selected then value else 0) =
      if selected < count then value else 0 := by
  induction count with
  | zero => simp [sum]
  | succ count ih =>
    rw [sum_succ, ih]
    by_cases same : count = selected
    · subst selected
      simp [Rat.zero_add]
    · by_cases before : selected < count
      · have next : selected < count + 1 := by omega
        simp only [before, next, same, ↓reduceIte, Rat.add_zero]
      · have after : ¬ selected < count + 1 := by omega
        simp only [before, after, same, ↓reduceIte, Rat.add_zero]

/-- The positive-sign polynomial adds the endpoint term in every positive degree. -/
theorem faulhaber_eq_minus (power : Nat) (x : Rat) :
    faulhaber (power + 1) x = faulhaberMinus (power + 1) x + x ^ (power + 1) := by
  unfold faulhaber faulhaberMinus
  have terms : sum (power + 1 + 1)
      (fun k => (choose (power + 1 + 1) k : Rat) * bernoulliPlus k /
        ((power + 1 + 1 : Nat) : Rat) * x ^ (power + 1 + 1 - k)) =
      sum (power + 1 + 1)
      (fun k => (choose (power + 1 + 1) k : Rat) * bernoulli k /
        ((power + 1 + 1 : Nat) : Rat) * x ^ (power + 1 + 1 - k)) +
      sum (power + 1 + 1) (fun k => if k = 1 then x ^ (power + 1) else 0) := by
    rw [← sum_add]
    apply sum_congr
    intro k hk
    rw [bernoulliPlus_eq, Rat.div_def, Rat.div_def, Rat.mul_add, Rat.add_mul, Rat.add_mul]
    congr 1
    by_cases same : k = 1
    · subst k
      simp only [↓reduceIte, choose_one, Rat.mul_one]
      have nonzero : ((power + 1 + 1 : Nat) : Rat) ≠ 0 := by
        intro h
        have := Rat.natCast_eq_zero_iff.mp h
        omega
      rw [Rat.mul_inv_cancel _ nonzero, Rat.one_mul,
        show power + 1 + 1 - 1 = power + 1 by omega]
    · simp only [same, ↓reduceIte, Rat.mul_zero, Rat.zero_mul]
  rw [terms, sum_single]
  simp only [show 1 < power + 1 + 1 by omega, ↓reduceIte]

@[simp] theorem faulhaber_zero (x : Rat) : faulhaber 0 x = x := by
  simp [faulhaber, sum, bernoulliPlus, Rat.div_def, Rat.zero_add]

/-- The actual positive-sign coefficient construction has the backward difference. -/
theorem faulhaber_step (power : Nat) (x : Rat) :
    faulhaber power x - faulhaber power (x - 1) = x ^ power := by
  cases power with
  | zero => simp only [faulhaber_zero, Rat.pow_zero]; grind
  | succ power =>
    rw [faulhaber_eq_minus, faulhaber_eq_minus]
    have previous := faulhaberMinus_step (power + 1) (x - 1)
    have cancel : x - 1 + 1 = x := by grind
    rw [cancel] at previous
    grind

/-- The recursive sum and the source's list sum have the same value. -/
theorem sum_range (count : Nat) (term : Nat → Rat) :
    ((List.range count).map term).sum = sum count term := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp [sum, Rat.add_zero]

/-- The sparse polynomial assembled by the production coefficient formula. -/
def polynomialFaulhaber (power : Nat) (argument : LatticePolynomial.Polynomial) :
    LatticePolynomial.Polynomial :=
  LatticePolynomial.sumPolynomials ((List.range (power + 1)).map fun k =>
    LatticePolynomial.multiplyPolynomials
      (LatticePolynomial.polynomialConstant
        ((productChoose (power + 1) k : Rat) * bernoulliPlus k / ((power + 1 : Nat) : Rat)))
      (LatticePolynomial.polynomialPower argument (power + 1 - k)))

/-- Sparse construction evaluates to the proved scalar Faulhaber expression. -/
theorem evaluate_polynomialFaulhaber (assignment : Nat → Rat) (power : Nat)
    (argument : LatticePolynomial.Polynomial) :
    LatticePolynomial.evaluate assignment (polynomialFaulhaber power argument) =
      faulhaber power (LatticePolynomial.evaluate assignment argument) := by
  unfold polynomialFaulhaber
  rw [LatticePolynomial.evaluate_sum]
  simp only [List.map_map, Function.comp_def, LatticePolynomial.evaluate_multiply,
    LatticePolynomial.evaluate_constant, LatticePolynomial.evaluate_power]
  rw [sum_range]
  unfold faulhaber
  apply sum_congr
  intro k hk
  rw [choose_eq_productChoose (power + 1) k (by omega)]

/-- All integer intervals follow from the coefficient theorem, including negative starts. -/
theorem interval_power_sum (power : Nat) (start : Int) (count : Nat) :
    Lattice.intervalSum (fun value => (value : Rat) ^ power) start count =
      faulhaber power ((start + count - 1 : Int) : Rat) -
      faulhaber power ((start - 1 : Int) : Rat) := by
  apply Lattice.intervalSum_antiderivative (fun value => (value : Rat) ^ power)
    (fun value => faulhaber power ((value - 1 : Int) : Rat))
  intro value
  have step := faulhaber_step power (value : Rat)
  have forward : ((value + 1 - 1 : Int) : Rat) = (value : Rat) := by congr 1; omega
  have previous : ((value - 1 : Int) : Rat) = (value : Rat) - 1 := by
    rw [Rat.intCast_sub]
    rfl
  rw [forward, previous]
  exact step

/-- The source's inclusive endpoints compute the exact interval sum. -/
theorem inclusive_power_sum (power : Nat) (low high : Int) (ordered : low ≤ high + 1) :
    Lattice.intervalSum (fun value => (value : Rat) ^ power) low (high - low + 1).toNat =
      faulhaber power (high : Rat) - faulhaber power ((low - 1 : Int) : Rat) := by
  rw [interval_power_sum]
  congr 2
  congr 1
  have nonnegative : 0 ≤ high - low + 1 := by omega
  rw [Int.toNat_of_nonneg nonnegative]
  omega

/-- The source's sparse endpoint difference evaluates to the exact integer sum. -/
theorem polynomial_interval_sum (assignment : Nat → Rat) (power : Nat)
    (low high : LatticePolynomial.Polynomial) (lowValue highValue : Int)
    (hl : LatticePolynomial.evaluate assignment low = (lowValue : Rat))
    (hh : LatticePolynomial.evaluate assignment high = (highValue : Rat))
    (ordered : lowValue ≤ highValue + 1) :
    LatticePolynomial.evaluate assignment
      (LatticePolynomial.addPolynomials (polynomialFaulhaber power high)
        (LatticePolynomial.multiplyPolynomials (LatticePolynomial.polynomialConstant (-1))
          (polynomialFaulhaber power
            (LatticePolynomial.addPolynomials low (LatticePolynomial.polynomialConstant (-1)))))) =
      Lattice.intervalSum (fun value => (value : Rat) ^ power) lowValue (highValue - lowValue + 1).toNat := by
  rw [LatticePolynomial.evaluate_add, LatticePolynomial.evaluate_multiply,
    LatticePolynomial.evaluate_constant, evaluate_polynomialFaulhaber,
    evaluate_polynomialFaulhaber, LatticePolynomial.evaluate_add,
    LatticePolynomial.evaluate_constant, hl, hh, inclusive_power_sum power lowValue highValue ordered]
  have previous : ((lowValue - 1 : Int) : Rat) = (lowValue : Rat) + (-1) := by
    rw [Rat.intCast_sub]
    grind
  rw [previous]
  grind

end MicroCFTA.Faulhaber
