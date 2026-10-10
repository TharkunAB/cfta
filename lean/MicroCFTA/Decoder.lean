import MicroCFTA.Probability
import MicroCFTA.Language

/-!
# Counted finite rank plans

The constructors correspond to finite sources, maps, ordered choices, and
applications in `Ranked/Internal/Decoder.hs`. Counts are computed rather than
supplied as unchecked metadata. The decoder uses offsets and mixed radix.
Its correctness theorem compares every rank with a separate list semantics.

The source representation is a finite list. Haskell source callbacks, shared
decoder caches, size tables, machine integers, and dispatch maps are separate
implementation obligations.
-/

namespace MicroCFTA.Decoder

/-- A finite decoding plan. Applications retain function-major rank order. -/
inductive Plan : Type → Type 1 where
  | source (values : List α) : Plan α
  | map (f : α → β) (input : Plan α) : Plan β
  | choice (left right : Plan α) : Plan α
  | ap (functions : Plan (α → β)) (arguments : Plan α) : Plan β

/-- Independent list semantics for function-major application. -/
def applyValues (functions : List (α → β)) (arguments : List α) : List β :=
  functions.flatMap fun f => arguments.map f

/-- Enumerate a plan in replay order. Repeated values remain separate runs. -/
def values : Plan α → List α
  | .source xs => xs
  | .map f p => (values p).map f
  | .choice p q => values p ++ values q
  | .ap p q => applyValues (values p) (values q)

/-- Count a plan without constructing its Cartesian products. -/
def count : Plan α → Nat
  | .source xs => xs.length
  | .map _ p => count p
  | .choice p q => count p + count q
  | .ap p q => count p * count q

/-- Decode a rank by branch offsets and quotient/remainder. -/
def decode : Plan α → Nat → Option α
  | .source xs, rank => xs[rank]?
  | .map f p, rank => (decode p rank).map f
  | .choice p q, rank =>
      if rank < count p then decode p rank else decode q (rank - count p)
  | .ap p q, rank =>
      if rank < count p * count q then
        (decode p (rank / count q)).bind fun f => (decode q (rank % count q)).map f
      else none

theorem length_applyValues (fs : List (α → β)) (xs : List α) :
    (applyValues fs xs).length = fs.length * xs.length := by
  induction fs with
  | nil => simp [applyValues]
  | cons f fs ih =>
    simp only [applyValues, List.flatMap_cons, List.length_append, List.length_map] at *
    rw [ih]
    simp [Nat.add_mul, Nat.add_comm]

/-- The compositional counter is exactly the number of replay ranks. -/
theorem count_correct (p : Plan α) : count p = (values p).length := by
  induction p with
  | source xs => rfl
  | map f p ih => simp [count, values, ih]
  | choice p q ihp ihq => simp [count, values, ihp, ihq]
  | ap p q ihp ihq => simp [count, values, length_applyValues, ihp, ihq]

/-- A product list has the same indexing equation as a mixed-radix decoder. -/
theorem get_applyValues (fs : List (α → β)) (xs : List α) (rank : Nat) :
    (applyValues fs xs)[rank]? =
      if rank < fs.length * xs.length then
        fs[rank / xs.length]?.bind (fun f => xs[rank % xs.length]?.map f)
      else none := by
  by_cases hzero : xs.length = 0
  · have : xs = [] := List.length_eq_zero_iff.mp hzero
    subst xs
    have hempty : applyValues fs [] = [] := by
      induction fs with
      | nil => rfl
      | cons f fs ih => simp [applyValues]
    simp [hempty]
  · have hpos : 0 < xs.length := by omega
    induction fs generalizing rank with
    | nil => simp [applyValues]
    | cons f fs ih =>
      simp only [applyValues, List.flatMap_cons]
      by_cases hfirst : rank < xs.length
      · rw [List.getElem?_append_left (by simpa using hfirst)]
        have hall : rank < (f :: fs).length * xs.length := by
          simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
          omega
        rw [ite_eq_left hall, Nat.div_eq_of_lt hfirst, Nat.mod_eq_of_lt hfirst]
        simp
      · rw [List.getElem?_append_right (by simpa using Nat.le_of_not_gt hfirst)]
        rw [show (fs.flatMap fun f => List.map f xs)[rank - (List.map f xs).length]? =
            (applyValues fs xs)[rank - xs.length]? by simp [applyValues]]
        rw [ih]
        have hle : xs.length ≤ rank := by omega
        have hdiv : rank / xs.length = (rank - xs.length) / xs.length + 1 := by
          have he : rank = xs.length + (rank - xs.length) := by omega
          calc
            rank / xs.length = (xs.length + (rank - xs.length)) / xs.length := congrArg (· / xs.length) he
            _ = (rank - xs.length) / xs.length + 1 := by rw [Nat.add_div_left _ hpos]
        have hmod : rank % xs.length = (rank - xs.length) % xs.length := by
          have he : rank = xs.length + (rank - xs.length) := by omega
          calc
            rank % xs.length = (xs.length + (rank - xs.length)) % xs.length := congrArg (· % xs.length) he
            _ = (rank - xs.length) % xs.length := by simp
        have hbound : rank - xs.length < fs.length * xs.length ↔
            rank < (f :: fs).length * xs.length := by
          simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
          omega
        simp only [hbound, hdiv, hmod, List.getElem?_cons_succ]

/-- Every decoder result agrees with the independent ordered list semantics. -/
theorem decode_correct (p : Plan α) (rank : Nat) :
    decode p rank = (values p)[rank]? := by
  induction p generalizing rank with
  | source xs => rfl
  | map f p ih => simp [decode, values, ih]
  | choice p q ihp ihq =>
    simp only [decode, values, ihp, ihq, count_correct, List.getElem?_append]
  | ap p q ihp ihq =>
    simp only [decode, values, ihp, ihq, count_correct, get_applyValues]

/-- A valid rank always decodes. -/
theorem decode_exists (p : Plan α) (rank : Nat) (h : rank < count p) :
    ∃ value, decode p rank = some value := by
  rw [decode_correct]
  rw [count_correct] at h
  exact ⟨(values p)[rank], List.getElem?_eq_getElem h⟩

/-- Invalid ranks are rejected, including every rank of an empty product. -/
theorem decode_none_iff (p : Plan α) (rank : Nat) :
    decode p rank = none ↔ count p ≤ rank := by
  simp [decode_correct, count_correct]

/-- Every semantic member is reachable by a valid replay rank. -/
theorem mem_values_iff (p : Plan α) (value : α) :
    value ∈ values p ↔ ∃ rank, rank < count p ∧ decode p rank = some value := by
  constructor
  · intro hm
    obtain ⟨rank, hr⟩ := List.mem_iff_getElem?.mp hm
    refine ⟨rank, ?_, by simpa [decode_correct] using hr⟩
    rw [count_correct]
    exact (List.getElem?_eq_some_iff.mp hr).1
  · rintro ⟨rank, _, hr⟩
    rw [decode_correct] at hr
    exact List.mem_of_getElem? hr

/-- Push a map into leaves, choices, and application functions. -/
def pushMap (f : α → β) : Plan α → Plan β
  | .source xs => .source (xs.map f)
  | .map g p => pushMap (f ∘ g) p
  | .choice p q => .choice (pushMap f p) (pushMap f q)
  | .ap p q => .ap (pushMap (fun g x => f (g x)) p) q

/-- Map pushing retains the exact ordered member list. -/
theorem values_pushMap (f : α → β) (p : Plan α) :
    values (pushMap f p) = (values p).map f := by
  induction p generalizing β with
  | source xs => rfl
  | map g p ih => simp [pushMap, values, ih, List.map_map, Function.comp_def]
  | choice p q ihp ihq => simp [pushMap, values, ihp, ihq]
  | ap p q ihp ihq =>
    simp [pushMap, values, ihp, applyValues, List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def]

/-- Splice a left choice into a right-associated sequence of alternatives. -/
def appendPlan : Plan α → Plan α → Plan α
  | .choice p q, r => appendPlan p (appendPlan q r)
  | p, r => .choice p r

/-- Choice splicing retains branch order and multiplicity. -/
theorem values_appendPlan (p q : Plan α) :
    values (appendPlan p q) = values p ++ values q := by
  induction p with
  | source xs => rfl
  | map f p ih => rfl
  | choice p r ihp ihr => simp [appendPlan, ihp, ihr, values, List.append_assoc]
  | ap p r ihp ihr => rfl

/-- Normalize maps and nested choices throughout a plan. -/
def normalize : Plan α → Plan α
  | .source xs => .source xs
  | .map f p => pushMap f (normalize p)
  | .choice p q => appendPlan (normalize p) (normalize q)
  | .ap p q => .ap (normalize p) (normalize q)

/-- Normalization preserves exact rank order, including duplicate outputs. -/
theorem values_normalize (p : Plan α) : values (normalize p) = values p := by
  induction p with
  | source xs => rfl
  | map f p ih => simp [normalize, values_pushMap, ih, values]
  | choice p q ihp ihq => simp [normalize, values_appendPlan, ihp, ihq, values]
  | ap p q ihp ihq => simp [normalize, values, ihp, ihq]

/-- Normalization preserves all cardinality metadata. -/
theorem count_normalize (p : Plan α) : count (normalize p) = count p := by
  simp only [count_correct, values_normalize]

/-- The normalized decoder returns exactly the same result at every rank. -/
theorem decode_normalize (p : Plan α) (rank : Nat) :
    decode (normalize p) rank = decode p rank := by
  simp only [decode_correct, values_normalize]

/-- Normalization preserves every weighted replay distribution, not only uniform ranks. -/
theorem normalization_preserves_weighted_replay (p : Plan α)
    (ranks : Probability.Distribution Nat) :
    Probability.map (decode (normalize p)) ranks = Probability.map (decode p) ranks := by
  simp [Probability.map, decode_normalize]

/-- A right radix of one eliminates quotient/remainder in an application. -/
theorem decode_single_argument (p : Plan (α → β)) (q : Plan α)
    (hq : count q = 1) (rank : Nat) (hr : rank < count p) :
    decode (.ap p q) rank = (decode p rank).bind (fun f => (decode q 0).map f) := by
  simp [decode, hq, hr, Nat.mod_one]

/-- A single function eliminates its rank selection in an application. -/
theorem decode_single_function (p : Plan (α → β)) (q : Plan α)
    (hp : count p = 1) (rank : Nat) (hr : rank < count q) :
    decode (.ap p q) rank = (decode p 0).bind (fun f => (decode q rank).map f) := by
  simp [decode, hp, hr, Nat.div_eq_of_lt hr, Nat.mod_eq_of_lt hr]

/-- Fuse two applications into one decoder with two quotient/remainder steps. -/
theorem decode_binary_fusion (p : Plan (α → β → γ)) (x : Plan α) (y : Plan β)
    (rank : Nat) (hr : rank < count p * count x * count y) :
    decode (.ap (.ap p x) y) rank =
      (decode p ((rank / count y) / count x)).bind (fun f =>
        (decode x ((rank / count y) % count x)).bind (fun a =>
          (decode y (rank % count y)).map (f a))) := by
  have hy : 0 < count y := by
    by_cases hz : count y = 0
    · simp [hz] at hr
    · omega
  have hi : rank / count y < count p * count x :=
    (Nat.div_lt_iff_lt_mul hy).mpr hr
  simp only [decode, count, ite_eq_left hr, ite_eq_left hi]
  cases decode p ((rank / count y) / count x) <;>
    cases decode x ((rank / count y) % count x) <;>
    cases decode y (rank % count y) <;> rfl

/-- A single binary function needs only the argument-pair split. -/
theorem decode_binary_single_function (p : Plan (α → β → γ))
    (x : Plan α) (y : Plan β) (hp : count p = 1)
    (rank : Nat) (hr : rank < count x * count y) :
    decode (.ap (.ap p x) y) rank =
      (decode p 0).bind (fun f => (decode x (rank / count y)).bind (fun a =>
        (decode y (rank % count y)).map (f a))) := by
  have hr' : rank < count p * count x * count y := by simpa [hp] using hr
  rw [decode_binary_fusion p x y rank hr']
  have hi : rank / count y < count x :=
    (MicroCFTA.Probability.split_lt hr).1
  rw [Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]

/-- Merge a finite list of branches in their original order. -/
def choices : List (Plan α) → Plan α
  | [] => .source []
  | p :: ps => .choice p (choices ps)

/-- Ordered choice compilation retains the concatenated branch lists. -/
theorem values_choices (ps : List (Plan α)) :
    values (choices ps) = ps.flatMap values := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [choices, values, ih]

/-- Count ordered choices by summing their branch cardinalities. -/
theorem count_choices (ps : List (Plan α)) : count (choices ps) = (ps.map count).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [choices, count, ih]

/-- Build the Cartesian product of child plans without enumerating its members. -/
def childPlans (planOf : State → Plan α) : List State → Plan (List α)
  | [] => .source [[]]
  | q :: qs => .ap (.map List.cons (planOf q)) (childPlans planOf qs)

/-- Applicative child compilation retains the ordered Cartesian product. -/
theorem values_childPlans (planOf : State → Plan α) (qs : List State) :
    values (childPlans planOf qs) = Language.products (fun q => values (planOf q)) qs := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    simp [childPlans, values, ih, applyValues, Language.products, List.flatMap_map]

/-- Child counts multiply, including the one empty tuple of a nullary edge. -/
theorem count_childPlans (planOf : State → Plan α) (qs : List State) :
    count (childPlans planOf qs) = (qs.map fun q => count (planOf q)).prod := by
  induction qs with
  | nil => rfl
  | cons q qs ih => simp [childPlans, count, ih]

/-- Compile a plain automaton to a finite plan at a height bound. -/
def compileAt (A : Language.Automaton State Symbol) : Nat → State → Plan (Language.Term Symbol)
  | 0, _ => .source []
  | fuel + 1, q => choices ((A q).map fun edge =>
      .map (Language.Term.node edge.label) (childPlans (compileAt A fuel) edge.children))

/-- The plain counter sums transition counts and multiplies child counts. -/
def countAt (A : Language.Automaton State Symbol) : Nat → State → Nat
  | 0, _ => 0
  | fuel + 1, q => ((A q).map fun edge =>
      (edge.children.map (countAt A fuel)).prod).sum

/-- A plain graph has no filtering guards. -/
def Plain (A : Language.Automaton State Symbol) : Prop :=
  ∀ q, ∀ edge ∈ A q, ∀ term, edge.guard term = true

/-- The compiled plan uses exactly the dynamic counting recurrence. -/
theorem count_compileAt (A : Language.Automaton State Symbol) (fuel : Nat) (q : State) :
    count (compileAt A fuel q) = countAt A fuel q := by
  induction fuel generalizing q with
  | zero => rfl
  | succ fuel ih =>
    simp [compileAt, count_choices, List.map_map, Function.comp_def, count, count_childPlans, ih, countAt]

/-- Compiling a plain graph preserves every replay position of bounded enumeration. -/
theorem values_compileAt (A : Language.Automaton State Symbol) (plain : Plain A)
    (fuel : Nat) (q : State) :
    values (compileAt A fuel q) = Language.enumerate A fuel q := by
  induction fuel generalizing q with
  | zero => rfl
  | succ fuel ih =>
    simp only [compileAt, values_choices, List.flatMap_map, values, values_childPlans, ih,
      Language.enumerate]
    apply congrArg List.flatten
    apply List.map_congr_left
    intro edge he
    symm
    apply List.filter_eq_self.mpr
    intro term _
    exact plain q edge he term

/-- The optimized plain counter equals the number of bounded accepting runs. -/
theorem countAt_correct (A : Language.Automaton State Symbol) (plain : Plain A)
    (fuel : Nat) (q : State) :
    countAt A fuel q = (Language.enumerate A fuel q).length := by
  rw [← count_compileAt, count_correct, values_compileAt A plain]

/-- Compiled rank decoding agrees with the reference enumerator at every rank. -/
theorem decode_compileAt (A : Language.Automaton State Symbol) (plain : Plain A)
    (fuel : Nat) (q : State) (rank : Nat) :
    decode (normalize (compileAt A fuel q)) rank = (Language.enumerate A fuel q)[rank]? := by
  rw [decode_normalize, decode_correct, values_compileAt A plain]

/-- Every bounded accepted term is reachable by the normalized counted decoder. -/
theorem compiled_coverage (A : Language.Automaton State Symbol) (plain : Plain A)
    (fuel : Nat) (q : State) (term : Language.Term Symbol) :
    (∃ rank, rank < countAt A fuel q ∧
      decode (normalize (compileAt A fuel q)) rank = some term) ↔
      Language.Accepts A q term ∧ term.height ≤ fuel := by
  rw [← Language.mem_enumerate_iff]
  constructor
  · rintro ⟨rank, _, hr⟩
    rw [decode_compileAt A plain] at hr
    exact List.mem_of_getElem? hr
  · intro hm
    obtain ⟨rank, hr⟩ := List.mem_iff_getElem?.mp hm
    exact ⟨rank, by rw [countAt_correct A plain]; exact (List.getElem?_eq_some_iff.mp hr).1,
      by simpa [decode_compileAt A plain] using hr⟩

/-- Plan compilation and normalization preserve every finite event probability. -/
theorem compiled_probability (A : Language.Automaton State Symbol) (plain : Plain A)
    (fuel : Nat) (q : State) (event : Language.Term Symbol → Bool) :
    Probability.eventMass event
        (Probability.normalize (Probability.counting (values (normalize (compileAt A fuel q))))) =
      ((Language.enumerate A fuel q).countP event : Rat) /
        (Language.enumerate A fuel q).length := by
  rw [values_normalize, values_compileAt A plain]
  exact Probability.uniform_event_probability event (Language.enumerate A fuel q)

/-- A compiled plan with an accepted bounded term defines a probability distribution. -/
theorem compiled_probability_normalized (A : Language.Automaton State Symbol) (plain : Plain A)
    (fuel : Nat) (q : State) (term : Language.Term Symbol)
    (ha : Language.Accepts A q term) (hh : term.height ≤ fuel) :
    Probability.IsProbability
      (Probability.normalize (Probability.counting (values (normalize (compileAt A fuel q))))) := by
  rw [values_normalize, values_compileAt A plain]
  apply Probability.uniform_probability
  have hm := (Language.mem_enumerate_iff A fuel q term).mpr ⟨ha, hh⟩
  exact List.length_pos_iff_exists_mem.mpr ⟨term, hm⟩

end MicroCFTA.Decoder
