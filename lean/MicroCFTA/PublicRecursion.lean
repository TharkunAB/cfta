import MicroCFTA.MinimumWitness
import MicroCFTA.OccurrenceGuard

/-!
# Recursive source metadata and public dispatch

The typed recursive body computes the same minimum and occurrence flags as
the source probe. The public result keeps unused finite bodies separate from
unguarded and empty recursive errors. Successful recursive records compose
the language, rank, and probability theorems.
-/

namespace MicroCFTA.PublicRecursion
open RecursiveSource

/-- Erase values while preserving all metadata operations read by the recursive probe. -/
def shape (token : Nat) : Recipe Root α → Option Nat → OccurrenceGuard.Shape
  | .finite source, _ => .source (SourceMinimum.minimum source).toList
  | .occurrence, assumed => .occurrence token assumed
  | .map _ inner, assumed => .map (shape token inner assumed)
  | .pay inner, assumed => .pay (shape token inner assumed)
  | .choice left right, assumed => .choice (shape token left assumed) (shape token right assumed)
  | .ap functions arguments, assumed => .product (shape token functions assumed) (shape token arguments assumed)

/-- Value erasure retains the exact minimum field, including an absent finite minimum. -/
theorem shape_minimum (token : Nat) (recipe : Recipe Root α) (assumed : Option Nat) :
    (OccurrenceGuard.summary (shape token recipe assumed)).minimum = minimum recipe assumed := by
  induction recipe with
  | finite source =>
      change (SourceMinimum.minimum source).toList.min? = SourceMinimum.minimum source
      cases SourceMinimum.minimum source <;> rfl
  | occurrence => rfl
  | map transform inner ih => exact ih
  | pay inner ih =>
      simp [shape, OccurrenceGuard.summary, minimum, minimumExpr, RecursionProbe.evaluate] at ih ⊢
      exact congrArg (fun n => n.map (· + 1)) ih
  | choice left right ihl ihr =>
      simp [shape, OccurrenceGuard.summary, ihl, ihr, minimum, minimumExpr, RecursionProbe.evaluate]
  | ap functions arguments ihf iha =>
      simp [shape, OccurrenceGuard.summary, ihf, iha, minimum, minimumExpr, RecursionProbe.evaluate]

/-- The actual size occurrence flags agree with the guard used in recursive completeness. -/
theorem size_guard_exact (token : Nat) (recipe : Recipe Root α) (assumed : Option Nat) :
    guarded recipe assumed = true ↔ token ∉ (OccurrenceGuard.summary (shape token recipe assumed)).unguarded := by
  induction recipe with
  | finite source => simp [guarded, shape, OccurrenceGuard.summary]
  | occurrence => simp [guarded, shape, OccurrenceGuard.summary]
  | map transform inner ih => exact ih
  | pay inner ih => simp [guarded, shape, OccurrenceGuard.summary]
  | choice left right ihl ihr =>
      simp [guarded, shape, OccurrenceGuard.summary, OccurrenceGuard.union, Bool.and_eq_true, ihl, ihr]
  | ap functions arguments ihf iha =>
      by_cases leftZero : minimum functions assumed = some 0 <;>
        by_cases rightZero : minimum arguments assumed = some 0 <;>
        simp [guarded, shape, OccurrenceGuard.summary, OccurrenceGuard.union, OccurrenceGuard.beside,
          shape_minimum, leftZero, rightZero, Bool.and_eq_true, ihf, iha]

/-- Pay changes size but does not add an engine term node. Application adds one. -/
def termGuard : Recipe Root α → Bool
  | .finite _ => true
  | .occurrence => false
  | .map _ inner | .pay inner => termGuard inner
  | .choice left right => termGuard left && termGuard right
  | .ap _ _ => true

/-- The public term-growth flags correspond to the computed typed source guard. -/
theorem term_guard_exact (token : Nat) (recipe : Recipe Root α) (assumed : Option Nat) :
    termGuard recipe = true ↔ token ∉ (OccurrenceGuard.summary (shape token recipe assumed)).termless := by
  induction recipe with
  | finite source => simp [termGuard, shape, OccurrenceGuard.summary]
  | occurrence => simp [termGuard, shape, OccurrenceGuard.summary]
  | map transform inner ih | pay inner ih => exact ih
  | choice left right ihl ihr =>
      simp [termGuard, shape, OccurrenceGuard.summary, OccurrenceGuard.union, Bool.and_eq_true, ihl, ihr]
  | ap functions arguments ihf iha => simp [termGuard, shape, OccurrenceGuard.summary]

/-- Occurrences remain used even when an intermediate class is currently empty. -/
def used : Recipe Root α → Bool
  | .finite _ => false
  | .occurrence => true
  | .map _ inner | .pay inner => used inner
  | .choice left right | .ap left right => used left || used right

/-- The typed body reports exactly the source's syntactic occurrence reachability. -/
theorem used_exact (token : Nat) (recipe : Recipe Root α) (assumed : Option Nat) :
    used recipe = true ↔ token ∈ (OccurrenceGuard.summary (shape token recipe assumed)).used := by
  induction recipe with
  | finite source => simp [used, shape, OccurrenceGuard.summary]
  | occurrence => simp [used, shape, OccurrenceGuard.summary]
  | map transform inner ih | pay inner ih => exact ih
  | choice left right ihl ihr | ap left right ihl ihr =>
      simp [used, shape, OccurrenceGuard.summary, OccurrenceGuard.union, Bool.or_eq_true, ihl, ihr]

/-- This is the source's combined size and term-growth rejection test. -/
def unguarded (body : Recipe Root Root) : Bool := !(guarded body (assumption body) && termGuard body)

/-- The combined rejection test reads exactly the two source token sets. -/
theorem unguarded_exact (token : Nat) (body : Recipe Root Root) :
    unguarded body = true ↔
      token ∈ (OccurrenceGuard.summary (shape token body (assumption body))).unguarded ∨
      token ∈ (OccurrenceGuard.summary (shape token body (assumption body))).termless := by
  simp [unguarded]
  have size := size_guard_exact token body (assumption body)
  have term := term_guard_exact token body (assumption body)
  grind

/-- A body without its distinguished occurrence remains an ordinary finite source. -/
def close : Recipe Root α → Option (FiniteSource.Source α)
  | .finite source => some source
  | .occurrence => none
  | .map transform inner => (close inner).map (.map transform)
  | .pay inner => (close inner).map .pay
  | .choice left right => do
      let leftSource ← close left
      let rightSource ← close right
      pure (.choice 1 1 (by decide) (by decide) leftSource rightSource)
  | .ap functions arguments => do
      let functionSource ← close functions
      let argumentSource ← close arguments
      pure (.ap functionSource argumentSource)

/-- Finite closure fails exactly when the body uses its own recursive occurrence. -/
theorem close_none (recipe : Recipe Root α) : close recipe = none ↔ used recipe = true := by
  induction recipe with
  | finite source => simp [close, used]
  | occurrence => simp [close, used]
  | map transform inner ih | pay inner ih => simp [close, used, ih]
  | choice left right ihl ihr | ap left right ihl ihr =>
      cases leftFound : close left <;> cases rightFound : close right <;>
        simp_all [close, used]

/-- An unused recursive occurrence meets both guard tests independently of its assumed minimum. -/
theorem unused_guard (recipe : Recipe Root α) (assumed : Option Nat) (unused : used recipe = false) :
    guarded recipe assumed = true ∧ termGuard recipe = true := by
  induction recipe with
  | finite source => exact ⟨rfl, rfl⟩
  | occurrence => simp [used] at unused
  | map transform inner ih => exact ih unused
  | pay inner ih => exact ⟨rfl, (ih unused).2⟩
  | choice left right ihl ihr =>
      have parts := Bool.or_eq_false_iff.mp unused
      obtain ⟨leftSize, leftTerm⟩ := ihl parts.1
      obtain ⟨rightSize, rightTerm⟩ := ihr parts.2
      simp [guarded, termGuard, leftSize, rightSize, leftTerm, rightTerm]
  | ap functions arguments ihf iha =>
      have parts := Bool.or_eq_false_iff.mp unused
      obtain ⟨leftSize, _⟩ := ihf parts.1
      obtain ⟨rightSize, _⟩ := iha parts.2
      simp [guarded, termGuard, leftSize, rightSize]

/-- Closing an unused body preserves every exact-size member in its original order. -/
theorem close_members (recipe : Recipe Root α) (source : FiniteSource.Source α)
    (closed : close recipe = some source) (environment : Nat → List Root) (size : Nat) :
    FiniteSource.classMembers source size = values recipe environment size := by
  induction recipe generalizing size with
  | finite original =>
      have same : original = source := Option.some.inj closed
      exact same ▸ rfl
  | occurrence => simp [close] at closed
  | map transform inner ih =>
      cases found : close inner with
      | none => simp [close, found] at closed
      | some innerSource =>
          have same : FiniteSource.Source.map transform innerSource = source := by simpa [close, found] using closed
          subst source
          simp only [FiniteSource.classMembers, values, ih innerSource found size]
  | pay inner ih =>
      cases found : close inner with
      | none => simp [close, found] at closed
      | some innerSource =>
          have same : FiniteSource.Source.pay innerSource = source := by simpa [close, found] using closed
          subst source
          cases size <;> simp [FiniteSource.classMembers, values, ih innerSource found]
  | choice left right ihl ihr =>
      cases leftFound : close left with
      | none => simp [close, leftFound] at closed
      | some leftSource =>
          cases rightFound : close right with
          | none => simp [close, leftFound, rightFound] at closed
          | some rightSource =>
              have same : FiniteSource.Source.choice 1 1 (by decide) (by decide) leftSource rightSource = source :=
                by simpa [close, leftFound, rightFound] using closed
              subst source
              simp [FiniteSource.classMembers, values, ihl leftSource leftFound, ihr rightSource rightFound]
  | ap functions arguments ihf iha =>
      cases leftFound : close functions with
      | none => simp [close, leftFound] at closed
      | some leftSource =>
          cases rightFound : close arguments with
          | none => simp [close, leftFound, rightFound] at closed
          | some rightSource =>
              have same : FiniteSource.Source.ap leftSource rightSource = source := by simpa [close, leftFound, rightFound] using closed
              subst source
              simp [FiniteSource.classMembers, values, ihf leftSource leftFound, iha rightSource rightFound]

/-- The recursive body has no opacity or construction error after its typed inputs are validated. -/
inductive Result (Root : Type) where
  | finite (source : FiniteSource.Source Root)
  | unguarded
  | empty
  | recursive (minimum : Nat) (classes : Nat → SamplerReplay.Record Root)

/-- Preserve the source's unused-body, guard-error, empty-error, and successful-knot order. -/
def compile (body : Recipe Root Root) : Result Root :=
  match close body with
  | some source => .finite source
  | none => if unguarded body then .unguarded
      else match assumption body with
        | none => .empty
        | some minimum => .recursive minimum (family body)

/-- Public finite success occurs exactly when the body's occurrence can be removed. -/
theorem compile_finite (body : Recipe Root Root) (source : FiniteSource.Source Root) :
    compile body = .finite source ↔ close body = some source := by
  cases closed : close body with
  | some original => simp [compile, closed]
  | none =>
      cases guard : unguarded body <;> cases found : assumption body <;> simp [compile, closed, guard, found]

/-- A returned finite body's size classes retain exactly its independent derivations. -/
theorem compile_finite_class (body : Recipe Root Root) (source : FiniteSource.Source Root)
    (success : compile body = .finite source) (size : Nat) (value : Root) :
    value ∈ FiniteSource.classMembers source size ↔ Derives body body value size := by
  have closed := (compile_finite body source).mp success
  have unused : used body = false := by
    cases reached : used body with
    | false => rfl
    | true => have absent := (close_none body).mpr reached; rw [closed] at absent; contradiction
  have accepted := (unused_guard body (assumption body) unused).1
  have exactFamily := family_exact body accepted size value
  rw [family, record_values] at exactFamily
  rw [close_members body source closed]
  exact exactFamily

/-- Finite dispatch preserves source probability and decoder replay through the standard finite compiler. -/
theorem compile_finite_record (body : Recipe Root Root) (source : FiniteSource.Source Root)
    (success : compile body = .finite source) :
    used body = false ∧ SamplerReplay.LiveValid (FiniteSource.finite source) ∧
      (FiniteSource.finite source).sampling.values = FiniteSource.distribution source := by
  have closed := (compile_finite body source).mp success
  have unused : used body = false := by
    cases reached : used body with
    | false => rfl
    | true => have absent := (close_none body).mpr reached; rw [closed] at absent; contradiction
  exact ⟨unused, FiniteSource.finite_live source, FiniteSource.finite_distribution source⟩

/-- The public recursive error corresponds to actual occurrence flags, after unused bodies return. -/
theorem compile_unguarded (body : Recipe Root Root) :
    compile body = .unguarded ↔ used body = true ∧ unguarded body = true := by
  cases closed : close body with
  | some source =>
      have unused : used body ≠ true := by intro used; have := (close_none body).mpr used; rw [closed] at this; contradiction
      simp [compile, closed, unused]
  | none =>
      have reached := (close_none body).mp closed
      cases guard : unguarded body <;> cases found : assumption body <;> simp [compile, closed, reached, guard, found]

/-- An empty recursive error means exactly an accepted used body with no finite derivation. -/
theorem compile_empty (body : Recipe Root Root) :
    compile body = .empty ↔ used body = true ∧ unguarded body = false ∧
      ¬ ∃ value size, Derives body body value size := by
  rw [← MinimumWitness.assumption_none_exact]
  cases closed : close body with
  | some source =>
      have unused : used body ≠ true := by intro used; have := (close_none body).mpr used; rw [closed] at this; contradiction
      simp [compile, closed, unused]
  | none =>
      have reached := (close_none body).mp closed
      cases guard : unguarded body <;> cases minimum : assumption body <;> simp [compile, closed, reached, guard, minimum]

/-- Success retains the exact family and derives both accepted guards and the attained minimum. -/
theorem compile_recursive (body : Recipe Root Root) (minimum : Nat) (classes : Nat → SamplerReplay.Record Root) :
    compile body = .recursive minimum classes ↔ used body = true ∧ guarded body (assumption body) = true ∧
      termGuard body = true ∧ assumption body = some minimum ∧ classes = family body := by
  cases closed : close body with
  | some source =>
      have unused : used body ≠ true := by intro used; have := (close_none body).mpr used; rw [closed] at this; contradiction
      simp [compile, closed, unused]
  | none =>
      have reached := (close_none body).mp closed
      cases found : assumption body <;>
        cases sizeGuard : guarded body (assumption body) <;> cases termGuard : termGuard body <;>
        simp_all [compile, unguarded]
      intro _
      exact eq_comm

/-- A successful public knot has all and only the specified members and a coherent probability record. -/
theorem compile_recursive_exact (body : Recipe Root Root) (minimum : Nat) (classes : Nat → SamplerReplay.Record Root)
    (success : compile body = .recursive minimum classes) :
    (∃ value, Derives body body value minimum) ∧
      (∀ size, SamplerReplay.LiveValid (classes size)) ∧
      (∀ size value, value ∈ Decoder.values (classes size).plan ↔ Derives body body value size) ∧
      (∀ size, (classes size).sampling.values = classProbability body size) := by
  obtain ⟨_, sizeGuard, _, found, rfl⟩ := (compile_recursive body minimum classes).mp success
  exact ⟨MinimumWitness.assumption_attains body minimum found, family_live body,
    family_exact body sizeGuard, family_probability body⟩

/-- An actual application supplies both guards even when the recursive occurrence is not under pay. -/
def naturalBody : Recipe Nat Nat := .choice (.finite (.pure 0))
  (.ap (.finite (.source [(1, Nat.succ)] (by intro entry present; simp at present; subst entry; decide))) .occurrence)

/-- The public compiler accepts the positive-sibling recursive body and finds its size-zero base. -/
theorem naturalBody_compiles : compile naturalBody = .recursive 0 (family naturalBody) := by
  apply (compile_recursive naturalBody 0 (family naturalBody)).mpr
  exact ⟨rfl, by decide +kernel, rfl, by decide +kernel, rfl⟩

/-- Size growth alone still fails the public engine-term growth requirement. -/
theorem pay_only_error : compile (.pay .occurrence : Recipe Nat Nat) = .unguarded := by rfl

/-- Guarded recursion without a base has no finite terms and returns the explicit empty error. -/
theorem guarded_empty_error :
    compile (.ap (.finite (.source [(1, Nat.succ)]
      (by intro entry present; simp at present; subst entry; decide))) .occurrence : Recipe Nat Nat) = .empty := by rfl

end MicroCFTA.PublicRecursion
