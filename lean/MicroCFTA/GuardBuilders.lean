import MicroCFTA.SourceGuards

/-!
# Source argument builders and transition checks

The standard recursive builder instances have a fixed number of arguments
in their Haskell type. Probe arguments determine only that count. Actual
construction supplies consecutive positions. Contract reach reads every
Holds atom, including atoms below negation and substitution.
-/
namespace MicroCFTA.GuardBuilders
open SourceGuards

/-- The standard builder instances retain their fixed function arity. -/
inductive Builder (Input Output : Type) : Nat → Type where
  | done (value : Output) : Builder Input Output 0
  | argument (next : Input → Builder Input Output count) : Builder Input Output (count + 1)

/-- Count arguments using the source's one repeated placeholder. -/
def arity (probe : Input) : Builder Input Output count → Nat
  | .done _ => 0
  | .argument next => 1 + arity probe (next probe)

/-- The placeholder cannot change the standard instances' fixed arity. -/
theorem arity_exact (probe : Input) (builder : Builder Input Output count) : arity probe builder = count := by
  induction builder with
  | done value => rfl
  | argument next ih => simp [arity, ih, Nat.add_comm]

/-- Raw guards have no arity requirement; a function guard has its full arity. -/
def guardArgumentCount (probe : Input) : Builder Input Output count → Option Nat
  | .done _ => none
  | .argument next => some (1 + (guardArgumentCount probe (next probe)).getD 0)

/-- The source optional arity probe agrees with the standard function shape. -/
theorem guardArgumentCount_exact (probe : Input) (builder : Builder Input Output count) :
    guardArgumentCount probe builder = if count = 0 then none else some count := by
  induction builder with
  | done value => rfl
  | @argument count next ih =>
      simp only [guardArgumentCount, ih]
      cases count <;> simp [Nat.add_comm]

/-- Apply one argument at each consecutive source position. -/
def buildFrom (argumentAt : Nat → Input) (index : Nat) : Builder Input Output count → Output
  | .done value => value
  | .argument next => buildFrom argumentAt (index + 1) (next (argumentAt index))

/-- An independent list application requires exactly the builder's argument count. -/
def applyArguments : Builder Input Output count → List Input → Option Output
  | .done value, [] => some value
  | .done _, _ :: _ => none
  | .argument _, [] => none
  | .argument next, first :: rest => applyArguments (next first) rest

/-- List application consumes exactly the positions supplied by buildFrom. -/
theorem buildFrom_arguments (argumentAt : Nat → Input) (index : Nat) (builder : Builder Input Output count) :
    applyArguments builder ((List.range' index count).map argumentAt) = some (buildFrom argumentAt index builder) := by
  induction builder generalizing index with
  | done value => rfl
  | argument next ih =>
      simpa [List.range'_succ, applyArguments, buildFrom] using ih (argumentAt index) (index + 1)

/-- Actual guard construction starts at child zero. -/
def argumentPath (index : Nat) : Path := [index]

/-- The builder's i-th supplied position is exactly child i plus the starting offset. -/
theorem supplied_path (start count index : Nat) (valid : index < count) :
    ((List.range' start count).map argumentPath)[index]? = some [start + index] := by
  simp [valid, argumentPath]

/-- Remove Boolean and substitution wrappers exactly as contractReach does. -/
def atoms : Guard Formula → List (Guard Formula)
  | .not inner | .substitute _ inner => atoms inner
  | .and parts | .or parts => parts.flatMap atoms
  | guard => [guard]

/-- Keep the complete ordered target lists from Holds atoms. -/
def targets (guard : Guard Formula) : List Path :=
  (atoms guard).flatMap fun atom => match atom with
    | .holds paths _ => paths
    | _ => []

/-- The source arity requirement reads only a target's first child index. -/
def indices (guard : Guard Formula) : List Nat := (targets guard).filterMap List.head?

/-- Every reported child index comes from an actual Holds target under any wrappers. -/
theorem indices_exact (guard : Guard Formula) (index : Nat) :
    index ∈ indices guard ↔ ∃ paths formula rest,
      Guard.holds paths formula ∈ atoms guard ∧ index :: rest ∈ paths := by
  simp only [indices, targets, List.mem_filterMap, List.mem_flatMap]
  constructor
  · rintro ⟨target, ⟨atom, present, found⟩, head⟩
    cases atom <;> try simp at found
    rename_i paths formula
    cases target with
    | nil => cases head
    | cons first rest =>
        have same : first = index := Option.some.inj head
        subst first
        exact ⟨paths, formula, rest, present, found⟩
  · rintro ⟨paths, formula, rest, present, found⟩
    exact ⟨index :: rest, ⟨.holds paths formula, present, found⟩, rfl⟩

/-- Compute the maximum of a nonempty index list from its first index. -/
def maximum (first : Nat) (rest : List Nat) : Nat := rest.foldl max first

/-- A maximum fits below a bound precisely when every contributing index does. -/
theorem maximum_lt (first bound : Nat) (rest : List Nat) :
    maximum first rest < bound ↔ first < bound ∧ ∀ index ∈ rest, index < bound := by
  induction rest generalizing first with
  | nil => simp [maximum]
  | cons index rest ih =>
      simp only [maximum, List.foldl_cons] at *
      rw [ih]
      simp only [Nat.max_lt, List.mem_cons, forall_eq_or_imp]
      constructor <;> intro h <;> simp_all

/-- One more than the largest Holds child index, or no named child. -/
def contractReach (guard : Guard Formula) : Option Nat :=
  match indices guard with
  | [] => none
  | first :: rest => some (maximum first rest + 1)

/-- The contract arity gate passes exactly when every named child is in range. -/
theorem reach_within (guard : Guard Formula) (children : Nat) :
    (∀ named, contractReach guard = some named → named ≤ children) ↔
      ∀ index ∈ indices guard, index < children := by
  cases found : indices guard with
  | nil => simp [contractReach, found]
  | cons first rest =>
      simpa [contractReach, found, Nat.succ_le_iff] using maximum_lt first children rest

/-- The source reports the actual child count and the conflicting requirement. -/
structure ArityMismatch where
  children : Nat
  supplied : Nat
  deriving DecidableEq, Repr

/-- Preserve function-arity error precedence before checking contract reach. -/
def transitionCheck (supplied : Option Nat) (children : Nat) (guard : Guard Formula) : Except ArityMismatch Unit :=
  match supplied with
  | some count =>
      if count ≠ children then .error ⟨children, count⟩
      else match contractReach guard with
        | some named => if children < named then .error ⟨children, named⟩ else .ok ()
        | none => .ok ()
  | none => match contractReach guard with
      | some named => if children < named then .error ⟨children, named⟩ else .ok ()
      | none => .ok ()

/-- Successful transition construction enforces both actual source arity conditions. -/
theorem transition_success (supplied : Option Nat) (children : Nat) (guard : Guard Formula) :
    transitionCheck supplied children guard = .ok () ↔
      (∀ count, supplied = some count → count = children) ∧
      (∀ index ∈ indices guard, index < children) := by
  rw [← reach_within]
  cases supplied with
  | none => cases reached : contractReach guard <;> simp [transitionCheck, reached] <;> omega
  | some count =>
      by_cases same : count = children
      · subst count
        cases reached : contractReach guard <;> simp [transitionCheck, reached] <;> omega
      · simp [transitionCheck, same]

/-- A function-arity mismatch wins even if the guard also has invalid contract paths. -/
theorem function_error_first (count children : Nat) (different : count ≠ children) (guard : Guard Formula) :
    transitionCheck (some count) children guard = .error ⟨children, count⟩ := by
  simp [transitionCheck, different]

/-- Raw Same and subtype paths impose no contract-specific constructor arity requirement. -/
theorem noncontract_paths (children : Nat) (left right : Path) :
    transitionCheck none children (Guard.same (Formula := Formula) left right) = .ok () ∧
      transitionCheck none children (Guard.entails (Formula := Formula) left right) = .ok () := by
  simp [transitionCheck, contractReach, indices, targets, atoms]

/-- Negation and substitution retain the exact contract reach checked by the source. -/
theorem wrapped_reach (guard : Guard Formula) (substitutions : List Substitution) :
    contractReach (.not guard) = contractReach guard ∧
      contractReach (.substitute substitutions guard) = contractReach guard := by
  simp [contractReach, indices, targets, atoms]

example : transitionCheck none 1 (Guard.not (.holds [[1]] ())) = .error ⟨1, 2⟩ := by cbv
example : transitionCheck (some 3) 1 (Guard.holds [[8]] ()) = .error ⟨1, 3⟩ := by cbv
example : buildFrom argumentPath 2 (.argument fun left => .argument fun right => .done (left, right)) =
    ([2], [3]) := rfl

end MicroCFTA.GuardBuilders
