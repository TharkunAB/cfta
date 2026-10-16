import MicroCFTA.SourceCurrentAllocatedScanWorkerStability

namespace MicroCFTA.ScanStabilityIndependentKernels
open Language EqualityNormalize InternedConstructorTemplates
open SourceCurrentAllocatedScanWorker
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- Primary false selects the class without using any query or decision bound. -/
theorem selected_singleton_ignores_query_bounds (g s budget : Nat) (values : List (Value Symbol Guard))
    (paths : Class) (before middle : Checked width) (memo : Memo)
    (primary : gate true g values paths before memo = .done false middle memo) :
    scan g s 0 0 0 budget values [paths] before memo = .done (none, [paths]) middle memo := by
  simp only [scan, primary, Outcome.bind, Bool.false_eq_true, ite_false, Outcome.select]

/-- Secondary true skips both lower phases at zero projection, read, and native bounds. -/
theorem secondary_skip_ignores_query_bounds (g s budget : Nat) (values : List (Value Symbol Guard))
    (paths : Class) (before middle later : Checked width) (memo : Memo)
    (primary : gate true g values paths before memo = .done true middle memo)
    (secondary : gate false s values paths middle memo = .done true later memo) :
    scan g s 0 0 0 budget values [paths] before memo = .done (none, []) later memo := by
  simp only [scan, primary, secondary, Outcome.bind, ite_true]

/-- A true answer stops before an arbitrary remaining class suffix. -/
theorem true_answer_skips_suffix (g s p h n budget : Nat) (values : List (Value Symbol Guard))
    (paths : Class) (classes : Constraints) (before middle later checked after : Checked width)
    (memo saved : Memo) (value : Value Symbol Guard)
    (primary : gate true g values paths before memo = .done true middle memo)
    (secondary : gate false s values paths middle memo = .done false later memo)
    (projected : query p h n values paths later memo = .done value checked memo)
    (decided : decision p h budget paths value checked memo = .done true after saved) :
    scan g s p h n budget values (paths :: classes) before memo = .done (some paths, []) after saved := by
  simp only [scan, primary, secondary, projected, decided, Outcome.bind, Bool.false_eq_true, ite_false, ite_true]

/-- A false answer runs the suffix at the exact decision state and saved fourth memo. -/
theorem false_answer_continues_exact_state (g s p h n budget : Nat) (values : List (Value Symbol Guard))
    (paths : Class) (classes : Constraints) (before middle later checked after final : Checked width)
    (memo current saved : Memo) (value : Value Symbol Guard) (result : Result)
    (primary : gate true g values paths before memo = .done true middle memo)
    (secondary : gate false s values paths middle memo = .done false later memo)
    (projected : query p h n values paths later memo = .done value checked memo)
    (decided : decision p h budget paths value checked memo = .done false after current)
    (rest : scan g s p h n budget values classes after current = .done result final saved) :
    scan g s p h n budget values (paths :: classes) before memo = .done result final saved := by
  simp only [scan, primary, secondary, projected, decided, Outcome.bind, Bool.false_eq_true, ite_false, ite_true, rest]

/-- Selection records the literal failed head occurrence and retains its reached state. -/
theorem failed_selected_suffix_retains_prefix (g s p h n budget : Nat) (values : List (Value Symbol Guard))
    (paths : Class) (classes : Constraints) (before middle after : Checked width) (memo saved : Memo) (fault : Fault width)
    (primary : gate true g values paths before memo = .done false middle memo)
    (rest : scan g s p h n budget values classes middle memo = .failed fault after saved) :
    scan g s p h n budget values (paths :: classes) before memo = .failed (.selected paths fault) after saved := by
  simp only [scan, primary, rest, Outcome.bind, Bool.false_eq_true, ite_false, Outcome.select]

/-- Independent successful bounds identify stopped paths, selected multiplicities, and complete caches. -/
theorem different_bounds_identify_every_result_field
    {g s p h n G S P H N budget : Nat} {values : List (Value Symbol Guard)} {classes : Constraints}
    {before after later : Checked width} {memo saved current : Memo} {first second : Result}
    (one : scan g s p h n budget values classes before memo = .done first after saved)
    (two : scan G S P H N budget values classes before memo = .done second later current) :
    first.1 = second.1 ∧ first.2 = second.2 ∧ after.operations = later.operations ∧
      after.native.nodes = later.native.nodes ∧ after.native.edges = later.native.edges ∧
      after.native.machine.domains = later.native.machine.domains ∧ saved = current := by
  obtain ⟨rfl, rfl, rfl⟩ := SourceCurrentAllocatedScanWorkerStability.scan_done_unique one two
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end MicroCFTA.ScanStabilityIndependentKernels
