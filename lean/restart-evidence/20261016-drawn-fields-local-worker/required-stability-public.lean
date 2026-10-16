import MicroCFTA.SourceEqualityRequiredWorkerStability
#print axioms MicroCFTA.SourceEqualityRequiredWorkerStability.head_done_stable
#check MicroCFTA.SourceEqualityRequiredWorkerStability.head_done_stable
#print axioms MicroCFTA.SourceEqualityRequiredWorkerStability.children_done_stable
#check MicroCFTA.SourceEqualityRequiredWorkerStability.children_done_stable
#print axioms MicroCFTA.SourceEqualityRequiredWorkerStability.rows_done_stable
#check MicroCFTA.SourceEqualityRequiredWorkerStability.rows_done_stable
#print axioms MicroCFTA.SourceEqualityRequiredWorkerStability.require_done_stable
#check MicroCFTA.SourceEqualityRequiredWorkerStability.require_done_stable
#print axioms MicroCFTA.SourceEqualityRequiredWorkerStability.children_require_done_stable
#check MicroCFTA.SourceEqualityRequiredWorkerStability.children_require_done_stable
#print axioms MicroCFTA.SourceEqualityRequiredWorkerStability.rows_require_done_stable
#check MicroCFTA.SourceEqualityRequiredWorkerStability.rows_require_done_stable
#print axioms MicroCFTA.SourceEqualityRequiredWorkerStability.requireAll_done_stable
#check MicroCFTA.SourceEqualityRequiredWorkerStability.requireAll_done_stable
#print axioms MicroCFTA.SourceEqualityRequiredWorkerStability.require_done_unique
#check MicroCFTA.SourceEqualityRequiredWorkerStability.require_done_unique
#print axioms MicroCFTA.SourceEqualityRequiredWorkerStability.children_require_done_unique
#check MicroCFTA.SourceEqualityRequiredWorkerStability.children_require_done_unique
#print axioms MicroCFTA.SourceEqualityRequiredWorkerStability.rows_require_done_unique
#check MicroCFTA.SourceEqualityRequiredWorkerStability.rows_require_done_unique
#print axioms MicroCFTA.SourceEqualityRequiredWorkerStability.requireAll_done_unique
#check MicroCFTA.SourceEqualityRequiredWorkerStability.requireAll_done_unique

namespace MicroCFTA.RequiredStabilityIndependentProbes
open InternedConstructorTemplates SourceEqualityNeeded SourceEqualityRequiredWorker
open SourceEqualityRequiredWorkerStability
variable [DecidableEq (EdgeKey Symbol Guard)]

-- An empty requirement list preserves unresolved children at zero worker and read bounds.
example (name : InternedBinderProtocol.Reference) (before : State Symbol Guard) :
    SourceEqualityRequiredExecution.requireAll 0 0 [] [.reference name, .empty] before =
      .done [.reference name, .empty] before := SourceEqualityRequiredExecution.requireAll_identity _ _ _ _

-- A completed empty node request remains literal under larger independent bounds.
example (name : InternedBinderProtocol.Reference) (before : State Symbol Guard) {r R h H : Nat}
    (enoughR : r + 1 ≤ R) (enoughH : h ≤ H) :
    require R H (.node []) (.reference name) before = .done (.reference name) before :=
  require_done_stable (identity r h (.reference name) before) enoughR enoughH

-- A rejected row requires no callback success, even at zero worker fuel.
example (entries : List (Int × Needed)) (edge : EdgeValue Symbol Guard) (before : State Symbol Guard)
    (rejected : fits (.node entries) edge.children.length = false) (R H : Nat) :
    rows (require R H) entries [edge] before = .done [] before := by
  have actual : rows (require 0 0) entries [edge] before = .done [] before := by
    simp only [rows, rejected, Bool.false_eq_true, ite_false]
  exact rows_require_done_stable actual (Nat.zero_le R) (Nat.zero_le H)

-- Selected node work changes its child while an unrelated unresolved sibling stays literal.
example {r h R H : Nat} (entries : List (Int × Needed)) (needed : Needed)
    (value result : Value Symbol Guard) (name : InternedBinderProtocol.Reference) (before middle : State Symbol Guard)
    (selected : SourceEqualityNeededMap.lookup (0 : Int) entries = some needed)
    (unselected : SourceEqualityNeededMap.lookup (1 : Int) entries = none)
    (actual : require r h needed value before = .done result middle)
    (enoughR : r ≤ R) (enoughH : h ≤ H) :
    children (require R H) entries 0 [value, .reference name] before = .done [result, .reference name] middle := by
  apply children_require_done_stable (r := r) (h := h) _ enoughR enoughH
  simp [children, selected, unselected, actual, Result.bind]

-- Row reconstruction retains its full raw guard and exact returned constructor heap.
example {r h R H : Nat} (entries : List (Int × Needed)) (edge : EdgeValue Symbol Guard)
    (values : List (Value Symbol Guard)) (result : EdgeValue Symbol Guard) (before middle after : State Symbol Guard)
    (matching : fits (.node entries) edge.children.length = true)
    (childrenDone : children (require r h) entries 0 edge.children before = .done values middle)
    (constructed : run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle = (result, after))
    (enoughR : r ≤ R) (enoughH : h ≤ H) :
    rows (require R H) entries [edge] before = .done [result] after := by
  apply rows_require_done_stable (r := r) (h := h) _ enoughR enoughH
  simp only [rows, matching, ite_true, childrenDone, Result.bind, work, constructed]

-- Independent successful source-entry bounds identify both returned forest and entire heap.
example {r h R H : Nat} {paths : List Path} {values first second : List (Value Symbol Guard)}
    {before after later : State Symbol Guard}
    (one : SourceEqualityRequiredExecution.requireAll r h paths values before = .done first after)
    (two : SourceEqualityRequiredExecution.requireAll R H paths values before = .done second later) :
    first = second ∧ after = later := requireAll_done_unique one two
end MicroCFTA.RequiredStabilityIndependentProbes
