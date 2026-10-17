import MicroCFTA.SourceCurrentRequiredWorkerNumeric
import MicroCFTA.SourceCurrentProjectionNumericReplay

/-!
# Uniform read replay for actual Required graphs

Each certificate records exact worker equations at one shared reader bound.
Ordinary nodes also retain the cheaper phase used after recursive Head.
The branch lemmas construct these laws from the same actual subgraphs.
-/
namespace MicroCFTA.SourceCurrentRequiredNumericReplay
open InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityNeeded SourceEqualityRequiredGraph SourceEqualityRequiredCache
open SourceEqualityRequiredWorker
open SourceCurrentRequiredWorkerNumeric (workFuel)
open SourceCurrentProjectionNumericReplay (HeadReady head_replay)
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

/-- Exact replay includes the ordinary phase that follows an actual Head. -/
def NodeReady (shared : Nat) {needed : Needed} {value result : Value Symbol Guard}
    {before after : State Symbol Guard} (_actual : RequireNode needed value before result after) : Prop :=
  (∀ worker reader, workFuel needed ≤ worker → shared ≤ reader →
    require worker reader needed value before = .done result after) ∧
  (Ordinary value → ∀ worker reader, 2 * sizeOf needed ≤ worker → shared ≤ reader →
    require worker reader needed value before = .done result after)

/-- An ordered child scan retains one common worker and reader bound. -/
def ChildrenReady (shared : Nat) {entries : List (Int × Needed)} {index : Nat}
    {values results : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (_actual : RequireChildren entries index values before results after) : Prop :=
  ∀ worker reader, 2 * sizeOf (Needed.node entries) - 1 ≤ worker → shared ≤ reader →
    children (require worker reader) entries index values before = .done results after

/-- Rejected and kept rows retain one common worker and reader bound. -/
def RowsReady (shared : Nat) {entries : List (Int × Needed)} {edges results : List (EdgeValue Symbol Guard)}
    {before after : State Symbol Guard} (_actual : RequireRows entries edges before results after) : Prop :=
  ∀ worker reader, 2 * sizeOf (Needed.node entries) - 1 ≤ worker → shared ≤ reader →
    rows (require worker reader) entries edges before = .done results after

/-- A larger common reader bound retains exact node replay. -/
theorem NodeReady.mono {first last : Nat} {needed : Needed} {value result : Value Symbol Guard}
    {before after : State Symbol Guard} {actual : RequireNode needed value before result after}
    (ready : NodeReady first actual) (increase : first ≤ last) : NodeReady last actual :=
  ⟨fun worker reader work read => ready.1 worker reader work (Nat.le_trans increase read),
    fun ordinary worker reader work read => ready.2 ordinary worker reader work (Nat.le_trans increase read)⟩

/-- A larger common reader bound retains exact ordered child replay. -/
theorem ChildrenReady.mono {first last : Nat} {entries : List (Int × Needed)} {index : Nat}
    {values results : List (Value Symbol Guard)} {before after : State Symbol Guard}
    {actual : RequireChildren entries index values before results after}
    (ready : ChildrenReady first actual) (increase : first ≤ last) : ChildrenReady last actual :=
  fun worker reader work read => ready worker reader work (Nat.le_trans increase read)

/-- A larger common reader bound retains exact row replay. -/
theorem RowsReady.mono {first last : Nat} {entries : List (Int × Needed)} {edges results : List (EdgeValue Symbol Guard)}
    {before after : State Symbol Guard} {actual : RequireRows entries edges before results after}
    (ready : RowsReady first actual) (increase : first ≤ last) : RowsReady last actual :=
  fun worker reader work read => ready worker reader work (Nat.le_trans increase read)

private theorem ordinary_pack {shared : Nat} {needed : Needed} {value result : Value Symbol Guard}
    {before after : State Symbol Guard} (actual : RequireNode needed value before result after)
    (done : ∀ worker reader, 2 * sizeOf needed ≤ worker → shared ≤ reader →
      require worker reader needed value before = .done result after) : NodeReady shared actual :=
  ⟨fun worker reader enough read => done worker reader (by unfold workFuel at enough; omega) read,
    fun _ => done⟩

/-- Empty requirements return before they inspect the input value. -/
theorem NodeReady.identity (shared : Nat) (value : Value Symbol Guard) (state : State Symbol Guard) :
    NodeReady shared (RequireNode.identity (value := value) (state := state)) := by
  apply ordinary_pack
  intro worker reader enough _
  have positive : 0 < sizeOf (Needed.node []) := by simp only [Needed.node.sizeOf_spec]; omega
  cases worker with
  | zero => omega
  | succ worker => rfl

/-- A nonempty requirement on Empty returns at the same state. -/
theorem NodeReady.empty (shared : Nat) {entries : List (Int × Needed)} (nonempty : entries ≠ [])
    (state : State Symbol Guard) : NodeReady shared (RequireNode.empty (state := state) nonempty) := by
  apply ordinary_pack
  intro worker reader enough _
  have positive : 0 < sizeOf (Needed.node entries) := by simp only [Needed.node.sizeOf_spec]; omega
  cases worker with
  | zero => omega
  | succ worker => simp only [require, List.isEmpty_iff, nonempty, ite_false]

/-- An actual ordinary node uses the certified row scan before reconstruction. -/
theorem NodeReady.ordinary {shared : Nat} {entries : List (Int × Needed)}
    {entry edges depth free before rebuilt middle result after}
    (nonempty : entries ≠ []) (actual : RequireRows (Symbol := Symbol) (Guard := Guard) entries edges before rebuilt middle)
    (built : run (makeNode rebuilt) middle = (result, after)) (ready : RowsReady shared actual) :
    NodeReady shared (RequireNode.ordinary (entry := entry) (depth := depth) (free := free) nonempty actual built) := by
  apply ordinary_pack
  intro worker reader enough readEnough
  have positive : 0 < sizeOf (Needed.node entries) := by simp only [Needed.node.sizeOf_spec]; omega
  cases worker with
  | zero => omega
  | succ worker =>
      have done := ready worker reader (by omega) readEnough
      simp only [require, List.isEmpty_iff, nonempty, ite_false, done, Result.bind, work, built]

/-- An actual recursive Head is followed by its certified ordinary phase. -/
theorem NodeReady.recursive {shared : Nat} {entries : List (Int × Needed)}
    {original exposed result : Value Symbol Guard} {before middle after : State Symbol Guard}
    (nonempty : entries ≠ []) (recursive : Recursive original)
    (head : SourceEqualityRequiredHead.Head original before exposed middle)
    (body : RequireNode (.node entries) exposed middle result after)
    (headReady : HeadReady shared head) (bodyReady : NodeReady shared body) :
    NodeReady shared (RequireNode.recursive nonempty recursive head body) := by
  constructor
  · intro worker reader enough readEnough
    cases worker with
    | zero => unfold workFuel at enough; omega
    | succ worker =>
        have headDone := head_replay headReady reader readEnough
        have bodyDone := bodyReady.2 headReady.ordinary worker reader (by unfold workFuel at enough; omega) readEnough
        cases original with
        | empty | reference | node => cases recursive
        | mu | union => simpa only [require, List.isEmpty_iff, nonempty, ite_false, headDone, Result.bind] using bodyDone
  · intro ordinary
    cases original <;> cases recursive <;> cases ordinary

/-- Empty child scans perform no work. -/
theorem ChildrenReady.nil (shared index : Nat) (entries : List (Int × Needed)) (state : State Symbol Guard) :
    ChildrenReady shared (RequireChildren.nil (entries := entries) (index := index) (state := state)) :=
  fun _ _ _ _ => rfl

/-- An unselected child is retained before the same ordered suffix. -/
theorem ChildrenReady.unselected {shared : Nat} {entries : List (Int × Needed)} {index : Nat}
    {value : Value Symbol Guard} {values results : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (absent : SourceEqualityNeededMap.lookup (index : Int) entries = none)
    (rest : RequireChildren entries (index + 1) values before results after) (ready : ChildrenReady shared rest) :
    ChildrenReady shared (RequireChildren.unselected (value := value) index absent rest) := by
  intro worker reader enough readEnough
  simp only [children, absent, ready worker reader enough readEnough, Result.bind]

/-- A selected child uses its strict subrequirement bound before the ordered suffix. -/
theorem ChildrenReady.selected {shared : Nat} {entries : List (Int × Needed)} {index : Nat} {needed : Needed}
    {value result : Value Symbol Guard} {values results : List (Value Symbol Guard)} {before middle after : State Symbol Guard}
    (found : SourceEqualityNeededMap.lookup (index : Int) entries = some needed)
    (first : RequireNode needed value before result middle)
    (rest : RequireChildren entries (index + 1) values middle results after)
    (firstReady : NodeReady shared first) (restReady : ChildrenReady shared rest) :
    ChildrenReady shared (RequireChildren.selected index found first rest) := by
  intro worker reader enough readEnough
  have member := SourceEqualityNeededMap.lookup_mem _ _ _ found
  have smaller := List.sizeOf_lt_of_mem member
  simp only [Prod.mk.sizeOf_spec] at smaller
  have firstDone := firstReady.1 worker reader (by
    unfold workFuel; simp only [Needed.node.sizeOf_spec] at enough; omega) readEnough
  simp only [children, found, firstDone, Result.bind, restReady worker reader enough readEnough]

/-- Empty row scans perform no work. -/
theorem RowsReady.nil (shared : Nat) (entries : List (Int × Needed)) (state : State Symbol Guard) :
    RowsReady shared (RequireRows.nil (entries := entries) (state := state)) := fun _ _ _ _ => rfl

/-- A rejected original row has no child or constructor work. -/
theorem RowsReady.rejected {shared : Nat} {entries : List (Int × Needed)} {edge : EdgeValue Symbol Guard}
    {edges results : List (EdgeValue Symbol Guard)} {before after : State Symbol Guard}
    (rejected : fits (.node entries) edge.children.length = false)
    (rest : RequireRows entries edges before results after) (ready : RowsReady shared rest) :
    RowsReady shared (RequireRows.rejected rejected rest) := by
  intro worker reader enough readEnough
  simpa only [rows, rejected, Bool.false_eq_true, ite_false] using ready worker reader enough readEnough

/-- A kept row rebuilds the exact original raw guard before its certified suffix. -/
theorem RowsReady.kept {shared : Nat} {entries : List (Int × Needed)} {edge result : EdgeValue Symbol Guard}
    {edges results : List (EdgeValue Symbol Guard)} {values : List (Value Symbol Guard)} {before middle afterEdge after : State Symbol Guard}
    (fits : SourceEqualityNeeded.fits (.node entries) edge.children.length = true)
    (child : RequireChildren entries 0 edge.children before values middle)
    (built : run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle = (result, afterEdge))
    (rest : RequireRows entries edges afterEdge results after)
    (childReady : ChildrenReady shared child) (restReady : RowsReady shared rest) :
    RowsReady shared (RequireRows.kept fits child built rest) := by
  intro worker reader enough readEnough
  simp only [rows, fits, ite_true, childReady worker reader enough readEnough, Result.bind, work, built,
    restReady worker reader enough readEnough]

/-- A certified actual node replays at the initial trie-only worker bound. -/
theorem node_replay {shared : Nat} {needed : Needed} {value result : Value Symbol Guard}
    {before after : State Symbol Guard} {actual : RequireNode needed value before result after}
    (ready : NodeReady shared actual) (worker reader : Nat) (enough : workFuel needed ≤ worker)
    (readEnough : shared ≤ reader) : require worker reader needed value before = .done result after :=
  ready.1 worker reader enough readEnough

end MicroCFTA.SourceCurrentRequiredNumericReplay
