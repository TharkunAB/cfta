import MicroCFTA.SourceEqualitySharedClassEdits
import MicroCFTA.SourceEqualityNativeTargetExamples

/-!
# Kernel checks for actual shared class target demand

Two original class paths visit four leaves across two-row nodes. First
force projects and merges the captured forest. Later row visits reuse the
same returned target. A repeated batch needs no target computation bounds.
-/
namespace MicroCFTA.SourceEqualitySharedEditExamples
open InternedConstructorTemplates InternedNestedConstruction SourceEqualitySharedTargetState
open SourceEqualitySharedTargetWorker SourceEqualitySharedEditWorker

/-- A nontrivial physical source class selects the first child of each original forest position. -/
def record : SourceEqualityClassOrder.Record :=
  ⟨.branch [(0, .branch [(0, .terminal)]), (1, .branch [(0, .terminal)])], [[0, 0], [1, 0]]⟩

/-- Both physical class fields represent the same canonical supported path set. -/
theorem record_coherent : SourceEqualityClassOrder.Coherent record := by
  refine ⟨?_, by cbv, ?_⟩
  · simp [record, EqualityTrie.Valid]
    intro index child member
    rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals
      constructor
      · intro impossible; cases impossible
      · simp [EqualityTrie.Valid]
  · intro path
    rfl

/-- Two original paths make this an active equality class. -/
theorem record_active : EqualityNormalize.Nontrivial record.paths := by
  simp [EqualityNormalize.Nontrivial, record]

/-- Shared cache hits return their exact stored value at zero target bounds. -/
theorem hit_zero (before : SourceEqualitySharedTargetState.State width Nat Unit) (path : EqualityNormalize.Path) (value : Value Nat Unit)
    (present : before.targets path = some value) :
    force () (fun _ _ => ()) (fun _ => true) () 0 0 0 0 record [] path before = .done value before := by
  simp only [force, present]

/-- Missing edit positions and ignored list-root callbacks force no target. -/
theorem ignored (before : SourceEqualitySharedTargetState.State width Nat Unit) :
    editAll () (fun _ _ => ()) (fun _ => true) () record [] 0 0 0 0 0 [([], [0, 0])] [.reference .depth] before = .done [.reference .depth] before ∧
    editAll () (fun _ _ => ()) (fun _ => true) () record [] 0 0 0 0 0 [([-1], [0, 0]), ([9], [1, 0])] [.reference .depth] before = .done [.reference .depth] before := ⟨rfl, rfl⟩

/-- Observe first force, reuse across rows, and later complete reuse at zero target bounds. -/
def SharedResults : Outcome Nat Unit (Value Nat Unit) → Prop
  | .pending .. => False
  | .done root heap => match root with
    | .node _ (edge :: _) _ _ =>
        let constant := edge.children.headD .empty
        let originals := [root, root]
        let before := initial (SourceRecursiveIntersectionThunks.initial 8 ⟨heap, Cache.emptyState⟩)
        let edits := SourceEqualityClassEdits.edits record.paths id
        match editAll () (fun _ _ => ()) (fun _ => true) () record originals 2 2 0 0 16 edits originals before with
        | .done values after => values = originals ∧ after.native.machine.heap = heap ∧ after.native.nodes.next = 1 ∧ after.native.edges.next = 0 ∧
            after.targets [0, 0] = some constant ∧ after.targets [1, 0] = some constant ∧
            force () (fun _ _ => ()) (fun _ => true) () 0 0 0 0 record originals [0, 0] after = .done constant after ∧
            force () (fun _ _ => ()) (fun _ => true) () 0 0 0 0 record originals [1, 0] after = .done constant after ∧
            editAll () (fun _ _ => ()) (fun _ => true) () record originals 2 0 0 0 16 edits originals after = .done originals after
        | _ => False
    | _ => False

/-- Four physical leaves share two first-forced targets and one warm native memo cell. -/
theorem first_force_and_row_reuse : SharedResults (InternedFreshOrdinaryConstruction.build
    (.node [.mk 31 () [.node [.mk 11 () []]], .mk 32 () [.node [.mk 11 () []]]]) [] empty) := by
  set_option maxRecDepth 20000 in
  set_option cbv.maxSteps 30000000 in cbv

end MicroCFTA.SourceEqualitySharedEditExamples
