import MicroCFTA.MergedFreshOrdinaryColdReplay

/-!
# Closed unfolding can allocate Mu records and increase cached depth

The actual repaired constructor builds two nested binders. The inner node
uses both arguments. Unfolding the closed outer result creates a new closed
Mu and increases cached depth. The cold reader still finishes. This is a
counterexample to two proposed measures, not to reader termination.
-/
namespace MicroCFTA.SourceColdUnfoldNewMuBoundary
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedConstruction (Syntax Outcome)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)

set_option maxRecDepth 30000
set_option maxHeartbeats 2000000

/-- The innermost node retains both lexical binder arguments. -/
def expression : Syntax Nat Unit :=
  .binder true (.binder true (.node [.mk 0 () [.var 1, .var 0]]))

/-- Retain the actual repaired source construction. -/
def built : Outcome Nat Unit (Value Nat Unit) :=
  InternedFreshOrdinaryConstruction.build expression [] empty

/-- Select the actual root. The pending alternative is excluded below. -/
def root : Value Nat Unit := match built with | .done value _ => value | .pending .. => .empty

/-- Retain the actual final source cache. -/
def source : State Nat Unit := built.state

/-- Execute the repaired cold unfolding in that exact cache. -/
def unfolded : Outcome Nat Unit (Value Nat Unit) :=
  InternedFreshOrdinaryStoredSubstitution.unfold root source

/-- Select the actual unfolding result. The pending alternative is excluded below. -/
def result : Value Nat Unit := match unfolded with | .done value _ => value | .pending .. => .empty

/-- Retain the actual final unfolding cache. -/
def final : State Nat Unit := unfolded.state

/-- Observe both depths, node counters, and closedness fields without cache function equality. -/
def observation : Option (Nat × Nat × Nat × Nat × Bool × Bool) :=
  match built, unfolded with
  | .done value before, .done target after =>
      some (value.depth, target.depth, before.nodes.next, after.nodes.next, value.free.isEmpty, target.free.isEmpty)
  | _, _ => none

set_option cbv.maxSteps 100000000 in
/-- Exact kernel evaluation derives successful closed construction and unfolding, with depth increasing from two to three. -/
theorem observed : observation = some (2, 3, 13, 17, true, true) := by cbv

/-- The actual repaired constructor returned the selected root and its exact cache. -/
theorem built_done : built = .done root source := by
  cases done : built with
  | done value state => simp only [root, source, done, Outcome.state]
  | pending key state =>
      have impossible := observed
      simp only [observation, done] at impossible
      cases impossible

/-- The actual repaired unfolding returned the selected result and its exact cache. -/
theorem unfolded_done : unfolded = .done result final := by
  cases done : unfolded with
  | done value state => simp only [result, final, done, Outcome.state]
  | pending key state =>
      have impossible := observed
      simp only [observation, built_done, done] at impossible
      cases impossible

/-- Actual construction supplies closed available input, complete semantic heaps, and payload coverage. -/
theorem source_verified : SemanticHeap source ∧ Covered [] source ∧ Available source root ∧ root.free = [] := by
  have built : InternedFreshOrdinaryConstruction.build expression [] empty = .done root source := built_done
  have available := InternedFreshOrdinaryFacts.closed_verified expression
  have fields := observed
  simp only [observation, built_done, unfolded_done, Option.some.injEq, Prod.mk.injEq] at fields
  exact ⟨SourceRecursiveIntersectionSemanticHeap.constructed expression root source built,
    InternedFreshOrdinaryCoverage.closed_covered expression root source built,
    available.result root source built, List.isEmpty_iff.mp fields.2.2.2.2.1⟩

/-- Actual unfolding retains complete semantic heaps, coverage, and its available closed result. -/
theorem final_verified : SemanticHeap final ∧ Covered [] final ∧ Available final result ∧ result.free = [] := by
  have initial := source_verified
  obtain ⟨value, after, done, context, heap, covered, available, _, _⟩ :=
    InternedFreshOrdinaryStoredSubstitution.unfold_complete_decoded root source initial.1.1 initial.2.2.1 initial.1.2 initial.2.1
  have equal := Outcome.done.inj (done.symm.trans unfolded_done)
  cases equal.1
  cases equal.2
  exact ⟨⟨context, heap⟩, covered, available,
    InternedFreshOrdinaryStoredSubstitution.unfold_closed root source initial.1.1 initial.2.2.1 initial.2.2.2 _ _ unfolded_done⟩

/-- Observe whether the returned Mu key was absent before actual unfolding. -/
def missing : Bool := match result with
  | .mu entry .. => (source.nodeRecords entry.key).isNone
  | _ => false

set_option cbv.maxSteps 100000000 in
/-- The newly returned Mu record was not in the original cache. -/
theorem missing_true : missing = true := by cbv

/-- The actual returned Mu has an absent original key and a resident final record. -/
theorem new_mu : ∃ entry body depth ordinary, result = .mu entry body depth ordinary ∧
    source.nodeRecords entry.key = none ∧ final.nodeRecords entry.key = some result := by
  have absent := missing_true
  have available := final_verified.2.2.1
  cases value : result with
  | empty | reference | node | union => simp only [missing, value, Bool.false_eq_true] at absent
  | mu entry body depth ordinary =>
      refine ⟨entry, body, depth, ordinary, rfl, ?_, ?_⟩
      · cases found : source.nodeRecords entry.key with
        | none => rfl
        | some stored => simp only [missing, value, found, Option.isNone, Bool.false_eq_true] at absent
      · rw [value] at available
        exact available.resident entry rfl

/-- General closed unfolding does not preserve the initial complete Mu inventory. -/
theorem not_noNewMu : ¬ InternedShallowHeap.NoNewMu source final := by
  intro unchanged
  obtain ⟨entry, body, depth, ordinary, same, absent, resident⟩ := new_mu
  have old := unchanged entry.key entry body depth ordinary (by simpa only [same] using resident)
  rw [absent] at old
  cases old

/-- Cached depth is not a decreasing measure for general closed cold unfolding. -/
theorem depth_increases : root.depth < result.depth := by
  have fields := observed
  simp only [observation, built_done, unfolded_done, Option.some.injEq, Prod.mk.injEq] at fields
  rw [fields.1, fields.2.1]
  decide

/-- Observe finite actual cold exposure independently of the failed measures. -/
def readObservation : Option (Nat × Nat) :=
  match MergedFreshOrdinaryExposure.nodeEdges 20 root source with
  | .done edges after => some (edges.length, after.nodes.next)
  | _ => none

set_option cbv.maxSteps 100000000 in
/-- The actual repaired reader completes despite Mu allocation and increased cached depth. -/
theorem read_finishes : readObservation = some (1, 18) := by cbv

end MicroCFTA.SourceColdUnfoldNewMuBoundary
