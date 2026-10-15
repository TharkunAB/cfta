import MicroCFTA.SourceMergedSource

/-!
# Kernel checks for general repaired merging

The nested binder comparison allocates a new actual Mu record. This case
requires the general cache law. The ordinary examples check both sides
of the source four-row threshold and its exhausted recursion result.
-/
namespace MicroCFTA.SourceMergedExamples
open InternedConstructorTemplates InternedNestedConstruction

/-- The inner binder captures its outer binder and its own recursive name. -/
def nested : Syntax Nat Unit :=
  .binder false (.node [.mk 0 () [.binder false (.node [.mk 1 () [.var 1, .var 0]])]])

/-- Observe an actual distinct comparison that must expose the open nested binder. -/
def nestedObservation : Option (Bool × Bool) :=
  match InternedFreshOrdinaryConstruction.build nested [] empty with
  | .pending .. => none
  | .done wide state =>
      match InternedFreshOrdinaryConstruction.build (.node [.mk 2 () []]) [] state with
      | .pending .. => none
      | .done narrow before =>
          match MergedFreshOrdinaryComparison.check (fun _ => true) 8 [] wide narrow before with
          | .failed .. => none
          | .done answer after => some (answer, decide (before.nodes.next < after.nodes.next))

/-- The actual repaired comparison finishes and allocates a Mu record during its demanded read. -/
theorem nested_allocates : nestedObservation = some (false, true) := by
  set_option maxRecDepth 20000 in
  set_option cbv.maxSteps 30000000 in cbv

/-- Distinct child constants make each parent row a separate structural alternative. -/
def alternatives (count : Nat) : Syntax Nat Unit :=
  .node ((List.range count).map fun index => .mk 0 () [.node [.mk (index + 1) () []]])

/-- Observe the returned root arities and the exact ordinary recursion exhaustion branch. -/
def groupObservation (count : Nat) : Option (Nat × List Nat × Bool) :=
  match InternedFreshOrdinaryConstruction.build (alternatives count) [] empty with
  | .pending .. => none
  | .done value before =>
      match SourceMergedWorker.execute (fun _ => true) () 8 value before with
      | .failed .. => none
      | .done result _ =>
          match result with
          | .node _ edges _ _ => some (edges.length, edges.map (fun edge => edge.children.length),
              match SourceMergedWorker.worker MergedSourceGrouping.groups (fun _ => true) () 0 8 value before with
              | .failed .exhausted _ => true
              | _ => false)
          | _ => none

/-- Four rows keep their separate original edges; five rows use one merged column edge. -/
theorem threshold : groupObservation 4 = some (4, [1, 1, 1, 1], true) ∧
    groupObservation 5 = some (1, [1], true) := by
  set_option maxRecDepth 20000 in
  set_option cbv.maxSteps 30000000 in cbv
  unfold MergedColdMerge.retainedColumn
  set_option maxRecDepth 20000 in
  set_option cbv.maxSteps 30000000 in cbv

end MicroCFTA.SourceMergedExamples
