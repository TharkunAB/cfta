import MicroCFTA.SourceSynthesisNativeTypeClassPass
import MicroCFTA.SourceSynthesisNativeTypeEditWorker
import MicroCFTA.SourceCurrentAllocatedClassWorker

/-!
# Type facts at actual class worker returns

Successful class returns derive their literal edit graphs from Type facts
and reached physical range checks. The right fold enters each head with
the actual tail's warm state and transported routes. No language inventory
or completed class graph is an input. Success and range checks remain
explicit. These laws do not establish completion or failed-prefix facts.
-/
namespace MicroCFTA.SourceSynthesisNativeTypeClassWorker
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceSynthesisTypeSyntax (Library)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceCurrentHereditaryTypePaths (ForestPath)
open SourceCurrentHereditaryTypeRouteConstructors (ForestRoutes)
open SourceCurrentAllocatedSharedTargetState (initial)
open SourceCurrentAllocatedClassEdits (Class ClassRanges)
open SourceCurrentAllocatedClassPass (Fold Pass Ranges)
open SourceRecursiveIntersectionKernel (Extension)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Ready" => SourceSynthesisNativeTypeSharedState.Ready
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

private theorem class_graph (lib : Library) (e p h m s n : Nat)
    {record values results} {before after : Checked width} {memo saved : Memo}
    (ready : Ready lib (initial before memo)) (available : Values before.native.machine.heap values)
    (closed : ClosedValues values) (coherent : SourceEqualityClassOrder.Coherent record)
    (routes : ∀ path ∈ record.paths, ForestPath (Origin lib) (path.map Int.ofNat) values)
    (ranges : ClassRanges record values before memo)
    (done : SourceCurrentAllocatedClassWorker.runClass e p h m s n record values before memo =
      .done results after saved) : Class record values before memo results after saved := by
  cases actual : SourceCurrentAllocatedSharedEditWorker.editList
      (SourceCurrentAllocatedSharedEditWorker.edit record values e p h m s n)
      (SourceCurrentAllocatedClassEditPlan.compiled record) values (initial before memo) with
  | failed =>
      simp only [SourceCurrentAllocatedClassWorker.runClass, actual] at done
      cases done
  | done outputs shared =>
      simp only [SourceCurrentAllocatedClassWorker.runClass, actual] at done
      cases done
      have lower := SourceSynthesisNativeTypeEditWorker.list lib e p h m s n ready available closed routes
        (SourceCurrentAllocatedClassEditPlan.compiled_populated record) available closed
        (SourceCurrentHereditaryTypeEditPlan.compiled_forest_paths (Origin lib) record coherent values routes)
        ranges actual
      exact .edit lower.1

private theorem fold_graph (lib : Library) (e p h m s n : Nat)
    {records values results} {before after : Checked width} {memo saved : Memo}
    (ready : Ready lib (initial before memo)) (available : Values before.native.machine.heap values)
    (closed : ClosedValues values)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (routes : ∀ record ∈ records, ∀ path ∈ record.paths,
      ForestPath (Origin lib) (path.map Int.ofNat) values)
    (ranges : Ranges records values before memo)
    (done : SourceCurrentAllocatedClassWorker.fold e p h m s n records values before memo =
      .done results after saved) : Fold records values before memo results after saved := by
  induction records generalizing results after saved with
  | nil => cases done; exact .nil
  | cons record records ih =>
      cases ranges with
      | cons tail head =>
          cases stepped : SourceCurrentAllocatedClassWorker.fold e p h m s n records values before memo with
          | failed =>
              simp only [SourceCurrentAllocatedClassWorker.fold, stepped,
                SourceCurrentAllocatedClassWorker.Outcome.bind] at done
              cases done
          | done middle next current =>
              simp only [SourceCurrentAllocatedClassWorker.fold, stepped,
                SourceCurrentAllocatedClassWorker.Outcome.bind] at done
              have tailCoherent := fun own member => coherent own (List.mem_cons_of_mem record member)
              have tailRoutes := fun own member => routes own (List.mem_cons_of_mem record member)
              have first := ih (results := middle) (after := next) (saved := current)
                tailCoherent tailRoutes tail stepped
              obtain ⟨currentReady, _, currentAvailable, currentClosed, retained⟩ :=
                SourceSynthesisNativeTypeClassPass.fold lib first ready available closed tailCoherent tailRoutes
              have last := class_graph lib e p h m s n currentReady currentAvailable currentClosed
                (coherent record List.mem_cons_self)
                (fun path member => retained (path.map Int.ofNat) (routes record List.mem_cons_self path member))
                (head middle next current first) done
              exact .cons first last

/-- A literal class return derives its graph and all returned Type-state facts. -/
theorem class_edit (lib : Library) (e p h m s n : Nat)
    {record values results} {before after : Checked width} {memo saved : Memo}
    (ready : Ready lib (initial before memo)) (available : Values before.native.machine.heap values)
    (closed : ClosedValues values) (coherent : SourceEqualityClassOrder.Coherent record)
    (routes : ∀ path ∈ record.paths, ForestPath (Origin lib) (path.map Int.ofNat) values)
    (ranges : ClassRanges record values before memo)
    (done : SourceCurrentAllocatedClassWorker.runClass e p h m s n record values before memo =
      .done results after saved) :
    Class record values before memo results after saved ∧ Ready lib (initial after saved) ∧
      Extension before.native.machine after.native.machine ∧ Values after.native.machine.heap results ∧
      ClosedValues results ∧ ForestRoutes (Origin lib) values results := by
  have graph := class_graph lib e p h m s n ready available closed coherent routes ranges done
  exact ⟨graph, SourceSynthesisNativeTypeClassPass.class_edit lib graph ready available closed coherent routes⟩

/-- Each executable head class uses the exact tail return and its transported routes. -/
theorem fold (lib : Library) (e p h m s n : Nat)
    {records values results} {before after : Checked width} {memo saved : Memo}
    (ready : Ready lib (initial before memo)) (available : Values before.native.machine.heap values)
    (closed : ClosedValues values)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (routes : ∀ record ∈ records, ∀ path ∈ record.paths,
      ForestPath (Origin lib) (path.map Int.ofNat) values)
    (ranges : Ranges records values before memo)
    (done : SourceCurrentAllocatedClassWorker.fold e p h m s n records values before memo =
      .done results after saved) :
    Fold records values before memo results after saved ∧ Ready lib (initial after saved) ∧
      Extension before.native.machine after.native.machine ∧ Values after.native.machine.heap results ∧
      ClosedValues results ∧ ForestRoutes (Origin lib) values results := by
  have graph := fold_graph lib e p h m s n ready available closed coherent routes ranges done
  exact ⟨graph, SourceSynthesisNativeTypeClassPass.fold lib graph ready available closed coherent routes⟩

/-- A literal full pass derives its graph, warm state and final propagated Type routes. -/
theorem pass (lib : Library) (e p h m s n : Nat)
    {records values results} {before after : Checked width} {memo saved : Memo}
    (ready : Ready lib (initial before memo)) (available : Values before.native.machine.heap values)
    (closed : ClosedValues values)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (routes : ∀ record ∈ records, ∀ path ∈ record.paths,
      ForestPath (Origin lib) (path.map Int.ofNat) values)
    (ranges : Ranges records values before memo)
    (done : SourceCurrentAllocatedClassWorker.pass e p h m s n records values before memo =
      .done results after saved) :
    Pass records values before memo results after saved ∧ Ready lib (initial after saved) ∧
      Extension before.native.machine after.native.machine ∧ Values after.native.machine.heap results ∧
      ClosedValues results ∧ ForestRoutes (Origin lib) values results := by
  cases stepped : SourceCurrentAllocatedClassWorker.fold e p h m s n records values before memo with
  | failed =>
      simp only [SourceCurrentAllocatedClassWorker.pass, stepped,
        SourceCurrentAllocatedClassWorker.Outcome.bind] at done
      cases done
  | done middle next current =>
      simp only [SourceCurrentAllocatedClassWorker.pass, stepped,
        SourceCurrentAllocatedClassWorker.Outcome.bind] at done
      cases done
      have graph : Pass records values before memo
          (EqualityLeafProjectionRuntimeEmpty.propagate middle) after saved :=
        .done (fold_graph lib e p h m s n ready available closed coherent routes ranges stepped)
      exact ⟨graph, SourceSynthesisNativeTypeClassPass.pass lib graph ready available closed coherent routes⟩

end MicroCFTA.SourceSynthesisNativeTypeClassWorker
