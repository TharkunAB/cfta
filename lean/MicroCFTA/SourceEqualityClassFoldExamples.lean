import MicroCFTA.SourceEqualitySelectedFoldSource
import MicroCFTA.SourceEqualitySharedEditExamples

/-!
# Kernel checks for source class order and final empty propagation

The rightmost class runs first. Each earlier class starts fresh target
slots over the returned forest and retains warm native tables. A repeated
class still needs its own first target demand. Final empty propagation
runs once after the fold and preserves the actual native state.
-/
namespace MicroCFTA.SourceEqualityClassFoldExamples
open InternedConstructorTemplates InternedNestedConstruction SourceEqualityClassFoldGraph SourceEqualityClassFoldWorker
open SourceEqualitySharedEditExamples (record)

/-- Two source classes run rightmost first and pass the exact returned forest and native state to the earlier class. -/
theorem right_fold (e p h c n : Nat) (first second : SourceEqualityClassOrder.Record)
    (values : List (Value Nat Unit)) (before : NativeState width Nat Unit) :
    fold () (fun _ _ => ()) (fun _ => true) () e p h c n [first, second] values before =
      (classEdit () (fun _ _ => ()) (fun _ => true) () e p h c n second values before).bind
        (fun current next => classEdit () (fun _ _ => ()) (fun _ => true) () e p h c n first current next) := rfl

/-- The empty class fold leaves mixed empty roots intact; only the final propagation erases the entire forest. -/
theorem final_propagation (before : NativeState width Nat Unit) :
    fold () (fun _ _ => ()) (fun _ => true) () 0 0 0 0 0 [] [.empty, .reference .depth] before = .done [.empty, .reference .depth] before ∧
    pass () (fun _ _ => ()) (fun _ => true) () 0 0 0 0 0 [] [.empty, .reference .depth] before = .done [.empty, .empty] before := ⟨rfl, rfl⟩

/-- Observe an actual next class forcing its own initially empty slots despite warm native tables. -/
def FreshSlots (values : List (Value Nat Unit)) (before : NativeState 8 Nat Unit) : Result 8 Nat Unit (List (Value Nat Unit)) → Prop
  | .incomplete actual captured (.target (.projection _ native) shared) => actual = record ∧ captured = values ∧ native = before ∧
      shared.native = before ∧ shared.targets [0, 0] = none ∧ shared.targets [1, 0] = none
  | _ => False

/-- Observe two actual classes sharing native state while keeping their target slots separate. -/
def FoldResults : Outcome Nat Unit (Value Nat Unit) → Prop
  | .pending .. => False
  | .done root heap =>
      let values := [root, root]
      let before := SourceEqualityNativeInitial.cold 8 heap
      match fold () (fun _ _ => ()) (fun _ => true) () 2 2 0 0 16 [record, record] values before with
      | .done results after => results = values ∧ after.machine.heap = heap ∧ after.nodes.next = 1 ∧ after.edges.next = 0 ∧
          pass () (fun _ _ => ()) (fun _ => true) () 3 3 1 2 20 [record, record] values before = .done values after ∧
          fold () (fun _ _ => ()) (fun _ => true) () 2 2 0 0 16 [record, record] values after = .done values after ∧
          FreshSlots values after (classEdit () (fun _ _ => ()) (fun _ => true) () 2 0 0 0 16 record values after)
      | _ => False

/-- Repeated classes construct fresh targets, retain one warm native cell, and stabilize at larger bounds. -/
theorem fresh_classes_and_warm_native : FoldResults (InternedFreshOrdinaryConstruction.build
    (.node [.mk 31 () [.node [.mk 11 () []]], .mk 32 () [.node [.mk 11 () []]]]) [] empty) := by
  set_option maxRecDepth 20000 in
  set_option cbv.maxSteps 30000000 in cbv

/-- Physical selection retains clear repeated records in their original occurrence order. -/
theorem selected_repeats (heap : State Nat Unit) :
    SourceEqualitySelectedRecords.keep [record, record, record]
      [⟨record.paths, heap, false, heap⟩, ⟨record.paths, heap, true, heap⟩, ⟨record.paths, heap, false, heap⟩] = [record, record] := rfl

end MicroCFTA.SourceEqualityClassFoldExamples
