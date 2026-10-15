import MicroCFTA.SourceEqualityNativeEditGraph

/-!
# Actual-prefix word checks for simultaneous native edits

Leaves retain their native request word checks. Later checks use only states
returned by actual completed prefixes. The precondition supplies no leaf or
whole-worker completion, cache preservation, or language law.
-/
namespace MicroCFTA.SourceEqualityNativeEditRanges
open InternedConstructorTemplates SourceEqualityEdits SourceEqualityNativeScoped SourceEqualityNativeEditGraph

mutual
  /-- Request word checks along the actual source node branches. -/
  inductive NodeRanges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
      (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) :
      Edits (Value Symbol Guard) → Value Symbol Guard → NativeState width Symbol Guard → Prop where
    | leaf (ranges : SourceRecursiveIntersectionNative.WordRanges emptyGuard conjoin
        (.node ⟨IntersectionEmptyDomain.emptyDomain, target, value⟩ .pure) before) :
        NodeRanges emptyGuard conjoin (.editAt target) value before
    | empty : NodeRanges emptyGuard conjoin (.editBelow entries) .empty state
    | ordinary (rows : RowsRanges emptyGuard conjoin entries edges before) :
        NodeRanges emptyGuard conjoin (.editBelow entries) (.node entry edges depth free) before
    | recursive (recursive : SourceEqualityRequiredGraph.Recursive original)
        (body : ∀ exposed heap, SourceEqualityRequiredHead.Head original before.machine.heap exposed heap →
          NodeRanges emptyGuard conjoin (.editBelow entries) exposed (advanceHeap before heap)) :
        NodeRanges emptyGuard conjoin (.editBelow entries) original before

  /-- Later child checks use the actual completed first edit's full native state. -/
  inductive ChildrenRanges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
      (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) :
      List (Int × Edits (Value Symbol Guard)) → Nat → List (Value Symbol Guard) → NativeState width Symbol Guard → Prop where
    | nil : ChildrenRanges emptyGuard conjoin entries index [] state
    | unselected (index : Nat) (absent : SourceEqualityNeededMap.lookup (index : Int) entries = none)
        (rest : ChildrenRanges emptyGuard conjoin entries (index + 1) values before) :
        ChildrenRanges emptyGuard conjoin entries index (value :: values) before
    | selected (index : Nat) (found : SourceEqualityNeededMap.lookup (index : Int) entries = some edits)
        (first : NodeRanges emptyGuard conjoin edits value before)
        (rest : ∀ result middle, EditNode emptyGuard conjoin edits value before result middle →
          ChildrenRanges emptyGuard conjoin entries (index + 1) values middle) :
        ChildrenRanges emptyGuard conjoin entries index (value :: values) before

  /-- Later row checks use actual child results and the subsequent literal edge request. -/
  inductive RowsRanges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
      (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) :
      List (Int × Edits (Value Symbol Guard)) → List (EdgeValue Symbol Guard) → NativeState width Symbol Guard → Prop where
    | nil : RowsRanges emptyGuard conjoin entries [] state
    | cons (children : ChildrenRanges emptyGuard conjoin entries 0 edge.children before)
        (rest : ∀ values middle, EditChildren emptyGuard conjoin entries 0 edge.children before values middle →
          RowsRanges emptyGuard conjoin entries edges (advanceHeap middle
            (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.machine.heap).2)) :
        RowsRanges emptyGuard conjoin entries (edge :: edges) before
end

/-- A source child-list root callback is ignored and requires no native word check. -/
def ListRanges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (edits : Edits (Value Symbol Guard))
    (values : List (Value Symbol Guard)) (before : NativeState width Symbol Guard) : Prop :=
  match edits with
  | .editAt _ => True
  | .editBelow entries => ChildrenRanges emptyGuard conjoin entries 0 values before

end MicroCFTA.SourceEqualityNativeEditRanges
