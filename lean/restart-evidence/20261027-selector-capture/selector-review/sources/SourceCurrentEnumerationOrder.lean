import MicroCFTA.Cache
import MicroCFTA.EnumerationCPS
import MicroCFTA.InternedEdgeResidency

/-!
# Current enumeration edge-order closures

The closure reads the weighted root map first. A missing key uses the
weighted canonical edges of that node. Raw interned order omits this map
and needs no symbol order. The weight stage retains multiplicity and equal
weight order under a total transitive comparison. Canonical-class
computation, Double comparison without NaN, source map storage, and lazy
demand remain separate implementation bridges. The source sortOn bridge
is also separate. All input rows here are completed finite lists.
-/
namespace MicroCFTA.SourceCurrentEnumerationOrder
variable {Node Edge Weight BranchState : Type}

/-- Descending weight order uses a stable comparison sort. -/
def byWeight (le : Weight → Weight → Bool) (weight : Edge → Weight) (edges : List Edge) : List Edge :=
  edges.mergeSort (fun first second => le (weight second) (weight first))

/-- An absent weight function retains the supplied edge order exactly. -/
def byWeights (le : Weight → Weight → Bool) (weights : Option (Edge → Weight)) (edges : List Edge) : List Edge :=
  match weights with
  | none => edges
  | some weight => byWeight le weight edges

/-- Capture the weighted original root map and retain the per-node fallback. -/
def canonicalEdgesOf (identity : Node → Int) (canonicalOrder : Node → Cache.Table Int (List Edge))
    (canonicalEdges : Node → List Edge) (le : Weight → Weight → Bool) (weights : Option (Edge → Weight))
    (root : Node) : Node → List Edge :=
  let ordered := fun key => (canonicalOrder root key).map (byWeights le weights)
  fun node => (ordered (identity node)).getD (byWeights le weights (canonicalEdges node))

/-- A root-map hit uses those exact original rows and applies the weight stage once. -/
theorem canonical_hit (identity : Node → Int) (canonicalOrder : Node → Cache.Table Int (List Edge))
    (canonicalEdges : Node → List Edge) (le : Weight → Weight → Bool) (weights : Option (Edge → Weight))
    (root node : Node) (edges : List Edge) (found : canonicalOrder root (identity node) = some edges) :
    canonicalEdgesOf identity canonicalOrder canonicalEdges le weights root node = byWeights le weights edges := by
  simp only [canonicalEdgesOf, found, Option.map_some, Option.getD_some]

/-- Only a missing original key selects the canonical per-node fallback and its weight stage. -/
theorem canonical_miss (identity : Node → Int) (canonicalOrder : Node → Cache.Table Int (List Edge))
    (canonicalEdges : Node → List Edge) (le : Weight → Weight → Bool) (weights : Option (Edge → Weight))
    (root node : Node) (absent : canonicalOrder root (identity node) = none) :
    canonicalEdgesOf identity canonicalOrder canonicalEdges le weights root node =
      byWeights le weights (canonicalEdges node) := by
  simp only [canonicalEdgesOf, absent, Option.map_none, Option.getD_none]

/-- The closure equals the earlier root-map selection followed by its unchanged weight stage. -/
theorem weights_after_lookup (identity : Node → Int) (canonicalOrder : Node → Cache.Table Int (List Edge))
    (canonicalEdges : Node → List Edge) (le : Weight → Weight → Bool) (weights : Option (Edge → Weight))
    (root node : Node) :
    canonicalEdgesOf identity canonicalOrder canonicalEdges le weights root node =
      byWeights le weights ((canonicalOrder root (identity node)).getD (canonicalEdges node)) := by
  cases found : canonicalOrder root (identity node) <;> simp only [canonicalEdgesOf, found,
    Option.map_none, Option.getD_none, Option.map_some, Option.getD_some]

/-- The unweighted runs closure retains root-map or fallback order without a sort. -/
theorem no_weights (identity : Node → Int) (canonicalOrder : Node → Cache.Table Int (List Edge))
    (canonicalEdges : Node → List Edge) (le : Weight → Weight → Bool) (root node : Node) :
    canonicalEdgesOf identity canonicalOrder canonicalEdges le none root node =
      (canonicalOrder root (identity node)).getD (canonicalEdges node) := by
  rw [weights_after_lookup]
  rfl

/-- Sorting retains all edge occurrences, including duplicates. -/
theorem byWeight_perm (le : Weight → Weight → Bool) (weight : Edge → Weight) (edges : List Edge) :
    (byWeight le weight edges).Perm edges := List.mergeSort_perm edges _

/-- Optional weighting retains the literal edge multiset. -/
theorem byWeights_perm (le : Weight → Weight → Bool) (weights : Option (Edge → Weight)) (edges : List Edge) :
    (byWeights le weights edges).Perm edges := by
  cases weights with
  | none => exact .refl _
  | some weight => exact byWeight_perm le weight edges

/-- Weighting changes only the order of the selected root-map or fallback list. -/
theorem canonical_perm (identity : Node → Int) (canonicalOrder : Node → Cache.Table Int (List Edge))
    (canonicalEdges : Node → List Edge) (le : Weight → Weight → Bool) (weights : Option (Edge → Weight))
    (root node : Node) :
    (canonicalEdgesOf identity canonicalOrder canonicalEdges le weights root node).Perm
      ((canonicalOrder root (identity node)).getD (canonicalEdges node)) := by
  rw [weights_after_lookup]
  exact byWeights_perm le weights _

/-- An original equal-weight pair retains its relative order under lawful weight comparison. -/
theorem equal_weight_order (le : Weight → Weight → Bool)
    (trans : ∀ first second third, le first second = true → le second third = true → le first third = true)
    (total : ∀ first second, (le first second || le second first) = true)
    (refl : ∀ value, le value value = true) (weight : Edge → Weight)
    (edges : List Edge) (first second : Edge) (equal : weight first = weight second)
    (ordered : [first, second].Sublist edges) : [first, second].Sublist (byWeight le weight edges) := by
  apply List.pair_sublist_mergeSort
    (fun first second third before after => trans (weight third) (weight second) (weight first) after before)
    (fun first second => total (weight second) (weight first)) ?_ ordered
  simpa only [equal] using refl (weight second)

/-- Raw interned order uses the supplied node read and ignores the original root. -/
def internedEdgesOf (nodeEdges : Node → List Edge) (_root node : Node) : List Edge := nodeEdges node

/-- Raw edge selection requires no order instance on symbols or nodes. -/
theorem interned_exact (nodeEdges : Node → List Edge) (root node : Node) :
    internedEdgesOf nodeEdges root node = nodeEdges node := rfl

/-- At the actual ordinary branch, the raw source accessor returns the stored edge list. -/
theorem interned_ordinary (root : InternedConstructorTemplates.Value Symbol Guard)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (InternedConstructorTemplates.EdgeValue Symbol Guard)) (depth : Nat)
    (free : List InternedBinderProtocol.Reference) :
    internedEdgesOf InternedEdgeResidency.nodeEdges root (.node entry edges depth free) = edges := rfl

/-- Actual finite CPS branching retains raw edge order, duplicates, and the same input state. -/
theorem interned_branches (nodeEdges : Node → List Edge) (root node : Node) (state : BranchState) :
    EnumerationCPS.allBranches (EnumerationCPS.branches (internedEdgesOf nodeEdges root node)) state =
      (nodeEdges node).map (fun edge => (edge, state)) :=
  EnumerationCPS.allBranches_exact _ _ (EnumerationCPS.branches_represents _) state

/-- Canonical closure branching retains the selected weighted rows in their exact order. -/
theorem canonical_branches (identity : Node → Int) (canonicalOrder : Node → Cache.Table Int (List Edge))
    (canonicalEdges : Node → List Edge) (le : Weight → Weight → Bool) (weights : Option (Edge → Weight))
    (root node : Node) (state : BranchState) :
    EnumerationCPS.allBranches
      (EnumerationCPS.branches (canonicalEdgesOf identity canonicalOrder canonicalEdges le weights root node)) state =
      (byWeights le weights ((canonicalOrder root (identity node)).getD (canonicalEdges node))).map
        (fun edge => (edge, state)) := by
  rw [EnumerationCPS.allBranches_exact _ _ (EnumerationCPS.branches_represents _) state, weights_after_lookup]

end MicroCFTA.SourceCurrentEnumerationOrder
