import MicroCFTA.SourceCurrentEnumerationOrder

/-!
# Current curried default markers and local edge filtering

The source checks complete edge labels and empty child lists. Filtering
keeps complete physical records in their original order. This module does
not prove curried erasure, domain construction, intersection scheduling,
or GHC instance and defaulting correctness.
-/
namespace MicroCFTA.SourceCurriedDefaulting
open InternedConstructorTemplates

/-- A marker or type head must be a leaf with the exact source symbol. -/
def leaf (name : String) (edge : EdgeValue String Guard) : Bool :=
  decide (edge.entry.key.symbol = name) && edge.children.isEmpty

/-- Follow the source open-marker guard before the no-default guard. -/
def narrowHeads (edges : List (EdgeValue String Guard)) : List (EdgeValue String Guard) :=
  if !(edges.any (leaf "?")) then edges
  else if edges.any (leaf "?nodefault") then []
  else edges.filter (leaf "List")

/-- An equal name at a nonleaf edge does not act as a marker. -/
theorem leaf_nonempty (name : String) (edge : EdgeValue String Guard)
    (children : edge.children ≠ []) : leaf name edge = false := by
  simp only [leaf, Bool.and_eq_false_iff]
  exact Or.inr (List.isEmpty_eq_false_iff.mpr children)

/-- Without the open marker, every original edge remains, including a lone no-default marker. -/
theorem narrow_no_open (edges : List (EdgeValue String Guard))
    (absent : edges.any (leaf "?") = false) : narrowHeads edges = edges := by
  simp only [narrowHeads, absent, Bool.not_false, ↓reduceIte]

/-- Both markers reject the complete local list before any edge is tried. -/
theorem narrow_no_default (edges : List (EdgeValue String Guard))
    (opened : edges.any (leaf "?") = true) (blocked : edges.any (leaf "?nodefault") = true) :
    narrowHeads edges = [] := by
  simp only [narrowHeads, opened, blocked, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

/-- An undetermined defaultable head keeps exactly the original List leaves. -/
theorem narrow_list (edges : List (EdgeValue String Guard))
    (opened : edges.any (leaf "?") = true) (allowed : edges.any (leaf "?nodefault") = false) :
    narrowHeads edges = edges.filter (leaf "List") := by
  simp only [narrowHeads, opened, allowed, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

/-- Local narrowing preserves physical records, order and duplicate occurrences. -/
theorem narrow_sublist (edges : List (EdgeValue String Guard)) : (narrowHeads edges).Sublist edges := by
  unfold narrowHeads
  split
  · exact .refl _
  · split
    · exact List.nil_sublist _
    · exact List.filter_sublist

/-- Repeating the local filter makes no additional change. -/
theorem narrow_idempotent (edges : List (EdgeValue String Guard)) :
    narrowHeads (narrowHeads edges) = narrowHeads edges := by
  cases opened : edges.any (leaf "?") with
  | false => rw [narrow_no_open edges opened, narrow_no_open edges opened]
  | true =>
      cases blocked : edges.any (leaf "?nodefault") with
      | true => rw [narrow_no_default edges opened blocked]; rfl
      | false =>
          rw [narrow_list edges opened blocked]
          apply narrow_no_open
          rw [List.any_eq_false]
          intro edge member
          have named := of_decide_eq_true (Bool.and_eq_true_iff.mp (List.mem_filter.mp member).2).1
          simp [leaf, named]

/-- Only recognized List leaves survive the defaulting branch. -/
theorem narrow_list_member (edges : List (EdgeValue String Guard))
    (opened : edges.any (leaf "?") = true) (allowed : edges.any (leaf "?nodefault") = false)
    (edge : EdgeValue String Guard) :
    edge ∈ narrowHeads edges ↔ edge ∈ edges ∧ leaf "List" edge = true := by
  rw [narrow_list edges opened allowed, List.mem_filter]

/-- A completed domain lookup distinguishes unrestricted heads from marked domains. -/
inductive Defaulting where
  | anyHead
  | onlyDefault (keys : Cache.Table String Bool)

/-- The source domain contributes the open marker before its optional rejection marker. -/
def domainMarkers : Defaulting → String → List String
  | .anyHead, _ => []
  | .onlyDefault keys, key =>
      match keys key with
      | none => []
      | some defaults => "?" :: (if !defaults then ["?nodefault"] else [])

/-- All higher-kind types carry both markers when default-only filtering is enabled. -/
def anyMarkers : Defaulting → List String
  | .anyHead => []
  | .onlyDefault _ => ["?", "?nodefault"]

/-- An absent domain-map key adds no marker or extra validation. -/
theorem domain_unknown (keys : Cache.Table String Bool) (key : String) (absent : keys key = none) :
    domainMarkers (.onlyDefault keys) key = [] := by simp only [domainMarkers, absent]

/-- A defaultable domain contributes only the open marker. -/
theorem domain_default (keys : Cache.Table String Bool) (key : String) (found : keys key = some true) :
    domainMarkers (.onlyDefault keys) key = ["?"] := by simp only [domainMarkers, found]; rfl

/-- A nondefaultable domain contributes both markers in source order. -/
theorem domain_blocked (keys : Cache.Table String Bool) (key : String) (found : keys key = some false) :
    domainMarkers (.onlyDefault keys) key = ["?", "?nodefault"] := by simp only [domainMarkers, found]; rfl

/-- Domain no-default markers always have their open marker in the same completed domain. -/
theorem domain_marker_guard (defaulting : Defaulting) (key : String)
    (blocked : "?nodefault" ∈ domainMarkers defaulting key) : "?" ∈ domainMarkers defaulting key := by
  cases defaulting with
  | anyHead => cases blocked
  | onlyDefault keys => cases found : keys key with
    | none => simp only [domainMarkers, found, List.not_mem_nil] at blocked
    | some defaults => simp only [domainMarkers, found, List.mem_cons_self]

/-- The default-only option is effective only in the curried encoding. -/
def extendedDefaults (curried onlyDefaulted : Bool) : Bool := curried && onlyDefaulted

/-- The host complete-check defaulting flag and the narrowed-run route use the same option guard. -/
theorem extendedDefaults_enabled (curried onlyDefaulted : Bool) :
    extendedDefaults curried onlyDefaulted = true ↔ curried = true ∧ onlyDefaulted = true := by
  simp only [extendedDefaults, Bool.and_eq_true]

/-- Narrow the already selected weighted rows; retain the original root-map closure. -/
def narrowedEdgesOf (identity : Node → Int) (canonicalOrder : Node → Cache.Table Int (List (EdgeValue String Guard)))
    (canonicalEdges : Node → List (EdgeValue String Guard)) (le : Weight → Weight → Bool)
    (weight : EdgeValue String Guard → Weight) (root node : Node) : List (EdgeValue String Guard) :=
  narrowHeads (SourceCurrentEnumerationOrder.canonicalEdgesOf identity canonicalOrder canonicalEdges le (some weight) root node)

/-- The new source closure filters after its root-map lookup and weight stage. -/
theorem narrowed_after_lookup (identity : Node → Int)
    (canonicalOrder : Node → Cache.Table Int (List (EdgeValue String Guard)))
    (canonicalEdges : Node → List (EdgeValue String Guard)) (le : Weight → Weight → Bool)
    (weight : EdgeValue String Guard → Weight) (root node : Node) :
    narrowedEdgesOf identity canonicalOrder canonicalEdges le weight root node =
      narrowHeads (SourceCurrentEnumerationOrder.byWeights le (some weight)
        ((canonicalOrder root (identity node)).getD (canonicalEdges node))) := by
  rw [narrowedEdgesOf, SourceCurrentEnumerationOrder.weights_after_lookup]

/-- Local enumeration tries exactly the surviving rows in order from the same branch state. -/
theorem narrowed_branches (edges : List (EdgeValue String Guard)) (state : BranchState) :
    EnumerationCPS.allBranches (EnumerationCPS.branches (narrowHeads edges)) state =
      (narrowHeads edges).map (fun edge => (edge, state)) :=
  EnumerationCPS.allBranches_exact _ _ (EnumerationCPS.branches_represents _) state

end MicroCFTA.SourceCurriedDefaulting
