import MicroCFTA.RecursiveRuntimeVerified
import MicroCFTA.RecursiveNaryExamples

/-!
# Recursive runtime routing examples

The examples use constructor-derived runtime certificates. Equal user values
retain distinct ranks. Recursive term tracking differs between probe and
term rebuilds. Error checks retain source precedence.
-/
namespace MicroCFTA.RecursiveRuntimeExamples
open Language GeneratorCombinators
open RecursiveRuntimeVerified
open RecursiveNaryExamples (pureCallbacks pure_exact)

/-- A concrete pure source supplies its local inverse and probability laws. -/
def leaf (value : Value) (symbol : Nat) : Body Unit Nat Nat Value :=
  pure pureCallbacks (value, .node (.user symbol) []) (pure_exact _)

/-- One delayed recursive join retains the source marker and term rebuilds. -/
def recursiveBranch : Body Unit Nat Nat Nat :=
  label 10 (join 2 (leaf Nat.succ 20) (.cons (occurrence pureCallbacks ()) .nil))

/-- Distinct ranks can return equal values in the unweighted source family. -/
def ordinary : Unit → Body Unit Nat Nat Nat :=
  fun _ => nary 3 fun
    | ⟨0, _⟩ => leaf 7 1
    | ⟨1, _⟩ => leaf 7 2
    | ⟨2, _⟩ => recursiveBranch

/-- An explicit key-mass table marks the weighted branch without changing its member values. -/
def weightedLeaf (mass : Rat) (positive : 0 < mass) (symbol : Nat) : Body Unit Nat Nat Nat :=
  retained pureCallbacks (fun _ => mass) (fun _ => positive)
    (.pure (7, .node (.user symbol) [])) (pure_exact _) false

/-- Retained nine-to-one masses remain visible after a recursive grouped join. -/
def weighted : Unit → Body Unit Nat Nat Nat :=
  fun _ => nary 3 fun
    | ⟨0, _⟩ => weightedLeaf 9 (by decide) 1
    | ⟨1, _⟩ => weightedLeaf 1 (by decide) 2
    | ⟨2, _⟩ => recursiveBranch

/-- The same typed body has absent probe terms and complete rebuilt terms. -/
theorem term_phases :
    ((ordinary ()).template.metadata (fun _ => RecursiveJoinRuntime.placeholder)).terms = false ∧
    ((ordinary ()).template.metadata (fun _ => RecursiveJoinRuntime.termPlaceholder)).terms = true := by
  decide +kernel

/-- The source family dispatcher chooses different sampler routes from primitive fields. -/
theorem sampler_flags :
    (RecursiveRuntimeOrigins.memberMetadata [()] (templates ordinary) ()).weighted = false ∧
    (RecursiveRuntimeOrigins.memberMetadata [()] (templates weighted) ()).weighted = true := by
  decide +kernel

/-- Unweighted recursive bounds retain all four replay positions, including repeated values. -/
theorem ordinary_ranked :
    (RecursiveJoinRuntime.boundedSampler
      (RecursiveRuntimeOrigins.memberMetadata [()] (templates ordinary) ()).weighted
      (fun size => KeyedSource.family (fun key => (ordinary key).template.checked.body.value) size ()) 1).sampling.ranked =
      [(1 / 4, (0, 7)), (1 / 4, (1, 7)), (1 / 4, (2, 8)), (1 / 4, (3, 8))] := by
  cbv

/-- Weighted runtime bounds preserve nine-to-one conditional rank mass at both sizes. -/
theorem weighted_ranked :
    (RecursiveJoinRuntime.boundedSampler
      (RecursiveRuntimeOrigins.memberMetadata [()] (templates weighted) ()).weighted
      (fun size => KeyedSource.family (fun key => (weighted key).template.checked.body.value) size ()) 1).sampling.ranked =
      [(9 / 20, (0, 7)), (1 / 20, (1, 7)), (9 / 20, (2, 8)), (1 / 20, (3, 8))] := by
  cbv

/-- A dropped key can still require the weighted sampler for retained keys. -/
theorem dropped_key_promotes :
    RecursiveRuntimeDispatch.members [0, 1] (fun key => if key = 0 then some 0 else none)
      [(0, ⟨false, false, true⟩), (1, ⟨false, true, false⟩)] (fun _ => true) =
      [(0, ⟨true, true, true⟩)] := by decide +kernel

/-- Public and internal bounded term queries retain their distinct error order. -/
theorem missing_term_precedence :
    RecursiveRuntimeDispatch.termAt (Cause := Nat) (TermValue := Nat) (.ok none) (-1) =
      .error (.negativeRank (-1)) ∧
    RecursiveRuntimeDispatch.boundedOutcome (Cause := Nat) (TermValue := Nat) 2 none (-1) =
      .error .cannotInspectRecursive ∧
    RecursiveRuntimeDispatch.bound (Cause := Nat) 0 ⟨false, false, false⟩ = .error .empty ∧
    RecursiveRuntimeDispatch.bound (Cause := Nat) 2 ⟨false, false, false⟩ = .ok ⟨false, false, false⟩ := by
  simp [RecursiveRuntimeDispatch.termAt, RecursiveRuntimeDispatch.boundedOutcome, RecursiveRuntimeDispatch.bound]

end MicroCFTA.RecursiveRuntimeExamples
