import MicroCFTA.SourceSizedFiniteKeysCanonical
import MicroCFTA.SourceSizedDecidedPublic

/-!
# Exact bounded-table execution under finite key restriction

The source state type can be infinite. Injective restriction preserves
candidate order, complete constraints, first errors, and every table insert.
The finite public fold is the readback of the same original-state fold.
-/
namespace MicroCFTA.SourceSizedFiniteKeysExecution
open Language SourceSizedDecided SourceSizedDecidedTable

/-- Read a table only at the injected finite state keys. -/
def pull (encode : Source → Target) (table : Table Target Value) : Table Source Value :=
  fun state size => table (encode state) size

/-- Exact state identity makes source inserts commute with restriction. -/
theorem insert_pull [DecidableEq Source] [DecidableEq Target]
    (encode : Source → Target) (injective : Function.Injective encode)
    (table : Table Target Value) (state : Source) (size : Nat) (values : List Value) :
    pull encode (insert table (encode state) size values) = insert (pull encode table) state size values := by
  funext query count
  simp only [pull, SourceSizedDecidedTable.insert, injective.eq_iff]

/-- The complete ordered frozen-table state fold retains the same result or first error. -/
theorem addStates_pull [DecidableEq Source] [DecidableEq Target]
    (encode : Source → Target) (injective : Function.Injective encode)
    (source : Table Source Value → Nat → Source → Except Error (List Value))
    (target : Table Target Value → Nat → Target → Except Error (List Value))
    (same : ∀ smaller size state, target smaller size (encode state) = source (pull encode smaller) size state)
    (states : List Source) (smaller built : Table Target Value) (size : Nat) :
    (addStates target smaller size (states.map encode) built).map (pull encode) =
      addStates source (pull encode smaller) size states (pull encode built) := by
  induction states generalizing built with
  | nil => rfl
  | cons state rest ih =>
    simp only [List.map_cons, addStates, ←same smaller size state]
    cases found : target smaller size (encode state) with
    | error failure => rfl
    | ok values =>
      rw [ih, insert_pull encode injective]

/-- Every size pass, including empty classes and early errors, retains the original result. -/
theorem upTo_pull [DecidableEq Source] [DecidableEq Target]
    (encode : Source → Target) (injective : Function.Injective encode)
    (source : Table Source Value → Nat → Source → Except Error (List Value))
    (target : Table Target Value → Nat → Target → Except Error (List Value))
    (same : ∀ smaller size state, target smaller size (encode state) = source (pull encode smaller) size state)
    (states : List Source) (bound : Nat) :
    (upTo target (states.map encode) bound).map (pull encode) = upTo source states bound := by
  induction bound with
  | zero => rfl
  | succ bound ih =>
    cases previous : upTo target (states.map encode) bound with
    | error failure =>
      have sourcePrevious : upTo source states bound = .error failure := by simpa [previous, Except.map] using ih.symm
      simp only [upTo, previous, sourcePrevious, Except.map]
    | ok smaller =>
      have sourcePrevious : upTo source states bound = .ok (pull encode smaller) := by simpa [previous, Except.map] using ih.symm
      simp only [upTo, previous, sourcePrevious]
      exact addStates_pull encode injective source target same states smaller smaller (bound + 1)

/-- Rename only a row's state references. Its original constraint remains unchanged. -/
def renameRow (encode : Source → Target) (row : Row Source Symbol Payload) : Row Target Symbol Payload :=
  ⟨row.label, row.children.map encode, row.constraint⟩

/-- Actual candidate traversal preserves the exact nested-product order. -/
theorem candidates_pull (encode : Source → Target) (smaller : Table Target (Term Symbol))
    (symbol : Symbol) (children : List Source) (size : Nat) :
    SourceSizedCandidates.candidates smaller symbol (children.map encode) size =
      SourceSizedCandidates.candidates (pull encode smaller) symbol children size := by
  cases size with
  | zero => rfl
  | succ remaining =>
    rw [SourceSizedCandidates.candidates_succ, SourceSizedCandidates.candidates_succ]
    rw [SourceSizedDispatch.forests_rename (fun size state => pull encode smaller state size)
      (fun size state => smaller state size) encode (fun _ _ => rfl) children]

/-- Every complete constraint/term pair is preserved in its original candidate position. -/
theorem pairs_pull (encode : Source → Target)
    (source : Source → List (Row Source Symbol Payload)) (target : Target → List (Row Target Symbol Payload))
    (same : ∀ state, target (encode state) = (source state).map (renameRow encode))
    (smaller : Table Target (Term Symbol)) (size : Nat) (state : Source) :
    pairs target smaller size (encode state) = pairs source (pull encode smaller) size state := by
  simp only [pairs, same state, List.flatMap_map]
  apply TablePosition.flatMap_congr
  intro row _
  simp only [renameRow, candidates_pull]

/-- Guard filtering and duplicate removal have exactly the same successful list or first error. -/
theorem make_pull [DecidableEq Symbol] (encode : Source → Target)
    (source : Source → List (Row Source Symbol Payload)) (target : Target → List (Row Target Symbol Payload))
    (same : ∀ state, target (encode state) = (source state).map (renameRow encode))
    (answer : Payload × Term Symbol → Guards.Verdict)
    (smaller : Table Target (Term Symbol)) (size : Nat) (state : Source) :
    make target answer smaller size (encode state) = make source answer (pull encode smaller) size state := by
  simp only [make, pairs_pull encode source target same]

/-- All bounded decided queries commute with key restriction, including rejected constraints. -/
theorem sizedUpTo_pull [DecidableEq Source] [DecidableEq Target] [DecidableEq Symbol]
    (encode : Source → Target) (injective : Function.Injective encode)
    (source : Source → List (Row Source Symbol Payload)) (target : Target → List (Row Target Symbol Payload))
    (same : ∀ state, target (encode state) = (source state).map (renameRow encode))
    (states : List Source) (answer : Payload × Term Symbol → Guards.Verdict) (bound : Int) :
    (sizedUpToSigned target (states.map encode) answer bound).map (pull encode) =
      sizedUpToSigned source states answer bound :=
  upTo_pull encode injective (make source answer) (make target answer)
    (make_pull encode source target same answer) states bound.toNat

open SourceDenseRows Std
attribute [local instance] lexOrd

/-- The original-state bounded fold equals the finite public fold after actual dense sorting. -/
theorem native_public [DecidableEq State] [Ord State] [DecidableEq Symbol] [Ord Symbol]
    [TransOrd Symbol] [LawfulEqOrd Symbol]
    (table : SourceSizedFiniteKeys.Table State Symbol Payload) (root : State)
    (valid : FTAValidation.validateRows root (SourceSizedFiniteKeys.interpreted table (fun _ _ => true)) =
      .ok (SourceSizedFiniteKeys.interpreted table (fun _ _ => true)))
    (answer : Payload × Term Symbol → Guards.Verdict) (bound : Int) :
    (sizedUpToSigned (SourceSizedFiniteKeys.nativeSorted table root valid)
      ((SourceSizedDecidedPublic.reached (SourceSizedFiniteKeys.input table root valid)).map Subtype.val)
      answer bound).map (pull Subtype.val) =
      SourceSizedDecidedPublic.publicSizedUpTo (SourceSizedFiniteKeys.input table root valid) answer bound := by
  apply sizedUpTo_pull Subtype.val (fun _ _ same => Subtype.ext same)
  intro state
  exact (SourceSizedFiniteKeys.sorted_readback table root valid state).symm

end MicroCFTA.SourceSizedFiniteKeysExecution
