import MicroCFTA.RecursiveJoinBodyFields
import MicroCFTA.RecursiveJoinFamily
import MicroCFTA.KeyedNaryGuards

/-!
# Original occurrence metadata for composite recursive joins

The decorated body retains the original label-aware shape beside its checked
callback compiler. Labels add constructor metadata; pay changes size only.
Join metadata follows the left fold in `recursiveChainProduct`. The final
JoinN term wrapper does not independently change the size-index flags.
-/
namespace MicroCFTA.RecursiveJoinGuards
open Language
open KeyedNaryGuards (SameSize)
open OccurrenceGuard (Shape summary)

/-- A checked body retains its original occurrence metadata and local size
correspondence. The constructor proofs derive this correspondence. -/
structure Body (Key Root Symbol Value : Type) where
  checked : RecursiveJoinBodyFields.CheckedBody Key Root Symbol Value
  shape : Nat → GroupedProbe.Table Key → Shape
  size : ∀ token known, SameSize (shape token known)
    (KeyedGuards.shape token known checked.body.value)

/-- Existing typed syntax supplies its original label-aware metadata. -/
def ofNary [DecidableEq Symbol] (callbacks : KeyedNaryFields.LeafCallbacks Symbol)
    (recipe : KeyedNaryAlignment.Recipe Key Root Symbol Value)
    (leaves : KeyedNaryFields.LeavesExact callbacks recipe) : Body Key Root Symbol Value where
  checked := RecursiveJoinBodyFields.ofNary callbacks recipe leaves
  shape := fun token known => KeyedNaryGuards.shape token known recipe
  size := fun token known => KeyedNaryGuards.lowered_summary token known recipe

/-- Mapping user values preserves every original occurrence flag. -/
def map (transform : Value → Result) (inner : Body Key Root Symbol Value) : Body Key Root Symbol Result where
  checked := RecursiveJoinBodyFields.map transform inner.checked
  shape := fun token known => .map (inner.shape token known)
  size := inner.size

/-- Pay clears only the size-unguarded flags. -/
def pay [DecidableEq Symbol] (inner : Body Key Root Symbol Value) : Body Key Root Symbol Value where
  checked := RecursiveJoinBodyFields.pay inner.checked
  shape := fun token known => .pay (inner.shape token known)
  size := fun token known => ⟨congrArg (Option.map (· + 1)) (inner.size token known).1,
    rfl, (inner.size token known).2.2⟩

/-- A source label clears both size-unguarded and termless flags. -/
def label [DecidableEq Symbol] (symbol : Symbol) (inner : Body Key Root Symbol Value) : Body Key Root Symbol Value where
  checked := RecursiveJoinBodyFields.label symbol inner.checked
  shape := fun token known => .constructor (inner.shape token known)
  size := fun token known => ⟨congrArg (Option.map (· + 1)) (inner.size token known).1,
    rfl, (inner.size token known).2.2⟩

/-- Product metadata depends only on the local minimum, size flags, and used flags. -/
theorem product_same (left right otherLeft otherRight : Shape)
    (leftSame : SameSize left otherLeft) (rightSame : SameSize right otherRight) :
    SameSize (.product left right) (.product otherLeft otherRight) := by
  rcases leftSame with ⟨lm, lg, lu⟩
  rcases rightSame with ⟨rm, rg, ru⟩
  simp only [SameSize, summary, OccurrenceGuard.beside, lm, lg, lu, rm, rg, ru, and_self]

/-- Ordinary application reads the same product flags as the source index. -/
def ap [DecidableEq Symbol] (functions : Body Key Root Symbol (A → B)) (arguments : Body Key Root Symbol A) :
    Body Key Root Symbol B where
  checked := RecursiveJoinBodyFields.ap functions.checked arguments.checked
  shape := fun token known => .product (functions.shape token known) (arguments.shape token known)
  size := fun token known => product_same _ _ _ _ (functions.size token known) (arguments.size token known)

/-- Unwrapped alternatives retain the exact ordered value lowering. -/
theorem alternatives_value (branches : List (RecursiveJoinComposition.Body Key Root Symbol Value)) :
    (RecursiveJoinComposition.alternatives branches).value =
      KeyedNaryAlignment.alternatives (branches.map (fun body => body.value)) := by
  induction branches with
  | nil => rfl
  | cons first rest ih =>
      cases rest with
      | nil => rfl
      | cons second rest => simpa only [RecursiveJoinComposition.alternatives, RecursiveJoinComposition.choice,
          List.map_cons, KeyedNaryAlignment.alternatives] using congrArg (KeyedSource.Recipe.choice first.value) ih

/-- Flat choices preserve all branch flags, including the singleton case. -/
def nary (count : Nat) (branches : Fin count → Body Key Root Symbol Value) : Body Key Root Symbol Value where
  checked := RecursiveJoinBodyFields.nary count (fun index => (branches index).checked)
  shape := fun token known => KeyedNaryGuards.alternatives
    (List.ofFn fun index => (branches index).shape token known)
  size := by
    intro token known
    change SameSize _ (KeyedGuards.shape token known (RecursiveJoinComposition.nary count _).value)
    simp only [RecursiveJoinComposition.nary, alternatives_value,
      KeyedNaryGuards.lowered_alternatives, List.map_ofFn, RecursiveJoinComposition.map]
    simpa only [List.map_ofFn, Function.comp_def, id_eq] using
      KeyedNaryGuards.alternatives_same (List.ofFn id)
        (fun index => (branches index).shape token known)
        (fun index => KeyedGuards.shape token known (.map id (branches index).checked.body.value))
        (fun index _ => (branches index).size token known)

/-- Each heterogeneous join argument retains its original occurrence metadata. -/
inductive Chain (Key Root Symbol : Type) : Type → Type → Type 1 where
  | nil : Chain Key Root Symbol Result Result
  | cons (argument : Body Key Root Symbol Argument) (rest : Chain Key Root Symbol Operand Result) :
      Chain Key Root Symbol (Argument → Operand) Result

/-- Erase only metadata certificates, retaining the checked callback compiler. -/
def Chain.lower : Chain Key Root Symbol Operand Result → RecursiveJoinBodyFields.Chain Key Root Symbol Operand Result
  | .nil => .nil
  | .cons argument rest => .cons argument.checked rest.lower

/-- Read the ordered source argument shapes under one probe environment. -/
def Chain.shapes (token : Nat) (known : GroupedProbe.Table Key) : Chain Key Root Symbol Operand Result → List Shape
  | .nil => []
  | .cons argument rest => argument.shape token known :: rest.shapes token known

/-- The actual join index folds products from the operation toward the last argument. -/
def foldShape (operation : Shape) (arguments : List Shape) : Shape :=
  arguments.foldl Shape.product operation

/-- The metadata fold agrees with every typed accumulation step. -/
theorem Chain.accumulate_size (arguments : Chain Key Root Symbol Operand Result)
    (token : Nat) (known : GroupedProbe.Table Key)
    (source : RecursiveJoinComposition.Compiled Key Root Symbol Operand (RecursiveJoinFields.Accumulated Symbol))
    (operation : Shape) (same : SameSize operation (KeyedGuards.shape token known source.value)) :
    SameSize (foldShape operation (arguments.shapes token known))
      (KeyedGuards.shape token known
        (RecursiveJoinComposition.accumulate source arguments.lower.lower).value) := by
  induction arguments generalizing operation with
  | nil => exact same
  | cons argument rest ih =>
      apply ih
      exact product_same _ _ _ _ same (argument.size token known)

/-- Every full join keeps its operation metadata and folds one product per argument. -/
def join (component : Nat) (operation : Body Key Root Symbol Operand) (arguments : Chain Key Root Symbol Operand Result) :
    Body Key Root Symbol Result where
  checked := RecursiveJoinBodyFields.join component operation.checked arguments.lower
  shape := fun token known => foldShape (operation.shape token known) (arguments.shapes token known)
  size := by
    intro token known
    exact arguments.accumulate_size token known _ _ (operation.size token known)

/-- Minimum discovery reads the original body shape even when labels erase to pay. -/
theorem minimum_exact (body : Body Key Root Symbol Value) (token : Nat) (known : GroupedProbe.Table Key) :
    (summary (body.shape token known)).minimum =
      (GroupedMinimum.evaluate (KeyedSource.minimumExpr body.checked.body.value) known).join :=
  (body.size token known).1.trans (KeyedGuards.shape_minimum token known body.checked.body.value)

/-- The original size flag is exactly the guard needed by source family semantics. -/
theorem size_guard_exact (body : Body Key Root Symbol Value) (token : Nat) (known : GroupedProbe.Table Key) :
    KeyedSource.guarded body.checked.body.value known = true ↔
      token ∉ (summary (body.shape token known)).unguarded := by
  rw [(body.size token known).2.1]
  exact KeyedGuards.size_guard_exact token known body.checked.body.value

/-- Original used-token metadata survives all composite joins and label erasure. -/
theorem used_exact (body : Body Key Root Symbol Value) (token : Nat) (known : GroupedProbe.Table Key) :
    KeyedGuards.used body.checked.body.value = true ↔ token ∈ (summary (body.shape token known)).used := by
  rw [(body.size token known).2.2]
  exact KeyedGuards.used_exact token known body.checked.body.value

/-- The public check combines the proved size guard with original termless metadata. -/
theorem public_guard_exact (body : Body Key Root Symbol Value) (token : Nat) (known : GroupedProbe.Table Key) :
    OccurrenceGuard.isUnguarded token (body.shape token known) = false ↔
      KeyedSource.guarded body.checked.body.value known = true ∧
      token ∉ (summary (body.shape token known)).termless := by
  rw [size_guard_exact body token known]
  simp [OccurrenceGuard.isUnguarded]

/-- Product minimum follows the exact left fold used by the source index. -/
theorem fold_minimum (operation : Shape) (arguments : List Shape) :
    (summary (foldShape operation arguments)).minimum =
      (arguments.map fun argument => (summary argument).minimum).foldl
        RecursionProbe.productMinimum (summary operation).minimum := by
  induction arguments generalizing operation with
  | nil => rfl
  | cons argument rest ih => exact ih (.product operation argument)

/-- The nullary case retains the operation's termless flags. Every nonempty
chain clears them through a source product, not through the final JoinN map. -/
theorem fold_termless (operation : Shape) (arguments : List Shape) :
    (summary (foldShape operation arguments)).termless =
      if arguments.isEmpty then (summary operation).termless else [] := by
  induction arguments generalizing operation with
  | nil => rfl
  | cons argument rest ih =>
      change (summary (foldShape (.product operation argument) rest)).termless = []
      rw [ih]
      cases rest <;> rfl

/-- The fold retains every syntactically used token from the operation and
every argument, even when one product has no finite members. -/
theorem fold_used (operation : Shape) (arguments : List Shape) (token : Nat) :
    token ∈ (summary (foldShape operation arguments)).used ↔
      token ∈ (summary operation).used ∨ ∃ argument ∈ arguments, token ∈ (summary argument).used := by
  induction arguments generalizing operation with
  | nil => simp [foldShape]
  | cons argument rest ih =>
      change token ∈ (summary (foldShape (.product operation argument) rest)).used ↔ _
      rw [ih]
      simp [summary, OccurrenceGuard.union, or_assoc]

/-- Original join metadata is exactly the source left fold for all three token sets. -/
theorem join_summary (component : Nat) (operation : Body Key Root Symbol Operand)
    (arguments : Chain Key Root Symbol Operand Result) (token : Nat) (known : GroupedProbe.Table Key) :
    summary ((join component operation arguments).shape token known) =
      summary ((arguments.shapes token known).foldl Shape.product (operation.shape token known)) := rfl

/-- A nullary join retains all flags of the operation, including termless flags. -/
theorem join_nil_summary (component : Nat) (operation : Body Key Root Symbol Value)
    (token : Nat) (known : GroupedProbe.Table Key) :
    summary ((join component operation .nil).shape token known) = summary (operation.shape token known) := rfl

/-- A nonempty join always clears the termless set, irrespective of size or productivity. -/
theorem join_cons_termless (component : Nat) (operation : Body Key Root Symbol (Argument → Operand))
    (argument : Body Key Root Symbol Argument) (rest : Chain Key Root Symbol Operand Result)
    (token : Nat) (known : GroupedProbe.Table Key) :
    (summary ((join component operation (.cons argument rest)).shape token known)).termless = [] := by
  exact fold_termless _ (_ :: _) |>.trans (by rfl)

/-- A nonempty join passes the public check exactly when it passes the
minimum-based size guard. A nullary join still needs the operation's term guard. -/
theorem join_cons_public_guard (component : Nat) (operation : Body Key Root Symbol (Argument → Operand))
    (argument : Body Key Root Symbol Argument) (rest : Chain Key Root Symbol Operand Result)
    (token : Nat) (known : GroupedProbe.Table Key) :
    OccurrenceGuard.isUnguarded token ((join component operation (.cons argument rest)).shape token known) = false ↔
      KeyedSource.guarded (join component operation (.cons argument rest)).checked.body.value known = true := by
  rw [public_guard_exact, join_cons_termless]
  simp

/-- Remove occurrence metadata after each constructor has established its local laws. -/
def lower (program : Key → Body Key Root Symbol Root) : Key → RecursiveJoinComposition.Body Key Root Symbol Root :=
  fun key => (program key).checked.body

/-- Public label-aware checks imply every value-family size guard, including nested joins. -/
theorem public_value_guards (token : Nat) (keys : List Key) (complete : ∀ key, key ∈ keys)
    (program : Key → Body Key Root Symbol Root)
    (accepted : ∀ key, OccurrenceGuard.isUnguarded token
      ((program key).shape token (KeyedSource.minima keys complete
        (RecursiveJoinFamily.valueProgram (lower program)))) = false) :
    ∀ key, KeyedSource.guarded (RecursiveJoinFamily.valueProgram (lower program) key)
      (KeyedSource.minima keys complete (RecursiveJoinFamily.valueProgram (lower program))) = true :=
  fun key => ((public_guard_exact (program key) token _).mp (accepted key)).1

/-- Constructor-derived minimum expressions make all three family probe results equal. -/
theorem family_minima_equal (keys : List Key) (complete : ∀ key, key ∈ keys)
    (code : Key → Nat) (program : Key → Body Key Root Symbol Root) :
    KeyedSource.minima keys complete (RecursiveJoinFamily.pairedProgram code (lower program)) =
      KeyedSource.minima keys complete (RecursiveJoinFamily.valueProgram (lower program)) ∧
    KeyedSource.minima keys complete (RecursiveJoinFamily.termProgram code (lower program)) =
      KeyedSource.minima keys complete (RecursiveJoinFamily.valueProgram (lower program)) :=
  RecursiveJoinFamily.minima_equal keys complete code (lower program)

/-- The actual combined public rejection check supplies all three semantic
family guards. No global guard or projection correspondence is a premise. -/
theorem public_family_guards (token : Nat) (keys : List Key) (complete : ∀ key, key ∈ keys)
    (code : Key → Nat) (program : Key → Body Key Root Symbol Root)
    (accepted : ∀ key, OccurrenceGuard.isUnguarded token
      ((program key).shape token (KeyedSource.minima keys complete
        (RecursiveJoinFamily.valueProgram (lower program)))) = false) :
    (∀ key, KeyedSource.guarded (RecursiveJoinFamily.valueProgram (lower program) key)
      (KeyedSource.minima keys complete (RecursiveJoinFamily.valueProgram (lower program))) = true) ∧
    (∀ key, KeyedSource.guarded (RecursiveJoinFamily.pairedProgram code (lower program) key)
      (KeyedSource.minima keys complete (RecursiveJoinFamily.pairedProgram code (lower program))) = true) ∧
    (∀ key, KeyedSource.guarded (RecursiveJoinFamily.termProgram code (lower program) key)
      (KeyedSource.minima keys complete (RecursiveJoinFamily.termProgram code (lower program))) = true) := by
  have values := public_value_guards token keys complete program accepted
  exact ⟨values, RecursiveJoinFamily.family_guards keys complete code (lower program) values⟩

/-- Public checks give exact independent finite derivations for the complete
correlated family, including arbitrary joins inside other constructors. -/
theorem public_paired_exact (token : Nat) (keys : List Key) (complete : ∀ key, key ∈ keys)
    (code : Key → Nat) (program : Key → Body Key Root Symbol Root)
    (accepted : ∀ key, OccurrenceGuard.isUnguarded token
      ((program key).shape token (KeyedSource.minima keys complete
        (RecursiveJoinFamily.valueProgram (lower program)))) = false)
    (size : Nat) (key : Key) (value : Root) (term : KeyedNaryAlignment.EngineTerm Symbol) :
    (value, term) ∈ Decoder.values
      (KeyedSource.family (RecursiveJoinFamily.pairedProgram code (lower program)) size key).members.plan ↔
      KeyedSource.Derives (RecursiveJoinFamily.pairedProgram code (lower program))
        (RecursiveJoinFamily.pairedProgram code (lower program) key) (value, term) size :=
  RecursiveJoinFamily.paired_exact keys complete code (lower program)
    (public_value_guards token keys complete program accepted) size key value term

/-- Accepted metadata excludes every shape context that adds no size or
constructor step. The shape retains labels before value erasure. -/
theorem context_growth (body : Body Key Root Symbol Value) (token : Nat) (known : GroupedProbe.Table Key)
    (accepted : OccurrenceGuard.isUnguarded token (body.shape token known) = false)
    (context : OccurrenceGuard.Context) (present : context ∈ OccurrenceGuard.contexts (body.shape token known))
    (same : context.token = token) (holeSize holeNodes : Nat) :
    holeSize < holeSize + context.size ∧ holeNodes < holeNodes + context.nodes :=
  OccurrenceGuard.guarded_context_growth _ token accepted context present same holeSize holeNodes

/-- Pay and label remain distinct even when either encloses a nullary join. -/
theorem nullary_pay_label (token : Nat) (assumed : Option Nat) :
    OccurrenceGuard.isUnguarded token (.pay (foldShape (.occurrence token assumed) [])) = true ∧
    OccurrenceGuard.isUnguarded token (.constructor (foldShape (.occurrence token assumed) [])) = false := by
  simp [foldShape, OccurrenceGuard.isUnguarded, summary]

/-- A zero-size argument does not guard a recursive operation. A positive
argument guards it, and both products clear the termless token. -/
theorem sibling_cases (token : Nat) (assumed : Option Nat) :
    OccurrenceGuard.isUnguarded token (foldShape (.occurrence token assumed) [.source [0]]) = true ∧
    OccurrenceGuard.isUnguarded token (foldShape (.occurrence token assumed) [.source [1]]) = false ∧
    (summary (foldShape (.occurrence token assumed) [.source [0]])).termless = [] := by
  simp [foldShape, OccurrenceGuard.isUnguarded, summary, OccurrenceGuard.beside, OccurrenceGuard.union]

/-- Three arguments combine in source order and retain the family used flag
even when an empty operand makes the minimum absent. -/
theorem empty_ternary_used :
    (summary (foldShape (.occurrence 7 (some 0)) [.source [0], .source [], .source [2]])).minimum = none ∧
    (summary (foldShape (.occurrence 7 (some 0)) [.source [0], .source [], .source [2]])).termless = [] ∧
    7 ∈ (summary (foldShape (.occurrence 7 (some 0)) [.source [0], .source [], .source [2]])).used := by
  decide +kernel

/-- A nested typed fixture keeps labels distinct from pay and uses two
different argument types in the outer join. -/
def nested [DecidableEq Symbol] (callbacks : KeyedNaryFields.LeafCallbacks Symbol)
    (key : Key) (symbol : Symbol) : Body Key Nat Symbol Nat :=
  let recursive : Body Key Nat Symbol Nat := ofNary callbacks (.occurrence key)
    (by simp [KeyedNaryFields.LeavesExact])
  let operation := map (fun n (flag : Bool) (other : Nat) => if flag then n + other else other) recursive
  let flag := label symbol (map (fun n => n == 0) recursive)
  let argument := pay (join 3 recursive .nil)
  join 2 operation (.cons flag (.cons argument .nil))

/-- The constructor-derived fixture has exact minimum, public acceptance,
and retained used-token metadata under a settled zero-size recursive root. -/
theorem nested_metadata [DecidableEq Symbol] (callbacks : KeyedNaryFields.LeafCallbacks Symbol)
    (key : Key) (symbol : Symbol) (token : Nat) :
    (summary ((nested callbacks key symbol).shape token (fun _ => some (some 0)))).minimum = some 2 ∧
    OccurrenceGuard.isUnguarded token ((nested callbacks key symbol).shape token (fun _ => some (some 0))) = false ∧
    token ∈ (summary ((nested callbacks key symbol).shape token (fun _ => some (some 0)))).used := by
  simp [nested, map, label, pay, join, ofNary, Chain.shapes, foldShape,
    KeyedNaryGuards.shape, summary, OccurrenceGuard.isUnguarded, OccurrenceGuard.beside,
    OccurrenceGuard.union, RecursionProbe.productMinimum]

end MicroCFTA.RecursiveJoinGuards
