import MicroCFTA.MergedFreshOrdinaryExposure

/-!
# Native bounded-depth copying

The worker retains the native constructor caches and a local depth memo.
It copies children in source order and keeps the full edge constraints.
The reader cutoff is separate from the signed source depth.
Raw Rec and unresolved reader references use the existing unresolved fault.
The model does not store the source error strings.
Completion, language preservation, and source correspondence remain open.
-/
namespace MicroCFTA.SourceNativeBoundDepth
open Cache InternedConstructorTemplates
open InternedBinderProtocol (Reference NodeKey)

/-- Each local memo entry uses the signed depth and original node identity. -/
abbrev Memo (Symbol Guard : Type) := Cache.Table (Int × Nat) (Value Symbol Guard)

/-- Success and failure retain the exact native heap and local memo. -/
abbrev Result (Symbol Guard Output : Type) :=
  MergedSourceComparison.Result Symbol Guard Output × Memo Symbol Guard

/-- Later work uses only the preceding successful value, heap, and memo. -/
def bind (actual : Result Symbol Guard First)
    (next : First → State Symbol Guard → Memo Symbol Guard → Result Symbol Guard Output) :
    Result Symbol Guard Output :=
  match actual with
  | (.done value after, memo) => next value after memo
  | (.failed fault after, memo) => (.failed fault after, memo)

/-- At depth zero, select leaf rows before any child call. -/
def retained (depth : Int) (edges : List (EdgeValue Symbol Guard)) : List (EdgeValue Symbol Guard) :=
  edges.filter fun edge => decide (0 < depth) || edge.children.isEmpty

/-- Copy children from left to right and stop at the first failed call. -/
def children
    (copy : Value Symbol Guard → State Symbol Guard → Memo Symbol Guard → Result Symbol Guard (Value Symbol Guard)) :
    List (Value Symbol Guard) → State Symbol Guard → Memo Symbol Guard →
      Result Symbol Guard (List (Value Symbol Guard))
  | [], before, memo => (.done [] before, memo)
  | first :: rest, before, memo =>
      bind (copy first before memo) fun value middle nextMemo =>
        bind (children copy rest middle nextMemo) fun values after finalMemo =>
          (.done (value :: values) after, finalMemo)

/-- Rebuild each edge after its complete ordered child list. -/
def edges [DecidableEq (EdgeKey Symbol Guard)]
    (copy : Value Symbol Guard → State Symbol Guard → Memo Symbol Guard → Result Symbol Guard (Value Symbol Guard)) :
    List (EdgeValue Symbol Guard) → State Symbol Guard → Memo Symbol Guard →
      Result Symbol Guard (List (EdgeValue Symbol Guard))
  | [], before, memo => (.done [] before, memo)
  | first :: rest, before, memo =>
      bind (children copy first.children before memo) fun values middle nextMemo =>
        let rebuilt := InternedConstructorTemplates.run
          (makeEdge first.entry.key.symbol first.entry.key.constraint values) middle
        bind (edges copy rest rebuilt.2 nextMemo) fun values after finalMemo =>
          (.done (rebuilt.1 :: values) after, finalMemo)

/-- A memo miss reads rows, copies retained alternatives, and then stores the parent. -/
def interned [DecidableEq (EdgeKey Symbol Guard)]
    (readerFuel : Nat) (depth : Int) (identity : Nat) (value : Value Symbol Guard)
    (copy : Value Symbol Guard → State Symbol Guard → Memo Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (before : State Symbol Guard) (memo : Memo Symbol Guard) : Result Symbol Guard (Value Symbol Guard) :=
  match memo (depth, identity) with
  | some bounded => (.done bounded before, memo)
  | none =>
      match MergedFreshOrdinaryExposure.nodeEdges readerFuel value before with
      | .done original afterRead =>
          bind (edges copy (retained depth original) afterRead memo) fun copied middle nextMemo =>
            let bounded := InternedConstructorTemplates.run (makeNode copied) middle
            (.done bounded.1 bounded.2, Cache.put nextMemo (depth, identity) bounded.1)
      | .unresolved name after => (.failed (.unresolved name) after, memo)
      | .pending key after => (.failed (.pending key) after, memo)
      | .exhausted after => (.failed .exhausted after, memo)

/-- Height zero encodes negative source depth; raw references still fail first. -/
def atHeight [DecidableEq (EdgeKey Symbol Guard)] (readerFuel : Nat) :
    Nat → Value Symbol Guard → State Symbol Guard → Memo Symbol Guard → Result Symbol Guard (Value Symbol Guard)
  | _, .empty, before, memo => (.done .empty before, memo)
  | _, .reference name, before, memo => (.failed (.unresolved name) before, memo)
  | 0, _, before, memo => (.done .empty before, memo)
  | height + 1, value@(.node entry ..), before, memo =>
      interned readerFuel (height : Int) entry.identity value (atHeight readerFuel height) before memo
  | height + 1, value@(.union entry ..), before, memo =>
      interned readerFuel (height : Int) entry.identity value (atHeight readerFuel height) before memo
  | height + 1, value@(.mu entry ..), before, memo =>
      interned readerFuel (height : Int) entry.identity value (atHeight readerFuel height) before memo

/-- Execute one signed-depth request with its current local memo. -/
def run [DecidableEq (EdgeKey Symbol Guard)] (readerFuel : Nat) (depth : Int)
    (value : Value Symbol Guard) (before : State Symbol Guard) (memo : Memo Symbol Guard) :
    Result Symbol Guard (Value Symbol Guard) :=
  atHeight readerFuel (depth + 1).toNat value before memo

/-- The public source operation starts with an empty local depth memo. -/
def boundDepth [DecidableEq (EdgeKey Symbol Guard)] (readerFuel : Nat) (depth : Int)
    (value : Value Symbol Guard) (before : State Symbol Guard) : Result Symbol Guard (Value Symbol Guard) :=
  run readerFuel depth value before (fun _ => none)

/-- Empty input returns before the depth test, row read, and memo lookup. -/
theorem run_empty [DecidableEq (EdgeKey Symbol Guard)] (readerFuel : Nat) (depth : Int)
    (before : State Symbol Guard) (memo : Memo Symbol Guard) :
    run readerFuel depth .empty before memo = (.done .empty before, memo) := by
  simp only [run, atHeight]

/-- Raw Rec fails even at a negative source depth. -/
theorem run_reference [DecidableEq (EdgeKey Symbol Guard)] (readerFuel : Nat) (depth : Int)
    (name : Reference) (before : State Symbol Guard) (memo : Memo Symbol Guard) :
    run readerFuel depth (.reference name) before memo = (.failed (.unresolved name) before, memo) := by
  simp only [run, atHeight]

/-- A negative request returns empty on every input except raw Rec. -/
theorem run_negative [DecidableEq (EdgeKey Symbol Guard)] (readerFuel : Nat) (depth : Int)
    (value : Value Symbol Guard) (before : State Symbol Guard) (memo : Memo Symbol Guard)
    (negative : depth < 0) (notReference : ∀ name, value ≠ .reference name) :
    run readerFuel depth value before memo = (.done .empty before, memo) := by
  have height : (depth + 1).toNat = 0 := by omega
  cases value with
  | empty => exact run_empty readerFuel depth before memo
  | reference name => exact False.elim (notReference name rfl)
  | node entry rows cachedDepth free => simp only [run, height, atHeight]
  | union entry members cachedDepth free => simp only [run, height, atHeight]
  | mu entry body depthShape ordinaryShape => simp only [run, height, atHeight]

/-- Nonnegative signed requests use one more unit of constructor height. -/
theorem run_nat [DecidableEq (EdgeKey Symbol Guard)] (readerFuel depth : Nat)
    (value : Value Symbol Guard) (before : State Symbol Guard) (memo : Memo Symbol Guard) :
    run readerFuel (depth : Int) value before memo = atHeight readerFuel (depth + 1) value before memo := by
  have height : ((depth : Int) + 1).toNat = depth + 1 := by omega
  simp only [run, height]

/-- A cached ordinary result returns without a row read or constructor work. -/
theorem atHeight_node_hit [DecidableEq (EdgeKey Symbol Guard)] (readerFuel height : Nat)
    (entry : Interned NodeKey) (rows : List (EdgeValue Symbol Guard)) (cachedDepth : Nat) (free : List Reference)
    (before : State Symbol Guard) (memo : Memo Symbol Guard) (bounded : Value Symbol Guard)
    (hit : memo ((height : Int), entry.identity) = some bounded) :
    atHeight readerFuel (height + 1) (.node entry rows cachedDepth free) before memo = (.done bounded before, memo) := by
  simp only [atHeight, interned, hit]

/-- A pending Mu read retains its exact failed endpoint and the current memo. -/
theorem atHeight_mu_pending [DecidableEq (EdgeKey Symbol Guard)] (readerFuel height : Nat)
    (entry : Interned NodeKey) (body depthShape ordinaryShape : Value Symbol Guard)
    (before after : State Symbol Guard) (memo : Memo Symbol Guard) (key : NodeKey)
    (miss : memo ((height : Int), entry.identity) = none)
    (observed : MergedFreshOrdinaryExposure.nodeEdges readerFuel (.mu entry body depthShape ordinaryShape) before =
      .pending key after) :
    atHeight readerFuel (height + 1) (.mu entry body depthShape ordinaryShape) before memo =
      (.failed (.pending key) after, memo) := by
  simp only [atHeight, interned, miss, observed]

/-- An exhausted union read retains its exact failed endpoint and the current memo. -/
theorem atHeight_union_exhausted [DecidableEq (EdgeKey Symbol Guard)] (readerFuel height : Nat)
    (entry : Interned NodeKey) (members : List (Value Symbol Guard)) (cachedDepth : Nat) (free : List Reference)
    (before after : State Symbol Guard) (memo : Memo Symbol Guard)
    (miss : memo ((height : Int), entry.identity) = none)
    (observed : MergedFreshOrdinaryExposure.nodeEdges readerFuel (.union entry members cachedDepth free) before =
      .exhausted after) :
    atHeight readerFuel (height + 1) (.union entry members cachedDepth free) before memo =
      (.failed .exhausted after, memo) := by
  simp only [atHeight, interned, miss, observed]

/-- An unresolved union read remains a failure at its actual endpoint. -/
theorem atHeight_union_unresolved [DecidableEq (EdgeKey Symbol Guard)] (readerFuel height : Nat)
    (entry : Interned NodeKey) (members : List (Value Symbol Guard)) (cachedDepth : Nat) (free : List Reference)
    (before after : State Symbol Guard) (memo : Memo Symbol Guard) (name : Reference)
    (miss : memo ((height : Int), entry.identity) = none)
    (observed : MergedFreshOrdinaryExposure.nodeEdges readerFuel (.union entry members cachedDepth free) before =
      .unresolved name after) :
    atHeight readerFuel (height + 1) (.union entry members cachedDepth free) before memo =
      (.failed (.unresolved name) after, memo) := by
  simp only [atHeight, interned, miss, observed]

/-- Depth zero discards nonleaf rows before ordered copying begins. -/
theorem retained_zero (rows : List (EdgeValue Symbol Guard)) :
    retained 0 rows = rows.filter (fun edge => edge.children.isEmpty) := by
  rfl

end MicroCFTA.SourceNativeBoundDepth
