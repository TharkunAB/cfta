import Lean
import IndexedTrace

/-!
# Checking a compiled stack table

Run `scripts/check-compiled-stack.sh` to build the exporter, capture the Z3
decisions, and check this file with Lean 4.26.0. Supply an exported TSV file
as the script argument to check that file. The first row lists the eleven
schema names in declaration order. Each input row records an output code or
`-` for each schema. The initial `start` node has its own input row. Each
`order` row preserves the predecessor/schema indices that the graph links
for one output. The `rank` rows give the annotated schemas in Haskell rank
order for lengths zero through two.

The compiled step relation stores output states. Haskell decodes replies
separately. This check compares the projection of the Lean decision onto
its output state. It also checks the finite rank streams below.
-/

open CFTA.IndexedTrace CFTA.IndexedTrace.Stack

namespace CFTA.CompiledStack

private def names : List String :=
  ["push-int-0", "push-int-1", "push-bool-False", "push-bool-True", "pop-int",
   "pop-bool", "add", "and", "equal-int", "equal-bool", "not"]

-- Parse the TSV as data. The kernel receives a literal list of natural numbers.
private def parseRow (line : String) : Except String (List Nat) := do
  let required (msg : String) (value : Option Nat) := match value with
    | some n => Except.ok n
    | none => Except.error msg
  let number (s : String) := required ("invalid number " ++ s) s.toNat?
  let choice (s : String) := required ("unknown schema " ++ s) (names.findIdx? (· == s))
  let source (s : String) := do
    let [input, c] := s.splitOn "/" | throw ("invalid predecessor/schema " ++ s)
    return [← number input, ← number c]
  match line.splitOn "\t" with
  | "schemas" :: cs => return 0 :: (← cs.mapM choice)
  | kind :: input :: outputs => match kind with
    | "start" | "step" =>
      let fields ← outputs.mapM fun s => if s == "-" then pure 0 else (· + 1) <$> number s
      return [if kind == "start" then 1 else 2, ← number input] ++ fields
    | "order" =>
      let out :: edges := outputs | throw "missing output block"
      let tag ← match input with
        | "start" => pure 3
        | "step" => pure 4
        | _ => throw "invalid predecessor kind"
      return [tag, ← number out] ++ (← edges.mapM source).flatten
    | "rank" =>
      let [events] := outputs | throw "invalid rank row"
      let cs ← if events.isEmpty then pure [] else (events.splitOn ",").mapM choice
      return [5, ← number input] ++ cs
    | _ => throw ("unknown row " ++ kind)
  | _ => throw "invalid row"

elab "stackRowsFrom " data:term : term => do
  let .lit (.strVal text) ← Lean.Elab.Term.elabTerm data (some (Lean.mkConst ``String))
    | throwError "expected a text literal"
  let lines := text.splitOn "\n"
  let lines := if lines.getLast? == some "" then lines.dropLast else lines
  let mut rows := #[]
  for (line, i) in lines.zipIdx do
    match parseRow line with
    | .ok row => rows := rows.push row
    | .error msg => throwError "compiled stack line {i + 1}: {msg}"
  return Lean.toExpr rows.toList

private def captured : List (List Nat) := stackRowsFrom (include_str "compiled-stack.tsv")

private def stacks : Nat → List (List Ty)
  | 0 => [[]]
  | n + 1 => [Ty.int, Ty.bool].flatMap fun ty => (stacks n).map (ty :: ·)

-- The graph builder visits stacks by depth, then by the types from the top.
private def inputOrder : List State :=
  ((List.range 4).flatMap stacks).filterMap fun stack =>
    if h : encode stack < 15 then some ⟨encode stack, h⟩ else none

private def tableRows (step : Decision 15 11 Reply) : List (List Nat) := Id.run do
  let states := List.finRange 15
  let choices := List.finRange 11
  let mut rows := [0 :: List.range 11]
  for (tag, inputs) in [(1, [0]), (2, states)] do
    for input in inputs do
      let fields := choices.map fun c =>
        match step input c with
        | some (_, out) => out.val + 1
        | none => 0
      rows := rows ++ [[tag, input.val] ++ fields]
  for (tag, inputs) in [(3, [0]), (4, inputOrder)] do
    for out in states do
      let sources := inputs.flatMap fun input =>
        choices.flatMap fun c =>
          if (step input c).map Prod.snd == some out then [input.val, c.val] else []
      rows := rows ++ [[tag, out.val] ++ sources]
  return rows

private def capturedSteps := captured.takeWhile (fun row => row.head? != some 5)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem captured_contract : capturedSteps = tableRows contract := by decide

-- contract_agrees links the arithmetic decisions to the list interpreter.
theorem captured_model : capturedSteps = tableRows modelDecision := by
  rw [captured_contract, funext (fun s => funext (contract_agrees s))]

private def readStep (row : Nat) (c : Choice) : Option (Unit × State) := do
  let fields ← captured[row]?
  let some (out + 1) := fields[2 + c.val]? | none
  if h : out < 15 then some ((), ⟨out, h⟩) else none

private def modelStep : Decision 15 11 Unit := fun s c =>
  (modelDecision s c).map (fun (_, out) => ((), out))

-- Row 1 represents start. Rows 2 through 16 represent step predecessors.
theorem compiled_initial : ∀ c : Choice, readStep 1 c = modelStep 0 c := by decide

theorem compiled_step : ∀ (s : State) (c : Choice), readStep (2 + s.val) c = modelStep s c := by decide

-- This order is the forward choice order of enumerate. The Haskell graph has its own ranks.
theorem compiled_forward_traces (length : Nat) (initial : State) :
    enumerate (fun s => readStep (2 + s.val)) length initial = enumerate modelStep length initial :=
  enumerate_congr _ _ compiled_step length initial

private def commands (trace : List (Choice × Reply) × State) : List Nat :=
  trace.1.map (fun e => e.1.val)

-- Through length two, the imported graph orders by final state code, then by
-- the outermost (last) schema, then by the preceding schema.
private def reverseChoiceOrder : Nat → List (List Choice)
  | 0 => [[]]
  | n + 1 => (List.finRange 11).flatMap fun last => (reverseChoiceOrder n).map (· ++ [last])

private def smallRankRows (n : Nat) : List (List Nat) :=
  (List.finRange 15).flatMap fun out =>
    (reverseChoiceOrder n).filterMap fun choices =>
      let final := choices.foldlM (fun s c => (modelDecision s c).map Prod.snd) (0 : State)
      if final == some out then some ([5, n] ++ choices.map Fin.val) else none

private def allRows := tableRows modelDecision ++ [0, 1, 2].flatMap smallRankRows

private def firstDifference {α : Type} [BEq α] : List α → List α → Nat → Option Nat
  | [], [], _ => none
  | a :: as, b :: bs, i => if a == b then firstDifference as bs (i + 1) else some i
  | _, _, i => some i

#eval do
  if let some i := firstDifference captured allRows 0 then
    IO.eprintln s!"compiled stack mismatch on certificate line {i+1}\n  Haskell: {captured[i]?}\n  Lean:    {allRows[i]?}"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem captured_rows_and_small_ranks : captured = allRows := by decide

-- Haskell rank zero pushes integer 0 and pops. The forward interpreter pushes twice.
example : (captured.find? (fun r => r.take 2 == [5, 2])) = some [5, 2, 0, 4] ∧
    ((enumerate modelDecision 2 0).map commands).head? = some [0, 0] := by decide

end CFTA.CompiledStack
