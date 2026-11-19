import Std

/-!
# Closed transition decisions for bounded traces

Run with `lean +leanprover/lean4:v4.26.0 docs/proofs/IndexedTrace.lean`.

The model enumerates finite ordered choices at each step. Its stack instance
uses the 15 state codes and 11 contract alternatives of
`StateMachineTraceLanguage.hs`. The arithmetic decisions and the list-based
stack model have separate definitions. Lean checks every state and choice.

The model contains closed, two-valued decisions. The Haskell correspondence
requires that the compiled decisions agree on every reachable state and
choice, that cache keys fix those decisions, and that rank enumeration uses
the same alternative order. The proof does not cover Z3, `Unknown`, label
grouping, the generic LTA compiler, or the concrete value-stack interpreter.
-/

namespace CFTA.IndexedTrace

/-- The result of one closed contract decision. -/
abbrev Decision (states choices : Nat) (Reply : Type) :=
  Fin states → Fin choices → Option (Reply × Fin states)

section

variable {states choices : Nat} {Reply : Type}

/-- The trace relation of a deterministic interpreter. -/
def Accepts (step : Decision states choices Reply) (initial : Fin states) :
    List (Fin choices × Reply) → Fin states → Prop
  | [], final => final = initial
  | (choice, reply) :: rest, final =>
    ∃ next, step initial choice = some (reply, next) ∧ Accepts step next rest final

/-- List traces of one length in the order of the transition choices. -/
def enumerate (step : Decision states choices Reply) :
    Nat → Fin states → List (List (Fin choices × Reply) × Fin states)
  | 0, initial => [([], initial)]
  | length + 1, initial =>
    (List.finRange choices).flatMap fun choice =>
      match step initial choice with
      | none => []
      | some (reply, next) =>
        (enumerate step length next).map fun (rest, final) => ((choice, reply) :: rest, final)

/-- Enumeration agrees with the trace relation and the requested length. -/
theorem mem_enumerate (step : Decision states choices Reply) (length : Nat)
    (initial final : Fin states) (events : List (Fin choices × Reply)) :
    (events, final) ∈ enumerate step length initial ↔
      events.length = length ∧ Accepts step initial events final := by
  induction length generalizing initial final events with
  | zero => cases events <;> simp [enumerate, Accepts]
  | succ length ih =>
    simp only [enumerate, List.mem_flatMap]
    constructor
    · rintro ⟨choice, _, member⟩
      cases result : step initial choice with
      | none => simp [result] at member
      | some outcome =>
        obtain ⟨reply, next⟩ := outcome
        simp only [result, List.mem_map] at member
        obtain ⟨⟨rest, last⟩, member, equality⟩ := member
        cases equality
        obtain ⟨len, accepted⟩ := (ih next last rest).mp member
        exact ⟨by simp [len], ⟨next, result, accepted⟩⟩
    · rintro ⟨len, accepted⟩
      cases events with
      | nil => simp at len
      | cons event rest =>
        obtain ⟨choice, reply⟩ := event
        obtain ⟨next, result, accepted⟩ := accepted
        refine ⟨choice, List.mem_finRange choice, ?_⟩
        simp only [result, List.mem_map]
        exact ⟨(rest, final), (ih next final rest).mpr ⟨by simpa using len, accepted⟩, rfl⟩

/-- Store one decision per state and choice. The indices retain their order. -/
def tabulate (step : Decision states choices Reply) :
    Vector (Vector (Option (Reply × Fin states)) choices) states :=
  Vector.ofFn fun state => Vector.ofFn (step state)

/-- Read the decision for one state and choice. -/
def lookup (table : Vector (Vector (Option (Reply × Fin states)) choices) states) :
    Decision states choices Reply :=
  fun state choice => table[state.val][choice.val]

/-- Table lookup returns the original decision for every pair of indices. -/
theorem lookup_eq (step : Decision states choices Reply) : lookup (tabulate step) = step := by
  funext state choice
  simp [lookup, tabulate]

/-- Agreement on every row preserves the whole ordered trace list. -/
theorem enumerate_congr (direct cached : Decision states choices Reply)
    (agree : ∀ s c, direct s c = cached s c) (length : Nat) (initial : Fin states) :
    enumerate direct length initial = enumerate cached length initial := by
  have same : direct = cached := by funext s c; exact agree s c
  rw [same]

/-- Reusing table entries preserves the count and every list position. -/
theorem enumerate_lookup (step : Decision states choices Reply) (length : Nat)
    (initial : Fin states) :
    enumerate (lookup (tabulate step)) length initial = enumerate step length initial := by
  rw [lookup_eq]

end

namespace Stack

inductive Ty where
  | int | bool
  deriving DecidableEq

inductive Reply where
  | accepted | popped (ty : Ty)
  deriving DecidableEq

abbrev State := Fin 15
abbrev Choice := Fin 11

def tag : Ty → Nat
  | .int => 1
  | .bool => 2

def encode : List Ty → Nat
  | [] => 0
  | ty :: rest => 2 * encode rest + tag ty

def decodeUpTo : Nat → Nat → List Ty
  | 0, _ => []
  | _ + 1, 0 => []
  | depth + 1, code =>
    (if code % 2 = 1 then Ty.int else Ty.bool) :: decodeUpTo depth ((code - 1) / 2)

def decode (state : State) : List Ty := decodeUpTo 3 state.val

/-- List-based abstract interpreter in the order of the eleven Haskell schemas.

Choices zero through three push the four distinct literals. The next two
choices are typed instances of Pop. Equal has two typed instances as well.
-/
def model (stack : List Ty) (choice : Choice) : Option (Reply × List Ty) :=
  match choice.val, stack with
  | 0, _ | 1, _ => if stack.length < 3 then some (.accepted, .int :: stack) else none
  | 2, _ | 3, _ => if stack.length < 3 then some (.accepted, .bool :: stack) else none
  | 4, .int :: rest => some (.popped .int, rest)
  | 5, .bool :: rest => some (.popped .bool, rest)
  | 6, .int :: .int :: rest => some (.accepted, .int :: rest)
  | 7, .bool :: .bool :: rest => some (.accepted, .bool :: rest)
  | 8, .int :: .int :: rest => some (.accepted, .bool :: rest)
  | 9, .bool :: .bool :: rest => some (.accepted, .bool :: rest)
  | 10, .bool :: _ => some (.accepted, stack)
  | _, _ => none

/-- Encoded output of the abstract interpreter. -/
def modelDecision : Decision 15 11 Reply := fun state choice =>
  (model (decode state) choice).bind fun (reply, stack) =>
    if h : encode stack < 15 then some (reply, ⟨encode stack, h⟩) else none

/-- Closed arithmetic decisions for the input sets and post-state equations. -/
def contract : Decision 15 11 Reply := fun state choice =>
  let code := state.val
  let intTop := code % 2 = 1
  let boolTop := code > 0 ∧ code % 2 = 0
  let twoInts := code % 4 = 3
  let twoBools := code ≥ 6 ∧ code % 4 = 2
  let output (reply : Reply) (ok : Nat → Bool) :=
    ((List.finRange 15).find? fun candidate => ok candidate.val).map fun next => (reply, next)
  match choice.val with
  | 0 | 1 => if code < 7 then output .accepted (fun out => out == 2 * code + 1) else none
  | 2 | 3 => if code < 7 then output .accepted (fun out => out == 2 * code + 2) else none
  | 4 => if intTop then output (.popped .int) (fun out => code == 2 * out + 1) else none
  | 5 => if boolTop then output (.popped .bool) (fun out => code == 2 * out + 2) else none
  | 6 => if twoInts then output .accepted (fun out => code == 2 * out + 1) else none
  | 7 => if twoBools then output .accepted (fun out => code == 2 * out + 2) else none
  | 8 => if twoInts then output .accepted (fun out => code + 1 == 2 * out) else none
  | 9 => if twoBools then output .accepted (fun out => code == 2 * out + 2) else none
  | 10 => if boolTop then output .accepted (fun out => out == code) else none
  | _ => none

/-- The two definitions agree on all 165 pairs, including rejected pairs. -/
theorem contract_agrees : ∀ s c, contract s c = modelDecision s c := by decide

/-- Encoding the interpreter's results loses no valid bounded step. -/
theorem model_decodes : ∀ s c,
    (modelDecision s c).map (fun (reply, next) => (reply, decode next)) = model (decode s) c := by
  decide

/-- The cached contract language has exactly the abstract interpreter's order. -/
theorem ordered_stack_traces (length : Nat) (initial : State) :
    enumerate (lookup (tabulate contract)) length initial = enumerate modelDecision length initial := by
  rw [enumerate_lookup]
  exact enumerate_congr contract modelDecision contract_agrees length initial

/-- The cached stack traces are exactly the model traces of the requested length. -/
theorem accepted_stack_trace (length : Nat) (initial final : State)
    (events : List (Choice × Reply)) :
    (events, final) ∈ enumerate (lookup (tabulate contract)) length initial ↔
      events.length = length ∧ Accepts modelDecision initial events final := by
  rw [ordered_stack_traces]
  exact mem_enumerate modelDecision length initial final events

end Stack
end CFTA.IndexedTrace
