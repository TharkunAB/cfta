import Std

/-!
# Shared work budget of source normal-form quotation

The source charges every quote call before it inspects a value. A beta
marker uses one charge and then quotes its successor. Other values use one
charge before their ordered children. All children share the remaining
budget. Case jobs retain explicit, expanded-default, and fallback order.

Views here are completed finite observations of evaluator values. This
module does not translate Core or prove that closure evaluation reaches
such a view. Pair and identity-case contraction occur after the jobs and
refund no charge. The separate output-size check uses a finite shape.
-/
namespace MicroCFTA.SourceNormalFormBudget

/-- The current source gives one normal form this shared work budget. -/
def reductionBudget : Nat := 1000000

/-- The current source checks this output-node limit after quotation. -/
def outputLimit : Nat := 20000

/-- The literal source spend operation uses a mathematical integer here. -/
def spend (remaining : Int) : Option (Unit × Int) :=
  if remaining > 0 then some ((), remaining - 1) else none

/-- A positive natural budget spends exactly one unit without underflow. -/
theorem spend_succ (remaining : Nat) :
    spend (Int.ofNat (remaining + 1)) = some ((), Int.ofNat remaining) := by
  simp only [spend, Int.ofNat_eq_natCast]
  split <;> simp_all <;> omega

/-- Exhaustion stops before quotation inspects its value. -/
theorem spend_nonpositive (remaining : Int) (exhausted : remaining ≤ 0) : spend remaining = none := by
  simp only [spend]
  split <;> simp_all <;> omega

/-- Finite constructor metadata supplies source case-family order and field counts. -/
structure Constructor where
  key : String
  tag : Int
  arity : Nat
  deriving DecidableEq

/-- Only a constructor alternative supplies a source constructor family. -/
inductive AltKey where
  | constructor (con : Constructor) (family : List Constructor)
  | literal (text : String)
  deriving DecidableEq

/-- The source compares alternative text before expanding a default. -/
def AltKey.text : AltKey → String
  | .constructor con _ => con.key
  | .literal text => text

/-- An explicit case alternative has its applied body and source field count. -/
structure Alternative (State : Type) where
  key : AltKey
  count : Nat
  body : State
  deriving DecidableEq

/-- These are the five source quote branches after a value reaches its outer constructor. -/
inductive View (State : Type) where
  | step (next : State)
  | neutral (arguments : List State)
  | lambda (body : State)
  | constructor (fields : List State)
  | caseOf (scrutinee : State) (alternatives : List (Alternative State)) (fallback : Option State)
  deriving DecidableEq

/-- Every deferred quote retains its actual depth and value. -/
structure Task (State : Type) where
  depth : Nat
  value : State
  deriving DecidableEq

/-- The first constructor alternative supplies the family, including an empty family. -/
def family : List (Alternative State) → List Constructor
  | [] => []
  | alt :: rest => match alt.key with
    | .constructor _ constructors => constructors
    | .literal _ => family rest

/-- Source case quotation visits the scrutinee, explicit alternatives, then default work. -/
def caseJobs (depth : Nat) (scrutinee : State) (alternatives : List (Alternative State))
    (fallback : Option State) : List (Task State) :=
  let constructors := family alternatives
  let present := alternatives.map fun alt => alt.key.text
  let defaults := match fallback with
    | none => []
    | some body => if constructors.isEmpty then [⟨depth, body⟩]
      else (constructors.filter fun con => !present.contains con.key).map fun con => ⟨depth + con.arity, body⟩
  ⟨depth, scrutinee⟩ :: alternatives.map (fun alt => ⟨depth + alt.count, alt.body⟩) ++ defaults

/-- Quotation keeps the exact source child order and does not reset child budgets. -/
def jobs (depth : Nat) : View State → List (Task State)
  | .step next => [⟨depth, next⟩]
  | .neutral arguments | .constructor arguments => arguments.map fun value => ⟨depth, value⟩
  | .lambda body => [⟨depth + 1, body⟩]
  | .caseOf scrutinee alternatives fallback => caseJobs depth scrutinee alternatives fallback

/-- A visited quote either consumes a beta marker or builds a pre-contraction node. -/
inductive Charge where
  | beta
  | node
  deriving DecidableEq

/-- The delayed beta marker is the only branch that does not build a normal-form node. -/
def charge : View State → Charge
  | .step _ => .beta
  | _ => .node

/-- Each observed charge retains its exact deferred quote. -/
structure Visit (State : Type) where
  task : Task State
  charge : Charge
  deriving DecidableEq

/-- Successful quotation retains the shared remainder and its ordered charges. -/
structure Receipt (State : Type) where
  remaining : Nat
  visits : List (Visit State)
  deriving DecidableEq

/-- Execute source quote jobs in depth-first order with one shared decreasing budget. -/
def quoteWork (view : Nat → State → View State) : Nat → List (Task State) → Option (Receipt State)
  | budget, [] => some ⟨budget, []⟩
  | 0, _ :: _ => none
  | budget + 1, task :: rest =>
      let observed := view task.depth task.value
      (quoteWork view budget (jobs task.depth observed ++ rest)).map fun result =>
        {result with visits := ⟨task, charge observed⟩ :: result.visits}

/-- A nonempty quotation at zero fuel fails without requesting any value view. -/
theorem zero (view : Nat → State → View State) (task : Task State) (rest : List (Task State)) :
    quoteWork view 0 (task :: rest) = none := rfl

/-- Every completed prefix accounts for every unit of the shared initial budget. -/
theorem accounting (view : Nat → State → View State) (budget : Nat) (tasks : List (Task State))
    (result : Receipt State) (done : quoteWork view budget tasks = some result) :
    result.visits.length + result.remaining = budget := by
  induction budget generalizing tasks result with
  | zero =>
      cases tasks with
      | nil => cases done; simp
      | cons => cases done
  | succ budget ih =>
      cases tasks with
      | nil => cases done; simp
      | cons task rest =>
          cases called : quoteWork view budget (jobs task.depth (view task.depth task.value) ++ rest) with
          | none => simp only [quoteWork, called, Option.map_none] at done; cases done
          | some first =>
              simp only [quoteWork, called, Option.map_some] at done
              cases done
              have earlier := ih _ _ called
              simp only [List.length_cons]
              omega

/-- Source sequencing passes the first job list's remaining budget to the second list. -/
theorem append (view : Nat → State → View State) (budget : Nat) (first second : List (Task State)) :
    quoteWork view budget (first ++ second) =
      (quoteWork view budget first).bind fun earlier =>
        (quoteWork view earlier.remaining second).map fun later =>
          {later with visits := earlier.visits ++ later.visits} := by
  induction budget generalizing first second with
  | zero =>
      cases first with
      | nil =>
          cases finished : quoteWork view 0 second <;> simp [quoteWork, finished]
      | cons => rfl
  | succ budget ih =>
      cases first with
      | nil =>
          cases finished : quoteWork view (budget + 1) second <;> simp [quoteWork, finished]
      | cons task rest =>
          simp only [List.cons_append, quoteWork]
          rw [← List.append_assoc, ih]
          cases quoteWork view budget (jobs task.depth (view task.depth task.value) ++ rest) with
          | none => rfl
          | some earlier =>
              simp only [Option.bind_some, Option.map_some]
              cases quoteWork view earlier.remaining second <;> simp

/-- Extra budget retains the exact successful visit sequence and increases only its remainder. -/
theorem more_budget (view : Nat → State → View State) (budget extra : Nat) (tasks : List (Task State))
    (result : Receipt State) (done : quoteWork view budget tasks = some result) :
    quoteWork view (budget + extra) tasks = some {result with remaining := result.remaining + extra} := by
  induction budget generalizing tasks result with
  | zero =>
      cases tasks with
      | nil => cases done; simp [quoteWork]
      | cons => cases done
  | succ budget ih =>
      cases tasks with
      | nil => cases done; simp [quoteWork]
      | cons task rest =>
          cases called : quoteWork view budget (jobs task.depth (view task.depth task.value) ++ rest) with
          | none => simp only [quoteWork, called, Option.map_none] at done; cases done
          | some first =>
              simp only [quoteWork, called, Option.map_some] at done
              cases done
              rw [show budget + 1 + extra = (budget + extra) + 1 by omega, quoteWork, ih _ _ called]
              rfl

/-- Count actual delayed beta markers in an ordered quotation receipt. -/
def betas (visits : List (Visit State)) : Nat := (visits.filter fun visit => visit.charge == .beta).length

/-- Count normal-form nodes before source pair and case contraction. -/
def nodes (visits : List (Visit State)) : Nat := (visits.filter fun visit => visit.charge == .node).length

/-- Beta markers and pre-contraction nodes partition all source quote charges. -/
theorem charges (visits : List (Visit State)) : betas visits + nodes visits = visits.length := by
  induction visits with
  | nil => rfl
  | cons visit rest ih =>
      cases visit with
      | mk task kind => cases kind <;> simp_all [betas, nodes] <;> omega

/-- A successful source quotation cannot spend more than its single shared budget. -/
theorem shared_bound (view : Nat → State → View State) (budget : Nat) (tasks : List (Task State))
    (result : Receipt State) (done : quoteWork view budget tasks = some result) :
    betas result.visits + nodes result.visits + result.remaining = budget ∧
      betas result.visits + nodes result.visits ≤ budget := by
  have counted := accounting view budget tasks result done
  rw [← charges result.visits] at counted
  exact ⟨counted, by omega⟩

/-- An endless delayed-beta successor is rejected after every finite budget. -/
theorem step_loop (budget depth : Nat) :
    quoteWork (fun _ (_ : Unit) => .step ()) budget [⟨depth, ()⟩] = none := by
  induction budget with
  | zero => rfl
  | succ budget ih => simp only [quoteWork, jobs, List.singleton_append, ih, Option.map_none]

/-- Only the child shape of a completed normal form matters for the separate node-size check. -/
inductive Shape where
  | node (children : List Shape)

mutual
  /-- Count one node for each completed normal-form constructor. -/
  def shapeNodes : Shape → Nat
    | .node children => 1 + shapeListNodes children
  termination_by shape => sizeOf shape

  /-- Ordered normal-form child lists contribute the sum of their node counts. -/
  def shapeListNodes : List Shape → Nat
    | [] => 0
    | shape :: rest => shapeNodes shape + shapeListNodes rest
  termination_by shapes => sizeOf shapes
end

/-- Appending a pending size frontier adds its exact remaining node counts. -/
theorem shapeListNodes_append (first second : List Shape) :
    shapeListNodes (first ++ second) = shapeListNodes first + shapeListNodes second := by
  induction first with
  | nil => simp [shapeListNodes]
  | cons shape rest ih => simp [shapeListNodes, ih, Nat.add_assoc]

/-- Source size checking charges one node before adding its ordered children. -/
def sizeWork : Nat → List Shape → Bool
  | _, [] => true
  | 0, _ :: _ => false
  | budget + 1, .node children :: rest => sizeWork budget (children ++ rest)

/-- The separate finite output check accepts exactly the requested number of nodes. -/
theorem sizeWork_exact (budget : Nat) (pending : List Shape) :
    sizeWork budget pending = true ↔ shapeListNodes pending ≤ budget := by
  induction budget generalizing pending with
  | zero =>
      cases pending with
      | nil => simp [sizeWork, shapeListNodes]
      | cons shape rest => cases shape; simp [sizeWork, shapeListNodes, shapeNodes]
  | succ budget ih =>
      cases pending with
      | nil => simp [sizeWork, shapeListNodes]
      | cons shape rest =>
          cases shape with
          | node children =>
              rw [sizeWork, ih, shapeListNodes_append]
              simp only [shapeListNodes, shapeNodes]
              omega

/-- The source post-check uses 20,000 output nodes, independently of reduction work. -/
def sizeAtMost (normal : Shape) : Bool := sizeWork outputLimit [normal]

/-- The post-check tests completed output size and does not substitute for the quotation budget. -/
theorem sizeAtMost_exact (normal : Shape) : sizeAtMost normal = true ↔ shapeNodes normal ≤ outputLimit := by
  simpa only [sizeAtMost, shapeListNodes, Nat.add_zero] using sizeWork_exact outputLimit [normal]

end MicroCFTA.SourceNormalFormBudget
