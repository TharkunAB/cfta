import MicroCFTA.SourceCurrentEmptinessMemo
import MicroCFTA.SourceEndpointReachability
import MicroCFTA.SourceMemoGate
import MicroCFTA.EnumerationState

/-!
# Current merge pruning guards and suspended constraints

Only two present unenumerated values form an intersection. Pruning tests
the initial recursion flag, then descendant reachability, then the separate
emptiness memo. Errors retain source precedence. The Boolean adapter states
literal value selection. The operational check graph derives conservative
replacement from actual completed memo calls. This module does not execute
the complete enumerator or transfer source lazy thunk demand.
-/
namespace MicroCFTA.SourceCurrentEmptinessMerge
noncomputable section
open Language InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredCache SourceEqualityNativeScoped
open InternedGuardedLanguage (meaning)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Value" => InternedConstructorTemplates.Value Symbol Guard
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin

/-- The moved source helper retains its existing complete-record traversal. -/
abbrev reaches (value : Value) : Bool := SourceEndpointReachability.reaches SourceMemoGate.unconstrained value

/-- The source initializer computes one recursion flag from the original root. -/
def initialFlag (root : Value) : Bool := reaches root

/-- Slot contents retain the original suspended equality constraints. -/
inductive UVarValue where
  | unenumerated (node : Option Value) (constraints : List EnumerationState.Suspended)
  | enumerated (fragment : Fragments.Fragment Symbol)
  | eliminated

/-- The pure result adapter retains the source's three nested guard tests. -/
def emptyIfProvably (checkEmpty : Bool) (answer : Value → Bool) (value : Value) : Value :=
  if checkEmpty then if reaches value then if answer value then .empty else value else value else value

/-- The source slot merge preserves errors and concatenates constraints in input order. -/
def intersectValues (intersect : Value → Value → Value) (checkEmpty : Bool) (answer : Value → Bool) :
    UVarValue → UVarValue → Except String UVarValue
  | .unenumerated first left, .unenumerated second right =>
      .ok (.unenumerated (match first, second with
        | none, other => other
        | other, none => other
        | some first, some second => some (emptyIfProvably checkEmpty answer (intersect first second))) (left ++ right))
  | .eliminated, _ => .error "intersectUVarValue: Unexpected UVarEliminated"
  | _, .eliminated => .error "intersectUVarValue: Unexpected UVarEliminated"
  | _, _ => .error "intersectUVarValue: Intersecting with enumerated value not implemented"

/-- A missing left node skips intersection and all pruning guards. -/
theorem missing_left (intersect : Value → Value → Value) (checkEmpty : Bool) (answer : Value → Bool)
    (node : Option Value) (left right : List EnumerationState.Suspended) :
    intersectValues intersect checkEmpty answer (.unenumerated none left) (.unenumerated node right) =
      .ok (.unenumerated node (left ++ right)) := rfl

/-- A missing right node skips intersection and all pruning guards. -/
theorem missing_right (intersect : Value → Value → Value) (checkEmpty : Bool) (answer : Value → Bool)
    (node : Option Value) (left right : List EnumerationState.Suspended) :
    intersectValues intersect checkEmpty answer (.unenumerated node left) (.unenumerated none right) =
      .ok (.unenumerated node (left ++ right)) := by cases node <;> rfl

/-- Only two present nodes reach the actual ordered intersection and pruning result. -/
theorem present (intersect : Value → Value → Value) (checkEmpty : Bool) (answer : Value → Bool)
    (first second : Value) (left right : List EnumerationState.Suspended) :
    intersectValues intersect checkEmpty answer (.unenumerated (some first) left) (.unenumerated (some second) right) =
      .ok (.unenumerated (some (emptyIfProvably checkEmpty answer (intersect first second))) (left ++ right)) := rfl

/-- An eliminated left slot selects its exact source error before enumerated-slot errors. -/
theorem eliminated_left (intersect : Value → Value → Value) (checkEmpty : Bool) (answer : Value → Bool)
    (right : UVarValue) :
    intersectValues intersect checkEmpty answer .eliminated right =
      .error "intersectUVarValue: Unexpected UVarEliminated" := rfl

/-- An eliminated right slot also selects the eliminated error for every left slot. -/
theorem eliminated_right (intersect : Value → Value → Value) (checkEmpty : Bool) (answer : Value → Bool)
    (left : UVarValue) :
    intersectValues intersect checkEmpty answer left .eliminated =
      .error "intersectUVarValue: Unexpected UVarEliminated" := by cases left <;> rfl

/-- A false initial flag retains the intersection without reading either later guard. -/
theorem disabled (answer : Value → Bool) (value : Value) : emptyIfProvably false answer value = value := rfl

/-- A false descendant result retains the intersection without an emptiness query. -/
theorem clear (answer : Value → Bool) (value : Value) (absent : reaches value = false) :
    emptyIfProvably true answer value = value := by simp only [emptyIfProvably, absent, Bool.false_eq_true, ↓reduceIte]

/-- The actual ordered pruning graph calls only the separate fourth memo family. -/
inductive Check [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat} :
    Bool → Value → Native width Symbol Guard → SourceCurrentEmptinessMemo.Memo →
      Value → Native width Symbol Guard → SourceCurrentEmptinessMemo.Memo → Prop where
  | disabled : Check false input before memo input before memo
  | clear (absent : reaches input = false) : Check true input before memo input before memo
  | query (reached : reaches input = true)
      (actual : SourceCurrentEmptinessMemo.Call memo input before answer after saved) :
      Check true input before memo (if answer then .empty else input) after saved

/-- Actual pruning preserves native invariants and every earlier completed emptiness entry. -/
theorem Check.effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {input result : Value} {before after : Native width Symbol Guard} {memo saved : SourceCurrentEmptinessMemo.Memo}
    (check : Check enabled input before memo result after saved) (ready : IdleReady top conjoin before)
    (fields : SourceEqualityNativeDemandFieldHeap.Heap before.machine.heap)
    (available : Available before.machine.heap input)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.machine.heap memo) :
    IdleReady top conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧
      SourceEqualityNativeDemandFieldHeap.Heap after.machine.heap ∧
      SourceCurrentEmptinessMemo.Correct formulas solver after.machine.heap saved ∧
      SourceCurrentEmptinessMemo.Extends memo saved := by
  cases check with
  | disabled => exact ⟨ready, pure_keeps _ ready.semantic.ready, fields, correct, fun _ _ found => found⟩
  | clear => exact ⟨ready, pure_keeps _ ready.semantic.ready, fields, correct, fun _ _ found => found⟩
  | query _ actual =>
      have checked := SourceCurrentEmptinessMemo.verified formulas solver actual ready fields available correct
      exact ⟨checked.1, checked.2.1, checked.2.2.1, checked.2.2.2.1, checked.2.2.2.2.2⟩

/-- Replacing a node by EmptyNode after an actual true query preserves its language. -/
theorem Check.exact [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {input result : Value} {before after : Native width Symbol Guard} {memo saved : SourceCurrentEmptinessMemo.Memo}
    (check : Check enabled input before memo result after saved) (ready : IdleReady top conjoin before)
    (fields : SourceEqualityNativeDemandFieldHeap.Heap before.machine.heap)
    (available : Available before.machine.heap input)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.machine.heap memo) :
    ∀ ambient term, meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term ↔
      meaning (SourceEqualityPCSGuard.holds formulas solver) ambient input term := by
  cases check with
  | disabled => intro ambient term; rfl
  | clear => intro ambient term; rfl
  | @query _ _ _ answer _ _ _ actual =>
      have checked := SourceCurrentEmptinessMemo.verified formulas solver actual ready fields available correct
      cases answer with
      | false => intro ambient term; rfl
      | true =>
          intro ambient term
          have excluded := checked.2.2.2.2.1.2 rfl ambient term
          constructor
          · intro impossible
            simp only [↓reduceIte, meaning] at impossible
          · intro accepted
            exact False.elim (excluded accepted)

end
end MicroCFTA.SourceCurrentEmptinessMerge
