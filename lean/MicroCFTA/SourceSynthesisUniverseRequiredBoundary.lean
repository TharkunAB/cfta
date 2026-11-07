import MicroCFTA.SourceSynthesisUniverseOrigins
import MicroCFTA.SourceEqualityOnePassWorker
import MicroCFTA.SourceEqualityNativeInitial
import MicroCFTA.SourceEqualityNormalizationReceipt
import MicroCFTA.SourceMemoGate
import MicroCFTA.InternedFreshOrdinaryFacts

/-!
# Required type paths can exceed their original application height

The input is an actual FirstOrder library, query, and signed size request.
The observation builds that input and completes its filter equality pass.
It then selects the returned application's classes and runs their actual
required-path worker. Its function annotation exposes the recursive universe.

The height counts ordinary nodes. Unions take the maximum member height.
Mu records and references have height zero. The observed growth refutes
strict descent for this measure. It does not refute termination. The module
does not complete the application's class fold or its outer recursive call.
-/
namespace MicroCFTA.SourceSynthesisUniverseRequiredBoundary
open InternedConstructorTemplates InternedNestedConstruction
open InternedNestedFacts InternedProbeProvenance
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (Guard top)

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option cbv.maxSteps 200000000

private theorem array_small (classes : EqualityNormalize.Constraints) :
    SourceCompactGuards.arrayNormalize classes = SourceEqualityNormalizationReceipt.observed 16 classes :=
  SourceEqualityNormalizationReceipt.observed_eq 16 classes

private theorem eqGuard_small (classes : EqualityNormalize.Constraints) :
    SourceSynthesisGeneralizeSyntax.eqGuard classes =
      ⟨SymbolicEqualityBridge.resultClasses (SourceEqualityNormalizationReceipt.observed 16 classes), .top⟩ := by
  rw [SourceSynthesisGeneralizeSyntax.eqGuard_eq_source]
  unfold SourceCompactGuards.normalize
  rw [array_small]

private theorem combine_small (first second : SourceEqualityPrecheck.Constraint) :
    SourceEqualityPrecheck.combine first second =
      match first, second with
      | none, _ | _, none => .contradiction
      | some [], some [] => .normalized []
      | some left, some right =>
          SourceEqualityNormalizationReceipt.observed 16
            (left.map SourceEqualityClassOrder.Record.paths ++
              right.map SourceEqualityClassOrder.Record.paths) := by
  cases first with
  | none => rfl
  | some left =>
      cases second with
      | none => rfl
      | some right =>
          cases left <;> cases right
          · rfl
          all_goals
            simp only [SourceEqualityPrecheck.combine]
            rw [← SourceCompactGuards.arrayNormalize_eq]
            exact array_small _

attribute [local cbv_eval] array_small eqGuard_small combine_small

private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)

private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) :=
  SourceEqualityPCSNativeEdge.guardDecidableEq

private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)

mutual
/-- Count ordinary layers and read through every explicit union. -/
def transparentHeight : Value Symbol Annotation → Nat
  | .node _ rows _ _ => transparentRows rows + 1
  | .union _ members _ _ => transparentChildren members
  | _ => 0

/-- Take the maximum child height across the complete row list. -/
def transparentRows : List (EdgeValue Symbol Annotation) → Nat
  | [] => 0
  | .mk _ children :: rest => max (transparentChildren children) (transparentRows rest)

/-- Take the maximum height of the complete ordered child list. -/
def transparentChildren : List (Value Symbol Annotation) → Nat
  | [] => 0
  | first :: rest => max (transparentHeight first) (transparentChildren rest)
end

/-- The source component has the literal polymorphic variable type. -/
def library : Library :=
  { libraryGroups := [("f", .tVar "a", [])]
    libraryArgumentOnly := []
    libraryAvoid := []
    libraryEncoding := .firstOrder }

/-- The original query has no required arguments and the first rigid variable. -/
def query : Query := { queryArguments := [], queryGoal := .tVar "a" }

/-- Read the actual size-two source cell and its original query filter. -/
def expression : Expr Guard :=
  SourceSynthesisFirstOrderConstruction.ofType
    (.union (SourceSynthesisFirstOrderConstruction.termsRows
      (SourceSynthesisFirstOrderConstruction.context library query) true 2))
    (typeNode top query.queryGoal)

/-- The signed original request succeeds in the source construction. -/
theorem source_accepts :
    SourceSynthesisFirstOrderConstruction.firstOrderRaw library query 2 = .ok expression := by
  let ctx := SourceSynthesisFirstOrderConstruction.context library query
  have arguments : ctx.argumentEdges = [] := rfl
  have resolved : SourceSynthesisFirstOrderConstruction.resolveArguments ctx [] = some [] :=
    SourceSynthesisSelections.resolveSelection_empty _
  have cell : SourceSynthesisFirstOrderConstruction.relevantRows ctx true 2 [] =
      .ok (SourceSynthesisFirstOrderConstruction.termsRows ctx true 2) := by
    rw [SourceSynthesisFirstOrderConstruction.relevantRows, resolved] <;> rfl
  change Except.bind
    ((SourceSynthesisSelections.permutations ctx.argumentEdges).mapM fun selected =>
      SourceSynthesisFirstOrderConstruction.relevantRows ctx true 2 (selected.map Prod.fst))
    (fun rows => .ok (SourceSynthesisFirstOrderConstruction.ofType (.union rows.flatten)
      (typeNode top query.queryGoal))) = .ok expression
  rw [arguments, SourceSynthesisSelections.permutations_nil]
  simp only [List.mapM_cons, List.mapM_nil, List.map_nil, cell,
    Bind.bind, Except.bind, Pure.pure, Except.pure,
    List.flatten_cons, List.flatten_nil, List.append_nil] <;> rfl

/-- Every original binder is the actual computed default universe. -/
theorem source_universe : SourceSynthesisUniverseOrigins.OverUniverse
    (SourceSynthesisFirstOrderConstruction.typesOf library query) expression :=
  SourceSynthesisUniverseOrigins.firstOrderRaw_overUniverse library query 2 expression source_accepts

private noncomputable def unconstrained (value : Value String Guard) : Bool :=
  InternedSourceCrush.unconstrained SourceMemoGate.plain value

/-- Each stage retains its exact original values and returned constructor cache. -/
structure Receipt where
  root : Value String Guard
  original : State String Guard
  filterRow : EdgeValue String Guard
  filterOwn : SourceEqualityPrecheck.Constraint
  filtered : List (Value String Guard)
  native : SourceRecursiveIntersectionThunks.State 8 String Guard
  application : Value String Guard
  applicationRow : EdgeValue String Guard
  records : List SourceEqualityClassOrder.Record
  queries : List (InternedSourceClassSelection.Query String Guard)
  selected : State String Guard
  required : List (Value String Guard)
  final : State String Guard

/-- Run the actual filter pass and the selected application's required stage. -/
noncomputable def observation : Option Receipt :=
  match InternedFreshOrdinaryConstruction.build expression [] empty with
  | .pending .. => none
  | .done root original => match root with
    | .node _ [filterRow] _ _ =>
      match SourceEqualityPhysicalPayload.own filterRow.entry.key.constraint with
      | .error _ => none
      | .ok filterOwn =>
        match SourceEqualityOnePassWorker.run unconstrained top SourceEqualityPCSNativeEdge.conjoin
            SourceMemoGate.plain top 8 8 8 8 8 128 filterOwn (some []) filterRow.children
            (SourceEqualityNativeInitial.cold 8 original) with
        | .done (.ok filtered) native => match filtered[1]? with
          | none => none
          | some application => match application with
            | .node _ [applicationRow] _ _ =>
              match SourceEqualityPhysicalPayload.own applicationRow.entry.key.constraint with
              | .ok (some records) =>
                match SourceEqualityRecordSelectionWorker.queries unconstrained 8
                    applicationRow.children records native.machine.heap with
                | .done (some queries) selected =>
                  match SourceEqualityRequiredExecution.requireAll 8 8
                      (SourceEqualitySelectedRequired.paths (InternedSourceClassSelection.selected queries))
                      applicationRow.children selected with
                  | .done required final =>
                    some ⟨root, original, filterRow, filterOwn, filtered, native,
                      application, applicationRow, records, queries, selected, required, final⟩
                  | _ => none
                | _ => none
              | _ => none
            | _ => none
        | _ => none
    | _ => none

/-- These equations state the actual original construction and every completed stage. -/
def Receipts (observed : Receipt) : Prop :=
  InternedFreshOrdinaryConstruction.build expression [] empty =
    .done observed.root observed.original ∧
  (∃ entry depth free, observed.root = .node entry [observed.filterRow] depth free) ∧
  SourceEqualityPhysicalPayload.own observed.filterRow.entry.key.constraint = .ok observed.filterOwn ∧
  SourceEqualityOnePassWorker.run unconstrained top SourceEqualityPCSNativeEdge.conjoin
    SourceMemoGate.plain top 8 8 8 8 8 128 observed.filterOwn (some []) observed.filterRow.children
    (SourceEqualityNativeInitial.cold 8 observed.original) = .done (.ok observed.filtered) observed.native ∧
  observed.filtered[1]? = some observed.application ∧
  (∃ entry depth free, observed.application = .node entry [observed.applicationRow] depth free) ∧
  SourceEqualityPhysicalPayload.own observed.applicationRow.entry.key.constraint = .ok (some observed.records) ∧
  SourceEqualityRecordSelectionWorker.queries unconstrained 8 observed.applicationRow.children
    observed.records observed.native.machine.heap = .done (some observed.queries) observed.selected ∧
  SourceEqualityRequiredExecution.requireAll 8 8
    (SourceEqualitySelectedRequired.paths (InternedSourceClassSelection.selected observed.queries))
    observed.applicationRow.children observed.selected = .done observed.required observed.final

/-- A returned observation retains all source-stage equations without another worker premise. -/
theorem observation_receipts (observed : Receipt) (found : observation = some observed) : Receipts observed := by
  unfold observation at found
  split at found <;> try contradiction
  split at found <;> try contradiction
  split at found <;> try contradiction
  split at found <;> try contradiction
  split at found <;> try contradiction
  split at found <;> try contradiction
  split at found <;> try contradiction
  split at found <;> try contradiction
  split at found <;> try contradiction
  cases found
  refine ⟨by assumption, ?_, by assumption, by assumption, by assumption, ?_,
    by assumption, by assumption, by assumption⟩ <;> exact ⟨_, _, _, rfl⟩

/-- Actual original construction derives record facts and root availability. -/
theorem construction_facts (observed : Receipt) (found : observation = some observed) :
    Facts observed.original ∧ Available observed.original observed.root := by
  have built := (observation_receipts observed found).1
  have checked := InternedFreshOrdinaryFacts.build_verified expression [] empty empty_facts
    (by intro value member; cases member)
  exact ⟨by simpa only [built, Outcome.state] using checked.facts,
    checked.result observed.root observed.original built⟩

/-- Read the function slot that is an actual child of the application row. -/
def functionValue (values : List (Value String Guard)) : Value String Guard :=
  values[2]?.getD .empty

/-- Check the exposed arrow at each retained function component annotation. -/
def arrowAnnotations (value : Value String Guard) : Bool :=
  match value with
  | .node _ (first :: rest) _ _ =>
      (first :: rest).all fun row => match row.children with
        | [.node _ [arrow] _ _] => arrow.entry.key.symbol == "->" && arrow.children.length == 3
        | _ => false
  | _ => false

/-- Read the measured heights and the exposed source arrow from one actual receipt. -/
def summary (observed : Receipt) : Nat × Nat × Nat × Bool :=
  (transparentHeight observed.application,
    transparentHeight (functionValue observed.applicationRow.children),
    transparentHeight (functionValue observed.required),
    arrowAnnotations (functionValue observed.required))

/-- Kernel evaluation starts at the original request and follows both completed source prefixes. -/
theorem actual_summary : observation.map summary = some (2, 1, 3, true) := by
  cbv

/-- A selected required-path result can contain a function taller than its original application. -/
theorem required_child_exceeds_application : ∃ observed,
    observation = some observed ∧ Receipts observed ∧
    transparentHeight (functionValue observed.applicationRow.children) < transparentHeight observed.application ∧
    transparentHeight observed.application < transparentHeight (functionValue observed.required) ∧
    arrowAnnotations (functionValue observed.required) = true := by
  cases found : observation with
  | none => have impossible := actual_summary; simp only [found, Option.map_none, reduceCtorEq] at impossible
  | some observed =>
      have checked : summary observed = (2, 1, 3, true) := by
        simpa only [found, Option.map_some, Option.some.injEq] using actual_summary
      have parent := congrArg (fun result => result.1) checked
      have original := congrArg (fun result => result.2.1) checked
      have required := congrArg (fun result => result.2.2.1) checked
      have exposed := congrArg (fun result => result.2.2.2) checked
      exact ⟨observed, rfl, observation_receipts observed found, by
        change transparentHeight (functionValue observed.applicationRow.children) = 1 at original
        change transparentHeight observed.application = 2 at parent
        omega, by
        change transparentHeight (functionValue observed.required) = 3 at required
        change transparentHeight observed.application = 2 at parent
        omega, exposed⟩

/-- Original application height cannot justify every selected required-path child request. -/
theorem not_required_child_descent : ¬ (∀ observed, observation = some observed →
    transparentHeight (functionValue observed.required) < transparentHeight observed.application) := by
  intro decrease
  obtain ⟨observed, found, _receipts, _old, increased, _exposed⟩ := required_child_exceeds_application
  have smaller := decrease observed found
  omega

end MicroCFTA.SourceSynthesisUniverseRequiredBoundary
