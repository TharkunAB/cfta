import MicroCFTA.EqualityReduction
import MicroCFTA.EqualityTermination

/-!
# The inherited-constraint reduction caller

The worker follows reducePartially: rebuild binders, keep unions, reduce
each ordinary edge, combine local and inherited equalities, descend those
equalities by child position, and rebuild the original guarded edge.
Execution bounds instrument the two recursive loops. They are not source
iteration limits. The theorem covers every completed execution.
-/
namespace MicroCFTA.PartialReductionCaller
open Language EqualityNormalize EqualityReduction

/-- An ordinary stored row retains its full guard and normalized equalities. -/
structure Row (Node Symbol : Type) where
  label : Symbol
  children : List Node
  classes : Constraints
  guard : Term Symbol → Prop
  active : Active classes
  guarded : ∀ term, guard term → Satisfies term classes

/-- The source does not descend into binders or unions and rejects a free reference. -/
inductive View (Node Symbol : Type) where
  | empty
  | binder
  | union
  | reference
  | ordinary (rows : List (Row Node Symbol))

/-- Interpret each retained row with the local child language. -/
def RowAccepts (meaning : Node → Term Symbol → Prop) (row : Row Node Symbol) : Term Symbol → Prop
  | .node label children => row.label = label ∧ All₂ meaning row.children children ∧ row.guard (.node label children)

/-- Node rebuilding is the disjunction of its complete guarded rows. -/
def RowsAccept (meaning : Node → Term Symbol → Prop) (rows : List (Row Node Symbol)) (term : Term Symbol) : Prop :=
  ∃ row ∈ rows, RowAccepts meaning row term

/-- The caller uses the previously modeled local reduction primitives. -/
structure Operations (Node Symbol : Type) where
  narrow : EqualityReduction.Operations Node Symbol
  view : Node → View Node Symbol
  modify : Node → List (Row Node Symbol) → Node
  rebuildBinder : Node → Node

/-- These contracts concern local row readback and constructor interpretation. -/
structure Laws (ops : Operations Node Symbol) : Prop where
  narrow : EqualityReduction.Laws ops.narrow
  ordinary : ∀ node rows, ops.view node = .ordinary rows → ∀ term,
    ops.narrow.meaning node term ↔ RowsAccept ops.narrow.meaning rows term
  modify : ∀ node original, ops.view node = .ordinary original → ∀ rows term,
    ops.narrow.meaning (ops.modify node rows) term ↔ RowsAccept ops.narrow.meaning rows term
  binder : ∀ node, ops.view node = .binder → ∀ term,
    ops.narrow.meaning (ops.rebuildBinder node) term ↔ ops.narrow.meaning node term

/-- Traverse children in order with their zero-based positions. -/
def walk (action : Nat → α → Option β) : Nat → List α → Option (List β)
  | _, [] => some []
  | index, first :: rest => do
      let value ← action index first
      let values ← walk action (index + 1) rest
      pure (value :: values)

/-- Completed traversal preserves its relation to each input element. -/
theorem walk_relation (action : Nat → α → Option β) (relation : α → β → Prop)
    (step : ∀ index before after, action index before = some after → relation before after)
    (index : Nat) (before : List α) (after : List β) (done : walk action index before = some after) :
    All₂ relation before after := by
  induction before generalizing index after with
  | nil => have same : after = [] := Option.some.inj done.symm; subst after; exact .nil
  | cons first rest ih =>
      cases head : action index first with
      | none => simp [walk, head] at done
      | some value =>
          cases tail : walk action (index + 1) rest with
          | none => simp [walk, head, tail] at done
          | some values =>
              have same : after = value :: values := by simpa [walk, head, tail] using done.symm
              subst after
              exact .cons (step index first value head) (ih (index + 1) values tail)

/-- Pointwise constructor semantics transport through an ordered row traversal. -/
theorem rows_transport (meaning : Node → Term Symbol → Prop) (before after : List (Row Node Symbol))
    (term : Term Symbol)
    (related : All₂ (fun left right => RowAccepts meaning right term ↔ RowAccepts meaning left term) before after) :
    RowsAccept meaning after term ↔ RowsAccept meaning before term := by
  induction related with
  | nil => simp [RowsAccept]
  | @cons first final rest finals head tail ih =>
      simp only [RowsAccept, List.mem_cons, exists_eq_or_imp]
      exact or_congr head ih

/-- Child traversal preserves the forest when each actual child position has its local law. -/
theorem walk_forest (meaning : Node → Term Symbol → Prop) (action : Nat → Node → Option Node)
    (index : Nat) (before after : List Node) (children : List (Term Symbol))
    (done : walk action index before = some after)
    (step : ∀ offset child, children[offset]? = some child → ∀ old fresh,
      action (index + offset) old = some fresh → (meaning fresh child ↔ meaning old child)) :
    All₂ meaning after children ↔ All₂ meaning before children := by
  induction before generalizing index after children with
  | nil =>
      have same : after = [] := Option.some.inj done.symm
      subst after
      rfl
  | cons old rest ih =>
      cases head : action index old with
      | none => simp [walk, head] at done
      | some fresh =>
          cases tail : walk action (index + 1) rest with
          | none => simp [walk, head, tail] at done
          | some next =>
              have same : after = fresh :: next := by simpa [walk, head, tail] using done.symm
              subst after
              cases children with
              | nil => constructor <;> intro impossible <;> cases impossible
              | cons child children =>
                  have headExact := step 0 child (by simp) old fresh (by simpa using head)
                  have tailExact := ih (index + 1) next children tail (by
                    intro offset value found old fresh called
                    exact step (offset + 1) value (by simpa using found) old fresh
                      (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using called))
                  constructor
                  · intro accepted
                    cases accepted with
                    | cons first rest => exact .cons (headExact.mp first) (tailExact.mp rest)
                  · intro accepted
                    cases accepted with
                    | cons first rest => exact .cons (headExact.mpr first) (tailExact.mpr rest)

/-- Execute the proved total equality normalizer on inherited and local classes. -/
def combine (inherited classes : Constraints) : RunResult :=
  mkEqConstraints (EqualityTermination.normalizationBound (inherited ++ classes)) (inherited ++ classes)

/-- The inherited combination has exactly the conjunction of both input meanings. -/
theorem combine_exact (inherited classes : Constraints) (term : Term Symbol) :
    RunSat term (combine inherited classes) ↔ Satisfies term inherited ∧ Satisfies term classes := by
  simpa [combine, Satisfies, or_imp, forall_and] using
    EqualityTermination.mkEqConstraints_total_correct term (inherited ++ classes)

/-- Normalization cannot exhaust the derived bound used by the caller model. -/
theorem combine_finishes (inherited classes : Constraints) : combine inherited classes ≠ .timeout :=
  EqualityTermination.mkEqConstraints_terminates (inherited ++ classes)

/-- Process one source edge after one local equality pass. -/
def process [DecidableEq Node] (ops : Operations Node Symbol)
    (recurse : Constraints → Node → Option Node) (inherited : Constraints)
    (row : Row Node Symbol) : Option (Row Node Symbol) := do
  let narrowed := EqualityReduction.pass ops.narrow row.classes inherited row.children
  let children ← match combine inherited row.classes with
    | .timeout => none
    | .contradiction => some (narrowed.map (fun _ => ops.narrow.empty))
    | .normalized classes => walk (fun index => recurse (eqConstraintsDescend index classes)) 0 narrowed
  pure { row with children }

/-- Execute the actual opaque cases and the ordinary-row recursive schedule. -/
def run [DecidableEq Node] (ops : Operations Node Symbol) : Nat → Constraints → Node → Option Node
  | 0, _, _ => none
  | fuel + 1, inherited, node =>
      match ops.view node with
      | .empty | .union => some node
      | .binder => some (ops.rebuildBinder node)
      | .reference => none
      | .ordinary rows =>
          (walk (fun _ => process ops (run ops fuel) inherited) 0 rows).map (ops.modify node)

/-- Each processed edge retains its exact guarded meaning under inherited equalities. -/
theorem process_exact [DecidableEq Node] (ops : Operations Node Symbol) (laws : Laws ops)
    (recurse : Constraints → Node → Option Node)
    (recursive : ∀ inherited before after, recurse inherited before = some after → ∀ term,
      Satisfies term inherited → (ops.narrow.meaning after term ↔ ops.narrow.meaning before term))
    (inherited : Constraints) (before after : Row Node Symbol)
    (done : process ops recurse inherited before = some after) (term : Term Symbol)
    (inheritedSat : Satisfies term inherited) :
    RowAccepts ops.narrow.meaning after term ↔ RowAccepts ops.narrow.meaning before term := by
  let nodes := EqualityReduction.pass ops.narrow before.classes inherited before.children
  cases combined : combine inherited before.classes with
  | timeout => exact False.elim (combine_finishes inherited before.classes combined)
  | contradiction =>
      have same : after = { before with children := nodes.map (fun _ => ops.narrow.empty) } := by
        simpa [process, combined] using done.symm
      subst after
      have noGuard : ¬before.guard term := by
        intro guard
        have impossible := (combine_exact inherited before.classes term).mpr ⟨inheritedSat, before.guarded term guard⟩
        simp [combined, RunSat] at impossible
      cases term
      simp [RowAccepts, noGuard]
  | normalized classes =>
      cases walked : walk (fun index => recurse (eqConstraintsDescend index classes)) 0
          (EqualityReduction.pass ops.narrow before.classes inherited before.children) with
      | none => simp [process, combined, walked] at done
      | some children =>
          have same : after = { before with children } := by
            simpa [process, combined, walked] using done.symm
          subst after
          cases term with
          | node label terms =>
              by_cases guard : before.guard (.node label terms)
              · have localSat := before.guarded _ guard
                have combinedSat : Satisfies (.node label terms) classes := by
                  have result := (combine_exact inherited before.classes (.node label terms)).mpr ⟨inheritedSat, localSat⟩
                  simpa [combined, RunSat] using result
                have walkedExact := walk_forest ops.narrow.meaning _ 0 nodes children terms walked (by
                  intro index child found old fresh called
                  exact recursive (eqConstraintsDescend index classes) old fresh (by simpa using called) child
                    (eqConstraintsDescend_sound label terms index child found classes combinedSat))
                have narrowedExact := constrained_pass_exact ops.narrow laws.narrow before.classes inherited
                  before.active before.children (.node label terms)
                have forestExact : All₂ ops.narrow.meaning nodes terms ↔ All₂ ops.narrow.meaning before.children terms := by
                  simpa only [Forest, localSat, inheritedSat, and_true] using narrowedExact
                simp only [RowAccepts, guard, and_true]
                exact and_congr_right (fun _ => walkedExact.trans forestExact)
              · simp [RowAccepts, guard]

/-- Every completed caller execution preserves the complete inherited language. -/
theorem run_exact [DecidableEq Node] (ops : Operations Node Symbol) (laws : Laws ops)
    (fuel : Nat) (inherited : Constraints) (before after : Node)
    (done : run ops fuel inherited before = some after) (term : Term Symbol)
    (satisfied : Satisfies term inherited) :
    ops.narrow.meaning after term ↔ ops.narrow.meaning before term := by
  induction fuel generalizing inherited before after term with
  | zero => simp [run] at done
  | succ fuel ih =>
      cases viewed : ops.view before with
      | empty | union =>
          have same : before = after := by simpa [run, viewed] using done
          subst after
          rfl
      | binder =>
          have same : ops.rebuildBinder before = after := by simpa [run, viewed] using done
          rw [← same]
          exact laws.binder before viewed term
      | reference => simp [run, viewed] at done
      | ordinary rows =>
          cases walked : walk (fun _ => process ops (run ops fuel) inherited) 0 rows with
          | none => simp [run, viewed, walked] at done
          | some changed =>
              have same : ops.modify before changed = after := by simpa [run, viewed, walked] using done
              rw [← same, laws.modify before rows viewed, laws.ordinary before rows viewed]
              have related := walk_relation _
                (fun original final => RowAccepts ops.narrow.meaning final term ↔ RowAccepts ops.narrow.meaning original term)
                (fun _ original final completed => process_exact ops laws (run ops fuel) ih inherited
                  original final completed term satisfied) 0 rows changed walked
              exact rows_transport ops.narrow.meaning rows changed term related

/-- The public empty-inherited entry preserves every complete accepted term. -/
theorem public_exact [DecidableEq Node] (ops : Operations Node Symbol) (laws : Laws ops)
    (fuel : Nat) (before after : Node) (done : run ops fuel [] before = some after) (term : Term Symbol) :
    ops.narrow.meaning after term ↔ ops.narrow.meaning before term :=
  run_exact ops laws fuel [] before after done term (by simp [Satisfies])

/-- A completed local identity loop is unchanged by a larger execution bound. -/
theorem loop_replay [DecidableEq Node] (ops : EqualityReduction.Operations Node Symbol)
    (classes inherited : Constraints) (fuel : Nat) (before after : List Node)
    (done : EqualityReduction.reduce ops classes inherited fuel before = some after) (extra : Nat) :
    EqualityReduction.reduce ops classes inherited (fuel + extra) before = some after := by
  induction fuel generalizing before with
  | zero => simp [EqualityReduction.reduce] at done
  | succ fuel ih =>
      simp only [EqualityReduction.reduce] at done
      simp only [Nat.succ_add, EqualityReduction.reduce]
      split at done
      next fixed => simpa [fixed] using done
      next changed => simpa [changed] using ih _ done

/-- Replaying every successful local call replays the complete ordered traversal. -/
theorem walk_replay (first second : Nat → α → Option β)
    (stable : ∀ index input output, first index input = some output → second index input = some output)
    (index : Nat) (before : List α) (after : List β) (done : walk first index before = some after) :
    walk second index before = some after := by
  induction before generalizing index after with
  | nil => exact done
  | cons head tail ih =>
      cases called : first index head with
      | none => simp [walk, called] at done
      | some value =>
          cases rest : walk first (index + 1) tail with
          | none => simp [walk, called, rest] at done
          | some values =>
              have same : after = value :: values := by simpa [walk, called, rest] using done.symm
              subst after
              simp [walk, stable index head value called, ih (index + 1) values rest]

/-- Replaying completed child calls retains the same processed source row. -/
theorem process_replay [DecidableEq Node] (ops : Operations Node Symbol)
    (first second : Constraints → Node → Option Node)
    (stable : ∀ classes before after, first classes before = some after → second classes before = some after)
    (inherited : Constraints) (before after : Row Node Symbol)
    (done : process ops first inherited before = some after) :
    process ops second inherited before = some after := by
  let nodes := EqualityReduction.pass ops.narrow before.classes inherited before.children
  cases combined : combine inherited before.classes with
  | timeout => simp [process, combined] at done
  | contradiction => simpa [process, combined] using done
  | normalized classes =>
      cases walked : walk (fun index => first (eqConstraintsDescend index classes)) 0
        (EqualityReduction.pass ops.narrow before.classes inherited before.children) with
      | none => simp [process, combined, walked] at done
      | some children =>
          have walkAgain := walk_replay _ (fun index => second (eqConstraintsDescend index classes))
            (fun index input output => stable (eqConstraintsDescend index classes) input output) 0 nodes children walked
          dsimp only [nodes] at walkAgain
          simpa [process, combined, walked, walkAgain] using done

/-- Every completed caller run has the same result at every larger bound. -/
theorem run_replay [DecidableEq Node] (ops : Operations Node Symbol)
    (fuel extra : Nat) (inherited : Constraints) (before after : Node)
    (done : run ops fuel inherited before = some after) :
    run ops (fuel + extra) inherited before = some after := by
  induction fuel generalizing inherited before after with
  | zero => simp [run] at done
  | succ fuel ih =>
      cases viewed : ops.view before with
      | empty | binder | union => simpa [run, Nat.succ_add, viewed] using done
      | reference => simp [run, viewed] at done
      | ordinary rows =>
          cases walked : walk (fun _ => process ops (run ops fuel) inherited) 0 rows with
          | none => simp [run, viewed, walked] at done
          | some changed =>
              have again := walk_replay _ (fun _ => process ops (run ops (fuel + extra)) inherited)
                (fun _ original final completed => process_replay ops (run ops fuel) (run ops (fuel + extra))
                  ih inherited original final completed) 0 rows changed walked
              simpa [run, Nat.succ_add, viewed, walked, again] using done

/-- Repeat completed public passes until source node identities stop changing. -/
def fixpoint [DecidableEq Node] (ops : Operations Node Symbol) (work : Nat) : Nat → Node → Option Node
  | 0, _ => none
  | rounds + 1, before => do
      let after ← run ops work [] before
      if after = before then some before else fixpoint ops work rounds after

/-- A completed outer identity fixed point preserves the original complete language. -/
theorem fixpoint_exact [DecidableEq Node] (ops : Operations Node Symbol) (laws : Laws ops)
    (work rounds : Nat) (before after : Node) (done : fixpoint ops work rounds before = some after)
    (term : Term Symbol) : ops.narrow.meaning after term ↔ ops.narrow.meaning before term := by
  induction rounds generalizing before with
  | zero => simp [fixpoint] at done
  | succ rounds ih =>
      cases called : run ops work [] before with
      | none => simp [fixpoint, called] at done
      | some next =>
          by_cases fixed : next = before
          · have same : before = after := by simpa [fixpoint, called, fixed] using done
            subst after
            rfl
          · have continued : fixpoint ops work rounds next = some after := by
              simpa [fixpoint, called, fixed] using done
            exact (ih next continued).trans (public_exact ops laws work before next called term)

end MicroCFTA.PartialReductionCaller
