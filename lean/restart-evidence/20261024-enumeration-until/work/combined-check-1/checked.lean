import MicroCFTA.EnumerationDriver
import MicroCFTA.EnumerationCPSChecked


/-!
# Parameterized enumeration with narrowing and partial stopping

The actions use the existing graph, state, and bounded enumeration monad.
The scheduler is the existing modeled slot scan. Cached-source scheduling
requires a separate correspondence argument.
-/

namespace MicroCFTA.EnumerationUntil
open Language Fragments EnumerationState EnumerationDriver

variable {Symbol Guard OracleState : Type}

local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

/-- Expand a node with its actual suspended constraints. -/
abbrev NodeExpansion (Symbol Guard : Type) :=
  List Suspended → Nat → EnumerateM Symbol Guard (Fragment Symbol)

/-- Prepare every child in order and retain the selected edge's residual. -/
def enumerateEdgeWith (prepareAt : Nat → NodeExpansion Symbol Guard) :
    Nat → List Suspended → EnumerationState.Edge Symbol Guard →
      EnumerateM Symbol Guard (Fragment Symbol)
  | 0, _, _ => failure .fuelExhausted
  | fuel + 1, scs, edge => do
      require (arityAllows edge.children.length scs)
      let added ← edge.equalities.mapM suspend
      let children ← edge.children.zipIdx |>.mapM fun (node, index) =>
        prepareAt fuel (descendScs index (scs ++ added)) node
      let fragment := Fragment.node edge.symbol children
      match edge.residual with
      | none => pure ()
      | some guard => modify fun state =>
          {state with obligations := (guard, fragment) :: state.obligations}
      pure fragment

/-- Defer an ordinary child and install its complete suspended list. -/
def prepareShallowChild (graph : Graph Symbol Guard) : Nat → NodeExpansion Symbol Guard
  | 0, _, _ => failure .fuelExhausted
  | fuel + 1, scs, node => do
      match graph.node node with
      | .alternatives _ =>
          if scs.any (fun sc => EqualityTrie.isTerminal sc.trie) then
            enumerateNode graph (fuel + 1) scs node
          else
            let uv ← allocate (some node)
            setValue uv (.unenumerated (some node) scs)
            pure (.hole uv)
      | _ => enumerateNode graph (fuel + 1) scs node

/-- Expand the selected ordinary root once instead of deferring that root. -/
def enumerateShallowHere (graph : Graph Symbol Guard) : Nat → NodeExpansion Symbol Guard
  | 0, _, _ => failure .fuelExhausted
  | fuel + 1, scs, node => do
      match graph.node node with
      | .alternatives edges =>
          if scs.any (fun sc => EqualityTrie.isTerminal sc.trie) then
            enumerateNode graph (fuel + 1) scs node
          else
            enumerateEdgeWith (prepareShallowChild graph) fuel scs (← choose edges)
      | _ => enumerateNode graph (fuel + 1) scs node

/-- Retain ancestry and write the fragment to the captured representative. -/
def enumerateOutWith (graph : Graph Symbol Guard) (expand : NodeExpansion Symbol Guard)
    (fuel uv : Nat) : EnumerateM Symbol Guard (Fragment Symbol) := do
  match ← getValue (fuel + 1) uv with
  | .unenumerated (some node) scs =>
      let root ← representative (fuel + 1) uv
      let ancestry := (← get).recursionAncestry root
      modify fun state => {state with expansionAncestry := (
        match graph.node node with
        | .recursive _ => (recursionKey node scs :: ancestry).eraseDups
        | _ => ancestry)}
      let fragment ← expand scs
        (match graph.node node with | .recursive body => body | _ => node)
      modify fun state => {state with expansionAncestry := []}
      setValue root (.enumerated fragment)
      pure fragment
  | _ => reject

/-- List every candidate before blocked representatives are removed. -/
def remaining (graph : Graph Symbol Guard) (state : State Symbol Guard) : List Nat :=
  (state.values.zipIdx.filter fun entry => candidate graph entry.1).map Prod.snd

/-- Retain the full stop, narrowing, ancestry, and two-oracle control flow. -/
def enumerateUntil (graph : Graph Symbol Guard)
    (stop : Option (OracleState → Nat → Bool))
    (narrow : OracleState → Nat → Nat → Nat)
    (expandAt : Nat → NodeExpansion Symbol Guard)
    (order : OracleState → List Nat → Option Nat)
    (oracle : Oracle Symbol Guard OracleState) :
    Nat → OracleState → EnumerateM Symbol Guard (Option OracleState)
  | 0, _ => failure .fuelExhausted
  | fuel + 1, oracleState => do
      let step : EnumerateM Symbol Guard (Option OracleState) := do
        let next := pickNext (order oracleState) (← findExpandable graph (fuel + 1))
        match next with
        | .done => pure none
        | .stuck => reject
        | .expand uv =>
            match ← getValue (fuel + 1) uv with
            | .unenumerated (some node) scs =>
                let repeated ← checkRepeated graph (fuel + 1) uv node scs
                if repeated then
                  enumerateUntil graph stop narrow expandAt order oracle fuel oracleState
                else
                  let narrowed := narrow oracleState uv node
                  match graph.node narrowed with
                  | .empty => reject
                  | _ =>
                      if narrowed = node then pure ()
                      else
                        let root ← representative (fuel + 1) uv
                        setValue root (.unenumerated (some narrowed) scs)
                      let (beforeReject, beforeState) ← oracle oracleState uv (.inr narrowed)
                      require (!beforeReject)
                      let fragment ← enumerateOutWith graph (expandAt (fuel + 1)) (fuel + 1) uv
                      let (afterReject, afterState) ← oracle beforeState uv (.inl fragment)
                      require (!afterReject)
                      enumerateUntil graph stop narrow expandAt order oracle fuel afterState
            | _ => reject
      match stop with
      | none => step
      | some rule =>
          let pending := remaining graph (← get)
          if !pending.isEmpty && pending.all (rule oracleState) then
            pure (some oracleState)
          else step

/-- Read the root fragment and retain the original root hole on pending work. -/
def rootFragment (fuel : Nat) : EnumerateM Symbol Guard (Fragment Symbol) := do
  match ← getValue (fuel + 1) 0 with
  | .enumerated fragment => pure fragment
  | _ => pure (.hole 0)

/-! The same bound supplies the driver and partial renderer. The root lookup
uses that bound plus one, as the existing slot-expansion actions do. -/
/-- Execute the public shallow path and retain partial terms, errors, and states. -/
def partialRunsUntil (graph : Graph Symbol Guard)
    (stop : OracleState → Nat → Bool) (narrow : OracleState → Nat → Nat → Nat)
    (order : OracleState → List Nat → Option Nat) (oracle : Oracle Symbol Guard OracleState)
    (fuel root : Nat) (oracleState : OracleState) :
    List (Except Error (Term (PartialSymbol Symbol) × State Symbol Guard)) :=
  let action : EnumerateM Symbol Guard (Term (PartialSymbol Symbol)) := do
    let _ ← enumerateUntil graph (some stop) narrow (enumerateShallowHere graph) order oracle fuel oracleState
    let fragment ← rootFragment fuel
    expandPartial graph fuel fragment
  action (initial root)

end MicroCFTA.EnumerationUntil

namespace MicroCFTA.EnumerationUntil

open Fragments EnumerationState

local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

/-- The parameterized worker retains the complete eager worker action. -/
theorem enumerateOutWith_eager (graph : Graph Symbol Guard) (fuel uv : Nat) :
    enumerateOutWith graph (enumerateNode graph fuel) fuel uv = enumerateOut graph fuel uv := rfl

/-- Eager child preparation retains the old edge action at the same bound. -/
theorem enumerateEdgeWith_eager (graph : Graph Symbol Guard) (fuel : Nat)
    (scs : List Suspended) (edge : EnumerationState.Edge Symbol Guard) :
    enumerateEdgeWith (fun remaining => enumerateNode graph remaining) fuel scs edge =
      enumerateEdge graph fuel scs edge := by
  cases fuel <;> rfl

/-- A positive bounded call stops before scheduling when all candidates pass the rule. -/
theorem stop_all (graph : Graph Symbol Guard) (rule : OracleState → Nat → Bool)
    (narrow : OracleState → Nat → Nat → Nat) (expandAt : Nat → NodeExpansion Symbol Guard)
    (order : OracleState → List Nat → Option Nat) (oracle : Oracle Symbol Guard OracleState)
    (fuel : Nat) (oracleState : OracleState) (before : State Symbol Guard)
    (nonempty : (remaining graph before).isEmpty = false)
    (accepted : (remaining graph before).all (rule oracleState) = true) :
    enumerateUntil graph (some rule) narrow expandAt order oracle (fuel + 1) oracleState before =
      [.ok (some oracleState, before)] := by
  have nonempty' : remaining graph before ≠ [] := by simpa using nonempty
  have accepted' : ∀ uv ∈ remaining graph before, rule oracleState uv = true := by simpa using accepted
  simp [enumerateUntil, nonempty', accepted', bind, get, getThe, MonadStateOf.get,
    pure, StateT.bind, StateT.get, StateT.pure, ExceptT.bind, ExceptT.bindCont,
    ExceptT.pure, ExceptT.mk]

end MicroCFTA.EnumerationUntil


namespace MicroCFTA.EnumerationUntilBridge

open Fragments EnumerationState EnumerationCorrectness EnumerationDriver
open EnumerationCPSChecked (successes mem_successes)

local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

local instance : LawfulMonad List where
  map_const := rfl
  id_map := by intro α xs; simp [Functor.map]
  seqLeft_eq := by
    intros
    simp [SeqLeft.seqLeft, Seq.seq, Functor.map, List.flatMap_map, ← List.map_eq_flatMap]
    simp only [List.map_const']
  seqRight_eq := by
    intros
    simp only [SeqRight.seqRight, Seq.seq, Functor.map, List.flatMap_map]
    simp
  pure_seq := by intros; simp [Seq.seq, Functor.map, pure]
  bind_pure_comp := by intros; simp [bind, pure, Functor.map, ← List.map_eq_flatMap]
  bind_map := by intros; rfl
  pure_bind := by intros; simp [pure, bind]
  bind_assoc := by intros; exact List.flatMap_assoc

/-- Binding preserves the order and multiplicity of successful rows. -/
theorem successes_bind (action : EnumerateM Symbol Guard α)
    (next : α → EnumerateM Symbol Guard β) (before : State Symbol Guard) :
    successes (ExceptT.run ((action >>= next) before)) =
      (successes (ExceptT.run (action before))).flatMap
        (fun pair => successes (ExceptT.run (next pair.1 pair.2))) := by
  rw [run_bind]
  generalize ExceptT.run (action before) = rows
  induction rows with
  | nil => rfl
  | cons row rows ih => cases row <;> simp [successes, ih, List.filterMap_append]

/-- Equal continuations on each actual successful branch give equal successful rows. -/
theorem successes_bind_congr (action : EnumerateM Symbol Guard α)
    (left right : α → EnumerateM Symbol Guard β) (before : State Symbol Guard)
    (same : ∀ value after, Success action before value after →
      successes (ExceptT.run (left value after)) = successes (ExceptT.run (right value after))) :
    successes (ExceptT.run ((action >>= left) before)) =
      successes (ExceptT.run ((action >>= right) before)) := by
  rw [successes_bind, successes_bind]
  generalize rowsEq : successes (ExceptT.run (action before)) = rows
  have memberSame : ∀ pair ∈ rows,
      successes (ExceptT.run (left pair.1 pair.2)) = successes (ExceptT.run (right pair.1 pair.2)) := by
    intro pair member
    apply same pair.1 pair.2
    exact (mem_successes _ _ _).mp (rowsEq.symm ▸ member)
  clear rowsEq
  induction rows with
  | nil => rfl
  | cons first rest ih =>
      simp only [List.flatMap_cons]
      rw [memberSame first (by simp), ih (fun pair member => memberSame pair (by simp [member]))]

/-- An action with no successful branch has an empty successful projection. -/
theorem successes_empty (action : EnumerateM Symbol Guard α) (before : State Symbol Guard)
    (absent : ∀ value after, ¬Success action before value after) :
    successes (ExceptT.run (action before)) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro pair member
  exact absent pair.1 pair.2 ((mem_successes _ _ _).mp member)

end MicroCFTA.EnumerationUntilBridge


namespace MicroCFTA.EnumerationUntilBridge

open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule

variable {Symbol Guard : Type}

local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

theorem getValue_repeat_value
    (firstFuel secondFuel uv : Nat)
    (before middle after : State Symbol Guard)
    (first second : UVarValue Symbol)
    (firstRead : Success (getValue firstFuel uv) before first middle)
    (secondRead : Success (getValue secondFuel uv) middle second after) :
    second = first := by
  obtain ⟨firstFound, firstLookup, firstStored, rfl⟩ :=
    (getValue_success firstFuel uv before middle first).mp firstRead
  obtain ⟨secondFound, secondLookup, secondStored, rfl⟩ :=
    (getValue_success secondFuel uv _ after second).mp secondRead
  change UnionFind.findRoot secondFuel firstFound.forest uv = some secondFound at secondLookup
  change before.values[secondFound.representative]? = some second at secondStored
  obtain ⟨path, preserved⟩ :=
    UnionFind.findRoot_correct firstFuel before.representatives uv firstFound firstLookup
  have same := (UnionFind.reaches_unique (preserved path)
    (UnionFind.findRoot_correct secondFuel firstFound.forest uv secondFound secondLookup).1).1
  rw [← same] at secondStored
  exact (Option.some.inj (firstStored.symm.trans secondStored)).symm

theorem empty_out_after_read
    (graph : Graph Symbol Guard) (firstFuel fuel uv node : Nat)
    (scs : List Suspended) (before readState after : State Symbol Guard)
    (fragment : Fragment Symbol) (empty : graph.node node = .empty)
    (reading : Success (getValue firstFuel uv) before
      (.unenumerated (some node) scs) readState) :
    ¬Success (enumerateOut graph fuel uv) readState fragment after := by
  intro success
  unfold enumerateOut at success
  obtain ⟨value, readAgain, rereading, continued⟩ :=
    (success_bind _ _ _ _ _).mp success
  have same := getValue_repeat_value firstFuel (fuel + 1) uv before readState readAgain
    (.unenumerated (some node) scs) value reading rereading
  subst value
  obtain ⟨root, resolved, _, continued⟩ := (success_bind _ _ _ _ _).mp continued
  obtain ⟨current, currentState, _, continued⟩ := (success_bind _ _ _ _ _).mp continued
  obtain ⟨ignored, started, _, continued⟩ := (success_bind _ _ _ _ _).mp continued
  obtain ⟨produced, expanded, expansion, _⟩ := (success_bind _ _ _ _ _).mp continued
  cases fuel with
  | zero =>
      exact (success_failure .fuelExhausted started expanded produced expansion).elim
  | succ fuel =>
      exact (reject_unsuccessful started expanded produced
        (by simpa only [empty, enumerateNode] using expansion)).elim

end MicroCFTA.EnumerationUntilBridge

namespace MicroCFTA.EnumerationUntilBridge

open Fragments EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDriver EnumerationUntil
open EnumerationCPSChecked (successes mem_successes)

local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

local instance : LawfulMonad List where
  map_const := rfl
  id_map := by intro α xs; simp [Functor.map]
  seqLeft_eq := by
    intros
    simp [SeqLeft.seqLeft, Seq.seq, Functor.map, List.flatMap_map, ← List.map_eq_flatMap]
    simp only [List.map_const']
  seqRight_eq := by
    intros
    simp only [SeqRight.seqRight, Seq.seq, Functor.map, List.flatMap_map]
    simp
  pure_seq := by intros; simp [Seq.seq, Functor.map, pure]
  bind_pure_comp := by intros; simp [bind, pure, Functor.map, ← List.map_eq_flatMap]
  bind_map := by intros; rfl
  pure_bind := by intros; simp [pure, bind]
  bind_assoc := by intros; exact List.flatMap_assoc

/-- A read-only observation cannot make a just-read empty slot expand successfully. -/
private theorem empty_observation (graph : Graph Symbol Guard)
    (oracle : Oracle Symbol Guard OracleState) (observer : ReadOnlyOracle oracle)
    (oracleState : OracleState) (firstFuel fuel uv node : Nat) (scs : List Suspended)
    (before readState : State Symbol Guard) (empty : graph.node node = .empty)
    (reading : Success (getValue firstFuel uv) before (.unenumerated (some node) scs) readState)
    (tail : Fragment Symbol → OracleState → EnumerateM Symbol Guard α) :
    successes (ExceptT.run ((do
      let decision ← oracle oracleState uv (.inr node)
      require (!decision.1)
      let fragment ← enumerateOut graph fuel uv
      tail fragment decision.2) readState)) = [] := by
  apply successes_empty
  intro value after success
  obtain ⟨decision, observed, observing, continued⟩ := (success_bind _ _ _ _ _).mp success
  have unchanged := observer oracleState uv (.inr node) readState decision observed observing
  subst observed
  obtain ⟨ignored, accepted, required, continued⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  obtain ⟨_, unchanged⟩ := (require_success _ readState accepted).mp required
  subst accepted
  obtain ⟨fragment, expanded, expansion, _⟩ := (success_bind _ _ _ _ _).mp continued
  exact empty_out_after_read graph firstFuel fuel uv node scs before readState expanded fragment empty reading expansion

/-- The eager specialization preserves every ordered successful continuation. -/
private theorem no_stop_eager_bind_successes (graph : Graph Symbol Guard)
    (order : OracleState → List Nat → Option Nat) (oracle : Oracle Symbol Guard OracleState)
    (observer : ReadOnlyOracle oracle) (next : Option OracleState → EnumerateM Symbol Guard α)
    (fuel : Nat) (oracleState : OracleState) (before : State Symbol Guard) :
    successes (ExceptT.run ((enumerateUntil graph none (fun _ _ node => node)
      (fun remaining => enumerateNode graph remaining) order oracle fuel oracleState >>= next) before)) =
    successes (ExceptT.run ((enumerateFully graph order oracle fuel oracleState >>= fun _ => next none) before)) := by
  induction fuel generalizing oracleState before with
  | zero => simp [enumerateUntil, enumerateFully, successes_bind, successes, failure, ExceptT.run]
  | succ fuel ih =>
      rw [enumerateUntil, fully_action]
      simp only [bind_assoc]
      apply successes_bind_congr
      intro available scanned _
      cases selected : pickNext (order oracleState) available with
      | done => simp only [selected, pure_bind]
      | stuck => simp [selected, successes_bind, successes, reject, ExceptT.run]
      | expand uv =>
          simp only [selected]
          apply successes_bind_congr
          intro value readState reading
          cases value with
          | eliminated | enumerated _ => simp [successes_bind, successes, reject, ExceptT.run]
          | unenumerated node scs =>
              cases node with
              | none => simp [successes_bind, successes, reject, ExceptT.run]
              | some node =>
                  apply successes_bind_congr
                  intro repeated checked checking
                  cases repeated with
                  | true => simp only [Bool.true_eq, ↓reduceIte]; exact ih oracleState checked
                  | false =>
                      simp only [Bool.false_eq_true, ↓reduceIte]
                      cases view : graph.node node with
                      | empty =>
                          have same : checked = readState :=
                            ((success_pure false false readState checked).mp
                              (by simpa only [checkRepeated, view] using checking)).2
                          subst checked
                          simpa only [view] using
                            (empty_observation graph oracle observer oracleState (fuel + 1) (fuel + 1)
                              uv node scs scanned readState view reading
                              (fun fragment beforeState => do
                                let (afterReject, afterState) ← oracle beforeState uv (.inl fragment)
                                require (!afterReject)
                                enumerateFully graph order oracle fuel afterState
                                next none)).symm
                      | alternatives edges | recursive body | unresolved ref =>
                          simp only [view, ↓reduceIte, pure_bind, enumerateOutWith_eager]
                          apply successes_bind_congr
                          intro decision observed _
                          rcases decision with ⟨beforeReject, beforeState⟩
                          apply successes_bind_congr
                          intro ignored accepted _
                          cases ignored
                          apply successes_bind_congr
                          intro fragment expanded _
                          apply successes_bind_congr
                          intro decision observedAfter _
                          rcases decision with ⟨afterReject, afterState⟩
                          apply successes_bind_congr
                          intro ignored acceptedAfter _
                          cases ignored
                          exact ih afterState acceptedAfter

/-- With eager expansion, successful rows retain their order and full final states. -/
theorem no_stop_eager_successes (graph : Graph Symbol Guard)
    (order : OracleState → List Nat → Option Nat) (oracle : Oracle Symbol Guard OracleState)
    (observer : ReadOnlyOracle oracle) (fuel : Nat) (oracleState : OracleState)
    (before : State Symbol Guard) :
    successes (ExceptT.run (enumerateUntil graph none (fun _ _ node => node)
      (fun remaining => enumerateNode graph remaining) order oracle fuel oracleState before)) =
    (successes (ExceptT.run (enumerateFully graph order oracle fuel oracleState before))).map
      (fun pair => ((none : Option OracleState), pair.2)) := by
  have bridge := no_stop_eager_bind_successes graph order oracle observer
    (fun result => pure result) fuel oracleState before
  simpa [successes_bind, successes, pure, StateT.pure, ExceptT.pure, ExceptT.run, ExceptT.mk,
    List.map_eq_flatMap] using bridge

end MicroCFTA.EnumerationUntilBridge

