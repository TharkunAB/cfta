import MicroCFTA.EnumerationPureSelection
import MicroCFTA.EnumerationUnionRoots

/-!
# Canonical caches through the source assimilation transaction

The source first transfers class counts. It then assimilates the old
representatives in their original order. Duplicate representatives remain
in that traversal. A completed assimilation keeps its waiting table.
The invariant concerns completed transactions, not temporary slot writes.
-/

namespace MicroCFTA.EnumerationCanonicalTransaction

open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationPureSelection
open EnumerationExpandableIndex (Cached)
open EnumerationUnionRoots

variable {Symbol Guard : Type}

local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

/-- Execute the source assimilation branches and their two empty-delta writes. -/
def assimilateOne (graph : Graph Symbol Guard) (target source : Nat)
    (state : Cached Symbol Guard) : Option (Cached Symbol Guard) := do
  if target = source then return state
  let sourceValue ← state.core.values[source]?
  match sourceValue with
  | .eliminated => return state
  | _ =>
      let targetValue ← state.core.values[target]?
      let merged ← intersectValues graph sourceValue targetValue
      if hasEmptyContents graph merged then none
      else some (EnumerationPureSelection.assimilate graph target source merged state)

private theorem one_endpoint (graph : Graph Symbol Guard) (roots : Nat → Nat)
    (target source : Nat) (before after : Cached Symbol Guard)
    (correct : Correct graph roots before)
    (done : assimilateOne graph target source before = some after) :
    Correct graph roots after ∧
      EnumerationState.assimilate graph target source before.core = [.ok ((), after.core)] ∧
      after.core.representatives = before.core.representatives ∧ after.waiting = before.waiting := by
  by_cases same : target = source
  · have unchanged : before = after := by simpa [assimilateOne, same] using done
    subst after
    exact ⟨correct, by simp [EnumerationState.assimilate, same]; rfl, rfl, rfl⟩
  · cases sourceRead : before.core.values[source]? with
    | none => simp [assimilateOne, same, sourceRead] at done
    | some sourceValue =>
      cases sourceValue with
      | eliminated =>
        have unchanged : before = after := by simpa [assimilateOne, same, sourceRead] using done
        subst after
        refine ⟨correct, ?_, rfl, rfl⟩
        simp [EnumerationState.assimilate, same, rawValue, sourceRead, bind, get, getThe,
          MonadStateOf.get, pure, StateT.bind, StateT.pure, StateT.get, ExceptT.bind,
          ExceptT.pure, ExceptT.bindCont, ExceptT.mk]
      | enumerated fragment =>
        cases targetRead : before.core.values[target]? <;>
          simp [assimilateOne, same, sourceRead, targetRead, intersectValues] at done
      | unenumerated sourceNode sourceScs =>
        cases targetRead : before.core.values[target]? with
        | none => simp [assimilateOne, same, sourceRead, targetRead] at done
        | some targetValue =>
          cases targetValue with
          | eliminated | enumerated _ =>
            simp [assimilateOne, same, sourceRead, targetRead, intersectValues] at done
          | unenumerated targetNode targetScs =>
            let merged : UVarValue Symbol := .unenumerated
              (match sourceNode, targetNode with
                | none, node => node
                | node, none => node
                | some left, some right => some (graph.intersect left right))
              (sourceScs ++ targetScs)
            have intersection : intersectValues graph (.unenumerated sourceNode sourceScs)
                (.unenumerated targetNode targetScs) = some merged := by
              cases sourceNode <;> cases targetNode <;> rfl
            cases empty : hasEmptyContents graph merged with
            | true =>
              simp [assimilateOne, same, sourceRead, targetRead, intersection, empty] at done
            | false =>
              have endpoint : EnumerationPureSelection.assimilate graph target source merged before = after := by
                simpa [assimilateOne, same, sourceRead, targetRead, intersection, empty] using done
              subst after
              obtain ⟨preserved, execution⟩ := EnumerationPureSelection.assimilate_source graph roots before correct
                target source sourceNode targetNode sourceScs targetScs merged same sourceRead targetRead intersection empty
              exact ⟨preserved, execution, rfl, rfl⟩

/-- Every returned source assimilation preserves both canonical caches. -/
theorem assimilateOne_correct (graph : Graph Symbol Guard) (roots : Nat → Nat)
    (target source : Nat) (before after : Cached Symbol Guard)
    (correct : Correct graph roots before)
    (done : assimilateOne graph target source before = some after) :
    Correct graph roots after :=
  (one_endpoint graph roots target source before after correct done).1

/-- A returned cached step has the exact existing core result, with no model error row. -/
theorem assimilateOne_source (graph : Graph Symbol Guard) (roots : Nat → Nat)
    (target source : Nat) (before after : Cached Symbol Guard)
    (correct : Correct graph roots before)
    (done : assimilateOne graph target source before = some after) :
    EnumerationState.assimilate graph target source before.core = [.ok ((), after.core)] :=
  (one_endpoint graph roots target source before after correct done).2.1

/-- Empty-delta assimilation changes neither class representatives nor waiting counts. -/
theorem assimilateOne_frame (graph : Graph Symbol Guard) (roots : Nat → Nat)
    (target source : Nat) (before after : Cached Symbol Guard)
    (correct : Correct graph roots before)
    (done : assimilateOne graph target source before = some after) :
    after.core.representatives = before.core.representatives ∧ after.waiting = before.waiting :=
  (one_endpoint graph roots target source before after correct done).2.2

/-- Every successful core assimilation has the corresponding canonical cached endpoint. -/
theorem assimilateOne_complete (graph : Graph Symbol Guard) (roots : Nat → Nat)
    (target source : Nat) (before : Cached Symbol Guard) (afterCore : State Symbol Guard)
    (correct : Correct graph roots before)
    (success : Success (EnumerationState.assimilate graph target source) before.core () afterCore) :
    ∃ after, assimilateOne graph target source before = some after ∧
      after.core = afterCore ∧ Correct graph roots after := by
  have original := success
  by_cases same : target = source
  · have unchanged : afterCore = before.core := by
      simpa [Success, EnumerationState.assimilate, same, pure, StateT.pure,
        ExceptT.pure, ExceptT.mk, ExceptT.run] using success
    exact ⟨before, by simp [assimilateOne, same], unchanged.symm, correct⟩
  · simp only [EnumerationState.assimilate, same, ↓reduceIte] at success
    obtain ⟨sourceValue, sourceState, sourceLookup, continued⟩ := (success_bind _ _ _ _ _).mp success
    obtain ⟨sourceRead, sourceSame⟩ :=
      (EnumerationSemantics.rawValue_success source before.core sourceState sourceValue).mp sourceLookup
    subst sourceState
    cases sourceValue with
    | eliminated =>
        obtain ⟨_, unchanged⟩ := (success_pure () () before.core afterCore).mp continued
        exact ⟨before, by simp [assimilateOne, same, sourceRead], unchanged.symm, correct⟩
    | enumerated fragment =>
        obtain ⟨targetValue, targetState, _, continued⟩ := (success_bind _ _ _ _ _).mp continued
        exact (success_failure .invalidIntersection targetState afterCore () continued).elim
    | unenumerated sourceNode sourceScs =>
        obtain ⟨targetValue, targetState, targetLookup, continued⟩ := (success_bind _ _ _ _ _).mp continued
        obtain ⟨targetRead, targetSame⟩ :=
          (EnumerationSemantics.rawValue_success target before.core targetState targetValue).mp targetLookup
        subst targetState
        cases targetValue with
        | eliminated | enumerated _ =>
            exact (success_failure .invalidIntersection before.core afterCore () continued).elim
        | unenumerated targetNode targetScs =>
            let merged : UVarValue Symbol := .unenumerated
              (match sourceNode, targetNode with
                | none, node => node
                | node, none => node
                | some left, some right => some (graph.intersect left right))
              (sourceScs ++ targetScs)
            have intersection : intersectValues graph (.unenumerated sourceNode sourceScs)
                (.unenumerated targetNode targetScs) = some merged := by
              cases sourceNode <;> cases targetNode <;> rfl
            simp only [intersection] at continued
            obtain ⟨ignored, checked, required, _⟩ := (success_bind _ _ _ _ _).mp continued
            cases ignored
            have notEmpty : hasEmptyContents graph merged = false := by
              simpa using ((require_success _ before.core checked).mp required).1
            let after := EnumerationPureSelection.assimilate graph target source merged before
            have done : assimilateOne graph target source before = some after := by
              simp [assimilateOne, same, sourceRead, targetRead, intersection, notEmpty, after]
            obtain ⟨preserved, execution, _, _⟩ := one_endpoint graph roots target source before after correct done
            have afterSame : afterCore = after.core := by
              simpa [Success, execution, ExceptT.run] using original
            exact ⟨after, done, afterSame.symm, preserved⟩

/-- Traverse the original representative list, including duplicates. -/
def assimilateMany (graph : Graph Symbol Guard) (target : Nat) :
    List Nat → Cached Symbol Guard → Option (Cached Symbol Guard)
  | [], state => some state
  | source :: rest, state => do
      let middle ← assimilateOne graph target source state
      assimilateMany graph target rest middle

/-- A complete ordered traversal retains both canonical cache equations. -/
theorem assimilateMany_correct (graph : Graph Symbol Guard) (roots : Nat → Nat)
    (target : Nat) (sources : List Nat) (before after : Cached Symbol Guard)
    (correct : Correct graph roots before)
    (done : assimilateMany graph target sources before = some after) :
    Correct graph roots after := by
  induction sources generalizing before with
  | nil =>
      have unchanged : before = after := by simpa [assimilateMany] using done
      simpa [← unchanged] using correct
  | cons source rest ih =>
      cases step : assimilateOne graph target source before with
      | none => simp [assimilateMany, step] at done
      | some middle =>
          apply ih middle (assimilateOne_correct graph roots target source before middle correct step)
          simpa [assimilateMany, step] using done

/-- The full ordered assimilation fold retains its class map and transferred waiting table. -/
theorem assimilateMany_frame (graph : Graph Symbol Guard) (roots : Nat → Nat)
    (target : Nat) (sources : List Nat) (before after : Cached Symbol Guard)
    (correct : Correct graph roots before)
    (done : assimilateMany graph target sources before = some after) :
    after.core.representatives = before.core.representatives ∧ after.waiting = before.waiting := by
  induction sources generalizing before with
  | nil =>
      have unchanged : before = after := by simpa [assimilateMany] using done
      subst after
      exact ⟨rfl, rfl⟩
  | cons source rest ih =>
      cases step : assimilateOne graph target source before with
      | none => simp [assimilateMany, step] at done
      | some middle =>
          have continued : assimilateMany graph target rest middle = some after := by
            simpa [assimilateMany, step] using done
          obtain ⟨forest, waiting⟩ :=
            assimilateOne_frame graph roots target source before middle correct step
          obtain ⟨forestAfter, waitingAfter⟩ :=
            ih middle (assimilateOne_correct graph roots target source before middle correct step) continued
          exact ⟨forestAfter.trans forest, waitingAfter.trans waiting⟩

/-- The complete cached traversal equals the existing source core traversal. -/
theorem assimilateMany_source (graph : Graph Symbol Guard) (roots : Nat → Nat)
    (target : Nat) (sources : List Nat) (before after : Cached Symbol Guard)
    (correct : Correct graph roots before)
    (done : assimilateMany graph target sources before = some after) :
    (sources.forM (EnumerationState.assimilate graph target)) before.core = [.ok ((), after.core)] := by
  induction sources generalizing before with
  | nil =>
      have unchanged : before = after := by simpa [assimilateMany] using done
      subst after
      rfl
  | cons source rest ih =>
      cases step : assimilateOne graph target source before with
      | none => simp [assimilateMany, step] at done
      | some middle =>
          have continued : assimilateMany graph target rest middle = some after := by
            simpa [assimilateMany, step] using done
          change ((EnumerationState.assimilate graph target source) >>= fun _ =>
            rest.forM (EnumerationState.assimilate graph target)) before.core = _
          rw [bind_single _ _ _ _ _ (assimilateOne_source graph roots target source before middle correct step)]
          exact ih middle (assimilateOne_correct graph roots target source before middle correct step) continued

/-- Every successful source traversal retains a canonical cached endpoint in the same order. -/
theorem assimilateMany_complete (graph : Graph Symbol Guard) (roots : Nat → Nat)
    (target : Nat) (sources : List Nat) (before : Cached Symbol Guard) (afterCore : State Symbol Guard)
    (correct : Correct graph roots before)
    (success : Success (sources.forM (EnumerationState.assimilate graph target)) before.core () afterCore) :
    ∃ after, assimilateMany graph target sources before = some after ∧
      after.core = afterCore ∧ Correct graph roots after := by
  induction sources generalizing before with
  | nil =>
      have unchanged : afterCore = before.core := (success_pure () () _ _).mp success |>.2
      exact ⟨before, rfl, unchanged.symm, correct⟩
  | cons source rest ih =>
      change Success ((EnumerationState.assimilate graph target source) >>= fun _ =>
        rest.forM (EnumerationState.assimilate graph target)) before.core () afterCore at success
      obtain ⟨ignored, middleCore, first, continued⟩ := (success_bind _ _ _ _ _).mp success
      cases ignored
      obtain ⟨middle, step, middleSame, middleCorrect⟩ :=
        assimilateOne_complete graph roots target source before middleCore correct first
      have remaining : Success (rest.forM (EnumerationState.assimilate graph target)) middle.core () afterCore := by
        rw [middleSame]
        exact continued
      obtain ⟨after, traversed, afterSame, afterCorrect⟩ := ih middle middleCorrect remaining
      exact ⟨after, by simp [assimilateMany, step, traversed], afterSame, afterCorrect⟩

/-- Cached traversal preserves and reflects every successful core traversal. -/
theorem assimilateMany_success_iff (graph : Graph Symbol Guard) (roots : Nat → Nat)
    (target : Nat) (sources : List Nat) (before : Cached Symbol Guard) (afterCore : State Symbol Guard)
    (correct : Correct graph roots before) :
    Success (sources.forM (EnumerationState.assimilate graph target)) before.core () afterCore ↔
      ∃ after, assimilateMany graph target sources before = some after ∧ after.core = afterCore := by
  constructor
  · intro success
    obtain ⟨after, done, same, _⟩ :=
      assimilateMany_complete graph roots target sources before afterCore correct success
    exact ⟨after, done, same⟩
  · rintro ⟨after, done, rfl⟩
    simp [Success, assimilateMany_source graph roots target sources before after correct done, ExceptT.run]

/-- The native set fold visits distinct old roots in increasing identifier order. -/
def transferSources (forest : FlatUnionFind.Forest) (head : Nat) (tail : List Nat) : List Nat :=
  (mergeSources forest head tail).mergeSort (fun left right => decide (left ≤ right))

private theorem transferSources_members (forest : FlatUnionFind.Forest) (head : Nat) (tail : List Nat)
    (source : Nat) :
    source ∈ transferSources forest head tail ↔ source ∈ mergeSources forest head tail := by
  simp [transferSources]

/-- Transfer class counts and use the final flat forest's erased comparison view. -/
def prepare (forest : FlatUnionFind.Forest) (head : Nat) (tail : List Nat)
    (state : Cached Symbol Guard) : Cached Symbol Guard :=
  let finalForest := mergeClasses forest head tail
  let target := FlatUnionFind.root finalForest head
  let moved := transfer target (transferSources forest head tail) state
  EnumerationExpandableIndex.frame
    {moved.core with representatives := FlatUnionFind.erase finalForest} moved

/-- The actual union fold derives the cache class map used by count transfer. -/
theorem prepare_correct (graph : Graph Symbol Guard) (forest : FlatUnionFind.Forest)
    (head : Nat) (tail : List Nat) (before : Cached Symbol Guard)
    (valid : FlatUnionFind.Valid forest) (correct : Correct graph (FlatUnionFind.root forest) before) :
    Correct graph (FlatUnionFind.root (mergeClasses forest head tail)) (prepare forest head tail before) := by
  let finalForest := mergeClasses forest head tail
  let target := FlatUnionFind.root finalForest head
  let sources := transferSources forest head tail
  let moved := transfer target sources before
  have redirected := transfer_correct graph (FlatUnionFind.root forest) target sources before correct
  have maps := mergeClasses_root_redirect_of_membership forest head tail valid sources
    (transferSources_members forest head tail)
  have movedCorrect : Correct graph (FlatUnionFind.root finalForest) moved := maps.symm ▸ redirected
  exact frame_correct graph (FlatUnionFind.root finalForest) moved
    {moved.core with representatives := FlatUnionFind.erase finalForest} movedCorrect rfl rfl

/-- Execute native union, class-count transfer, and the original representative traversal. -/
def mergeTransaction (graph : Graph Symbol Guard) (forest : FlatUnionFind.Forest)
    (head : Nat) (tail : List Nat) (before : Cached Symbol Guard) : Option (Cached Symbol Guard) :=
  assimilateMany graph (FlatUnionFind.root (mergeClasses forest head tail) head)
    ((head :: tail).map (FlatUnionFind.root forest)) (prepare forest head tail before)

/-- Every returned transaction derives both cache equations for the actual final class map. -/
theorem mergeTransaction_correct (graph : Graph Symbol Guard) (forest : FlatUnionFind.Forest)
    (head : Nat) (tail : List Nat) (before after : Cached Symbol Guard)
    (valid : FlatUnionFind.Valid forest) (correct : Correct graph (FlatUnionFind.root forest) before)
    (done : mergeTransaction graph forest head tail before = some after) :
    Correct graph (FlatUnionFind.root (mergeClasses forest head tail)) after :=
  assimilateMany_correct graph _ _ _ _ after (prepare_correct graph forest head tail before valid correct) done

/-- Assimilation retains the final forest view and the already transferred waiting table. -/
theorem mergeTransaction_frame (graph : Graph Symbol Guard) (forest : FlatUnionFind.Forest)
    (head : Nat) (tail : List Nat) (before after : Cached Symbol Guard)
    (valid : FlatUnionFind.Valid forest) (correct : Correct graph (FlatUnionFind.root forest) before)
    (done : mergeTransaction graph forest head tail before = some after) :
    after.core.representatives = FlatUnionFind.erase (mergeClasses forest head tail) ∧
      after.waiting = EnumerationCanonicalWaiting.moveMany
        (FlatUnionFind.root (mergeClasses forest head tail) head) (transferSources forest head tail) before.waiting := by
  obtain ⟨forestSame, waitingSame⟩ := assimilateMany_frame graph _ _ _ _ after
    (prepare_correct graph forest head tail before valid correct) done
  exact ⟨forestSame, waitingSame⟩

/-- The transaction preserves and reflects the existing ordered assimilation core. -/
theorem mergeTransaction_success_iff (graph : Graph Symbol Guard) (forest : FlatUnionFind.Forest)
    (head : Nat) (tail : List Nat) (before : Cached Symbol Guard) (afterCore : State Symbol Guard)
    (valid : FlatUnionFind.Valid forest) (correct : Correct graph (FlatUnionFind.root forest) before) :
    Success (((head :: tail).map (FlatUnionFind.root forest)).forM
      (EnumerationState.assimilate graph (FlatUnionFind.root (mergeClasses forest head tail) head)))
      (prepare forest head tail before).core () afterCore ↔
      ∃ after, mergeTransaction graph forest head tail before = some after ∧ after.core = afterCore :=
  assimilateMany_success_iff graph _ _ _ _ afterCore
    (prepare_correct graph forest head tail before valid correct)

private theorem transaction_roots (graph : Graph Symbol Guard) (forest : FlatUnionFind.Forest)
    (head : Nat) (tail : List Nat) (before after : Cached Symbol Guard)
    (valid : FlatUnionFind.Valid forest) (correct : Correct graph (FlatUnionFind.root forest) before)
    (done : mergeTransaction graph forest head tail before = some after) :
    Roots after.core.representatives (FlatUnionFind.root (mergeClasses forest head tail)) := by
  rw [(mergeTransaction_frame graph forest head tail before after valid correct done).1]
  intro uv
  exact ⟨_, FlatUnionFind.erase_reaches (mergeClasses_valid forest head tail valid) uv⟩

/-- The returned native cache view has a finite agreeing scan without a supplied root witness. -/
theorem mergeTransaction_scan_complete (graph : Graph Symbol Guard) (forest : FlatUnionFind.Forest)
    (head : Nat) (tail : List Nat) (before after : Cached Symbol Guard)
    (valid : FlatUnionFind.Valid forest) (correct : Correct graph (FlatUnionFind.root forest) before)
    (done : mergeTransaction graph forest head tail before = some after) :
    ∃ fuel scanned, Success (findExpandable graph fuel) after.core (find after) scanned ∧
      EnumerationCompressionFrame.Frame after.core scanned :=
  scan_complete graph _ after (mergeTransaction_correct graph forest head tail before after valid correct done)
    (transaction_roots graph forest head tail before after valid correct done)

/-- Every successful comparison scan has the same offered list and a compression frame. -/
theorem mergeTransaction_scan_agrees (graph : Graph Symbol Guard) (forest : FlatUnionFind.Forest)
    (head : Nat) (tail : List Nat) (before after : Cached Symbol Guard)
    (valid : FlatUnionFind.Valid forest) (correct : Correct graph (FlatUnionFind.root forest) before)
    (done : mergeTransaction graph forest head tail before = some after)
    (fuel : Nat) (result : Option (List Nat)) (scanned : State Symbol Guard)
    (success : Success (findExpandable graph fuel) after.core result scanned) :
    result = find after ∧ EnumerationCompressionFrame.Frame after.core scanned :=
  scan_agrees graph _ after (mergeTransaction_correct graph forest head tail before after valid correct done)
    (transaction_roots graph forest head tail before after valid correct done) fuel result scanned success

end MicroCFTA.EnumerationCanonicalTransaction
