import MicroCFTA.EnumerationPartialObservation
import MicroCFTA.EnumerationOrder

/-!
# Finite partial rendering from fragment dependency levels

Stored fragment references strictly increase their dependency level.
Pending slots stop partial rendering. They need no completed graph value.
-/

namespace MicroCFTA.EnumerationPartialCompletion
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule
open EnumerationDriver EnumerationDependencies EnumerationOrder EnumerationReferences
open EnumerationExecution EnumerationObservations EnumerationCompressionFrame

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

/-- An allocated variable has a finite actual slot read with safe compression. -/
theorem getValue_complete (before : State Symbol Guard) (safe : Safe before)
    (uv : Nat) (inside : uv < before.counter) :
    ∃ fuel root value after, Success (getValue fuel uv) before value after ∧
      RenderStable before after ∧ before.values[root]? = some value ∧
      ∃ size, UnionFind.Reaches before.representatives uv root size := by
  obtain ⟨root, size, path⟩ := safe.1.total uv
  have index : root < before.values.length := by
    rw [← safe.1.aligned]
    exact reaches_bounded before.representatives before.counter safe.1.forest path inside
  let value := before.values[root]
  have stored : before.values[root]? = some value := List.getElem?_eq_getElem index
  obtain ⟨fuel, found, lookup⟩ := UnionFind.findRoot_terminates path
  have rootSame := (UnionFind.reaches_unique
    (UnionFind.findRoot_correct fuel before.representatives uv found lookup).1 path).1
  let after := {before with representatives := found.forest}
  have reading : Success (getValue fuel uv) before value after :=
    (getValue_success fuel uv before after value).mpr
      ⟨found, lookup, by simpa [rootSame] using stored, rfl⟩
  exact ⟨fuel, root, value, after, reading,
    (getValue_storage fuel uv before after value safe inside reading).1, stored, size, path⟩

/-- Bounded partial rendering completes and retains safety, its full frame and dependency levels. -/
theorem expandPartial_complete (graph : Graph Symbol Guard) (level : Nat → Nat)
    (frontier : Nat) (fragment : Fragment Symbol) (before : State Symbol Guard)
    (safe : Safe before) (stratified : Stratified before level frontier)
    (allocated : FragmentBound before.counter fragment) :
    ∃ fuel term after, Success (expandPartial graph fuel fragment) before term after ∧
      RenderStable before after ∧ Frame before after ∧ Stratified after level frontier := by
  have construct : ∀ depth, ∀ fragment (before : State Symbol Guard), Safe before →
      Stratified before level frontier → FragmentBound before.counter fragment →
      (∀ uv, HasHole fragment uv → frontier - level uv < depth) →
      ∃ fuel term after, Success (expandPartial graph fuel fragment) before term after ∧
        RenderStable before after := by
    intro depth
    induction depth using Nat.strongRecOn with
    | ind depth ih =>
        intro fragment
        induction fragment using Fragment.rec
          (motive_2 := fun fragments => ∀ (before : State Symbol Guard), Safe before →
            Stratified before level frontier →
            (∀ fragment ∈ fragments, FragmentBound before.counter fragment) →
            (∀ fragment ∈ fragments, ∀ uv, HasHole fragment uv → frontier - level uv < depth) →
            ∃ fuel terms after, Success (fragments.mapM (expandPartial graph fuel)) before terms after ∧
              RenderStable before after) with
        | hole uv =>
            intro before safe stratified allocated bounded
            have small := bounded uv (.hole uv)
            obtain ⟨readFuel, root, value, resolved, reading, readStable, stored, size, path⟩ :=
              getValue_complete before safe uv allocated
            have readingAt : ∀ fuel, readFuel ≤ fuel →
                Success (getValue fuel uv) before value resolved := by
              intro fuel enough
              obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le enough
              exact getValue_moreFuel readFuel extra uv before value resolved reading
            cases value with
            | enumerated storedFragment =>
                have sameLevel := stratified.classes uv root (UnionFind.sameClass_root path)
                obtain ⟨rootBound, dependencies⟩ := stratified.expanded root storedFragment stored
                have storedAllocated : FragmentBound resolved.counter storedFragment := by
                  rw [readStable.counter]
                  exact safe.1.values _ (List.mem_of_getElem? stored)
                have storedBound : ∀ child, HasHole storedFragment child →
                    frontier - level child < frontier - level uv := by
                  intro child hole
                  have higher := dependencies child hole
                  omega
                obtain ⟨renderFuel, term, after, rendering, renderedStable⟩ :=
                  ih (frontier - level uv) small storedFragment resolved readStable.safe
                    (stratified_read before resolved level frontier readStable stratified)
                    storedAllocated storedBound
                let fuel := readFuel + renderFuel
                refine ⟨fuel + 1, term, after, ?_, readStable.trans renderedStable⟩
                simp only [expandPartial]
                apply (success_bind _ _ _ _ _).mpr
                refine ⟨.enumerated storedFragment, resolved, readingAt (fuel + 1) (by dsimp [fuel]; omega), ?_⟩
                simpa [fuel, Nat.add_comm] using
                  expandPartial_moreFuel graph renderFuel readFuel storedFragment resolved term after rendering
            | eliminated =>
                exact ⟨readFuel + 1, .node (.hole uv) [], resolved,
                  (success_bind _ _ _ _ _).mpr ⟨.eliminated, resolved,
                    readingAt (readFuel + 1) (by omega), (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩,
                  readStable⟩
            | unenumerated node scs =>
                cases node with
                | none =>
                    exact ⟨readFuel + 1, .node (.hole uv) [], resolved,
                      (success_bind _ _ _ _ _).mpr ⟨.unenumerated none scs, resolved,
                        readingAt (readFuel + 1) (by omega), (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩,
                      readStable⟩
                | some node =>
                    cases scs with
                    | cons first rest =>
                        exact ⟨readFuel + 1, .node (.hole uv) [], resolved,
                          (success_bind _ _ _ _ _).mpr ⟨.unenumerated (some node) (first :: rest), resolved,
                            readingAt (readFuel + 1) (by omega), (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩,
                          readStable⟩
                    | nil =>
                        refine ⟨readFuel + 1, (match graph.node node with
                          | .recursive _ => .node .truncated []
                          | _ => .node (.hole uv) []), resolved,
                          (success_bind _ _ _ _ _).mpr ⟨.unenumerated (some node) [], resolved,
                            readingAt (readFuel + 1) (by omega), ?_⟩, readStable⟩
                        cases view : graph.node node <;> simp only [view] <;>
                          exact (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩
        | node symbol children childIH =>
            intro before safe stratified allocated bounded
            obtain ⟨fuel, terms, after, traversal, stable⟩ := childIH before safe stratified
              (fun child member => fragmentsBound_member before.counter children allocated child member)
              (fun child member uv hole => bounded uv (.child symbol children child uv member hole))
            exact ⟨fuel + 1, .node (.concrete symbol) terms, after,
              (success_bind _ _ _ _ _).mpr ⟨terms, after, traversal,
                (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩, stable⟩
        | nil =>
            rename_i before safe stratified allocated bounded
            exact ⟨0, [], before, (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩, .refl before safe⟩
        | cons child children childIH childrenIH =>
            rename_i before safe stratified allocated bounded
            obtain ⟨firstFuel, term, middle, first, firstStable⟩ :=
              childIH before safe stratified (allocated child (by simp)) (bounded child (by simp))
            obtain ⟨restFuel, terms, after, continued, lastStable⟩ :=
              childrenIH middle firstStable.safe
                (stratified_read before middle level frontier firstStable stratified)
                (fun fragment member => by rw [firstStable.counter]; exact allocated fragment (by simp [member]))
                (fun fragment member => bounded fragment (by simp [member]))
            refine ⟨firstFuel + restFuel, term :: terms, after, ?_, firstStable.trans lastStable⟩
            rw [List.mapM_cons]
            apply (success_bind _ _ _ _ _).mpr
            refine ⟨term, middle, expandPartial_moreFuel graph firstFuel restFuel child before term middle first, ?_⟩
            apply (success_bind _ _ _ _ _).mpr
            refine ⟨terms, after, ?_, (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩
            have more := retains_mapM _ _
              (fun fragment => expandPartial_moreFuel graph restFuel firstFuel fragment)
              children middle terms after continued
            simpa [Nat.add_comm] using more
  obtain ⟨fuel, term, after, rendering, stable⟩ := construct (frontier + 1) fragment before
    safe stratified allocated (by intro uv _; omega)
  exact ⟨fuel, term, after, rendering, stable,
    expandPartial_frame graph fuel fragment before after term safe.1.total rendering,
    stratified_read before after level frontier stable stratified⟩

end MicroCFTA.EnumerationPartialCompletion
