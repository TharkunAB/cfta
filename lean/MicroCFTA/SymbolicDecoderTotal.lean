import MicroCFTA.SymbolicCounterTotal
import MicroCFTA.SymbolicVerified

/-!
# Successful finite bounds for source decoding

The counter's proven totality supplies stable exact block counts. Constructor
coverage comes from graph rows and projection coverage. Recursive singleton
selection decreases the height of its unique finite accepted term.
-/
namespace MicroCFTA.SymbolicDriver
open Language

/-- Every actual accepted subtree has its constructor in the source candidate list. -/
def ConstructorCoverage [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph) : Prop :=
  ∀ root path whole symbol children, whole ∈ meaning.terms root →
    whole.atPath path = some (.node symbol children) →
      (symbol, children.length) ∈ constructorsAt graph order path root

/-- Independent row semantics supplies constructor coverage for the literal projection/map/dedup/sort worker. -/
theorem constructorsAt_coverage [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph)
    (rows : ∀ node term, term ∈ meaning.terms node → ∃ edge ∈ graph.edges node, ShapeHolds meaning.terms edge term) :
    ConstructorCoverage graph order meaning := by
  intro root path whole symbol children accepted located
  obtain ⟨edge, member, values, same, related⟩ := rows (graph.project path root) (.node symbol children)
    (meaning.project path root whole (.node symbol children) accepted located)
  have shape := Term.node.inj same
  simp only [constructorsAt, List.mem_mergeSort, List.mem_eraseDups, List.mem_map]
  refine ⟨edge, member, Prod.ext shape.1.symm ?_⟩
  exact related.length_eq.trans (congrArg List.length shape.2.symm)

/-- A singleton root's conditioned language contains exactly its matching subtree constructor. -/
theorem singleton_condition_count (graph : Graph Symbol) (meaning : FiniteMeaning graph)
    [DecidableEq Symbol] (root : Nat) (path : List Nat) (whole : Term Symbol) (symbol : Symbol)
    (children : List (Term Symbol)) (singleton : meaning.terms root = [whole])
    (located : whole.atPath path = some (.node symbol children)) (constructor : Symbol × Nat) :
    (meaning.terms (graph.condition path constructor root)).length =
      if constructor = (symbol, children.length) then 1 else 0 := by
  have identifies : ∀ term ∈ meaning.terms (graph.condition path constructor root), term = whole ∧ constructor = (symbol, children.length) := by
    intro term member
    obtain ⟨rootMember, values, found, arity⟩ := (meaning.condition path constructor.1 constructor.2 root term).mp member
    have same : term = whole := by simpa only [singleton, List.mem_singleton] using rootMember
    subst term
    have shape := Term.node.inj (Option.some.inj (found.symm.trans located))
    exact ⟨rfl, Prod.ext shape.1 (arity.symm.trans (congrArg List.length shape.2))⟩
  by_cases matching : constructor = (symbol, children.length)
  · rw [ite_eq_left matching]
    have accepted : whole ∈ meaning.terms (graph.condition path constructor root) := by
      apply (meaning.condition path constructor.1 constructor.2 root whole).mpr
      exact ⟨by simp [singleton], children, by simpa only [matching] using located, by simp only [matching]⟩
    have positive := List.length_pos_of_mem accepted
    have upper := List.Nodup.length_le_of_subset (meaning.distinct (graph.condition path constructor root)) (by
      intro term member
      exact (List.mem_singleton).mpr (identifies term member).1)
    simp only [List.length_singleton] at upper
    omega
  · rw [ite_eq_right matching]
    apply List.length_eq_zero_iff.mpr
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro term member
    exact matching (identifies term member).2

/-- Proven counter semantics and totality give stable exact values and a correct final cache. -/
theorem count_eventual_exact [DecidableEq Symbol] [Ord Symbol] (graph : Graph Symbol) (meaning : FiniteMeaning graph)
    (invariant : Counts Symbol → Prop)
    (sound : CountSound graph (fun node => (meaning.terms node).length) invariant)
    (total : ∀ node state, Eventually (fun fuel => countNode graph fuel node) state)
    (node : Nat) (initial : Counts Symbol) (valid : invariant initial) :
    ∃ bound finalState, invariant finalState ∧ ∀ fuel, bound ≤ fuel →
      countNode graph fuel node initial = .ok (((meaning.terms node).length : Int), finalState) := by
  obtain ⟨bound, count, finalState, stable⟩ := total node initial
  have correct := sound bound node initial count finalState valid (stable bound (Nat.le_refl _))
  refine ⟨bound, finalState, correct.2, ?_⟩
  intro fuel enough
  simpa only [correct.1] using stable fuel enough

/-- Isolated finite child traversals share one bound and return their exact input cache. -/
theorem isolated_mapM_eventual (action : Nat → Input → CountM Symbol Output) (inputs : List Input)
    (initial : Counts Symbol) (total : ∀ input ∈ inputs, Eventually (fun fuel => action fuel input) initial) :
    ∃ bound outputs, ∀ fuel, bound ≤ fuel →
      (inputs.mapM (fun input => isolated (action fuel input)) : CountM Symbol (List Output)) initial = .ok (outputs, initial) := by
  induction inputs with
  | nil => exact ⟨0, [], fun _ _ => rfl⟩
  | cons input inputs ih =>
      obtain ⟨firstBound, output, discarded, firstStable⟩ := total input (by simp)
      obtain ⟨restBound, outputs, restStable⟩ := ih (fun other member => total other (by simp [member]))
      dsimp only at firstStable
      refine ⟨max firstBound restBound, output :: outputs, ?_⟩
      intro fuel enough
      have head : isolated (action fuel input) initial = .ok (output, initial) := by
        rw [isolated_run, firstStable fuel (by omega)]
      simp only [List.mapM_cons]
      change Except.bind (isolated (action fuel input) initial) (fun (value, cache) =>
        Except.bind ((inputs.mapM (fun input => isolated (action fuel input)) : CountM Symbol (List Output)) cache)
          (fun (values, state) => .ok (value :: values, state))) = _
      rw [head]
      simp only [Except.bind, restStable fuel (by omega)]

/-- A finite singleton constructor scan eventually chooses its existing constructor and traverses all child positions. -/
theorem uniqueConstructor_eventual [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph)
    (invariant : Counts Symbol → Prop) (sound : CountSound graph (fun node => (meaning.terms node).length) invariant)
    (countTotal : ∀ node state, Eventually (fun fuel => countNode graph fuel node) state)
    (root : Nat) (path : List Nat) (whole : Term Symbol) (symbol : Symbol) (children : List (Term Symbol))
    (singleton : meaning.terms root = [whole]) (located : whole.atPath path = some (.node symbol children))
    (childTotal : ∀ index ∈ List.range children.length, ∀ state, invariant state →
      Eventually (fun fuel => selectUnique graph order fuel root (path ++ [index])) state)
    (constructors : List (Symbol × Nat)) (covered : (symbol, children.length) ∈ constructors)
    (initial : Counts Symbol) (valid : invariant initial) :
    Eventually (fun fuel => uniqueConstructor graph order fuel root path constructors) initial := by
  induction constructors generalizing initial with
  | nil => cases covered
  | cons constructor rest ih =>
      obtain ⟨countBound, middle, middleValid, counted⟩ :=
        count_eventual_exact graph meaning invariant sound countTotal (graph.condition path constructor root) initial valid
      have countValue := singleton_condition_count graph meaning root path whole symbol children singleton located constructor
      by_cases matching : constructor = (symbol, children.length)
      · subst constructor
        have countOne : (meaning.terms (graph.condition path (symbol, children.length) root)).length = 1 := by
          simpa only [ite_true] using countValue
        obtain ⟨childBound, outputs, childrenStable⟩ := isolated_mapM_eventual
          (fun fuel index => selectUnique graph order fuel root (path ++ [index])) (List.range children.length) middle
          (fun index member => childTotal index member middle middleValid)
        refine ⟨max countBound childBound + 1, .node symbol outputs, middle, ?_⟩
        intro fuel enough
        cases fuel with
        | zero => omega
        | succ fuel =>
            simp only [uniqueConstructor, Bind.bind, StateT.bind, counted fuel (by omega), countOne, Except.bind,
              Int.natCast_one, Int.one_ne_zero, ite_false]
            change Except.bind ((List.range children.length |>.mapM fun index => isolated (selectUnique graph order fuel root (path ++ [index]))) middle)
              (fun (values, cache) => .ok (Term.node symbol values, cache)) = _
            rw [childrenStable fuel (by omega)]
            rfl
      · have countZero : (meaning.terms (graph.condition path constructor root)).length = 0 := by
          simpa only [ite_eq_right matching] using countValue
        have tailCovered : (symbol, children.length) ∈ rest := by
          rcases List.mem_cons.mp covered with equal | tail
          · exact False.elim (matching equal.symm)
          · exact tail
        obtain ⟨restBound, output, finalState, restStable⟩ := ih tailCovered middle middleValid
        dsimp only at restStable
        refine ⟨max countBound restBound + 1, output, finalState, ?_⟩
        intro fuel enough
        cases fuel with
        | zero => omega
        | succ fuel =>
            simp only [uniqueConstructor, Bind.bind, StateT.bind, counted fuel (by omega), countZero, Except.bind]
            exact restStable fuel (by omega)

/-- The actual singleton decoder terminates by strict descent in the selected finite subtree. -/
theorem selectUnique_eventual [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph)
    (invariant : Counts Symbol → Prop) (sound : CountSound graph (fun node => (meaning.terms node).length) invariant)
    (countTotal : ∀ node state, Eventually (fun fuel => countNode graph fuel node) state)
    (coverage : ConstructorCoverage graph order meaning)
    (height : Nat) : ∀ root path whole part, meaning.terms root = [whole] →
      whole.atPath path = some part → part.height = height → ∀ initial, invariant initial →
      Eventually (fun fuel => selectUnique graph order fuel root path) initial := by
  induction height using Nat.strongRecOn with
  | ind height ih =>
      intro root path whole part singleton located heightSame initial valid
      cases part with
      | node symbol children =>
          have childTotal : ∀ index ∈ List.range children.length, ∀ state, invariant state →
              Eventually (fun fuel => selectUnique graph order fuel root (path ++ [index])) state := by
            intro index member state stateValid
            have bound := List.mem_range.mp member
            have childFound : children[index]? = some children[index] := List.getElem?_eq_getElem bound
            have childLocated : whole.atPath (path ++ [index]) = some children[index] := by
              simp only [atPath_append, located, Option.bind_some, Term.atPath, childFound, Option.bind_some]
            have childHeight := height_le_forestHeight children children[index] (List.getElem_mem bound)
            have smaller : children[index].height < height := by
              simp only [Term.height, forestHeight] at heightSame childHeight
              omega
            exact ih children[index].height smaller root (path ++ [index]) whole children[index] singleton childLocated rfl state stateValid
          have scan := uniqueConstructor_eventual graph order meaning invariant sound countTotal root path whole symbol children
            singleton located childTotal (constructorsAt graph order path root)
            (coverage root path whole symbol children (by simp [singleton]) located) initial valid
          exact eventually_succ _ _ initial (fun _ => rfl) scan

end MicroCFTA.SymbolicDriver
