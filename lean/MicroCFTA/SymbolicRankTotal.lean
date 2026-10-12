import MicroCFTA.SymbolicRankCache

/-!
# Total inverse ranking for every supplied finite term

Accepted and rejected terms both terminate. The proof descends through the
supplied term and through each finite constructor list. It uses the proved
counter and singleton decoder termination results. No successful inverse
execution is assumed.
-/
namespace MicroCFTA.SymbolicDriver
open Language

/-- A finite inverse child traversal returns even when an earlier child is rejected. -/
theorem rankChildren_eventual [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (size : Nat → Nat)
    (invariant : Counts Symbol → Prop) (sound : CountSound graph size invariant)
    (children : List (Term Symbol × Nat))
    (childTotal : ∀ child ∈ children, ∀ root path before initial, invariant initial →
      Eventually (fun fuel => rankAt graph order fuel root path child.1 before) initial)
    (root : Nat) (path : List Nat) (before : Int) (initial : Counts Symbol) (valid : invariant initial) :
    Eventually (fun fuel => rankChildren graph order fuel root path before children) initial := by
  induction children generalizing root before initial with
  | nil => exact ⟨0, some (root, before), initial, fun fuel _ => by simp only [rankChildren]; rfl⟩
  | cons child rest ih =>
    rcases child with ⟨term, index⟩
    obtain ⟨firstBound, result, middle, firstStable⟩ :=
      childTotal (term, index) (by simp) root (path ++ [index]) before initial valid
    dsimp only at firstStable
    have middleValid := (ranking_preserves graph order size invariant sound firstBound).1
      root (path ++ [index]) term before initial result middle valid (firstStable firstBound (Nat.le_refl _))
    cases result with
    | none =>
      refine ⟨firstBound + 1, none, middle, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel =>
        simp only [rankChildren, Bind.bind, StateT.bind, firstStable fuel (by omega), Except.bind]
        rfl
    | some pair =>
      rcases pair with ⟨restricted, next⟩
      obtain ⟨restBound, result, after, restStable⟩ := ih
        (fun child member => childTotal child (by simp [member])) restricted next middle middleValid
      dsimp only at restStable
      refine ⟨max firstBound restBound + 1, result, after, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel =>
        simp only [rankChildren, Bind.bind, StateT.bind, firstStable fuel (by omega), Except.bind]
        exact restStable fuel (by omega)

/-- The inverse scans finitely many constructors and checks a finite supplied child tuple. -/
theorem rankConstructor_eventual [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph)
    (invariant : Counts Symbol → Prop) (sound : CountSound graph (fun node => (meaning.terms node).length) invariant)
    (countTotal : ∀ node state, Eventually (fun fuel => countNode graph fuel node) state)
    (children : List (Term Symbol))
    (childTotal : ∀ child ∈ children.zipIdx, ∀ root path before initial, invariant initial →
      Eventually (fun fuel => rankAt graph order fuel root path child.1 before) initial)
    (available : List (Symbol × Nat)) (root : Nat) (path : List Nat) (wanted : Symbol × Nat)
    (before : Int) (initial : Counts Symbol) (valid : invariant initial) :
    Eventually (fun fuel => rankConstructor graph order fuel root path wanted children before available) initial := by
  induction available generalizing before initial with
  | nil =>
    refine ⟨1, none, initial, ?_⟩
    intro fuel enough
    cases fuel with
    | zero => omega
    | succ fuel => rfl
  | cons constructor rest ih =>
    obtain ⟨countBound, middle, middleValid, counted⟩ :=
      count_eventual_exact graph meaning invariant sound countTotal (graph.condition path constructor root) initial valid
    by_cases same : constructor = wanted
    · subst wanted
      by_cases zero : ((meaning.terms (graph.condition path constructor root)).length : Int) = 0
      · refine ⟨countBound + 1, none, middle, ?_⟩
        intro fuel enough
        cases fuel with
        | zero => omega
        | succ fuel =>
          simp only [rankConstructor, Bind.bind, StateT.bind, counted fuel (by omega), Except.bind,
            ↓reduceIte, zero]
          rfl
      · obtain ⟨childBound, result, after, childrenStable⟩ := rankChildren_eventual graph order
          (fun node => (meaning.terms node).length) invariant sound children.zipIdx childTotal
          (graph.condition path constructor root) path before middle middleValid
        dsimp only at childrenStable
        refine ⟨max countBound childBound + 1, result, after, ?_⟩
        intro fuel enough
        cases fuel with
        | zero => omega
        | succ fuel =>
          simpa only [rankConstructor, Bind.bind, StateT.bind, counted fuel (by omega), Except.bind,
            ↓reduceIte, zero] using childrenStable fuel (by omega)
    · obtain ⟨restBound, result, after, restStable⟩ :=
        ih (before + ((meaning.terms (graph.condition path constructor root)).length : Int)) middle middleValid
      dsimp only at restStable
      refine ⟨max countBound restBound + 1, result, after, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel =>
        simp only [rankConstructor, Bind.bind, StateT.bind, counted fuel (by omega), Except.bind, same, ↓reduceIte]
        exact restStable fuel (by omega)

/-- Every finite supplied subtree has an eventual inverse result, including nonmembers. -/
theorem rankAt_eventual [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph)
    (invariant : Counts Symbol → Prop) (sound : CountSound graph (fun node => (meaning.terms node).length) invariant)
    (countTotal : ∀ node state, Eventually (fun fuel => countNode graph fuel node) state)
    (coverage : ConstructorCoverage graph order meaning) (term : Term Symbol)
    (root : Nat) (path : List Nat) (before : Int) (initial : Counts Symbol) (valid : invariant initial) :
    Eventually (fun fuel => rankAt graph order fuel root path term before) initial := by
  have loop : ∀ height term, term.height = height → ∀ root path before initial, invariant initial →
      Eventually (fun fuel => rankAt graph order fuel root path term before) initial := by
    intro height
    induction height using Nat.strongRecOn with
    | ind height ih =>
      intro term heightSame root path before initial valid
      cases term with
      | node symbol children =>
        obtain ⟨countBound, middle, middleValid, counted⟩ :=
          count_eventual_exact graph meaning invariant sound countTotal (graph.project path root) initial valid
        by_cases singleton : ((meaning.terms (graph.project path root)).length : Int) = 1
        · have length : (meaning.terms (graph.project path root)).length = 1 := by omega
          obtain ⟨whole, language⟩ := List.length_eq_one_iff.mp length
          obtain ⟨uniqueBound, unique, discarded, uniqueStable⟩ := selectUnique_eventual graph order meaning invariant
            sound countTotal coverage whole.height (graph.project path root) [] whole whole language rfl rfl middle middleValid
          dsimp only at uniqueStable
          refine ⟨max countBound uniqueBound + 1,
            (if termEq unique (.node symbol children) then some (root, before) else none), middle, ?_⟩
          intro fuel enough
          cases fuel with
          | zero => omega
          | succ fuel =>
            simp only [rankAt, Bind.bind, StateT.bind, counted fuel (by omega), Except.bind, singleton, ↓reduceIte]
            change Except.bind (isolated (selectUnique graph order fuel (graph.project path root) []) middle)
              (fun (chosen, cache) => .ok ((if termEq chosen (.node symbol children) then some (root, before) else none), cache)) = _
            rw [isolated_run, uniqueStable fuel (by omega)]
            rfl
        · by_cases present : (symbol, children.length) ∈ constructorsAt graph order path root
          · have childTotal : ∀ child ∈ children.zipIdx, ∀ root path before initial, invariant initial →
                Eventually (fun fuel => rankAt graph order fuel root path child.1 before) initial := by
              intro child member
              have childMember : child.1 ∈ children :=
                List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp member)
              have bound := height_le_forestHeight children child.1 childMember
              have smaller : child.1.height < height := by
                simp only [Term.height, forestHeight] at heightSame bound
                omega
              exact ih child.1.height smaller child.1 rfl
            obtain ⟨constructorBound, result, after, constructorStable⟩ := rankConstructor_eventual graph order meaning
              invariant sound countTotal children childTotal (constructorsAt graph order path root) root path
              (symbol, children.length) before middle middleValid
            dsimp only at constructorStable
            refine ⟨max countBound constructorBound + 1, result, after, ?_⟩
            intro fuel enough
            cases fuel with
            | zero => omega
            | succ fuel =>
              simp only [rankAt, Bind.bind, StateT.bind, counted fuel (by omega), Except.bind, singleton, ↓reduceIte, present]
              exact constructorStable fuel (by omega)
          · refine ⟨countBound + 1, none, middle, ?_⟩
            intro fuel enough
            cases fuel with
            | zero => omega
            | succ fuel =>
              simp only [rankAt, Bind.bind, StateT.bind, counted fuel (by omega), Except.bind, singleton, ↓reduceIte, present]
              rfl
  exact loop term.height term rfl root path before initial valid

/-- Public inverse ranking eventually returns one stable answer for every finite input term. -/
theorem rankOf_eventual [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph)
    (invariant : Counts Symbol → Prop) (empty : invariant {})
    (sound : CountSound graph (fun node => (meaning.terms node).length) invariant)
    (countTotal : ∀ node state, Eventually (fun fuel => countNode graph fuel node) state)
    (coverage : ConstructorCoverage graph order meaning) (root : Nat) (term : Term Symbol) :
    ∃ bound result, ∀ fuel, bound ≤ fuel → rankOf graph order fuel root term = .ok result := by
  obtain ⟨countBound, middle, middleValid, counted⟩ := count_eventual_exact graph meaning invariant sound countTotal root {} empty
  obtain ⟨rankBound, result, after, ranked⟩ := rankAt_eventual graph order meaning invariant sound countTotal coverage
    term root [] 0 middle middleValid
  dsimp only at ranked
  refine ⟨max countBound rankBound, result.map Prod.snd, ?_⟩
  intro fuel enough
  simp only [rankOf, counted fuel (by omega), ranked fuel (by omega), Bind.bind, Except.bind]
  rfl

/-- A nonmember is eventually rejected, without assuming that inverse execution succeeds. -/
theorem rankOf_eventually_rejects [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph)
    (invariant : Counts Symbol → Prop) (empty : invariant {})
    (sound : CountSound graph (fun node => (meaning.terms node).length) invariant)
    (countTotal : ∀ node state, Eventually (fun fuel => countNode graph fuel node) state)
    (coverage : ConstructorCoverage graph order meaning) (rootExact : RootProjectionExact graph meaning)
    (root : Nat) (term : Term Symbol) (absent : term ∉ meaning.terms root) :
    ∃ bound, ∀ fuel, bound ≤ fuel → rankOf graph order fuel root term = .ok none := by
  obtain ⟨bound, result, stable⟩ := rankOf_eventual graph order meaning invariant empty sound countTotal coverage root term
  have rejected := rankOf_rejects_nonmember graph order meaning invariant empty sound rootExact bound root term absent result
    (stable bound (Nat.le_refl _))
  exact ⟨bound, fun fuel enough => by simpa only [rejected] using stable fuel enough⟩

end MicroCFTA.SymbolicDriver
