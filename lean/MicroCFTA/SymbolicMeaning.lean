import MicroCFTA.SymbolicBounds

/-!
# Finite-language meaning of source symbolic selection

The graph interface states exact constructor conditioning and conservative
subtree projection. The counter contract remains explicit. These proofs use
the actual selection functions and their cache state.
-/
namespace MicroCFTA.SymbolicDriver
open Language

/-- The finite distinct-term meaning of the graph operations used by the decoder. -/
structure FiniteMeaning (graph : Graph Symbol) where
  terms : Nat → List (Term Symbol)
  distinct : ∀ node, (terms node).Nodup
  condition : ∀ path symbol arity root whole,
    whole ∈ terms (graph.condition path (symbol, arity) root) ↔
      whole ∈ terms root ∧ ∃ children,
        whole.atPath path = some (.node symbol children) ∧ children.length = arity
  project : ∀ path root whole part,
    whole ∈ terms root → whole.atPath path = some part → part ∈ terms (graph.project path root)

/-- Extract the successful inner singleton execution from an isolated source call. -/
theorem isolated_inner (action : CountM Symbol Value) (initial after : Counts Symbol) (value : Value)
    (success : isolated action initial = .ok (value, after)) :
    ∃ inner, action initial = .ok (value, inner) ∧ after = initial := by
  rw [isolated_run] at success
  cases result : action initial with
  | error error => simp only [result] at success; cases success
  | ok pair =>
      rcases pair with ⟨found, inner⟩
      simp only [result, Except.ok.injEq, Prod.mk.injEq] at success
      rcases success with ⟨rfl, rfl⟩
      exact ⟨inner, rfl, rfl⟩

/-- Indexed lookup reconstructs the full ordered child list. -/
theorem map_lookup_range (values : List Value) (fallback : Value) :
    (List.range values.length).map (fun index => (values[index]?).getD fallback) = values := by
  apply List.ext_getElem
  · simp
  · intro index left right
    simp [List.getElem?_eq_getElem right]

def UniqueMeaning [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph)
    (invariant : Counts Symbol → Prop) (fuel : Nat) : Prop :=
  ∀ root path initial term after whole, meaning.terms root = [whole] → invariant initial →
    selectUnique graph order fuel root path initial = .ok (term, after) →
      whole.atPath path = some term ∧ invariant after

def UniqueConstructorMeaning [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph)
    (invariant : Counts Symbol → Prop) (fuel : Nat) : Prop :=
  ∀ root path constructors initial term after whole, meaning.terms root = [whole] → invariant initial →
    uniqueConstructor graph order fuel root path constructors initial = .ok (term, after) →
      whole.atPath path = some term ∧ invariant after

/-- A nonempty constructor block in a singleton language identifies its sole subtree. -/
theorem unique_constructor_meaning_step [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph)
    (invariant : Counts Symbol → Prop)
    (countsSound : CountSound graph (fun node => (meaning.terms node).length) invariant) (fuel : Nat)
    (unique : UniqueMeaning graph order meaning invariant fuel)
    (remaining : UniqueConstructorMeaning graph order meaning invariant fuel) :
    UniqueConstructorMeaning graph order meaning invariant (fuel + 1) := by
  intro root path constructors initial term after whole singleton starts success
  cases constructors with
  | nil => cases success
  | cons constructor rest =>
      rcases constructor with ⟨symbol, arity⟩
      cases counted : countNode graph fuel (graph.condition path (symbol, arity) root) initial with
      | error error =>
          simp only [uniqueConstructor, Bind.bind, StateT.bind, counted, Except.bind] at success
          cases success
      | ok pair =>
          rcases pair with ⟨count, middle⟩
          have countedCorrect := countsSound fuel (graph.condition path (symbol, arity) root) initial count middle starts counted
          simp only [uniqueConstructor, Bind.bind, StateT.bind, counted, Except.bind] at success
          by_cases empty : count = 0
          · simp only [empty, ↓reduceIte] at success
            exact remaining root path rest middle term after whole singleton countedCorrect.2 success
          · simp only [empty, ↓reduceIte] at success
            have countMeaning := countedCorrect.1
            dsimp only at countMeaning
            have nonempty : 0 < (meaning.terms (graph.condition path (symbol, arity) root)).length := by omega
            obtain ⟨accepted, member⟩ := List.length_pos_iff_exists_mem.mp nonempty
            obtain ⟨rootMember, children, located, length⟩ := (meaning.condition path symbol arity root accepted).mp member
            have same : accepted = whole := by simpa only [singleton, List.mem_singleton] using rootMember
            subst accepted
            let action := fun index => isolated (selectUnique graph order fuel root (path ++ [index]))
            change Except.bind ((List.range arity |>.mapM action : CountM Symbol (List (Term Symbol))) middle)
              (fun (terms, cache) => .ok (Term.node symbol terms, cache)) = .ok (term, after) at success
            cases selected : ((List.range arity).mapM action : CountM Symbol (List (Term Symbol))) middle with
            | error error => simp only [selected, Except.bind] at success; cases success
            | ok pair =>
                rcases pair with ⟨terms, cache⟩
                have childrenCorrect := state_mapM_correct action
                  (fun index => (whole.atPath (path ++ [index])).getD whole) invariant
                  (fun index before child final start done => by
                    obtain ⟨inner, innerRun, restored⟩ := isolated_inner _ before final child done
                    have result := unique root (path ++ [index]) before child inner whole singleton start innerRun
                    refine ⟨?_, restored ▸ start⟩
                    simp only [result.1, Option.getD_some])
                  (List.range arity) middle cache terms countedCorrect.2 selected
                have expected : (List.range arity).map (fun index => (whole.atPath (path ++ [index])).getD whole) = children := by
                  rw [← length]
                  simp only [atPath_append, located, Option.bind_some, Term.atPath, Option.bind_fun_some]
                  exact map_lookup_range children whole
                simp only [selected, Except.bind, Except.ok.injEq, Prod.mk.injEq] at success
                rcases success with ⟨rfl, rfl⟩
                exact ⟨by rw [childrenCorrect.1, expected]; exact located, childrenCorrect.2⟩

/-- The actual singleton decoder returns the selected subtree of the unique finite term. -/
theorem singleton_decoder_meaning [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph)
    (invariant : Counts Symbol → Prop)
    (countsSound : CountSound graph (fun node => (meaning.terms node).length) invariant) (fuel : Nat) :
    UniqueMeaning graph order meaning invariant fuel ∧ UniqueConstructorMeaning graph order meaning invariant fuel := by
  induction fuel with
  | zero =>
      constructor
      · intro root path initial term after whole singleton starts success
        cases success
      · intro root path constructors initial term after whole singleton starts success
        cases success
  | succ fuel ih =>
      constructor
      · intro root path initial term after whole singleton starts success
        exact ih.2 root path (constructorsAt graph order path root) initial term after whole singleton starts success
      · exact unique_constructor_meaning_step graph order meaning invariant countsSound fuel ih.1 ih.2

/-- A selected graph retains only terms from the previous graph. -/
def GraphSubset (meaning : FiniteMeaning graph) (selected original : Nat) : Prop :=
  ∀ term ∈ meaning.terms selected, term ∈ meaning.terms original

/-- The caller selects a position that exists in every current candidate. -/
def PathExists (meaning : FiniteMeaning graph) (root : Nat) (path : List Nat) : Prop :=
  ∀ whole ∈ meaning.terms root, ∃ part, whole.atPath path = some part

def SelectionMeaning [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph)
    (invariant : Counts Symbol → Prop) (fuel : Nat) : Prop :=
  ∀ root path rank initial term final suffix after, invariant initial → 0 ≤ rank → PathExists meaning root path →
    selectAt graph order fuel root path rank initial = .ok ((term, final, suffix), after) →
      invariant after ∧ GraphSubset meaning final root ∧
        ∀ whole ∈ meaning.terms final, whole.atPath path = some term

def ConstructorMeaning [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph)
    (invariant : Counts Symbol → Prop) (fuel : Nat) : Prop :=
  ∀ root path rank constructors initial term final suffix after, constructors.Nodup → invariant initial → 0 ≤ rank →
    chooseConstructor graph order fuel root path rank constructors initial = .ok ((term, final, suffix), after) →
      invariant after ∧ GraphSubset meaning final root ∧
        ∀ whole ∈ meaning.terms final, whole.atPath path = some term

def ChildrenMeaning [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph)
    (invariant : Counts Symbol → Prop) (fuel : Nat) : Prop :=
  ∀ root path rank indices initial children final suffix after, invariant initial → 0 ≤ rank →
    (∀ index ∈ indices, PathExists meaning root (path ++ [index])) →
    selectChildren graph order fuel root path rank indices initial = .ok ((children, final, suffix), after) →
      invariant after ∧ GraphSubset meaning final root ∧
        ∀ whole ∈ meaning.terms final,
          All₂ (fun index term => whole.atPath (path ++ [index]) = some term) indices children

/-- Pointwise functional outputs form the mapped input list. -/
theorem all₂_functional (value : Input → Output) (inputs : List Input) (outputs : List Output)
    (related : All₂ (fun input output => output = value input) inputs outputs) : outputs = inputs.map value := by
  induction related with
  | nil => rfl
  | cons head tail ih => simp only [List.map_cons, head, ih]

/-- Selecting all child positions determines the entire child tuple. -/
theorem child_positions_determine (whole : Term Symbol) (path : List Nat) (symbol : Symbol)
    (original selected : List (Term Symbol)) (located : whole.atPath path = some (.node symbol original))
    (related : All₂ (fun index term => whole.atPath (path ++ [index]) = some term)
      (List.range original.length) selected) : selected = original := by
  have mapped := all₂_functional (fun index => (original[index]?).getD whole) _ _
    (related.imp fun index term same => by
      have child : original[index]? = some term := by
        simpa only [atPath_append, located, Option.bind_some, Term.atPath, Option.bind_fun_some] using same
      simp only [child, Option.getD_some])
  exact mapped.trans (map_lookup_range original whole)

/-- A singleton projection fixes every candidate's selected subtree without changing its siblings. -/
theorem selection_meaning_step [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph)
    (invariant : Counts Symbol → Prop)
    (countsSound : CountSound graph (fun node => (meaning.terms node).length) invariant) (fuel : Nat)
    (constructors : ConstructorMeaning graph order meaning invariant fuel) :
    SelectionMeaning graph order meaning invariant (fuel + 1) := by
  intro root path rank initial term final suffix after starts nonnegative existsPath success
  cases counted : countNode graph fuel (graph.project path root) initial with
  | error error => simp only [selectAt, Bind.bind, StateT.bind, counted, Except.bind] at success; cases success
  | ok pair =>
      rcases pair with ⟨count, middle⟩
      have correct := countsSound fuel (graph.project path root) initial count middle starts counted
      simp only [selectAt, Bind.bind, StateT.bind, counted, Except.bind] at success
      by_cases singleton : count = 1
      · simp only [singleton, ↓reduceIte] at success
        have countMeaning := correct.1
        dsimp only at countMeaning
        have length : (meaning.terms (graph.project path root)).length = 1 := by omega
        obtain ⟨uniqueTerm, uniqueLanguage⟩ := List.length_eq_one_iff.mp length
        change Except.bind (isolated (selectUnique graph order fuel (graph.project path root) []) middle)
          (fun (selected, cache) => .ok ((selected, root, rank), cache)) = .ok ((term, final, suffix), after) at success
        cases unique : isolated (selectUnique graph order fuel (graph.project path root) []) middle with
        | error error => simp only [unique, Except.bind] at success; cases success
        | ok pair =>
            rcases pair with ⟨chosen, cache⟩
            obtain ⟨inner, innerRun, restored⟩ := isolated_inner _ middle cache chosen unique
            have decoded := (singleton_decoder_meaning graph order meaning invariant countsSound fuel).1
              (graph.project path root) [] middle chosen inner uniqueTerm uniqueLanguage correct.2 innerRun
            have chosenSame : uniqueTerm = chosen := Option.some.inj decoded.1
            simp only [unique, Except.bind, Except.ok.injEq, Prod.mk.injEq] at success
            rcases success with ⟨⟨rfl, rfl, rfl⟩, rfl⟩
            refine ⟨restored ▸ correct.2, fun _ member => member, ?_⟩
            intro whole member
            obtain ⟨part, located⟩ := existsPath whole member
            have projected := meaning.project path root whole part member located
            have same : part = chosen := by simpa only [uniqueLanguage, List.mem_singleton, chosenSame] using projected
            simpa only [same] using located
      · simp only [singleton, ↓reduceIte] at success
        exact constructors root path rank (constructorsAt graph order path root) middle term final suffix after
          (constructorsAt_nodup graph order path root) correct.2 nonnegative success

/-- Constructor conditioning and all selected children determine the returned subtree. -/
theorem constructor_meaning_step [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph)
    (invariant : Counts Symbol → Prop)
    (countsSound : CountSound graph (fun node => (meaning.terms node).length) invariant) (fuel : Nat)
    (remaining : ConstructorMeaning graph order meaning invariant fuel)
    (childrenMeaning : ChildrenMeaning graph order meaning invariant fuel) :
    ConstructorMeaning graph order meaning invariant (fuel + 1) := by
  intro root path rank constructors initial term final suffix after distinct starts nonnegative success
  cases constructors with
  | nil => cases success
  | cons constructor rest =>
      rcases constructor with ⟨symbol, arity⟩
      cases counted : countNode graph fuel (graph.condition path (symbol, arity) root) initial with
      | error error => simp only [chooseConstructor, Bind.bind, StateT.bind, counted, Except.bind] at success; cases success
      | ok pair =>
          rcases pair with ⟨count, middle⟩
          have correct := countsSound fuel (graph.condition path (symbol, arity) root) initial count middle starts counted
          simp only [chooseConstructor, Bind.bind, StateT.bind, counted, Except.bind] at success
          by_cases skip : rank ≥ count
          · simp only [skip, ↓reduceIte] at success
            exact remaining root path (rank - count) rest middle term final suffix after
              (List.nodup_cons.mp distinct).2 correct.2 (by omega) success
          · simp only [skip, ↓reduceIte] at success
            have existsPath : ∀ index ∈ List.range arity,
                PathExists meaning (graph.condition path (symbol, arity) root) (path ++ [index]) := by
              intro index valid whole member
              obtain ⟨_, children, located, length⟩ := (meaning.condition path symbol arity root whole).mp member
              have bound : index < children.length := by simpa only [length, List.mem_range] using valid
              refine ⟨children[index]'bound, ?_⟩
              simp only [atPath_append, located, Option.bind_some, Term.atPath, List.getElem?_eq_getElem bound, Option.bind_some]
            change Except.bind
              (selectChildren graph order fuel (graph.condition path (symbol, arity) root) path rank (List.range arity) middle)
              (fun ((terms, last, residual), cache) => .ok ((Term.node symbol terms, last, residual), cache)) =
                .ok ((term, final, suffix), after) at success
            cases selected : selectChildren graph order fuel (graph.condition path (symbol, arity) root)
                path rank (List.range arity) middle with
            | error error => simp only [selected, Except.bind] at success; cases success
            | ok pair =>
                rcases pair with ⟨⟨terms, last, residual⟩, cache⟩
                have decoded := childrenMeaning (graph.condition path (symbol, arity) root) path rank
                  (List.range arity) middle terms last residual cache correct.2 nonnegative existsPath selected
                simp only [selected, Except.bind, Except.ok.injEq, Prod.mk.injEq] at success
                rcases success with ⟨⟨rfl, rfl, rfl⟩, rfl⟩
                refine ⟨decoded.1, ?_, ?_⟩
                · intro whole member
                  exact ((meaning.condition path symbol arity root whole).mp (decoded.2.1 whole member)).1
                · intro whole member
                  obtain ⟨_, originals, located, length⟩ :=
                    (meaning.condition path symbol arity root whole).mp (decoded.2.1 whole member)
                  have related := decoded.2.2 whole member
                  rw [← length] at related
                  have same := child_positions_determine whole path symbol originals terms located related
                  simpa only [same] using located

/-- Later child restrictions retain the subtrees selected at all earlier positions. -/
theorem children_meaning_step [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph)
    (invariant : Counts Symbol → Prop) (fuel : Nat)
    (selection : SelectionMeaning graph order meaning invariant fuel)
    (remaining : ChildrenMeaning graph order meaning invariant fuel) :
    ChildrenMeaning graph order meaning invariant (fuel + 1) := by
  intro root path rank indices initial children final suffix after starts nonnegative existsPath success
  cases indices with
  | nil => cases success; exact ⟨starts, fun _ member => member, fun _ _ => .nil⟩
  | cons index rest =>
      cases selected : selectAt graph order fuel root (path ++ [index]) rank initial with
      | error error => simp only [selectChildren, Bind.bind, StateT.bind, selected, Except.bind] at success; cases success
      | ok pair =>
          rcases pair with ⟨⟨term, restricted, residual⟩, middle⟩
          have first := selection root (path ++ [index]) rank initial term restricted residual middle starts nonnegative
            (existsPath index (by simp)) selected
          have residualNonnegative := ((decoder_inverse_mutual graph order fuel).1 root (path ++ [index]) rank initial
            term restricted residual middle nonnegative selected).1
          have tailPaths : ∀ index ∈ rest, PathExists meaning restricted (path ++ [index]) := by
            intro next member whole accepted
            exact existsPath next (by simp [member]) whole (first.2.1 whole accepted)
          cases tailSelected : selectChildren graph order fuel restricted path residual rest middle with
          | error error =>
              simp only [selectChildren, Bind.bind, StateT.bind, selected, Except.bind, tailSelected] at success
              cases success
          | ok pair =>
              rcases pair with ⟨⟨terms, last, lastRank⟩, cache⟩
              have tail := remaining restricted path residual rest middle terms last lastRank cache first.1 residualNonnegative tailPaths tailSelected
              simp only [selectChildren, Bind.bind, StateT.bind, selected, Except.bind, tailSelected,
                Pure.pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at success
              rcases success with ⟨⟨rfl, rfl, rfl⟩, rfl⟩
              exact ⟨tail.1, fun whole member => first.2.1 whole (tail.2.1 whole member),
                fun whole member => .cons (first.2.2 whole (tail.2.1 whole member)) (tail.2.2 whole member)⟩

/-- The source decoder successively fixes exactly the selected subtree while retaining earlier restrictions. -/
theorem decoder_meaning_mutual [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph)
    (invariant : Counts Symbol → Prop)
    (countsSound : CountSound graph (fun node => (meaning.terms node).length) invariant) (fuel : Nat) :
    SelectionMeaning graph order meaning invariant fuel ∧ ConstructorMeaning graph order meaning invariant fuel ∧
      ChildrenMeaning graph order meaning invariant fuel := by
  induction fuel with
  | zero =>
      refine ⟨?_, ?_, ?_⟩
      · intro root path rank initial term final suffix after starts nonnegative existsPath success
        cases success
      · intro root path rank constructors initial term final suffix after distinct starts nonnegative success
        cases success
      · intro root path rank indices initial children final suffix after starts nonnegative existsPath success
        cases indices with
        | cons first rest => cases success
        | nil => cases success; exact ⟨starts, fun _ member => member, fun _ _ => .nil⟩
  | succ fuel ih =>
      exact ⟨selection_meaning_step graph order meaning invariant countsSound fuel ih.2.1,
        constructor_meaning_step graph order meaning invariant countsSound fuel ih.2.1 ih.2.2,
        children_meaning_step graph order meaning invariant fuel ih.1 ih.2.2⟩

/-- A nonempty distinct language whose every term is fixed has cardinality one. -/
theorem fixed_language_singleton (terms : List Value) (distinct : terms.Nodup)
    (nonempty : 0 < terms.length) (value : Value) (fixed : ∀ term ∈ terms, term = value) :
    terms = [value] := by
  have subset : terms ⊆ [value] := fun term member => by simpa only [List.mem_singleton] using fixed term member
  have bound := List.Nodup.length_le_of_subset distinct subset
  have one : terms.length = 1 := by simp only [List.length_singleton] at bound; omega
  obtain ⟨only, same⟩ := List.length_eq_one_iff.mp one
  have member : only ∈ terms := by simp [same]
  simpa only [fixed only member] using same

/-- Complete root selection leaves exactly the returned accepted term and residual zero. -/
theorem selected_root_exact [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph)
    (invariant : Counts Symbol → Prop)
    (countsSound : CountSound graph (fun node => (meaning.terms node).length) invariant)
    (fuel root : Nat) (rank : Int) (initial after : Counts Symbol) (term : Term Symbol) (final : Nat) (suffix : Int)
    (starts : invariant initial) (nonnegative : 0 ≤ rank) (bounded : rank < ((meaning.terms root).length : Int))
    (success : selectAt graph order fuel root [] rank initial = .ok ((term, final, suffix), after)) :
    term ∈ meaning.terms root ∧ meaning.terms final = [term] ∧ suffix = 0 ∧ invariant after := by
  have semantic := (decoder_meaning_mutual graph order meaning invariant countsSound fuel).1
    root [] rank initial term final suffix after starts nonnegative (fun whole _ => ⟨whole, rfl⟩) success
  have bounds := (decoder_bounds_mutual graph order (fun node => (meaning.terms node).length) invariant countsSound fuel).1
    root [] rank initial term final suffix after starts nonnegative bounded success
  have lower := ((decoder_inverse_mutual graph order fuel).1 root [] rank initial term final suffix after nonnegative success).1
  have positive : 0 < (meaning.terms final).length := by
    have upper := bounds.2
    dsimp only at upper
    omega
  have fixed : meaning.terms final = [term] := fixed_language_singleton (meaning.terms final) (meaning.distinct final)
    positive term (fun whole member => Option.some.inj (semantic.2.2 whole member))
  have emptySuffix : suffix = 0 := singleton_final_residual_zero graph order (fun node => (meaning.terms node).length)
    invariant countsSound fuel root [] rank initial after term final suffix starts nonnegative bounded success
    (by simp only [fixed, List.length_singleton])
  exact ⟨semantic.2.1 term (by simp only [fixed, List.mem_singleton]), fixed, emptySuffix, semantic.1⟩

/-- Every successful source decode is accepted and has exactly its original inverse rank. -/
theorem unrank_sound_and_inverse [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph)
    (invariant : Counts Symbol → Prop) (emptyCache : invariant {})
    (countsSound : CountSound graph (fun node => (meaning.terms node).length) invariant)
    (fuel root : Nat) (rank : Int) (term : Term Symbol)
    (success : unrank graph order fuel root rank = .ok term) :
    term ∈ meaning.terms root ∧ rankOf graph order fuel root term = .ok (some rank) := by
  cases counted : countNode graph fuel root {} with
  | error error => simp only [unrank, counted] at success; cases success
  | ok pair =>
      rcases pair with ⟨total, counts⟩
      have correct := countsSound fuel root {} total counts emptyCache counted
      simp only [unrank, counted, Bind.bind, Except.bind] at success
      split at success
      · cases success
      · rename_i inRange
        have nonnegative : 0 ≤ rank := by omega
        have countMeaning := correct.1
        dsimp only at countMeaning
        have bounded : rank < ((meaning.terms root).length : Int) := by omega
        cases selected : selectAt graph order fuel root [] rank counts with
        | error error => simp only [selected] at success; cases success
        | ok pair =>
            rcases pair with ⟨⟨chosen, final, suffix⟩, after⟩
            simp only [selected, Pure.pure, Except.pure, Except.ok.injEq] at success
            subst term
            have exactRoot := selected_root_exact graph order meaning invariant countsSound fuel root rank
              counts after chosen final suffix correct.2 nonnegative bounded selected
            have inverse := (decoder_inverse_mutual graph order fuel).1 root [] rank counts chosen final suffix after nonnegative selected
            refine ⟨exactRoot.1, ?_⟩
            simp only [rankOf, counted, Bind.bind, Except.bind, inverse.2 0, Pure.pure, Except.pure, Option.map_some,
              exactRoot.2.2.1, Int.zero_add, Int.sub_zero]

/-- Distinct successful source ranks cannot accidentally decode to the same accepted term. -/
theorem unrank_injective [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph)
    (invariant : Counts Symbol → Prop) (emptyCache : invariant {})
    (countsSound : CountSound graph (fun node => (meaning.terms node).length) invariant)
    (fuel root : Nat) (left right : Int) (term : Term Symbol)
    (first : unrank graph order fuel root left = .ok term)
    (second : unrank graph order fuel root right = .ok term) : left = right := by
  have leftRank := (unrank_sound_and_inverse graph order meaning invariant emptyCache countsSound fuel root left term first).2
  have rightRank := (unrank_sound_and_inverse graph order meaning invariant emptyCache countsSound fuel root right term second).2
  exact Option.some.inj (Except.ok.inj (leftRank.symm.trans rightRank))

/-- Totality states only that every in-range source decode returns. It makes no language claim. -/
def DecodeTotal [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (fuel root count : Nat) : Prop :=
  ∀ rank : Fin count, ∃ term, unrank graph order fuel root rank.val = .ok term

/-- A total source decoder gives every accepted term exactly one rank in the full finite range. -/
theorem source_rank_bijection [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph)
    (invariant : Counts Symbol → Prop) (emptyCache : invariant {})
    (countsSound : CountSound graph (fun node => (meaning.terms node).length) invariant)
    (fuel root : Nat) (total : DecodeTotal graph order fuel root (meaning.terms root).length)
    (term : Term Symbol) (accepted : term ∈ meaning.terms root) :
    ∃ rank : Fin (meaning.terms root).length,
      unrank graph order fuel root rank.val = .ok term ∧
      rankOf graph order fuel root term = .ok (some rank.val) ∧
      ∀ other : Fin (meaning.terms root).length,
        unrank graph order fuel root other.val = .ok term → other = rank := by
  classical
  let decoded := fun rank : Fin (meaning.terms root).length => Classical.choose (total rank)
  have decodes : ∀ rank, unrank graph order fuel root rank.val = .ok (decoded rank) :=
    fun rank => Classical.choose_spec (total rank)
  have injective : Function.Injective decoded := by
    intro left right same
    have rightResult : unrank graph order fuel root right.val = .ok (decoded left) := by
      simpa only [same] using decodes right
    have equal := unrank_injective graph order meaning invariant emptyCache countsSound fuel root left.val right.val
      (decoded left) (decodes left) rightResult
    apply Fin.ext
    omega
  have distinct : (List.ofFn decoded).Nodup := by
    apply List.nodup_iff_eq_of_getElem_eq.mpr
    intro left right leftBound rightBound same
    have outputs := injective (by simpa only [List.getElem_ofFn] using same)
    exact congrArg Fin.val outputs
  have subset : List.ofFn decoded ⊆ meaning.terms root := by
    intro output member
    obtain ⟨rank, same⟩ := List.mem_ofFn.mp member
    subst output
    exact (unrank_sound_and_inverse graph order meaning invariant emptyCache countsSound fuel root rank.val
      (decoded rank) (decodes rank)).1
  have present : term ∈ List.ofFn decoded := by
    apply Classical.byContradiction
    intro absent
    have extendedDistinct : (term :: List.ofFn decoded).Nodup := List.nodup_cons.mpr ⟨absent, distinct⟩
    have extendedSubset : term :: List.ofFn decoded ⊆ meaning.terms root := by
      intro output member
      rcases List.mem_cons.mp member with rfl | member
      · exact accepted
      · exact subset member
    have tooMany := List.Nodup.length_le_of_subset extendedDistinct extendedSubset
    simp only [List.length_cons, List.length_ofFn] at tooMany
    omega
  obtain ⟨rank, same⟩ := List.mem_ofFn.mp present
  have result : unrank graph order fuel root rank.val = .ok term := by simpa only [same] using decodes rank
  refine ⟨rank, result,
    (unrank_sound_and_inverse graph order meaning invariant emptyCache countsSound fuel root rank.val term result).2, ?_⟩
  intro other otherResult
  have equal := unrank_injective graph order meaning invariant emptyCache countsSound fuel root other.val rank.val term otherResult result
  apply Fin.ext
  omega

end MicroCFTA.SymbolicDriver
