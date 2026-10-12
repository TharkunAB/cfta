import MicroCFTA.SymbolicCanonicalOrder

/-!
# Successful inverse ranking cannot admit an invalid term

The actual inverse progressively restricts constructor and child positions.
Every successful branch retains a nonempty final language and fixes the
requested subtree. Root projection is exact, including for an empty language.
-/
namespace MicroCFTA.SymbolicDriver
open Language

/-- A successful subtree rank retains at least one complete matching root term. -/
def RankingMeaning [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph)
    (invariant : Counts Symbol → Prop) (fuel : Nat) : Prop :=
  ∀ root path term before initial final rank after, invariant initial → meaning.terms root ≠ [] →
    PathExists meaning root path → rankAt graph order fuel root path term before initial = .ok (some (final, rank), after) →
    invariant after ∧ GraphSubset meaning final root ∧ meaning.terms final ≠ [] ∧
      ∀ whole ∈ meaning.terms final, whole.atPath path = some term

/-- A matched nonzero constructor block retains a complete term after all child checks. -/
def RankingConstructorMeaning [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph)
    (invariant : Counts Symbol → Prop) (fuel : Nat) : Prop :=
  ∀ root path wanted children before available initial final rank after,
    children.length = wanted.2 → invariant initial →
    rankConstructor graph order fuel root path wanted children before available initial = .ok (some (final, rank), after) →
    invariant after ∧ GraphSubset meaning final root ∧ meaning.terms final ≠ [] ∧
      ∀ whole ∈ meaning.terms final, whole.atPath path = some (.node wanted.1 children)

/-- Later inverse child checks retain every previously checked subtree. -/
def RankingChildrenMeaning [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph)
    (invariant : Counts Symbol → Prop) (fuel : Nat) : Prop :=
  ∀ root path before children initial final rank after, invariant initial → meaning.terms root ≠ [] →
    (∀ child ∈ children, PathExists meaning root (path ++ [child.2])) →
    rankChildren graph order fuel root path before children initial = .ok (some (final, rank), after) →
    invariant after ∧ GraphSubset meaning final root ∧ meaning.terms final ≠ [] ∧
      ∀ whole ∈ meaning.terms final, ∀ child ∈ children, whole.atPath (path ++ [child.2]) = some child.1

/-- Every successful singleton rank compares against the actual unique projected term. -/
theorem ranking_meaning_step [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph)
    (invariant : Counts Symbol → Prop)
    (sound : CountSound graph (fun node => (meaning.terms node).length) invariant) (fuel : Nat)
    (constructors : RankingConstructorMeaning graph order meaning invariant fuel) :
    RankingMeaning graph order meaning invariant (fuel + 1) := by
  intro root path term before initial final rank after starts nonempty existsPath success
  cases term with
  | node symbol children =>
    cases counted : countNode graph fuel (graph.project path root) initial with
    | error error => simp only [rankAt, Bind.bind, StateT.bind, counted, Except.bind] at success; cases success
    | ok pair =>
      rcases pair with ⟨count, middle⟩
      have correct := sound fuel (graph.project path root) initial count middle starts counted
      simp only [rankAt, Bind.bind, StateT.bind, counted, Except.bind] at success
      by_cases singleton : count = 1
      · simp only [singleton, ↓reduceIte] at success
        have countMeaning := correct.1
        dsimp only at countMeaning
        have length : (meaning.terms (graph.project path root)).length = 1 := by omega
        obtain ⟨uniqueTerm, uniqueLanguage⟩ := List.length_eq_one_iff.mp length
        change Except.bind (isolated (selectUnique graph order fuel (graph.project path root) []) middle)
          (fun (chosen, cache) => .ok ((if termEq chosen (.node symbol children) then some (root, before) else none), cache)) =
            .ok (some (final, rank), after) at success
        cases unique : isolated (selectUnique graph order fuel (graph.project path root) []) middle with
        | error error => simp only [unique, Except.bind] at success; cases success
        | ok pair =>
          rcases pair with ⟨chosen, cache⟩
          obtain ⟨inner, innerRun, restored⟩ := isolated_inner _ middle cache chosen unique
          have decoded := (singleton_decoder_meaning graph order meaning invariant sound fuel).1
            (graph.project path root) [] middle chosen inner uniqueTerm uniqueLanguage correct.2 innerRun
          have chosenSame : uniqueTerm = chosen := Option.some.inj decoded.1
          simp only [unique, Except.bind] at success
          by_cases equal : termEq chosen (.node symbol children) = true
          · simp only [equal, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at success
            rcases success with ⟨⟨rfl, rfl⟩, rfl⟩
            have identical := (termEq_correct chosen (.node symbol children)).mp equal
            refine ⟨restored ▸ correct.2, fun _ member => member, nonempty, ?_⟩
            intro whole member
            obtain ⟨part, located⟩ := existsPath whole member
            have projected := meaning.project path root whole part member located
            have same : part = .node symbol children := by
              simpa only [uniqueLanguage, List.mem_singleton, chosenSame, identical] using projected
            simpa only [same] using located
          · simp only [equal, Except.ok.injEq, Prod.mk.injEq] at success
            cases success.1
      · simp only [singleton, ↓reduceIte] at success
        by_cases present : (symbol, children.length) ∈ constructorsAt graph order path root
        · simp only [present, ↓reduceIte] at success
          exact constructors root path (symbol, children.length) children before
            (constructorsAt graph order path root) middle final rank after rfl correct.2 success
        · simp only [present, ↓reduceIte, Pure.pure, StateT.pure, Except.pure,
            Except.ok.injEq, Prod.mk.injEq] at success
          cases success.1

/-- Checking all indexed children determines the entire requested tuple. -/
theorem checked_children_determine (whole : Term Symbol) (path : List Nat) (symbol : Symbol)
    (original requested : List (Term Symbol)) (located : whole.atPath path = some (.node symbol original))
    (length : original.length = requested.length)
    (checked : ∀ child ∈ requested.zipIdx, whole.atPath (path ++ [child.2]) = some child.1) :
    original = requested := by
  apply List.ext_getElem length
  intro index originalBound requestedBound
  have atRequested := checked (requested[index], index)
    (List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem requestedBound))
  have atOriginal : whole.atPath (path ++ [index]) = some original[index] := by
    simp only [atPath_append, located, Option.bind_some, Term.atPath,
      List.getElem?_eq_getElem originalBound, Option.bind_some]
  exact Option.some.inj (atOriginal.symm.trans atRequested)

/-- Constructor rejection is explicit; every accepted block has a nonempty final language. -/
theorem ranking_constructor_step [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph)
    (invariant : Counts Symbol → Prop)
    (sound : CountSound graph (fun node => (meaning.terms node).length) invariant) (fuel : Nat)
    (remaining : RankingConstructorMeaning graph order meaning invariant fuel)
    (childrenMeaning : RankingChildrenMeaning graph order meaning invariant fuel) :
    RankingConstructorMeaning graph order meaning invariant (fuel + 1) := by
  intro root path wanted children before available initial final rank after arity starts success
  cases available with
  | nil => cases success
  | cons constructor rest =>
    cases counted : countNode graph fuel (graph.condition path constructor root) initial with
    | error error => simp only [rankConstructor, Bind.bind, StateT.bind, counted, Except.bind] at success; cases success
    | ok pair =>
      rcases pair with ⟨count, middle⟩
      have correct := sound fuel (graph.condition path constructor root) initial count middle starts counted
      simp only [rankConstructor, Bind.bind, StateT.bind, counted, Except.bind] at success
      by_cases matching : constructor = wanted
      · subst constructor
        simp only [↓reduceIte] at success
        by_cases zero : count = 0
        · simp only [zero, ↓reduceIte, Pure.pure, StateT.pure, Except.pure,
            Except.ok.injEq, Prod.mk.injEq] at success
          cases success.1
        · simp only [zero, ↓reduceIte] at success
          have nonempty : meaning.terms (graph.condition path wanted root) ≠ [] := by
            intro empty
            have countedLength := correct.1
            simp only [empty, List.length_nil, Int.natCast_zero] at countedLength
            exact zero countedLength
          have childPaths : ∀ child ∈ children.zipIdx,
              PathExists meaning (graph.condition path wanted root) (path ++ [child.2]) := by
            intro child present whole accepted
            have requested := List.mem_zipIdx_iff_getElem?.mp present
            have indexBound : child.2 < children.length := by
              by_cases inside : child.2 < children.length
              · exact inside
              · have absent := List.getElem?_eq_none (l := children) (by omega : children.length ≤ child.2)
                rw [absent] at requested
                cases requested
            obtain ⟨_, originals, located, length⟩ := (meaning.condition path wanted.1 wanted.2 root whole).mp accepted
            have bound : child.2 < originals.length := by omega
            exact ⟨originals[child.2], by simp only [atPath_append, located, Option.bind_some,
              Term.atPath, List.getElem?_eq_getElem bound, Option.bind_some]⟩
          have result := childrenMeaning (graph.condition path wanted root) path before children.zipIdx
            middle final rank after correct.2 nonempty childPaths success
          refine ⟨result.1, ?_, result.2.2.1, ?_⟩
          · intro whole accepted
            exact ((meaning.condition path wanted.1 wanted.2 root whole).mp (result.2.1 whole accepted)).1
          · intro whole accepted
            obtain ⟨_, originals, located, length⟩ :=
              (meaning.condition path wanted.1 wanted.2 root whole).mp (result.2.1 whole accepted)
            have same := checked_children_determine whole path wanted.1 originals children located (length.trans arity.symm)
              (result.2.2.2 whole accepted)
            simpa only [same] using located
      · simp only [matching, ↓reduceIte] at success
        exact remaining root path wanted children (before + count) rest middle final rank after arity correct.2 success

/-- Successful sequential child checks preserve nonemptiness and every earlier checked subtree. -/
theorem ranking_children_step [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph)
    (invariant : Counts Symbol → Prop) (fuel : Nat)
    (selection : RankingMeaning graph order meaning invariant fuel)
    (remaining : RankingChildrenMeaning graph order meaning invariant fuel) :
    RankingChildrenMeaning graph order meaning invariant (fuel + 1) := by
  intro root path before children initial final rank after starts nonempty existsPath success
  cases children with
  | nil => cases success; exact ⟨starts, fun _ member => member, nonempty, fun _ _ child member => by cases member⟩
  | cons child rest =>
    rcases child with ⟨term, index⟩
    cases first : rankAt graph order fuel root (path ++ [index]) term before initial with
    | error error => simp only [rankChildren, Bind.bind, StateT.bind, first, Except.bind] at success; cases success
    | ok pair =>
      rcases pair with ⟨result, middle⟩
      cases result with
      | none => simp only [rankChildren, Bind.bind, StateT.bind, first, Except.bind] at success; cases success
      | some pair =>
        rcases pair with ⟨restricted, next⟩
        have firstMeaning := selection root (path ++ [index]) term before initial restricted next middle
          starts nonempty (existsPath (term, index) (by simp)) first
        simp only [rankChildren, Bind.bind, StateT.bind, first, Except.bind] at success
        have tailPaths : ∀ child ∈ rest, PathExists meaning restricted (path ++ [child.2]) := by
          intro child member whole accepted
          exact existsPath child (by simp [member]) whole (firstMeaning.2.1 whole accepted)
        have tailMeaning := remaining restricted path next rest middle final rank after firstMeaning.1
          firstMeaning.2.2.1 tailPaths success
        refine ⟨tailMeaning.1, fun whole accepted => firstMeaning.2.1 whole (tailMeaning.2.1 whole accepted),
          tailMeaning.2.2.1, ?_⟩
        intro whole accepted child member
        rcases List.mem_cons.mp member with rfl | member
        · exact firstMeaning.2.2.2 whole (tailMeaning.2.1 whole accepted)
        · exact tailMeaning.2.2.2 whole accepted child member

/-- The three actual inverse workers preserve accepted matching roots on every successful call. -/
theorem ranking_meaning_mutual [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph)
    (invariant : Counts Symbol → Prop)
    (sound : CountSound graph (fun node => (meaning.terms node).length) invariant) (fuel : Nat) :
    RankingMeaning graph order meaning invariant fuel ∧ RankingConstructorMeaning graph order meaning invariant fuel ∧
      RankingChildrenMeaning graph order meaning invariant fuel := by
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro root path term before initial final rank after starts nonempty existsPath success
      cases success
    · intro root path wanted children before available initial final rank after arity starts success
      cases success
    · intro root path before children initial final rank after starts nonempty existsPath success
      cases children with
      | nil => cases success; exact ⟨starts, fun _ member => member, nonempty, fun _ _ child member => by cases member⟩
      | cons first rest => cases success
  | succ fuel ih =>
    exact ⟨ranking_meaning_step graph order meaning invariant sound fuel ih.2.1,
      ranking_constructor_step graph order meaning invariant sound fuel ih.2.1 ih.2.2,
      ranking_children_step graph order meaning invariant fuel ih.1 ih.2.2⟩

/-- Unlike deeper conservative projection, projection at the root preserves exact membership. -/
def RootProjectionExact (graph : Graph Symbol) (meaning : FiniteMeaning graph) : Prop :=
  ∀ root term, term ∈ meaning.terms (graph.project [] root) ↔ term ∈ meaning.terms root

/-- A successful inverse call at the complete root cannot bypass an empty language. -/
theorem rankAt_root_nonempty [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph)
    (invariant : Counts Symbol → Prop)
    (sound : CountSound graph (fun node => (meaning.terms node).length) invariant)
    (rootExact : RootProjectionExact graph meaning) (fuel root : Nat) (term : Term Symbol)
    (before : Int) (initial : Counts Symbol) (final : Nat) (rank : Int) (after : Counts Symbol)
    (starts : invariant initial)
    (success : rankAt graph order fuel root [] term before initial = .ok (some (final, rank), after)) :
    meaning.terms root ≠ [] := by
  cases fuel with
  | zero => cases success
  | succ fuel =>
    cases term with
    | node symbol children =>
      cases counted : countNode graph fuel (graph.project [] root) initial with
      | error error => simp only [rankAt, Bind.bind, StateT.bind, counted, Except.bind] at success; cases success
      | ok pair =>
        rcases pair with ⟨count, middle⟩
        have correct := sound fuel (graph.project [] root) initial count middle starts counted
        by_cases singleton : count = 1
        · have countMeaning := correct.1
          dsimp only at countMeaning
          have nonempty : meaning.terms (graph.project [] root) ≠ [] := by
            intro empty
            simp only [empty, List.length_nil, Int.natCast_zero] at countMeaning
            omega
          obtain ⟨whole, accepted⟩ := List.exists_mem_of_ne_nil _ nonempty
          have accepted := (rootExact root whole).mp accepted
          intro empty
          simp [empty] at accepted
        · simp only [rankAt, Bind.bind, StateT.bind, counted, Except.bind, singleton, ↓reduceIte] at success
          by_cases present : (symbol, children.length) ∈ constructorsAt graph order [] root
          · simp only [present, ↓reduceIte] at success
            have result := (ranking_meaning_mutual graph order meaning invariant sound fuel).2.1
              root [] (symbol, children.length) children before (constructorsAt graph order [] root)
              middle final rank after rfl correct.2 success
            obtain ⟨whole, accepted⟩ := List.exists_mem_of_ne_nil _ result.2.2.1
            have accepted := result.2.1 whole accepted
            intro empty
            simp [empty] at accepted
          · simp only [present, ↓reduceIte, Pure.pure, StateT.pure, Except.pure,
              Except.ok.injEq, Prod.mk.injEq] at success
            cases success.1

/-- The actual public inverse returns a rank only for an accepted term. -/
theorem rankOf_sound [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph)
    (invariant : Counts Symbol → Prop) (empty : invariant {})
    (sound : CountSound graph (fun node => (meaning.terms node).length) invariant)
    (rootExact : RootProjectionExact graph meaning) (fuel root : Nat) (term : Term Symbol) (rank : Int)
    (success : rankOf graph order fuel root term = .ok (some rank)) : term ∈ meaning.terms root := by
  cases counted : countNode graph fuel root {} with
  | error error => simp only [rankOf, counted, Bind.bind, Except.bind] at success; cases success
  | ok pair =>
    rcases pair with ⟨count, middle⟩
    have correct := sound fuel root {} count middle empty counted
    cases ranked : rankAt graph order fuel root [] term 0 middle with
    | error error => simp only [rankOf, counted, ranked, Bind.bind, Except.bind] at success; cases success
    | ok pair =>
      rcases pair with ⟨result, after⟩
      cases result with
      | none => simp only [rankOf, counted, ranked, Bind.bind, Except.bind] at success; cases success
      | some pair =>
        rcases pair with ⟨final, value⟩
        have nonempty := rankAt_root_nonempty graph order meaning invariant sound rootExact fuel root term
          0 middle final value after correct.2 ranked
        have result := (ranking_meaning_mutual graph order meaning invariant sound fuel).1
          root [] term 0 middle final value after correct.2 nonempty (fun whole _ => ⟨whole, rfl⟩) ranked
        obtain ⟨whole, accepted⟩ := List.exists_mem_of_ne_nil _ result.2.2.1
        have same : whole = term := Option.some.inj (result.2.2.2 whole accepted)
        simpa only [same] using result.2.1 whole accepted

/-- Any completed inverse execution on a nonmember returns the explicit rejection value. -/
theorem rankOf_rejects_nonmember [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph)
    (invariant : Counts Symbol → Prop) (empty : invariant {})
    (sound : CountSound graph (fun node => (meaning.terms node).length) invariant)
    (rootExact : RootProjectionExact graph meaning) (fuel root : Nat) (term : Term Symbol)
    (absent : term ∉ meaning.terms root) (result : Option Int)
    (success : rankOf graph order fuel root term = .ok result) : result = none := by
  cases result with
  | none => rfl
  | some rank => exact False.elim (absent (rankOf_sound graph order meaning invariant empty sound rootExact fuel root term rank success))

/-- Every returned inverse rank is in range and decodes back to the supplied term. -/
theorem rankOf_checked_inverse [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph)
    (invariant : Counts Symbol → Prop) (empty : invariant {})
    (sound : CountSound graph (fun node => (meaning.terms node).length) invariant)
    (rootExact : RootProjectionExact graph meaning) (fuel root : Nat)
    (total : DecodeTotal graph order fuel root (meaning.terms root).length) (term : Term Symbol) (rank : Int)
    (success : rankOf graph order fuel root term = .ok (some rank)) :
    0 ≤ rank ∧ rank < ((meaning.terms root).length : Int) ∧ unrank graph order fuel root rank = .ok term := by
  have accepted := rankOf_sound graph order meaning invariant empty sound rootExact fuel root term rank success
  obtain ⟨index, decoded, ranked, _⟩ := source_rank_bijection graph order meaning invariant empty sound fuel root total term accepted
  have same : (index.val : Int) = rank := Option.some.inj (Except.ok.inj (ranked.symm.trans success))
  rw [← same]
  exact ⟨by omega, by have := index.isLt; omega, decoded⟩

/-- The concrete cleaned projection worker establishes the exact-root condition. -/
theorem closed_rootProjection [DecidableEq Symbol] (graph : Graph Symbol)
    (guard : Edge Symbol → Term Symbol → Bool) (view : SymbolicGraphView.ClosedOperationRows graph guard)
    (budget : SourceBudget graph) : RootProjectionExact graph (SymbolicGraphView.closedMeaning graph guard view budget) := by
  intro root term
  simp only [SymbolicGraphView.closedMeaning, SymbolicGraphView.finiteTerms_exact]
  exact (SymbolicGraphView.normalizedRows_exact _ _ _ (view.projection [] root) none term).trans
    ((SymbolicGraphView.union_root_exact _ _ term).trans (SymbolicGraph.project_root_exact _ root term))

end MicroCFTA.SymbolicDriver
