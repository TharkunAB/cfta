import MicroCFTA.SourceTypingRules
import MicroCFTA.SourceTypingFinite

/-!
# Finite-term acceptance of completed typing rows

The independent judgment checks typed subterms and matching environment
positions. Fixed encoded fields use an explicit independent validity law.
Actual unrestricted source rows correspond to the permissive fixed-field
judgment. Validation must establish a stronger fixed-value law before the
advertised closed typing domain can be concluded.
-/
namespace MicroCFTA.SourceTypingRules
open Language
variable {Ty Symbol : Type}

/-- A selected alternative comes from an ordinary rule or an exact environment position. -/
theorem selected_cases [DecidableEq Ty] (rules : List (Rule Ty Symbol)) (env : List Ty) (typ : Ty) (remaining : Int)
    (label : Symbol) (children : List (Child Ty Symbol))
    (member : (label, children) ∈ selected rules env typ remaining) :
    Rule.ordinary label children typ ∈ rules ∨
      ∃ schema index, Rule.variable label schema ∈ rules ∧ env[index]? = some typ ∧ children = schema index typ := by
  rcases List.mem_append.mp member with ordinary | varCase
  · obtain ⟨rule, present, found⟩ := List.mem_flatMap.mp ordinary
    cases rule with
    | ordinary name fields result =>
        dsimp only at found
        split at found
        · rename_i kept
          have same : (label, children) = (name, fields) := List.mem_singleton.mp found
          rcases Prod.mk.inj same with ⟨rfl, rfl⟩
          cases kept.1
          exact Or.inl present
        · cases found
    | «variable» => cases found
  · obtain ⟨rule, present, found⟩ := List.mem_flatMap.mp varCase
    cases rule with
    | ordinary => cases found
    | «variable» name schema =>
        obtain ⟨⟨actual, index⟩, position, found⟩ := List.mem_flatMap.mp found
        dsimp only at found
        split at found
        · rename_i kept
          have same : (label, children) = (name, schema index actual) := List.mem_singleton.mp found
          rcases Prod.mk.inj same with ⟨rfl, rfl⟩
          have lookup := List.mem_zipIdx_iff_getElem?.mp position
          cases kept.1
          exact Or.inr ⟨schema, index, present, lookup, rfl⟩
        · cases found

/-- An ordinary rule with permitted fields occurs in the first source alternative group. -/
theorem selected_ordinary [DecidableEq Ty] (rules : List (Rule Ty Symbol)) (env : List Ty) (typ : Ty) (remaining : Int)
    (label : Symbol) (children : List (Child Ty Symbol))
    (member : Rule.ordinary label children typ ∈ rules) (permitted : nests remaining children = true) :
    (label, children) ∈ selected rules env typ remaining := by
  apply List.mem_append.mpr
  exact Or.inl (List.mem_flatMap.mpr ⟨.ordinary label children typ, member, by simp [permitted]⟩)

/-- A variable rule uses the actual matching de Bruijn position, including repeated types. -/
theorem selected_variable [DecidableEq Ty] (rules : List (Rule Ty Symbol)) (env : List Ty) (typ : Ty) (remaining : Int)
    (label : Symbol) (schema : Nat → Ty → List (Child Ty Symbol)) (index : Nat)
    (member : Rule.variable label schema ∈ rules) (position : env[index]? = some typ)
    (permitted : nests remaining (schema index typ) = true) :
    (label, schema index typ) ∈ selected rules env typ remaining := by
  apply List.mem_append.mpr
  refine Or.inr (List.mem_flatMap.mpr ⟨.variable label schema, member, ?_⟩)
  exact List.mem_flatMap.mpr ⟨(typ, index), List.mem_zipIdx_iff_getElem?.mpr position, by simp [permitted]⟩

/-- Independent field derivations imply the compiler's local nesting test. -/
theorem fields_nests {fixedAllowed : Term Symbol → Prop} {rules : List (Rule Ty Symbol)}
    {env : List Ty} {remaining : Int} {children : List (Child Ty Symbol)} {terms : List (Term Symbol)}
    (actual : FieldsTyped fixedAllowed rules env remaining children terms) : nests remaining children = true := by
  induction children generalizing terms with
  | nil => simp [nests]
  | cons child children ih =>
      cases actual with
      | cons first rest =>
          cases first with
          | subterm positive _ => simp [nests, positive]
          | value => simpa only [nests, List.any_cons, Child.isSubterm, Bool.false_or] using ih rest

/-- A selected Subterm field has a positive bound before its one-level decrease. -/
theorem nests_subterm (remaining : Int) (children : List (Child Ty Symbol)) (binds : List Ty) (typ : Ty)
    (permitted : nests remaining children = true) (member : Child.subterm binds typ ∈ children) : 0 < remaining := by
  by_cases positive : 0 < remaining
  · exact positive
  · have found : children.any Child.isSubterm = true := List.any_eq_true.mpr ⟨.subterm binds typ, member, rfl⟩
    simp [nests, positive, found] at permitted

/-- A nonpositive bound excludes every Subterm from selected alternatives. -/
theorem selected_nonpositive [DecidableEq Ty] (rules : List (Rule Ty Symbol)) (env : List Ty) (typ : Ty) (remaining : Int)
    (nonpositive : remaining ≤ 0) (alternative : Symbol × List (Child Ty Symbol))
    (member : alternative ∈ selected rules env typ remaining) :
    ∀ binds childType, Child.subterm binds childType ∉ alternative.2 := by
  intro binds childType included
  have positive := nests_subterm remaining alternative.2 binds childType (selected_nests rules env typ remaining alternative member) included
  omega

/-- The independent fixed-value law applies to every selected fixed field. -/
theorem selected_fixed [DecidableEq Ty] (fixedAllowed : Term Symbol → Prop) (rules : List (Rule Ty Symbol))
    (lawful : LawfulFixed fixedAllowed rules) (env : List Ty) (typ : Ty) (remaining : Int)
    (label : Symbol) (children : List (Child Ty Symbol))
    (member : (label, children) ∈ selected rules env typ remaining) :
    ∀ term, Child.value term ∈ children → fixedAllowed term := by
  rcases selected_cases rules env typ remaining label children member with ordinary | ⟨schema, index, rule, _, rfl⟩
  · exact lawful.1 label children typ ordinary
  · exact lawful.2 label schema rule index typ

/-- Read the independent judgment at each source automaton state. -/
def Denotes (fixedAllowed : Term Symbol → Prop) (rules : List (Rule Ty Symbol)) (roots : List Ty) (bound : Int) :
    Goal Ty Symbol → Term Symbol → Prop
  | .root, term => ∃ typ ∈ roots, Typed fixedAllowed rules [] typ bound term
  | .typed env typ remaining, term => Typed fixedAllowed rules env typ remaining term
  | .fixed original, term => term = original

private theorem fields_iff (fixedAllowed : Term Symbol → Prop) (rules : List (Rule Ty Symbol))
    (roots : List Ty) (bound : Int) (relation : Goal Ty Symbol → Term Symbol → Prop)
    (env : List Ty) (remaining : Int) (children : List (Child Ty Symbol)) (terms : List (Term Symbol))
    (ih : ∀ term ∈ terms, ∀ goal, relation goal term ↔ Denotes fixedAllowed rules roots bound goal term)
    (positive : ∀ binds typ, Child.subterm binds typ ∈ children → 0 < remaining)
    (allowed : ∀ term, Child.value term ∈ children → fixedAllowed term) :
    All₂ relation (children.map (childGoal env remaining)) terms ↔
      FieldsTyped fixedAllowed rules env remaining children terms := by
  induction children generalizing terms with
  | nil =>
      constructor <;> intro actual <;> cases actual <;> exact .nil
  | cons child children induction =>
      constructor
      · intro actual
        cases actual with
        | cons first rest =>
            refine .cons ?_ ((induction _ (fun term member => ih term (List.mem_cons_of_mem _ member))
              (fun binds typ member => positive binds typ (List.mem_cons_of_mem _ member))
              (fun term member => allowed term (List.mem_cons_of_mem _ member))).mp rest)
            cases child with
            | subterm binds typ =>
                exact .subterm (positive binds typ List.mem_cons_self)
                  ((ih _ List.mem_cons_self _).mp first)
            | value original =>
                have same : _ = original := (ih _ List.mem_cons_self _).mp first
                subst original
                exact .value (allowed _ List.mem_cons_self)
      · intro actual
        cases actual with
        | cons first rest =>
            refine .cons ?_ ((induction _ (fun term member => ih term (List.mem_cons_of_mem _ member))
              (fun binds typ member => positive binds typ (List.mem_cons_of_mem _ member))
              (fun term member => allowed term (List.mem_cons_of_mem _ member))).mpr rest)
            cases first with
            | subterm _ typed => exact (ih _ List.mem_cons_self _).mpr typed
            | value _ => exact (ih _ List.mem_cons_self _).mpr rfl

private theorem typed_step [DecidableEq Ty] (fixedAllowed : Term Symbol → Prop)
    (rules : List (Rule Ty Symbol)) (lawful : LawfulFixed fixedAllowed rules) (roots : List Ty) (bound : Int)
    (label : Symbol) (terms : List (Term Symbol))
    (ih : ∀ term ∈ terms, ∀ goal,
      Accepts (row roots rules bound) goal term ↔ Denotes fixedAllowed rules roots bound goal term)
    (env : List Ty) (typ : Ty) (remaining : Int) :
    Accepts (row roots rules bound) (.typed env typ remaining) (.node label terms) ↔
      Typed fixedAllowed rules env typ remaining (.node label terms) := by
  constructor
  · intro actual
    obtain ⟨edge, member, same, accepted, _⟩ := (accepts_node_iff _ _ _ _).mp actual
    obtain ⟨⟨name, children⟩, selected, rfl⟩ := List.mem_map.mp member
    dsimp only at same accepted
    subst name
    have fields := (fields_iff fixedAllowed rules roots bound _ env remaining children terms ih
      (fun binds childType member => nests_subterm remaining children binds childType
        (selected_nests rules env typ remaining (label, children) selected) member)
      (selected_fixed fixedAllowed rules lawful env typ remaining label children selected)).mp accepted
    rcases selected_cases rules env typ remaining label children selected with ordinary | ⟨schema, index, rule, position, rfl⟩
    · exact .ordinary ordinary fields
    · exact .variable rule position fields
  · intro actual
    have build : ∀ children, (label, children) ∈ selected rules env typ remaining →
        FieldsTyped fixedAllowed rules env remaining children terms →
        Accepts (row roots rules bound) (.typed env typ remaining) (.node label terms) := by
      intro children selected fields
      refine (accepts_node_iff _ _ _ _).mpr ⟨⟨label, children.map (childGoal env remaining), fun _ => true⟩,
        List.mem_map.mpr ⟨(label, children), selected, rfl⟩, rfl, ?_, rfl⟩
      exact (fields_iff fixedAllowed rules roots bound _ env remaining children terms ih
        (fun binds childType member => nests_subterm remaining children binds childType
          (selected_nests rules env typ remaining (label, children) selected) member)
        (selected_fixed fixedAllowed rules lawful env typ remaining label children selected)).mpr fields
    cases actual with
    | ordinary member fields =>
        exact build _ (selected_ordinary rules env typ remaining label _ member (fields_nests fields)) fields
    | «variable» member position fields =>
        exact build _ (selected_variable rules env typ remaining label _ _ member position (fields_nests fields)) fields

private theorem fixed_children_iff (fixedAllowed : Term Symbol → Prop) (rules : List (Rule Ty Symbol))
    (roots : List Ty) (bound : Int) (relation : Goal Ty Symbol → Term Symbol → Prop)
    (originals terms : List (Term Symbol))
    (ih : ∀ term ∈ terms, ∀ goal, relation goal term ↔ Denotes fixedAllowed rules roots bound goal term) :
    All₂ relation (originals.map Goal.fixed) terms ↔ terms = originals := by
  induction originals generalizing terms with
  | nil =>
      constructor
      · intro actual
        cases actual
        rfl
      · rintro rfl
        exact .nil
  | cons original originals induction =>
      constructor
      · intro actual
        cases actual with
        | cons first rest =>
            have head : _ = original := (ih _ List.mem_cons_self _).mp first
            have tail := (induction _ (fun term member => ih term (List.mem_cons_of_mem _ member))).mp rest
            cases head
            cases tail
            rfl
      · rintro rfl
        exact .cons ((ih _ List.mem_cons_self _).mpr rfl)
          ((induction _ (fun term member => ih term (List.mem_cons_of_mem _ member))).mpr rfl)

/-- Completed source rows accept exactly the independent bounded derivations under the fixed-field law. -/
theorem accepts_denotes [DecidableEq Ty] (fixedAllowed : Term Symbol → Prop)
    (rules : List (Rule Ty Symbol)) (lawful : LawfulFixed fixedAllowed rules) (roots : List Ty) (bound : Int)
    (term : Term Symbol) (goal : Goal Ty Symbol) :
    Accepts (row roots rules bound) goal term ↔ Denotes fixedAllowed rules roots bound goal term := by
  have result := Term.rec
    (motive_1 := fun term => ∀ goal, Accepts (row roots rules bound) goal term ↔
      Denotes fixedAllowed rules roots bound goal term)
    (motive_2 := fun terms => ∀ term ∈ terms, ∀ goal, Accepts (row roots rules bound) goal term ↔
      Denotes fixedAllowed rules roots bound goal term)
    (fun label terms ih goal => by
      cases goal with
      | typed env typ remaining => exact typed_step fixedAllowed rules lawful roots bound label terms ih env typ remaining
      | root =>
          constructor
          · intro actual
            obtain ⟨edge, member, same, accepted, guard⟩ := (accepts_node_iff _ _ _ _).mp actual
            obtain ⟨typ, present, selected⟩ := List.mem_flatMap.mp member
            have typed : Accepts (row roots rules bound) (.typed [] typ bound) (.node label terms) :=
              (accepts_node_iff _ _ _ _).mpr ⟨edge, selected, same, accepted, guard⟩
            exact ⟨typ, List.mem_eraseDups.mp present,
              (typed_step fixedAllowed rules lawful roots bound label terms ih [] typ bound).mp typed⟩
          · rintro ⟨typ, present, typed⟩
            obtain ⟨edge, selected, same, accepted, guard⟩ := (accepts_node_iff _ _ _ _).mp
              ((typed_step fixedAllowed rules lawful roots bound label terms ih [] typ bound).mpr typed)
            exact (accepts_node_iff _ _ _ _).mpr ⟨edge,
              List.mem_flatMap.mpr ⟨typ, List.mem_eraseDups.mpr present, selected⟩, same, accepted, guard⟩
      | fixed original =>
          cases original with
          | node name originals =>
              constructor
              · intro actual
                obtain ⟨edge, member, same, accepted, _⟩ := (accepts_node_iff _ _ _ _).mp actual
                have edgeSame := List.mem_singleton.mp member
                subst edge
                have children := (fixed_children_iff fixedAllowed rules roots bound _ originals terms ih).mp accepted
                cases same
                cases children
                rfl
              · intro same
                have parts := Term.node.inj same
                refine (accepts_node_iff _ _ _ _).mpr ⟨⟨name, originals.map Goal.fixed, fun _ => true⟩,
                  List.mem_singleton_self _, parts.1.symm, ?_, rfl⟩
                exact (fixed_children_iff fixedAllowed rules roots bound _ originals terms ih).mpr parts.2)
    (by intro term member; cases member)
    (fun head tail first rest term member => by
      rcases List.mem_cons.mp member with same | later
      · subst term
        exact first
      · exact rest term later)
    term
  exact result goal

/-- Actual fixed rows require no typing law when the independent fixed domain is unrestricted. -/
theorem lawful_permissive (rules : List (Rule Ty Symbol)) : LawfulFixed (fun _ => True) rules :=
  ⟨fun _ _ _ _ _ _ => True.intro, fun _ _ _ _ _ _ _ => True.intro⟩

/-- The permissive judgment describes resolved source rows without a fixed-value validation assumption. -/
theorem accepts_permissive [DecidableEq Ty] (rules : List (Rule Ty Symbol)) (roots : List Ty) (bound : Int)
    (term : Term Symbol) (goal : Goal Ty Symbol) :
    Accepts (row roots rules bound) goal term ↔ Denotes (fun _ => True) rules roots bound goal term :=
  accepts_denotes _ rules (lawful_permissive rules) roots bound term goal

/-- A typed goal accepts exactly independent derivations with its original environment and signed budget. -/
theorem accepts_typed [DecidableEq Ty] (fixedAllowed : Term Symbol → Prop)
    (rules : List (Rule Ty Symbol)) (lawful : LawfulFixed fixedAllowed rules) (roots : List Ty) (bound : Int)
    (env : List Ty) (typ : Ty) (remaining : Int) (term : Term Symbol) :
    Accepts (row roots rules bound) (.typed env typ remaining) term ↔
      Typed fixedAllowed rules env typ remaining term :=
  accepts_denotes fixedAllowed rules lawful roots bound term (.typed env typ remaining)

/-- Root acceptance uses one of the original root types and an empty environment. -/
theorem accepts_root [DecidableEq Ty] (fixedAllowed : Term Symbol → Prop)
    (rules : List (Rule Ty Symbol)) (lawful : LawfulFixed fixedAllowed rules) (roots : List Ty) (bound : Int)
    (term : Term Symbol) :
    Accepts (row roots rules bound) .root term ↔ ∃ typ ∈ roots, Typed fixedAllowed rules [] typ bound term :=
  accepts_denotes fixedAllowed rules lawful roots bound term .root

/-- A fixed encoded value accepts only its complete literal tree, at every signed typing budget. -/
theorem accepts_fixed [DecidableEq Ty] (rules : List (Rule Ty Symbol)) (roots : List Ty) (bound : Int)
    (original term : Term Symbol) : Accepts (row roots rules bound) (.fixed original) term ↔ term = original :=
  accepts_permissive rules roots bound term (.fixed original)

/-- Removing repeated root types preserves finite-term language. -/
theorem roots_dedup [DecidableEq Ty] (rules : List (Rule Ty Symbol)) (roots : List Ty) (bound : Int)
    (term : Term Symbol) :
    Accepts (row roots.eraseDups rules bound) .root term ↔ Accepts (row roots rules bound) .root term := by
  rw [accepts_root (fun _ => True) rules (lawful_permissive rules),
    accepts_root (fun _ => True) rules (lawful_permissive rules)]
  simp only [List.mem_eraseDups]

private theorem all₂_on_iff {State Symbol : Type} (first second : State → Term Symbol → Prop)
    (states : List State) (terms : List (Term Symbol))
    (same : ∀ state ∈ states, ∀ term ∈ terms, first state term ↔ second state term) :
    All₂ first states terms ↔ All₂ second states terms := by
  induction states generalizing terms with
  | nil => constructor <;> intro actual <;> cases actual <;> exact .nil
  | cons state states ih =>
      constructor <;> intro actual
      · cases actual with
        | cons first rest =>
            exact .cons ((same _ List.mem_cons_self _ List.mem_cons_self).mp first)
              ((ih _ (fun state member term included =>
                same state (List.mem_cons_of_mem _ member) term (List.mem_cons_of_mem _ included))).mp rest)
      · cases actual with
        | cons first rest =>
            exact .cons ((same _ List.mem_cons_self _ List.mem_cons_self).mpr first)
              ((ih _ (fun state member term included =>
                same state (List.mem_cons_of_mem _ member) term (List.mem_cons_of_mem _ included))).mpr rest)

/-- Row-map correspondence is sufficient only on a domain closed under the actual completed row children. -/
theorem completed_rows_accepts [DecidableEq Ty] (rules : List (Rule Ty Symbol)) (roots : List Ty) (bound : Int)
    (graph : Automaton (Goal Ty Symbol) Symbol) (domain : Goal Ty Symbol → Prop)
    (agrees : ∀ goal, domain goal → graph goal = row roots rules bound goal)
    (closed : ∀ goal, domain goal → ∀ edge ∈ row roots rules bound goal, ∀ child ∈ edge.children, domain child)
    (term : Term Symbol) (goal : Goal Ty Symbol) (included : domain goal) :
    Accepts graph goal term ↔ Accepts (row roots rules bound) goal term := by
  have result := Term.rec
    (motive_1 := fun term => ∀ goal, domain goal →
      (Accepts graph goal term ↔ Accepts (row roots rules bound) goal term))
    (motive_2 := fun terms => ∀ term ∈ terms, ∀ goal, domain goal →
      (Accepts graph goal term ↔ Accepts (row roots rules bound) goal term))
    (fun label terms ih goal included => by
      rw [accepts_node_iff, accepts_node_iff, agrees goal included]
      constructor
      · rintro ⟨edge, member, same, children, guard⟩
        exact ⟨edge, member, same,
          (all₂_on_iff _ _ edge.children terms (fun child memberChild term memberTerm =>
            ih term memberTerm child (closed goal included edge member child memberChild))).mp children, guard⟩
      · rintro ⟨edge, member, same, children, guard⟩
        exact ⟨edge, member, same,
          (all₂_on_iff _ _ edge.children terms (fun child memberChild term memberTerm =>
            ih term memberTerm child (closed goal included edge member child memberChild))).mpr children, guard⟩)
    (by intro term member; cases member)
    (fun head tail first rest term member => by
      rcases List.mem_cons.mp member with same | later
      · subst term
        exact first
      · exact rest term later)
    term
  exact result goal included

/-- A completed row map inherits independent typing after its explicit domain correspondence is established. -/
theorem completed_rows_denotes [DecidableEq Ty] (fixedAllowed : Term Symbol → Prop)
    (rules : List (Rule Ty Symbol)) (lawful : LawfulFixed fixedAllowed rules) (roots : List Ty) (bound : Int)
    (graph : Automaton (Goal Ty Symbol) Symbol) (domain : Goal Ty Symbol → Prop)
    (agrees : ∀ goal, domain goal → graph goal = row roots rules bound goal)
    (closed : ∀ goal, domain goal → ∀ edge ∈ row roots rules bound goal, ∀ child ∈ edge.children, domain child)
    (term : Term Symbol) (goal : Goal Ty Symbol) (included : domain goal) :
    Accepts graph goal term ↔ Denotes fixedAllowed rules roots bound goal term :=
  (completed_rows_accepts rules roots bound graph domain agrees closed term goal included).trans
    (accepts_denotes fixedAllowed rules lawful roots bound term goal)

/-- Read the finite table returned by the actual cold visited-map traversal. -/
def completed [DecidableEq Ty] [DecidableEq (Goal Ty Symbol)] (rules : List (Rule Ty Symbol))
    (roots : List Ty) (bound : Int) (start : Goal Ty Symbol) : Automaton (Goal Ty Symbol) Symbol :=
  fun goal => (SourceTypingFinite.lookup goal (SourceTypingFinite.close roots rules bound [] [start])).getD []

/-- Finite close derives its own row correspondence and child domain before independent typing is concluded. -/
theorem close_denotes [DecidableEq Ty] [DecidableEq (Goal Ty Symbol)] (fixedAllowed : Term Symbol → Prop)
    (rules : List (Rule Ty Symbol)) (lawful : LawfulFixed fixedAllowed rules) (roots : List Ty) (bound : Int)
    (start : Goal Ty Symbol) (term : Term Symbol) :
    Accepts (completed rules roots bound start) start term ↔ Denotes fixedAllowed rules roots bound start term := by
  let table := SourceTypingFinite.close roots rules bound [] [start]
  have computed := SourceTypingFinite.close_complete roots rules bound start
  let domain := fun goal => ∃ edges, SourceTypingFinite.lookup goal table = some edges
  apply completed_rows_denotes fixedAllowed rules lawful roots bound (completed rules roots bound start) domain
  · intro goal included
    obtain ⟨edges, found⟩ := included
    change (SourceTypingFinite.lookup goal table).getD [] = row roots rules bound goal
    rw [found]
    exact (computed.2.2 goal edges found).1
  · intro goal included edge member child childMember
    obtain ⟨edges, found⟩ := included
    obtain ⟨rfl, children⟩ := computed.2.2 goal edges found
    exact children child (List.mem_flatMap.mpr ⟨edge, member, childMember⟩)
  · exact ⟨row roots rules bound start, computed.2.1⟩

/-- Cold finite compilation describes permissive source fixed fields without a validation premise. -/
theorem close_permissive [DecidableEq Ty] [DecidableEq (Goal Ty Symbol)]
    (rules : List (Rule Ty Symbol)) (roots : List Ty) (bound : Int) (start : Goal Ty Symbol) (term : Term Symbol) :
    Accepts (completed rules roots bound start) start term ↔ Denotes (fun _ => True) rules roots bound start term :=
  close_denotes _ rules (lawful_permissive rules) roots bound start term

/-- The finite root graph accepts exactly a closed-environment derivation for an original root type. -/
theorem close_root [DecidableEq Ty] [DecidableEq (Goal Ty Symbol)] (fixedAllowed : Term Symbol → Prop)
    (rules : List (Rule Ty Symbol)) (lawful : LawfulFixed fixedAllowed rules) (roots : List Ty) (bound : Int)
    (term : Term Symbol) :
    Accepts (completed rules roots bound .root) .root term ↔ ∃ typ ∈ roots, Typed fixedAllowed rules [] typ bound term :=
  close_denotes fixedAllowed rules lawful roots bound .root term

end MicroCFTA.SourceTypingRules
