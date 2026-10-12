import MicroCFTA.LexicalBinderClosure
import MicroCFTA.BoundDepth

/-!
# Exact language of finite lexical constructor exposure

The least-language semantics forces each accepted term to reach a constructor
through a finite epsilon path. The proof uses exposed constructors as the
candidate language for each binder. It does not assume a row-language law.
-/
namespace MicroCFTA.LexicalExposureLanguage
open Language Binding BinderLanguage EnumerationBinderExposure LexicalBinderClosure

/-- A finite epsilon path reaches a constructor whose complete term is accepted. -/
def Head (environment : Env Symbol) (root : Shape (Payload Symbol)) : Lang Symbol :=
  fun term => ∃ payload children,
    Productivity.Reachable epsilonSuccessors [root] (.branch payload children) ∧
      meaning environment (.branch payload children) term

/-- One epsilon step preserves accepted terms in the reverse direction. -/
theorem epsilon_sound (environment : Env Symbol) (before after : Shape (Payload Symbol))
    (closed : free before = []) (member : after ∈ epsilonSuccessors before) :
    Included (meaning environment after) (meaning environment before) := by
  cases before with
  | empty | ref | branch => simp [epsilonSuccessors] at member
  | alternatives parts =>
      intro term accepted
      simpa only [meaning] using (show ∃ selected : {selected // selected ∈ parts}, meaning environment selected.val term from ⟨⟨after, member⟩, accepted⟩)
  | binder name body =>
      have same : after = unfold name body := by simpa [epsilonSuccessors] using member
      subst after
      rw [unfold_exact environment name body closed]
      exact fun _ accepted => accepted

/-- Every finite epsilon path transports the complete constructor language to its root. -/
theorem reachable_sound (environment : Env Symbol) (root target : Shape (Payload Symbol))
    (closed : free root = []) (reached : Productivity.Reachable epsilonSuccessors [root] target) :
    Included (meaning environment target) (meaning environment root) := by
  induction reached with
  | seed member =>
      have same : _ = root := List.mem_singleton.mp member
      subst_vars
      exact fun _ accepted => accepted
  | @step parent child previous member ih =>
      intro term accepted
      exact ih term (epsilon_sound environment parent child
        (reachable_closed closed (epsilon_reachable root parent previous)) member term accepted)

/-- Constructor exposure cannot create any accepted term. -/
theorem head_sound (environment : Env Symbol) (root : Shape (Payload Symbol)) (closed : free root = []) :
    Included (Head environment root) (meaning environment root) := by
  rintro term ⟨payload, children, reached, accepted⟩
  exact reachable_sound environment root _ closed reached term accepted

/-- A constructor is its own zero-step exposure. -/
theorem head_constructor (environment : Env Symbol) (payload : Payload Symbol)
    (children : List (Shape (Payload Symbol))) :
    Included (meaning environment (.branch payload children)) (Head environment (.branch payload children)) := by
  intro term accepted
  exact ⟨payload, children, .seed (by simp), accepted⟩

/-- Prefixing one epsilon step retains a finite constructor witness. -/
theorem head_step (environment : Env Symbol) (before after : Shape (Payload Symbol))
    (member : after ∈ epsilonSuccessors before) : Included (Head environment after) (Head environment before) := by
  rintro term ⟨payload, children, reached, accepted⟩
  exact ⟨payload, children, EpsilonUnion.reach_trans _ _ _ _ (.step (.seed (by simp)) member) reached, accepted⟩

/-- Each interpreted free reference supplies a finite constructor witness in its closed replacement. -/
def Related (environment : Env Symbol) (substitution : Environment (Payload Symbol)) (values : Env Symbol) : Prop :=
  ∀ name term, values name term → ∃ replacement, substitution name = some replacement ∧
    free replacement = [] ∧ Head environment replacement term

/-- Closed replacement values make the prepared substitution capture-free. -/
theorem closed_fresh (substitution : Environment (Payload Symbol)) (closed : ClosedEnvironment substitution)
    (names : List Nat) : Fresh substitution names := by
  intro name member reference replacement found
  simp [closed reference replacement found]

/-- The complete instantiated language contains every externally interpreted constructor witness. -/
theorem related_meaning (environment : Env Symbol) (substitution : Environment (Payload Symbol))
    (closed : ClosedEnvironment substitution) (values : Env Symbol) (related : Related environment substitution values)
    (shape : Shape (Payload Symbol)) :
    Included (meaning values shape) (meaning environment (substitute substitution shape)) := by
  rw [substitution_exact shape environment substitution (closed_fresh substitution closed _)]
  apply meaning_mono
  intro name term accepted
  obtain ⟨replacement, found, replacementClosed, witness⟩ := related name term accepted
  simpa [substitutedEnv, found] using head_sound environment replacement replacementClosed term witness

/-- A binder's leastness derives a finite constructor witness, including nested and epsilon binders. -/
theorem meaning_head (environment : Env Symbol) (shape : Shape (Payload Symbol))
    (substitution : Environment (Payload Symbol)) (closed : ClosedEnvironment substitution)
    (resolved : Resolved substitution shape) (values : Env Symbol)
    (related : Related environment substitution values) :
    Included (meaning values shape) (Head environment (substitute substitution shape)) := by
  induction shape using Shape.rec
    (motive_2 := fun shapes => ∀ shape ∈ shapes, ∀ substitution : Environment (Payload Symbol),
      ClosedEnvironment substitution → Resolved substitution shape → ∀ values : Env Symbol,
      Related environment substitution values →
      Included (meaning values shape) (Head environment (substitute substitution shape)))
    generalizing substitution values with
  | empty => simp only [meaning, Included]; intro term impossible; exact False.elim impossible
  | ref name =>
      intro term accepted
      obtain ⟨replacement, found, _, witness⟩ := related name term (by simpa only [meaning] using accepted)
      simpa [substitute, found] using witness
  | branch payload children =>
      intro term accepted
      exact head_constructor environment payload (substituteList substitution children) term
        (related_meaning environment substitution closed values related (.branch payload children) term accepted)
  | alternatives parts ih =>
      simp only [meaning, Included]
      rintro term ⟨⟨part, member⟩, accepted⟩
      apply head_step environment (substitute substitution (.alternatives parts)) (substitute substitution part)
      · simp only [substitute, epsilonSuccessors, substituteList_map]
        exact List.mem_map.mpr ⟨part, member, rfl⟩
      · exact ih part member substitution closed (resolved_member substitution parts resolved part member)
          values related term accepted
  | binder name body ih =>
      let value := substitute substitution (.binder name body)
      have valueClosed : free value = [] := instance_closed substitution (.binder name body) closed resolved
      simp only [meaning]
      apply least_le
      intro term accepted
      have bodyRelated : Related environment (extend substitution name value) (bind values name (Head environment value)) := by
        intro other tree present
        by_cases hit : other = name
        · exact ⟨value, by simp [extend, hit], valueClosed, by simpa [BinderLanguage.bind, hit] using present⟩
        · obtain ⟨replacement, found, replacementClosed, witness⟩ := related other tree (by simpa [BinderLanguage.bind, hit] using present)
          exact ⟨replacement, by simp [extend, hit, found], replacementClosed, witness⟩
      have witness := ih (extend substitution name value)
        (extend_closed substitution name value closed valueClosed) (body_resolved substitution name body resolved)
        (bind values name (Head environment value)) bodyRelated term accepted
      apply head_step environment value (substitute (extend substitution name value) body) ?_ term witness
      simp only [value, substitute, epsilonSuccessors, List.mem_singleton]
      exact (unfold_instance substitution name body closed).symm
  | nil =>
      rename_i shape member substitution closed resolved values related
      simp at member
  | cons first rest ih ir =>
      rename_i shape member substitution closed resolved values related
      rcases List.mem_cons.mp member with rfl | member
      · exact ih substitution closed resolved values related
      · exact ir shape member substitution closed resolved values related

/-- Every accepted term of a closed lexical root has a finite constructor exposure. -/
theorem head_complete (environment : Env Symbol) (root : Shape (Payload Symbol)) (closed : free root = []) :
    Included (meaning environment root) (Head environment root) := by
  have environmentClosed : ClosedEnvironment (fun _ => none : Environment (Payload Symbol)) := by
    intro name value found
    cases found
  have resolved : Resolved (fun _ => none : Environment (Payload Symbol)) root := by
    intro name member
    simp [closed] at member
  have related : Related environment (fun _ => none) (fun _ _ => False) := by
    intro name term impossible
    exact False.elim impossible
  have exact := meaning_head environment root (fun _ => none) environmentClosed resolved (fun _ _ => False) related
  have same : meaning environment root = meaning (fun _ _ => False) root :=
    meaning_congr root _ _ (fun name member => by simp [closed] at member)
  simpa [substitute_empty, same] using exact

/-- Constructor exposure has exactly the least-language semantics of every closed root. -/
theorem head_exact (environment : Env Symbol) (root : Shape (Payload Symbol))
    (closed : free root = []) (term : Term Symbol) :
    Head environment root term ↔ meaning environment root term :=
  ⟨head_sound environment root closed term, head_complete environment root closed term⟩

/-- The concrete visited rows contain all accepted constructor terms and only those terms. -/
theorem exposed_language [DecidableEq (Shape (Payload Symbol))] (environment : Env Symbol)
    (root : Shape (Payload Symbol)) (closed : free root = []) (term : Term Symbol) :
    rowsMeaning environment (exposedRows root) term ↔ meaning environment root term := by
  rw [← head_exact environment root closed term]
  constructor
  · rintro ⟨row, member, accepted⟩
    obtain ⟨shape, reached, rowMember⟩ := (exposed_rows_exact root closed row).mp member
    cases shape with
    | empty | ref | alternatives | binder => simp [constructorRows] at rowMember
    | branch payload children =>
        have same : row = (payload, children) := by simpa [constructorRows] using rowMember
        subst row
        exact ⟨payload, children, reached, accepted⟩
  · rintro ⟨payload, children, reached, accepted⟩
    exact ⟨(payload, children), (exposed_rows_exact root closed _).mpr
      ⟨.branch payload children, reached, by simp [constructorRows]⟩, accepted⟩

/-- Epsilon closure leaves the constructor-height bound unchanged. -/
theorem exposed_bounded_language [DecidableEq (Shape (Payload Symbol))] (environment : Env Symbol)
    (root : Shape (Payload Symbol)) (closed : free root = []) (height : Nat) (term : Term Symbol) :
    (rowsMeaning environment (exposedRows root) term ∧ term.height ≤ height) ↔
      meaning environment root term ∧ term.height ≤ height := by
  rw [exposed_language environment root closed term]

/-- Convert one complete exposed row to the ordinary constructor graph representation. -/
noncomputable def rowEdge (row : EnumerationBinderExposure.Row Symbol) :
    Language.Edge (Shape (Payload Symbol)) Symbol := by
  classical
  exact ⟨row.1.label, row.2, fun term => decide (row.1.guard term)⟩

/-- The constructor graph reads exactly the derived visited rows at every lexical instance. -/
noncomputable def automaton [DecidableEq (Shape (Payload Symbol))] :
    Automaton (Shape (Payload Symbol)) Symbol := fun root => (exposedRows root).map rowEdge

/-- Reading the exposed constructor graph gives exactly the original closed lexical language. -/
theorem automaton_exact [DecidableEq (Shape (Payload Symbol))] (environment : Env Symbol)
    (root : Shape (Payload Symbol)) (closed : free root = []) (term : Term Symbol) :
    Accepts automaton root term ↔ meaning environment root term := by
  classical
  induction term using Term.rec
    (motive_2 := fun terms => ∀ shapes : List (Shape (Payload Symbol)),
      (∀ shape ∈ shapes, free shape = []) →
      (All₂ (Accepts automaton) shapes terms ↔ BinderLanguage.forest environment shapes terms))
    generalizing root with
  | node symbol children ih =>
      rw [← exposed_language environment root closed (.node symbol children), accepts_node_iff]
      constructor
      · rintro ⟨edge, member, label, runs, guard⟩
        change edge ∈ (exposedRows root).map rowEdge at member
        obtain ⟨row, rowMember, sameEdge⟩ := List.mem_map.mp member
        subst edge
        refine ⟨row, rowMember, ?_⟩
        simp only [meaning]
        refine ⟨children, ?_, ?_, ?_⟩
        · exact congrArg (fun symbol => Term.node symbol children) label.symm
        · exact (ih row.2 (fun child childMember =>
            (exposed_child_in_inventory root closed row rowMember child childMember).2)).mp runs
        · simpa [rowEdge] using guard
      · rintro ⟨row, member, accepted⟩
        simp only [meaning, Term.node.injEq] at accepted
        obtain ⟨terms, ⟨label, sameTerms⟩, forest, guard⟩ := accepted
        subst terms
        refine ⟨rowEdge row, List.mem_map.mpr ⟨row, member, rfl⟩, label.symm, ?_, ?_⟩
        · exact (ih row.2 (fun child childMember =>
            (exposed_child_in_inventory root closed row member child childMember).2)).mpr forest
        · simpa [rowEdge] using guard
  | nil =>
      rename_i shapes closed
      cases shapes with
      | nil => simp only [BinderLanguage.forest]; exact ⟨fun _ => trivial, fun _ => .nil⟩
      | cons first rest =>
          simp only [BinderLanguage.forest]
          constructor
          · intro h; cases h
          · intro h; exact False.elim h
  | cons first rest ih ir =>
      rename_i shapes closed
      cases shapes with
      | nil =>
          simp only [BinderLanguage.forest]
          constructor
          · intro h; cases h
          · intro h; exact False.elim h
      | cons shape tail =>
          simp only [BinderLanguage.forest]
          constructor
          · intro runs
            cases runs with
            | cons head rest => exact ⟨(ih shape (closed shape (by simp))).mp head,
                (ir tail (fun child member => closed child (by simp [member]))).mp rest⟩
          · rintro ⟨head, rest⟩
            exact .cons ((ih shape (closed shape (by simp))).mpr head)
              ((ir tail (fun child member => closed child (by simp [member]))).mpr rest)

/-- The existing bounded constructor construction now starts from a proved lexical row language. -/
theorem bounded_exact [DecidableEq (Shape (Payload Symbol))] (environment : Env Symbol)
    (root : Shape (Payload Symbol)) (closed : free root = []) (height : Nat) (term : Term Symbol) :
    Accepts (BoundDepth.bound automaton) (height, root) term ↔
      meaning environment root term ∧ term.height ≤ height := by
  rw [BoundDepth.bound_exact, automaton_exact environment root closed term]

/-- Bounding after epsilon exposure preserves every accepted finite term at a sufficient depth. -/
theorem eventually_bounded [DecidableEq (Shape (Payload Symbol))] (environment : Env Symbol)
    (root : Shape (Payload Symbol)) (closed : free root = []) (term : Term Symbol) :
    meaning environment root term ↔ ∃ height, Accepts (BoundDepth.bound automaton) (height, root) term := by
  rw [← automaton_exact environment root closed term]
  exact BoundDepth.eventually_bounded automaton root term

end MicroCFTA.LexicalExposureLanguage
