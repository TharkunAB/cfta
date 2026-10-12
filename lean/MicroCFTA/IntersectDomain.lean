import MicroCFTA.IntersectSchedule

/-!
# Recursive environment coverage in the source intersection schedule

The source can unfold only `RecInt` values stored by enclosing binders.
Cached free-variable sets provide the scope information needed by each
recursive call. Typed bindings and complete coverage are separate invariants.
-/
namespace MicroCFTA.IntersectSchedule
open Language Binding BinderLanguage

/-- Cached free-variable sets agree with every input payload constructor. -/
structure FreeCorrect (view : View Symbol) : Prop where
  empty : view.free .empty = []
  reference : ∀ name, view.free (.ref name) = [name]
  binder : ∀ bound name, name ∈ view.free (.mu bound) ↔ name ∈ view.free (view.body bound) ∧ name ≠ bound
  node : ∀ node name, name ∈ view.free (.node node) ↔
    ∃ row ∈ view.rows node, ∃ child ∈ row.children, name ∈ view.free child
  union : ∀ node name, name ∈ view.free (.union node) ↔
    ∃ member ∈ view.members node, name ∈ view.free member

/-- A covered recursive name resolves to the binder with that same identity. -/
def Assigned (domain : Domain) (name : Nat) : Prop := lookup domain name = some (.mu name)

/-- Every free reference of an input has its binder in the current domain. -/
def Covers (view : View Symbol) (domain : Domain) (input : Input) : Prop :=
  ∀ name ∈ view.free input, Assigned domain name

/-- Stored bindings have the correct identity and their own free variables remain covered. -/
structure ValidDomain (view : View Symbol) (domain : Domain) : Prop where
  typed : ∀ name input, lookup domain name = some input → input = .mu name
  closed : ∀ name, Assigned domain name → Covers view domain (.mu name)

/-- Prefix bindings to their own identities override only those same identities. -/
theorem prefix_lookup (names : List Nat) (entries : List (Nat × Input)) (seen : List Pair) (name : Nat) :
    lookup ⟨names.map (fun key => (key, Input.mu key)) ++ entries, seen⟩ name =
      if name ∈ names then some (.mu name) else lookup ⟨entries, seen⟩ name := by
  induction names with
  | nil => simp [lookup]
  | cons first rest ih =>
    by_cases same : name = first
    · subst first; simp [lookup]
    · have different : (first == name) = false := beq_eq_false_iff_ne.mpr (Ne.symm same)
      simpa only [List.map_cons, List.cons_append, lookup, List.find?_cons, different,
        List.mem_cons, same, false_or] using ih

/-- Source environment extension retains every old valid binding. -/
theorem extend_lookup (domain : Domain) (names : List Nat) (key : Pair) (name : Nat) :
    lookup (extend domain (names.map (fun bound => (bound, Input.mu bound))) key) name =
      if name ∈ names then some (.mu name) else lookup domain name := by
  unfold extend
  rw [← List.map_reverse, prefix_lookup]
  simp only [List.mem_reverse]
  rfl

/-- New binder entries cannot invalidate an old identity-correct lookup. -/
theorem extend_assigned (domain : Domain) (names : List Nat) (key : Pair) (name : Nat)
    (old : Assigned domain name) :
    Assigned (extend domain (names.map (fun bound => (bound, Input.mu bound))) key) name := by
  unfold Assigned at old ⊢
  rw [extend_lookup]
  split
  · rfl
  · exact old

/-- Each newly encountered binder is immediately available for recursive occurrences. -/
theorem extend_new (domain : Domain) (names : List Nat) (key : Pair) (name : Nat) (member : name ∈ names) :
    Assigned (extend domain (names.map (fun bound => (bound, Input.mu bound))) key) name := by
  unfold Assigned
  rw [extend_lookup, ite_eq_left member]

/-- Preserving every existing binding preserves coverage of all input free variables. -/
theorem covers_mono (view : View Symbol) (before after : Domain) (input : Input)
    (preserved : ∀ name, Assigned before name → Assigned after name) (covered : Covers view before input) :
    Covers view after input := fun name member => preserved name (covered name member)

/-- Extension preserves coverage of the original input nodes. -/
theorem covers_extend (view : View Symbol) (domain : Domain) (names : List Nat) (key : Pair) (input : Input)
    (covered : Covers view domain input) :
    Covers view (extend domain (names.map (fun bound => (bound, Input.mu bound))) key) input :=
  covers_mono view domain _ input (extend_assigned domain names key) covered

/-- The empty domain has no stored binding to violate either invariant. -/
theorem valid_empty (view : View Symbol) : ValidDomain view {} := by
  constructor
  · intro name input stored; cases stored
  · intro name stored; cases stored

/-- A cached closed input needs no environment binding. -/
theorem closed_covered (view : View Symbol) (domain : Domain) (input : Input)
    (isClosed : closed view input = true) : Covers view domain input := by
  have empty : view.free input = [] := List.isEmpty_iff.mp isClosed
  intro name member
  simp [empty] at member

/-- Extension preserves the complete recursive environment invariant. -/
theorem valid_extend (view : View Symbol) (domain : Domain) (names : List Nat) (key : Pair)
    (valid : ValidDomain view domain) (covered : ∀ name ∈ names, Covers view domain (.mu name)) :
    ValidDomain view (extend domain (names.map (fun bound => (bound, Input.mu bound))) key) := by
  constructor
  · intro name input stored
    rw [extend_lookup] at stored
    split at stored
    · exact (Option.some.inj stored).symm
    · exact valid.typed name input stored
  · intro name stored
    by_cases member : name ∈ names
    · exact covers_extend view domain names key _ (covered name member)
    · have old : Assigned domain name := by
        unfold Assigned at stored ⊢
        simpa only [extend_lookup, ite_eq_right member] using stored
      exact covers_extend view domain names key _ (valid.closed name old)

/-- Opening a binder makes every free variable of its body available. -/
theorem binder_body_covered (view : View Symbol) (freeCorrect : FreeCorrect view)
    (domain : Domain) (names : List Nat) (key : Pair) (bound : Nat) (member : bound ∈ names)
    (covered : Covers view domain (.mu bound)) :
    Covers view (extend domain (names.map (fun name => (name, Input.mu name))) key) (view.body bound) := by
  intro name present
  by_cases same : name = bound
  · subst name; exact extend_new domain names key bound member
  · exact extend_assigned domain names key name (covered name ((freeCorrect.binder bound name).mpr ⟨present, same⟩))

/-- A covered recursive occurrence resolves without the source's partial-map failure. -/
theorem reference_resolves (view : View Symbol) (freeCorrect : FreeCorrect view)
    (domain : Domain) (name : Nat) (covered : Covers view domain (.ref name)) :
    lookup domain name = some (.mu name) :=
  covered name (by rw [freeCorrect.reference]; simp)

/-- Every child of a covered constructor row remains covered. -/
theorem node_child_covered (view : View Symbol) (freeCorrect : FreeCorrect view)
    (domain : Domain) (node : Nat) (row : Row Symbol) (present : row ∈ view.rows node)
    (child : Input) (member : child ∈ row.children) (covered : Covers view domain (.node node)) :
    Covers view domain child := by
  intro name free
  exact covered name ((freeCorrect.node node name).mpr ⟨row, present, child, member, free⟩)

/-- Every member of a covered epsilon union remains covered. -/
theorem union_member_covered (view : View Symbol) (freeCorrect : FreeCorrect view)
    (domain : Domain) (node : Nat) (input : Input) (member : input ∈ view.members node)
    (covered : Covers view domain (.union node)) : Covers view domain input := by
  intro name free
  exact covered name ((freeCorrect.union node name).mpr ⟨input, member, free⟩)

/-- A bounded result succeeds or reports only exhaustion, never an invalid free lookup. -/
def NoLookupFailure : Except Error α → Prop
  | .ok _ => True
  | .error .fuelExhausted => True
  | .error (.missingBinder _) => False

/-- Mapping a successful value cannot introduce a lookup error. -/
theorem noLookup_map (action : Except Error α) (convert : α → β) (safe : NoLookupFailure action) :
    NoLookupFailure (action.map convert) := by
  cases action with
  | ok => trivial
  | error error => cases error <;> exact safe

/-- A traversal can report only an error already reported by one of its workers. -/
theorem noLookup_walk (action : α → Except Error β) (inputs : List α)
    (safe : ∀ input ∈ inputs, NoLookupFailure (action input)) : NoLookupFailure (walk action inputs) := by
  induction inputs with
  | nil => trivial
  | cons first rest ih =>
    have firstSafe := safe first (by simp)
    cases headRun : action first with
    | error error =>
      cases error with
      | fuelExhausted => simp [walk, headRun, Bind.bind, Except.bind, NoLookupFailure]
      | missingBinder name => simp only [headRun, NoLookupFailure] at firstSafe
    | ok value =>
      have tailSafe := ih (fun input member => safe input (by simp [member]))
      cases tailRun : walk action rest with
      | error error =>
        cases error <;> simpa [walk, headRun, tailRun, Bind.bind, Except.bind] using tailSafe
      | ok values =>
        simp [walk, headRun, tailRun, Bind.bind, Except.bind, Pure.pure, Except.pure, NoLookupFailure]

/-- Every matched hash-join row pair comes from its corresponding original node. -/
theorem joined_members [DecidableEq Symbol] (left right : List (Row Symbol)) (rows : Row Symbol × Row Symbol)
    (member : rows ∈ joined left right) : rows.1 ∈ left ∧ rows.2 ∈ right := by
  obtain ⟨first, firstMember, second, secondMember, _, same⟩ :=
    (SymbolicHashJoin.hashJoin_member Row.label (fun a b => (a, b)) left right rows).mp member
  subst rows
  exact ⟨firstMember, secondMember⟩

/-- Complete cached free-variable sets and covered environments exclude every partial source lookup error. -/
theorem run_no_lookup_failure [DecidableEq Symbol] (view : View Symbol) (freeCorrect : FreeCorrect view)
    (fuel : Nat) :
    (∀ domain left right, ValidDomain view domain → Covers view domain left → Covers view domain right →
      NoLookupFailure (run view fuel domain left right)) ∧
    (∀ domain left right, ValidDomain view domain →
      (∀ child ∈ left.children, Covers view domain child) →
      (∀ child ∈ right.children, Covers view domain child) → NoLookupFailure (edge view fuel domain left right)) := by
  induction fuel with
  | zero => constructor <;> intros <;> trivial
  | succ fuel ih =>
    constructor
    · intro domain left right valid leftCovered rightCovered
      rw [run.eq_def]
      dsimp only
      by_cases empty : left = .empty ∨ right = .empty
      · rw [ite_eq_left empty]; trivial
      rw [ite_eq_right empty]
      by_cases reset : (closed view left && closed view right && !domain.free.isEmpty) = true
      · rw [ite_eq_left reset]
        have both : closed view left = true ∧ closed view right = true := by
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at reset
          exact reset.1
        exact ih.1 {} left right (valid_empty view) (closed_covered view {} left both.1)
          (closed_covered view {} right both.2)
      rw [ite_eq_right reset]
      by_cases same : left = right ∧ closed view left = true
      · rw [ite_eq_left same]; trivial
      rw [ite_eq_right same]
      by_cases swap : greater left right = true
      · rw [ite_eq_left swap]; exact ih.1 domain right left valid rightCovered leftCovered
      rw [ite_eq_right swap]
      by_cases seen : pair left right ∈ domain.seen
      · rw [ite_eq_left seen]; trivial
      rw [ite_eq_right seen]
      split
      · next first second =>
        refine noLookup_map _ _ (ih.1 _ _ _ (valid_extend view domain [first, second] _ valid ?_) ?_ ?_)
        · intro name member
          rcases List.mem_cons.mp member with rfl | member
          · exact leftCovered
          · have same : name = second := by simpa using member
            exact same ▸ rightCovered
        · exact binder_body_covered view freeCorrect domain [first, second] _ first (by simp) leftCovered
        · exact binder_body_covered view freeCorrect domain [first, second] _ second (by simp) rightCovered
      · next first other =>
        refine noLookup_map _ _ (ih.1 _ _ _ (valid_extend view domain [first] _ valid ?_) ?_ ?_)
        · intro name member
          have same : name = first := by simpa using member
          exact same ▸ leftCovered
        · exact binder_body_covered view freeCorrect domain [first] _ first (by simp) leftCovered
        · exact covers_extend view domain [first] _ _ rightCovered
      · next second other =>
        refine noLookup_map _ _ (ih.1 _ _ _ (valid_extend view domain [second] _ valid ?_) ?_ ?_)
        · intro name member
          have same : name = second := by simpa using member
          exact same ▸ rightCovered
        · exact covers_extend view domain [second] _ _ leftCovered
        · exact binder_body_covered view freeCorrect domain [second] _ second (by simp) rightCovered
      · next first other =>
        refine noLookup_map _ _ (noLookup_walk _ _ ?_)
        intro input member
        exact ih.1 domain input _ valid (union_member_covered view freeCorrect domain first input member leftCovered) rightCovered
      · next second _ _ =>
        refine noLookup_map _ _ (noLookup_walk _ _ ?_)
        intro input member
        exact ih.1 domain _ input valid leftCovered (union_member_covered view freeCorrect domain second input member rightCovered)
      · next name _ _ =>
        have resolved := reference_resolves view freeCorrect domain name leftCovered
        rw [resolved]
        exact ih.1 domain (.mu name) _ valid (valid.closed name resolved) rightCovered
      · next name _ _ _ =>
        have resolved := reference_resolves view freeCorrect domain name rightCovered
        rw [resolved]
        exact ih.1 domain _ (.mu name) valid leftCovered (valid.closed name resolved)
      · next first second =>
        refine noLookup_map _ _ (noLookup_walk _ _ ?_)
        intro rows member
        have originals := joined_members _ _ rows member
        exact ih.2 domain rows.1 rows.2 valid
          (fun child present => node_child_covered view freeCorrect domain first rows.1 originals.1 child present leftCovered)
          (fun child present => node_child_covered view freeCorrect domain second rows.2 originals.2 child present rightCovered)
      · trivial
      · trivial
    · intro domain left right valid leftCovered rightCovered
      rw [edge.eq_def]
      dsimp only
      split
      · trivial
      · refine noLookup_map _ _ (noLookup_walk _ _ ?_)
        intro children member
        have originals := List.of_mem_zip member
        exact ih.1 domain children.1 children.2 valid (leftCovered children.1 originals.1) (rightCovered children.2 originals.2)

/-- Closed top-level inputs can fail only because the explicit execution bound was exhausted. -/
theorem top_no_lookup_failure [DecidableEq Symbol] (view : View Symbol) (freeCorrect : FreeCorrect view)
    (fuel : Nat) (left right : Input) (leftClosed : closed view left = true) (rightClosed : closed view right = true) :
    NoLookupFailure (run view fuel {} left right) :=
  (run_no_lookup_failure view freeCorrect fuel).1 {} left right (valid_empty view)
    (closed_covered view {} left leftClosed) (closed_covered view {} right rightClosed)

end MicroCFTA.IntersectSchedule
