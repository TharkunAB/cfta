import MicroCFTA.InternedUnionHeadGuard

/-!
# Prepared source substitution without open nested binders

The adapter follows the source closed-record shortcut, reference lookup,
ordered children, edge rebuilding, and smart node and union constructors.
An open nested Mu returns none to identify the unsupported adapter branch.
This is not a source error or a fuel limit. Closed Mu records are retained.
-/
namespace MicroCFTA.InternedPreparedSubstitution
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedTemplateProvenance InternedUnionHeadGuard InternedGateRank
open InternedBinderProtocol (Reference NodeKey)

mutual
/-- Prepare one source substitution, retaining each closed input record exactly. -/
def prepare (name : Reference) (value : Value Symbol Guard) : Option (Template Symbol Guard) :=
  if value.free.isEmpty then some (.captured value) else
  match value with
  | .empty => some (.captured .empty)
  | .reference other => some (if other = name then .argument else .captured value)
  | .node _ edges _ _ => (prepareEdges name edges).map .node
  | .union _ members _ _ => (prepareMany name members).map .union
  | .mu .. => none
termination_by sizeOf value

/-- Source child plans retain their original order. -/
def prepareMany (name : Reference) : List (Value Symbol Guard) → Option (List (Template Symbol Guard))
  | [] => some []
  | first :: rest => do
      let head ← prepare name first
      let tail ← prepareMany name rest
      pure (head :: tail)
termination_by values => sizeOf values

/-- Source edge plans retain the symbol and constraint from the actual key. -/
def prepareEdges (name : Reference) : List (EdgeValue Symbol Guard) → Option (List (EdgeTemplate Symbol Guard))
  | [] => some []
  | .mk entry children :: rest => do
      let values ← prepareMany name children
      let edges ← prepareEdges name rest
      pure (.mk entry.key.symbol entry.key.constraint values :: edges)
termination_by edges => sizeOf edges
end

/-- The source closed shortcut creates no constructor effects. -/
theorem prepare_closed (name : Reference) (value : Value Symbol Guard) (closed : value.free = []) :
    prepare name value = some (.captured value) := by rw [prepare.eq_def]; simp [closed]

/-- An open nested binder is explicitly outside this prepared adapter. -/
theorem prepare_open_mu (name : Reference) (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) (openBody : (.mu entry body depth ordinary : Value Symbol Guard).free ≠ []) :
    prepare name (.mu entry body depth ordinary) = none := by rw [prepare.eq_def]; simp [List.isEmpty_iff, openBody]

/-- Root union paths encounter a constructor or an unchanged external reference. -/
inductive GuardedValue (name : Reference) : Value Symbol Guard → Prop where
  | empty : GuardedValue name .empty
  | reference (other) (different : other ≠ name) : GuardedValue name (.reference other)
  | node (entry edges depth free) : GuardedValue name (.node entry edges depth free)
  | union (entry members depth free) (guarded : ∀ value ∈ members, GuardedValue name value) :
      GuardedValue name (.union entry members depth free)

/-- The original guarded record contains no Mu on any root union path. -/
theorem GuardedValue.headSafe (guarded : GuardedValue name value) : HeadSafe value := by
  induction guarded with
  | empty => exact .empty
  | reference other _ => exact .reference other
  | node entry edges depth free => exact .node entry edges depth free
  | union entry members depth free _ ih => exact .union entry members depth free ih

mutual
/-- The actual prepared plan derives its constructor guards from the source record. -/
theorem prepare_guarded (name : Reference) (value : Value Symbol Guard) (template : Template Symbol Guard)
    (prepared : prepare name value = some template) (guarded : GuardedValue name value) : Guarded template := by
  rw [prepare.eq_def] at prepared
  split at prepared
  · cases prepared
    exact .captured _ guarded.headSafe
  · cases guarded with
    | empty => cases prepared; exact .captured _ .empty
    | reference other different =>
        simp only [different, ↓reduceIte, Option.some.injEq] at prepared
        subst template
        exact .captured _ (.reference other)
    | node entry edges depth free =>
        cases result : prepareEdges name edges with
        | none => simp [result] at prepared
        | some values => simp only [result, Option.map_some, Option.some.injEq] at prepared; subst template; exact .node values
    | union entry members depth free safe =>
        cases result : prepareMany name members with
        | none => simp [result] at prepared
        | some values =>
            simp only [result, Option.map_some, Option.some.injEq] at prepared
            subst template
            exact .union values (prepareMany_guarded name members values result safe)
termination_by sizeOf value

/-- Ordered prepared union members inherit their original record guards. -/
theorem prepareMany_guarded (name : Reference) (values : List (Value Symbol Guard)) (templates : List (Template Symbol Guard))
    (prepared : prepareMany name values = some templates)
    (guarded : ∀ value ∈ values, GuardedValue name value) : ∀ template ∈ templates, Guarded template := by
  cases values with
  | nil => simp only [prepareMany, Option.some.injEq] at prepared; subst templates; simp
  | cons first rest =>
      simp only [prepareMany] at prepared
      cases head : prepare name first with
      | none => simp [head] at prepared
      | some firstTemplate =>
          cases tail : prepareMany name rest with
          | none => simp [head, tail] at prepared
          | some restTemplates =>
              simp [head, tail] at prepared
              subst templates
              intro template member
              rcases List.mem_cons.mp member with rfl | member
              · exact prepare_guarded name first _ head (guarded first (by simp))
              · exact prepareMany_guarded name rest restTemplates tail (fun value member => guarded value (by simp [member])) template member
termination_by sizeOf values
end

mutual
/-- Captured records in the prepared plan are actual resident input descendants. -/
theorem prepare_available (name : Reference) (value : Value Symbol Guard) (template : Template Symbol Guard)
    (state : State Symbol Guard) (available : Available state value)
    (prepared : prepare name value = some template) : ∀ captured ∈ captures template, Available state captured := by
  rw [prepare.eq_def] at prepared
  split at prepared
  · cases prepared
    simpa only [captures, List.mem_singleton] using (show ∀ captured, captured = value → Available state captured from fun _ same => same ▸ available)
  · cases value with
    | empty => cases prepared; simpa only [captures, List.mem_singleton] using
        (show ∀ captured, captured = .empty → Available state captured from fun _ same => same ▸ available)
    | reference other =>
        simp only [] at prepared
        split at prepared
        · cases prepared; simp [captures]
        · cases prepared; simpa only [captures, List.mem_singleton] using
            (show ∀ captured, captured = .reference other → Available state captured from fun _ same => same ▸ available)
    | mu => contradiction
    | node entry edges depth free =>
        cases result : prepareEdges name edges with
        | none => simp [result] at prepared
        | some templates =>
            simp only [result, Option.map_some, Option.some.injEq] at prepared
            subst template
            simpa only [captures] using prepareEdges_available name edges templates state (fun child member => available.children child member) result
    | union entry members depth free =>
        cases result : prepareMany name members with
        | none => simp [result] at prepared
        | some templates =>
            simp only [result, Option.map_some, Option.some.injEq] at prepared
            subst template
            simpa only [captures] using prepareMany_available name members templates state (fun child member => available.children child member) result
termination_by sizeOf value

/-- Child plan captures retain availability from the original source children. -/
theorem prepareMany_available (name : Reference) (values : List (Value Symbol Guard)) (templates : List (Template Symbol Guard))
    (state : State Symbol Guard) (available : ∀ value ∈ values, Available state value)
    (prepared : prepareMany name values = some templates) : ∀ captured ∈ manyCaptures templates, Available state captured := by
  cases values with
  | nil => simp only [prepareMany, Option.some.injEq] at prepared; subst templates; simp [manyCaptures]
  | cons first rest =>
      simp only [prepareMany] at prepared
      cases head : prepare name first with
      | none => simp [head] at prepared
      | some firstTemplate =>
          cases tail : prepareMany name rest with
          | none => simp [head, tail] at prepared
          | some restTemplates =>
              simp [head, tail] at prepared
              subst templates
              intro captured member
              simp only [manyCaptures] at member
              rcases List.mem_append.mp (show captured ∈ _ ++ _ from member) with left | right
              · exact prepare_available name first firstTemplate state (available first (by simp)) head captured left
              · exact prepareMany_available name rest restTemplates state (fun value member => available value (by simp [member])) tail captured right
termination_by sizeOf values

/-- Source edge plans retain available captures from their actual ordered payloads. -/
theorem prepareEdges_available (name : Reference) (edges : List (EdgeValue Symbol Guard)) (templates : List (EdgeTemplate Symbol Guard))
    (state : State Symbol Guard) (available : ∀ value ∈ edges.flatMap EdgeValue.children, Available state value)
    (prepared : prepareEdges name edges = some templates) : ∀ captured ∈ edgeCaptures templates, Available state captured := by
  cases edges with
  | nil => simp only [prepareEdges, Option.some.injEq] at prepared; subst templates; simp [edgeCaptures]
  | cons first rest =>
      cases first with
      | mk entry children =>
          simp only [prepareEdges] at prepared
          cases head : prepareMany name children with
          | none => simp [head] at prepared
          | some childTemplates =>
              cases tail : prepareEdges name rest with
              | none => simp [head, tail] at prepared
              | some edgeTemplates =>
                  simp [head, tail] at prepared
                  subst templates
                  intro captured member
                  simp only [edgeCaptures] at member
                  rcases List.mem_append.mp (show captured ∈ _ ++ _ from member) with left | right
                  · exact prepareMany_available name children childTemplates state
                      (fun value member => available value (by simp [EdgeValue.children, member])) head captured left
                  · exact prepareEdges_available name rest edgeTemplates state
                      (fun value member => available value (by simp [EdgeValue.children, member])) tail captured right
termination_by sizeOf edges
end

mutual
/-- Actual cached depth zero proves that preparation cannot reach an open Mu. -/
theorem prepare_zero (name : Reference) (value : Value Symbol Guard) (state : State Symbol Guard)
    (coherent : Coherent state) (available : Available state value) (zero : value.depth = 0) :
    ∃ template, prepare name value = some template := by
  rw [prepare.eq_def]
  split
  · exact ⟨_, rfl⟩
  · cases value with
    | empty | reference => exact ⟨_, rfl⟩
    | mu => simp [Value.depth] at zero
    | node entry edges depth free =>
        have childZero : ∀ child ∈ edges.flatMap EdgeValue.children, child.depth = 0 := by
          intro child member
          have bound := InternedUnionSeparation.child_depth state coherent (.node entry edges depth free) child available member
          exact Nat.eq_zero_of_le_zero (zero ▸ bound)
        obtain ⟨templates, prepared⟩ := prepareEdges_zero name edges state coherent
          (fun child member => available.children child member) childZero
        exact ⟨.node templates, by simp [prepared]⟩
    | union entry members depth free =>
        have childZero : ∀ child ∈ members, child.depth = 0 := by
          intro child member
          have bound := InternedUnionSeparation.child_depth state coherent (.union entry members depth free) child available member
          exact Nat.eq_zero_of_le_zero (zero ▸ bound)
        obtain ⟨templates, prepared⟩ := prepareMany_zero name members state coherent
          (fun child member => available.children child member) childZero
        exact ⟨.union templates, by simp [prepared]⟩
termination_by sizeOf value

/-- Depth-zero ordered children always have complete source plans in this fragment. -/
theorem prepareMany_zero (name : Reference) (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (available : ∀ value ∈ values, Available state value)
    (zero : ∀ value ∈ values, value.depth = 0) : ∃ templates, prepareMany name values = some templates := by
  cases values with
  | nil => exact ⟨[], by simp [prepareMany]⟩
  | cons first rest =>
      obtain ⟨head, preparedHead⟩ := prepare_zero name first state coherent (available first (by simp)) (zero first (by simp))
      obtain ⟨tail, preparedTail⟩ := prepareMany_zero name rest state coherent
        (fun value member => available value (by simp [member])) (fun value member => zero value (by simp [member]))
      exact ⟨head :: tail, by simp [prepareMany, preparedHead, preparedTail]⟩
termination_by sizeOf values

/-- Resident source edge children inherit the same depth-zero plan guarantee. -/
theorem prepareEdges_zero (name : Reference) (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (available : ∀ value ∈ edges.flatMap EdgeValue.children, Available state value)
    (zero : ∀ value ∈ edges.flatMap EdgeValue.children, value.depth = 0) :
    ∃ templates, prepareEdges name edges = some templates := by
  cases edges with
  | nil => exact ⟨[], by simp [prepareEdges]⟩
  | cons first rest =>
      cases first with
      | mk entry children =>
          obtain ⟨head, preparedHead⟩ := prepareMany_zero name children state coherent
            (fun value member => available value (by simp [EdgeValue.children, member]))
            (fun value member => zero value (by simp [EdgeValue.children, member]))
          obtain ⟨tail, preparedTail⟩ := prepareEdges_zero name rest state coherent
            (fun value member => available value (by simp [EdgeValue.children, member]))
            (fun value member => zero value (by simp [EdgeValue.children, member]))
          exact ⟨.mk entry.key.symbol entry.key.constraint head :: tail, by simp [prepareEdges, preparedHead, preparedTail]⟩
termination_by sizeOf edges
end

/-- Actual prepared substitution has rank zero for a guarded source body.
Both input and result are complete records in the source cache computation. -/
theorem prepared_rank [DecidableEq (EdgeKey Symbol Guard)] (name : Reference)
    (body replacement : Value Symbol Guard) (template : Template Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state) (cached : Cached state)
    (bodyAvailable : Available state body) (replacementAvailable : Available state replacement)
    (prepared : prepare name body = some template) (guarded : GuardedValue name body) :
    headRank (run (compile template replacement) state).1 = 0 :=
  (compile_safeHead template replacement state coherent cached replacementAvailable
    (prepare_available name body template state bodyAvailable prepared)
    (prepare_guarded name body template prepared guarded)).rank

/-- A guarded depth-zero body supplies a complete plan and a strict actual
head-rank decrease. No output rank or plan-success premise is supplied. -/
theorem shallow_unfold_decreases [DecidableEq (EdgeKey Symbol Guard)]
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) (state : State Symbol Guard)
    (coherent : Coherent state) (cached : Cached state) (available : Available state (.mu entry body depth ordinary))
    (zero : body.depth = 0) (guarded : GuardedValue (.interned entry.identity) body) :
    ∃ template, prepare (.interned entry.identity) body = some template ∧
      headRank (run (compile template (.mu entry body depth ordinary)) state).1 <
        headRank (.mu entry body depth ordinary) := by
  have bodyAvailable : Available state body := available.children body (by simp [InternedProbeProvenance.children])
  obtain ⟨template, prepared⟩ := prepare_zero (.interned entry.identity) body state coherent bodyAvailable zero
  refine ⟨template, prepared, ?_⟩
  rw [prepared_rank (.interned entry.identity) body (.mu entry body depth ordinary) template state
    coherent cached bodyAvailable available prepared guarded]
  simp [headRank]

end MicroCFTA.InternedPreparedSubstitution
