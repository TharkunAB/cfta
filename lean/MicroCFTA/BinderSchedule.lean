import MicroCFTA.BinderComponents

/-!
# Optional binder construction in graph import

The source adds a binder only when its cycle test selects the current state.
Otherwise it copies the constructor body in the current context. This module
models those control branches with bounded instrumentation. The success
theorem does not require a correct cycle test. A missed cycle can prevent
termination, but cannot change a successfully constructed language.
-/

namespace MicroCFTA.BinderSchedule
open Language Binding BinderLanguage BinderGraph BinderCompile

/-- Traverse a complete ordered list, failing if one child construction fails. -/
def walk (action : α → Option β) : List α → Option (List β)
  | [] => some []
  | head :: tail => do
    let first ← action head
    let rest ← walk action tail
    pure (first :: rest)

/-- A successful traversal has exactly one successful result for each input position. -/
theorem walk_exact (action : α → Option β) (input : List α) (output : List β) :
    walk action input = some output ↔ All₂ (fun original copied => action original = some copied) input output := by
  induction input generalizing output with
  | nil =>
    constructor
    · intro same; cases same; exact .nil
    · intro related; cases related; rfl
  | cons head tail ih =>
    cases first : action head with
    | none =>
      constructor
      · simp [walk, first]
      · intro related; cases related with | cons same _ => rw [first] at same; cases same
    | some value =>
      cases rest : walk action tail with
      | none =>
        constructor
        · simp [walk, first, rest]
        · intro related
          cases related with
          | cons _ tail => have same := (ih _).mpr tail; rw [rest] at same; cases same
      | some values =>
        constructor
        · intro returned
          have same : value :: values = output := by simpa [walk, first, rest] using returned
          subst output
          exact .cons first ((ih _).mp rest)
        · intro related
          cases related with
          | cons head tail =>
            have same := Option.some.inj (first.symm.trans head)
            have tailSame := Option.some.inj (rest.symm.trans ((ih _).mpr tail))
            subst_vars
            simp [walk, first, rest]

/-- Every output member has a corresponding original input member. -/
theorem related_origin (relation : α → β → Prop) {input : List α} {output : List β}
    (paired : All₂ relation input output) (target : β) (member : target ∈ output) :
    ∃ source ∈ input, relation source target := by
  induction paired with
  | nil => simp at member
  | @cons source result sources results head tail ih =>
    rcases List.mem_cons.mp member with same | present
    · subst target; exact ⟨source, by simp, head⟩
    · obtain ⟨original, originalMember, matched⟩ := ih present
      exact ⟨original, by simp [originalMember], matched⟩

/-- Every input position has a corresponding output position. -/
theorem related_target (relation : α → β → Prop) {input : List α} {output : List β}
    (paired : All₂ relation input output) (source : α) (member : source ∈ input) :
    ∃ target ∈ output, relation source target := by
  induction paired with
  | nil => simp at member
  | @cons original result originals results head tail ih =>
    rcases List.mem_cons.mp member with same | present
    · subst source; exact ⟨result, by simp, head⟩
    · obtain ⟨target, targetMember, matched⟩ := ih present
      exact ⟨target, by simp [targetMember], matched⟩

/-- Construct one copied edge after all of its children have been constructed. -/
def buildEdge (children : Nat → Option (Shape (Payload Symbol))) (edge : Edge Nat Symbol) :
    Option (Shape (Payload Symbol)) :=
  (walk children edge.children).map (fun copied => Shape.branch ⟨edge.label, fun term => edge.guard term = true⟩ copied)

/-- Build each constructor's ordered children before the alternative list. -/
def buildRows (graph : Automaton Nat Symbol) (state : Nat)
    (children : Nat → Option (Shape (Payload Symbol))) : Option (Shape (Payload Symbol)) :=
  (walk (buildEdge children) (graph state)).map Shape.alternatives

/-- Pointwise semantics of the child traversal gives the complete copied forest. -/
theorem forest_copy (environment : Env Symbol) (children : Nat → Option (Shape (Payload Symbol)))
    (languages : Env Symbol) (exact : ∀ state copied, children state = some copied → meaning environment copied = languages state)
    (states : List Nat) (shapes : List (Shape (Payload Symbol)))
    (built : walk children states = some shapes) (terms : List (Term Symbol)) :
    forest environment shapes terms ↔ All₂ languages states terms := by
  have paired := (walk_exact children states shapes).mp built
  clear built
  induction paired generalizing terms with
  | nil => cases terms <;> simp only [forest] <;> constructor <;> intro h <;> first | exact .nil | trivial | cases h
  | @cons state shape states shapes headBuilt tail ih =>
    cases terms with
    | nil => simp only [forest]; constructor <;> intro impossible <;> cases impossible
    | cons term terms =>
      simp only [forest, exact state shape headBuilt, ih]
      constructor
      · rintro ⟨head, tail⟩; exact .cons head tail
      · intro related; cases related with | cons head tail => exact ⟨head, tail⟩

/-- A successful row copy has the original body language under its child construction. -/
theorem buildRows_exact (graph : Automaton Nat Symbol) (state : Nat) (environment : Env Symbol)
    (children : Nat → Option (Shape (Payload Symbol))) (languages : Env Symbol)
    (exact : ∀ child copied, children child = some copied → meaning environment copied = languages child)
    (shape : Shape (Payload Symbol)) (built : buildRows graph state children = some shape) :
    meaning environment shape = body graph state languages := by
  unfold buildRows at built
  cases copied : walk (buildEdge children) (graph state) with
  | none => simp [copied] at built
  | some edges =>
    have shapeSame : shape = .alternatives edges := by simpa [copied] using built.symm
    subst shape
    have paired := (walk_exact _ _ _).mp copied
    have rowMeaning : ∀ (original : Edge Nat Symbol) target,
        buildEdge children original = some target →
        ∀ term, meaning environment target term ↔
          ∃ terms, term = .node original.label terms ∧ All₂ languages original.children terms ∧ original.guard term = true := by
      intro original target success term
      unfold buildEdge at success
      cases result : walk children original.children with
      | none => simp [result] at success
      | some shapes =>
        have same : target = Shape.branch ⟨original.label, fun term => original.guard term = true⟩ shapes := by
          simpa [result] using success.symm
        subst target
        simp only [meaning, forest_copy environment children languages exact original.children shapes result]
    funext term
    apply propext
    simp only [meaning, body]
    constructor
    · rintro ⟨⟨target, member⟩, accepted⟩
      obtain ⟨original, member, success⟩ := related_origin _ paired target member
      exact ⟨original, member, (rowMeaning original target success term).mp accepted⟩
    · rintro ⟨original, member, accepted⟩
      obtain ⟨target, member, success⟩ := related_target _ paired original member
      exact ⟨⟨target, member⟩, (rowMeaning original target success term).mpr accepted⟩

/-- The source adds a binder only at a cycle-selected state in the current context. -/
def build (graph : Automaton Nat Symbol) (cyclic : List Nat → Nat → Bool) :
    Nat → List Nat → Nat → Option (Shape (Payload Symbol))
  | 0, _, _ => none
  | fuel + 1, active, state =>
    if state ∈ active then
      if cyclic active state then
        (buildRows graph state (build graph cyclic fuel (active.erase state))).map (fun body => cleanup (.binder state body))
      else buildRows graph state (build graph cyclic fuel active)
    else some (.ref state)

/-- An active root run exposes exactly one original constructor body. -/
theorem run_body (graph : Automaton Nat Symbol) (active : List Nat) (environment : Env Symbol)
    (state : Nat) (present : state ∈ active) :
    Run graph active environment state = body graph state (Run graph active environment) := by
  funext term
  apply propext
  constructor
  · intro accepted
    cases accepted with
    | external outside _ => exact False.elim (outside present)
    | node edge children _ member runs guard => exact ⟨edge, member, children, rfl, runs, guard⟩
  · rintro ⟨edge, member, children, rfl, runs, guard⟩; exact .node edge children present member runs guard

/-- Every successfully constructed context has exactly the original open graph language. -/
theorem build_exact (graph : Automaton Nat Symbol) (cyclic : List Nat → Nat → Bool) (fuel : Nat)
    (active : List Nat) (unique : active.Nodup) (state : Nat) (shape : Shape (Payload Symbol))
    (built : build graph cyclic fuel active state = some shape) (environment : Env Symbol) :
    meaning environment shape = Run graph active environment state := by
  induction fuel generalizing active state shape environment with
  | zero => simp [build] at built
  | succ fuel ih =>
    by_cases present : state ∈ active
    · cases chosen : cyclic active state with
      | false =>
        have rowsBuilt : buildRows graph state (build graph cyclic fuel active) = some shape := by
          simpa [build, present, chosen] using built
        rw [buildRows_exact graph state environment _ _ (fun child copied success => ih active unique child copied success environment) shape rowsBuilt]
        exact (run_body graph active environment state present).symm
      | true =>
        have mapped : (buildRows graph state (build graph cyclic fuel (active.erase state))).map
            (fun body => cleanup (.binder state body)) = some shape := by simpa [build, present, chosen] using built
        obtain ⟨bodyShape, rowsBuilt, shapeSame⟩ := Option.map_eq_some_iff.mp mapped
        subst shape
        rw [cleanup_exact]
        simp only [meaning]
        have bodyExact : ∀ value,
            meaning (BinderLanguage.bind environment state value) bodyShape = step graph active environment state value := by
          intro value
          exact buildRows_exact graph state _ _ _
            (fun child copied success => ih _ (unique.erase state) child copied success _) bodyShape rowsBuilt
        rw [least_congr _ _ (fun value term => by rw [bodyExact value])]
        funext term
        exact propext (least_exact graph active environment state unique present term)
    · have same : shape = .ref state := by simpa [build, present] using built.symm
      subst shape
      funext term
      simpa only [meaning] using propext (external_exact graph active environment state present term).symm

end MicroCFTA.BinderSchedule
