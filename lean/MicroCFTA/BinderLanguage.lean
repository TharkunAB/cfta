import MicroCFTA.Binding
import MicroCFTA.Language

/-!
# Least-language semantics of recursive binders

A binder denotes the least language that contains its body. This definition
applies to open shapes as well as closed shapes. It separates the semantic
requirements of `createMu` from allocation and interning.
-/
namespace MicroCFTA.BinderLanguage
open Language Binding

/-- A language is a predicate on finite constructor terms. -/
abbrev Lang (Symbol : Type) := Term Symbol → Prop

/-- Language inclusion. -/
def Included (left right : Lang Symbol) : Prop := ∀ term, left term → right term

/-- A language transformer preserves inclusion. -/
def Monotone (transform : Lang Symbol → Lang Symbol) : Prop :=
  ∀ left right, Included left right → Included (transform left) (transform right)

/-- The intersection of all languages closed under the transformer. -/
def least (transform : Lang Symbol → Lang Symbol) : Lang Symbol :=
  fun term => ∀ candidate, Included (transform candidate) candidate → candidate term

/-- The least language is included in every closed candidate. -/
theorem least_le (transform : Lang Symbol → Lang Symbol) (candidate : Lang Symbol)
    (closed : Included (transform candidate) candidate) : Included (least transform) candidate :=
  fun _ accepted => accepted candidate closed

/-- Applying a monotone transformer to its least language cannot add a term. -/
theorem least_closed (transform : Lang Symbol → Lang Symbol) (monotone : Monotone transform) :
    Included (transform (least transform)) (least transform) := by
  intro term accepted candidate closed
  exact closed term (monotone _ _ (least_le transform candidate closed) term accepted)

/-- Every term in a least language has one body derivation in that language. -/
theorem least_unfold (transform : Lang Symbol → Lang Symbol) (monotone : Monotone transform) :
    Included (least transform) (transform (least transform)) :=
  least_le transform _ (monotone _ _ (least_closed transform monotone))

/-- Positive recursive binding satisfies its defining language equation. -/
theorem least_fix (transform : Lang Symbol → Lang Symbol) (monotone : Monotone transform)
    (term : Term Symbol) : least transform term ↔ transform (least transform) term :=
  ⟨least_unfold transform monotone term, least_closed transform monotone term⟩

/-- Increasing every body result can only increase the least language. -/
theorem least_mono (left right : Lang Symbol → Lang Symbol)
    (pointwise : ∀ language, Included (left language) (right language)) :
    Included (least left) (least right) := by
  intro term accepted candidate closed
  exact accepted candidate (fun term body => closed term (pointwise candidate term body))

/-- Extensionally equal body transformers have the same least language. -/
theorem least_congr (left right : Lang Symbol → Lang Symbol)
    (same : ∀ language term, left language term ↔ right language term) : least left = least right := by
  funext term
  apply propext
  exact ⟨least_mono left right (fun language term => (same language term).mp) term,
    least_mono right left (fun language term => (same language term).mpr) term⟩

/-- Interpret a free recursive name by a language. -/
abbrev Env (Symbol : Type) := Nat → Lang Symbol

/-- A binder replaces the interpretation of its own recursive name. -/
def bind (environment : Env Symbol) (name : Nat) (value : Lang Symbol) : Env Symbol :=
  fun other => if other = name then value else environment other

/-- The complete non-child payload of one constructor transition. -/
structure Payload (Symbol : Type) where
  label : Symbol
  guard : Term Symbol → Prop

mutual
  /-- Interpret finite syntax, with positive least-language recursive binders. -/
  def meaning (environment : Env Symbol) : Shape (Payload Symbol) → Lang Symbol
    | .empty => fun _ => False
    | .ref name => environment name
    | .branch payload children => fun term =>
        ∃ terms, term = .node payload.label terms ∧ forest environment children terms ∧ payload.guard term
    | .alternatives edges => fun term => ∃ edge : {edge // edge ∈ edges}, meaning environment edge.val term
    | .binder name body => least (fun language => meaning (bind environment name language) body)
  termination_by shape => sizeOf shape
  decreasing_by
    all_goals simp_wf
    all_goals first | omega | (have smaller := List.sizeOf_lt_of_mem edge.property; omega)

  /-- Interpret an ordered child forest without changing its length or order. -/
  def forest (environment : Env Symbol) : List (Shape (Payload Symbol)) → List (Term Symbol) → Prop
    | [], [] => True
    | child :: rest, term :: terms => meaning environment child term ∧ forest environment rest terms
    | _, _ => False
  termination_by shapes _ => sizeOf shapes
  decreasing_by all_goals simp_wf; all_goals omega
end

/-- Component inclusion gives ordered-forest inclusion. -/
theorem forest_mono (children : List (Shape (Payload Symbol))) (left right : Env Symbol)
    (included : ∀ child ∈ children, Included (meaning left child) (meaning right child))
    (terms : List (Term Symbol)) (accepted : forest left children terms) :
    forest right children terms := by
  induction children generalizing terms with
  | nil => cases terms <;> simp_all only [forest]
  | cons child rest ih =>
      cases terms with
      | nil => simp_all only [forest]
      | cons term terms =>
          simp only [forest] at accepted ⊢
          exact ⟨included child (by simp) term accepted.1,
          ih (fun child member => included child (by simp [member])) terms accepted.2⟩

/-- A shape is monotone in every free reference interpretation. -/
theorem meaning_mono (shape : Shape (Payload Symbol)) (left right : Env Symbol)
    (included : ∀ name, Included (left name) (right name)) :
    Included (meaning left shape) (meaning right shape) := by
  induction shape using Shape.rec
    (motive_2 := fun shapes => ∀ left right : Env Symbol,
      (∀ name, Included (left name) (right name)) →
      ∀ shape ∈ shapes, Included (meaning left shape) (meaning right shape))
    generalizing left right with
  | empty => simp [meaning, Included]
  | ref name => simpa only [meaning] using included name
  | branch payload children ih =>
      simp only [meaning, Included]
      rintro term ⟨terms, same, children, guard⟩
      exact ⟨terms, same, forest_mono _ left right (ih left right included) terms children, guard⟩
  | alternatives edges ih =>
      simp only [meaning, Included]
      intro term accepted
      obtain ⟨⟨edge, member⟩, accepted⟩ := accepted
      exact ⟨⟨edge, member⟩, ih left right included edge member term accepted⟩
  | binder name body ih =>
      simp only [meaning]
      apply least_mono
      intro value
      apply ih
      intro other term accepted
      by_cases same : other = name
      · simpa [bind, same] using accepted
      · simpa [bind, same] using included other term (by simpa [bind, same] using accepted)
  | nil => rename_i left right included shape member; simp at member
  | cons child rest ih ihtail =>
      rename_i left right included shape member
      rcases List.mem_cons.mp member with rfl | member
      · exact ih left right included
      · exact ihtail left right included shape member

/-- Component equality preserves the complete child forest. -/
theorem forest_congr (children : List (Shape (Payload Symbol))) (left right : Env Symbol)
    (same : ∀ child ∈ children, meaning left child = meaning right child)
    (terms : List (Term Symbol)) : forest left children terms ↔ forest right children terms := by
  constructor
  · exact forest_mono children left right (fun child member term => by rw [same child member]; exact id) terms
  · exact forest_mono children right left (fun child member term => by rw [same child member]; exact id) terms

/-- A free name of one child is free in its containing forest. -/
theorem freeList_member (shapes : List (Shape Item)) (shape : Shape Item)
    (member : shape ∈ shapes) (name : Nat) (present : name ∈ free shape) : name ∈ freeList shapes := by
  induction shapes with
  | nil => simp at member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · simp [freeList, present]
      · simp [freeList, ih member]

/-- Semantic interpretation depends only on the shape's free recursive names. -/
theorem meaning_congr (shape : Shape (Payload Symbol)) (left right : Env Symbol)
    (agree : ∀ name ∈ free shape, left name = right name) :
    meaning left shape = meaning right shape := by
  induction shape using Shape.rec
    (motive_2 := fun shapes => ∀ left right : Env Symbol,
      (∀ name ∈ freeList shapes, left name = right name) →
      ∀ shape ∈ shapes, meaning left shape = meaning right shape)
    generalizing left right with
  | empty => simp only [meaning]
  | ref name => simpa only [meaning] using agree name (by simp [free])
  | branch payload children ih =>
      funext term
      simp only [meaning]
      have each := ih left right agree
      simp only [forest_congr children left right each]
  | alternatives edges ih =>
      funext term
      apply propext
      simp only [meaning]
      constructor
      · rintro ⟨⟨edge, member⟩, accepted⟩
        exact ⟨⟨edge, member⟩, by rw [← ih left right agree edge member]; exact accepted⟩
      · rintro ⟨⟨edge, member⟩, accepted⟩
        exact ⟨⟨edge, member⟩, by rw [ih left right agree edge member]; exact accepted⟩
  | binder name body ih =>
      simp only [meaning]
      apply least_congr
      intro value term
      have same : meaning (bind left name value) body = meaning (bind right name value) body := by
        apply ih
        intro other present
        by_cases hit : other = name
        · simp [bind, hit]
        · simp [bind, hit, agree other (by simp [free, present, hit])]
      rw [same]
  | nil => rename_i left right agree shape member; simp at member
  | cons child rest ih ihtail =>
      rename_i left right agree shape member
      rcases List.mem_cons.mp member with rfl | member
      · exact ih left right (fun name present => agree name (by simp [freeList, present]))
      · exact ihtail left right (fun name present => agree name (by simp [freeList, present])) shape member

/-- Every shape defines a positive recursive body transformer. -/
theorem binder_monotone (environment : Env Symbol) (name : Nat) (body : Shape (Payload Symbol)) :
    Monotone (fun value => meaning (bind environment name value) body) := by
  intro left right included
  apply meaning_mono
  intro other term accepted
  by_cases hit : other = name
  · simpa [bind, hit] using included term (by simpa [bind, hit] using accepted)
  · simpa [bind, hit] using accepted

/-- Unfolding a binder retains exactly its least language. -/
theorem binder_unfold (environment : Env Symbol) (name : Nat) (body : Shape (Payload Symbol))
    (term : Term Symbol) : meaning environment (.binder name body) term ↔
      meaning (bind environment name (meaning environment (.binder name body))) body term := by
  simpa only [meaning] using least_fix _ (binder_monotone environment name body) term

/-- A body that ignores its recursive language has that language as its least solution. -/
theorem least_constant (value : Lang Symbol) : least (fun _ => value) = value := by
  funext term
  apply propext
  exact ⟨fun accepted => accepted value (fun _ => id), fun accepted _ closed => closed term accepted⟩

/-- Removing an unused binder preserves every accepted term. -/
theorem unused_binder (environment : Env Symbol) (name : Nat) (body : Shape (Payload Symbol))
    (unused : name ∉ free body) : meaning environment (.binder name body) = meaning environment body := by
  simp only [meaning]
  rw [least_congr _ (fun _ => meaning environment body)]
  · exact least_constant _
  · intro value term
    have same : meaning (bind environment name value) body = meaning environment body := by
      apply meaning_congr
      intro other present
      have different : other ≠ name := fun equal => unused (equal ▸ present)
      simp [bind, different]
    rw [same]

/-- A binder whose entire body is its own reference accepts no finite term. -/
theorem self_binder_empty (environment : Env Symbol) (name : Nat) :
    meaning environment (.binder name (.ref name)) = meaning environment .empty := by
  funext term
  apply propext
  simp only [meaning, bind, ite_true]
  constructor
  · intro accepted
    exact accepted (fun _ => False) (fun _ => id)
  · intro impossible; exact impossible.elim

/-- The unused/self-binder cleanup in `createMu`. The preceding root-union
filter in current `createMuDontCleanup` is proved in `BinderSelfUnion`. -/
def cleanup : Shape (Payload Symbol) → Shape (Payload Symbol)
  | .binder name body =>
      if name ∉ free body then body
      else match body with
        | .ref other => if other = name then .empty else .binder name body
        | _ => .binder name body
  | shape => shape

/-- The source binder cleanup preserves exactly the complete term language. -/
theorem cleanup_exact (environment : Env Symbol) (shape : Shape (Payload Symbol)) :
    meaning environment (cleanup shape) = meaning environment shape := by
  cases shape with
  | binder name body =>
      by_cases unused : name ∉ free body
      · simpa only [cleanup, ite_eq_left unused] using (unused_binder environment name body unused).symm
      · simp only [cleanup, ite_eq_right unused]
        cases body with
        | ref other =>
            by_cases same : other = name
            · subst other
              simpa using (self_binder_empty environment name).symm
            · simp [same]
        | empty => rfl
        | branch => rfl
        | alternatives => rfl
        | binder => rfl
  | empty => rfl
  | ref => rfl
  | branch => rfl
  | alternatives => rfl

end MicroCFTA.BinderLanguage
