import MicroCFTA.BinderSchedule
import MicroCFTA.SymbolicHashJoin

/-!
# The recursive interned intersection schedule

This port follows `Interned.Operations.intersectOpen` in source guard order.
Interned payloads are read through a finite graph view. Recursive references
share their binder identity but retain the source's separate ordering tag.
The result uses explicit recursive syntax before physical interning.
Memo hits and identity allocation remain separate representation steps.
-/
namespace MicroCFTA.IntersectSchedule
open Language Binding BinderLanguage
variable {α β : Type}

/-- Fully interned inputs exclude unresolved source placeholders. -/
inductive Input where
  | empty
  | node (identity : Nat)
  | mu (identity : Nat)
  | union (identity : Nat)
  | ref (identity : Nat)
  deriving DecidableEq, Repr

/-- Source ordering compares a constructor tag before its identity. -/
def tag : Input → Nat
  | .empty => 0
  | .node _ => 1
  | .mu _ => 2
  | .union _ => 3
  | .ref _ => 4

/-- A recursive occurrence and its binder have the same identity. -/
def identity : Input → Nat
  | .empty => 0
  | .node name | .mu name | .union name | .ref name => name

/-- The source's node comparison retains the recursive-reference tag. -/
def greater (left right : Input) : Bool :=
  decide (tag right < tag left ∨ (tag right = tag left ∧ identity right < identity left))

/-- A repeated intersection has one name for either operand order. -/
abbrev Pair := Nat × Nat

/-- Source `IntersectId` orders identities independently of node tags. -/
def pair (left right : Input) : Pair :=
  (min (identity left) (identity right), max (identity left) (identity right))

/-- Every intersection reference has a distinct natural binder name. -/
def pairName (key : Pair) : Nat := key.2 * key.2 + key.1

/-- A stored constructor row retains its complete executable guard. -/
structure Row (Symbol : Type) where
  label : Symbol
  children : List Input
  guard : Term Symbol → Bool

/-- The graph view separates interned payload reads from recursive scheduling. -/
structure View (Symbol : Type) where
  rows : Nat → List (Row Symbol)
  body : Nat → Input
  members : Nat → List Input
  free : Input → List Nat
  copy : Input → Shape (Payload Symbol)

/-- The source checks cached free variables for each closed-input shortcut. -/
def closed (view : View Symbol) (input : Input) : Bool := (view.free input).isEmpty

/-- An intersection domain retains enclosing binders and already introduced pairs. -/
structure Domain where
  free : List (Nat × Input) := []
  seen : List Pair := []
  deriving DecidableEq, Repr

/-- Read a free recursive binder from the current domain. -/
def lookup (domain : Domain) (name : Nat) : Option Input :=
  (domain.free.find? fun entry => entry.1 == name).map Prod.snd

/-- New bindings override the old map; the last repeated new binding wins. -/
def extend (domain : Domain) (bindings : List (Nat × Input)) (key : Pair) : Domain :=
  ⟨bindings.reverse ++ domain.free, key :: domain.seen⟩

/-- Source binder construction also removes an unused binder or a self-only binder. -/
def maybeMu (key : Pair) (body : Shape (Payload Symbol)) : Shape (Payload Symbol) :=
  cleanup (.binder (pairName key) body)

/-- Bounded execution distinguishes exhaustion from an unresolved free reference. -/
inductive Error where
  | fuelExhausted
  | missingBinder (name : Nat)
  deriving DecidableEq, Repr

/-- Visit each input in order and retain every returned element. -/
def walk (action : α → Except Error β) : List α → Except Error (List β)
  | [] => .ok []
  | first :: rest => do
    let value ← action first
    let values ← walk action rest
    pure (value :: values)

/-- Match exactly the source's equal-symbol hash join, preserving every matching row pair. -/
def joined [DecidableEq Symbol] (left right : List (Row Symbol)) : List (Row Symbol × Row Symbol) :=
  SymbolicHashJoin.hashJoin Row.label (fun a b => (a, b)) left right

mutual
  /-- Execute the source guard order before examining recursive and constructor payloads. -/
  def run [DecidableEq Symbol] (view : View Symbol) :
      Nat → Domain → Input → Input → Except Error (Shape (Payload Symbol))
    | 0, _, _, _ => .error .fuelExhausted
    | fuel + 1, domain, left, right =>
      if left = .empty ∨ right = .empty then .ok .empty
      else if closed view left && closed view right && !domain.free.isEmpty then
        run view fuel {} left right
      else if left = right ∧ closed view left then .ok (view.copy left)
      else if greater left right then run view fuel domain right left
      else if pair left right ∈ domain.seen then .ok (.ref (pairName (pair left right)))
      else match left, right with
      | .mu first, .mu second =>
        (run view fuel (extend domain [(first, left), (second, right)] (pair left right))
          (view.body first) (view.body second)).map (maybeMu (pair left right))
      | .mu first, _ =>
        (run view fuel (extend domain [(first, left)] (pair left right)) (view.body first) right).map
          (maybeMu (pair left right))
      | _, .mu second =>
        (run view fuel (extend domain [(second, right)] (pair left right)) left (view.body second)).map
          (maybeMu (pair left right))
      | .union first, _ =>
        (walk (fun member => run view fuel domain member right) (view.members first)).map Shape.alternatives
      | _, .union second =>
        (walk (fun member => run view fuel domain left member) (view.members second)).map Shape.alternatives
      | .ref name, _ => match lookup domain name with
        | none => .error (.missingBinder name)
        | some binder => run view fuel domain binder right
      | _, .ref name => match lookup domain name with
        | none => .error (.missingBinder name)
        | some binder => run view fuel domain left binder
      | .node first, .node second =>
        (walk (fun rows => edge view fuel domain rows.1 rows.2) (joined (view.rows first) (view.rows second))).map
          Shape.alternatives
      | .empty, _ | _, .empty => .ok .empty

  /-- Unequal arities produce an empty edge; equal arities intersect ordered children and conjoin guards. -/
  def edge [DecidableEq Symbol] (view : View Symbol) :
      Nat → Domain → Row Symbol → Row Symbol → Except Error (Shape (Payload Symbol))
    | 0, _, _, _ => .error .fuelExhausted
    | fuel + 1, domain, left, right =>
      if left.children.length ≠ right.children.length then .ok .empty
      else (walk (fun children => run view fuel domain children.1 children.2)
        (left.children.zip right.children)).map fun children =>
          .branch ⟨left.label, fun term => left.guard term = true ∧ right.guard term = true⟩ children
end

/-- Shared recursive identity is explicit; the source ordering tag remains different. -/
theorem recursive_identity (name : Nat) :
    identity (.ref name) = identity (.mu name) ∧ tag (.ref name) ≠ tag (.mu name) := by
  exact ⟨rfl, by simp [tag]⟩

/-- Canonical intersection names ignore operand order. -/
theorem pair_symmetric (left right : Input) : pair left right = pair right left := by
  simp [pair, Nat.min_comm, Nat.max_comm]

/-- A canonical pair name uniquely determines both stored identities. -/
theorem pairName_injective (left right : Pair)
    (leftOrdered : left.1 ≤ left.2) (rightOrdered : right.1 ≤ right.2)
    (same : pairName left = pairName right) : left = right := by
  have gap : ∀ a b : Nat, a < b → a * a + a < b * b := by
    intro a b smaller
    have squared := Nat.mul_le_mul (show a + 1 ≤ b by omega) (show a + 1 ≤ b by omega)
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one] at squared
    omega
  have sameUpper : left.2 = right.2 := by
    apply Classical.byContradiction
    intro different
    rcases Nat.lt_or_gt_of_ne different with smaller | smaller
    · have apart := gap left.2 right.2 smaller
      unfold pairName at same
      omega
    · have apart := gap right.2 left.2 smaller
      unfold pairName at same
      omega
  apply Prod.ext
  · unfold pairName at same
    rw [sameUpper] at same
    omega
  · exact sameUpper

/-- A source canonical-order swap cannot request another swap at the next step. -/
theorem greater_asymmetric (left right : Input) (larger : greater left right = true) :
    greater right left = false := by
  simp only [greater, decide_eq_true_eq] at larger
  simp only [greater, decide_eq_false_iff_not]
  omega

/-- The optional binder has exactly the least recursive language of its body. -/
theorem maybeMu_exact (environment : Env Symbol) (key : Pair) (body : Shape (Payload Symbol)) :
    meaning environment (maybeMu key body) = meaning environment (.binder (pairName key) body) :=
  cleanup_exact environment _

/-- A completed mapping has one completed original value. -/
theorem map_success (action : Except Error α) (convert : α → β) (result : β)
    (completed : action.map convert = .ok result) :
    ∃ value, action = .ok value ∧ convert value = result := by
  cases action with
  | error error => cases completed
  | ok value => exact ⟨value, rfl, Except.ok.inj completed⟩

/-- A successful traversal retains exactly the ordered successful input executions. -/
theorem walk_exact (action : α → Except Error β) (inputs : List α) (outputs : List β)
    (completed : walk action inputs = .ok outputs) :
    All₂ (fun input output => action input = .ok output) inputs outputs := by
  induction inputs generalizing outputs with
  | nil => cases completed; exact .nil
  | cons first rest ih =>
    cases headRun : action first with
    | error error => simp only [walk, headRun, Bind.bind, Except.bind] at completed; cases completed
    | ok value =>
      cases tailRun : walk action rest with
      | error error => simp only [walk, headRun, tailRun, Bind.bind, Except.bind] at completed; cases completed
      | ok values =>
        have same : value :: values = outputs := by
          simpa [walk, headRun, tailRun, Bind.bind, Except.bind, Pure.pure, Except.pure] using completed
        subst outputs
        exact .cons headRun (ih values tailRun)

/-- Every output free reference names an enclosing intersection pair. -/
def Scoped (seen : List Pair) (shape : Shape Item) : Prop :=
  ∀ name ∈ Binding.free shape, ∃ key ∈ seen, name = pairName key

/-- Removing optional binders cannot add a free reference. -/
theorem cleanup_free (shape : Shape (Payload Symbol)) (name : Nat)
    (present : name ∈ Binding.free (cleanup shape)) : name ∈ Binding.free shape := by
  cases shape with
  | binder bound body =>
    by_cases unused : bound ∉ Binding.free body
    · have member : name ∈ Binding.free body := by simpa [cleanup, unused] using present
      have different : name ≠ bound := fun same => unused (same ▸ member)
      simp [Binding.free, member, different]
    · cases body with
      | ref other =>
        by_cases same : other = bound
        · subst other; simp [cleanup, Binding.free] at present
        · simpa [cleanup, unused, same] using present
      | empty => exact present
      | branch => simpa [cleanup, unused] using present
      | alternatives => simpa [cleanup, unused] using present
      | binder => simpa [cleanup, unused] using present
  | empty => exact present
  | ref => exact present
  | branch => exact present
  | alternatives => exact present

/-- Binding the newly introduced pair discharges only its own free references. -/
theorem maybeMu_scoped (seen : List Pair) (key : Pair) (body : Shape (Payload Symbol))
    (scope : Scoped (key :: seen) body) : Scoped seen (maybeMu key body) := by
  intro name present
  have member := cleanup_free (.binder (pairName key) body) name present
  have inside : name ∈ Binding.free body ∧ name ≠ pairName key := by simpa [Binding.free] using member
  obtain ⟨original, member, same⟩ := scope name inside.1
  rcases List.mem_cons.mp member with rfl | member
  · exact False.elim (inside.2 same)
  · exact ⟨original, member, same⟩

/-- Free references of copied closed inputs remain closed. -/
def CopyClosed (view : View Symbol) : Prop :=
  ∀ input, closed view input = true → Binding.free (view.copy input) = []

/-- A scope shape remains scope when more enclosing pairs are available. -/
theorem scoped_mono (before after : List Pair) (shape : Shape Item) (included : before ⊆ after)
    (scope : Scoped before shape) : Scoped after shape := by
  intro name present
  obtain ⟨key, member, same⟩ := scope name present
  exact ⟨key, included member, same⟩

/-- Every free reference in a shape list comes from an actual member. -/
theorem freeList_origin (shapes : List (Shape Item)) (name : Nat) (present : name ∈ freeList shapes) :
    ∃ shape ∈ shapes, name ∈ Binding.free shape := by
  induction shapes with
  | nil => simp [freeList] at present
  | cons shape rest ih =>
    rcases List.mem_append.mp present with head | tail
    · exact ⟨shape, by simp, head⟩
    · obtain ⟨origin, member, free⟩ := ih tail
      exact ⟨origin, by simp [member], free⟩

/-- Copied alternatives introduce no free references outside their children. -/
theorem alternatives_scoped (seen : List Pair) (shapes : List (Shape Item))
    (scope : ∀ shape ∈ shapes, Scoped seen shape) : Scoped seen (.alternatives shapes) := by
  intro name present
  obtain ⟨shape, member, free⟩ := freeList_origin shapes name present
  exact scope shape member name free

/-- Copied constructor rows introduce no free references outside their children. -/
theorem branch_scoped (seen : List Pair) (payload : Item) (shapes : List (Shape Item))
    (scope : ∀ shape ∈ shapes, Scoped seen shape) : Scoped seen (.branch payload shapes) := by
  intro name present
  obtain ⟨shape, member, free⟩ := freeList_origin shapes name present
  exact scope shape member name free

/-- Every successful list traversal inherits the input workers' scope invariant. -/
theorem walk_scoped (action : α → Except Error (Shape Item)) (inputs : List α) (shapes : List (Shape Item))
    (seen : List Pair) (correct : ∀ input ∈ inputs, ∀ shape, action input = .ok shape → Scoped seen shape)
    (completed : walk action inputs = .ok shapes) : ∀ shape ∈ shapes, Scoped seen shape := by
  intro shape member
  obtain ⟨input, member, run⟩ := BinderSchedule.related_origin _ (walk_exact action inputs shapes completed) shape member
  exact correct input member shape run

/-- The actual recursive schedule never leaves a fresh intersection placeholder outside its binder. -/
theorem run_scoped [DecidableEq Symbol] (view : View Symbol) (copyClosed : CopyClosed view) (fuel : Nat) :
    (∀ domain left right result, run view fuel domain left right = .ok result → Scoped domain.seen result) ∧
    (∀ domain left right result, edge view fuel domain left right = .ok result → Scoped domain.seen result) := by
  induction fuel with
  | zero =>
    constructor <;> intro domain left right result completed <;> cases completed
  | succ fuel ih =>
    constructor
    · intro domain left right result completed
      rw [run.eq_def] at completed
      dsimp only at completed
      by_cases empty : left = .empty ∨ right = .empty
      · rw [ite_eq_left empty] at completed
        cases completed
        intro name present
        simp [Binding.free] at present
      rw [ite_eq_right empty] at completed
      by_cases reset : (closed view left && closed view right && !domain.free.isEmpty) = true
      · rw [ite_eq_left reset] at completed
        exact scoped_mono [] domain.seen result (by simp) (ih.1 {} left right result completed)
      rw [ite_eq_right reset] at completed
      by_cases same : left = right ∧ closed view left = true
      · rw [ite_eq_left same] at completed
        cases completed
        intro name present
        rw [copyClosed left same.2] at present
        cases present
      rw [ite_eq_right same] at completed
      by_cases swap : greater left right = true
      · rw [ite_eq_left swap] at completed
        exact ih.1 domain right left result completed
      rw [ite_eq_right swap] at completed
      by_cases seen : pair left right ∈ domain.seen
      · rw [ite_eq_left seen] at completed
        cases completed
        intro name member
        have same : name = pairName (pair left right) := by simpa [Binding.free] using member
        exact ⟨pair left right, seen, same⟩
      rw [ite_eq_right seen] at completed
      split at completed
      · obtain ⟨body, built, rfl⟩ := map_success _ _ _ completed
        exact maybeMu_scoped _ _ body (ih.1 _ _ _ body built)
      · obtain ⟨body, built, rfl⟩ := map_success _ _ _ completed
        exact maybeMu_scoped _ _ body (ih.1 _ _ _ body built)
      · obtain ⟨body, built, rfl⟩ := map_success _ _ _ completed
        exact maybeMu_scoped _ _ body (ih.1 _ _ _ body built)
      · obtain ⟨shapes, built, rfl⟩ := map_success _ _ _ completed
        exact alternatives_scoped _ _ (walk_scoped _ _ _ _ (fun input _ shape success => ih.1 _ _ _ shape success) built)
      · obtain ⟨shapes, built, rfl⟩ := map_success _ _ _ completed
        exact alternatives_scoped _ _ (walk_scoped _ _ _ _ (fun input _ shape success => ih.1 _ _ _ shape success) built)
      · split at completed
        · cases completed
        · exact ih.1 _ _ _ result completed
      · split at completed
        · cases completed
        · exact ih.1 _ _ _ result completed
      · obtain ⟨shapes, built, rfl⟩ := map_success _ _ _ completed
        exact alternatives_scoped _ _ (walk_scoped _ _ _ _ (fun input _ shape success => ih.2 _ _ _ shape success) built)
      · cases completed; intro name present; simp [Binding.free] at present
      · cases completed; intro name present; simp [Binding.free] at present
    · intro domain left right result completed
      rw [edge.eq_def] at completed
      dsimp only at completed
      split at completed
      · cases completed; intro name present; simp [Binding.free] at present
      · obtain ⟨shapes, built, rfl⟩ := map_success _ _ _ completed
        exact branch_scoped _ _ _ (walk_scoped _ _ _ _ (fun input _ shape success => ih.1 _ _ _ shape success) built)

/-- A completed top-level intersection has no unresolved recursive placeholders. -/
theorem top_closed [DecidableEq Symbol] (view : View Symbol) (copyClosed : CopyClosed view)
    (fuel : Nat) (left right : Input) (result : Shape (Payload Symbol))
    (completed : run view fuel {} left right = .ok result) : Binding.free result = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro name present
  obtain ⟨key, impossible, _⟩ := (run_scoped view copyClosed fuel).1 {} left right result completed name present
  cases impossible

/-- A larger execution bound preserves each successfully completed mapped result. -/
theorem map_preserve (before after : Except Error α) (convert : α → β)
    (preserves : ∀ value, before = .ok value → after = .ok value)
    (result : β) (completed : before.map convert = .ok result) : after.map convert = .ok result := by
  obtain ⟨value, built, rfl⟩ := map_success before convert result completed
  rw [preserves value built]
  rfl

/-- Pointwise preservation of successful workers preserves their full ordered traversal. -/
theorem walk_preserve (before after : α → Except Error β) (inputs : List α)
    (preserves : ∀ input ∈ inputs, ∀ result, before input = .ok result → after input = .ok result)
    (results : List β) (completed : walk before inputs = .ok results) : walk after inputs = .ok results := by
  induction inputs generalizing results with
  | nil => exact completed
  | cons first rest ih =>
    cases headRun : before first with
    | error error => simp [walk, headRun, Bind.bind, Except.bind] at completed
    | ok value =>
      cases tailRun : walk before rest with
      | error error => simp [walk, headRun, tailRun, Bind.bind, Except.bind] at completed
      | ok values =>
        have same : value :: values = results := by
          simpa [walk, headRun, tailRun, Bind.bind, Except.bind, Pure.pure, Except.pure] using completed
        subst results
        have head := preserves first (by simp) value headRun
        have tail := ih (fun input member => preserves input (by simp [member])) values tailRun
        simp [walk, head, tail, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Increasing fuel by one preserves every completed source schedule result. -/
theorem run_successor [DecidableEq Symbol] (view : View Symbol) (fuel : Nat) :
    (∀ domain left right result, run view fuel domain left right = .ok result →
      run view (fuel + 1) domain left right = .ok result) ∧
    (∀ domain left right result, edge view fuel domain left right = .ok result →
      edge view (fuel + 1) domain left right = .ok result) := by
  induction fuel with
  | zero => constructor <;> intro domain left right result completed <;> cases completed
  | succ fuel ih =>
    constructor
    · intro domain left right result completed
      rw [run.eq_def] at completed ⊢
      dsimp only at completed ⊢
      by_cases empty : left = .empty ∨ right = .empty
      · rw [ite_eq_left empty] at completed ⊢; exact completed
      rw [ite_eq_right empty] at completed ⊢
      by_cases reset : (closed view left && closed view right && !domain.free.isEmpty) = true
      · rw [ite_eq_left reset] at completed ⊢; exact ih.1 {} left right result completed
      rw [ite_eq_right reset] at completed ⊢
      by_cases same : left = right ∧ closed view left = true
      · rw [ite_eq_left same] at completed ⊢; exact completed
      rw [ite_eq_right same] at completed ⊢
      by_cases swap : greater left right = true
      · rw [ite_eq_left swap] at completed ⊢; exact ih.1 domain right left result completed
      rw [ite_eq_right swap] at completed ⊢
      by_cases seen : pair left right ∈ domain.seen
      · rw [ite_eq_left seen] at completed ⊢; exact completed
      rw [ite_eq_right seen] at completed ⊢
      split at completed
      · exact map_preserve _ _ _ (ih.1 _ _ _) result completed
      · exact map_preserve _ _ _ (ih.1 _ _ _) result completed
      · exact map_preserve _ _ _ (ih.1 _ _ _) result completed
      · exact map_preserve _ _ _ (walk_preserve _ _ _ (fun input _ => ih.1 _ _ _)) result completed
      · exact map_preserve _ _ _ (walk_preserve _ _ _ (fun input _ => ih.1 _ _ _)) result completed
      · split at completed
        · cases completed
        · exact ih.1 _ _ _ result completed
      · split at completed
        · cases completed
        · exact ih.1 _ _ _ result completed
      · exact map_preserve _ _ _ (walk_preserve _ _ _ (fun input _ => ih.2 _ _ _)) result completed
      · exact completed
      · exact completed
    · intro domain left right result completed
      rw [edge.eq_def] at completed ⊢
      dsimp only at completed ⊢
      by_cases different : left.children.length ≠ right.children.length
      · rw [ite_eq_left different] at completed ⊢; exact completed
      · rw [ite_eq_right different] at completed ⊢
        exact map_preserve _ _ _ (walk_preserve _ _ _ (fun input _ => ih.1 _ _ _)) result completed

/-- A successful bounded result is unchanged at every larger bound. -/
theorem run_stable [DecidableEq Symbol] (view : View Symbol) (fuel larger : Nat) (enough : fuel ≤ larger)
    (domain : Domain) (left right : Input) (result : Shape (Payload Symbol))
    (completed : run view fuel domain left right = .ok result) : run view larger domain left right = .ok result := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le enough
  induction extra with
  | zero => exact completed
  | succ extra ih => exact (run_successor view (fuel + extra)).1 domain left right result (ih (by omega))

end MicroCFTA.IntersectSchedule
