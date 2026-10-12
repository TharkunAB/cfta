import MicroCFTA.BinderLanguage

/-!
# Removal of a binder reference from its root union

`createMuDontCleanup` removes its own reference from an `InternedUnion` at
the root of the body. It does not remove a reference below a constructor or
another binder. This module proves that operation for least languages.
Allocation, interning, and the normalization in `createUnion` are separate.
-/
namespace MicroCFTA.BinderSelfUnion
open Language Binding BinderLanguage

/-- Test only a bare reference to the selected binder. -/
def isSelf (name : Nat) : Shape Item → Bool
  | .ref other => other == name
  | _ => false

/-- Filter the root alternatives, and leave every other body unchanged. -/
def withoutSelf (name : Nat) : Shape Item → Shape Item
  | .alternatives members => .alternatives (members.filter (fun member => !isSelf name member))
  | body => body

/-- A selected operand is precisely the bare binder reference. -/
theorem isSelf_iff (name : Nat) (body : Shape Item) :
    isSelf name body = true ↔ body = .ref name := by
  cases body <;> simp [isSelf]

/-- Removing the self operand cannot remove any other root alternative. -/
theorem retained_iff (name : Nat) (members : List (Shape Item)) (body : Shape Item) :
    body ∈ members.filter (fun member => !isSelf name member) ↔
      body ∈ members ∧ body ≠ .ref name := by
  cases body <;> simp [isSelf]

/-- Repeating the root filter has no further effect. -/
theorem withoutSelf_idempotent (name : Nat) (body : Shape Item) :
    withoutSelf name (withoutSelf name body) = withoutSelf name body := by
  cases body <;> simp [withoutSelf, List.filter_filter]

/-- The root filter preserves every body with no bare self operand. -/
theorem withoutSelf_unchanged (name : Nat) (members : List (Shape Item))
    (absent : .ref name ∉ members) : withoutSelf name (.alternatives members) = .alternatives members := by
  simp only [withoutSelf]
  congr 1
  apply List.filter_eq_self.mpr
  intro member present
  have different : member ≠ .ref name := fun same => absent (same ▸ present)
  cases member <;> simp_all [isSelf]

/-- A candidate language is closed under the original body exactly when it
is closed under the filtered body. The deleted operand contributes only the
candidate language itself. -/
theorem closed_iff (environment : Env Symbol) (name : Nat)
    (body : Shape (Payload Symbol)) (candidate : Lang Symbol) :
    Included (meaning (bind environment name candidate) (withoutSelf name body)) candidate ↔
      Included (meaning (bind environment name candidate) body) candidate := by
  cases body with
  | alternatives members =>
      simp only [withoutSelf, Included, meaning]
      constructor
      · intro closed term accepted
        obtain ⟨⟨member, present⟩, accepts⟩ := accepted
        by_cases self : member = .ref name
        · simpa [self, meaning, BinderLanguage.bind] using accepts
        · exact closed term ⟨⟨member, (retained_iff name members member).mpr ⟨present, self⟩⟩, accepts⟩
      · intro closed term accepted
        obtain ⟨⟨member, present⟩, accepts⟩ := accepted
        exact closed term ⟨⟨member, (retained_iff name members member).mp present |>.1⟩, accepts⟩
  | empty | ref | branch | binder => rfl

/-- The new source binder normalization preserves every finite term, including
open bodies and bodies with recursive occurrences below constructors. -/
theorem binder_exact (environment : Env Symbol) (name : Nat) (body : Shape (Payload Symbol)) :
    meaning environment (.binder name (withoutSelf name body)) =
      meaning environment (.binder name body) := by
  funext term
  apply propext
  simp only [meaning, least]
  exact ⟨fun accepted candidate closed => accepted candidate ((closed_iff environment name body candidate).mpr closed),
    fun accepted candidate closed => accepted candidate ((closed_iff environment name body candidate).mp closed)⟩

/-- The existing unused/self-binder cleanup remains exact after the new filter. -/
theorem cleanup_exact (environment : Env Symbol) (name : Nat) (body : Shape (Payload Symbol)) :
    meaning environment (BinderLanguage.cleanup (.binder name (withoutSelf name body))) =
      meaning environment (.binder name body) := by
  rw [BinderLanguage.cleanup_exact, binder_exact]

/-- A root self alternative is redundant even when the remaining body is
recursive. No closedness or productivity premise is required. -/
theorem add_self_exact (environment : Env Symbol) (name : Nat)
    (members : List (Shape (Payload Symbol))) :
    meaning environment (.binder name (.alternatives (.ref name :: members))) =
      meaning environment (.binder name (.alternatives members)) := by
  rw [← binder_exact environment name (.alternatives (.ref name :: members)),
    ← binder_exact environment name (.alternatives members)]
  simp [withoutSelf, isSelf]

/-- References below a constructor and references to an outer binder remain. -/
theorem filter_scope (payload : Payload Symbol) :
    withoutSelf 0 (.alternatives [.ref 0, .branch payload [.ref 0], .ref 1]) =
      .alternatives [.branch payload [.ref 0], .ref 1] ∧
    withoutSelf 0 (.binder 1 (.alternatives [.ref 0, .ref 1]) : Shape (Payload Symbol)) =
      .binder 1 (.alternatives [.ref 0, .ref 1]) := by
  simp [withoutSelf, isSelf]

end MicroCFTA.BinderSelfUnion
