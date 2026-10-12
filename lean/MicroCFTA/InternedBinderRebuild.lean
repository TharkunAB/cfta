import MicroCFTA.LexicalExposureLanguage
import MicroCFTA.IntersectSchedule

/-!
# Closed substitution through a rebuilt source binder

The source substitution plan restricts the external environment, inserts the
new local reference, constructs the binder, and applies createMu cleanup.
This adapter proves that step from its operations. It permits a new binder
identity. It does not assume an alpha-renaming or language equation.
-/
namespace MicroCFTA.InternedBinderRebuild
open Language Binding BinderLanguage EnumerationBinderExposure LexicalBinderClosure

/-- A finite syntax bound supplies a reference outside the listed names. -/
def ceiling : List Nat → Nat
  | [] => 0
  | name :: rest => max (name + 1) (ceiling rest)

/-- Every listed name is smaller than the computed finite bound. -/
theorem below_ceiling (names : List Nat) (name : Nat) (member : name ∈ names) :
    name < ceiling names := by
  induction names with
  | nil => simp at member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · simp only [ceiling]
        omega
      · have smaller := ih member
        simp only [ceiling]
        omega

/-- Include both free and bound references, and the old binder identity. -/
def freshName (name : Nat) (body : Shape Item) : Nat :=
  ceiling (name :: free body ++ bound body)

/-- The chosen reference differs from every reference that can affect renaming. -/
theorem freshName_absent (name : Nat) (body : Shape Item) :
    freshName name body ≠ name ∧ freshName name body ∉ free body ∧
      freshName name body ∉ bound body := by
  have smaller : ∀ other ∈ name :: free body ++ bound body, other < freshName name body :=
    below_ceiling _
  constructor
  · have h := smaller name (by simp)
    omega
  constructor
  · intro member
    exact Nat.lt_irrefl _ (smaller _ (by simp [member]))
  · intro member
    exact Nat.lt_irrefl _ (smaller _ (by simp [member]))

/-- Keep only external free bindings, then override the old local reference. -/
def localBindings (name fresh : Nat) (body : Shape Item) (environment : Environment Item) : Environment Item :=
  fun other => if other = name then some (.ref fresh)
    else restrict (free (.binder name body)) environment other

/-- Execute the source binder reconstruction at its selected new identity. -/
def rebuildAt (name fresh : Nat) (body : Shape (Payload Symbol))
    (environment : Environment (Payload Symbol)) : Shape (Payload Symbol) :=
  cleanup (.binder fresh (substitute (localBindings name fresh body environment) body))

/-- The source returns a closed binder unchanged before it constructs any new binder. -/
def rebuild (name : Nat) (body : Shape (Payload Symbol))
    (environment : Environment (Payload Symbol)) : Shape (Payload Symbol) :=
  if (free (.binder name body)).isEmpty then .binder name body
  else rebuildAt name (freshName name body) body environment

/-- Local-reference insertion is capture-free when its new identity is absent from nested binders. -/
theorem localBindings_fresh (name fresh : Nat) (body : Shape (Payload Symbol))
    (environment : Environment (Payload Symbol)) (closed : ClosedEnvironment environment)
    (unused : fresh ∉ bound body) : Fresh (localBindings name fresh body environment) (bound body) := by
  intro binder member reference replacement found
  by_cases hit : reference = name
  · have same : replacement = .ref fresh := by simpa [localBindings, hit] using found.symm
    simp only [same, free, List.mem_singleton]
    intro equal
    exact unused (equal ▸ member)
  · have present : environment reference = some replacement := by
      by_cases relevant : reference ∈ free (.binder name body)
      · simpa [localBindings, hit, restrict, relevant] using found
      · simp [localBindings, hit, restrict, relevant] at found
    simp [closed reference replacement present]

/-- Closed inserted values do not depend on the interpretation of the new local identity. -/
theorem localBindings_semantics (semantic : Env Symbol) (name fresh : Nat)
    (body : Shape (Payload Symbol)) (environment : Environment (Payload Symbol))
    (closed : ClosedEnvironment environment) (unused : fresh = name ∨ fresh ∉ free body)
    (value : Lang Symbol) :
    meaning (substitutedEnv (BinderLanguage.bind semantic fresh value) (localBindings name fresh body environment)) body =
      meaning (BinderLanguage.bind (substitutedEnv semantic environment) name value) body := by
  apply meaning_congr
  intro reference member
  by_cases hit : reference = name
  · simp [substitutedEnv, localBindings, hit, meaning, BinderLanguage.bind]
  · have relevant : reference ∈ free (.binder name body) := by simp [free, member, hit]
    have different : reference ≠ fresh := by
      intro same
      rcases unused with previous | absent
      · exact hit (same.trans previous)
      · exact absent (same ▸ member)
    simp only [substitutedEnv, localBindings, hit, ↓reduceIte, restrict, relevant]
    cases found : environment reference with
    | none => simp [BinderLanguage.bind, hit, different, substitutedEnv, found]
    | some replacement =>
        simp only [BinderLanguage.bind, hit, ↓reduceIte, substitutedEnv, found]
        apply meaning_congr
        intro other present
        simp [closed reference replacement found] at present

/-- Binder reconstruction and cleanup preserve the exact lexical substitution language. -/
theorem rebuildAt_exact (semantic : Env Symbol) (name fresh : Nat)
    (body : Shape (Payload Symbol)) (environment : Environment (Payload Symbol))
    (closed : ClosedEnvironment environment) (freeUnused : fresh = name ∨ fresh ∉ free body)
    (boundUnused : fresh ∉ bound body) :
    meaning semantic (rebuildAt name fresh body environment) =
      meaning semantic (substitute environment (.binder name body)) := by
  rw [rebuildAt, cleanup_exact]
  rw [substitution_exact (.binder name body) semantic environment (by
    intro binder member reference replacement found
    simp [closed reference replacement found])]
  simp only [meaning]
  apply least_congr
  intro value term
  rw [substitution_exact body (BinderLanguage.bind semantic fresh value) _
    (localBindings_fresh name fresh body environment closed boundUnused)]
  rw [localBindings_semantics semantic name fresh body environment closed freeUnused value]

/-- The actual closed shortcut and a computed finite fresh name need no alpha-equivalence premise. -/
theorem rebuild_exact (semantic : Env Symbol) (name : Nat) (body : Shape (Payload Symbol))
    (environment : Environment (Payload Symbol)) (closed : ClosedEnvironment environment) :
    meaning semantic (rebuild name body environment) =
      meaning semantic (substitute environment (.binder name body)) := by
  unfold rebuild
  split
  · next empty =>
      rw [closed_unchanged (.binder name body) (List.isEmpty_iff.mp empty)]
  · exact rebuildAt_exact semantic name _ body environment closed
      (Or.inr (freshName_absent name body).2.1) (freshName_absent name body).2.2

/-- Reusing the previous identity also preserves the language when no nested binder owns it. -/
theorem reused_identity_exact (semantic : Env Symbol) (name : Nat) (body : Shape (Payload Symbol))
    (environment : Environment (Payload Symbol)) (closed : ClosedEnvironment environment)
    (unique : name ∉ bound body) :
    meaning semantic (rebuildAt name name body environment) =
      meaning semantic (rebuild name body environment) := by
  rw [rebuildAt_exact semantic name name body environment closed (Or.inl rfl) unique,
    rebuild_exact semantic name body environment closed]

/-- Resolving the external references leaves only the newly bound reference in the rebuilt body. -/
theorem localBindings_resolved (name fresh : Nat) (body : Shape (Payload Symbol))
    (environment : Environment (Payload Symbol)) (closed : ClosedEnvironment environment)
    (resolved : Resolved environment (.binder name body)) :
    ∀ reference ∈ free (substitute (localBindings name fresh body environment) body), reference = fresh := by
  apply substitute_free body _ (· = fresh)
  intro reference member
  by_cases hit : reference = name
  · simp [localBindings, hit, free]
  · have relevant : reference ∈ free (.binder name body) := by simp [free, member, hit]
    obtain ⟨replacement, found⟩ := resolved reference relevant
    simp [localBindings, hit, restrict, relevant, found, closed reference replacement found]

/-- Cleanup cannot expose an unresolved reference after all external bindings are supplied. -/
theorem rebuildAt_closed (name fresh : Nat) (body : Shape (Payload Symbol))
    (environment : Environment (Payload Symbol)) (closed : ClosedEnvironment environment)
    (resolved : Resolved environment (.binder name body)) :
    free (rebuildAt name fresh body environment) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro reference member
  have before := IntersectSchedule.cleanup_free
    (.binder fresh (substitute (localBindings name fresh body environment) body)) reference member
  have outside : reference ∈ free (substitute (localBindings name fresh body environment) body) ∧
      reference ≠ fresh := by simpa [free] using before
  exact outside.2 (localBindings_resolved name fresh body environment closed resolved reference outside.1)

/-- The closed shortcut and binder reconstruction both produce a closed result. -/
theorem rebuild_closed (name : Nat) (body : Shape (Payload Symbol))
    (environment : Environment (Payload Symbol)) (closed : ClosedEnvironment environment)
    (resolved : Resolved environment (.binder name body)) :
    free (rebuild name body environment) = [] := by
  unfold rebuild
  split
  · next empty => exact List.isEmpty_iff.mp empty
  · exact rebuildAt_closed name _ body environment closed resolved

/-- Rebuilt closed binders expose exactly the lexical substituted language through the visited worker. -/
theorem rebuild_exposed [DecidableEq (Shape (Payload Symbol))] (semantic : Env Symbol)
    (name : Nat) (body : Shape (Payload Symbol)) (environment : Environment (Payload Symbol))
    (closed : ClosedEnvironment environment) (resolved : Resolved environment (.binder name body))
    (term : Term Symbol) :
    rowsMeaning semantic (exposedRows (rebuild name body environment)) term ↔
      meaning semantic (substitute environment (.binder name body)) term := by
  rw [LexicalExposureLanguage.exposed_language semantic _ (rebuild_closed name body environment closed resolved),
    rebuild_exact semantic name body environment closed]

/-- A rebuilt closed binder exposes no raw recursive reference at any later lexical request. -/
theorem rebuild_no_unexpected_reference (name : Nat) (body : Shape (Payload Symbol))
    (environment : Environment (Payload Symbol)) (closed : ClosedEnvironment environment)
    (resolved : Resolved environment (.binder name body)) (reference : Nat) :
    ¬ Reachable (rebuild name body environment) (.ref reference) :=
  no_unexpected_reference (rebuild_closed name body environment closed resolved) reference

/-- Constructor-depth bounds are independent of the rebuilt binder identity and cleanup result. -/
theorem rebuild_bounded [DecidableEq (Shape (Payload Symbol))] (semantic : Env Symbol)
    (name : Nat) (body : Shape (Payload Symbol)) (environment : Environment (Payload Symbol))
    (closed : ClosedEnvironment environment) (resolved : Resolved environment (.binder name body))
    (height : Nat) (term : Term Symbol) :
    Accepts (BoundDepth.bound LexicalExposureLanguage.automaton)
        (height, rebuild name body environment) term ↔
      meaning semantic (substitute environment (.binder name body)) term ∧ term.height ≤ height := by
  rw [LexicalExposureLanguage.bounded_exact semantic _
    (rebuild_closed name body environment closed resolved), rebuild_exact semantic name body environment closed]

end MicroCFTA.InternedBinderRebuild
