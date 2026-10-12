import MicroCFTA.SupportTerms
import MicroCFTA.SupportClosing

/-!
# Recursive occurrence closing mismatch

The source support for `recur (oneof [pure, node s self])` wraps its unresolved
reference as one child. The old term callback closes the realized recursive
term instead. It can remove the choice and pure roots across that boundary.
-/
namespace MicroCFTA.RecursiveSupportBoundary
open Language GeneratorCombinators SupportTerms

/-- The source's three constructor states after exposing the recursive binder. -/
def source : Automaton Nat (Label Nat)
  | 0 => [⟨.choice 0, [1], fun _ => true⟩, ⟨.choice 1, [2], fun _ => true⟩]
  | 1 => [⟨.pure, [], fun _ => true⟩]
  | 2 => [⟨.user 7, [0], fun _ => true⟩]
  | _ => []

/-- The zero-size base term selected by the recursive decoder. -/
def base : Term (Label Nat) := .node (.choice 0) [.node .pure []]

/-- The next decoder term applies the ordinary term closer across the occurrence. -/
def first : Term (Label Nat) := .node (.choice 1) [labelTerm 7 base]

/-- The source graph correctly accepts its base term. -/
theorem base_accepted : Accepts source 0 base := by
  exact ((mem_enumerate_iff source 2 0 base).mp (by decide +kernel)).1

/-- The next selected term has lost the recursive child expected by the support. -/
theorem first_shape : first = .node (.choice 1) [.node (.user 7) []] := by
  simp [first, base, labelTerm]

/-- A decoded finite term lies outside the source recursive support. -/
theorem decoded_not_accepted : ¬Accepts source 0 first := by
  intro accepted
  have listed := (mem_enumerate_iff source 2 0 first).mpr
    ⟨accepted, by simp [first_shape, Term.height]⟩
  have absent : first ∉ enumerate source 2 0 := by decide +kernel
  exact absent listed

/-- Wrapping the complete recursive term retains the source's required child. -/
def wrappedFirst : Term (Label Nat) := .node (.choice 1) [.node (.user 7) [base]]

/-- The term that respects the occurrence boundary is accepted by the same support. -/
theorem wrapped_accepted : Accepts source 0 wrappedFirst := by
  exact ((mem_enumerate_iff source 4 0 wrappedFirst).mp (by decide +kernel)).1

/-- The mismatch is in engine structure; both terms have the same user surface. -/
theorem same_surface : surface first = surface wrappedFirst := by
  simp [first_shape, wrappedFirst, base, surface, surfaceForest]

/-- The repaired source retains one private boundary around each recursive member. -/
def wrap (term : Term (Label Symbol)) : Term (Label Symbol) := .node .recursion [term]

/-- The inverse accepts exactly one child under the same private boundary. -/
def unwrap : Term (Label Symbol) → Option (Term (Label Symbol))
  | .node .recursion [term] => some term
  | _ => none

/-- Every wrapped selected term retains an exact inverse. -/
theorem unwrap_wrap (term : Term (Label Symbol)) : unwrap (wrap term) = some term := rfl

/-- Distinct recursive member terms cannot merge at the new boundary. -/
theorem wrap_injective (left right : Term (Label Symbol)) (same : wrap left = wrap right) : left = right := by
  simpa [wrap] using same

/-- Closing a parent treats a recursive member as one complete child. -/
theorem label_wrap (symbol : Symbol) (term : Term (Label Symbol)) :
    labelTerm symbol (wrap term) = .node (.user symbol) [wrap term] := by
  simp [wrap, labelTerm, applicationTermChildren]

/-- A recursive function member remains complete on the left of an application. -/
theorem spine_wrap (term : Term (Label Symbol)) : applicationLeftChildren (wrap term) = [wrap term] := by
  simp [wrap, applicationLeftChildren, applicationTermChildren]

/-- The private boundary adds no user constructor or child. -/
theorem surface_wrap (term : Term (Label Symbol)) : surface (wrap term) = surface term := by
  simp [wrap, surface, surfaceForest]

/-- The repair changes only the stored engine term of each member. -/
def wrapMember (member : Member Symbol Value) : Member Symbol Value := {member with term := wrap member.term}

/-- Decoded values and their complete weighted distribution are unchanged. -/
theorem wrapped_values (members : Finite Symbol Value) :
    values (Probability.map wrapMember members) = values members := by
  simp [values, Probability.map, wrapMember, List.map_map]

/-- Wrapping preserves every member position, mass, and size. -/
theorem wrapped_select (members : Finite Symbol Value) (rank : Nat) :
    select (Probability.map wrapMember members) rank =
      (select members rank).map (fun entry => (entry.1, wrapMember entry.2)) := by
  simp [select, Probability.map, List.getElem?_map]

/-- The corresponding support wrapper has precisely the same image language. -/
theorem support_wrap (environment : BinderLanguage.Env (Label Symbol)) (body : SupportGraph.Support Symbol)
    (term : Term (Label Symbol)) :
    BinderLanguage.meaning environment (SupportGraph.edge .recursion [body]) term ↔
      ∃ original, BinderLanguage.meaning environment body original ∧ term = wrap original :=
  SupportClosing.unary_exact environment .recursion body term

/-- The repaired fixed-point graph stores the boundary inside its recursive body. -/
def repaired : Automaton Nat (Label Nat)
  | 0 => [⟨.recursion, [3], fun _ => true⟩]
  | 1 => [⟨.pure, [], fun _ => true⟩]
  | 2 => [⟨.user 7, [0], fun _ => true⟩]
  | 3 => [⟨.choice 0, [1], fun _ => true⟩, ⟨.choice 1, [2], fun _ => true⟩]
  | _ => []

/-- The repaired decoder retains the boundary at the base and every recursive use. -/
def selected : Nat → Term (Label Nat)
  | 0 => wrap base
  | n + 1 => wrap (.node (.choice 1) [labelTerm 7 (selected n)])

/-- Every term in the example's repaired recursive stream is accepted. -/
theorem selected_accepted (count : Nat) : Accepts repaired 0 (selected count) := by
  induction count with
  | zero => exact ((mem_enumerate_iff repaired 3 0 (selected 0)).mp (by decide +kernel)).1
  | succ count ih =>
      have wrapped : ∃ body, selected count = wrap body := by cases count <;> exact ⟨_, rfl⟩
      obtain ⟨body, same⟩ := wrapped
      rw [selected, same, label_wrap]
      simp only [wrap]
      apply Accepts.node (A := repaired) (q := 0) ⟨Label.recursion, [3], fun _ => true⟩ _ (by simp [repaired])
      · apply All₂.cons ?_ .nil
        apply Accepts.node (A := repaired) (q := 3) ⟨Label.choice 1, [2], fun _ => true⟩ _ (by simp [repaired])
        · apply All₂.cons ?_ .nil
          apply Accepts.node (A := repaired) (q := 2) ⟨Label.user 7, [0], fun _ => true⟩ _ (by simp [repaired])
          · exact .cons (by simpa only [same, wrap] using ih) .nil
          · rfl
        · rfl
      · rfl

end MicroCFTA.RecursiveSupportBoundary
