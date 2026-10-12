import MicroCFTA.RankedGateCompletion
import MicroCFTA.InternedSubstitution

/-!
# A derived same-path rank for lexical binder reconstruction

Only consecutive binders at the root contribute to the rank. Substitution
can insert a binder at a root reference. An open outer binder cannot have
its own reference at the end of that root chain. This fact supplies the
decrease; the result does not assume a termination certificate.

This adapter uses the existing lexical reconstruction worker. Its union
case retains a list of alternatives. Source union canonicalization can
change that root tag, so its additional representation proof is separate.
-/
namespace MicroCFTA.LexicalGateRank
open Binding BinderLanguage InternedBinderRebuild InternedSubstitution
open ConstrainedRecursionGate

/-- Count consecutive root binders and stop at every other constructor. -/
def headRank : Shape Item → Nat
  | .binder _ body => headRank body + 1
  | _ => 0

/-- A free reference can terminate a root binder chain. Constructor children
and union operands do not participate in that chain. -/
def headReference : Shape Item → Option Nat
  | .ref name => some name
  | .binder name body => match headReference body with
      | none => none
      | some reference => if reference = name then none else some reference
  | _ => none

/-- A root reference chain has exactly one free reference. -/
theorem headReference_free (shape : Shape Item) (reference : Nat)
    (found : headReference shape = some reference) : free shape = [reference] := by
  induction shape using Shape.rec (motive_2 := fun _ => True) with
  | empty | branch | alternatives => simp [headReference] at found
  | ref name => simpa [headReference, free] using found
  | binder name body ih =>
      cases inner : headReference body with
      | none => simp [headReference, inner] at found
      | some other =>
          by_cases same : other = name
          · simp [headReference, inner, same] at found
          · have equal : other = reference := by simpa [headReference, inner, same] using found
            subst other
            simp [free, ih inner, same]
  | nil => trivial
  | cons => trivial

/-- Removing a root self operand does not add a head binder in the lexical worker. -/
theorem withoutSelf_rank (name : Nat) (shape : Shape Item) :
    headRank (BinderSelfUnion.withoutSelf name shape) = headRank shape := by
  cases shape <;> rfl

/-- Cleanup either retains the new binder or removes it. -/
theorem cleanup_rank (name : Nat) (body : Shape (Payload Symbol)) :
    headRank (cleanup (.binder name body)) ≤ headRank body + 1 := by
  simp only [cleanup]
  split
  · omega
  · cases body <;> simp [headRank]
    split <;> simp [headRank]

/-- Only a replacement at the free root reference can increase the head rank. -/
def HeadSmall (environment : Environment Item) (shape : Shape Item) : Prop :=
  ∀ reference replacement, headReference shape = some reference →
    environment reference = some replacement → headRank replacement = 0

/-- Local renaming inserts a reference, and external root substitutions keep
the original environment entry. -/
theorem local_headSmall (next name : Nat) (body : Shape (Payload Symbol))
    (environment : Environment (Payload Symbol))
    (small : HeadSmall environment (.binder name body)) :
    HeadSmall (localBindings name (allocate next name body environment) body environment) body := by
  intro reference replacement head found
  by_cases own : reference = name
  · have equal : replacement = .ref (allocate next name body environment) := by
      simpa [localBindings, own] using found.symm
    simp [equal, headRank]
  · have outer : headReference (.binder name body) = some reference := by
      simp [headReference, head, own]
    have relevant : reference ∈ free (.binder name body) := by
      simp [free, headReference_free body reference head, own]
    apply small reference replacement outer
    simpa [localBindings, own, restrict, relevant] using found

/-- Derive the reconstruction bound from every worker branch. The bound is
independent of the fresh-name supply and the number of nested children. -/
theorem run_rank (shape : Shape (Payload Symbol)) (next : Nat)
    (environment : Environment (Payload Symbol)) (small : HeadSmall environment shape) :
    headRank (run next environment shape).1 ≤ headRank shape := by
  induction shape using Shape.rec (motive_2 := fun _ => True) generalizing next environment with
  | empty => simp [run, free, headRank]
  | ref name =>
      cases found : environment name with
      | none => simp [run, free, found, headRank]
      | some replacement =>
          have zero := small name replacement rfl found
          simp [run, free, found, headRank, zero]
  | branch payload children ih =>
      unfold run
      split <;> simp [headRank]
  | alternatives members ih =>
      unfold run
      split <;> simp [headRank]
  | binder name body ih =>
      unfold run
      split
      · exact Nat.le_refl _
      · have bounded := ih (allocate next name body environment + 1)
          (localBindings name (allocate next name body environment) body environment)
          (local_headSmall next name body environment small)
        exact Nat.le_trans (cleanup_rank _ _) (by simpa [withoutSelf_rank, headRank] using Nat.add_le_add_right bounded 1)
  | nil => trivial
  | cons => trivial

/-- An open binder cannot end its root chain at its own reference. -/
theorem open_headSmall (name : Nat) (body : Shape (Payload Symbol))
    (opened : free (.binder name body) ≠ []) :
    HeadSmall (BinderLanguage.single name (.binder name body)) body := by
  intro reference replacement head found
  by_cases own : reference = name
  · have only := headReference_free body reference head
    exfalso
    apply opened
    simp [free, only, own]
  · simp [BinderLanguage.single, own] at found

/-- Every open binder unfolding strictly decreases consecutive head binders.
The proof uses the actual lexical reconstruction and current root self filter. -/
theorem unfold_decreases (next name : Nat) (body : Shape (Payload Symbol))
    (opened : free (.binder name body) ≠ []) :
    headRank (unfoldRebuilt next name body) < headRank (.binder name body) := by
  have bounded := run_rank body next _ (open_headSmall name body opened)
  exact Nat.lt_of_le_of_lt bounded (Nat.lt_succ_self _)

/-- Compute the cached maximum binder depth over constructor children. -/
def nested : Shape Item → Nat
  | .empty | .ref _ => 0
  | .branch _ children | .alternatives children => (children.map nested).foldl max 0
  | .binder _ body => nested body + 1

/-- The lexical tag view preserves the child order at each constructor. -/
def view : Shape Item → RecursiveReductionBarrier.View (Shape Item)
  | .empty => .empty
  | .ref _ => .reference
  | .branch _ children => .branches [children]
  | .alternatives _ => .union
  | .binder _ _ => .binder

mutual
/-- Read the edge constraint predicate at every stored constructor. -/
def unconstrained (plain : Item → Bool) : Shape Item → Bool
  | .empty | .ref _ => true
  | .branch payload children => plain payload && unconstrainedMany plain children
  | .alternatives members => unconstrainedMany plain members
  | .binder _ body => unconstrained plain body

/-- Every ordered child contributes its stored edge constraints. -/
def unconstrainedMany (plain : Item → Bool) : List (Shape Item) → Bool
  | [] => true
  | first :: rest => unconstrained plain first && unconstrainedMany plain rest
end

/-- Install lexical reconstruction and computed metadata in the current gate. -/
def read (next : Nat) (plain : Payload Symbol → Bool) : Read (Shape (Payload Symbol)) where
  view := view
  nested := nested
  free := free
  unconstrained := unconstrained plain
  unfold := fun shape => match shape with
    | .binder name body => unfoldRebuilt next name body
    | _ => shape

/-- The complete lexical gate has a derived rank. No rank or global
termination premise is accepted from its caller. -/
def ranking (next : Nat) (plain : Payload Symbol → Bool) : UnfoldingRank (read next plain) where
  rank := headRank
  decreases := by
    intro shape binder _ opened
    cases shape with
    | empty | ref | branch | alternatives => simp [read, view] at binder
    | binder name body =>
        apply unfold_decreases
        intro closed
        simp [read, closed] at opened

/-- A completed finite computation agrees with the derived unbounded worker. -/
theorem completed_exact (next : Nat) (plain : Payload Symbol → Bool)
    (fuel : Nat) (path : EqualityNormalize.Path) (shape : Shape (Payload Symbol)) (result : Bool)
    (completed : nodeMeets (read next plain) fuel path shape = some result) :
    total (read next plain) (ranking next plain) path shape = result :=
  completed_agrees _ _ fuel path shape result completed

/-- The same unfold used by the rank also preserves the complete open language. -/
theorem ranked_unfold_exact (next name : Nat) (body : Shape (Payload Symbol))
    (environment : Env Symbol) :
    meaning environment ((read next (fun _ => true)).unfold (.binder name body)) =
      meaning environment (.binder name body) :=
  unfoldRebuilt_exact next name body environment

/-- The concrete lexical reconstruction has a finite successful fuel amount
for every path. Every larger fuel amount has the same decision. -/
theorem eventually_exact (next : Nat) (plain : Payload Symbol → Bool)
    (path : EqualityNormalize.Path) (shape : Shape (Payload Symbol)) :
    ∃ bound, ∀ extra, nodeMeets (read next plain) (bound + extra) path shape =
      some (total (read next plain) (ranking next plain) path shape) :=
  RankedGateCompletion.eventually_exact (read next plain) (ranking next plain) path shape

/-- Both nested binders are used, and reference 2 remains free. -/
def nestedOpen : Shape (Payload Nat) :=
  .binder 0 (.binder 1 (.branch ⟨0, fun _ => True⟩ [.ref 0, .ref 1, .ref 2]))

/-- Two same-path unfoldings remove two head binders even though the stored
replacement copies retain the complete original recursive shape. -/
theorem nested_rank :
    headRank nestedOpen = 2 ∧
      headRank ((read 10 (fun _ => true)).unfold nestedOpen) = 1 ∧
      headRank ((read 10 (fun _ => true)).unfold
        ((read 10 (fun _ => true)).unfold nestedOpen)) = 0 := by decide +kernel

end MicroCFTA.LexicalGateRank
