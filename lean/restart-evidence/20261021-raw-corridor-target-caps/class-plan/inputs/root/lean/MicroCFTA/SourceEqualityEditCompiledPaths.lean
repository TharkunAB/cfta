import MicroCFTA.SourceEqualityEditLeafPaths
import MicroCFTA.SourceEqualityEditMapLeaves
import MicroCFTA.SourceEqualityEditAPI

/-!
# Original path readback of nonoverlapping simultaneous edits

The source right fold retains every callback occurrence when no input path
is a prefix of another. Its independent condition then checks exactly the
original complete paths. Raw overlapping inputs keep their shadowing behavior.
-/
namespace MicroCFTA.SourceEqualityEditCompiledPaths
open Language SourceEqualityEdits SourceEqualityNeededMap SourceEqualityEditLeafPaths
open SourceEqualityEditMeaning

/-- Neither of two edit paths can select an ancestor of the other. -/
def Disjoint (first second : Path) : Prop := ¬ first.IsPrefix second ∧ ¬ second.IsPrefix first

/-- An inserted path is separate from every retained callback path. -/
def Compatible (path : Path) (edits : Edits Action) : Prop :=
  ∀ prior action, (prior, action) ∈ leaves edits → Disjoint path prior

/-- A disjoint insertion adds exactly its original callback occurrence to the retained leaves. -/
theorem insert_leaves (path : Path) (action : Action) (edits : Edits Action)
    (valid : SourceEqualityEdits.Valid edits) (compatible : Compatible path edits) :
    (leaves (insert path action edits)).Perm ((path, action) :: leaves edits) := by
  induction path generalizing edits with
  | nil =>
      have noLeaves : leaves edits = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro leaf member
        exact (compatible leaf.1 leaf.2 member).1 ⟨leaf.1, rfl⟩
      simp only [SourceEqualityEdits.insert, leaves, noLeaves]
      exact List.Perm.refl _
  | cons index rest ih =>
      cases edits with
      | editAt prior =>
          exact False.elim ((compatible [] prior (by simp [leaves])).2 ⟨index :: rest, rfl⟩)
      | editBelow entries =>
          rw [SourceEqualityEdits.Valid] at valid
          let previous := (lookup index entries).getD (empty : Edits Action)
          have previousValid : SourceEqualityEdits.Valid previous := by
            cases found : lookup index entries with
            | none => simpa only [previous, found, Option.getD_none] using (empty_valid (Action := Action))
            | some child => simpa only [previous, found, Option.getD_some] using valid.2 index child (lookup_mem _ _ _ found)
          have previousCompatible : Compatible rest previous := by
            cases found : lookup index entries with
            | none => simp [previous, found, Compatible, empty, leaves]
            | some child =>
                intro prior oldAction member
                have retained : (prior, oldAction) ∈ leaves child := by simpa only [previous, found, Option.getD_some] using member
                have parent := compatible (index :: prior) oldAction
                  (below_member entries index child (lookup_mem _ _ _ found) prior oldAction retained)
                exact ⟨fun initial => parent.1 (List.cons_prefix_cons.mpr ⟨rfl, initial⟩),
                  fun initial => parent.2 (List.cons_prefix_cons.mpr ⟨rfl, initial⟩)⟩
          have mapped := (ih previous previousValid previousCompatible).map
            (fun leaf : Path × Action => (index :: leaf.1, leaf.2))
          have changed : ((leaves (insert rest action previous)).map (fun leaf => (index :: leaf.1, leaf.2))).Perm
              ((index :: rest, action) :: (lookup index entries).toList.flatMap
                (fun child => (leaves child).map (fun leaf => (index :: leaf.1, leaf.2)))) := by
            cases found : lookup index entries <;> simpa [previous, found, empty, leaves] using mapped
          simpa only [SourceEqualityEdits.insert, leaves] using
            SourceEqualityEditMapLeaves.alter_flatMap index (fun prior => insert rest action (prior.getD empty)) entries valid.1
              (fun key child => (leaves child).map (fun leaf => (key :: leaf.1, leaf.2))) (index :: rest, action) changed

/-- Nonoverlapping original edit pairs retain every callback occurrence through actual compilation. -/
theorem build_leaves (edits : List (Path × Action))
    (disjoint : edits.Pairwise (fun first second => Disjoint first.1 second.1)) :
    (leaves (build edits)).Perm edits := by
  induction edits with
  | nil => simpa only [build, List.foldr_nil, empty, leaves, List.flatMap_nil] using (List.Perm.refl ([] : List (Path × Action)))
  | cons edit rest ih =>
      have order := List.pairwise_cons.mp disjoint
      have prior := ih order.2
      have compatible : Compatible edit.1 (build rest) := by
        intro path action member
        exact order.1 (path, action) (prior.mem_iff.mp member)
      exact (insert_leaves edit.1 edit.2 (build rest) (build_valid rest) compatible).trans (prior.cons edit)

/-- The compiled trie condition is exactly each original callback condition at its existing complete path. -/
theorem build_matches (condition : Action → Term Symbol → Prop) (edits : List (Path × Action))
    (disjoint : edits.Pairwise (fun first second => Disjoint first.1 second.1)) (term : Term Symbol) :
    Matches condition (build edits) term ↔ ∀ path action, (path, action) ∈ edits →
      ∀ part, SymbolicSignedPaths.lookup term path = some part → condition action part := by
  rw [matches_exact]
  have occurrence := build_leaves edits disjoint
  exact ⟨fun allPaths path action member => allPaths path action (occurrence.mem_iff.mpr member),
    fun allPaths path action member => allPaths path action (occurrence.mem_iff.mp member)⟩

/-- Nonroot original edits cannot compile to the ignored list-root callback branch. -/
theorem build_not_leaf (edits : List (Path × Action))
    (disjoint : edits.Pairwise (fun first second => Disjoint first.1 second.1))
    (nonroot : ∀ path action, (path, action) ∈ edits → path ≠ []) (action : Action) :
    build edits ≠ .editAt action := by
  intro same
  have member : ([], action) ∈ leaves (build edits) := by simp [same, leaves]
  exact nonroot [] action ((build_leaves edits disjoint).mem_iff.mp member) rfl

/-- Actual child-list compilation checks precisely the original nonroot edit paths. -/
theorem list_condition_exact (condition : Action → Term Symbol → Prop) (edits : List (Path × Action))
    (disjoint : edits.Pairwise (fun first second => Disjoint first.1 second.1))
    (nonroot : ∀ path action, (path, action) ∈ edits → path ≠ []) (symbol : Symbol) (terms : List (Term Symbol)) :
    SourceEqualityEditAPI.ListCondition condition (build edits) terms ↔
      ∀ path action, (path, action) ∈ edits → ∀ part,
        SymbolicSignedPaths.lookup (.node symbol terms) path = some part → condition action part := by
  cases compiled : build edits with
  | editAt action => exact False.elim (build_not_leaf edits disjoint nonroot action compiled)
  | editBelow entries =>
      have valid := build_valid edits
      rw [compiled, SourceEqualityEdits.Valid] at valid
      have original := build_matches condition edits disjoint (.node symbol terms)
      rw [compiled] at original
      exact (forest_zero condition entries valid.1 symbol terms).trans original

open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityEditGraph SourceEqualityEditWorker SourceEqualityEditLanguage
open SourceEqualityRequiredSemanticCache
open InternedGuardedLanguage (meaning)

/-- Actual simultaneous edits accept precisely the original terms that satisfy each original path callback condition. -/
theorem editAll_paths [DecidableEq (EdgeKey Symbol Guard)] (call : Callback Action Symbol Guard)
    (condition : Action → Term Symbol → Prop) (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (fuel readFuel : Nat) (edits : List (Path × Action))
    (disjoint : edits.Pairwise (fun first second => Disjoint first.1 second.1))
    (nonroot : ∀ path action, (path, action) ∈ edits → path ≠ [])
    (values results : List (Value Symbol Guard)) (before after : State Symbol Guard)
    (done : editAll call fuel readFuel edits values before = .done results after)
    (laws : ∀ path action, (path, action) ∈ edits → LeafLaw call condition holds ambient action)
    (semantic : SemanticReady before) (available : Values before values) (closed : ClosedValues values)
    (symbol : Symbol) (terms : List (Term Symbol)) :
    All₂ (meaning holds ambient) results terms ↔ All₂ (meaning holds ambient) values terms ∧
      ∀ path action, (path, action) ∈ edits → ∀ part,
        SymbolicSignedPaths.lookup (.node symbol terms) path = some part → condition action part := by
  rw [SourceEqualityEditAPI.editAll_done call condition holds ambient fuel readFuel edits values results before after done laws
    semantic available closed terms, list_condition_exact condition edits disjoint nonroot symbol terms]

end MicroCFTA.SourceEqualityEditCompiledPaths
