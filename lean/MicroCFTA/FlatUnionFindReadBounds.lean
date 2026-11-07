import MicroCFTA.FlatUnionFindRefinement
import MicroCFTA.SourcePruningEnumerationNativeIndex

/-!
# A constant bound for direct-parent reads

A valid flat forest stores at most one parent edge per lookup. Two units of
the earlier read-only search therefore cover every query and every count fold.
-/

namespace MicroCFTA.FlatUnionFindReadBounds

open FlatUnionFind

/-- Two search steps read any variable in the erased direct-parent forest. -/
theorem root_erase (forest : Forest) (valid : Valid forest) (uv : Nat) :
    SourceUnionFindRoot.root 2 (erase forest) uv = some (root forest uv) := by
  cases lookup : forest uv with
  | none => simp [SourceUnionFindRoot.root, erase, root, lookup]
  | some entry =>
      cases entry with
      | root size members => simp [SourceUnionFindRoot.root, erase, root, lookup]
      | parent parent =>
          obtain ⟨size, members, terminal⟩ := valid.parents uv parent lookup
          simp [SourceUnionFindRoot.root, erase, root, lookup, terminal]

/-- Any larger search budget returns the same direct representative. -/
theorem root_erase_moreFuel (forest : Forest) (valid : Valid forest) (extra uv : Nat) :
    SourceUnionFindRoot.root (2 + extra) (erase forest) uv = some (root forest uv) :=
  SourceUnionFindRoot.root_moreFuel 2 extra (erase forest) uv (root forest uv)
    (root_erase forest valid uv)

/-- One search step cannot follow even one stored parent edge. -/
theorem root_erase_one_parent (forest : Forest) (uv parent : Nat)
    (lookup : forest uv = some (.parent parent)) :
    SourceUnionFindRoot.root 1 (erase forest) uv = none := by
  simp [SourceUnionFindRoot.root, erase, lookup]

/-- One fixed bound counts all occurrences, for every change and starting map. -/
theorem count_erase_moreFuel (forest : Forest) (valid : Valid forest) (extra : Nat)
    (change : Int) (scs : List EnumerationState.Suspended)
    (waiting : EnumerationWaitingIndex.Waiting) :
    SourcePruningEnumerationNativeIndex.count (2 + extra) (erase forest) change scs waiting =
      some (EnumerationCanonicalWaiting.count (root forest) change scs waiting) := by
  induction scs generalizing waiting with
  | nil => rfl
  | cons first rest ih =>
      rw [SourcePruningEnumerationNativeIndex.count,
        root_erase_moreFuel forest valid extra first.var, Option.bind_some, ih]
      rfl

/-- Two search steps per reference compute the complete native count fold. -/
theorem count_erase (forest : Forest) (valid : Valid forest) (change : Int)
    (scs : List EnumerationState.Suspended) (waiting : EnumerationWaitingIndex.Waiting) :
    SourcePruningEnumerationNativeIndex.count 2 (erase forest) change scs waiting =
      some (EnumerationCanonicalWaiting.count (root forest) change scs waiting) :=
  count_erase_moreFuel forest valid 0 change scs waiting

private theorem root_succ_read (fuel : Nat) (forest : UnionFind.Forest) (query : Nat) :
    SourceUnionFindRoot.root (fuel + 1) forest query =
      match UnionFind.read forest query with
      | .parent parent => SourceUnionFindRoot.root fuel forest parent
      | .root _ => some query := by
  cases lookup : forest query with
  | none => simp [SourceUnionFindRoot.root, UnionFind.read, lookup]
  | some entry => cases entry <;> simp [SourceUnionFindRoot.root, UnionFind.read, lookup]

private theorem root_congr_read (left right : UnionFind.Forest)
    (same : ∀ query, UnionFind.read left query = UnionFind.read right query)
    (fuel query : Nat) :
    SourceUnionFindRoot.root fuel left query = SourceUnionFindRoot.root fuel right query := by
  induction fuel generalizing query with
  | zero => rfl
  | succ fuel ih =>
      rw [root_succ_read, root_succ_read, same query]
      cases UnionFind.read right query with
      | parent parent => exact ih parent
      | root size => rfl

/-- Compression retains all effective entries of an erased valid flat forest. -/
theorem findRoot_erase_reads (forest : Forest) (valid : Valid forest) (fuel uv : Nat)
    (found : UnionFind.Result)
    (completed : UnionFind.findRoot fuel (erase forest) uv = some found) :
    ∀ query, UnionFind.read found.forest query = UnionFind.read (erase forest) query := by
  cases fuel with
  | zero => simp [UnionFind.findRoot] at completed
  | succ fuel =>
      cases lookup : forest uv with
      | none =>
          simp [UnionFind.findRoot, erase, lookup] at completed
          subst found
          exact UnionFind.insert_missing (by simp [erase, lookup])
      | some entry =>
          cases entry with
          | root size members =>
              simp [UnionFind.findRoot, erase, lookup] at completed
              subst found
              intro query
              rfl
          | parent parent =>
              obtain ⟨size, members, terminal⟩ := valid.parents uv parent lookup
              cases fuel with
              | zero => simp [UnionFind.findRoot, erase, lookup] at completed
              | succ fuel =>
                  simp [UnionFind.findRoot, erase, lookup, terminal] at completed
                  subst found
                  intro query
                  by_cases same : query = uv
                  · subst query
                    simp [UnionFind.read, UnionFind.put, erase, lookup]
                  · simp [UnionFind.read, UnionFind.put, same]

/-- The actual returned forest retains the same two-step read bound for all queries. -/
theorem root_findRoot_erase (forest : Forest) (valid : Valid forest) (fuel uv : Nat)
    (found : UnionFind.Result)
    (completed : UnionFind.findRoot fuel (erase forest) uv = some found)
    (more query : Nat) :
    SourceUnionFindRoot.root (2 + more) found.forest query = some (root forest query) :=
  (root_congr_read found.forest (erase forest)
    (findRoot_erase_reads forest valid fuel uv found completed) (2 + more) query).trans
      (root_erase_moreFuel forest valid more query)

/-- A computed read returns its actual forest and preserves the uniform bound. -/
theorem findRoot_erase (forest : Forest) (valid : Valid forest) (extra uv : Nat) :
    ∃ found, UnionFind.findRoot (2 + extra) (erase forest) uv = some found ∧
      found.representative = root forest uv ∧
      found.size = (entryOf forest (root forest uv)).1 ∧
      Represents forest found.forest ∧
      ∀ more query, SourceUnionFindRoot.root (2 + more) found.forest query =
        some (root forest query) := by
  have pureRead := root_erase_moreFuel forest valid extra uv
  rw [SourceUnionFindRoot.root_eq] at pureRead
  cases completed : UnionFind.findRoot (2 + extra) (erase forest) uv with
  | none => simp [completed] at pureRead
  | some found =>
      obtain ⟨representative, size, related⟩ :=
        findRoot_represents (erase_represents valid) completed
      exact ⟨found, rfl, representative, size, related,
        root_findRoot_erase forest valid (2 + extra) uv found completed⟩

/-- Counts use the same fixed bound on the actual forest returned by compression. -/
theorem count_findRoot_erase (forest : Forest) (valid : Valid forest) (fuel uv : Nat)
    (found : UnionFind.Result)
    (completed : UnionFind.findRoot fuel (erase forest) uv = some found)
    (more : Nat) (change : Int) (scs : List EnumerationState.Suspended)
    (waiting : EnumerationWaitingIndex.Waiting) :
    SourcePruningEnumerationNativeIndex.count (2 + more) found.forest change scs waiting =
      some (EnumerationCanonicalWaiting.count (root forest) change scs waiting) := by
  induction scs generalizing waiting with
  | nil => rfl
  | cons first rest ih =>
      rw [SourcePruningEnumerationNativeIndex.count,
        root_findRoot_erase forest valid fuel uv found completed more first.var,
        Option.bind_some, ih]
      rfl

end MicroCFTA.FlatUnionFindReadBounds
