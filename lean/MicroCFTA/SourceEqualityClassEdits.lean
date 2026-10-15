import MicroCFTA.SourceEqualityEditCompiledPaths
import MicroCFTA.SourceEqualityClassOrder
import MicroCFTA.SourceEqualitySelectedRequired

/-!
# Simultaneous edit conditions for physical equality classes

A coherent nontrivial source class derives nonoverlapping nonroot edit paths.
Natural path conversion retains exact signed lookup. The source edit worker
therefore supplies its forest law at the original class paths.
-/
namespace MicroCFTA.SourceEqualityClassEdits
open Language SourceEqualityEdits SourceEqualityEditCompiledPaths

/-- Natural source paths retain and reflect prefix relations under signed conversion. -/
theorem signed_prefix (first second : EqualityNormalize.Path) :
    (first.map Int.ofNat).IsPrefix (second.map Int.ofNat) ↔ first.IsPrefix second := by
  constructor
  · intro initial
    have decoded := initial.map Int.toNat
    simp only [List.map_map, Function.comp_def] at decoded
    change (first.map id).IsPrefix (second.map id) at decoded
    simpa only [List.map_id] using decoded
  · exact fun initial => initial.map Int.ofNat

/-- Pair each original class path with its actual callback token in source set order. -/
def edits (paths : EqualityNormalize.Class) (target : EqualityNormalize.Path → Action) : List (Path × Action) :=
  paths.map (fun path => (path.map Int.ofNat, target path))

/-- A supported source class derives the disjointness required by the actual compiler theorem. -/
theorem edits_disjoint (paths : EqualityNormalize.Class) (supported : EqualityTrie.Supported paths)
    (target : EqualityNormalize.Path → Action) :
    (edits paths target).Pairwise (fun first second => Disjoint first.1 second.1) := by
  rw [edits, List.pairwise_map]
  apply supported.imp
  intro first second separate
  exact ⟨fun initial => separate.1 ((signed_prefix first second).mp initial),
    fun initial => separate.2 ((signed_prefix second first).mp initial)⟩

/-- A supported nontrivial class cannot contain an empty root path. -/
theorem supported_nonroot (paths : EqualityNormalize.Class) (supported : EqualityTrie.Supported paths)
    (active : EqualityNormalize.Nontrivial paths) : ∀ path ∈ paths, path ≠ [] := by
  intro path member same
  subst path
  have singleton := EqualityTrie.supported_nil paths supported member
  simp [EqualityNormalize.Nontrivial, singleton] at active

/-- Nonroot natural source paths cannot become root edits under signed conversion. -/
theorem edits_nonroot (paths : EqualityNormalize.Class) (nonroot : ∀ path ∈ paths, path ≠ [])
    (target : EqualityNormalize.Path → Action) : ∀ path action, (path, action) ∈ edits paths target → path ≠ [] := by
  intro path action member
  obtain ⟨original, included, same⟩ := List.mem_map.mp member
  cases same
  intro empty
  exact nonroot original included (List.map_eq_nil_iff.mp empty)

/-- Coherent physical trie and path-set fields derive supported original class paths. -/
theorem coherent_supported (record : SourceEqualityClassOrder.Record) (coherent : SourceEqualityClassOrder.Coherent record) :
    EqualityTrie.Supported record.paths := by
  have represented := EqualityTrie.fromPathTrie_supported record.trie coherent.1
  have unique : record.paths.Nodup := by
    rw [← coherent.2.1]
    exact EqualityNormalize.canonicalClass_nodup record.paths
  have occurrence := (List.perm_ext_iff_of_nodup (EqualityTrie.supported_nodup _ represented) unique).mpr coherent.2.2
  exact represented.perm occurrence (fun separate => ⟨separate.2, separate.1⟩)

/-- The callback condition on signed edit pairs has the exact original natural-path meaning. -/
theorem conditions_exact (condition : Action → Term Symbol → Prop) (paths : EqualityNormalize.Class)
    (target : EqualityNormalize.Path → Action) (term : Term Symbol) :
    (∀ path action, (path, action) ∈ edits paths target → ∀ part,
      SymbolicSignedPaths.lookup term path = some part → condition action part) ↔
      ∀ path ∈ paths, ∀ part, term.atPath path = some part → condition (target path) part := by
  constructor
  · intro allPaths path member part found
    exact allPaths (path.map Int.ofNat) (target path) (List.mem_map.mpr ⟨path, member, rfl⟩) part
      (by simpa only [SourceEqualitySelectedRequired.lookup_natural] using found)
  · intro allPaths path action member part found
    obtain ⟨original, included, same⟩ := List.mem_map.mp member
    cases same
    exact allPaths original included part (by simpa only [SourceEqualitySelectedRequired.lookup_natural] using found)

open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityEditGraph SourceEqualityEditWorker SourceEqualityEditLanguage
open SourceEqualityRequiredSemanticCache
open InternedGuardedLanguage (meaning)

/-- One physical source class derives the actual edit forest law without supplied path-disjointness premises. -/
theorem class_exact [DecidableEq (EdgeKey Symbol Guard)] (call : Callback Action Symbol Guard)
    (condition : Action → Term Symbol → Prop) (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (record : SourceEqualityClassOrder.Record) (coherent : SourceEqualityClassOrder.Coherent record)
    (active : EqualityNormalize.Nontrivial record.paths) (target : EqualityNormalize.Path → Action)
    (fuel readFuel : Nat) (values results : List (Value Symbol Guard)) (before after : State Symbol Guard)
    (done : editAll call fuel readFuel (edits record.paths target) values before = .done results after)
    (laws : ∀ path ∈ record.paths, LeafLaw call condition holds ambient (target path))
    (semantic : SemanticReady before) (available : Values before values) (closed : ClosedValues values)
    (symbol : Symbol) (terms : List (Term Symbol)) :
    All₂ (meaning holds ambient) results terms ↔ All₂ (meaning holds ambient) values terms ∧
      ∀ path ∈ record.paths, ∀ part, (Term.node symbol terms).atPath path = some part → condition (target path) part := by
  have supported := coherent_supported record coherent
  have callbackLaws : ∀ path action, (path, action) ∈ edits record.paths target → LeafLaw call condition holds ambient action := by
    intro path action member
    obtain ⟨original, included, same⟩ := List.mem_map.mp member
    cases same
    exact laws original included
  rw [editAll_paths call condition holds ambient fuel readFuel _ (edits_disjoint _ supported target)
    (edits_nonroot _ (supported_nonroot _ supported active) target) values results before after done callbackLaws
    semantic available closed symbol terms, conditions_exact]

end MicroCFTA.SourceEqualityClassEdits
