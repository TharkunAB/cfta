import MicroCFTA.SourceCurrentRetainedMuDirectedCase
import MicroCFTA.SourceCurrentSourceDirectedCases
import MicroCFTA.SourceCurrentStoredLiveSourceLineage

/-!
# Actual child generators for ordinary source nodes

A fresh absent filter preserves each actual raw child result, including
root unions. Actual live source rows retain their child alias conditions.
Their warm stored calls then generate both ordered child directions.
No child observation or whole-parent output relation is assumed.
-/
namespace MicroCFTA.SourceCurrentGeneratedNodeCases
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open InternedNestedProvenance (Values)
open InternedFreshOrdinaryConstruction (build buildMany)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedFreshOrdinaryLiveInputs (input inputProfile)
open InternedStoredSubstitution (Environment Replacements)
open InternedBinderProtocol (Reference)
open SourceEqualityRequiredCache (Ready)
open SourceCurrentRetainedMuDirectedCase (Generated Inputs)
open SourceCurrentUsedBinderAliasTransport (Aliases Scope)
open SourceCurrentNativeNormalizationInputs (support inputNames)
open SourceCurrentOpenPreorderSimulation (Mutual)

private theorem reverse_inputs [DecidableEq (EdgeKey Symbol Guard)] {reader : State Symbol Guard}
    {first second : Environment Symbol Guard} {left right : List (Value Symbol Guard)}
    (paired : Inputs reader first second left right) : Inputs reader second first right left := by
  cases paired with
  | nil first second => exact .nil second first
  | reference forward backward tail => exact .reference backward forward (reverse_inputs tail)
  | fixed value agree tail => exact .fixed value (fun name member => (agree name member).symm) (reverse_inputs tail)
termination_by structural paired

private theorem fresh_free (reader : State Symbol Guard) (ready : Ready reader)
    (value : Value Symbol Guard) (available : Available reader value) :
    Reference.interned reader.nodes.next ∉ value.free := by
  intro member
  obtain ⟨key,issued⟩ := available.issued _ member
  exact Nat.lt_irrefl _ (ready.semantic.1.normal.facts.coherent.valid.2.1 _ _ issued)

private theorem fresh_scope (expression : Syntax Symbol Guard)
    (inputs : List (Sum (Value Symbol Guard) Atom)) (names : Atom → Reference)
    (reader : State Symbol Guard) (ready : Ready reader)
    (available : Values reader (inputs.map (input names))) :
    Reference.interned reader.nodes.next ∉ (Scope expression inputs).map (Sum.elim id names) := by
  intro member
  simp only [Scope,List.map_cons,Sum.elim_inl,id_eq,List.mem_cons,reduceCtorEq,false_or] at member
  obtain ⟨value,present,free⟩ := SourceCurrentNativeNormalizationFreshness.support_origin expression inputs names _ member
  exact fresh_free reader ready value (available value present) free

private theorem filter_absent [DecidableEq (EdgeKey Symbol Guard)] (name : Reference) (value : Value Symbol Guard)
    (reader : State Symbol Guard) (ready : Ready reader) (available : Available reader value)
    (absent : name ∉ value.free) : run (withoutSelfReference name value) reader = (value,reader) := by
  cases value with
  | empty | reference | node | mu => rfl
  | union entry members level free =>
      rw [withoutSelfReference_absent name entry members level free]
      · rfl
      · intro member
        exact absent ((InternedNormalizationFree.unionMembers_free reader ready.semantic.1.normal.facts.coherent
          (.union entry members level free) available name).mpr
            ⟨.reference name,member,by simp only [Value.free,List.mem_singleton]⟩)

private theorem generate_one [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (inputs : List (Sum (Value Symbol Guard) Atom)) (firstNames secondNames : Atom → Reference)
    (first second : Environment Symbol Guard) (reader : State Symbol Guard) (ready : Ready reader)
    (firstInputs : Values reader (inputs.map (input firstNames)))
    (secondInputs : Values reader (inputs.map (input secondNames)))
    (aliases : Aliases expression inputs firstNames secondNames)
    (paired : Inputs reader first second (inputs.map (input firstNames)) (inputs.map (input secondNames)))
    (firstReplacements : Replacements reader first) (secondReplacements : Replacements reader second)
    (rawFirst rawSecond left right : Value Symbol Guard)
    (firstBuild : build expression (inputs.map (input firstNames)) reader = .done rawFirst reader)
    (secondBuild : build expression (inputs.map (input secondNames)) reader = .done rawSecond reader)
    (firstDone : execute rawFirst first reader = .done left reader)
    (secondDone : execute rawSecond second reader = .done right reader) : Generated reader left right := by
  have firstContext : SourceCurrentConstrainedCapSourceHistory.Context reader (inputs.map (input firstNames)) :=
    ⟨SourceRecursiveIntersectionSemanticHeap.context reader ready.semantic _ firstInputs,ready.semantic.2⟩
  have secondContext : SourceCurrentConstrainedCapSourceHistory.Context reader (inputs.map (input secondNames)) :=
    ⟨SourceRecursiveIntersectionSemanticHeap.context reader ready.semantic _ secondInputs,ready.semantic.2⟩
  have firstAvailable := (InternedFreshOrdinaryFacts.build_verified expression _ reader
    ready.semantic.1.normal.facts firstInputs).result rawFirst reader firstBuild
  have secondAvailable := (InternedFreshOrdinaryFacts.build_verified expression _ reader
    ready.semantic.1.normal.facts secondInputs).result rawSecond reader secondBuild
  have firstFilter := filter_absent (.interned reader.nodes.next) rawFirst reader ready firstAvailable
    (fresh_free reader ready rawFirst firstAvailable)
  have secondFilter := filter_absent (.interned reader.nodes.next) rawSecond reader ready secondAvailable
    (fresh_free reader ready rawSecond secondAvailable)
  have firstFresh := fresh_scope expression inputs firstNames reader ready firstInputs
  have secondFresh := fresh_scope expression inputs secondNames reader ready secondInputs
  have tests : ∀ label ∈ Scope expression inputs,
      Sum.elim id firstNames label = .interned reader.nodes.next ↔
      Sum.elim id secondNames label = .interned reader.nodes.next := by
    intro label member
    exact iff_of_false (fun same => firstFresh (List.mem_map.mpr ⟨label,member,same⟩))
      (fun same => secondFresh (List.mem_map.mpr ⟨label,member,same⟩))
  exact Generated.filtered expression inputs firstNames secondNames
    (.interned reader.nodes.next) (.interned reader.nodes.next) first second
    reader reader reader reader reader reader rawFirst rawSecond rawFirst rawSecond left right
    ready firstContext secondContext aliases tests paired firstReplacements secondReplacements
    firstAvailable secondAvailable firstBuild secondBuild firstFilter secondFilter
    (grows_refl _) (grows_refl _) (grows_refl _) (grows_refl _)
    firstBuild secondBuild firstFilter secondFilter firstDone secondDone

/-- Actual warm source and stored calls generate both directions with derived absent root filters. -/
theorem warm_pair [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (inputs : List (Sum (Value Symbol Guard) Atom)) (firstNames secondNames : Atom → Reference)
    (first second : Environment Symbol Guard) (reader : State Symbol Guard) (ready : Ready reader)
    (firstInputs : Values reader (inputs.map (input firstNames)))
    (secondInputs : Values reader (inputs.map (input secondNames)))
    (aliases : Aliases expression inputs firstNames secondNames)
    (paired : Inputs reader first second (inputs.map (input firstNames)) (inputs.map (input secondNames)))
    (firstReplacements : Replacements reader first) (secondReplacements : Replacements reader second)
    (rawFirst rawSecond left right : Value Symbol Guard)
    (firstBuild : build expression (inputs.map (input firstNames)) reader = .done rawFirst reader)
    (secondBuild : build expression (inputs.map (input secondNames)) reader = .done rawSecond reader)
    (firstDone : execute rawFirst first reader = .done left reader)
    (secondDone : execute rawSecond second reader = .done right reader) :
    Mutual (Generated reader) left right := by
  exact ⟨generate_one expression inputs firstNames secondNames first second reader ready firstInputs secondInputs
      aliases paired firstReplacements secondReplacements rawFirst rawSecond left right firstBuild secondBuild firstDone secondDone,
    generate_one expression inputs secondNames firstNames second first reader ready secondInputs firstInputs
      (fun a aMember b bMember => (aliases a aMember b bMember).symm) (reverse_inputs paired)
      secondReplacements firstReplacements rawSecond rawFirst right left secondBuild firstBuild secondDone firstDone⟩

private theorem live_aliases (rows : List (EdgeSyntax Symbol Guard))
    (inputs : List (Sum (Value Symbol Guard) Atom)) (firstNames secondNames : Atom → Reference)
    (aliases : Aliases (.node rows) inputs firstNames secondNames)
    (symbol : Symbol) (guard : Guard) (children : List (Syntax Symbol Guard))
    (row : EdgeSyntax.mk symbol guard children ∈ rows)
    (live : (InternedProfileSemantics.evaluateMany children (inputs.map inputProfile)).all
      (fun child => !InternedProfileSemantics.isEmpty child) = true)
    (child : Syntax Symbol Guard) (member : child ∈ children) :
    Aliases child inputs firstNames secondNames := by
  have included (label : Sum Reference Atom) (present : label ∈ Scope child inputs) :
      label ∈ Scope (.node rows) inputs := by
    rcases List.mem_cons.mp present with rfl | present
    · exact List.mem_cons_self
    · apply List.mem_cons_of_mem
      unfold support at present ⊢
      rw [InternedFreeNameSemantics.evaluate]
      exact (InternedFreeNameSemantics.evaluateEdges_member rows (inputs.map inputProfile)
        (inputs.map inputNames) label).mpr ⟨symbol,guard,children,row,live,child,member,present⟩
  exact fun a aMember b bMember => aliases a (included a aMember) b (included b bMember)

private theorem source_live [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (inputs : List (Sum (Value Symbol Guard) Atom)) (names : Atom → Reference)
    (reader : State Symbol Guard) (ready : Ready reader) (available : Values reader (inputs.map (input names)))
    (values : List (Value Symbol Guard)) (called : buildMany expressions (inputs.map (input names)) reader = .done values reader)
    (live : values.any (fun value => value.referenceOf == .empty) = false) :
    (InternedProfileSemantics.evaluateMany expressions (inputs.map inputProfile)).all
      (fun child => !InternedProfileSemantics.isEmpty child) = true := by
  have output := (InternedFreshOrdinaryFacts.buildMany_verified expressions _ reader
    ready.semantic.1.normal.facts available).result values reader called
  have matched := (InternedFreshOrdinaryProfiles.buildMany_profile expressions _ reader
    ready.semantic.1.normal available ready.semantic.1.profiles).result values reader called
  have actualLive : values.all (fun value => !InternedProfileSemantics.isEmpty (InternedRootProfile.profile value)) = true := by
    apply List.all_eq_true.mpr
    intro value member
    rw [InternedRootProfileNode.isEmpty_profile value reader ready.semantic.1.normal.proper (output value member)]
    have absent := List.any_eq_false.mp live value member
    rw [Bool.eq_false_iff.mpr absent]
    rfl
  rw [InternedProfileComposition.children_matched matched] at actualLive
  simpa only [InternedFreshOrdinaryLiveInputs.input_profiles,InternedProfileSemantics.evaluateMany_map,
    List.all_map,Function.comp_def,InternedProfileSemantics.isEmpty_map] using actualLive

/-- An actual live node row derives each child generator from its own source and stored calls. -/
theorem live_child [DecidableEq (EdgeKey Symbol Guard)] (rows : List (EdgeSyntax Symbol Guard))
    (inputs : List (Sum (Value Symbol Guard) Atom)) (firstNames secondNames : Atom → Reference)
    (first second : Environment Symbol Guard) (reader : State Symbol Guard) (ready : Ready reader)
    (firstInputs : Values reader (inputs.map (input firstNames)))
    (secondInputs : Values reader (inputs.map (input secondNames)))
    (aliases : Aliases (.node rows) inputs firstNames secondNames)
    (paired : Inputs reader first second (inputs.map (input firstNames)) (inputs.map (input secondNames)))
    (firstReplacements : Replacements reader first) (secondReplacements : Replacements reader second)
    (symbol : Symbol) (guard : Guard) (children : List (Syntax Symbol Guard))
    (row : EdgeSyntax.mk symbol guard children ∈ rows)
    (values : List (Value Symbol Guard))
    (called : buildMany children (inputs.map (input firstNames)) reader = .done values reader)
    (alive : values.any (fun value => value.referenceOf == .empty) = false)
    (child : Syntax Symbol Guard) (member : child ∈ children)
    (rawFirst rawSecond left right : Value Symbol Guard)
    (firstBuild : build child (inputs.map (input firstNames)) reader = .done rawFirst reader)
    (secondBuild : build child (inputs.map (input secondNames)) reader = .done rawSecond reader)
    (firstDone : execute rawFirst first reader = .done left reader)
    (secondDone : execute rawSecond second reader = .done right reader) :
    Mutual (Generated reader) left right :=
  warm_pair child inputs firstNames secondNames first second reader ready firstInputs secondInputs
    (live_aliases rows inputs firstNames secondNames aliases symbol guard children row
      (source_live children inputs firstNames reader ready firstInputs values called alive) child member)
    paired firstReplacements secondReplacements rawFirst rawSecond left right firstBuild secondBuild firstDone secondDone

end MicroCFTA.SourceCurrentGeneratedNodeCases
