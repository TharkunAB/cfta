import MicroCFTA.SourceCurrentFilteredSourceFusion

/-!
# Filtered Empty fusion with original raw depth bounds

Both actual original raw results have depth at most the supplied bound.
The contract retains the full historical source and warm reader calls.
It puts no depth bound on reconstructed outputs or replacement values.
-/
namespace MicroCFTA.SourceCurrentBoundedFilteredFusion
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryLiveInputs (input)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedStoredSubstitution (Environment Replacements)
open InternedBinderProtocol (Reference)
open SourceCurrentReaderReplacementSlots (Paired)
open SourceCurrentUsedBinderAliasTransport (Scope Aliases)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceEqualityRequiredCache (Ready)
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Actual reader-filtered fusion restricted to original raw results within a fixed depth. -/
def Fusion (bound : Nat) (expression : Syntax Symbol Guard) : Prop :=
  ∀ {Atom : Type} (reader : State Symbol Guard) (_ready : Ready reader)
    (inputs : List (Sum (Value Symbol Guard) Atom)) (firstNames secondNames : Atom → Reference)
    (firstOwn secondOwn : Reference) (firstMap secondMap : Environment Symbol Guard)
    (firstBefore secondBefore firstRawHeap secondRawHeap : State Symbol Guard)
    (firstRaw secondRaw firstFiltered secondFiltered left right : Value Symbol Guard),
    firstRaw.depth ≤ bound → secondRaw.depth ≤ bound →
    Context firstBefore (inputs.map (input firstNames)) →
    Context secondBefore (inputs.map (input secondNames)) →
    Aliases expression inputs firstNames secondNames →
    (∀ label ∈ Scope expression inputs,
      Sum.elim id firstNames label = firstOwn ↔ Sum.elim id secondNames label = secondOwn) →
    Paired (fun a b => (a.referenceOf == .empty) = (b.referenceOf == .empty)) firstMap secondMap
      (inputs.map (input firstNames)) (inputs.map (input secondNames)) →
    Replacements reader firstMap → Replacements reader secondMap →
    Available reader firstRaw → Available reader secondRaw →
    build expression (inputs.map (input firstNames)) firstBefore = .done firstRaw firstRawHeap →
    build expression (inputs.map (input secondNames)) secondBefore = .done secondRaw secondRawHeap →
    Grows firstRawHeap reader → Grows secondRawHeap reader →
    run (withoutSelfReference firstOwn firstRaw) reader = (firstFiltered,reader) →
    run (withoutSelfReference secondOwn secondRaw) reader = (secondFiltered,reader) →
    execute firstFiltered firstMap reader = .done left reader →
    execute secondFiltered secondMap reader = .done right reader →
    (left.referenceOf == .empty) = (right.referenceOf == .empty)


/-- An unbounded source fusion law applies at every original raw depth bound. -/
theorem of_fusion (bound : Nat) (expression : Syntax Symbol Guard)
    (original : SourceCurrentFilteredSourceFusion.Fusion expression) : Fusion bound expression := by
  intro Atom reader ready inputs firstNames secondNames firstOwn secondOwn firstMap secondMap
    firstBefore secondBefore firstRawHeap secondRawHeap firstRaw secondRaw firstFiltered secondFiltered left right
    _firstDepth _secondDepth
  exact original reader ready inputs firstNames secondNames firstOwn secondOwn firstMap secondMap
    firstBefore secondBefore firstRawHeap secondRawHeap firstRaw secondRaw firstFiltered secondFiltered left right

/-- A law at a larger original raw depth bound applies at every smaller bound. -/
theorem mono (smaller larger : Nat) (within : smaller ≤ larger) (expression : Syntax Symbol Guard)
    (original : Fusion larger expression) : Fusion smaller expression := by
  intro Atom reader ready inputs firstNames secondNames firstOwn secondOwn firstMap secondMap
    firstBefore secondBefore firstRawHeap secondRawHeap firstRaw secondRaw firstFiltered secondFiltered left right
    firstDepth secondDepth
  exact original reader ready inputs firstNames secondNames firstOwn secondOwn firstMap secondMap
    firstBefore secondBefore firstRawHeap secondRawHeap firstRaw secondRaw firstFiltered secondFiltered left right
    (firstDepth.trans within) (secondDepth.trans within)

/-- Empty source calls satisfy every original raw depth bound. -/
theorem empty (bound : Nat) : Fusion bound (.empty : Syntax Symbol Guard) :=
  of_fusion bound .empty SourceCurrentFilteredSourceFusion.empty

/-- Variable source calls satisfy every original raw depth bound. -/
theorem reference (bound index : Nat) : Fusion bound (.var index : Syntax Symbol Guard) :=
  of_fusion bound (.var index) (SourceCurrentFilteredSourceFusion.reference index)

end MicroCFTA.SourceCurrentBoundedFilteredFusion
