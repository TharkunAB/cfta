import MicroCFTA.SourceSynthesisNativeTypeSites
import MicroCFTA.SourceCurrentStoredMuRetainedAlignment
import MicroCFTA.InternedFreshOrdinaryCompletedSites

/-!
# Original Mu certificates at earlier constructor calls

Exact record growth transports a completed Mu certificate backward.
The accepted original build supplies the certificate at its final heap.
An actual row-call receipt supplies growth from each earlier row heap.
Source sites before a crossed binder also derive a complete earlier call.
These laws do not infer source roles from stored symbols or guards.
-/
namespace MicroCFTA.SourceSynthesisOriginalPrefixMuStore
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open SourceCurrentHereditaryConstruction (MuStored)

/-- Exact record growth retains each earlier completed Mu with its full payload. -/
theorem muStored_of_grows (valid : Guard → Prop) (before after : State Symbol Guard)
    (growth : Grows before after) (stored : MuStored valid after) : MuStored valid before := by
  intro key entry body depth ordinary present
  exact stored key entry body depth ordinary (growth.nodeRecords key _ present)

section Source
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisFirstOrderConstruction (Expression firstOrderRaw)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- The actual accepted original build derives the store at every earlier record prefix. -/
theorem prefix_muStored (valid : Guard → Prop) (validTop : valid top)
    (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (accepted : firstOrderRaw lib query signed = .ok expression)
    (value : Value Symbol Guard) (heap : State Symbol Guard)
    (built : build (SourceSynthesisUniverseCallerBoundary.ordinarySymbols expression) [] empty = .done value heap)
    (before : State Symbol Guard) (growth : Grows before heap) : MuStored valid before :=
  muStored_of_grows valid before heap growth
    (SourceSynthesisNativeTypeSites.firstOrderRaw_muStored valid validTop
      lib query signed expression accepted value heap built)

/-- An actual row receipt derives the store at entry, child return, and edge return. -/
theorem rowCall_muStored (valid : Guard → Prop) (validTop : valid top)
    (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (accepted : firstOrderRaw lib query signed = .ok expression)
    (value : Value Symbol Guard) (heap : State Symbol Guard)
    (built : build (SourceSynthesisUniverseCallerBoundary.ordinarySymbols expression) [] empty = .done value heap)
    (expressions : List (EdgeSyntax Symbol Guard)) (environment : List (Value Symbol Guard))
    (before : State Symbol Guard) (outputs : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (index : Nat) (symbol : Symbol) (guard : Guard) (children : List (Syntax Symbol Guard))
    (call : SourceCurrentStoredMuRetainedAlignment.RowCall
      expressions environment before outputs after heap index symbol guard children) :
    MuStored valid call.current ∧ MuStored valid call.middle ∧ MuStored valid call.next := by
  have stored := SourceSynthesisNativeTypeSites.firstOrderRaw_muStored valid validTop
    lib query signed expression accepted value heap built
  exact ⟨muStored_of_grows valid call.current heap call.current_growth stored,
    muStored_of_grows valid call.middle heap call.middle_growth stored,
    muStored_of_grows valid call.next heap call.next_growth stored⟩

/-- A source site before any binder crossing derives its actual call and both stores. -/
theorem original_site_muStored (valid : Guard → Prop) (validTop : valid top)
    (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (accepted : firstOrderRaw lib query signed = .ok expression)
    (value : Value Symbol Guard) (heap : State Symbol Guard)
    (built : build (SourceSynthesisUniverseCallerBoundary.ordinarySymbols expression) [] empty = .done value heap)
    (target : Syntax Symbol Guard)
    (site : InternedNestedTraceSites.Site
      (SourceSynthesisUniverseCallerBoundary.ordinarySymbols expression) target 0) :
    ∃ start result finish, build target [] start = .done result finish ∧
      InternedFreshOrdinaryContext.Context start [] ∧ Grows start heap ∧ Grows finish heap ∧
      MuStored valid start ∧ MuStored valid finish := by
  obtain ⟨start, result, finish, called, context, _, suffix⟩ :=
    InternedFreshOrdinaryCompletedSites.zero_site site rfl [] empty heap value
      InternedFreshOrdinaryContext.empty_context built
  have checked := InternedFreshOrdinaryFacts.build_verified target [] start
    context.normal.facts context.inputs
  have growth : Grows start finish := by
    simpa only [called, Outcome.state] using checked.growth
  have prefixGrowth := grows_trans growth suffix
  exact ⟨start, result, finish, called, context, prefixGrowth, suffix,
    prefix_muStored valid validTop lib query signed expression accepted value heap built start prefixGrowth,
    prefix_muStored valid validTop lib query signed expression accepted value heap built finish suffix⟩

end Source
end MicroCFTA.SourceSynthesisOriginalPrefixMuStore
