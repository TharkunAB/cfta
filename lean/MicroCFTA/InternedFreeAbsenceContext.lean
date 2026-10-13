import MicroCFTA.InternedFreeAbsenceConstructors
import MicroCFTA.InternedFreeNameMuOrigins
import MicroCFTA.InternedLiteralObservations
import MicroCFTA.InternedSourceFreeNames

/-!
# Verified source contexts for free-name absence replay

An input change replaces one interned reference and permits target
aliases. Both actual executions retain the profile and free-name tables.
Callback replay uses the same supplied probe name on both sides.
-/
namespace MicroCFTA.InternedFreeAbsenceContext
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open InternedNestedMissReadback InternedStoredMuOrigins InternedNestedMuOrigins
open InternedFreeAbsenceConstructors InternedOccurrenceObservations
open InternedBinderProtocol (Reference)

/-- Replace one interned reference without changing either source probe sentinel. -/
def change (identity : Nat) (replacement name : Reference) : Reference :=
  if name = .interned identity then replacement else name

/-- A source prefix retains both semantic tables and every literal lexical input. -/
structure Context (state : State Symbol Guard) (names : List Reference) : Prop where
  normal : Normal state
  inputs : Values state (names.map Value.reference)
  profiles : InternedProfileHeap.Heap state
  freeNames : InternedFreeNameHeap.Heap state

/-- The stronger context includes the established source profile context. -/
theorem Context.profileContext (context : Context state names) :
    InternedProfileTraceSites.Context state (names.map Value.reference) :=
  ⟨context.normal, context.inputs, context.profiles⟩

/-- Full source construction retains the original literal environment and both semantic tables. -/
theorem Context.build [DecidableEq (EdgeKey Symbol Guard)] (context : Context state names)
    (expression : Syntax Symbol Guard) : Context (build expression (names.map Value.reference) state).state names :=
  ⟨(context.profileContext.build expression).normal, (context.profileContext.build expression).inputs,
    (context.profileContext.build expression).heap,
    (InternedNestedFreeNames.build_free expression _ state context.normal context.inputs context.freeNames context.profiles).heap⟩

/-- Ordered source children retain the original literal environment and both tables. -/
theorem Context.many [DecidableEq (EdgeKey Symbol Guard)] (context : Context state names)
    (expressions : List (Syntax Symbol Guard)) : Context (buildMany expressions (names.map Value.reference) state).state names :=
  ⟨(context.profileContext.many expressions).normal, (context.profileContext.many expressions).inputs,
    (context.profileContext.many expressions).heap,
    (InternedNestedFreeNames.buildMany_free expressions _ state context.normal context.inputs context.freeNames context.profiles).heap⟩

/-- Source edge lists retain the original literal environment and both tables. -/
theorem Context.edges [DecidableEq (EdgeKey Symbol Guard)] (context : Context state names)
    (expressions : List (EdgeSyntax Symbol Guard)) : Context (buildEdges expressions (names.map Value.reference) state).state names :=
  ⟨buildEdges_normal expressions _ state context.normal context.inputs,
    fun value member => (buildEdges_verified expressions _ state context.normal.facts context.inputs).available value (context.inputs value member),
    (InternedNestedProfiles.buildEdges_profile expressions _ state context.normal context.inputs context.profiles).heap,
    (InternedNestedFreeNames.buildEdges_free expressions _ state context.normal context.inputs context.freeNames context.profiles).heap⟩

/-- Adding an available literal input changes neither semantic table. -/
theorem Context.local (context : Context state names) (name : Reference) (available : Available state (.reference name)) :
    Context state (name :: names) := by
  refine ⟨context.normal, ?_, context.profiles, context.freeNames⟩
  intro value member
  rcases List.mem_cons.mp member with rfl | member
  · exact available
  · exact context.inputs value member

/-- Edge allocation changes no complete recursive payload invariant. -/
theorem Context.edge [DecidableEq (EdgeKey Symbol Guard)] (context : Context state names)
    (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard)) (inputs : Values state values) :
    Context (run (makeEdge symbol guard values) state).2 names :=
  ⟨(context.profileContext.edge symbol guard values inputs).normal,
    (context.profileContext.edge symbol guard values inputs).inputs,
    (context.profileContext.edge symbol guard values inputs).heap, context.freeNames⟩

/-- Every normalized source callback retains its original literal inputs and both tables. -/
theorem Context.callback [DecidableEq (EdgeKey Symbol Guard)] (context : Context state names)
    (expression : Syntax Symbol Guard) (name : Reference) (available : Available state (.reference name)) :
    Context (callback expression (names.map Value.reference) name state).state names := by
  have all := (context.local name available).inputs
  have kept := InternedSpecialKeyReadiness.Context.callback context.profileContext expression name available
  exact ⟨kept.normal, kept.inputs, kept.heap,
    (InternedSourceFreeNames.callback_checked expression _ name state context.normal all context.freeNames context.profiles).heap⟩

/-- The raw source replay property uses the actual completed calls and their common cache history. -/
def RawReplay [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (identity : Nat) (replacement : Reference) : Prop :=
  ∀ names left right common afterLeft afterRight,
    Context left names → Context right (names.map (change identity replacement)) → Coherent common →
    ∀ first second,
      build expression (names.map Value.reference) left = .done first afterLeft →
      build expression ((names.map (change identity replacement)).map Value.reference) right = .done second afterRight →
      Grows afterLeft common → Grows afterRight common → Related (.interned identity) first second

/-- Full source syntax preserves emptiness under the selected literal replacement. -/
theorem build_empty [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (identity : Nat) (replacement : Reference) (names : List Reference)
    (left right afterLeft afterRight : State Symbol Guard)
    (lc : Context left names) (rc : Context right (names.map (change identity replacement)))
    (first second : Value Symbol Guard)
    (firstDone : build expression (names.map Value.reference) left = .done first afterLeft)
    (secondDone : build expression ((names.map (change identity replacement)).map Value.reference) right = .done second afterRight) :
    first.referenceOf = .empty ↔ second.referenceOf = .empty := by
  rw [InternedEmptyNormalization.reference_empty, InternedEmptyNormalization.reference_empty]
  exact InternedLiteralObservations.build_empty expression names _ (by simp) left right afterLeft afterRight
    lc.profileContext rc.profileContext first second firstDone secondDone

/-- Equal source probe names transport raw absence replay through the actual root filter. -/
theorem callback_equal [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (identity : Nat) (replacement : Reference) (recurse : RawReplay expression identity replacement)
    (names : List Reference) (name : Reference) (different : name ≠ .interned identity)
    (left right common afterLeft afterRight : State Symbol Guard)
    (lc : Context left names) (rc : Context right (names.map (change identity replacement)))
    (coherent : Coherent common) (la : Available left (.reference name)) (ra : Available right (.reference name))
    (first second : Value Symbol Guard)
    (firstDone : callback expression (names.map Value.reference) name left = .done first afterLeft)
    (secondDone : callback expression ((names.map (change identity replacement)).map Value.reference) name right = .done second afterRight)
    (lg : Grows afterLeft common) (rg : Grows afterRight common) (absent : .interned identity ∉ first.free) : first = second := by
  obtain ⟨rawLeft, middleLeft, rawDoneLeft, filterDoneLeft⟩ := InternedNestedSpecialization.bind_done _ _ _ _ firstDone
  obtain ⟨rawRight, middleRight, rawDoneRight, filterDoneRight⟩ := InternedNestedSpecialization.bind_done _ _ _ _ secondDone
  have localLeft := lc.local name la
  have localRight : Context right ((name :: names).map (change identity replacement)) := by
    simpa only [List.map_cons, change, different, ↓reduceIte] using rc.local name ra
  have middleContext : Context middleLeft (name :: names) := by
    simpa only [List.map_cons, rawDoneLeft, Outcome.state] using localLeft.build expression
  have middleRightContext : Context middleRight ((name :: names).map (change identity replacement)) := by
    simpa only [List.map_cons, change, different, ↓reduceIte, rawDoneRight, Outcome.state] using localRight.build expression
  have leftFilterGrowth : Grows middleLeft afterLeft := by
    simpa only [filterDoneLeft, Outcome.state] using
      (work_correct (withoutSelfReference name rawLeft) middleLeft middleContext.normal.facts.coherent.valid).2
  have rightFilterGrowth : Grows middleRight afterRight := by
    simpa only [filterDoneRight, Outcome.state] using
      (work_correct (withoutSelfReference name rawRight) middleRight middleRightContext.normal.facts.coherent.valid).2
  have rawAbsent : .interned identity ∉ rawLeft.free := by
    intro member
    exact absent ((InternedFreeNameConstructors.callback_other expression (names.map Value.reference) name (.interned identity)
      (Ne.symm different) left middleLeft afterLeft lc.normal localLeft.inputs rawLeft first rawDoneLeft firstDone).mpr member)
  have observed := recurse (name :: names) left right common middleLeft middleRight localLeft localRight coherent rawLeft rawRight
    (by simpa only [List.map_cons] using rawDoneLeft)
    (by simpa only [List.map_cons, change, different, ↓reduceIte] using rawDoneRight)
    (grows_trans leftFilterGrowth lg) (grows_trans rightFilterGrowth rg)
  have same := observed.2 rawAbsent
  subst rawRight
  have leftValue := filterDoneLeft
  have rightValue := filterDoneRight
  simp only [work, Outcome.done.injEq] at leftValue rightValue
  have filtered := InternedObservedAbsence.run_shared (withoutSelfReference name rawLeft) middleLeft middleRight common
    middleContext.normal.facts.coherent.valid middleRightContext.normal.facts.coherent.valid
    (by simpa only [leftValue.2] using lg) (by simpa only [rightValue.2] using rg)
  exact leftValue.1.symm.trans (filtered.trans rightValue.1)

end MicroCFTA.InternedFreeAbsenceContext
