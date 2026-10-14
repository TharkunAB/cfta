import MicroCFTA.InternedRecordDepthLevels
import MicroCFTA.InternedFreshOrdinaryActiveReplay

/-!
# Actual paired source routes preserve ordinary names

The earlier route retains its captured suffix at every crossing. The
current source path supplies its own exact lexical inputs. The proof
compares outer callbacks before it enters their nested source bodies.
-/
namespace MicroCFTA.InternedRecordDepthRoutes
open InternedConstructorTemplates InternedProbeProvenance
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts InternedFreshOrdinaryContext
open InternedFreshOrdinaryActiveOrigins InternedFreshOrdinaryActiveReplay
open InternedFreshOrdinaryLevelReplay (ordinaryNames)
open InternedRecordDepthLevels
open InternedBinderProtocol (Reference)

/-- Corresponding actual crossings select equal projected names from equal projected captured records. -/
theorem crossing_name [DecidableEq (EdgeKey Symbol Guard)]
    (previous : InternedFreshOrdinaryProbeChoiceSites.Crossing Symbol Guard) (actual : Crossing Symbol Guard)
    (firstEnvironment secondEnvironment : List (Value Symbol Guard))
    (firstInputs : previous.environment = firstEnvironment)
    (secondInputs : actual.environment = secondEnvironment)
    (same : project firstEnvironment = project secondEnvironment)
    (body : previous.body = actual.body) (choice : previous.ordinary = Crossing.probeChoice actual)
    (firstHeap : InternedFreshOrdinaryDepthHeap.Heap previous.before)
    (secondHeap : InternedFreshOrdinaryDepthHeap.Heap actual.before) :
    ordinaryNames previous.name = ordinaryNames actual.name := by
  rcases actual with ⟨smart, expression, environment, before, name, start, context, entered⟩
  cases entered with
  | depth =>
      have flag : previous.ordinary = false := by simpa only [Crossing.probeChoice] using choice
      simp [InternedFreshOrdinaryProbeChoiceSites.Crossing.name, flag, ordinaryNames]
  | @ordinary depth after done =>
      change environment = secondEnvironment at secondInputs
      have flag : previous.ordinary = true := by simpa only [Crossing.probeChoice] using choice
      have previousContext : Context previous.before firstEnvironment := by simpa only [firstInputs] using previous.context
      have currentContext : Context before secondEnvironment := by simpa only [secondInputs] using context
      have previousDone : callback expression firstEnvironment .depth previous.before = .done previous.depth previous.afterDepth := by
        simpa only [body, firstInputs] using previous.depthDone
      have currentDone : callback expression secondEnvironment .depth before = .done depth start := by
        simpa only [secondInputs] using done
      have levels := callback_level expression firstEnvironment secondEnvironment same previous.before before previousContext currentContext
        firstHeap secondHeap previous.depth depth previous.afterDepth start previousDone currentDone
      simpa only [InternedFreshOrdinaryProbeChoiceSites.Crossing.name, flag, ↓reduceIte, ordinaryNames] using
        congrArg Reference.uninterned levels
  | fresh =>
      have flag : previous.ordinary = false := by simpa only [Crossing.probeChoice] using choice
      simp [InternedFreshOrdinaryProbeChoiceSites.Crossing.name, flag, ordinaryNames]

/-- Every corresponding route crossing preserves the ordinary-name projection through its actual captured suffix. -/
theorem Path.projected_names [DecidableEq (EdgeKey Symbol Guard)]
    {expression target : InternedNestedConstruction.Syntax Symbol Guard}
    {environment current : List (Value Symbol Guard)} {crossings : List (Crossing Symbol Guard)}
    (path : Path expression environment target current crossings)
    (previous : List (InternedFreshOrdinaryProbeChoiceSites.Crossing Symbol Guard))
    (firstEnvironment secondEnvironment : List (Value Symbol Guard)) (inputs : environment = secondEnvironment)
    (descriptors : previous.map (fun crossing => (crossing.body, crossing.ordinary)) =
      crossings.map (fun crossing => (crossing.body, Crossing.probeChoice crossing)))
    (captures : InternedFreshOrdinaryProbeChoiceSites.Captures firstEnvironment previous)
    (same : project firstEnvironment = project secondEnvironment)
    (previousHeap : ∀ crossing ∈ previous, InternedFreshOrdinaryDepthHeap.Heap crossing.before)
    (currentHeap : ∀ crossing ∈ crossings, InternedFreshOrdinaryDepthHeap.Heap crossing.before) :
    previous.map (fun crossing => ordinaryNames crossing.name) = crossings.map (fun crossing => ordinaryNames crossing.name) := by
  induction path generalizing previous firstEnvironment secondEnvironment with
  | here expression environment =>
      have length := congrArg List.length descriptors
      simp only [List.length_map, List.length_nil] at length
      have empty : previous = [] := by simpa using length
      subst previous
      rfl
  | node edge member nested ih | union member nested ih =>
      exact ih previous firstEnvironment secondEnvironment inputs descriptors captures same previousHeap currentHeap
  | binder crossing nested ih =>
      rcases List.eq_nil_or_concat previous with rfl | ⟨innerPrevious, outer, split⟩
      · have length := congrArg List.length descriptors
        simp at length
      · rw [List.concat_eq_append] at split
        subst previous
        simp only [List.map_append, List.map_cons, List.map_nil] at descriptors
        have separated := List.append_inj' descriptors rfl
        have own : outer.body = crossing.body ∧ outer.ordinary = Crossing.probeChoice crossing := by simpa using separated.2
        obtain ⟨outerInputs, innerCaptures⟩ := (InternedFreshOrdinaryProbeChoiceSites.captures_snoc _ innerPrevious outer).mp captures
        have ownName := crossing_name outer crossing firstEnvironment secondEnvironment outerInputs inputs same own.1 own.2
          (previousHeap outer (List.mem_append_right _ (by simp))) (currentHeap crossing (List.mem_append_right _ (by simp)))
        have innerNames := ih innerPrevious (.reference outer.name :: firstEnvironment) (.reference crossing.name :: secondEnvironment)
          (by simp only [inputs]) separated.1
          innerCaptures
          (project_cons firstEnvironment secondEnvironment outer.name crossing.name ownName same)
          (fun selected member => previousHeap selected (List.mem_append_left _ member))
          (fun selected member => currentHeap selected (List.mem_append_left _ member))
        simp only [List.map_append, List.map_cons, List.map_nil, innerNames, ownName]

end MicroCFTA.InternedRecordDepthRoutes
