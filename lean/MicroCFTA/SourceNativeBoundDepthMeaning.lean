import MicroCFTA.SourceNativeBoundDepthCompletion
import MicroCFTA.InternedGuardedExecutionLists
import MicroCFTA.MergedOrdinaryHeight

/-!
# Meaning of the same completed native bounded copy

The proof observes the existing native run and its local memo updates.
Each memo entry retains a ghost original payload with its bounded meaning.
Canonical identity determines that payload in the current coherent heap.
The public theorem retains one complete stable execution receipt.
-/
namespace MicroCFTA.SourceNativeBoundDepthMeaning
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedRecordCoherence InternedFreshProbeKeys
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache (Keeps)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceNativeBoundDepth (Memo Result atHeight)
open InternedGuardedLanguage (meaning Env)
open MergedColdInterpretation (EdgeMeaning)

/-- Every actual descendant is empty or an ordinary constructor record. -/
inductive DeepOrdinary : Value Symbol Guard → Prop where
  | empty : DeepOrdinary .empty
  | node (entry : Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Guard))
      (depth : Nat) (free : List InternedBinderProtocol.Reference)
      (children : ∀ edge ∈ edges, ∀ child ∈ edge.children, DeepOrdinary child) :
      DeepOrdinary (.node entry edges depth free)

private def ValueSpec (height : Nat) (original copied : Value Symbol Guard) : Prop :=
  DeepOrdinary copied ∧ MergedOrdinaryHeight.height copied ≤ height ∧
    ∀ holds ambient term, meaning holds ambient copied term ↔ meaning holds ambient original term ∧ term.height ≤ height

private def EdgeSpec (height : Nat) (original copied : EdgeValue Symbol Guard) : Prop :=
  (∀ child ∈ copied.children, DeepOrdinary child ∧ MergedOrdinaryHeight.height child ≤ height) ∧
    ∀ holds ambient term, EdgeMeaning (meaning holds ambient) holds copied term ↔
      EdgeMeaning (meaning holds ambient) holds original term ∧ term.height ≤ height + 1

private def MemoSpec (state : State Symbol Guard) (memo : Memo Symbol Guard) : Prop :=
  ∀ key copied, memo key = some copied → Available state copied ∧ copied.free = [] ∧
    ∃ original entry, Available state original ∧ original.free = [] ∧ entryOf original = some entry ∧
      entry.identity = key.2 ∧ ValueSpec (key.1 + 1).toNat original copied

private theorem memo_keeps {before after : State Symbol Guard} {memo : Memo Symbol Guard}
    (keeps : Keeps before after) (spec : MemoSpec before memo) : MemoSpec after memo := by
  intro key copied found
  obtain ⟨available, closed, original, entry, sourceAvailable, sourceClosed, field, identity, bounded⟩ := spec key copied found
  exact ⟨keeps.available copied available, closed, original, entry, keeps.available original sourceAvailable,
    sourceClosed, field, identity, bounded⟩

private theorem memo_put {state : State Symbol Guard} {memo : Memo Symbol Guard}
    (spec : MemoSpec state memo) (key : Int × Nat) (copied original : Value Symbol Guard)
    (entry : Interned InternedBinderProtocol.NodeKey) (available : Available state copied) (closed : copied.free = [])
    (sourceAvailable : Available state original) (sourceClosed : original.free = [])
    (field : entryOf original = some entry) (identity : entry.identity = key.2)
    (bounded : ValueSpec (key.1 + 1).toNat original copied) : MemoSpec state (Cache.put memo key copied) := by
  intro other actual found
  by_cases same : other = key
  · subst other
    simp [Cache.put] at found
    subst actual
    exact ⟨available, closed, original, entry, sourceAvailable, sourceClosed, field, identity, bounded⟩
  · exact spec other actual (by simpa only [Cache.put, ite_eq_right same] using found)

private theorem all₂_right {R : A → B → Prop} {original : List A} {copied : List B}
    (related : All₂ R original copied) (value : B) (member : value ∈ copied) : ∃ source ∈ original, R source value := by
  induction related with
  | nil => cases member
  | @cons source result sources results head tail ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨source, List.mem_cons_self, head⟩
      · obtain ⟨earlier, present, relation⟩ := ih member
        exact ⟨earlier, List.mem_cons_of_mem source present, relation⟩

private theorem all₂_transfer {R : B → C → Prop} {S : A → C → Prop}
    {original : List A} {copied : List B}
    (related : All₂ (fun source result => ∀ term, R result term ↔ S source term) original copied) (terms : List C) :
    All₂ R copied terms ↔ All₂ S original terms := by
  induction related generalizing terms with
  | nil =>
      constructor <;> intro runs <;> cases runs <;> exact .nil
  | cons head tail ih =>
      constructor
      · intro runs
        cases runs with
        | cons first rest => exact .cons ((head _).mp first) ((ih _).mp rest)
      · intro runs
        cases runs with
        | cons first rest => exact .cons ((head _).mpr first) ((ih _).mpr rest)

private theorem children_exact (height : Nat) {original copied : List (Value Symbol Guard)}
    (related : All₂ (ValueSpec height) original copied) (holds : Guard → Term Symbol → Bool)
    (ambient : Env Symbol) (terms : List (Term Symbol)) :
    All₂ (meaning holds ambient) copied terms ↔ All₂ (meaning holds ambient) original terms ∧ forestHeight terms ≤ height := by
  have paired := related.imp (fun _ _ spec => spec.2.2 holds ambient)
  exact (all₂_transfer paired terms).trans (all₂_height_iff (meaning holds ambient) original terms height)

private theorem rebuilt_edge_spec [DecidableEq (EdgeKey Symbol Guard)] (height : Nat)
    (original : EdgeValue Symbol Guard) (copied : List (Value Symbol Guard))
    (related : All₂ (ValueSpec height) original.children copied) (state : State Symbol Guard)
    (semantic : SemanticReady state) (available : Values state copied) :
    EdgeSpec height original (InternedConstructorTemplates.run
      (makeEdge original.entry.key.symbol original.entry.key.constraint copied) state).1 := by
  have fields := InternedGuardedExecutionLists.makeEdge_fields original.entry.key.symbol original.entry.key.constraint
    copied state semantic.ready.semantic.1.normal.facts.coherent semantic.ready.semantic.1.normal.facts.cached available
  refine ⟨?_, ?_⟩
  · intro child member
    have copiedMember : child ∈ copied := by simpa only [fields.2] using member
    obtain ⟨source, _, spec⟩ := all₂_right related child copiedMember
    exact ⟨spec.1, spec.2.1⟩
  · intro holds ambient term
    constructor
    · rintro ⟨terms, root, runs, guard⟩
      have runs' : All₂ (meaning holds ambient) copied terms := by simpa only [fields.2] using runs
      obtain ⟨sourceRuns, bounded⟩ := (children_exact height related holds ambient terms).mp runs'
      have root' : term = .node original.entry.key.symbol terms := by simpa only [fields.1] using root
      have guard' : holds original.entry.key.constraint term = true := by simpa only [fields.1] using guard
      refine ⟨⟨terms, root', sourceRuns, guard'⟩, ?_⟩
      rw [root']
      simpa only [Term.height, forestHeight] using Nat.succ_le_succ bounded
    · rintro ⟨⟨terms, root, runs, guard⟩, bounded⟩
      have childBound : forestHeight terms ≤ height := by
        rw [root] at bounded
        have parentBound : forestHeight terms + 1 ≤ height + 1 := by
          simpa only [Term.height, forestHeight] using bounded
        omega
      refine ⟨terms, ?_, ?_, ?_⟩
      · simpa only [fields.1] using root
      · have copiedRuns := (children_exact height related holds ambient terms).mpr ⟨runs, childBound⟩
        simpa only [fields.2] using copiedRuns
      · simpa only [fields.1] using guard

private theorem edges_exact (height : Nat) {original copied : List (EdgeValue Symbol Guard)}
    (related : All₂ (EdgeSpec height) original copied) (holds : Guard → Term Symbol → Bool)
    (ambient : Env Symbol) (term : Term Symbol) :
    (∃ edge ∈ copied, EdgeMeaning (meaning holds ambient) holds edge term) ↔
      ∃ edge ∈ original, EdgeMeaning (meaning holds ambient) holds edge term ∧ term.height ≤ height + 1 := by
  induction related with
  | nil => simp
  | cons head tail ih =>
      rw [InternedGuardedExecutionLists.exists_cons, InternedGuardedExecutionLists.exists_cons]
      exact or_congr (head.2 holds ambient term) ih

private theorem retained_exact (height : Nat) (original : List (EdgeValue Symbol Guard))
    (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol) (term : Term Symbol) :
    (∃ edge ∈ SourceNativeBoundDepth.retained (height : Int) original,
      EdgeMeaning (meaning holds ambient) holds edge term ∧ term.height ≤ height + 1) ↔
      (∃ edge ∈ original, EdgeMeaning (meaning holds ambient) holds edge term) ∧ term.height ≤ height + 1 := by
  constructor
  · rintro ⟨edge, member, accepted, bound⟩
    exact ⟨⟨edge, (List.mem_filter.mp member).1, accepted⟩, bound⟩
  · rintro ⟨⟨edge, member, accepted⟩, bound⟩
    refine ⟨edge, List.mem_filter.mpr ⟨member, ?_⟩, accepted, bound⟩
    by_cases positive : 0 < height
    · simp [positive]
    · have zero : height = 0 := by omega
      subst height
      obtain ⟨terms, root, runs, _⟩ := accepted
      have forestZero : forestHeight terms = 0 := by
        rw [root] at bound
        have parentBound : forestHeight terms + 1 ≤ 0 + 1 := by
          simpa only [Term.height, forestHeight] using bound
        omega
      have noTerms : terms = [] := by
        cases terms with
        | nil => rfl
        | cons first rest =>
            have positive := first.height_pos
            simp only [forestHeight, List.foldr_cons] at forestZero
            omega
      subst terms
      have noChildren : edge.children = [] := List.length_eq_zero_iff.mp (by simpa using runs.length_eq)
      rw [noChildren]
      rfl

private theorem makeNode_deep [DecidableEq (EdgeKey Symbol Guard)] (input : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (semantic : SemanticReady state) (resident : Edges state input)
    (deep : ∀ edge ∈ input, ∀ child ∈ edge.children, DeepOrdinary child) :
    DeepOrdinary (InternedConstructorTemplates.run (makeNode input) state).1 := by
  have selected : ∀ edge ∈ canonicalEdges (surviving input), ∀ child ∈ edge.children, DeepOrdinary child := by
    intro edge member
    exact deep edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  have selectedResident : Edges state (canonicalEdges (surviving input)) := by
    intro edge member
    exact resident edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  unfold makeNode
  dsimp only
  split
  · exact .empty
  · rename_i first rest same
    obtain ⟨entry, readback⟩ := identifyNode_readback (first :: rest) state
      semantic.ready.semantic.1.normal.facts.coherent semantic.ready.semantic.1.normal.facts.linked
      (by simpa only [Edges, same] using selectedResident)
    simp only [InternedConstructorTemplates.run, readback, identifyNode]
    exact .node entry (first :: rest) _ _ (by simpa only [same] using selected)

private theorem node_spec [DecidableEq (EdgeKey Symbol Guard)] (height : Nat)
    (source : Value Symbol Guard) (original copied : List (EdgeValue Symbol Guard))
    (related : All₂ (EdgeSpec height) (SourceNativeBoundDepth.retained (height : Int) original) copied)
    (before state : State Symbol Guard) (sourceSemantic : SemanticReady before)
    (sourceAvailable : Available before source) (sourceClosed : source.free = [])
    (read : SourceEqualityProjectionRead.Read source before original state)
    (current : State Symbol Guard) (semantic : SemanticReady current) (resident : Edges current copied) :
    ValueSpec (height + 1) source (InternedConstructorTemplates.run (makeNode copied) current).1 := by
  have deep : ∀ edge ∈ copied, ∀ child ∈ edge.children, DeepOrdinary child := by
    intro edge member child inside
    obtain ⟨original, _, spec⟩ := all₂_right related edge member
    exact (spec.1 child inside).1
  have bounded : ∀ edge ∈ copied, MergedOrdinaryHeight.edgeHeight edge + 1 ≤ height + 1 := by
    intro edge member
    obtain ⟨original, _, spec⟩ := all₂_right related edge member
    have bound : MergedOrdinaryHeight.edgeHeight edge ≤ height := by
      cases edge with
      | mk entry children => exact (MergedOrdinaryHeight.childrenHeight_le children height).mpr (fun child inside => (spec.1 child inside).2)
    omega
  refine ⟨makeNode_deep copied current semantic resident deep,
    MergedOrdinaryHeight.makeNode_bound copied current semantic.ready.semantic.1.normal.facts.coherent
      semantic.ready.semantic.1.normal.facts.linked resident (height + 1) bounded, ?_⟩
  intro holds ambient term
  rw [MergedColdInterpretation.makeNode_exact current semantic.ready.semantic.1.normal.facts
    (meaning holds ambient) copied resident holds (InternedGuardedLanguage.laws holds ambient) term]
  exact (edges_exact height related holds ambient term).trans
    ((retained_exact height original holds ambient term).trans
      (and_congr (read.exact sourceSemantic sourceAvailable sourceClosed holds ambient term) Iff.rfl))

private def Observes (height : Nat)
    (call : Value Symbol Guard → State Symbol Guard → Memo Symbol Guard → Result Symbol Guard (Value Symbol Guard)) : Prop :=
  ∀ value before memo result after finalMemo, SemanticReady before → Available before value → value.free = [] →
    MemoSpec before memo → call value before memo = (.done result after, finalMemo) →
    SemanticReady after ∧ Keeps before after ∧ Available after result ∧ result.free = [] ∧
      MemoSpec after finalMemo ∧ ValueSpec height value result

private theorem bind_done {actual : Result Symbol Guard First}
    {next : First → State Symbol Guard → Memo Symbol Guard → Result Symbol Guard Output}
    {result : Output} {after : State Symbol Guard} {finalMemo : Memo Symbol Guard}
    (observed : SourceNativeBoundDepth.bind actual next = (.done result after, finalMemo)) :
    ∃ value middle memo, actual = (.done value middle, memo) ∧ next value middle memo = (.done result after, finalMemo) := by
  rcases actual with ⟨outcome, memo⟩
  cases outcome with
  | done value middle => exact ⟨value, middle, memo, rfl, observed⟩
  | failed fault middle => simp [SourceNativeBoundDepth.bind] at observed

private theorem children_observed (height : Nat)
    (copy : Value Symbol Guard → State Symbol Guard → Memo Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (observe : Observes height copy) (original : List (Value Symbol Guard))
    (before : State Symbol Guard) (memo : Memo Symbol Guard) (result : List (Value Symbol Guard))
    (after : State Symbol Guard) (finalMemo : Memo Symbol Guard) (semantic : SemanticReady before)
    (available : Values before original) (closed : ClosedValues original) (memoSpec : MemoSpec before memo)
    (observed : SourceNativeBoundDepth.children copy original before memo = (.done result after, finalMemo)) :
    SemanticReady after ∧ Keeps before after ∧ Values after result ∧ ClosedValues result ∧
      MemoSpec after finalMemo ∧ All₂ (ValueSpec height) original result := by
  induction original generalizing before memo result after finalMemo with
  | nil =>
      simp only [SourceNativeBoundDepth.children, Prod.mk.injEq, MergedSourceComparison.Result.done.injEq] at observed
      rcases observed with ⟨⟨resultEq, heapEq⟩, memoEq⟩
      subst result
      subst after
      subst finalMemo
      refine ⟨semantic, SourceEqualityRequiredCache.pure_keeps before semantic.ready, ?_, ?_, memoSpec, .nil⟩
      · intro value member
        cases member
      · intro value member
        cases member
  | cons first rest ih =>
      obtain ⟨firstResult, middle, nextMemo, firstDone, remaining⟩ := bind_done
        (by simpa only [SourceNativeBoundDepth.children] using observed)
      obtain ⟨restResult, last, saved, restDone, finished⟩ := bind_done remaining
      simp only [Prod.mk.injEq, MergedSourceComparison.Result.done.injEq] at finished
      rcases finished with ⟨⟨resultEq, heapEq⟩, memoEq⟩
      subst result
      subst after
      subst finalMemo
      obtain ⟨middleSemantic, firstKeeps, firstAvailable, firstClosed, firstMemo, firstSpec⟩ :=
        observe first before memo firstResult middle nextMemo semantic (available first List.mem_cons_self)
          (closed first List.mem_cons_self) memoSpec firstDone
      have remainingAvailable : Values middle rest := by
        intro value member
        exact firstKeeps.available value (available value (List.mem_cons_of_mem first member))
      obtain ⟨lastSemantic, restKeeps, restAvailable, restClosed, restMemo, restSpecs⟩ :=
        ih middle nextMemo restResult last saved middleSemantic remainingAvailable
          (fun value member => closed value (List.mem_cons_of_mem first member)) firstMemo restDone
      refine ⟨lastSemantic, firstKeeps.trans restKeeps, ?_, ?_, restMemo, .cons firstSpec restSpecs⟩
      · intro value member
        rcases List.mem_cons.mp member with rfl | member
        · exact restKeeps.available value firstAvailable
        · exact restAvailable value member
      · intro value member
        rcases List.mem_cons.mp member with rfl | member
        · exact firstClosed
        · exact restClosed value member

private theorem edges_observed [DecidableEq (EdgeKey Symbol Guard)] (height : Nat)
    (copy : Value Symbol Guard → State Symbol Guard → Memo Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (observe : Observes height copy) (original : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (memo : Memo Symbol Guard) (result : List (EdgeValue Symbol Guard))
    (after : State Symbol Guard) (finalMemo : Memo Symbol Guard) (semantic : SemanticReady before)
    (resident : Edges before original) (closed : ClosedEdges original) (memoSpec : MemoSpec before memo)
    (observed : SourceNativeBoundDepth.edges copy original before memo = (.done result after, finalMemo)) :
    SemanticReady after ∧ Keeps before after ∧ Edges after result ∧ ClosedEdges result ∧
      MemoSpec after finalMemo ∧ All₂ (EdgeSpec height) original result := by
  induction original generalizing before memo result after finalMemo with
  | nil =>
      simp only [SourceNativeBoundDepth.edges, Prod.mk.injEq, MergedSourceComparison.Result.done.injEq] at observed
      rcases observed with ⟨⟨resultEq, heapEq⟩, memoEq⟩
      subst result
      subst after
      subst finalMemo
      refine ⟨semantic, SourceEqualityRequiredCache.pure_keeps before semantic.ready, ?_, ?_, memoSpec, .nil⟩
      · intro edge member
        cases member
      · intro edge member
        cases member
  | cons first rest ih =>
      obtain ⟨copiedChildren, middle, nextMemo, childrenDone, remaining⟩ := bind_done
        (by simpa only [SourceNativeBoundDepth.edges] using observed)
      let rebuilt := InternedConstructorTemplates.run
        (makeEdge first.entry.key.symbol first.entry.key.constraint copiedChildren) middle
      change SourceNativeBoundDepth.bind (SourceNativeBoundDepth.edges copy rest rebuilt.2 nextMemo)
        (fun values state saved => (.done (rebuilt.1 :: values) state, saved)) = (.done result after, finalMemo) at remaining
      obtain ⟨restResult, last, saved, restDone, finished⟩ := bind_done remaining
      simp only [Prod.mk.injEq, MergedSourceComparison.Result.done.injEq] at finished
      rcases finished with ⟨⟨resultEq, heapEq⟩, memoEq⟩
      subst result
      subst after
      subst finalMemo
      have originalChildren : Values before first.children :=
        semantic.ready.semantic.1.normal.facts.cached.edges first.entry.key first (resident first List.mem_cons_self)
      obtain ⟨middleSemantic, childKeeps, childAvailable, childClosed, childMemo, childSpecs⟩ :=
        children_observed height copy observe first.children before memo copiedChildren middle nextMemo semantic
          originalChildren (closed first List.mem_cons_self) memoSpec childrenDone
      have checked := SourceEqualityRequiredCache.edge first.entry.key.symbol first.entry.key.constraint
        copiedChildren middle middleSemantic.ready childAvailable
      have edgeSemantic : SemanticReady rebuilt.2 :=
        SourceEqualityRequiredSemanticCache.edge first.entry.key.symbol first.entry.key.constraint
          copiedChildren middle middleSemantic childAvailable
      have edgeKeeps : Keeps middle rebuilt.2 := checked.1
      have edgeResident : EdgeResident rebuilt.2 rebuilt.1 := checked.2.1
      have edgeClosed : ClosedValues rebuilt.1.children := by
        rw [checked.2.2]
        exact childClosed
      have edgeSpec : EdgeSpec height first rebuilt.1 :=
        rebuilt_edge_spec height first copiedChildren childSpecs middle middleSemantic childAvailable
      have headKeeps := childKeeps.trans edgeKeeps
      have restResident : Edges rebuilt.2 rest := by
        intro edge member
        exact edge_grows before rebuilt.2 headKeeps.growth edge (resident edge (List.mem_cons_of_mem first member))
      obtain ⟨lastSemantic, restKeeps, restAvailable, restClosed, restMemo, restSpecs⟩ :=
        ih rebuilt.2 nextMemo restResult last saved edgeSemantic restResident
          (fun edge member => closed edge (List.mem_cons_of_mem first member)) (memo_keeps edgeKeeps childMemo) restDone
      refine ⟨lastSemantic, headKeeps.trans restKeeps, ?_, ?_, restMemo, .cons edgeSpec restSpecs⟩
      · intro edge member
        rcases List.mem_cons.mp member with rfl | member
        · exact edge_grows rebuilt.2 last restKeeps.growth rebuilt.1 edgeResident
        · exact restAvailable edge member
      · intro edge member
        rcases List.mem_cons.mp member with rfl | member
        · exact edgeClosed
        · exact restClosed edge member

private theorem interned_observed [DecidableEq (EdgeKey Symbol Guard)] (fuel height : Nat)
    (observe : Observes height (atHeight (Symbol := Symbol) (Guard := Guard) fuel height))
    (entry : Interned InternedBinderProtocol.NodeKey) (value : Value Symbol Guard) (field : entryOf value = some entry)
    (before : State Symbol Guard) (memo : Memo Symbol Guard) (result : Value Symbol Guard)
    (after : State Symbol Guard) (finalMemo : Memo Symbol Guard) (semantic : SemanticReady before)
    (available : Available before value) (closed : value.free = []) (memoSpec : MemoSpec before memo)
    (observed : SourceNativeBoundDepth.interned fuel (height : Int) entry.identity value
      (atHeight fuel height) before memo = (.done result after, finalMemo)) :
    SemanticReady after ∧ Keeps before after ∧ Available after result ∧ result.free = [] ∧
      MemoSpec after finalMemo ∧ ValueSpec (height + 1) value result := by
  cases found : memo ((height : Int), entry.identity) with
  | some cached =>
      simp only [SourceNativeBoundDepth.interned, found, Prod.mk.injEq, MergedSourceComparison.Result.done.injEq] at observed
      rcases observed with ⟨⟨resultEq, heapEq⟩, memoEq⟩
      subst result
      subst after
      subst finalMemo
      obtain ⟨cachedAvailable, cachedClosed, original, originalEntry, originalAvailable, originalClosed,
          originalField, originalIdentity, spec⟩ := memoSpec _ _ found
      have same : value = original := resident_identity_unique before semantic.ready.semantic.1.normal.facts.coherent
        value original available.resident originalAvailable.resident entry originalEntry field originalField originalIdentity.symm
      have keyHeight : ((height : Int) + 1).toNat = height + 1 := by omega
      have bounded : ValueSpec (height + 1) value cached := by
        rw [same]
        simpa only [keyHeight] using spec
      exact ⟨semantic, SourceEqualityRequiredCache.pure_keeps before semantic.ready,
        cachedAvailable, cachedClosed, memoSpec, bounded⟩
  | none =>
      cases readDone : MergedFreshOrdinaryExposure.nodeEdges fuel value before with
      | unresolved name stopped => simp [SourceNativeBoundDepth.interned, found, readDone] at observed
      | pending key stopped => simp [SourceNativeBoundDepth.interned, found, readDone] at observed
      | exhausted stopped => simp [SourceNativeBoundDepth.interned, found, readDone] at observed
      | done original afterRead =>
          obtain ⟨copied, middle, nextMemo, copiedDone, finished⟩ := bind_done
            (by simpa only [SourceNativeBoundDepth.interned, found, readDone] using observed)
          let bounded := InternedConstructorTemplates.run (makeNode copied) middle
          change (MergedSourceComparison.Result.done bounded.1 bounded.2,
            Cache.put nextMemo ((height : Int), entry.identity) bounded.1) =
            (MergedSourceComparison.Result.done result after, finalMemo) at finished
          simp only [Prod.mk.injEq, MergedSourceComparison.Result.done.injEq] at finished
          rcases finished with ⟨⟨resultEq, heapEq⟩, memoEq⟩
          subst result
          subst after
          subst finalMemo
          have trace : SourceEqualityProjectionRead.Read value before original afterRead := .done fuel readDone
          obtain ⟨readKeeps, readSemantic, readResident, readClosed⟩ := trace.verified semantic available closed
          have retainedResident : Edges afterRead (SourceNativeBoundDepth.retained (height : Int) original) := by
            intro edge member
            exact readResident edge (List.mem_filter.mp member).1
          have retainedClosed : ClosedEdges (SourceNativeBoundDepth.retained (height : Int) original) := by
            intro edge member
            exact readClosed edge (List.mem_filter.mp member).1
          obtain ⟨middleSemantic, copiedKeeps, copiedResident, copiedClosed, copiedMemo, copiedSpecs⟩ :=
            edges_observed height (atHeight fuel height) observe
              (SourceNativeBoundDepth.retained (height : Int) original) afterRead memo copied middle nextMemo
              readSemantic retainedResident retainedClosed (memo_keeps readKeeps memoSpec) copiedDone
          have checked := SourceEqualityRequiredCache.node copied middle middleSemantic.ready copiedResident copiedClosed
          have finalSemantic : SemanticReady bounded.2 :=
            SourceEqualityRequiredSemanticCache.node copied middle middleSemantic copiedResident copiedClosed
          have nodeKeeps : Keeps middle bounded.2 := checked.1
          have finalAvailable : Available bounded.2 bounded.1 := checked.2.1
          have finalClosed : bounded.1.free = [] := checked.2.2.1
          have keeps := readKeeps.trans (copiedKeeps.trans nodeKeeps)
          have resultSpec : ValueSpec (height + 1) value bounded.1 :=
            node_spec height value original copied copiedSpecs before afterRead semantic available closed trace
              middle middleSemantic copiedResident
          have keyHeight : ((height : Int) + 1).toNat = height + 1 := by omega
          have storedSpec : ValueSpec ((height : Int) + 1).toNat value bounded.1 := by
            simpa only [keyHeight] using resultSpec
          exact ⟨finalSemantic, keeps, finalAvailable, finalClosed,
            memo_put (memo_keeps nodeKeeps copiedMemo) ((height : Int), entry.identity) bounded.1 value entry
              finalAvailable finalClosed (keeps.available value available) closed field rfl storedSpec,
            resultSpec⟩

private theorem empty_spec (height : Nat) : ValueSpec height (.empty : Value Symbol Guard) .empty := by
  refine ⟨.empty, Nat.zero_le _, ?_⟩
  intro holds ambient term
  simp only [InternedGuardedLanguage.meaning, false_and]

private theorem zero_spec (value : Value Symbol Guard) : ValueSpec 0 value .empty := by
  refine ⟨.empty, Nat.le_refl _, ?_⟩
  intro holds ambient term
  constructor
  · intro accepted
    exact False.elim ((InternedGuardedLanguage.laws holds ambient).empty term accepted)
  · rintro ⟨_, bound⟩
    have positive := term.height_pos
    omega

private theorem worker_observed [DecidableEq (EdgeKey Symbol Guard)] (fuel height : Nat) :
    Observes height (atHeight (Symbol := Symbol) (Guard := Guard) fuel height) := by
  induction height with
  | zero =>
      intro value before memo result after finalMemo semantic available closed memoSpec observed
      cases value
      case reference name => cases closed
      all_goals
        simp only [atHeight, Prod.mk.injEq, MergedSourceComparison.Result.done.injEq] at observed
        rcases observed with ⟨⟨resultEq, heapEq⟩, memoEq⟩
        subst result
        subst after
        subst finalMemo
        exact ⟨semantic, SourceEqualityRequiredCache.pure_keeps before semantic.ready,
          empty_available before, rfl, memoSpec, zero_spec _⟩
  | succ height ih =>
      intro value before memo result after finalMemo semantic available closed memoSpec observed
      cases value with
      | reference name => cases closed
      | empty =>
          simp only [atHeight, Prod.mk.injEq, MergedSourceComparison.Result.done.injEq] at observed
          rcases observed with ⟨⟨resultEq, heapEq⟩, memoEq⟩
          subst result
          subst after
          subst finalMemo
          exact ⟨semantic, SourceEqualityRequiredCache.pure_keeps before semantic.ready,
            empty_available before, rfl, memoSpec, empty_spec (height + 1)⟩
      | node entry rows cachedDepth free =>
          exact interned_observed fuel height ih entry (.node entry rows cachedDepth free) rfl before memo result after
            finalMemo semantic available closed memoSpec (by simpa only [atHeight] using observed)
      | union entry members cachedDepth free =>
          exact interned_observed fuel height ih entry (.union entry members cachedDepth free) rfl before memo result after
            finalMemo semantic available closed memoSpec (by simpa only [atHeight] using observed)
      | mu entry body depthShape ordinaryShape =>
          exact interned_observed fuel height ih entry (.mu entry body depthShape ordinaryShape) rfl before memo result after
            finalMemo semantic available closed memoSpec (by simpa only [atHeight] using observed)

/-- One existing completion receipt has exactly the original bounded independent language. -/
theorem complete_exact [DecidableEq (EdgeKey Symbol Guard)] (depth : Int) (root : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Available before root) (closed : root.free = []) :
    ∃ cutoff result after memo,
      (∀ fuel, cutoff ≤ fuel → SourceNativeBoundDepth.boundDepth fuel depth root before = (.done result after, memo)) ∧
      SemanticReady after ∧ Keeps before after ∧ Available after root ∧ root.free = [] ∧
      Available after result ∧ result.free = [] ∧
      (∀ key value, memo key = some value → Available after value ∧ value.free = []) ∧
      DeepOrdinary result ∧ MergedOrdinaryHeight.height result ≤ (depth + 1).toNat ∧
      (∀ holds ambient term, meaning holds ambient result term ↔
        meaning holds ambient root term ∧ (term.height : Int) ≤ depth + 1) := by
  obtain ⟨cutoff, result, after, memo, stable, finalSemantic, keeps, rootAvailable, rootClosed,
      resultAvailable, resultClosed, memoAvailable⟩ :=
    SourceNativeBoundDepthCompletion.complete depth root before semantic available closed
  have actual : atHeight cutoff (depth + 1).toNat root before (fun _ => none) = (.done result after, memo) := by
    simpa only [SourceNativeBoundDepth.boundDepth, SourceNativeBoundDepth.run] using stable cutoff (Nat.le_refl _)
  obtain ⟨_, _, _, _, _, spec⟩ := worker_observed (Symbol := Symbol) (Guard := Guard) cutoff (depth + 1).toNat root before (fun _ => none)
    result after memo semantic available closed (by intro key value impossible; cases impossible) actual
  refine ⟨cutoff, result, after, memo, stable, finalSemantic, keeps, rootAvailable, rootClosed,
    resultAvailable, resultClosed, memoAvailable, spec.1, spec.2.1, ?_⟩
  intro holds ambient term
  have height : term.height ≤ (depth + 1).toNat ↔ (term.height : Int) ≤ depth + 1 := by
    have positive := term.height_pos
    omega
  exact (spec.2.2 holds ambient term).trans (and_congr Iff.rfl height)

end MicroCFTA.SourceNativeBoundDepthMeaning
