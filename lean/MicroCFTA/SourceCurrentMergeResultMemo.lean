import MicroCFTA.SourceCurrentMergedQueryMemos

/-!
# Completed resident merge-result memo projection

The unary key retains the source node tag and identity. Each completed entry
retains its original request and a historical actual body execution. Hits
reuse the stored resident result without replaying the body. Misses in this
completed projection retain an explicit body receipt.

The source publishes a lazy candidate before evaluating its body. The
separate publication graph below records lookup, first-writer insertion,
and winner reread without body evaluation. Completion insertion in this
projection is not the source publication point. Recursive memo-aware body
execution, pending thunks, and runtime scheduling remain separate bridges.
-/
namespace MicroCFTA.SourceCurrentMergeResultMemo
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedRecordCoherence (record_cases)
open InternedBinderProtocol (NodeRef)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open InternedGuardedLanguage (meaning)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Value" => InternedConstructorTemplates.Value Symbol Guard
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- Completed entries retain the original producer argument and its literal returned record. -/
structure Entry where
  original : Value
  result : Value

/-- One fixed symbol type and merge operation have one tagged physical-key table. -/
abbrev CompletedMemo := NodeRef → Option Entry

/-- Stored results come from actual historical resident body execution. -/
def Origin [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (top : Guard) (input output : Value) : Prop :=
  ∃ fuel before after, SemanticReady before ∧ Available before input ∧
    SourceMergedWorker.execute clear top fuel input before = .done output after

/-- A completed memo has exact keys, resident records, and actual producer provenance. -/
def Correct [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (top : Guard) (heap : Heap) (memo : CompletedMemo) : Prop :=
  ∀ key entry, memo key = some entry → entry.original.referenceOf = key ∧
    Available heap entry.original ∧ Available heap entry.result ∧ Origin clear top entry.original entry.result

/-- No result is supplied by the initial completed projection. -/
def empty : CompletedMemo := fun _ => none

/-- An empty table satisfies producer provenance in every heap. -/
theorem empty_correct [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (top : Guard) (heap : Heap) : Correct clear top heap empty := by
  intro key entry impossible
  cases impossible

/-- Physical heap growth retains complete entry records and their historical producers. -/
theorem Correct.grows [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {before after : Heap} {memo : CompletedMemo}
    (correct : Correct clear top before memo) (keeps : Keeps before after) : Correct clear top after memo := by
  intro key entry found
  obtain ⟨identity, original, result, origin⟩ := correct key entry found
  exact ⟨identity, keeps.available _ original, keeps.available _ result, origin⟩

/-- Open source body inputs return the same complete record. -/
theorem Origin.open_result [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {input output : Value}
    (origin : Origin clear top input output) (notClosed : input.free ≠ []) : output = input := by
  obtain ⟨fuel, before, after, _, _, done⟩ := origin
  have returned := SourceCurrentMergedHeapEffects.worker_open MergedSourceGrouping.groups clear top
    (MergedOrdinaryHeight.height input) fuel input before notClosed
  exact (MergedSourceComparison.Result.done.inj (returned.symm.trans done)).1.symm

/-- Actual historical body execution derives independent language coverage for its cached result. -/
theorem Origin.covers [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {input output : Value}
    (origin : Origin clear top input output) (holds : Guard → Term Symbol → Bool)
    (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true)
    (topTrue : ∀ term, holds top term = true) :
    ∀ term, meaning holds ambient input term → meaning holds ambient output term := by
  by_cases closed : input.free = []
  · obtain ⟨fuel, before, after, semantic, available, done⟩ := origin
    exact (SourceMergedSoundness.execute_covers clear top holds ambient clearTrue topTrue fuel input before
      semantic available closed output after done).2.2.2
  · rw [origin.open_result closed]
    exact fun _ accepted => accepted

/-- Actual historical completion retains closedness when its original argument is closed. -/
theorem Origin.closed_result [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {input output : Value}
    (origin : Origin clear top input output) (closed : input.free = []) : output.free = [] := by
  obtain ⟨fuel, before, after, semantic, available, done⟩ := origin
  exact (SourceMergedSoundness.execute_covers clear top (fun _ _ => true) (fun _ _ => False)
    (fun _ _ _ => rfl) (fun _ => rfl) fuel input before semantic available closed output after done).2.2.1

/-- Completion records an actual producer result without replacing an earlier completed entry. -/
def remember (memo : CompletedMemo) (input output : Value) : CompletedMemo :=
  keepFirst memo input.referenceOf ⟨input, output⟩

/-- Completing an entry retains every earlier original record and result. -/
theorem remember_extends (memo : CompletedMemo) (input output : Value) :
    Extends memo (remember memo input output) := keepFirst_extends memo input.referenceOf ⟨input, output⟩

/-- An absent completed key records its actual original argument and literal output. -/
theorem remember_absent (memo : CompletedMemo) (input output : Value) (absent : memo input.referenceOf = none) :
    remember memo input output input.referenceOf = some ⟨input, output⟩ := by
  simp only [remember, keepFirst, absent, put, ite_true]

/-- A completed insertion derives all new entry provenance from the actual returned records. -/
theorem remember_correct [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {heap : Heap} {memo : CompletedMemo}
    (correct : Correct clear top heap memo) (input output : Value)
    (inputAvailable : Available heap input) (outputAvailable : Available heap output)
    (origin : Origin clear top input output) : Correct clear top heap (remember memo input output) := by
  intro key entry found
  rcases record_cases memo input.referenceOf key ⟨input, output⟩ entry found with old | ⟨same, entrySame⟩
  · exact correct key entry old
  · subst entry
    exact ⟨same.symm, inputAvailable, outputAvailable, origin⟩

/-- Completed hits skip the body; completed misses retain its actual native merge receipt. -/
inductive CompletedCall [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (top : Guard) {width : Nat} :
    CompletedMemo → Value → Native width Symbol Guard → Value → Native width Symbol Guard → CompletedMemo → Prop where
  | hit (found : memo input.referenceOf = some entry) :
      CompletedCall clear top memo input before entry.result before memo
  | miss (absent : memo input.referenceOf = none)
      (actual : SourceEqualityNativeMerge.Merge clear top input before output after) :
      CompletedCall clear top memo input before output after (remember memo input output)

/-- Every completed lookup preserves earlier complete entries without a validity premise. -/
theorem CompletedCall.extends [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {memo saved : CompletedMemo} {input output : Value}
    {before after : Native width Symbol Guard} (call : CompletedCall clear top memo input before output after saved) :
    Extends memo saved := by
  cases call with
  | hit => exact extends_refl _
  | miss => exact remember_extends _ _ _

/-- A completed present key retains the whole native state and its existing completed memo. -/
theorem CompletedCall.hit_unchanged [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {memo saved : CompletedMemo} {input output : Value}
    {before after : Native width Symbol Guard} (call : CompletedCall clear top memo input before output after saved)
    {entry : Entry} (found : memo input.referenceOf = some entry) :
    after = before ∧ saved = memo ∧ output = entry.result := by
  cases call with
  | hit actual => cases Option.some.inj (actual.symm.trans found); exact ⟨rfl, rfl, rfl⟩
  | miss absent => rw [absent] at found; cases found

/-- A resident cache hit recovers the exact original producer and literal complete result. -/
theorem hit_origin [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {heap : Heap} {memo : CompletedMemo} {input : Value} {entry : Entry}
    (semantic : SemanticReady heap) (available : Available heap input) (correct : Correct clear top heap memo)
    (found : memo input.referenceOf = some entry) :
    entry.original = input ∧ Available heap entry.result ∧ Origin clear top input entry.result := by
  obtain ⟨identity, original, result, origin⟩ := correct _ _ found
  have same := InternedFreshProbeKeys.resident_reference_injective heap semantic.ready.semantic.1.normal.facts.coherent
    entry.original input original.resident available.resident identity
  exact ⟨same, result, same ▸ origin⟩

/-- Native body receipts supply actual historical producer provenance. -/
theorem origin_of_merge [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {input output : Value} {before after : Native width Symbol Guard}
    (actual : SourceEqualityNativeMerge.Merge clear top input before output after)
    (semantic : SemanticReady before.machine.heap) (available : Available before.machine.heap input) :
    Origin clear top input output := by
  cases actual with
  | done fuel done => exact ⟨fuel, before.machine.heap, _, semantic, available, done⟩

/-- Every completed hit or miss recovers actual historical producer execution. -/
theorem CompletedCall.origin [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {memo saved : CompletedMemo} {input output : Value}
    {before after : Native width Symbol Guard} (call : CompletedCall clear top memo input before output after saved)
    (semantic : SemanticReady before.machine.heap) (available : Available before.machine.heap input)
    (correct : Correct clear top before.machine.heap memo) : Origin clear top input output := by
  cases call with
  | hit found => exact (hit_origin semantic available correct found).2.2
  | miss _ actual => exact origin_of_merge actual semantic available

/-- A closed requested record has a closed completed result on hits and misses. -/
theorem CompletedCall.closed_result [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {memo saved : CompletedMemo} {input output : Value}
    {before after : Native width Symbol Guard} (call : CompletedCall clear top memo input before output after saved)
    (semantic : SemanticReady before.machine.heap) (available : Available before.machine.heap input)
    (correct : Correct clear top before.machine.heap memo) (closed : input.free = []) : output.free = [] :=
  (call.origin semantic available correct).closed_result closed

/-- Global receipts distinguish a completed result hit from actual miss body execution. -/
inductive GlobalReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat} :
    {clear : Guard → Bool} → {top : Guard} → {memo saved : CompletedMemo} → {input output : Value} →
    {before after : Native width Symbol Guard} → CompletedCall clear top memo input before output after saved →
      Memos → Memos → Prop where
  | hit {clear : Guard → Bool} {top : Guard} {memo : CompletedMemo} {input : Value}
      {before : Native width Symbol Guard} {entry : Entry} (found : memo input.referenceOf = some entry)
      (memos : Memos) : GlobalReads
        (CompletedCall.hit (clear := clear) (top := top) (before := before) found) memos memos
  | miss {clear : Guard → Bool} {top : Guard} {memo : CompletedMemo} {input output : Value}
      {before after : Native width Symbol Guard} {memos final : Memos}
      (absent : memo input.referenceOf = none)
      (actual : SourceEqualityNativeMerge.Merge clear top input before output after)
      (receipt : SourceCurrentMergedQueryMemos.MergeReads actual memos final) :
      GlobalReads (CompletedCall.miss absent actual) memos final

/-- Completed result reuse and actual body receipts retain both query tables. -/
theorem GlobalReads.query [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {memo saved : CompletedMemo} {input output : Value}
    {before after : Native width Symbol Guard} {call : CompletedCall clear top memo input before output after saved}
    {memos final : Memos} (receipt : GlobalReads call memos final) : final.query = memos.query := by
  cases receipt with
  | hit => rfl
  | miss _ _ actual => exact actual.query

/-- A completed lookup derives producer provenance, resident output, and all returned memo invariants. -/
theorem verified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {memo saved : CompletedMemo} {input output : Value} {before after : Native width Symbol Guard}
    (call : CompletedCall clear top memo input before output after saved)
    (ready : SourceEqualityNativeScoped.IdleReady emptyGuard conjoin before)
    (costs : CostHeap before.machine.heap) (available : Available before.machine.heap input)
    (correct : Correct clear top before.machine.heap memo) (memos : Memos)
    (valid : EndpointMemoGateTrace.Valid before.machine.heap memos) :
    ∃ final, GlobalReads call memos final ∧
      SourceCurrentSubsumesQueryMemos.Effect before.machine.heap after.machine.heap memos final ∧
      SourceEqualityNativeScoped.IdleReady emptyGuard conjoin after ∧ Available after.machine.heap output ∧
      Correct clear top after.machine.heap saved ∧ Extends memo saved ∧ Origin clear top input output ∧
      after.nodes = before.nodes ∧ after.edges = before.edges ∧ after.machine.domains = before.machine.domains := by
  cases call with
  | hit found =>
      have entry := hit_origin ready.semantic available correct found
      exact ⟨memos, .hit found memos, ⟨pure_keeps _ ready.semantic.ready, ready.semantic, costs, valid, extends_refl _, rfl⟩,
        ready, entry.2.1, correct, extends_refl _, entry.2.2, rfl, rfl, rfl⟩
  | miss absent actual =>
      obtain ⟨final, receipt, effects, afterReady, resultAvailable, nodes, edges, domains⟩ :=
        SourceCurrentMergedQueryMemos.merge_memos actual ready costs available memos valid
      have origin := origin_of_merge actual ready.semantic available
      exact ⟨final, .miss absent actual receipt, effects, afterReady, resultAvailable,
        remember_correct (correct.grows effects.keeps) input output (effects.keeps.available input available) resultAvailable origin,
        remember_extends _ _ _, origin, nodes, edges, domains⟩

/-- Every completed cache request retains independent accepted input terms. -/
theorem included [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {memo saved : CompletedMemo} {input output : Value}
    {before after : Native width Symbol Guard} (call : CompletedCall clear top memo input before output after saved)
    (semantic : SemanticReady before.machine.heap) (available : Available before.machine.heap input)
    (correct : Correct clear top before.machine.heap memo) (holds : Guard → Term Symbol → Bool)
    (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true)
    (topTrue : ∀ term, holds top term = true) :
    ∀ term, meaning holds ambient input term → meaning holds ambient output term := by
  cases call with
  | hit found => exact (hit_origin semantic available correct found).2.2.covers holds ambient clearTrue topTrue
  | miss _ actual => exact (origin_of_merge actual semantic available).covers holds ambient clearTrue topTrue

/-- Literal key lookup chooses a completed hit or an actual finitely completed resident body. -/
theorem complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (memo : CompletedMemo) (input : Value) (before : Native width Symbol Guard)
    (ready : SourceEqualityNativeScoped.IdleReady emptyGuard conjoin before)
    (available : Available before.machine.heap input) :
    ∃ output after saved, CompletedCall clear top memo input before output after saved := by
  cases found : memo input.referenceOf with
  | some entry => exact ⟨entry.result, before, memo, .hit found⟩
  | none =>
      by_cases closed : input.free = []
      · obtain ⟨output, after, actual, _⟩ := SourceEqualityNativeMerge.complete emptyGuard conjoin clear top input before ready available closed
        exact ⟨output, after, _, .miss found actual⟩
      · have done := SourceCurrentMergedHeapEffects.worker_open MergedSourceGrouping.groups clear top
          (MergedOrdinaryHeight.height input) 0 input before.machine.heap closed
        exact ⟨input, SourceEqualityNativeScoped.advanceHeap before before.machine.heap, _, .miss found (.done 0 done)⟩



/-- A producer names a lazy candidate and retains its captured original argument.
The ticket is an abstract thunk name, not a source node identity allocation. -/
structure Producer where
  ticket : Nat
  original : Value

/-- The publication table contains producers before their results are demanded. -/
abbrev Published := NodeRef → Option Producer

/-- Every published producer retains the tagged key of its captured original argument. -/
def ProducersCorrect (table : Published) : Prop :=
  ∀ key producer, table key = some producer → producer.original.referenceOf = key

/-- Finite intervening source inserts use each producer's own captured physical key. -/
def publishMany (table : Published) (producers : List Producer) : Published :=
  updates table (producers.map fun producer => (producer.original.referenceOf, producer))

/-- Arbitrary intervening first-writer inserts retain all earlier producer entries. -/
theorem publishMany_extends (table : Published) (producers : List Producer) : Extends table (publishMany table producers) :=
  updates_extend table _

/-- First-writer publication retains or installs the exact captured producer key. -/
theorem keepFirst_producers (table : Published) (correct : ProducersCorrect table) (producer : Producer) :
    ProducersCorrect (keepFirst table producer.original.referenceOf producer) := by
  intro key actual found
  rcases record_cases table producer.original.referenceOf key producer actual found with old | ⟨same, equal⟩
  · exact correct key actual old
  · subst actual
    exact same.symm

/-- Each intervening source insert derives producer-key coherence without a final-table premise. -/
theorem publishMany_correct (table : Published) (correct : ProducersCorrect table) (producers : List Producer) :
    ProducersCorrect (publishMany table producers) := by
  induction producers generalizing table with
  | nil => exact correct
  | cons producer rest ih => exact ih _ (keepFirst_producers table correct producer)

/-- Atomic first-writer insertion and a later read return the same winner. -/
theorem reread_winner (table : Published) (input : Value) (ticket : Nat) (later : List Producer) :
    let candidate : Producer := ⟨ticket, input⟩
    let saved := publishMany (keepFirst table input.referenceOf candidate) later
    ∃ winner, keepFirst table input.referenceOf candidate input.referenceOf = some winner ∧
      saved input.referenceOf = some winner ∧ winner = (table input.referenceOf).getD candidate := by
  dsimp only
  cases found : table input.referenceOf with
  | some winner =>
      have selected := keepFirst_existing found (⟨ticket, input⟩ : Producer)
      exact ⟨winner, selected, publishMany_extends _ later _ _ selected, by simp only [Option.getD_some]⟩
  | none =>
      have selected : keepFirst table input.referenceOf (⟨ticket, input⟩ : Producer) input.referenceOf = some ⟨ticket, input⟩ := by
        simp only [keepFirst, found, put, ite_true]
      exact ⟨⟨ticket, input⟩, selected, publishMany_extends _ later _ _ selected, by simp only [Option.getD_none]⟩

/-- A winner already installed at the atomic update displaces the unevaluated candidate. -/
theorem reread_existing (table : Published) (input : Value) (ticket : Nat) (later : List Producer)
    (winner : Producer) (found : table input.referenceOf = some winner) :
    (publishMany (keepFirst table input.referenceOf (⟨ticket, input⟩ : Producer)) later input.referenceOf).getD
      ⟨ticket, input⟩ = winner := by
  have present := publishMany_extends _ later _ _ (keepFirst_existing found (⟨ticket, input⟩ : Producer))
  simp only [present, Option.getD_some]

/-- Actual publication order is lookup, optional atomic insert, and winner reread.
No constructor in this graph evaluates a producer body. -/
inductive Publication : Published → Value → Nat → Published → Producer → Prop where
  | hit (found : table input.referenceOf = some producer) : Publication table input ticket table producer
  | miss (absent : table input.referenceOf = none) (earlier later : List Producer) :
      Publication table input ticket
        (publishMany (keepFirst (publishMany table earlier) input.referenceOf ⟨ticket, input⟩) later)
        ((publishMany (keepFirst (publishMany table earlier) input.referenceOf ⟨ticket, input⟩) later input.referenceOf).getD
          ⟨ticket, input⟩)

/-- A completed source publication never deletes an earlier producer. -/
theorem Publication.extends {table saved : Published} {input : Value} {ticket : Nat} {winner : Producer}
    (actual : Publication table input ticket saved winner) : Extends table saved := by
  cases actual with
  | hit => exact extends_refl _
  | miss _ earlier later =>
      exact extends_trans (publishMany_extends _ earlier)
        (extends_trans (keepFirst_extends _ _ _) (publishMany_extends _ later))

/-- The winner reread sees a stored producer, so the source fallback is unused. -/
theorem Publication.present {table saved : Published} {input : Value} {ticket : Nat} {winner : Producer}
    (actual : Publication table input ticket saved winner) : saved input.referenceOf = some winner := by
  cases actual with
  | hit found => exact found
  | miss _ earlier later =>
      obtain ⟨producer, _, found, _⟩ := reread_winner (publishMany table earlier) input ticket later
      simp only [found, Option.getD_some]

/-- Completed publication derives key provenance through every intervening insert. -/
theorem Publication.correct {table saved : Published} {input : Value} {ticket : Nat} {winner : Producer}
    (actual : Publication table input ticket saved winner) (correct : ProducersCorrect table) :
    ProducersCorrect saved := by
  cases actual with
  | hit => exact correct
  | miss _ earlier later =>
      exact publishMany_correct _ (keepFirst_producers _ (publishMany_correct table correct earlier) ⟨ticket, input⟩) later

/-- The source winner retains an original argument with the actual requested tagged key. -/
theorem Publication.winner_key {table saved : Published} {input : Value} {ticket : Nat} {winner : Producer}
    (actual : Publication table input ticket saved winner) (correct : ProducersCorrect table) :
    winner.original.referenceOf = input.referenceOf := actual.correct correct _ _ actual.present

/-- Literal initial hits return the existing producer and skip all publication work. -/
theorem Publication.hit_unchanged {table saved : Published} {input : Value} {ticket : Nat} {winner producer : Producer}
    (actual : Publication table input ticket saved winner) (found : table input.referenceOf = some producer) :
    saved = table ∧ winner = producer := by
  cases actual with
  | hit same => exact ⟨rfl, Option.some.inj (same.symm.trans found)⟩
  | miss absent => rw [absent] at found; cases found

end MicroCFTA.SourceCurrentMergeResultMemo
