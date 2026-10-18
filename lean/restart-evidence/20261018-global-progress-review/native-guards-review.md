# Range-free native causal guard-heap returns

Reviewed on 2026-10-18 at 03:35 CEST.

The final production file is `SourceCurrentNativeGuardHeapReturns.lean`.
Its SHA256 is `77f472becb858c0211f59de50e9311e445220aa1b454b40031128d0e7b67c8bf`.
It has 369 lines. Its public heads are `code`, `node`, and `edge`.

## Contract and proof

The retained invariant is `SourceCurrentConstrainedCapGuardHeap.Heap annotation`. It states equality of each literal stored Mu body's guard-depth profile and its complete ordinary probe profile. The predicate is arbitrary. This invariant differs from `SourceEqualityAnnotationHeap.Heap annotation`, which requires every resident raw edge guard to satisfy the predicate. The new theorem does not establish that stronger property or that every returned value is Annotated.

`code` consumes an actual successful bounded execution and initial NativeOperationHeap.Good. It also consumes initial source Safe, Operands, and CodeFields certificates. Those certificates contain physical continuation conditions. They do not contain the desired causal guard-heap postcondition. The node and edge wrappers derive these certificates from their literal request and initial NodeReady or EdgeReady. These wrappers take no future trace, InputsThrough, word-range, semantic native key law, callback preservation law, final heap invariant, closedness, or finite Cap.

Strong induction follows the actual yielded-step count. A request with a continuation splits into the actual bare request and the actual remaining continuation. Public NativeOperationHeap.node and edge derive the returned intermediate Good, physical availability and operation growth. The new proof does not copy their physical-validity induction. Four short private lookup/demand helpers derive physical Cells for the captured compiled-body start. In a warm native table, the proof uses the actual captured request and its physical ready operands. It does not assume that a key collision identifies that request with the newly requested input.

The bare-request proof expands only actual dispatch branches. Direct and evaluating branches check their actual compiled bodies by the smaller induction hypothesis. Ready branches leave the constructor heap unchanged. Protected finish frames also leave that heap unchanged. Busy or absent dispatch cannot inhabit the supplied successful run.

Primitive intermediate Good is derived by the existing public code theorem on the same one-instruction computation with a pure continuation. Actual ordinary Work uses the existing generic guard-heap Work law. Actual optional binding uses GuardNative.optional_heap at its actual available body and current semantic heap. The checked edge body derives its actual emitted code and operation cache from body_complete and body_certified. No new guard restriction is needed because an edge write does not install a Mu record.

## Constructed initial-source integration

One public constructed endpoint retains both a cold and a warm query. It has only the guard predicate as a parameter. It builds its own source and derives all initial physical and operation facts. Its source contains two distinct productive retained Mu operands. The equality operation cache contains a real constructed equality value and a descent record. Both native result tables start empty.

The first native query succeeds, returns a retained Mu, and populates the native node table. The initial guard heap is derived from GuardExecution.closed_heap for the exact source build. The new node theorem derives the first returned guard heap. The second query starts from that exact returned full checked state and succeeds at the warm bound. It returns the same value without increasing the native node counter. Its guard heap follows from the first produced invariant. The endpoint does not take a future execution, heap, or desired invariant as an input.

The checked private witness is printer-free. A public alias has the exact same explicit statement. The full imported probe prints that public statement, proof, and axiom list without expanding the private evaluator proof.

## Validation and preserved attempts

Selected production direct3 and constructed kernels1 logs are genuinely zero bytes. Canonical2 succeeds with 1781 jobs and replays one unchanged ClosedCompletion unused-input warning. Public1 checks all three public heads. Kernels-public1 checks the one constructed endpoint. Both full probe sources state linter.all and all seven proof-print options, and use #check @. Their axiom sets contain only propext, Classical.choice and Quot.sound.

Direct1 failed on local substitution/elaboration issues and unused section instances. Its exact snapshot and raw log remain. Direct2 succeeded with an empty log. Root review identified one misleading copied comment about word ranges. Only that comment changed before direct3 and canonical2. The earlier canonical1 and all old attempt bytes remain.

The capped inner worker records and verifies actual memory.max and memory.high of 4294967296 bytes and memory.swap.max of zero. Each direct attempt executes its own immutable numbered source snapshot. No old production source, Audit, authority documentation, Haskell source, Git metadata, or prior evidence was edited.

## Residual boundary

The public theorems verify actual successful bounded native returns. They do not construct a successful run, prove absence of busy outcomes, preserve the invariant at every failed stopping state, or provide lower/Parent/outer-prefix composition. Existing generic projection, Required and Merge guard-heap laws can support that next composition. This module does not prove guard occurrence lineage, retained-used Mu child congruence, ordered row correspondence, or outer termination.
