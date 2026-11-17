# The same eager ledger under a strict guarded policy

Status: COMPLETE BOUNDED PROOF DRAFT, UNCOMPILED. Root alone checks.

The public header was frozen before proof. The theorem retains the EXACT same
input ledger event list, path, current position, callbacks, original five fuels,
caller/cache/query endpoints, supplied output/index, terminal exit and consumer
index. It does not call the independent ledger producer.

The proof uses induction on ORIGINAL inputs and cases the existing ledger.
Each cons head uses guarded_lower with its actual height qualification and
SAME eager head ledger. The exact remaining list qualifies the tail visitor.
A private runtime equality rewrites only that head's literal remaining callback.
The existing tail ledger is recursively transported with identical tail events.
Nil and stopped constructors retain their original observations. A done prefix
followed by a stopped tail stays supported through the generic TupleExit index.

Two small private runtime equality helpers reuse the checked proof pattern in
GuardedInvocationTransport (members congruence and guarded/eager list equality).
That module's helpers are private and cannot be referenced by ordinary QName.
No owner import/private-name hack, new runtime evaluator, datatype or cache
framework is introduced. The transitive import graph excludes the resource
owner. The module uses normal default limits, autoImplicit false and no option
that changes heartbeat limits or warnings.

No compiler/Source/Audit/Git/board/temporary-path action was performed. This is
pure policy transport, not semantic Holds/TypeIn/native/guard truth or a claim
of one joint source-root completion. It has no theorem credit before strict
module exit0. Public probes contain only the public QName and no self-import.
