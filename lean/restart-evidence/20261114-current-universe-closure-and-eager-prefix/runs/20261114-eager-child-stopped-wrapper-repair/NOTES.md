# Empty eager tuple: stopped output transport repair

Status: UNCOMPILED. Root owns strict validation and publication.
The original 811d packet remains immutable.

The strict check rejected the new empty-tuple proof at its stopped hook branch.
The actual hook stops with outputs, reason and endpoint. The captured visitor
retains those outputs and wraps the stopping receipt and reason in alternatives.
IdentityEmittedCompleteResources requires output resources for a stopped result.
It does not require a resource certificate for that stopped endpoint.

The repair explicitly unfolds IdentityEmittedCompleteResources and emitted in
that branch. Both sides then require the same output-list resource statement
and True. No stopped-reason or endpoint equality is needed. No endpoint premise
or stronger induction hypothesis is added.

Two simp-only steps using observedFinish were redundant after the surrounding
cases split. They are removed. The successful finalizer comparison still uses
the actual observedFinish receipt in run_some_moreFuel.

The empty-tuple theorem header, every premise and its entire conclusion remain
byte for byte. The checked b3 owner input remains an unchanged source prefix.
The full worker and prepared marked targets remain byte for byte. The patch has
only these three proof changes. No import, operation or predicate changed.

The original strict failure log is pinned. Its new theorem report contained
sorryAx from failed elaboration and gives no proof credit. This repair has no
compiler result yet. Nonempty eager tuples, the prepared scan, full worker,
generated-Type closure and common finite original-root witness remain OPEN.
No Haskell defect is established. No Haskell, contract or FINDINGS file changed.
The clear-writing checks were applied to these notes.
