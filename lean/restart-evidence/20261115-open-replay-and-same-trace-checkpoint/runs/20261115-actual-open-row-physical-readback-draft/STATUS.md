# Actual open-row physical readback

Status: UNCOMPILED candidate. No proof credit is claimed.

The sole public target is `open_row_physical_readback_of_children`.
It derives exact `result.children` and the complete result key from the same
completed checked edge-body physical `Trace`. It starts with weak `Physical`
validity at the original state. It retains the original Top allocation origin,
actual source row, unchanged domain, supplied execution fuel and same-body
smaller child replay hypothesis.

The earlier row replay theorem supplies the actual allocated prefix, ordered
child walk and constructor arguments at that original fuel. Its cache-law
parameters are instantiated with `True` only to use its observation component.
No cache invariant is claimed from this instantiation. No semantic provider or
future state is supplied.

A private operational split selects that literal yielded prefix from the same
full physical trace. The existing `checked_trace_extension` theorem derives
middle physical validity and machine extension from the original weak state.
The next actual work instruction's current `WorkInputs` gives availability of
all actual constructor arguments in that middle heap. Thus heap Facts and
argument availability are derived. Neither is an input premise at that future
state.

The existing `InternedGuardedExecutionLists.makeEdge_fields` theorem then gives
the exact ordered child payloads and complete literal key. The actual interned
result and full returned native/equality-cache endpoint remain unchanged.
The conclusion also retains the actual physical prefix and derived current
argument availability.

The domain can remain open. No closedness or `Profile` premise appears.
The cutoff is the literal source substitution cutoff, including a distinct
off-diagonal body/Mu pair. Actual smaller child replay remains an intermediate
induction hypothesis. It must be derived from the source control and existing
returned laws. This packet does not establish that hypothesis or physical
trace existence from initialized source execution.

No resident target row is assumed. A consumer can combine the derived key and
current physical facts with existing resident replay once it has an actual
target residency proof. The present theorem keeps the actual returned row.

No compiler, live source edit, Git action, board action or `/tmp` action ran.
No Haskell source changed. No Haskell bug or fix is claimed.
