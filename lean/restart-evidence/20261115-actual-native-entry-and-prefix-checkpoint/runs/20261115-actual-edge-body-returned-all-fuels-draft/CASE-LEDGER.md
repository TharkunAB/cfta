# Returned laws through every actual edge-body endpoint

Status: UNCOMPILED. Root must check the complete module and both public axiom reports.

The module reuses SourceCurrentAllocatedNativeContextCache.Returned directly.
It has no new cache predicate, cache datatype, semantic model or eager evaluator.
It does not edit existing public source or the completed-body theorem headers.

Existing steps_bind_cases splits yielded Steps prefixes. It does not cover all
execute endpoint tags. The new operational bind_endpoint_state_cases covers
that missing composition. The bound execution either has the same complete
checked state as the unbound execution at the same fuel, or an actual inner
Steps trace reaches its pure value and the remaining original fuel executes
the continuation. The latter trace is strictly shorter than the supplied fuel.
The proof uses step_bind, appendStep and step_done_iff. It preserves operation
caches and both native memo tables through exact state equality.

The accepted branch inducts over the actual ordered child list. The remaining
control retains its final constructor continuation. A partial or stopped child
uses the first endpoint case. A completed child uses its actual Steps trace,
then continues the tail at the exact reached state. Steps.bind and Steps.trans
retain the parent prefix and actual continuation in each child hypothesis.
Both branches preserve the same Returned nodeLaw and Returned edgeLaw.
No child result property is assumed for every arbitrary weakly-valid cache.

Every child hypothesis is scoped to THIS parent .edgeBody execution and its
actual Steps prefix. Its input state has both previously proved Returned laws.
The child fuel is strictly below the original parent fuel. Prefix plus child
fuel is at most that same original supplied fuel. For a completed child trace,
the standalone pure-return observation uses trace length plus one, still within
those original bounds. This is a local smaller-execution induction hypothesis.

Every field-decision outcome retains the native state by existing body_native.
Yielded code is either the sentinel or accepted child code. Sentinel and final
edge construction execute only work followed by pure, so all their supplied
fuel endpoints retain both native memo tables. Done, failed, constraintError
and blocked body-prefix cases retain the prior laws directly. Yielded endpoints
are covered even when a child is incomplete. No returned row is fabricated.

The theorem is conditional intermediate infrastructure. It does not derive the
child induction hypothesis from accepted-source initialization or prove whole
native cache history, all producer families, pending-slot provenance or one
joint finite accepted completion. It has no PhysicalCache.Valid premise and
does not replace it with stronger thunk provenance. Request domains remain
arbitrary. Original source fuels and budgets are unchanged.
No Haskell source changed, and no runtime defect is claimed.
