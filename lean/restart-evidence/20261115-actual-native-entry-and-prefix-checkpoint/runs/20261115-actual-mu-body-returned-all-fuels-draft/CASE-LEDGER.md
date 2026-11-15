# Mu body Returned laws at every supplied fuel

Status: UNCOMPILED. Root must build the required public EdgeBodyReturned dependency,
then check the complete candidate and its two public axiom reports.

The candidate reuses the existing Returned nodeLaw and Returned edgeLaw.
It adds no cache predicate, cache datatype or semantic model.
It does not edit existing public theorem headers or source modules.

The optional-binder theorem covers fuel zero, maybeMu.pending and maybeMu.done.
Pending construction can allocate heap state. It retains both native memo tables.
Completed construction also retains those tables, then returns its pure value.
The theorem has no closedness, availability, physical-validity or future result premise.
It does not claim that a newly constructed Mu value has only-U atoms.

The actual compileNode theorem keeps the literal decision equal to bothMu,
leftMu or rightMu, and the real operand identities. Existing MuSource.enter_prefix
supplies the exact one-step entered domain and started native state. The prefix
retains the actual optional-binder continuation. Entry updates the domain cache,
so both prior Returned families hold at that same started state.

The local child IH refers only to that literal entered child query and started
state. It also receives the same Steps-1 parent prefix and optional continuation.
Its child fuel is strictly below the original parent fuel. Because the prefix
has length one, prefix plus child fuel is at most that same supplied parent fuel.
The hypothesis is not quantified over unrelated weakly-valid warm caches.

At parent fuel zero the initial laws suffice. At positive parent fuel the exact
entry step consumes one instruction. bind_endpoint_state_cases then distinguishes
an endpoint still in the child from an actual reached optional continuation.
Partial, failed, constraint-error and blocked child endpoints use the child IH.
A completed child trace uses trace length plus one within the original remaining
budget. Its exact state supplies both prior laws for the optional operation.
That operation covers every remaining supplied-fuel endpoint, including pending.
No original enumeration fuel or budget is increased.

This is intermediate local preservation infrastructure. The recursive proof must
still derive the child IH from initialized-source history and prove each actual
producer result law before an enclosing finish stores a new returned payload.
Whole native history, all-slot provenance and the final joint finite accepted
completion remain open. No Haskell source changed and no runtime defect is claimed.
