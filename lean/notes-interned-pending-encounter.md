# Actual pending source-call witnesses

`InternedPendingScopes.ScopedOrigins` connects every active pending key to
its original reservation and its exact recursive reference in the current
lexical environment. Actual reservation adds the new local reference.
Nested probes retain all older references in their lexical tail. Later
source effects preserve the complete origins and cached identities.

`InternedPendingEncounter.build_encounter` handles unrestricted `Syntax`.
If execution reports a pending key, it exposes the actual callback body,
lexical inputs, starting state, and both completed normalized probe calls.
Both returned probes are fully available in the final table. The key is
exactly their canonical pair, with a reserved identity and no payload.
The witness also gives the selected reservation's origin before those
probe calls and its reference in the actual lexical inputs.

`closed_encounter` constructs all origin, scope, and coverage premises from
empty caches and an empty environment. It has no admission grammar or
callback relation premise. The focused build has 158 jobs. The isolated
axiom audit checks 7,117 theorem dependencies.

`InternedPendingOldCall.closed_old_call` combines this witness with the
earlier reservation. The actual lexical inputs contain the reference whose
identity was fresh at that reservation. Both completed probe results are
already complete available values in the pre-reservation cache. The proof
derives full record equality with the original probe pair from canonical
readback. Their old footprints exclude every later reference or Mu boundary.

`InternedBoundaryCleanup.request_miss_cases` handles arbitrary forbidden
boundary predicates. If the newly reserved Mu is forbidden and the returned
value has no forbidden boundary, the call must be smart. It returns an
unused body with the same absence property or removes a bare self reference.
The theorem uses the actual callback execution and exact miss payload.
It needs no age condition on discarded ordinary identities.

This result exposes the remaining general completion obligation. It does
not rule out the witnessed pending call. The origin's earlier complete
probes must still be connected to this source call by observed-absence
replay, including both smart cleanup branches and probe-sentinel aliasing.
