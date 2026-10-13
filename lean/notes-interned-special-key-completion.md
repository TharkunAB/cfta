# Closed source execution excludes the two smart-empty pending keys

`InternedSpecialKeyCompletion.closed_safe` applies to arbitrary full
`Syntax` from empty caches and an empty lexical environment. It proves
that execution cannot stop at either canonical Mu key:

- `(EmptyNode, EmptyNode)`.
- `(Rec Depth, Rec (Uninterned 0))`.

The syntax has no admission restriction. The theorem does not assume a
callback substitution law, a key-stability law, or whole-run completion.
It excludes these two pending keys. Other pending keys remain open.

`InternedSpecialProbeKeys.source_classified` derives the exact key from
both actual normalized source probes. A symbolic profile with no captured
root reference selects the first key when it does not use its argument.
It selects the second key when it uses its argument. Record reflection
makes this an equivalence with the actual canonical key.

`InternedProfileReferenceInputs.classified_equal_length` proves that these
classes are unchanged by arbitrary literal-reference aliases. The proof
maps every external name to `Depth`. It preserves the distinguished
argument marker and whether the captured-reference list is empty. No
injectivity or freshness premise is needed.

`InternedProfileTraceSites.completed_site_checked` extracts the actual
completed execution of every nested syntax site from an earlier completed
trace. Each witness retains source normalization, input availability,
and the decoded profile table at the original starting state.

`InternedSpecialKeyReadiness.ready_from_trace` applies that witness to
all classified descendant binders. Every binder executes its depth body
before reservation. On a fresh reservation, that completed trace therefore
supplies the complete special-key payloads needed by its later body.
The full syntax induction derives this readiness each time. Its initial
pending-key allowance is empty, so the closed theorem has no readiness
premise. The existing coverage theorem handles older pending allowances.

`InternedProfilePendingEncounter.closed_encounter` separately retains the
exact callback and its verified historical profile context at any actual
pending readback. `InternedPendingProfileBoundary.closed_remaining`
combines it with the two exclusions. A remaining pending callback must
have either two opaque probes, or two pure probes with a nonempty fixed
captured-reference profile. This is a necessary condition. It does not
assert that either remaining case is reachable.

The general closed-source no-pending theorem remains open. In particular,
the pure captured-reference case still needs exact request replay after
normalization erases a changed enclosing dependency. Set equality of root
profiles alone does not establish ordered canonical union identities.
The opaque case also needs the dynamic Mu boundary argument.

The focused combined build completes 245 jobs with Lean 4.34.1. The
isolated audit checks 8,876 theorem dependencies. Both checks pass.
No Haskell source changed for this proof group.
