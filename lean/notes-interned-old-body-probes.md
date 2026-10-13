# Exact source misses and the remaining smart-cleanup case

`InternedNestedMissReadback.request_miss` applies to arbitrary source
`Syntax`. A fresh Mu reservation stays pending throughout its callback.
Thus a successful callback cannot replace that reservation's missing
payload. The final `keepFirst` readback installs exactly this callback's
body and original probes. No body-completion or key-stability law is assumed
beyond the supplied actual successful request trace.

`request_miss_old` combines this source result with
`InternedCleanupAge.finish_old_cases`. If a newly reserved source call
returns a value whose complete node-identity footprint predates the fresh
reservation, the constructor is smart. It either returns an unused old
body or removes a bare self reference. Raw return and retained smart Mu
return cannot hide the new identity.

`InternedBoundaryAge.atom_occurs` relates the ordinary boundary profile to
that complete footprint. An interned reference or Mu boundary contributes
its actual node identity. `old_absent` therefore excludes both kinds of new
boundary from old probe records. Ordinary normalization may remove node
identities, so boundary equality alone does not establish request identity.

The general source induction must handle both smart branches. In the
unused-body branch, the old returned body does not identify either
normalized probe. `InternedOldBodyProbeAliases` checks a minimal closed
example:

```
mu outer -> mu middle -> mu unused -> union [middle, outer]
```

During an earlier probe call, the innermost callback captures `RecUnint 0`
and `RecDepth`. Its source body ignores its local variable. Each root self
filter removes a different captured sentinel. The stored Mu has identity 2,
its actual body is the earlier union with identity 1, and its normalized
probes are the two separate references. The module proves the exact stored
record, the body's old complete footprint, its cleanup return, and its
inequality with both probes. The whole closed program completes as empty.
This is a counterexample to a proposed proof shortcut. It is not a
pending-readback or termination counterexample.

The focused build has 159 jobs. The isolated axiom audit checks 7,268 theorem
dependencies. A separate Haskell check confirms the distinct actual body and
probe identities. The raw callback satisfies renaming from its actual fresh
local name to either probe sentinel. The literal unrestricted substitution
law also permits substitution of a captured name and therefore fails for
that callback. These domains must remain separate in source correspondence
claims.

The remaining general obligation must relate the two probe observations
jointly to the actual fresh body and derive earlier completed source-call
replay when a pending candidate's probes contain no new identity. Old
output identity alone is insufficient. The current result does not assume
this obligation as a whole-family premise and does not claim general
closed-source completion.
