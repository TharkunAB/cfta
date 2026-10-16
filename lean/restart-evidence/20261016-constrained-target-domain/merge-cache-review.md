# Completed merge-cache scope

Reviewed: 2026-10-16T16:41:31+02:00.

`Stored` is generic in Symbol and Guard. It requires a finite ordinary result
only when the captured original has that domain. The predicate has no heap
parameter. It places no condition on other stored originals.

`remember_stored` retains old entries and checks the new candidate with the
local implication `Domain.Node input → Domain.Node candidate`. It supplies no
body execution. A hit is not treated as a body execution.

`hit_domain` uses physical Stored, SemanticReady and input availability to
recover full original equality from the literal physical key. It then uses
that entry's conditional structural law. Key equality alone is not treated as
record equality. `winner_original` derives the same original readback for an
old winner or a new candidate without a structural or candidate-domain premise.

`winner_domain` checks the local candidate domain, retains old structural
entries, and reads the literal keep-first winner. It returns exact original
equality and domain for that winner's result. The candidate premise is needed
on absence. The earlier-winner kernels omit it on a hit, including when a
proposed candidate is a reference outside the finite ordinary domain.

The helpers do not prove a merge body's domain law, recursive Call preservation,
target slot domains, result height, language equality, early lazy publication,
GHC forcing, concurrency, or host cache correspondence. The actual Run/Call
induction must derive each candidate law from its body. Initial warm structural
Stored is explicit; empty tables derive it without a producer premise. No
Haskell defect or repair follows from this component.
