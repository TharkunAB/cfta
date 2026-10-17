# Optional-binder allocation bound

The production module is `SourceCurrentAllocatedRecursiveOptionalBudget.lean`.
Its frozen SHA-256 is `592150198bd4beeff98eb2ba4a562b23be4cd393b59c2e3e5578f10b8bce9bc0`.
It has 110 lines. Strict direct attempt two passed with an empty diagnostic log.

## Input and result

`constructionSyntax key body` is the literal smart binder around the complete
stored-body encoding. It uses the original `leaves body` as lexical captures and
the exact `.intersection key.1 key.2` as the local replacement name. Encoding
retains open nested Mu syntax. It does not use `PreparedWithoutMu`.

`nodeBudget` and `edgeBudget` return zero if the pair is absent from `body.free`.
Otherwise, they use the full `InternedFreshOrdinaryAllocationBudget` recurrences
on `constructionSyntax`. A binder charges three body traversals, three possible
root filters, and one node reservation. Cache hits and earlier pending returns
can use less than this upper bound.

`bound` takes only the actual initial heap facts and body availability. It bounds
the counters at the literal outcome state for both normal and pending outcomes.
The proof uses the existing exact `maybeMu_eq` equation. That equation preserves
all callback arguments, both probe schedules, the ordinary-name choice, actual
reservation, and keep-first readback. No successful callback or result premise
is needed. `unused` gives the exact identical body and heap, with both budgets zero.

## Checked execution

`checked_state` applies to every outcome of the actual checked optional-binder
instruction. It proves an exact state equation: the actual constructor heap is
updated, and the native node table, native edge table, domain cache, and equality
operations remain identical. It needs no valid-cache or completion premise.

`checked_bound` derives the corresponding actual instruction-state counter bounds
from initial heap facts and body availability. `checked_yielded` additionally
extracts the exact successful `maybeMu` return and continuation from an actual
one-step yielded observation. This eliminator does not take an output budget or
a future callback law.

## Scope

These are executable initial-body syntax budgets for one local instruction.
They are not whole-query initial resource bounds. A complete query can generate
a later body; its encoded syntax budget still needs a bound from that query's
original inputs. No result-profile recurrence, total instruction bound, general
resource reservation, or whole-library Haskell correspondence follows here.
The exact source model is the preserved repaired fresh-ordinary executor.

## Validation and constructive integration

Canonical `canonical-optional-budget-1.log` passed all 1056 jobs. It replayed only
the old unused-variable warning in `InternedFreshOrdinaryClosedCompletion`.
The new source has no warnings. Final public and integration probes use all
explicit proof, universe, deep-term, and signature settings with ten million
pretty-printer steps. Eight public pairs and three integration pairs passed.
The only reported axioms are `propext`, `Classical.choice`, and `Quot.sound`.

`constructed_optional` starts with the empty constructor heap and one literal
intersection-name capture. For arbitrary finite source syntax, including nested
Mu, it constructs its own body and complete optional-binder return. All body
facts, availability, semantic context, depth heap, and complete cache coverage
are derived from actual construction. It then derives the local supply bounds.

`constructed_checked` uses that independently constructed source and binder.
It proves the literal yielded checked step while retaining arbitrary supplied
native tables, domain cache, and equality operations. It does not take a
completed optional binder or checked-step premise.

`used_nested_mu` specializes actual source to a raw binder whose ordinary body
contains both the local binder reference and a captured intersection reference.
The returned open Mu cannot satisfy `PreparedWithoutMu`. Its pair is used, and
its complete optional-binder syntax has budgets exactly 25 nodes and 9 edges.
The same own successful return satisfies those upper bounds. These numbers
are conservative syntax costs, not claims of exact observed allocation.

Production attempt one retains its exact source and error log. It used reserved
Lean command names for a definition and section. Attempt two only corrected
those parser names. Before the canonical object was ready, one temporary-import
probe failed to locate its dependency. Three local full-source integration
checks retain their raw sources and logs. Local attempt three passed. Final
imported integration attempt two passed against the canonical object; the local
source checks are historical development evidence, not extra imported pairs.
