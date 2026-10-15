# Curried synthesis, defaulting, and typed-run accounting

Main `9a2f9bea` is merged at `d8beb7f5`. The upstream delta from
`5c53de80` changes 19 existing files. It preserves the production bodies of
equality reduction, interned graph import, Sized, and normal-form filtering.

## Current source behavior

`Library` has an `Encoding`. `FirstOrder` retains the earlier type encoding.
`Curried` uses application edges for type constructors and gives type
variables domains. `AnyHead` retains every available head. `OnlyDefault`
uses marker leaves to distinguish undetermined variables with and without
a list default. `narrowHeads` reads these leaves before edge enumeration.

`runsNarrowedBy` applies the supplied edge function after the canonical
weighted lookup for each current run node. It does not change `runsBy`.
The hook can intentionally remove runs. Its complete source scheduler and
intersection correspondence need separate proofs.

`programRuns` returns one `Maybe Program` for each typed run. A repeated
decoded program has `Nothing` at its original position. `distinctProgramsIn`
reads the present programs in the first-order encoding. The walk places a
run-count marker before each run's expanded programs. Its next-program
worker counts these markers, including a final suffix with no new program.
The program limit is checked before this demand.

The GHC search enables curried encoding by default. Default-only selection
and domains for variables of kind `Type` remain disabled by default.
Curried erasure retains higher-kinded bound variables. Candidate and query
types determine their domains. `mayHold` gives the conservative instance
test. Default-only checking enables `ExtendedDefaultRules` for complete
programs. The new erasure, class-key, domain, instance, and host-checking
connections remain explicit source boundaries.

## Proof boundary

`SourceCurriedDefaulting` proves physical marker filtering, source guard
priority, sublist order and multiplicity, idempotence, exact default markers,
and filtering after the current weighted lookup. A lone no-default marker
has no effect when the open marker is absent.

`SourceProgramRunAccounting` proves one optional output per completed typed
run, first-occurrence program proposals, distinct emitted programs, one
Walk counting marker per run after expansion, and exact next-program prefix
and suffix accounting. The program cap precedes the next listing demand.
The models start at completed rows, runs, decoders, and expansions.

These proofs do not establish the language of the compiled curried search
space. They also do not
establish GHC instance adequacy, defaulting completeness, lazy demand,
machine-counter bounds, or whole walk behavior.

The previous normal-form quotient and its partial-value exception retain
their scope. The current complete `streamFits` caller still needs its
host-language correspondence. All earlier constructor, equality, Sized,
enumeration, generator, and runtime obligations remain active.

## Validation

The strict Nix build passes for every active package, test, and benchmark
with `-Werror`. All six suites pass: 735 examples and the hole-fit golden
check. Fourmolu passes the 13 changed Haskell files. Cabal-gild passes all
four active package files. Logs and exact commands use
`/tmp/mcfta-required-language-main-9a-*` and
`/tmp/mcfta-required-language-haskell-validation-20261015.json`.
