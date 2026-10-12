# Exact language after lexical constructor exposure

`LexicalExposureLanguage` closes the semantic connection from the finite
lexical inventory to the visited constructor rows. Its main theorem is
`exposed_language`:

```
rowsMeaning environment (exposedRows root) term
  ↔ meaning environment root term
```

The only source-language premise is that the lexical root is closed.
The worker also needs decidable equality of lexical shapes. There is no
assumed row-language equation, finite derivation, finite state set, or
successful fuel result.

`Head` describes a constructor reached through a finite epsilon path.
`head_sound` follows that path backward. Union membership and the proved
closed self-substitution law justify each step.

`meaning_head` proves completeness by induction on the original lexical
syntax. Each free semantic reference must provide a constructor witness in
its closed replacement. At a binder, the proof uses `Head` of its instantiated
binder as the candidate language in the least-fixed-point definition. The
induction hypothesis shows that the body preserves that candidate. Leastness
then supplies a finite constructor witness. A self-cycle without constructors
cannot satisfy this candidate. The argument also handles nested binders and
outer references. `head_complete` discharges the environment premises for a
closed input.

`exposed_language` combines this semantic result with the exact visited-row
membership theorem from `LexicalBinderClosure`. `automaton_exact` then proves
that the ordinary constructor graph made from those rows has precisely the
same finite-term language. Its induction follows the finite term structure;
every emitted child is closed by the inventory theorem.

`bounded_exact` applies the existing `BoundDepth.bound_exact` construction to
that proved graph. Its result contains exactly the original accepted terms
within the supplied constructor height. `eventually_bounded` proves that every
accepted finite term survives at some bound. Epsilon closure consumes no
constructor height. The graph model counts a leaf at height one. Haskell
`boundDepth` counts a leaf at depth zero, so nonnegative source depth `d`
corresponds to model height `d + 1`.

## Concrete memoized builder

`LexicalBoundedBuilder` connects this result to
`EnumerationBuilderRuntime`, including the memo table, separate edge and node
caches, empty-child cleanup, and terminal-entry elision. `requested_exact` and
`elided_requested_exact` conclude the bounded lexical language at each
requested constructed root.

This adapter requires structural `RowsCorrespond` readback from source runtime
identities to lexical instances. That premise preserves symbols, ordered
children, complete guard meaning, and row membership. It permits alternative
reordering, duplicate removal, and shared identities. It is not a language
equivalence premise. The language equation follows from the proved rows and
the new lexical semantics. The existing valid-edge premise also remains for
the runtime enumeration builder.

## Remaining source boundary

The full source correspondence still must show that mutable interning,
alpha-renaming, binder rebuilding, and smart-constructor cleanup implement
that structural readback. The finite lexical inventory alone does not prove
this property of runtime identities. These modules do not add that claim.
They also do not claim extraction of the abstract proposition-valued payload
predicates into executable guard decisions. Guard semantics and runtime
storage retain their separate adapters.

The repaired source `boundDepth` now exposes every interned node form through
`nodeEdges` before it descends into constructor children. The derived bounded
row theorem therefore matches its current control structure. No further
Haskell change was needed for this semantic connection.

Validation on 2026-10-12: pinned Lean 4.34.1 successfully builds
`MicroCFTA.LexicalBoundedBuilder` and its 112 dependencies. The new declarations
use no additional axioms, `sorry`, or `native_decide`.
