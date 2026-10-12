# Original typed guards for keyed flat choices

`KeyedNaryGuards.lean` reads occurrence metadata from the original typed
`KeyedNaryAlignment.Recipe`. A label uses `OccurrenceGuard.Shape.constructor`.
A plain pay uses `Shape.pay`. This follows `labelRecursive` and
`constructorIndex`: both operations increment size, but only a constructor
clears termless occurrences. Applications also clear termless occurrences.
Raw choice wrappers preserve the children's termless flags.

The flat choice fold preserves the source minimum fold. Each of its three
token sets contains a token exactly when a child contains that token. Empty
and singleton choices follow the same laws. The proof retains every branch,
including a branch with no current finite member.

`lowered_summary` proves equality of minimum, size-unguarded flags, and used
flags with the value compiler's core metadata. It deliberately excludes
termless flags. `shape_minimum` connects the original body to the actual
per-key minimum expression. `size_guard_exact`, `term_guard_exact`, and
`used_exact` connect each original flag to its corresponding executable
predicate. `lowered_used` also proves that label erasure does not change the
finite-shortcut decision.

`public_guard_exact` proves that the actual combined rejection test accepts
exactly when both the size guard and original term guard pass.
`public_family_guards` derives every semantic family guard from that public
check at the discovered minimum table. `context_growth` derives strict size
and term growth in every original probe context. No guard for the entire
family is assumed as a substitute for public acceptance.

The parameterized examples prove that a label accepts an occurrence while
a plain pay fails the term-growth check. They also prove that a singleton
raw choice retains its occurrence flag. These facts explain why the
lowered value program cannot supply the original term-growth check.

The adapter tracks the current family token. Separate occurrence-metadata
proofs cover the preservation of enclosing tokens when a nested family
closes. Haskell representation and extraction remain correspondence
boundaries.
