# Checked domain trace review

Result: PASS. No material defect was found in frozen `SourceCurrentAllocatedNativeDomainTrace.lean`, SHA-256 `36e2461dbd87ec5e6921ccf8f46b041006e090eb5dbfa6f5e603e6c1bab6ee1a`.

`CodeEntered` at line 24 uses the exact structural key passed by `SourceRecursiveIntersectionEnvironment.enter`: the current domain key, actual left and right Mu bindings in source order, and the sorted operand pair. The native enter case records the literal `IntersectionEmptyDomain.make` result. It does not substitute a key inferred from the returned identity.

The other cases preserve the domain cache. Work and optional-binder execution can change the constructor heap. Neither changes the domain cache. Native node and edge lookup and demand retain the whole source machine. The checked edge-body case uses `body_native`, which retains the complete native state in every outcome. Field errors, absent fields, rejected constraints, arity mismatch, and successful child compilation therefore retain the same domain cache. Finish frames change memo cells only.

The public `step` theorem at line 90 covers the state of every actual outcome. It does not require successful execution or physical key safety. `yielded` specializes this result to the exact yielded state. `trace` at line 152 composes these histories over the supplied raw `Steps` graph. The induction uses current admission and the actual first yielded step to restrict admission to the remaining prefix.

`Prefixes` at line 132 remains an explicit premise. It quantifies enter-key membership at all raw reached controls. The source does not derive this premise from an initial constructor history, request scope, or a finite key carrier. Therefore `next_le` and `identity_lt` are conditional transport results. They do not establish initial-only query capacity or query completion. `identity_lt` also requires initial cache validity and an actual represented domain in the final cache. This is the correct condition for its shifted-identity conclusion.

No future `WordRanges`, successful query, completed recursive child law, constructor-work count, or final cache-validity premise appears in these results. The finite inventory admission obligation is explicit. The module does not claim the full recursive bootstrap.

Validation uses the pinned Lean 4.34.1 toolchain with both unused-variable linters enabled. The imported public file checks all ten public declarations with explicit types, proofs, universes, deep terms, and ten million print steps. `domain-trace-independent-public-1.log` passes without diagnostics or `sorryAx`.

The first integration kernel constructs a literal four-step checked prefix: enter, repeated same-key enter, read, and arbitrary finite constructor work. It derives `Prefixes` for this finite program instead of assuming it. It then applies `trace` and `next_le` to the same actual prefix. The result retains the complete operation state and both native memo tables, and charges at most one domain identity. Arbitrary work may allocate constructor output; the proof requires no output-work bound.

The second kernel applies `identity_lt` to that same prefix and the literal represented shifted return. It derives strict domain-word headroom from the initial domain supply plus one. The final imported two-kernel probe passes without diagnostics in `domain-trace-independent-kernels-2.log`. The first kernel attempt passed Lean but reported an unused-section-variable warning in a private helper. Its source and log remain unchanged as historical evidence.

The canonical module build passes in `domain-trace-build.log`, with 1059 jobs. That log replays the historical unused `inputs` warning from `InternedFreshOrdinaryClosedCompletion.lean`; it contains no warning from the reviewed module. No production source, older evidence, Git state, or Haskell file was changed by this review.
