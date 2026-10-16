# Checked prefix split review

Result: PASS. No material defect was found in `SourceEqualityNativeDemandPrefixSplit.lean`, 82 lines, SHA-256 `7f0b5c9038018041f4cc760d7213883df779cc7a90f130bde7c16cc089cf113e`.

`steps_bind_cases` retains the actual checked `Control` and the entire checked state. Its first result covers a prefix that still ends in a nonpure inner control. Its second result supplies the actual inner return and the actual outer continuation trace at the same intermediate state. Both native memo families and all equality-operation caches remain part of that state.

The zero-step case distinguishes a pure inner control from every nonpure code and from `edgeBody`. The positive case uses the actual `step_bind` equation. A yielded inner step retains its exact body and state. The induction then extends either split by that step. A pure inner control starts the outer code at the same state, with zero inner yielded steps. This handles the return boundary without adding a false extra step. Failed, constraint-error, and blocked observations cannot equal the supplied yielded step. These branches do not fabricate a continuation or a successful answer.

`Steps.length_le_complete` compares two traces with the same original control and checked state. Its complete trace ends at a pure control. Determinism identifies the full intermediate controls and states at each positive step. A pure control cannot yield another raw step. The bound concerns yielded steps to the pure control, rather than the extra terminal interpreter step that observes `done`.

Both declarations are structural trace helpers. The second declaration explicitly takes a completed trace for comparison. Neither declaration constructs that trace from initial query inputs. These results do not close the simultaneous source-scope, key-word, and domain-admission invariant. They add no `WordRanges`, semantic result law, numeric capacity, or recursive callback premise.

Imported validation uses pinned Lean 4.34.1 with both unused-variable linters enabled. The public probe checks both declarations with explicit types, proofs, universes, deep terms, and ten million print steps. `checked-prefix-split-independent-public-1.log` passes without diagnostics or `sorryAx`.

The first integration kernel executes the actual mismatched `edgeBody` branch for arbitrary incoming checked state. It retains the exact empty-field operation state and the whole native state. It then applies `steps_bind_cases`. A trace through an inner return would require at least two steps, so the one-step supplied prefix must remain inside the sentinel body. This test requires no field load, child availability, or output law.

The second integration kernel executes arbitrary constructor work, reaches its inner pure result, and executes the outer read. The outer constructor work remains pending. It applies `steps_bind_cases` and uses `Steps.length_le_complete` to exclude the pending-inner alternative. The outer continuation therefore starts at the exact inner returned checked state. The kernel also retains the operation state and both native memo tables.

Both integration pairs pass without diagnostics in `checked-prefix-split-independent-kernels-2.log`. The first attempt contains a dotted-constructor elaboration error. Its exact source and log remain unchanged. The canonical build and full Audit pass in `lean-audit-final.log`: 2700 jobs and 61554 checked theorem dependencies. The historical dependency warning for `InternedFreshOrdinaryClosedCompletion.lean` is separate from the clean reviewed module and imported probes.

This review changed only new independent evidence files. It did not change production sources, older evidence, Git state, or Haskell files.
