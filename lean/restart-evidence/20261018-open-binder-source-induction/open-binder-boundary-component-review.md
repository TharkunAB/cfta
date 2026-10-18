# Open binder observation boundary

The checked theorem refutes the unrestricted arbitrary-reader `AlignedAt` contract. It uses an active open binder. The theorem does not describe a failure of Haskell execution or finite-tree language equality.

## Exact checked statement

`SourceCurrentOpenBinderObservationBoundary.arbitrary_reader` constructs one Ready execution heap and a separate observation reader. The reader has valid identity caches. It is not Coherent and is not Ready. The source is exactly `binder true (node [mk 2 false [var 0, var 1]])`. It is Scoped at one capture and is not Scoped at zero captures. The two input lists satisfy `Paired (RelatedAt 0 view)` under their sparse replacement maps. Both maps satisfy Replacements at the execution heap. Both source builds and both stored reconstructions return at that same heap. Both reconstructed outputs are retained Mu values with `usesLocal = true`. Their depth-zero observations differ. The source therefore fails `AlignedAt 0 view execution`.

## Actual support and observation

The private `source_effect` helper (line 76) constructs each successful source return from initial Ready and available literal reference inputs. It derives Keeps and output availability. The private `execute_effect` helper (line 123) invokes actual stored reconstruction from initial Ready, available source and sparse replacements. No future successful return is assumed. The first actual unfolding prepares the first node key. Replay then places all four source and stored calls at one final Ready common heap (lines 206–221).

The separate reader changes only one nodeRecords payload (line 184). It maps the first unfolding's node key to a bare reference. The identity caches remain valid. The payload violates Coherent.nodes (lines 253–259). Actual unfolding equations at this reader expose the bare reference on the first side and an ordinary node on the second side (lines 198–204). These equations allow their returned heaps to differ. Finite observations continue to use the original fixed reader. The proof uses the depth-zero reference observations to distinguish the outputs (line 260).

This is a deliberately unsupported observation reader. No actual supported execution reaches the modified reader in this theorem. Cache.Valid alone is therefore insufficient for the unrestricted reader contract. The theorem does not show that Ready alone is a sufficient repair. Availability at the reader and support for unfolding tails and row children may also matter. No repair theorem is asserted here. The two substitutions use distinct related ordinary leaves. The theorem does not refute a publication law that uses the same replacement on both sides or preserves the exact publication alias pattern.

Conditional node, union and publication source clauses remain valid. They retain genuine strict child or body induction premises. This theorem rules out discharging those premises for every active binder at an arbitrary reader without further support.

## Final proof packaging

The final source is `edbfc376472fcb0c79ec2385a5311bed10bd9bcd32b4ce311c168856c03812c0`. The original complete theorem proof is now the private `checked_witness` (line 275). The public theorem (line 313) forwards to that proof. The public statement is byte-identical to the original strict-8 statement. The private proof is unchanged. The alias comparison receipt and component verifier check both equalities.

Selected strict direct-9 returned zero and its log has exactly zero bytes. Canonical-2 returned zero for 594 jobs. Its only warning is the pre-existing `InternedFreshOrdinaryClosedCompletion.lean:24:5` unused-variable warning. The new source has no diagnostic. Public-2 prints the complete public type, alias proof and axioms with all eight required options. The hardened checker passes with only the three standard axioms allowed. Its log has 32,194 bytes. All selected checks record memory.max = memory.high = 4 GiB and memory.swap.max = 0 under the five-minute cap.

Public-1 was interrupted by SIGTERM (-15) after incomplete output. Its receipt does not identify the signal source. No OOM or cap-timeout cause is claimed. The exact-statement private-witness alias makes the final full printer tractable. All nine strict snapshots, both canonical receipts and both public receipts remain present. The selection records each failed or superseded attempt. No test or proof was omitted from the final public statement.

Counts: one new public theorem, zero additional constructed pairs, zero auxiliary pairs. The public theorem itself contains the source-built counterexample. The package does not count it twice. Root owns the full-library Audit and any authority documentation.
