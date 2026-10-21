# Independent mathematical review

Reviewed on 2026-10-21 at 02:55 CEST. The complete 99-line source is
`SourceCurrentNativeStoredMuPositivePositions.lean`, SHA256
`47cfe76a07a55c15e23ec3c66ccbba10b169aa91148e5ad60b03ab229c52a089`.
No material issue was found. This review owns zero Lean/Lake commands and zero
public proof pairs. It reuses the two selected public readbacks.

## Exact result and cell

The public heads are reached (line 70) and source (line 84). For one selected
full Mu cell at the SAME final checked heap, both prove:

`PositiveAt (finish smart storedMu) path` if and only if `smart = true`, the
stored Depth/ordinary pair has `usesLocal = false`, and
`PositiveAt ordinary path`.

The cell lookup fixes the exact entry, body, Depth and ordinary payloads. The
proof passes that same lookup to the causal-history and semantic heap laws.
It does not choose another Mu publication or compare only erased keys. The
law applies to any selected full record at that heap, including a nested
publication or an earlier retained first winner.

`reached` requires initial SemanticHeap and an actual publication History from
empty to the initial heap. `source` requires only an actual physically admitted
yielded Trace and equality of its initial heap with the stopping state of the
actual source build with empty lexical captures and empty constructor tables.
It does not require a separate desired semantic, history, callback, unused-body
or positive-position correspondence premise. It has no separate completed-build
equation or source Scoped premise.

## Three cases

The raw smart=false case returns the same Mu constructor. PositiveAt has no Mu
constructor, so both sides are false. In the smart/used case, the exact selected
record's depth Correct certificate from SemanticHeap yields retained_of_used.
The actual smart finish remains the full Mu, and again cannot have PositiveAt.
This uses the decoded deep-local decision, not a guessed syntactic free test.

In the smart/unused case, history_unused gives the actual first-writer readback
law for that exact selected full record. It equates the smart finish with the
stored ordinary probe after bare-self erasure. The private erase_positions
lemma (line 24) proves that this erasure preserves positive positions. Erasure
removes only a value whose reference is literally the selected bare reference;
an ordinary node or literal union cannot have that reference constructor.
A bare reference cannot have PositiveAt. All other values pass through.

The proof does not equate the raw callback body with the ordinary probe. It
does not need BinderFree or Plain captures. The unused law is the existing
causal first-writer theorem, not a new supplied body/probe equivalence.

## Source and unfinished-trace support

SourceCurrentNativePublicationTrace.from_history extends the actual prior
history through the SAME physical Trace. source_trace derives both initial
semantic support and the initial empty-to-build-state history from the actual
source computation, then uses the same trace transport. The Trace constructors
carry each actual yielded step and its physical admission. They require no
future return of the whole native call and no native-table reset.

The causal history retains callback subhistories. Its unused-law induction
handles nested publications and keepFirst by either using the selected old
full record's earlier law or the actual new publication law. Normal controls
and primitive Work retain the correct history; actual optionalBinder effects
supply their own stopping histories. No history is fabricated from Grows.

## Scope

This is a stored-cell readback law. The Trace may end at an unfinished control;
the theorem does not assert that the selected cell is the output of a completed
native query or that a particular reader has executed finish. A later consumer
must connect its actual returned readback to this same stored cell. The law
retains the same finite natural child path. PositiveAt keeps Mu bodies and
references opaque and ignores row/member index changes; it is not an
observational unfolding relation.

The result does not establish native intersection output support in its
operands, a general body/ordinary positional law, initial binding ancestry,
active-owner renewal, global termination, outer completion or Haskell
refinement. It does not assert existence or uniqueness of an actual final
native return or of a historical publication interval.

## Readback and preservation

The selected strict stem is stored-mu-position-direct-2. Its log is literally
empty and its source matches the final candidate. The selected full stem is
stored-mu-position-public-1; its 36,247-byte log contains complete check, proof
and axiom readbacks for both public heads. All eight printer settings are
present. There are no omissions or private generated names in the public
types. Axioms are limited to propext, Classical.choice and Quot.sound. Both
selected commands have terminal zero, effective 4 GiB max/high, zero swap,
a five-minute cap and fresh usage above one percent. The original receipt
commands remain unchanged. The earlier failed attempt remains in the owner
package. No check was rerun for this review. Snapshot verification is portable;
--live also checks the chosen ROOT sources and installed candidate.
