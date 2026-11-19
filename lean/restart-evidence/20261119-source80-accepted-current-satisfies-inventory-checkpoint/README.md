# Current satisfaction from accepted eager output inventory

[2026-11-19 03:05 CET] Source80: current satisfaction for the same eager output assignment

Code: `fba6e8c66971245ae3ca6bce12bacefc898e22f6`. Branch: `formalize`. The authorized destination is
`git@github.com:TharkunAB/cfta.git`, `refs/heads/formalize`.

The new public theorem is
`SourceSynthesisCurrentRealDoneSatisfiesInventory.accepted_real_done_satisfies_from_original_inventory`.
For each actual emitted output of the formalized accepted first-order source
pipeline, one finite assignment satisfies the current native and union-find
state and the current stored guards. That same assignment completes every
successful partial-root readback of that output. The proof retains the original
source, build, root, initialization, fuel, depth, and eager execution witnesses
from Source74. It also retains the existing choices for pending slots.

The proof uses Source79 to preserve the initial obligation list through the
whole actual worker. It derives that the cold-start list is empty. It then adds
`EnumerationCorrectness.Satisfies` to the same Source74 assignment. It derives
the required initial resource, reservation, and guard-pool facts from the accepted
source construction. It adds no future model or historical-discharge premise.

The change adds one public theorem in one new module and its Audit import.
It adds no private theorem, extra helper, definition, or runtime code. The other
6296 existing Lean source files are byte-exact. The Shared module from Source79
is unchanged. Private check 84501 passed the exact public axiom report with only
standard Lean axioms. Normal publication 80572 passed all five gates:
794, 1, 389, 794, and 794 reports. Each gate has zero definition checks and zero
diagnostics, `sorry`, or custom axioms. All 14937 publication inputs were
rehashed after termination. The normal run took about 53 seconds and peaked at
517 MiB under its 8 GiB, zero-swap cap. The curated report total is 638.

True-owner metadata was measured before and after the normal build. Runs 59667
and 80197 show zero to one theorem in the new module. The only addition is the
authored public theorem. There are no generated additions or removals. Full Audit
contains 100470 theorems. Its import closure grows from 6093 to 6094 by this
one module. Metadata adds no proof credit. The six historical unclassified
Source72 differences remain open.

The original publication preparer failed before runtime creation because it
expected a Git-index field absent from the staging receipt. The premature
dependent launcher also failed before a compiler ran. These failures retain zero
proof credit. The reviewed successor checks the empty Git index directly and
preserves the original receipt. A separate hash-bound composition records both
the successful publication and its successful preparer. The code input map also
retains the complete frozen controller inputs. All failed controls and receipts
are retained. The theorem statement and body did not change.

Cleanup removed 709680 bytes in one compiler object and 6331 links
from one exact inactive temporary namespace. The cumulative known cleanup is
9698655917 bytes. The 6302 source and toolchain inputs, 6332 normal cache objects,
and runtime files kept their exact fingerprints. Unknown temporary files remain.
Protected process inspection errors are retained. Complete visibility is not
claimed.

The largest remaining soundness gap is one compatible finite assignment for the
current state and all causal constraints that were removed or parked. Separate
witnesses for separate groups do not establish that result. Causal transport must
then establish acceptance of the same original emitted root. The current theorem
does not establish output existence or successful readback. General completeness
and correspondence with the compiled Haskell program remain open.

Next: run the prepared fresh-instantiation occurs diagnostic. Its negative
candidate is `sink (t t)` and its positive control is `sink (t i)`. At this cut it
is unrun. Then check the small terminal-join proof draft. That draft concerns the
case where inherited and fresh constraints reach a child terminal. It does not
cover repeated-key clearing before the paths reach a terminal. Both drafts have
zero proof credit at this cut.

The full objective also retains typing, preprocessing and LPO, output order and
multiplicity, laziness, counts, weights, training and ranking inverses, and host
bounds. No Haskell source changed at this checkpoint. No new Haskell defect or fix
was established. Record any future Haskell fix in root FINDINGS.md as well.

The shared board note has sequence 1607. Primary usage is 46.0 percent
at 2026-11-19T01:53:17.206Z. Pause if usage exceeds 80 percent. The goal control reports
paused; the user's explicit resume authorizes this manual work. No goal status
change or completion claim was made. Preserve all proof drafts and failures.


Use --current-tree only at this exact Source and document state.
