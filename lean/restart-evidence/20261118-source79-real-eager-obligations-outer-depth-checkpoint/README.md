# Actual eager outer-depth obligation preservation

[2026-11-19 02:32 CET] Source79: actual eager outer-depth obligation preservation

Code: `310143d4946bb556b235700b9d89e359617ed96d`. Branch: `formalize`. The destination is
`git@github.com:TharkunAB/cfta.git`, `refs/heads/formalize`.
The Source79 checkpoint preserves the complete Source78 archive by digest link.

The new public theorem is
`SourcePruningEnumerationSharedEagerReservation.runEager_real_preserves_obligations_at_any_budget`.
It proves that every emitted output of the actual eager worker has the exact
initial obligation list. It closes the lower-depth induction hypothesis from
Source78. It uses the original work fuel and depth. It includes outputs emitted
before a later stop. The theorem retains its explicit packet, resource, guard
pool, reservation, and physical selector assumptions. It does not assume that a
generic initial obligation list is empty.

The change adds one public theorem and ten private lemmas in the existing Shared
module. The ten helpers are those same ten private lemmas. It adds no definitions
or runtime code. The final private check, run 12949, passed the exact eleven
theorem axiom reports with only the standard Lean axioms. Normal publication 7372
passed all five gates: 793, 11, 388, 793, and 793 axiom reports. Each gate has zero
definition checks. All 14715 actual publication inputs were rehashed after the
driver stopped. The three failed private attempts, 30300, 58456, and 93956, retain
zero proof credit. Their exact sources, logs, and input maps are retained.

Metadata run 51754 measured true Shared ownership from 1028 to 1057 theorems.
The 29 additions are eleven authored theorems and eighteen generated declarations:
fourteen equation lemmas, two simplifier auxiliaries, and two proof auxiliaries.
No name was removed. The Audit import closure remains 6093 modules. Full Audit
contains 100469 theorems. The curated report total is 637. Metadata adds no
proof credit. The six historical unclassified Source72 differences remain open.

Cleanup removed 226404064 bytes in two compiler objects and 31650 cache
links from five exact inactive temporary namespaces. The cumulative known cleanup
is 9697946237 bytes. The 6301 source and toolchain inputs, 6331 normal cache
objects, and 68 runtime files kept their exact fingerprints. Unknown temporary
files were preserved. Protected process inspection errors are retained. Complete
process visibility is not claimed.

The strongest emitted-output assignment theorem remains Source74. For the same
accepted first-order source, cold initialization, and actual emitted output, one
finite assignment satisfies the current native and union-find state. That same
assignment completes each successful partial-root readback. This does not prove
that an output or readback exists. Source79 supplies the worker obligation-list
law needed by the next composition theorem.

Next: bind this actual published parent into the Source80 private checker.
Source80 must derive the cold-start empty obligation list and add current
`EnumerationCorrectness.Satisfies` for the same Source74 assignment. Its present
draft and normal controllers are uncompiled and receive zero proof credit.

The largest remaining soundness gap is one compatible finite assignment for the
current state and all causal constraints that were removed or parked. Separate
witnesses for separate constraint groups do not establish compatibility. After
that result, causal transport must prove acceptance of the original emitted root.
Fresh equality classes and inherited proper paths still need a joint finite-model
argument. A new small fresh-instantiation occurs diagnostic is prepared but has
not run. No reachable accepted-source counterexample is established.

The full objective also retains completeness, typing, preprocessing and LPO,
output order and multiplicity, laziness, counts, weights, training and ranking
inverses, host bounds, and correspondence with the compiled Haskell program.
No Haskell source changed at this checkpoint. No new Haskell defect or fix was
established. Future Haskell fixes must also be recorded in root FINDINGS.md.

The shared board note has sequence 1604. The measured primary usage is
45.0 percent at 2026-11-19T01:22:38.093Z. Pause if usage exceeds 80 percent. The goal
control still reports paused; the user's explicit resume authorizes this manual
work. No goal status change or completion claim was made. Keep temporary compiler
output bounded. Preserve all proof drafts and historical failures.


Use --current-tree only at this exact Source and document state.
