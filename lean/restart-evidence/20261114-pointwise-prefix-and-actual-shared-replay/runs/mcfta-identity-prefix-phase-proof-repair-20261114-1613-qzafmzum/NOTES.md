# Prefix phase proof-only repair

Status: UNCOMPILED repair. Root owns strict checking and publication.

Base candidate d02cc00f07a6b6dede50e872b91342f36082c03003e6dd24821f33e9cec18264 is preserved.
The repair changes only four lines in the final case-control tactic.
Both public theorem headers, the complete no-output helper, all read/check/frame/mass proofs,
and every original live proof and operational definition remain byte-identical.

Check1 has two reported locations: line524:33 and line525:76.
Their open goals are parked.none, parked.some, narrowed.done and narrowed.failed.
The mass and actual admission subproofs precede these goals and are not the reported failure.
The structured `cases observed with` branches require their subgoals to close inside each branch.
Their branch-local `cases candidate` and `cases prepared` leave goals for an outer all_goals block.
That outer block cannot discharge the structured branch-local obligations.

The repair uses unstructured `cases observed`, closes the stopped case, and uses `case'`
to leave the parked and narrowed subgoals available to the existing all_goals continuation.
SourcePruningEnumerationIdentityWorkerMetadataErasure.lean already uses this case' pattern.
The existing all_goals block then handles the unsupported True branches and supported transports.
No statement or resource premise is weakened.

repair.patch is the minimal d02cc-to-repaired proof patch.
live.patch includes the already-reviewed additions against the unchanged original live module.
The old failed candidate and full diagnostic remain separate evidence with no proof credit.
Check1's helper axiom report alone does not give the failed module credit.

No compiler, Lake, Nix, heavy job, live edit, Git, board or child agent was used.
All-budget stopped partial-output history and the finite common original-root witness remain open.
