# Current formalization findings

## Haskell fix handoff for external work

### External Haskell repair status

No new Haskell repair is required by this proof checkpoint.

| Repair | Imported status | External action |
| --- | --- | --- |
| Recursive self-type field pools | Fixed by `b9219b9e`, merged in PR #65 at `c0cc8a05`. The API rejects a field pool for the datatype itself. This includes the reported `Chain` case. | No additional patch. Keep the historical reproducer and validation below. |
| Typing binder size-order documentation | Fixed by `74691832`, merged in PR #97 at current imported main `794903b3f`. This changes documentation. | No additional patch. The earlier failed runtime reproduction remains unvalidated. |

Both repairs are in the imported main history. No Haskell source changes
in this checkpoint. All earlier repair entries and evidence remain below.

## Checked state after a completed pair hit

Updated: 2026-10-23 05:41 CEST. Proof checkpoint: `7d9b7e8c93`.
Start: `d8503f9112`. Imported main remains `794903b3f`.
Read `lean/notes-current-completed-hit-readback.md`.

The checked theorem reads the effect of the SAME supplied H7 hit completion.
Initial Stable and a published original or reversed key remain premises.
The exact observed fuel, result and full after state stay fixed.
The conclusion is after.checked = before.checked. The pair memo may change.
The proof does not choose another completion or assume cross-fuel uniqueness.
No new execution, native or pair admission, model rebase, resource packet,
generated-root composition, public pass, Haskell refinement, practical width
or convergence result is derived. H6 constructed_node_calls remains strongest combined.
The whole goal remains ACTIVE and incomplete.
Preservation covers 104210 baseline files/modes, 298 baseline Haskell files
and 207 active package files. FINDINGS keeps its repair index FIRST.
H26 was pushed and remote-verified at d8503f911255e53beb8904dacd7d978349ec7887.
The user authorized further pushes to formalize. H27 seal and push remain future work.
The local publisher stays LOCAL_ONLY and has no network command.
Root push follows successful seal and local checkpoint verification.

## Native coverage through one original-row comparison

Updated: 2026-10-23 04:00 CEST. Proof checkpoint: `776c5b29af`.
Start: `6ca7ff763c`. Imported main remains `794903b3f`.
Read `lean/notes-current-both-miss-native-covered.md`.

The checked theorem augments the SAME H13 BOTH-miss comparison with final native Covered.
