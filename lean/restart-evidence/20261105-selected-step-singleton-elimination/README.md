# Incomplete singleton-elimination draft

Both drafts keep the full observed-totality statement. The header has eight
caller gates, five fuel witnesses and nine universal binders. It is unchanged.
The drafts add no external premise. They are incomplete and uncompiled.
They are excluded from the normal Lean build. They are not compiler candidates.

Partial285 gives terms for singleton membership and the local Success predicate.
Partial288 adds primitive singleton elimination. Its setter proof stops before
the retained StateT.modifyGet definition. That definition was received earlier.
The current replay needs its exact cut and guard context. The actual setter,
prepare action and returned representative totality proof remain open.

The full two-worker bound and all-state, count, order, inverse, runtime and
Haskell correspondence requirements remain open. No checked theorem is added.
No Haskell source fix is made. All earlier failed attempts and the permanent
SourceProcessFAIL and Root upperUNKNOWN states remain part of the record.
