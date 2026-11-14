# False boundary simplification repair

Prepared: 2026-11-14 20:46 CET.
Status: UNCOMPILED CANDIDATE.

The only proof change adds `Bool.false_eq_true` to the last `simpa only`.
This reduces the false Bool condition before the inherited-history conclusion.
Both theorem headers and all other source bytes are unchanged.
The original packet and original full joint-assignment target remain unchanged.
No compiler, live module, Git, board, or Haskell change was made.

Original module SHA256:
`ead55dfe2de17474adccf1e15bec22b6b890512286dd4b4825d834476197b6c0`.

Root reported one proof error at line 99 in the original source.
Root also reported incorrect probe names in its original check.
The exact declaration names are
`MicroCFTA.SourcePruningEnumerationEntry.enter_recorded_bucket_origin` and
`MicroCFTA.SourcePruningEnumerationEntry.enter_active_key_origin`.

The complete target and boundary note remain in
`../20261114-current-emitted-clear-provenance-draft/`.
The emitted-branch provenance and ONE finite assignment remain open.
