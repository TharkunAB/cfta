# Terminal-child incoming interval: syntax repair

Recorded: 2026-11-14 21:58 CET.

This packet preserves the original `2439392f` packet. It makes three token
changes in the final proof. The reserved binder name `prefix` becomes
`prefixObserved` at its declaration and use. The deprecated `if_false`
lemma becomes `ite_false`.

Source SHA256:
`cd5ae46fc118373a0d5381c5861ceeac46ce26a8211114047bfd53bc1f8a8864`.

The public and private raw headers are byte-identical to the original:

- `cached_terminal_child_success_incoming_interval`:
  `359d27fa1e3c65cd49547398c9b672768f33acbbaa8088404c03fd0370109702`
- `terminal_success_incoming_interval`:
  `833f83c2af293d243b2db39391e2b7b42ba27785feab261582795fb345af2888`

The strict log is
`20261114-planning-filter-raw-target-publication/SourceSynthesisCurrentTerminalChildIncomingInterval.txt`.
It reports these syntax and deprecation errors. The earlier interval proof
and all operation statements remain unchanged.

The original CASE note still defines the scope and source pins. The theorem
derives the actual terminal prefix, recorded fold, and incoming operation
from a successful cached child dispatch with a terminal input bucket. It
preserves the actual descendants, operands, caller, queries, and endpoints.
It adds no future interval, history, provenance, or native-result provider.

Root must run the strict checks. No compiler, live module, Git, board,
Haskell, or original target was changed here. No Haskell fix was found.
