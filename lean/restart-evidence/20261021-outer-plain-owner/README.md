# Outer plain owner proof checkpoint

Proof commit: 7e42285939b21306ceb7e934267afaaa77ebae52.
Read ../../notes-current-outer-plain-owner.md and next-selected-copy-plan.md.

Run `python3 verify-checkpoint.py` under heavy-management with 4 GiB and
five minutes. It checks selected sources, strict and complete readbacks,
component manifests, actual attempt accounting and baseline preservation.
Run `python3 verify-seal.py` under the same cap to check all sealed bytes.
Both scripts resolve paths from their own directory.

The old fixture review is historical and portable. Current components use
live source checks. All failed and superseded attempts remain. No command
count is a completion measure. The full formalization goal stays active.
