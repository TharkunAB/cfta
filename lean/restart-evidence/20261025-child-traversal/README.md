# Ordered child traversal evidence

Each strict directory retains the complete checked source and raw output.
Every run has a command/hash report. Rejected inputs remain distinct from
final passing inputs. Final strict sources match the committed proof files.

`verification.json` checks all twenty recorded proof/build/readback reports.
`source-review.json` records unchanged existing runtime bodies and current
proof hashes. `public-1/raw.log` contains all thirteen public signatures and
axiom readbacks without display omissions. The pretty-printer options apply
only to this separate readback. `heavy-peaks` records the serial capped jobs.
`cap-probe.json` records effective memory and swap limits for the cap mechanism.

The new worker and trace certificates do not derive completion from genuine
initial admission. They do not certify arbitrary cache candidates. See
`lean/notes-current-pruning-enumeration-child-traversal.md` for exact limits,
failed proof attempts and the next completion and integration obligations.
