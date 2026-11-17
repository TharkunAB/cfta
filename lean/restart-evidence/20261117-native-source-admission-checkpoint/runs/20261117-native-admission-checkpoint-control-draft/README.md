# Native admission checkpoint controls

Status: FROZEN CANDIDATE. The controllers have not run.

This packet adapts the prior whole-worker checkpoint tools for
`20261117-native-source-admission-work` and archive
`20261117-native-source-admission-checkpoint`. It does not create that archive.
It does not change normal Source, Audit, root documents, Git, board posts,
compiler state, or temporary files.

Root must review the scripts before use. Root must supply `checkpoint-note.md`
in the active Work directory. The note must retain `{{TIME}}`, `{{TREE}}`, and
`{{CODE}}`. The prepare controller can also replace `{{THEOREMS}}`, `{{REMOVED}}`,
`{{CLEANUP}}`, and `{{USAGE}}`. The board and cleanup receipts already use the
existing Work schemas. The Source commit comes from `SOURCE-COMMIT.json`.
No controller embeds the new Source commit or a board sequence number.

The proposed order is install, prepare, assemble, finalize, verify with
`--write-manifest --current-tree`, then commit. These are Root actions.
The install controller only copies the reviewed controls into active Work.
It rejects conflicting destination files. It does not run the copied controls.
The prepare controller rejects a dirty tracked tree, changed proof pins,
wrong counts, nonterminal selected checks, or changed Source byte boundaries.
It does not start a compiler or remove files. The generic commit controller
retains the existing local commit behavior. It does not push.

The five publication gates contain 38 fresh strict reports and 405 inherited
reports. The combined component count is 443. The unchanged resource owner has
264 inherited reports. This batch has no fresh owner preflight. The independent
gate has 253 reports. Audit has 5249 imports and 658 reports. Source has 6249
files. The old 6246 non-Audit/non-Reader Source files remain byte exact. The
Reader retains its exact 14650-byte old prefix. Audit retains its old 656-report
block after one new import and before the two new probes.

The native result classifies requests from an accepted original source build,
its stored full U, an empty root domain, both root Profiles, and the same cold
whole trace and query prefix. It retains the original physical and field plans.
It does not prove native inhabitance or arbitrary independent warm histories.
The Reader result exports an existing proof with the same contract.

The exact original441e target also passed a separate private 43-report check.
It is not staged in normal Source and is not part of the fresh38 publication
count. The config retains `optional441e_proved = false` for this normal Source
checkpoint. It records `optional441e_checked_outside_normal_source = true` and
`normal_source_optional441e_staged = false` separately. All first attempts,
failed checks, repairs, and eight exact copies of the original header are kept.

The selection has 33 roots. Older first native failures, unchanged source cuts,
and the Reader export inputs remain in the committed prior immutable archive.
The new selection keeps every subsequent native failure and repair, the fresh
publication, the optional first/layout/owner-helper attempts, and the successful
trace/fields retry. The prepare controller binds the prior committed manifest,
Source pins, toolchain, historical verification, and original inputs map.

The finalizer checks the exact current Source path set and digest. It checks all
three root documents against the Source commit before it changes any of them.
It binds the dynamic canonical board post and sequence again before it writes
documents. The archive verifier retains exact file-set, lossless input, code
patch, Source-tree, and document-prefix checks. `--current-tree` applies only at
the pinned Source and checkpoint document state.

The global goal remains one finite accepted completion of the same original
root under one assignment. Type/Marker class compatibility, native inhabitance,
all causal obligations, and compiled Haskell correspondence remain open.
