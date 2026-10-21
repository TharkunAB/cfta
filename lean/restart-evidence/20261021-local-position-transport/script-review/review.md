# Independent checkpoint script review

Reviewed on 2026-10-21 at 03:20 CEST. No material issue was found. This
review owns zero Lean/Lake commands and zero public pairs. It does not rerun
source proofs, Audit, sealing, commits, pushes or Haskell. It reviews the
final script definitions and the already recorded evidence. Existing proof
and mathematical review packages remain unchanged.

## Audit and source identity

The first maybeMu proof publication appended its import after the audit
command. The exact earlier script snapshot is preserved by the root. The
separate fix-audit-import.py moves that one import before the audit marker.
The current publish-proof.py inserts new imports before that same marker.
The live Audit source contains each new import once, both before run_cmd.
Removing exactly those two imports restores the original Audit source.

verify-checkpoint.py checks those order and uniqueness conditions. It also
checks selected installed source hashes against the exact literally empty
root strict receipts. The component verifiers independently check their
frozen sources and complete public readbacks. Thus the dynamically written
selected-sources table is tied back to the independently frozen candidates.
The selected default Lake build has no target suffix. Its terminal-zero
receipt and log record 3,563 jobs and 74,623 theorem checks. Only the existing
InternedFreshOrdinaryClosedCompletion warning is permitted by the verifier.
The former dependency placeholder has been replaced in the final script.

## Command counts and preservation

An independent scan of the actual receipt JSON gives fourteen distinct
Lean/Lake commands and seven nonzero commands. Receipt copies in independent
review packages have identical complete JSON and therefore do not add jobs.
Historical previous-publication-support is excluded. Python archive,
publication, verification and seal commands are not counted as Lean/Lake.
The expected count is eleven author commands plus the two root strict
checks and the default Audit. Seven failed elaboration attempts are retained.
No canonical job count is invented for commands completed inside that build.

verify-preservation.py compares every baseline tracked file hash. Only nine
restart documents and Audit can differ. It also checks the exact old Audit
bytes after import removal; old frozen registries and source hashes; actual
stashes and other worktrees; baseline ancestry; branch and unchanged main;
and exact Haskell and active-package inventories. Its frozen-entry archive
exception checks both the preserved historical snapshot and the declared
current bytes. The unchanged baseline registry files prevent silent removal
of entries from that check. This review does not invoke the mutating root
verifier or claim an independent full baseline filesystem rescan.

## Nine document insertions

update-documents.py first requires every destination to equal its baseline
version. It inserts one block after the title, except FINDINGS, where it keeps
the external Haskell repair registry first. It checks exact restoration after
removing that block. The independent byte check reproduced this for all nine
final documents. The compact document certificates retain baseline/current
hashes and exact inserted blocks. --live repeats the byte check against ROOT.
The focused note accurately separates local conditional positive-position
laws from open native/cache transport, chronological edits and global renewal.

## Sealing and final publication

seal-checkpoint.py first requires root verification. It records all current
checkpoint files except its two self-generated manifests, plus selected
sources, Audit, the nine documents and the focused note. Its 90 MiB maximum
prevents an unhandled oversized Git blob. scope-manifest includes byte counts
and full hashes. SHA256SUMS covers physical checkpoint files and that scope
manifest. verify-seal.py checks both sets. Generated checksum output itself
is excluded from its own hash list.

The final publication script verifies the seal before staging. git add -f
includes the declared documentation and the complete evidence directory,
including ignored raw logs. It rejects unrelated staged paths. It then scans
ALL historical SHA256SUMS and requires every named physical file in the
index. It commits only after those checks, requires clean tracked/untracked
status, and compares every HEAD blob and executable mode with the filesystem
and index. It reruns the seal check after commit. The bounded push and remote
readback verify formalize and the exact unchanged main. The publication
receipt remains outside the sealed root so that recording it does not mutate
the checkpoint after sealing. The script review does not execute those actions
or certify a future successful push.

## Frozen scope

The critical script definitions, Audit, toolchain, installed candidates,
selected sources, exact inserted blocks, compact document certificates and
fourteen distinct receipts are snapshotted. The external final-publication
script has a separate exact candidate pin. archive-support.py is deliberately
not pinned because the root will add receipt filenames before sealing. Mutable
logs, component lists, live index/preservation outputs and future seal or push
outputs are not pinned. The report does not claim final publication has already
run. Portable verification checks this review's snapshots. --live additionally
checks the reviewed ROOT files, candidate script if still present and all nine
exact byte-restoration certificates. No new proof or runtime claim is made.
