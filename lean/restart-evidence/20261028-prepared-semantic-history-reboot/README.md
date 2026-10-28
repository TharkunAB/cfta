# Reboot evidence snapshot

Read root `REBOOT-HANDOFF.md` first. All proof and Audit commits are already
published. This archive preserves the entire stopped TEMP evidence area.
It includes all drafts, failed commands, raw logs and completed owner reviews.
The four independent owner subtrees are sealed. The usual final root seal
and per-payload archive were interrupted by the requested server reboot.
The manifest records this boundary. No later finalization result is implied.

Verify all compressed and raw bytes from the repository root:

```sh
python3 lean/restart-evidence/20261028-prepared-semantic-history-reboot/verify.py lean/restart-evidence/20261028-prepared-semantic-history-reboot
```

To reconstruct, add `--extract /tmp/mcfta-reboot-recovery` with a NEW path.
The verifier refuses an existing destination. Treat the saved snapshot as
immutable. Use a fresh directory for subsequent proof work.
