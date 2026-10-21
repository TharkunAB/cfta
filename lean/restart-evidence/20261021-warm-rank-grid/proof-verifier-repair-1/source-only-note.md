The retained finite-full-readback.failed-1.json is the zero-byte stdout from one failed Python metadata reader. It is not a Lean receipt.
The corrected verifier checks that exact filename has zero bytes and skips only that file before JSON decoding. Every other JSON file is still parsed normally.
The original 130-line unexecuted verifier and the exact repair patch are retained. The inverse restores all original bytes.
The successful Audit log is now pinned by its actual raw hash. Its build and dependency counts remain parsed from that same log.
Root observed Audit terminal zero with 3620 jobs and 75252 dependencies at 2026-10-21 19:08:53 UTC. These counts were not inferred from earlier builds.
The actual ledger stays seven source jobs plus Audit, with three failed Lean checks. The failed metadata reader is separate.
No verifier, compiler, FULL, runtime or official source command was run for this repair.
