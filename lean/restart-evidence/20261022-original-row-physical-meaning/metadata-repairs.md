# Root metadata repair

One root Python source-precheck job failed before any gate write or Lean command.
The helper assumed a mapping for source-proposal/pins.json. The file contains a list.
The repair reads each list item's path. No semantic check or assertion was removed.
The repaired precheck passes. The exact helper delta is metadata-precheck-repair.patch.
The failed and successful helpers, raw logs, receipts, usage and cap records remain
in the external mcfta-original-row-physical-meaning-source-precheck-{1,2} files.
The final one-shot completed-root-support archive must include these files.
This is one root metadata failure, separate from the three successful Lean/Lake jobs.
Reviewer-only diagnostics remain in their own frozen review packages.
