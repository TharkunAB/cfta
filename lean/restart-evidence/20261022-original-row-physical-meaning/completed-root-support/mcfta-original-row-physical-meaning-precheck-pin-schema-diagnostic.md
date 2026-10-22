# Source precheck metadata repair

Updated: 2026-10-22 08:17 CEST.

The first root source-precheck job failed before any gate write or Lean command.
The helper assumed a mapping for source-proposal/pins.json. That file contains a list.
The repair iterates the list and reads each item's path field.
The failed helper, raw log, receipt and caps remain in the first driver's external records.
The source proposal and its frozen evidence remain unchanged.
This is one failed root metadata job. It is not a Lean proof failure.
