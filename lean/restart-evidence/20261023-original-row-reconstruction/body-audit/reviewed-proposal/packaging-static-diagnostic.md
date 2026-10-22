# Static packaging diagnostic

The first inline packaging pass stopped with `ValueError: substring not found` at its inverse check.
It searched for the private header including its final newline. The source adds ` := by` before that newline.
The corrected check searches for the exact header without that final newline.
The source and all approved contracts were unchanged. This was not a compiler or prepared-tool job.
