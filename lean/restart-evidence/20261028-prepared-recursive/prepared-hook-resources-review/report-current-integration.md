# Current integration review — OPEN

Root's actual `strict-prepared-head-v1` receipt reports exit zero and an empty raw log. The inspected strict snapshot, installed source, and immutable reviewer v1 are byte-identical at SHA256 `8141fd9426a2b09c0dcdda6af2bbc55af5030e494bcbeb233cc3b464fab519de`. The receipt records 4 GiB memory max/high and zero swap. This reviewer ran no compiler. Exact report, raw output, and snapshot are preserved under `evidence/strict-prepared-head-v1`.

The installed PreparedRecursive runtime was read whole. Its callback calls its own resume and uses its own Failure. Both first resource drafts explicitly state old Recursive.continueWith/resume/Complete and old Recursive.Failure. They prove local prepared-head/old-callback resources, not completion for the new worker. Even zero expansion can return a differently typed exhaustion failure. A direct new zero callback proof or justified result transport is required before attaching that result to the new worker. No such transfer is claimed for those first drafts.

The new worker's actual ordinary branch uses SelectedContinuations.run with its own callback, then retains the actual fold outputs or exact stop. The preparation observation stays inside preparation failures. Native alternatives restore the captured cache between siblings and thread actual callback caller/query endpoints. No false original decoded-parent identity is reused.

The primary prepared finite-head proof is source-clear. Operational witnesses precede outcomes. Its head cache bound comes from its own exact observation. Full callback Post/Memos retain the same actual caller at summed bounds. No semantic model, future success, or desired endpoint invariant is an input.
