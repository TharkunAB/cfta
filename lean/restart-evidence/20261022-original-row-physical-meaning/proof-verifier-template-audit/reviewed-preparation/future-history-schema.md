Source history remains a ROOT_ACCEPTED object with selected_source_sha256, variants, artifacts, patches and rejected_public_types.
Each variant has a relative path, actual SHA and positive line count at most 180. Each other artifact has a relative path, SHA and byte count; empty failed metadata output is valid retained data.
Every actual non-public checked input must equal a listed variant. Each listed patch reconstructs the exact before-to-after unified diff with its recorded labels.
Every public TYPE rejection has the actual root job stem, raw SHA, a reason and pinned artifacts. Copies do not create jobs.
No H18 failure, warning, repair, success, TYPE metric or job count is known at this cut. No H17 failed job is a new H18 event.
