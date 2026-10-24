# Frozen owner reader schema correction

The first Root read-only pin-check snippet expected the preceding owner's
pinned_files field. The new frozen owner uses pins_count. That snippet stopped
with KeyError before iterating through its pins. The corrected reader checks
the actual schema. No owner or mathematical source changed. No Lean job ran.
The new verifier now uses pins_count, local_instance_count,
global_instance_count, the exact twelve source snapshots and the actual
route_defining_sources mapping. Its complete prior source and exact patch
remain. Independent script review must cover this schema correction.
