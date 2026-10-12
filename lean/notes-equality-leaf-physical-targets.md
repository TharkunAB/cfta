# Retained physical equality targets

`EqualityLeafProjectionPhysicalTargets.edits_agree` identifies the complete
stateful run of two edit closures. One closure retains a physical target.
The other closure builds its finite leaf witness before intersection.
A closed representation of each target makes that build allocation-free.
The equality includes the final cache and holds in every valid grown cache.

The proof preserves first-root selection, target order, selected path
suffixes, and the actual ordered edge and child requests. It derives
recursive agreement from the local physical intersection equation.
`physical_transport` combines this agreement with recursive occurrence
transport. Its input cache must already represent the paired targets.

These theorems do not establish a complete multi-pass runtime bound. Later
proof preparation may allocate hidden original rows. That prepared cache
must not replace the next runtime cache. A complete multi-pass proof needs
an occurrence witness that reconstructs in the actual output cache, or an
explicit cache-renaming argument. Trimming dead occurrences is the current
construction direction.
