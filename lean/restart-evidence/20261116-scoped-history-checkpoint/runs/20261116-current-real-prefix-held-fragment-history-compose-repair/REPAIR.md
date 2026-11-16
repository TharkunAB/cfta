# Prefix history proof repair

Status: UNCOMPILED. The original failed packet and strict log remain unchanged.

The public header and probes are byte-identical to the original packet.
The bucket-shape split now retains named equations. It rewrites only the write
receipt. It does not delete `oldScs` through dependent substitution.

All four history compositions now supply the explicit held IDs and three core
endpoints to `HeldFragmentHistory.trans`. This includes the later action
composition, which the earlier declaration error had hidden from the first log.
Frame and equality composition calls remain unchanged. No premise or budget changed.
