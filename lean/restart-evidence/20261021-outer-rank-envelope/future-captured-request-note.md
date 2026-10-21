# Captured request equality in the future physical proof

This is a source audit. It adds no proof or adequacy claim.
`SourceCurrentAllocatedPartialState.lean:28-45` keys node requests by inherited identity and node reference. A key is not the complete request.
The future completion proof must relate a selected request to its captured request before it reuses the selected numeric rank.
The private `same_request` proof in `SourceCurrentOlderOwnerLineage.lean:41-60` derives complete request equality from genuine Context, NodeReady for both requests, and key equality.
It uses the existing `ready_eq_of_identity` and `resident_reference_injective` laws. No new equality oracle is needed.
`SourceCurrentActualChildRank.lean:108-153` supplies rank descent for the selected child request. The captured request still needs the equality argument at its actual cut.
The first pure envelope module does not prove this physical connection.
