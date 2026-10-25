[2026-10-25 02:07:01 CEST] FINAL — SOURCE CLEAR for the exact archive retry candidate.

I read all 63 candidate lines and compared them with the complete retained basis. The only executable change replaces the current receipt exclusion `archive-1.` with `archive-2.`. The exact forward and inverse patches and one-substitution recipe reconstruct both files. All five pinned payloads and the complete seven-file proposal match its frozen controls. This permits capture of the finished archive-1 family while excluding the in-flight archive-2 family. The verifier, source, proof, public declarations, resource limits and verification guards do not change.

Archive-1 actually failed because `work/audit-addition.json` was absent. The retained failed snapshot has exactly 394 manifest payloads plus SHA256SUMS. I checked every manifest path, hash and the complete physical file set. Both retained failure-result copies agree. All six failed archive-1 cap artifacts agree byte for byte with their external originals. The receipt records exit 1; limits are max/high 4 GiB and swap 0, with fresh usage age 0 and 68% remaining.

The added Audit record equals the existing installation.audit record, including the exact prepend and before/after hashes. build-summary now records `failed_seal_attempts = ["archive-1"]`; the original six check attempts and the strict-1/strict-2 failures remain unchanged. The unchanged verifier already includes failed seal families in its exact receipt set and requires their actual failed exit status. The revised validation text identifies the missing record and makes no retry success claim.

I rechecked the original 104 owner payloads, four overlay payloads and 55 script-proposal payloads. They remain exact. Production and selected proof source retain SHA256 7f09100d11c24ff225560b3c782d7eb4080f7dad082d9d4b9171cc787cc153b9. The earlier declaration, model, script and pre-seal evidence reviews remain unchanged. The failure result remains in failed-seal-records before a later retry can replace the live seal result.

I performed source/data review only. I did not activate or execute the candidate, verifier, compiler or Git. This clearance applies to the pinned candidate below. It asserts no retry, seal or publication outcome.

Exact identities:
- Proposal FROZEN: 461b088b7fcd4428ca50d30c239da47ec7ba26c63bd5a7bd689ef37232c52521
- Proposal pins: 59bd3a96702dd00e5813016c33969f05f3f0eb26f38d42017aacd32c78715dd8
- Candidate archive.py: 1f45f7af9c6a74c9cac0816c45a7fa786d4b172532db02b35cc44c012f309534
- Original basis: ef547c399bea767e1fd368eaed2995a5c87fdbcfca51e461c4096b9e52b26b16
- Unchanged verifier: 549133f7dff218d7df21dcbb8705a6ee7760a0e18ad71c11c13af498895bd3fc
- Failed snapshot manifest: 813f15797a9519a1c884139d466c9cb6d3329f931cf2552b315452f79dcef7e5
- Retained failure result: 41046fd241a13f415d6befe38c695c74f805376ea3dd6f1828daaaedcfaf8665
- Added Audit record: 5c3bde2d40ba4ab781a79cf94c78c3e5b9f39ec74430d672b5a6bccbc213f134
- Updated build-summary: 70f0de08a260d96f486df090cc8694b12f98b15cdc327ed9ff98aacab7af363a
