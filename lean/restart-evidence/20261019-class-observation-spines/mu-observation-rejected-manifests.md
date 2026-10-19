# Rejected owner manifest drafts

The first 74-pin manifest had SHA `30637f24b99d7b070a248eaa80bf371ad3320c736e4303605bd9aec6a7a20b6e`.
It pinned the mutable owner peaks file after ten jobs.
The final-import strict check then appended the eleventh row.
The parent verifier rejected the stale byte count for `mu-observation-peaks.txt`.
The exact rejected manifest and its four changed input snapshots are retained as `mu-observation-rejected-1-*`.
The recovered manifest SHA matches the original SHA exactly.

An intermediate 90-pin manifest had SHA `896ae8c97389971c2d1640fca9b0bcb98d82adb484c49726e64d1ad5de3eeb96`.
It passed locally before the final full public check started.
It still pinned the mutable peaks path. It is superseded and unselected.
Its manifest, selection, review, verifier and verification remain as `mu-observation-superseded-2-*`.
The original unversioned files also remain unchanged.

The final selected manifest uses the distinct `mu-observation-final-*` names.
It pins a dedicated immutable peaks snapshot.
It excludes the mutable peaks path and shared mutable metadata.
The selected final checks use the unchanged fixture against final production SHA `ebc2c41f025b4803e58c5212087a6799117c7ae8807771c36a89e254f3cf0cb2`.
No source fixture statement or proof changed during these metadata corrections.
