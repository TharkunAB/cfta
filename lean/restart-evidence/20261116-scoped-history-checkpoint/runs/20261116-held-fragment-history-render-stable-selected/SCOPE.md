Status: UNCOMPILED. This is the selected implementation for one public declaration.

The selected full header is exactly eee855c0 from Canonical's sharper draft. It has no redundant Safe-before premise. RenderStable already gives Safe after and exact stored values and classes. The original Safe-before draft b76f37d7 is not selected. Preserve both reference drafts. Do not append either draft in addition to this selected implementation.

The proof uses the existing IsolatedPending.through_renderStable. Exact values retain the held payload and every old expanded payload. Safe after makes each retained expanded slot a root. Exact classes establish each Protected.classes field. The origin field follows by the same stored-value equality. The result places no constraint on expansion ancestry.

Compared with Canonical's complete draft, the only source change adds EnumerationDependencies to the open list. This resolves the existing enumerated_root theorem in ordinary standalone imports. The full header and proof body are unchanged.

For a standalone check, use SourcePruningEnumerationStableReadHeldHistory.lean and the appendable PROBES.lean.txt. For owner publication, add REQUIRED-OWNER-TOP-IMPORT.lean.txt at the ordinary top of OpaqueSuffixIsolation, then append APPEND.lean.txt once. The import DAG is acyclic. No private-name access or visibility change is required.

This pure factor does not prove actual preparation, a whole-worker history, Holds, an assignment or the one compatible accepted completion. It changes no source runtime or fuel. Root owns compilation and publication.
