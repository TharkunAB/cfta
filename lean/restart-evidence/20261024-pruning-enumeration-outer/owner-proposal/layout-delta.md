# V2 local continuation layout correction

Frozen source-only declaration revision at 2026-10-24T07:54:46.931336+02:00. Root authorized this layout correction before any body. The V1 owner remains unchanged at /tmp/mcfta-pruning-enumeration-outer-20261024-proposal. No body, Lean parser experiment, compiler or prepared program was used.

Only the continuation of local-stable.lean.txt changes from four leading spaces to eight. Root can prefix the first have line by six spaces in its nested fallback while retaining the continuation literally at eight. The complete token sequence, type, name, scopes, public contract and every other mathematical fragment remain unchanged. The exact STRING binding and insertion-map fragment byte/hash binding are updated. The insertion map states first-line-only prefixing and literal continuation retention.

```diff
--- V1/local-stable.lean.txt
+++ V2/local-stable.lean.txt
@@ -1,2 +1,2 @@
 have stable : ∀ extra, SourcePruningOuterNarrow.narrow holeKey fits admits metadata (nativeFuel + extra) uv oldValue heap =
-    .done result nextHeap := by
+        .done result nextHeap := by
```

V1 pins.json: 10800 bytes, SHA-256 1d746ce6c3757f68305404d8fe19d583308ca4491a1213e3a8e209e9c14ed90d. V1 FROZEN.json: 1060 bytes, SHA-256 88d2ef8bee9f50369aa4dff00de0a56a68d6a3996f6ba2613a7c1ebf8fb9c3ac. Their exact bytes are retained at origin-v1/pins.json and origin-v1/FROZEN.json. These controls bind the complete immutable original payload. All seventy-eight old payloads were checked before copying.

Changed existing payloads are exactly contracts.json, insertion-map.json and local-stable.lean.txt. Regenerated top-level controls are pins.json and FROZEN.json. Added provenance files are this note and the two exact origin-v1 controls. All remaining old payload bytes, including every context/public/local type, obtained field, source snapshot, cut, schema and historical static/self-review record, are unchanged. Historical record timestamps remain historical, with this revision note describing the current layout.

All twelve STRINGs still contain65 lines; the public header remains39 and context14. Seven have headers, both conditions, one local instance, all36 obtain fields and hard180 remain unchanged. Whitespace-token equality was checked directly. No new property, premise, helper, instance, state, action or declaration is added. V2 exact independent review and Root acceptance remain pending.
