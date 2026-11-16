# Outer depth proof candidate

This snapshot preserves the 13 frozen inputs from the outer-depth draft. The draft
was completed after the main checkpoint snapshot. It is uncompiled and has no proof
credit. Source remains the verified df642fe checkpoint.

`archive-inputs.json` records each original path, byte count and SHA256. The PREFIX
payload uses gzip to retain its final blank line without a whitespace warning.
Decode it as PREFIX.lean.txt before checking MANIFEST.sha256 in a restored folder.
Every other input is stored as its original bytes.
