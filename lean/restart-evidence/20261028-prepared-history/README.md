# Prepared output history and projection evidence

The manifest records every frozen TEMP payload and its stored and raw SHA256.
Large payloads, logs, patches and whitespace-sensitive text use deterministic gzip. No file is omitted from the frozen set.
The source checkpoint precedes the documentation and evidence commit.
Run `python3 files/verify-archive.py SNAPSHOT --live` to verify live sources.
Add `--reconstruct DESTINATION` to reconstruct and compare the exact TEMP set.
Use `--committed` after the evidence commit to compare stored Git bytes.
The old proof and evidence archives remain unchanged.
