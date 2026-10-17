# Readable language values

The complete version 2 format uses one pure typed parser/printer for graphs,
documents and languages. It no longer depends on JSON. See the
[complete syntax](../cfta-serialization/README.md),
[implementation specification](complete-readable-language.md), and
[prior-art comparison](language-authoring-prior-art.md).

The law is `parseLanguage (printLanguage value) == Right value` for lawful
state codecs. Canonical text is stable. Whitespace and comments are presentation.
Preserve source identities, separate facts, raw logic syntax, all source rows,
transition order, complete symbols and named root/subtree exclusions.
Changes remain typed expressions over values. Persistence is a separate step.

## Readable-v1 baseline (PR #78)

A fresh all-component `-O0 -Werror` build passes. The six rebuilt test executables
are byte-identical to the passing base (798 examples plus the golden suite).
Focused probes cover exact value and canonical-text round trips for all formula,
guard, and template forms; generic state codecs; unusual names; malformed input;
and independent-process ranks. All existing JSON probes still pass with unchanged
graph fixture bytes. The text example also reopens UTF-8 under `LC_ALL=C`.
Formatting, lint, package metadata, and Cabal formatting pass.

All six rebuilt `-O2` core benchmark executables equal the measured main binaries.
The eight standard cells therefore retain their checksums and costs. The shared
JSON graph probe changes from 6,137,964,819 to 6,137,964,915 instructions. Both
allocate 1,719,841,536 bytes and produce the same 1,437,836-byte graph snapshot.

The two language formats were measured on identical source values:

| Language | Format | Encoded bytes | Instructions | Allocated bytes |
| --- | --- | ---: | ---: | ---: |
| 10,000-state chain | JSON | 1,637,903 | 7,221,239,002 | 1,974,571,240 |
| 10,000-state chain | Text | 737,798 | 2,154,434,344 | 655,248,568 |
| Refined pair example | JSON | 1,111 | 7,463,487 | 2,582,456 |
| Refined pair example | Text | 283 | 4,379,319 | 1,495,184 |

The chain includes graph and document construction, encoding, decoding, and exact
value comparison. The small example includes a common JSON fixture load before
that round trip. These are complete-process measurements, not isolated parser
costs. No query or solver runs in these cells. Cachegrind instruction counts and
RTS allocation were collected with a 12 GiB process cap and a 4 GiB RTS cap.
