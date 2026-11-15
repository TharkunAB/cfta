# Common-reader key equality repair

UNCOMPILED. No new proof credit.

The original raw source is unchanged. This repair preserves the complete public header byte-for-byte. The generic Output, real bound producer continuation, actual entry trace, actual common reader, and every original endpoint and assumption are unchanged. The preserved strong header, raw producer header, probes, and original full coupled header are also copied byte-for-byte.

Both diagnostics are rewrite failures. The derived enteredKey fact uses the expanded enter expression with emptyDomain.key. The two rewrite sites use the local entered.1.key, whose original source parameter is emptyKey. These expressions are definitionally equal.

The repair adds one typed change at enteredKey immediately after the actual entry receipt is destructured. It folds the same exact equality to entered.1.key and the literal emptyKey extension. Both existing rw uses then refer to the identical local key expression. No branch proof, heap witness, actual operation, continuation, or endpoint changes.

The complete diagnostics report only these two proof failures. Their axiom print includes recovery sorryAx, so the old raw has no proof credit. The existing PROBES file has no import and can be appended after the raw file.
