# Warm admission Checked alias repair

Status: FROZEN UNCOMPILED REPAIR. The failed original has no theorem credit.

The original first check failed because the reopened projection namespace had local Symbol, Guard and Node notation but no Checked notation. The new warm start binder therefore resolved Checked to the kernel predicate instead of the checked state type. Two later diagnostics followed from the missing projection theorem.

This repair inserts one line after the local Node notation in that namespace: `local notation "Checked" => SourceEqualityNativeDemand.State`. Every other source byte is retained. All 37 private theorem headers, the complete public FIRST ee896af3, all four carrier definitions, every proof body and both probe files remain exact. No logical premise, conclusion, runtime, fuel, proof limit or linter setting changes.

Use this candidate in place of the failed warm admission input. The normal module and public QName remain unchanged. The public probe gives one theorem report. The separate same-file internal fixture gives 37 private theorem reports and four declaration checks. Neither fixture imports the candidate into itself.

The original packet, check log and failing assembled source remain immutable. Their hashes are recorded here. No Source, Work, compiler, Git, board, temporary file or old packet was changed. The candidate remains UNCOMPILED until Root completes the strict check. The full finite-completion goal remains open.
