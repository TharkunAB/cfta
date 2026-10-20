# Actual source row integration review

Frozen on 2026-10-20 at 15:18 CEST. All fixture work took place under `/tmp/mcfta-build-row-origins-kernels`. No repository file was edited. The package is prepared for a basename-preserving copy into `lean/restart-evidence/20261020-build-structural-row-origins`.

The sole public theorem is `MicroCFTA.BuildRowOriginsKernels.actual_builds`. Its expanded type is identical to the private checked witness. It retains five actual completed call families and five applications of the official `build_row_origin` theorem.

1. An actual initial build allocates row 3. A later node builds rows `[9,3,9]`. The source row at index 1 is row 3. The canonical result has row 3 at index 0 and two rows in total. The duplicate source rows remain explicit. The theorem does not assert uniqueness of the existential source receipt.
2. An actual union builds `[Empty,node3]`. The selected result row obtains a union `SourceRow` receipt. There is no assumed member origin or desired parent result equation.
3. The union result is placed in lexical slot 0. Availability follows from its actual closed build. The complete lexical Context is derived from the actual returned context. The variable returns that exact captured value and obtains a capture receipt.
4. A cold raw binder builds the used Mu `mu x.node7[x]`. A later source with different syntax, `mu x.union[Empty,node7[x]]`, returns the same Mu at the same heap. The witness retains the earlier cold call, syntax disequality, selected stored payload, and actual used-local test. The official theorem supplies the warm binder row receipt. The fixture does not assert uniqueness of the historical source writer.
5. A smart binder with body `node8[]` returns an ordinary node. Its selected row obtains a binder receipt after actual unused cleanup. It does not test the bare-self Empty branch, which cannot have a selected row.

All source contexts come from `empty_context` and actual build preservation. The only changed lexical list contains an actual available returned value. No semantic law, whole-output relation, future return, or desired row origin is a premise of the constructed theorem. The fixture concerns structural `RowAt`, including a row beneath a retained Mu. It does not assert observational Origin, language preservation, source rank decrease, or completion for all source terms.

The selected strict attempt is `build-row-direct-2`: exit 0, literal zero-byte log. The selected full probe is `build-row-public-1`: exit 0, one constructed declaration with `#check @`, full `#print`, and `#print axioms`. It uses all eight required printer/linter options and has no warning or omission. Axiom reports contain only the standard three allowed names. Attempt 1 is retained as an unselected elaboration failure. It required explicit constructor witnesses and a simplified lexical lookup equation; no mathematical endpoint changed.

All three Lean jobs ran through heavy-management with a five-minute timeout. Effective max/high were 4294967296 and swap was zero. Each job records fresh usage before execution. The mutable peaks file is excluded from the manifest; its final three-row snapshot is pinned. Receipt commands retain the original `/tmp` execution paths.

The verifier defaults to `HERE.parents[2]` for repository ROOT after installation. Before installation, run it with `/home/tritlo/Code/mcfta` as its sole argument. All owned manifest paths are relative to the intended repository destination; owned bytes are resolved by basename in HERE. Production source bytes are checked separately against the official module. PASS checks evidence integrity and the selected successful Lean output; it is not a new Lean run.
