# Import-free appended entry probe

Status: UNCOMPILED REPAIR. No new proof credit.

The only supplied private diagnostic is:

```
SourceCurrentNativeEnterCommonOperand.lean:113:0: error: invalid 'import' command, it must be used in the beginning of the file
```

The private source file contains the complete candidate followed by the
standalone probe. That probe starts with an `import` command. The command
occurs after the module body. The error is in the combined probe layout.
The supplied log contains no proof or type diagnostic. This does not establish
that the full strict check passed.

The candidate source is BYTE-IDENTICAL to the original frozen source. All
proof bytes, the public header, premises, conclusions, and actual-continuation
growth derivation stay exact. No proof change was needed for this diagnostic.
The raw original and private failed attempt remain in their original paths.

`PROBE.lean` now contains only `#print axioms` and `#check`. Append this file
to the candidate source for a private check. It has no `import` command.
`STANDALONE-PROBE.lean` preserves the original probe for a separate file
which imports a built module. Do not append the standalone probe.

`COMPATIBILITY.json` records byte comparisons and hashes. The public header
hash is unchanged. Root owns the strict rerun and publication. No compiler,
live source edit, Git, board, Haskell, or `/tmp` operation was used. The full
same-root joint finite accepted-completion objective is unchanged.
