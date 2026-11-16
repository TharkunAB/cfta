# Actual opaque receipt inversion

Status: UNCOMPILED. The failed literal-guard packet remains unchanged.

Only `alias_opaque_complete` changes. The proof removes the independently
elaborated intermediate match equation. It cases the actual terminal Boolean
and the operand value, then reduces the literal source guards in `actual`.
Impossible empty and deferred-node cases close from that actual receipt.
Every remaining case contains the actual child/finalizer match from the source.

The proof splits that observed match directly. The source child constructor
provides the same fragment, returned core, caller, queries, read core, waiting
map, cache, and literal dispatch equation. The source finalizer constructor
provides the same finished cache and actual finalization equation. The proof
uses those concrete receipts for alias growth and projects the final-cache
equality. It introduces no second match equation, future event, or supplier.

This direct inversion follows the checked `opaque_counter` control structure
in `SourcePruningEnumerationSharedPreparedRunCounter.lean`, lines 110–123.
The value and terminal cases are reduced before either observed match is split.
The child operand placeholder is fixed by the supplied literal child equation.

All 12 declaration headers remain byte-exact, including original `c4cb44f2`.
Every byte outside this private theorem body and all probes remain unchanged.
No premise, runtime fuel, proof limit, or linter setting changes. No compiler,
Source edit, Audit edit, Git command, board action, or temporary file was used.
