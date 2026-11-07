# Default enumeration reference validity

Run `python3 lean/restart-evidence/20261107-enumeration-default-indices/check.py` from the repository root.
Use a serial capped job. The script uses `shell.nix` and builds the actual module.
It checks all three public theorem axiom sets. It removes its temporary report.
A cold rebuild was not tested separately.

The default callback satisfies `OraclePreservesIndices` by its definition.
The default worker therefore preserves `Indexed` and counter monotonicity on successful return.
The initial-state theorem derives the incoming invariant. It needs no callback law from the caller.
The graph remains an abstract interface. The theorem assumes a successful fuel-bounded return.
It does not prove termination, all error prefixes, exact output terms, or Haskell correspondence.

Source inspection found the same default callback and ordering behavior in `cfta/src/Data/CFTA/Enumeration.hs:859` and `:912`.
This inspection is not a verified translation of the Haskell implementation.
The native continuation representation and cached selection still require a correspondence proof.
No Haskell source changed in this increment.
