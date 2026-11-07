# Ordinary union and normalized rows

Run `python3 check.py` from this directory or pass its path from the repository root.
The checker uses the project Nix environment. It checks the own source with warnings as errors and checks every public theorem for allowed standard axioms.

The laws recover actual row payloads from resident ordinary values. The union-to-node law requires two operands with different original references. A singleton union can return its operand without normalizing its payload. The proofs permit duplicate catalog entries and overlapping symbols. They do not establish synthesis body execution or intersection closure.

`checked.json` records the verified source hash and every public theorem. The original source and checker reproduce this result; no build archive is required.
