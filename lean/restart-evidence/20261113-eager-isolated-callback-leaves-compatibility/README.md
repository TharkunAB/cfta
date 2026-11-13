# Compatibility of the eager isolated-marker leaves

The checker hashes the complete affected source set, builds the Audit frontier,
and checks those hashes again. The frontier covers all five affected modules:
Audit, SharedEagerReservation, CurrentProgramEagerEnumerationWidth,
CurrentProgramEagerResources and CurrentProgramEagerOutputs.

The checked graph has 5895 live modules and 4892 Audit imports. The build passes
with 94865 standard-axiom reports. Counts include private and generated
declarations. They do not prove completion of the full library formalization.

Run `check.py` under the existing serial 4 GiB Nix heavy-management scope, with
swap 0 and one Lean thread. The packet passed from `/tmp`. `frontier.json` pins
every affected source. `checked.json` records the actual build and cgroup limits.
No Audit source, Haskell source or public theorem statement changes here.
