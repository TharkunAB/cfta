# Complete payload preservation by recursive path workers

`EqualityLeafProjectionRequireAvailability` derives coherence, stored child
availability, and node-to-edge links through every required-path worker
branch. `require_available`, `requireEdges_available`, and
`requireChildren_available` follow actual optional results and ordered cache
effects. A rejected arity performs no child computation. Successful parent
construction receives the exact available child records from those effects.

`EqualityLeafProjectionEditAvailability` proves the corresponding results for
simultaneous editing. `MeetAvailable` is a local payload-preservation condition
on leaf intersection. Parent editing and child sequencing have no supplied
correctness equation. The empty and unselected branches preserve their exact
records. Unsupported selected constructors return none and retain the cache
facts reached before failure.

These results concern complete physical payloads. Ordinary-input completion
remains a separate proved fact. Together, the two facts provide successful
available output records for the compiled finite occurrence fragment. The
local leaf-intersection availability condition still needs its concrete
physical constructor instance for each admitted or raw leaf carrier.
