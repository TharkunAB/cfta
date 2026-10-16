# Current allocation prefix validation

Timestamp: 2026-10-16 15:48 CEST.

The source is `lean/MicroCFTA/SourceCurrentAllocatedPartialPlainPrefixes.lean`.
Its SHA-256 is `b7bb6a49479eddc574be5caccc6fb8cb5d130b98a0e3b96676b582e930410189`.
The source has 62 lines. The frozen copy has the same bytes.

The two public endpoints derive actual indexed-descent and resident inherited-prefix receipts from the initial caller context. They retain the literal caller return, the structural returned-edge domain, and `ActiveExcept` for arbitrary excluded node and edge handles. The inherited-prefix endpoint constructs its own successful prefix through the resident field. It does not require a supplied prefix result, child call, or future range plan. Its uniform signature still requires edge residency when inherited contradiction would skip the accessor.

The root canonical build passed with 1408 jobs. `prefixes-build-1.log` contains the raw output. The only warning comes from the older `InternedFreshOrdinaryClosedCompletion` dependency. The final direct source check is `prefixes-direct-3.log`; it passed without output. The first direct check records a structure-index elaboration error. The second records an incorrect toolchain executable path. Both remain available.

The final external check is `prefixes-checks-2.log`. It passed with exit code 0 and no errors, warnings, or `sorryAx`. It contains two public axiom reports and two full signatures. It also contains three independently checked integration theorems, each with its own axiom report and full signature:

- A resident inherited prefix followed by actual indexed descent returns the composed full `Post`, `Stored`, and the original `ActiveExcept` bound.
- Satisfaction of the actual inherited and own parent constraints implies satisfaction of the literal allocated child payload at the selected index.
- The composed prefixes retain the exact native state, node result table, edge result table, merge table, and fourth memo. Only the equality-operation state can change.

The first external check passed but reported one unused-instance warning in a pure integration theorem. The final check omits that unused section instance. The source module did not change.

These are nonrecursive prefix results. They do not assert completion of a recursive child, general caller termination, host demand order, or concrete runtime memo behavior. The full initial `Context`, residency, ready inherited allocation, and structural returned domain remain explicit premises.
