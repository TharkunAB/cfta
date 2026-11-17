# History-independent source seed algebra

Status: READ-ONLY DESIGN AUDIT. All new sequence producers remain OPEN.
No theorem or compiler credit is claimed.

The proposed route is sound as a conditional proof step inside a genuine source
query induction. Full call admission and the true producer's Gamma suffice for
any produced node whose domain key is a singleton original base. The pure key
lemma excludes every auxiliary alternative against ANY singleton base. In the
remaining Qualified alternative, the producer's own Gamma gives Profile. Its
full history may differ from a later history. No pattern identity comparison or
later AuthenticEntryAt is needed for that output Profile.

Admission alone gives no result meaning. The true producer Gamma must still be
derived internally from the current query's genuine initial seeds. Inherited
cells need the sequence induction hypothesis and exact forward cell retention.
The third-query node candidate implements this distinction for two prefixes.

Use u for the original universe identity, b for its actual body identity, and:

    D(pid) = extend emptyKey [u] (pair u pid)
    Kb(pid) = extend D(pid) [u] (pair b u)
    Kd(pid) = extend D(pid) [u] (pair u u)
    Kt(pid) = extend Kd(pid) [u] (pair b u)

The actual source supplies b != u. Inspection of the callback proofs gives:

| Callback fact | Sufficient source algebra |
| --- | --- |
| Kb BB compiler | b != u; pair(b,b) is absent from D(pid)+pair(b,u) |
| Kb U/R selects leftMu | pid != u and b != u keep pair(u,u) absent |
| Kb U/R child is pure cutoff | pair(b,u) is already present; actual source body is fixed |
| Kb R/R read | same freshness; u is bound; physical heap grows from source |
| Kd B/U selects rightMu | pid != b and b != u keep pair(b,u) absent |
| Kd B/R read | same freshness and actual stored-U read |
| Kt BB compiler | b != u keeps pair(b,b) absent |
| Kt ordered row inputs | source row classification, closed marker fields and pure R/R cutoff |

Thus pid != u AND pid != b suffice for the combined four-family callbacks.
No literal future pattern is needed after direct construction of D(pid).
The existing pattern-based APIs derive these inequalities from source readback.
They still require an actual pattern in their headers; they are not yet the
pattern-free callback exports. The ordered row proof must remain complete.

The exclusions cannot be dropped. If pid=u, Kb contains pair(u,u), so U/R
selects the repeated branch instead of leftMu. If pid=b, Kd contains pair(b,u),
so B/U selects the repeated branch instead of rightMu. These are algebraic
boundary cases. They are not claimed to be reachable original source entries.
An actual closed node/union pattern is distinct from both stored U and open B.

A useful query-start invariant can use existing predicates without a new
runtime or datatype. It must include: source inventory; the history-independent
ClosedQualified node/edge clauses; singleton-base node/edge Profiles; and, for
every pid apart from u and b, the existing BodyFirst and Coherent+TopRow Returned
pairs at Kb(pid), Kd(pid), Kt(pid). Each family engine preserves its pair pointwise
in pid at the supplied query budget. This avoids a future-H start mismatch.

The exact remaining work is:

1. Extract the five uniform callbacks from source B/U structure and pid apart,
   using literal D(pid). Reuse the existing family engines, not their proofs.
2. Map this H-independent start invariant to C/M initial laws for one fixed
   actual next history. Each future authentic base has the singleton key and
   the required pid inequalities. Use the actual-prefix Returned engine and
   conditional mixed-finish factor with internally preserved auxiliary laws.
3. After that query, derive the singleton node clause from ONE true producer
   origin, admission and its derived Gamma; retain inherited cells forward.
   Derive the singleton edge clause from actual ordered child calls and those
   same completed cells. Full edge admission supplies child classification.
   Do not assume every child is qualified as a new public supplier.
4. Derive that query's NoNewMu from the same actual prefix laws. Then perform
   the real query-sequence induction with original per-query fuels and plans.

ClosedQualified is independent of H, but it is not limited to singleton keys:
it permits the empty domain and any domain that resets closed inputs. It must
remain an explicit invariant clause. A singleton-only invariant is incomplete.
NoNewMu, Physical or admission alone supplies Gamma, native inhabitance, guards
or a model. The arbitrary-sequence target ce659 and full one-assignment finite
completion remain OPEN.
