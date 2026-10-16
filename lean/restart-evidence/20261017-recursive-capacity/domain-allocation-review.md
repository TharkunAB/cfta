# Sequential domain allocation

Status: frozen. Both production modules pass strict direct Lean checks and canonical builds. The final imported probes contain 35 axiom and full-signature pairs. The four integration kernels pass without diagnostics or `sorryAx`.

`CacheFiniteInterning.missing inventory state` counts inventory occurrences that have no table entry. The inventory can contain duplicates. A literal sequential miss increases `next` by one and removes at least one missing occurrence. A hit returns the earlier entry and the entire unchanged state. Actual `Trace` steps preserve `next + missing`. Therefore every finite trace satisfies:

```
after.next <= before.next + missing inventory before
           <= before.next + inventory.length
```

The allocation bound does not require `Cache.Valid`. The trace contains the actual `Cache.intern` states. Every recorded key belongs to the static inventory. The theorem does not accept a future query, completed query, output law, or trace-length bound.

`SourceRecursiveIntersectionDomainAllocation.Trace` records the literal reserved-zero `IntersectionEmptyDomain.make`. Its `make` constructor requires `key = emptyKey` or inventory membership. Empty calls need no inventory entry and retain the whole cache. `Trace.interns` removes only these unchanged empty calls and produces the generic sequential trace.

`represented_identity_le` uses cache validity to prove that every represented shifted domain identity is at most the raw supply. The empty identity is zero. For a nonempty key, the stored raw identity is less than `next`, so its successor is at most `next`. Consequently `Trace.identity_lt trace initialValid represented room` derives the strict bound from `initial.next + inventory.length < limit`. Use `limit = 2 ^ (bits + 1)` for the current signed domain word. `Trace.returned` retains the exact literal constructor return after subsequent domain calls.

The integration kernels check an arbitrarily long single-key sequence, a warm raw identity seventeen that returns shifted identity eighteen, empty calls with an empty inventory, and cold repeated calls against the canonical `DomainInventory.inventory_length` bound. The warm kernel retains the entire cache across both an empty call and a repeated hit. The cold kernel combines actual allocation provenance with the finite domain-universe cardinal and strict word headroom.

Validation:

- `domain-allocation-cache-direct-3.log`: clean exit 0.
- `domain-allocation-domain-direct-2.log`: clean exit 0 against the canonical cache dependency.
- `inventory-allocation-build.log`: canonical exit 0, 380 jobs. This batch builds the generic cache module and the separate inventory module.
- `source-allocation-build.log`: canonical exit 0, 475 jobs. This batch builds domain allocation and the separate source inventory module.
- `domain-allocation-public-2.log`: 35 imported axiom/signature pairs, clean exit 0.
- `domain-allocation-kernels-4.log`: four imported integration pairs, clean exit 0.

Earlier failures and exact source snapshots remain in this directory. Direct cache attempts 1 and 2 contain proof elaboration errors. Domain attempt 1 contains an isolated import-path failure. Kernel attempts 1 and 2 contain proof errors. These logs are historical failures, not final validation logs. Public attempt 1 and kernel attempt 3 pass against isolated copies of the same final production bytes. The final public and kernel logs use the canonical imported modules.

This component covers sequential `intern` calls. It does not bound arbitrary interleaved reservations from `Cache.Steps`. Cache validity alone does not bound supply growth. The source-query proof must still establish inventory membership for each actual domain event and preserve source request scope. This component does not bound output constructor work, generated subsequent queries, or general outer reduction.
