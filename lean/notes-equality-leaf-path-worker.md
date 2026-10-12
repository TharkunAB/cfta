# Physical ordinary path projection

`EqualityLeafProjectionPathWorker` copies the ordinary `getPath` branches
from `Data.CFTA.Interned.Operations`. A proper path selects the indexed
child of every stored edge. Missing positions issue no child request. The
worker makes one source union from the returned projection list. It keeps
the actual canonical edge order. Forest root projection unions the entire
forest. Forest child projection returns EmptyNode for an absent position.

`read_safe` derives complete-key request safety. `read_returns` proves
completion on every finite ordinary input. `read_available` derives full
cache facts and complete result availability. The optional failure branch
records an unsupported recursive or open union root. The ordinary input
proof excludes that branch; this module does not model recursive unfolding.

The next step proves that a represented occurrence with leaf endpoints
projects to a represented finite raw leaf. The result will use the actual
projection-union correspondence. No global finite-cache closure is assumed.
