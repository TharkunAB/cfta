# Checked machine arithmetic in weighted sampling

`SamplerMachineBounds` connects the source ticket compiler's arithmetic to
the existing exact two's-complement model. Its width parameter includes one
sign bit. The source's successful total-ticket check supplies every local
bound; no individual cast result is assumed.

`group_machine` proves the exact signed width and array-length conversions.
It also proves the source upper bound after width multiplication and prefix
addition. `midpoint_machine` checks subtraction, addition of one, division
by two, and addition of the lower index in their actual order.

`payload_machine` proves that the selected ticket's local quotient is exact
and is below the payload-array length. `lookup_machine` obtains that interval
from the existing binary search theorem. Thus the group and payload lookups
have safe indexes. Ticket widths must be positive, as required by the source
compiler's documented input contract. The theorem does not silently accept
zero or negative widths.

The word model uses modular arithmetic and signed reads. Division in these
paths is over nonnegative values, so the modeled quotient is the source
signed quotient. Concrete GHC conversions and array storage remain external
representation interfaces. Sampler backend uniformity and the correctness
of caller-supplied indexed callbacks remain separate contracts.

Validation: the pinned `lake build MicroCFTA.SamplerMachineBounds` succeeds.
No Haskell source changed for these arithmetic proofs.
