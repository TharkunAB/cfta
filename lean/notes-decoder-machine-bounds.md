# Checked decoder machine arithmetic

`DecoderMachineBounds` models a signed word with one sign bit and `bits`
magnitude bits. Casts store a natural value modulo `2 * 2^bits`. Signed
reads interpret the upper half of that range as negative. Addition,
multiplication, and subtraction use the same word modulus.

`checked_rank` connects the existing `Sampler.checked_machine_rank` theorem
to this explicit signed interpretation. A valid rank below a checked count
keeps both its stored value and its signed value. `localRank_exact` proves
both branches of the small/large local-cardinality guard. The wide product
lemma derives valid local quotient and remainder ranks without requiring
the outer product to fit in a machine word.

`offsetWords` executes cumulative offset construction with machine casts
and addition. `offsetWords_cast` proves the modular correspondence at every
step. `offsets_signed_exact` proves exact signed offsets under the checked
cumulative-total bound. Zero-count branches remain omitted.

`multiply_cast` proves that casting both factors and then multiplying gives
the modular image of the exact product. Thus a checked product block is
exact even if an unused factor does not fit. `zero_product` proves both
zero-factor cases for an arbitrary other factor. The proofs do not impose
range bounds on unused factors.

`productSplitWord` follows the source `productSplitInt` scan. It casts both
factors, multiplies, compares the signed block width, and either splits the
selected rank or subtracts the skipped block. `productSplitWord_exact`
proves equality with the exact arithmetic scan from a checked complete
class total and a valid rank. `productSplitWord_total` proves that this call
returns a selected block and valid component ranks. It cannot reach the
source's exhausted-list error. Both positive factor bounds follow only
when a block is selected.

`fusedRanks_exact` proves the two signed quotient/remainder operations and
all three local rank bounds for a checked binary application. `fused_decode`
combines those coordinates with `Decoder.decode_binary_fusion` to retain
the decoded value. `fused_single_function_decode` checks the optimized
single-function branch, which uses only one quotient/remainder operation.
Every source division covered by these theorems has a positive divisor.

## Remaining interfaces

The model uses natural cardinalities and valid rank inputs. It does not
justify inconsistent metadata or unchecked callbacks. A size-class caller
must supply the complete list of product blocks and its correct total.
The existing count models supply mathematical totals; concrete Haskell
record wiring remains an interface.

The proofs model two's-complement word operations mathematically. They do
not prove the GHC implementation, choose the host word width, or model
allocation and runtime cost. Size-label subtraction is separate from rank
arithmetic. Array layout and callback decoding remain separate adapters.

## Validation

`lake build MicroCFTA.DecoderMachineBounds` checks 25 theorems and eleven
dependency modules. Principal declarations use only `propext` and
`Quot.sound`.
