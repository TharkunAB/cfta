# Full source callback reflection and verified record origins

`InternedProfileRenaming` proves that external-name maps preserve the pure
empty case. They also reflect a selected bare local when its target has
only that source local as a preimage. Other names can merge under the map.
Both observations survive the actual root-profile normalization rule.

`InternedNormalizedProfileReflection.reflects` converts these profile
properties into exact EmptyNode and bare-reference properties of actual
available records. `InternedCallbackReflection.callback_reflects` supplies
the profile premises from the full nested source executor theorem. It
handles arbitrary nested binders and complete canonical cache hits.

The callback theorem requires the actual completed calls, valid initial
source invariants, available inputs, and the decoded profile table at each
start. Captured profile lists must follow the stated name map. It assumes
no relation between the completed callback values. `completed_prefix`
derives the initial state invariants from a completed empty-cache prefix.

`InternedProfileMuOrigins.closed_origins` strengthens the complete stored
Mu origin theorem. Each original three-call witness also retains the
decoded profile table at its historical starting state. The proof threads
the full executor's table preservation through probes, reservations,
fresh bodies, and sibling computations. It applies to complete stored
records even when the containing run reaches a pending key.

These results supply actual empty and direct-local cases for the general
observed replay argument. Exact agreement for every erased dynamic
dependency and first-run closed-Syntax completion remain separate
obligations.
