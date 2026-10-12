# Mutually recursive keyed source callbacks

`KeyedSourceUnfolding.lean` derives the complete ordered class equations for
all keys. It uses the source's finite key list, discovered minimum table,
and per-key body guards. A positive sibling minimum excludes an empty-size
product factor. This fact removes the compiler's same-size environment
cutoff without dropping a member or changing its class rank.

`KeyedCallbackFields.lean` interprets `KeyedTermAlignment.Recipe`. An
occurrence reads the selected key's count, term selector, and callback.
Finite and retained finite leaves use the same local term callback.
Retained masses change sampling but do not change ranks or term positions.
Maps, pays, choices, heterogeneous intermediate applications, and user
labels use the existing proved local field operations. Binary choices use
the flat choice adapter and preserve both source branch wrappers and sorts.

The field compiler proves its complete ordered term classes. It proves
that every selector covers exactly its declared class interval. It also
proves restricted-height inverse contracts and bounds, source order, and
distinct positions for all checked flags. These contracts assume only the
corresponding local finite-leaf contracts.

`KeyedCallbackInverse.lean` attaches the actual value counts and independent
member-term selectors to every key. The grouped source guards and the
ordered class equations derive each count and selector knot. No count or
inverse knot equation is assumed as a postcondition. The key boundary uses
`KeyedTermBoundary.atKeyTerm`: an outer `AtKey` contains a key label and an
inner `Family` with the same key label. The callback checks both labels.
All request views retain the complete member boundary.

The inverse recurses on a finite fuel amount selected from the requested
forest height. The proof is simultaneous over every key. A successful
member dispatch removes two private nodes from the requested path. The
proof gives the child body only the inverse contracts for smaller
requests. Each complete decoded term returns a true checked row. Each true
checked row replays through the independent term selector. All candidates,
including false flags, remain in range, in source order, and distinct by
position.

`KeyedCallbackCausality.lean` removes fuel from the source correspondence.
Any two adequate fuel amounts produce exactly the same row list. This
includes false flags and order. `positions_equation` derives the source's
simultaneous callback fixed point. `positions_member` dispatches a complete
member to its selected key's body. `positions_rejects` excludes wrong keys
and malformed wrappers.

`KeyedCallbackQuery.lean` applies the final replay filter and connects class
positions to the actual bounded grouped decoder. It proves exact per-key
and global rank preimages, source order, and distinct returned ranks.
`KeyedCallbackExamples.lean` checks two mutually recursive keys with retained
leaf masses nine and one. It checks both finite members, all three views, a
second mutual step, a wrong outer key, and an inconsistent inner family key.

The typed family shares one root value type. Intermediate application values
can have different types. The current family syntax has binary choice nodes.
An arbitrary flat source choice requires the separate n-ary extension;
a nested binary choice does not preserve its original flat branch labels.
The key code supplied to this model must agree with source key identity.
Per-key inverse correctness does not require an inverse postcondition for
that code. Cross-key term separation uses the separate key-code injectivity
proof. Runtime key representations, Haskell lazy evaluation, container
behavior, arbitrary callbacks, and extraction remain correspondence
boundaries. Source member ranks retain derivations; they are not an
unconditional distinct-term quotient.
