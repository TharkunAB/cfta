{- | Nondeterministic enumeration with one state for each branch.

A computation gets the state, a success continuation, and the result of the
branches after it. The success continuation gets a result, the new state, and
the result of the branches after it. The branches run depth first, in the
order of @StateT state []@, but a bind builds no intermediate list.
-}
newtype EnumerateM symbol a = EnumerateM
    { runEnumerateM ::
        forall r.
        EnumerationState symbol ->
        (a -> EnumerationState symbol -> r -> r) ->
        r ->
