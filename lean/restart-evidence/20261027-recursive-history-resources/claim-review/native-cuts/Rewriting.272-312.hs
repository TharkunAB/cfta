rewriteStep :: (Term -> Term -> Bool) -> Rules -> Term -> Maybe Term
rewriteStep greater rules = go id
  where
    -- The application of a function to its arguments, for the order check.
    inFunction context ty v = case rulesOrder rules of
        PathOrder _ -> context . (\f' -> Term "app" [ty, f', v])
        KnuthBendix _ -> id
    go context t =
        case [ r'
             | (l, r) <- candidates (oriented rules) t
             , Just s <- [matchTyped l t Map.empty]
             , Just r' <- [instantiate s r]
             , greater (context t) (context r')
             ]
            ++ [ r'
               | (l, r) <- candidates (unoriented rules) t
               , Just s <- [matchTyped l t Map.empty]
               , Just r' <- [instantiate s r]
               , greater (context t) (context r')
               ] of
            r' : _ -> Just r'
            [] -> case t of
                Term "app" [ty, f, v] ->
                    (\f' -> Term "app" [ty, f', v]) <$> go (inFunction context ty v) f
                        <|> (\v' -> Term "app" [ty, f, v']) <$> go id v
                _ -> Nothing

{- | The normal form of a term: rewrite it until no rule rewrites it. Each
step makes the term smaller in a well-founded order, so this ends.
-}
normalForm :: (Term -> Term -> Bool) -> Rules -> Term -> Term
normalForm greater rules t = maybe t (normalForm greater rules) (rewriteStep greater rules t)

{- | Whether a rule rewrites a subterm of the term to a smaller term in the
Knuth-Bendix order. Then the term equals a smaller term, which the search
sees, so the term is redundant. This is ordered rewriting, as in Twee: a
law that the order cannot orient, such as commutativity, rewrites an
instance only when the instance gets smaller.
-}
reducible :: (Symbol -> Bool) -> Rules -> Term -> Bool
reducible isVar rules = isJust . rewriteStep (orderGreater (rulesOrder rules) isVar) rules
