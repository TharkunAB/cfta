definitionWeights :: Rules -> Map Symbol Int
definitionWeights rules = Map.mapWithKey (\c _ -> weightOf c) kept
  where
    rewriting = concatMap (concat . Map.elems . byHead) [oriented rules, unoriented rules]
    found = Map.fromListWith (++) [(c, [body]) | (l, r) <- rewriting, Just (c, body) <- [definition l r]]
    kept = foldl' keep Map.empty (Map.toDescList found)
    keep acc (c, bodies) = case filter (not . any (leadsTo acc c)) bodies of
        [] -> acc
        acyclic -> Map.insert c acyclic acc
    leadsTo acc c s = s == c || any (any (leadsTo acc c)) (Map.findWithDefault [] s acc)
    weightOf c = 1 + maximum [sum [weightOf s | s <- body, Map.member s kept] | body <- kept Map.! c]
    -- The defined symbol and the symbols of the body, with repetitions.
    definition l r = case spine l of
        (Term c [_], args)
            | not (isTemplateVar c)
            , Just vars <- traverse templateVar args
            , length (nubOrd vars) == length vars
            , c `notElem` symbols r
            , length (nubOrd (templateVars r)) == length (templateVars r)
            , leaves l == leaves r ->
                Just (c, symbols r)
        _ -> Nothing
    templateVar (Term v [_]) | isTemplateVar v = Just v
    templateVar _ = Nothing
    symbols (Term "app" [_, f, v]) = symbols f ++ symbols v
    symbols (Term s _) = [s | not (isTemplateVar s)]

{- | The Knuth-Bendix order on ground terms. Each symbol has the weight 1.
Of two terms of the same weight, the term with the smaller weight of
definition is smaller (see 'TermOrder'). An application is the binary
symbol app, which is above the other symbols. Of the other symbols, the generated variables are below the
constants, so that the more general terms come first, and symbols of one
kind compare by their names, then by their types. The generated
variables of a term are constants here. Smaller type instances come first.
The order is total,
well-founded, and closed under contexts, so rewriting with it ends.
-}
kboCompare :: Map Symbol Int -> (Symbol -> Bool) -> Term -> Term -> Ordering
kboCompare defined isVar s t = heavier defined s t <> sameWeight s t
  where
    sameWeight (Term "app" [_, f, v]) (Term "app" [_, g, u]) =
        kboCompare defined isVar f g <> kboCompare defined isVar v u
    sameWeight (Term "app" _) _ = GT
    sameWeight _ (Term "app" _) = LT
    sameWeight (Term a tys) (Term b tys') =
