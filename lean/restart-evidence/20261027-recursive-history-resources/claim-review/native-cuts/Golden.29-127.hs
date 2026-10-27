{- | The name of each golden file and the run that gives its laws, with or
without the test of the types.
-}
cases :: [(String, Bool -> IO [String])]
cases =
    [
        ( "lists-4"
        , \checked ->
            monomorphic
                checked
                4
                (const Nothing)
                [ con "reverse" (reverse :: [A] -> [A])
                , con "++" ((++) :: [A] -> [A] -> [A])
                , con "[]" ([] :: [A])
                , con "map" (map :: (A -> B) -> [A] -> [B])
                , con "length" (length :: [A] -> Int)
                , con "concat" (concat :: [[A]] -> [A])
                , arith (Proxy :: Proxy Int)
                ]
        )
    ,
        ( "list-monad-4"
        , \checked ->
            monomorphic
                checked
                4
                (const Nothing)
                [ con "return" (return :: A -> [A])
                , con ">>=" ((>>=) :: [A] -> (A -> [B]) -> [B])
                , con "++" ((++) :: [A] -> [A] -> [A])
                ]
        )
    ,
        ( "mini-list-4"
        , \checked ->
            monomorphic
                checked
                4
                (const Nothing)
                [ con "reverse" (reverse :: [A] -> [A])
                , con "[]" ([] :: [A])
                , con "null" (null :: [A] -> Bool)
                , con "True" True
                , con "False" False
                ]
        )
    ,
        ( "lists-kbo-5"
        , \checked ->
            monomorphic
                checked
                5
                (const Nothing)
                [ con "reverse" (reverse :: [A] -> [A])
                , con "++" ((++) :: [A] -> [A] -> [A])
                , con "[]" ([] :: [A])
                ]
        )
    ,
        ( "lists-lpo-5"
        , \checked ->
            withOrder
                (PathOrder ["[]", "++", "reverse"])
                checked
                5
                (const Nothing)
                [ con "reverse" (reverse :: [A] -> [A])
                , con "++" ((++) :: [A] -> [A] -> [A])
                , con "[]" ([] :: [A])
                ]
        )
    ,
        ( "gcd-3"
        , \checked ->
            monomorphic
                checked
                3
                posIntReps
                [ con "0" (P 0)
                , con "21" (P 21)
                , con "1029" (P 1029)
                , con "1071" (P 1071)
                , con "gcd" (gcd :: PosInt -> PosInt -> PosInt)
                ]
        )
    ]

{- | Run one case on untyped values and on checked values. Return whether
the laws of both runs equal the golden file.
-}
check :: Bool -> (String, Bool -> IO [String]) -> IO Bool
check accept (name, run) = do
    laws <- run False
    checkedLaws <- run True
    let file = "test/golden/" ++ name ++ ".laws"
    when accept $ writeFile file (unlines laws)
    expected <- lines <$> readFile file
    and <$> mapM (same file expected) [(name, laws), (name ++ " (checked)", checkedLaws)]
