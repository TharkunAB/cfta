'KnuthBendix' is the Knuth-Bendix order of 'kboCompare' and 'kboGreater':
each symbol and each application has the weight 1. It orients an equation
towards the side with fewer symbols, so a rule never makes a term larger,
and a term that a rule rewrites has a smaller form in the search. The map
gives the weights of definition of the defined symbols
('definitionWeights'). Of two terms of the same weight, the term with the
smaller sum of the weights of definition of its leaves is smaller. Then a
definition whose body has its size, such as @(f >=> g) x = f x >>= g@,
orients towards its body for each instance. The weight decides first, so a
rule still never makes a term larger.

'PathOrder' is the lexicographic path order on the uncurried terms: the
function symbol of the spine of an application with its arguments. The list
gives the precedence of the function symbols from the lowest to the
highest. A symbol that the list does not give is below each listed symbol,
and generated variables are below all function symbols. The order can
make a term larger, for example
@reverse (xs ++ ys) > reverse ys ++ reverse xs@ when @reverse@ is above
@++@. Thus a rule can rewrite a term to a form with more symbols, and the
search can then prune a term whose smaller form is over the size bound.
-}
data TermOrder
    = KnuthBendix !(Map Symbol Int)
    | PathOrder ![T.Text]
    deriving (Eq, Show)
