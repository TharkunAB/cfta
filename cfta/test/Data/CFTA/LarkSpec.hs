module Data.CFTA.LarkSpec (spec) where

import Data.Char (chr, isAlphaNum)
import Data.Containers.ListUtils (nubOrd)
import Data.List (isPrefixOf)
import qualified Data.Map.Lazy as Map
import Data.Maybe (fromMaybe)
import Numeric (readHex)
import Test.Hspec (Spec, describe, it, shouldBe)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, equalityConstraint, noConstraint)
import qualified Data.CFTA.Equality as ECTA
import Data.CFTA.Index (Arity (..))
import Data.CFTA.Lark
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

spec :: Spec
spec = describe "Data.CFTA.Lark" $ do
    it "writes the grammar of arithmetic expressions" $
        larkGrammar arithmeticTexts arithmetic
            `shouldBe` Right (unlines ["start: s0", "s0: s1 | \"-\" s0 | \"(\" s0 \" + \" s0 \")\"", "s1: \"1\" | \"2\""])
    it "escapes a text as a JSON string" $
        larkGrammar (const ["\"\\\n\t\1é"]) (automaton "s" [("s", [leaf "q"])])
            `shouldBe` Right (unlines ["start: s0", "s0: \"\\\"\\\\\\n\\t\\u0001é\""])
    it "writes an empty alternative for an empty text" $
        larkGrammar (\symbol -> if symbol == "one" then [""] else arithmeticTexts symbol) arithmetic
            `shouldBe` Right (unlines ["start: s0", "s0: s1 | \"-\" s0 | \"(\" s0 \" + \" s0 \")\"", "s1:  | \"2\""])
    describe "by state" $ do
        it "writes the texts of one symbol in each state" $
            larkGrammarByState tableTexts tables
                `shouldBe` Right (unlines ["start: s1", "s0: \".\" | s3 \"\\n\" s0", "s1: s0", "s2: \"1\" | \"2\"", "s3: \";\" | s2 \" \" s3"])
        it "linearizes a term by its run" $ do
            let words' = term "cons" [term "one" [], term "cons" [term "two" [], term "nil" []]]
            linearizeRun tableTexts tables (term "table" [term "cons" [words', term "cons" [term "nil" [], term "nil" []]]])
                `shouldBe` Just "1 2 ;\n;\n."
            linearizeRun tableTexts tables words' `shouldBe` Nothing
        it "accepts the text of each term of the run" $ do
            let grammar = readGrammar $ either (error . show) id $ larkGrammarByState tableTexts tables
            length (members tables) `shouldBe` 14
            [ found
              | found <- members tables
              , not $ recognizes grammar $ fromMaybe (error "no text") $ linearizeRun tableTexts tables found
              ]
                `shouldBe` []
        it "is the grammar of a linearization when each state has its texts" $
            larkGrammarByState (everyState arithmeticTexts) arithmetic `shouldBe` larkGrammar arithmeticTexts arithmetic
    describe "with an order of the children" $ do
        it "writes the children in the order of the text" $
            larkGrammarByState conditionalTexts conditionals
                `shouldBe` Right (unlines ["start: s1", "s0: \"T\" | \"F\"", "s1: \"x\" | \"y\" | s1 \" if \" s0 \" else \" s1"])
        it "linearizes a term in the order, and accepts the text of each term" $ do
            let grammar = readGrammar $ either (error . show) id $ larkGrammarByState conditionalTexts conditionals
            linearizeRun
                conditionalTexts
                conditionals
                (term "cond" [term "true" [], term "x" [], term "cond" [term "false" [], term "y" [], term "x" []]])
                `shouldBe` Just "x if T else y if F else x"
            [ found
              | found <- members conditionals
              , not $ recognizes grammar $ fromMaybe (error "no text") $ linearizeRun conditionalTexts conditionals found
              ]
                `shouldBe` []
    describe "with brackets around another state" $ do
        it "writes the rule of the inner state between the texts" $
            larkGrammarByState operandTexts operands
                `shouldBe` Right (unlines ["start: s0", "s0: \"x\" | \"not \" s0 | s0 \" + \" s1", "s1: \"x\" | s0 \" + \" s1 | \"(\" s0 \")\""])
        it "accepts a term of the inner state in brackets, which the automaton refuses" $ do
            let grammar = readGrammar $ either (error . show) id $ larkGrammarByState operandTexts operands
                negated = term "add" [term "x" [], term "not" [term "x" []]]
            FTA.accepts operands negated `shouldBe` False
            linearizeRun operandTexts operands negated `shouldBe` Nothing
            map (recognizes grammar) ["x + (not x)", "not x + x", "x + x + x", "x + (x + x)"] `shouldBe` replicate 4 True
            map (recognizes grammar) ["x + not x", "(x)", "x + (not x"] `shouldBe` replicate 3 False
    describe "with lexemes" $ do
        it "splits each literal into runs of spaces, runs of word characters, and other characters" $
            lexemes
                (unlines ["start: s0", "s0: \"    return\" | \"    \" s1", "s1: \"result\" | \"(1 + 2)\\n\" | \"\\u0001\233_x\""])
                `shouldBe` unlines
                    [ "start: s0"
                    , "s0: \"    \" \"return\" | \"    \" s1"
                    , "s1: \"result\" | \"(\" \"1\" \" \" \"+\" \" \" \"2\" \")\" \"\\n\" | \"\\u0001\" \"\233_x\""
                    ]
        it "keeps the texts of the grammar" $ do
            let grammar = readGrammar $ lexemes $ either (error . show) id $ larkGrammar listTexts lists
            [found | found <- members lists, not $ recognizes grammar $ linearizeOrFail listTexts found] `shouldBe` []
    describe "with brackets" $ do
        it "writes an alternative without a symbol for each pair" $
            larkGrammarByState sums arithmetic
                `shouldBe` Right (unlines ["start: s0", "s0: s1 | \"-\" s0 | s0 \" + \" s0 | \"(\" s0 \")\"", "s1: \"1\" | \"2\""])
        it "accepts the text of a term with and without brackets, and gives the text without them" $ do
            let grammar = readGrammar $ either (error . show) id $ larkGrammarByState sums arithmetic
                sum' = term "add" [term "lit" [term "one" []], term "add" [term "lit" [term "two" []], term "lit" [term "one" []]]]
            linearizeRun sums arithmetic sum' `shouldBe` Just "1 + 2 + 1"
            map (recognizes grammar) ["1 + 2 + 1", "1 + (2 + 1)", "(1 + 2) + 1", "-(1 + 2)", "((1))"] `shouldBe` replicate 5 True
            map (recognizes grammar) ["(1 + 2", "()", "(1) + ", "1 +2", "(-)"] `shouldBe` replicate 5 False
            [ found
              | found <- members arithmetic
              , not $ recognizes grammar $ fromMaybe (error "no text") $ linearizeRun sums arithmetic found
              ]
                `shouldBe` []
    it "linearizes a term" $ do
        linearize arithmeticTexts (term "add" [term "lit" [term "one" []], term "neg" [term "lit" [term "two" []]]])
            `shouldBe` Just "(1 + -2)"
        linearize (const ["(", ")"]) (term "add" [term "one" [], term "two" []]) `shouldBe` Nothing
    it "accepts the text of each term that the automaton accepts" $
        [ (name, [text | found <- members fixture, let text = linearizeOrFail texts found, not (recognizes grammar text)])
        | (name, fixture, texts) <- fixtures
        , let grammar = readGrammar $ either (error . show) id $ larkGrammar texts fixture
        ]
            `shouldBe` [(name, []) | (name, _, _) <- fixtures]
    it "has terms to check in each fixture" $
        [(name, length (members fixture)) | (name, fixture, _) <- fixtures]
            `shouldBe` [("arithmetic", 110), ("chains of even length", 4), ("lists of special characters", 156)]
    it "accepts the text of a chain exactly when the automaton accepts the chain" $ do
        let grammar = readGrammar $ either (error . show) id $ larkGrammar chainTexts evenChains
        [recognizes grammar (linearizeOrFail chainTexts found) | found <- allTerms (alphabet evenChains) =<< [1 .. sizeBound]]
            `shouldBe` [FTA.accepts evenChains found | found <- allTerms (alphabet evenChains) =<< [1 .. sizeBound]]
    it "rejects texts that are not linearizations" $ do
        let grammar = readGrammar $ either (error . show) id $ larkGrammar arithmeticTexts arithmetic
        map (recognizes grammar) ["", "1 + 2", "(1+2)", "(1 + 2", "3", "--", "(1 + 2) ", "1\n"] `shouldBe` replicate 8 False
        map (recognizes grammar) ["1", "--2", "((1 + 2) + -1)"] `shouldBe` replicate 3 True
    describe "rejects an automaton that it cannot write" $ do
        it "with a constraint" $ do
            let equal = equalityConstraint $ ECTA.mkEqConstraints [[ECTA.path [0], ECTA.path [1]]]
            larkGrammar arithmeticTexts (automaton "e" [("e", [FTA.Transition "add" ["n", "n"] equal]), ("n", [leaf "one"])])
                `shouldBe` Left ConstrainedAutomaton
        it "with a wrong number of texts" $
            larkGrammar (\symbol -> if symbol == "add" then ["(", ")"] else arithmeticTexts symbol) arithmetic
                `shouldBe` Left (WrongTextCount "e" "add" (Arity 2) 2)
        it "with a wrong number of texts in one state" $
            larkGrammarByState
                tableTexts
                    { stateTexts = \state symbol -> if state == "words" && symbol == "cons" then [""] else stateTexts tableTexts state symbol
                    }
                tables
                `shouldBe` Left (WrongTextCount "words" "cons" (Arity 2) 1)
        it "with brackets of two empty texts" $
            larkGrammarByState (everyState arithmeticTexts){stateBrackets = const [Bracket "" "e" ""]} arithmetic
                `shouldBe` Left (EmptyBrackets "e")
        it "with an order that is not a permutation" $ do
            let ordered order = conditionalTexts{stateOrder = \_ symbol -> if symbol == "cond" then Just order else Nothing}
            map (\order -> larkGrammarByState (ordered order) conditionals) [[0, 0, 2], [1, 0]]
                `shouldBe` [Left (WrongOrder "e" "cond" [0, 0, 2]), Left (WrongOrder "e" "cond" [1, 0])]
        it "with brackets around a state outside the trimmed automaton" $
            larkGrammarByState operandTexts{stateBrackets = \state -> [Bracket "(" "dead" ")" | state == "r"]} operands
                `shouldBe` Left (BracketOutside "r" "dead")
        it "with no term" $
            larkGrammar arithmeticTexts (automaton "e" [("e", [node "neg" ["e"]])]) `shouldBe` Left EmptyLanguage

-- | The largest number of nodes of a checked term.
sizeBound :: Int
sizeBound = 8

-- | The fixtures with their linearizations.
fixtures :: [(String, FTA.PlainFTA String String, Linearization String)]
fixtures =
    [ ("arithmetic", arithmetic, arithmeticTexts)
    , ("chains of even length", evenChains, chainTexts)
    , ("lists of special characters", lists, listTexts)
    ]

{- | Expressions: a number, a negation, or a sum. The number has a symbol of
its own, @lit@, whose texts are empty, so its rule is one rule name.
-}
arithmetic :: FTA.PlainFTA String String
arithmetic = automaton "e" [("e", [node "lit" ["n"], node "neg" ["e"], node "add" ["e", "e"]]), ("n", [leaf "one", leaf "two"])]

-- | The texts of 'arithmetic'.
arithmeticTexts :: Linearization String
arithmeticTexts symbol = case symbol of
    "lit" -> ["", ""]
    "neg" -> ["-", ""]
    "add" -> ["(", " + ", ")"]
    "one" -> ["1"]
    "two" -> ["2"]
    _ -> []

{- | The sums of 'arithmetic' without parentheses, and brackets for the
expressions.
-}
sums :: StateLinearization String String
sums = (everyState texts){stateBrackets = \state -> [Bracket "(" state ")" | state == "e"]}
  where
    texts symbol = case symbol of
        "add" -> ["", " + ", ""]
        _ -> arithmeticTexts symbol

-- | Conditionals: a value, or a conditional with a test, a value, and another value.
conditionals :: FTA.PlainFTA String String
conditionals = automaton "e" [("e", [leaf "x", leaf "y", node "cond" ["b", "e", "e"]]), ("b", [leaf "true", leaf "false"])]

-- | The texts of 'conditionals': the value first, then the test, then the other value.
conditionalTexts :: StateLinearization String String
conditionalTexts = (everyState texts){stateOrder = \_ symbol -> if symbol == "cond" then Just [1, 0, 2] else Nothing}
  where
    texts symbol = case symbol of
        "cond" -> ["", " if ", " else ", ""]
        "x" -> ["x"]
        "y" -> ["y"]
        "true" -> ["T"]
        "false" -> ["F"]
        _ -> []

{- | Sums and negations, with right operands that do not start with a
negation, and a state that accepts no term.
-}
operands :: FTA.PlainFTA String String
operands =
    automaton
        "e"
        [ ("e", [leaf "x", node "not" ["e"], node "add" ["e", "r"]])
        , ("r", [leaf "x", node "add" ["e", "r"]])
        , ("dead", [node "not" ["dead"]])
        ]

-- | The texts of 'operands', with brackets around any expression for a right operand.
operandTexts :: StateLinearization String String
operandTexts = (everyState texts){stateBrackets = \state -> [Bracket "(" "e" ")" | state == "r"]}
  where
    texts symbol = case symbol of
        "not" -> ["not ", ""]
        "add" -> ["", " + ", ""]
        "x" -> ["x"]
        _ -> []

-- | Tables: lines of words, with the same list symbols for the lines and for the words.
tables :: FTA.PlainFTA String String
tables =
    automaton
        "table"
        [ ("table", [node "table" ["lines"]])
        , ("lines", [leaf "nil", node "cons" ["words", "lines"]])
        , ("words", [leaf "nil", node "cons" ["word", "words"]])
        , ("word", [leaf "one", leaf "two"])
        ]

-- | The texts of 'tables': a line feed between lines, and a space between words.
tableTexts :: StateLinearization String String
tableTexts = StateLinearization{stateTexts = texts, stateOrder = \_ _ -> Nothing, stateBrackets = const []}
  where
    texts state symbol = case (state, symbol) of
        ("table", "table") -> ["", ""]
        ("lines", "nil") -> ["."]
        ("lines", "cons") -> ["", "\n", ""]
        ("words", "nil") -> [";"]
        ("words", "cons") -> ["", " ", ""]
        (_, "one") -> ["1"]
        (_, "two") -> ["2"]
        _ -> []

-- | The chains with an even number of s nodes, through two states.
evenChains :: FTA.PlainFTA String String
evenChains = automaton "even" [("even", [leaf "z", node "s" ["odd"]]), ("odd", [node "s" ["even"]])]

-- | The texts of 'evenChains'.
chainTexts :: Linearization String
chainTexts symbol = case symbol of
    "z" -> ["0"]
    "s" -> ["S(", ")"]
    _ -> []

{- | Lists of items with special characters, with a transition to a state that
accepts nothing and a state that the initial state cannot reach.
-}
lists :: FTA.PlainFTA String String
lists =
    automaton
        "list"
        [ ("list", [leaf "nil", node "cons" ["item", "list"], node "wrap" ["dead"]])
        , ("item", [leaf "quote", leaf "backslash", leaf "newline", leaf "control", leaf "accent"])
        , ("dead", [node "wrap" ["dead"]])
        , ("unreachable", [leaf "nil"])
        ]

-- | The texts of 'lists'.
listTexts :: Linearization String
listTexts symbol = case symbol of
    "nil" -> ["[]"]
    "cons" -> ["", " :: ", ""]
    "wrap" -> ["<", ">"]
    "quote" -> ["\"q\""]
    "backslash" -> ["\\"]
    "newline" -> ["\n\t"]
    "control" -> ["\1"]
    "accent" -> ["é"]
    _ -> []

-- | The terms of the automaton with at most 'sizeBound' nodes.
members :: FTA.PlainFTA String String -> [Term String]
members fixture = filter (FTA.accepts fixture) $ allTerms (alphabet fixture) =<< [1 .. sizeBound]

-- | The text of a term, or an error when the linearization does not fit.
linearizeOrFail :: Linearization String -> Term String -> String
linearizeOrFail texts found = fromMaybe (error $ "no text for a term of size " <> show (length found)) $ linearize texts found

-- | The symbols of the automaton with their arities.
alphabet :: FTA.PlainFTA String String -> [(String, Int)]
alphabet fixture =
    nubOrd
        [ (FTA.transitionSymbol transition, length $ FTA.transitionChildren transition)
        | transitions <- Map.elems $ FTA.transitionTable fixture
        , transition <- transitions
        ]

-- | Every term of the given size over the symbols.
allTerms :: [(String, Int)] -> Int -> [Term String]
allTerms symbols size =
    [ term symbol children
    | (symbol, arity) <- symbols
    , children <- spread arity (size - 1)
    ]
  where
    spread 0 0 = [[]]
    spread 0 _ = []
    spread arity remaining =
        [ first : rest
        | firstSize <- [1 .. remaining - (arity - 1)]
        , first <- allTerms symbols firstSize
        , rest <- spread (arity - 1) (remaining - firstSize)
        ]

-- | One item of an alternative: the name of a rule, or a literal text.
data Item = Rule String | Literal String

-- | A token of a grammar line: a name, a literal text, or one of the marks @:@ and @|@.
data Token = Name String | Text String | Colon | Bar

{- | The rules of a grammar in the part of the Lark syntax that 'larkGrammar'
writes: one rule on each line, with alternatives of names and literals.
-}
readGrammar :: String -> Map.Map String [[Item]]
readGrammar = Map.fromList . map (rule . tokens) . lines
  where
    rule (Name name : Colon : rest) = (name, alternatives rest)
    rule _ = error "not a rule"
    alternatives line = case break isBar line of
        (first, _ : rest) -> map item first : alternatives rest
        (first, []) -> [map item first]
    isBar Bar = True
    isBar _ = False
    item (Name name) = Rule name
    item (Text text) = Literal text
    item _ = error "not an item"

-- | The tokens of a line, with the JSON escapes of the literals read.
tokens :: String -> [Token]
tokens line = case line of
    [] -> []
    ' ' : rest -> tokens rest
    ':' : rest -> Colon : tokens rest
    '|' : rest -> Bar : tokens rest
    '"' : rest -> let (text, after) = literalText rest in Text text : tokens after
    _ -> case span isAlphaNum line of
        ("", _) -> error "an unexpected character"
        (name, rest) -> Name name : tokens rest
  where
    literalText input = case input of
        '"' : rest -> ("", rest)
        '\\' : 'u' : rest -> case readHex (take 4 rest) of
            [(code, "")] -> prepend (chr code) $ literalText $ drop 4 rest
            _ -> error "a bad unicode escape"
        '\\' : escaped : rest -> prepend (fromMaybe (error "a bad escape") $ lookup escaped escapes) $ literalText rest
        character : rest -> prepend character $ literalText rest
        [] -> error "an open literal"
    escapes = [('"', '"'), ('\\', '\\'), ('/', '/'), ('b', '\b'), ('f', '\f'), ('n', '\n'), ('r', '\r'), ('t', '\t')]
    prepend character (text, rest) = (character : text, rest)

{- | Whether the rule @start@ of the grammar derives the text.

A table holds whether a rule derives the text between two positions. Each
item that is a rule takes at least one character, because each rule derives
only texts that are not empty. So a rule that is not the last item of its
alternative takes a shorter text than the alternative, and an entry reads only
entries for shorter texts, or for the same text through an alternative that is
only one rule. The fixtures have no cycle of such alternatives, so the lazy
table is well founded.
-}
recognizes :: Map.Map String [[Item]] -> String -> Bool
recognizes grammar text = derives "start" 0 (length text)
  where
    table =
        Map.fromList
            [ ((name, from, to), any (\alternative -> matches alternative from to) alternatives)
            | (name, alternatives) <- Map.toList grammar
            , from <- [0 .. length text]
            , to <- [from .. length text]
            ]
    derives name from to = table Map.! (name, from, to)
    matches [] from to = from == to
    matches (Literal literal : rest) from to =
        from + length literal <= to && literal `isPrefixOf` drop from text && matches rest (from + length literal) to
    matches (Rule name : rest) from to =
        or [derives name from middle && matches rest middle to | middle <- [from + 1 .. if null rest then to else to - 1]]

-- | An automaton from rows of named states.
automaton :: String -> [(String, [FTA.Transition String String Constraint])] -> FTA.PlainFTA String String
automaton initial rows = either (error . show) id $ FTA.mkFTA initial rows

-- | A transition without children.
leaf :: String -> FTA.Transition String String Constraint
leaf symbol = FTA.Transition symbol [] noConstraint

-- | A transition without a constraint.
node :: String -> [String] -> FTA.Transition String String Constraint
node symbol children = FTA.Transition symbol children noConstraint

-- | A term from its symbol and children.
term :: String -> [Term String] -> Term String
term = Term.Node
