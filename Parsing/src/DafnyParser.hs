{- | A Parser for MiniDafny
     ======================

For this problem, you will implement a parser for the Lu programming language.

-} 

module DafnyParser where

{- |

Make sure that you read the [`Syntax`](Syntax.html) module that describes
the syntax of MiniDafny before continuing.

This problem also uses definitions from the Parsers module from the lecture
notes, gathered together in the module [`Parser.hs`](Parser.hs). Operations
such as `chainl1` and `filter` are imported as `P.chainl1` and `P.filter`.
You should also familiarize yourself with this module before continuing.

The goal of this part of the exercise is to give you practice with the
operations in the `Control.Applicative` library. As a result the `Parser`
type is *not* given a monad instance, so you will not be able use `do`
notation with it. Furthermore, you may not edit the `Parser` module, and you
do not have access to the constructor for the `Parser` type, so you will not
be able to define your own monad instance either. 

-}

import Control.Applicative
import qualified Data.Char as Char
import Syntax
import Parser (Parser)
import qualified Parser as P
import Test.HUnit  (runTestTT,Test(..),Assertion, (~?=), (~:), assert, Counts)

{- | Testing your Parser
      ------------------

Your primary method of testing your parser should be using the following properties, though you will also
want to define your own unit tests as you go.

In particular, the following "round tripping" properties should be satisfied
 by your implementation. These properties state that given an arbitrary
 Value/Expression/Statement, if we pretty print it 

-}

prop_roundtrip_val :: Value -> Bool
prop_roundtrip_val v = P.parse valueP (pretty v) == Right v

prop_roundtrip_exp :: Expression -> Bool
prop_roundtrip_exp e = P.parse expP (pretty e) == Right e

prop_roundtrip_stat :: Statement -> Bool
prop_roundtrip_stat s = P.parse statementP (pretty s) == Right s

{- | More Parser combinators
     -----------------------

As a warm-up, let's define a few helper functions that we can use later.

In general, so that our parsers are flexible about spaces that appear in
source programs, all of the parsers will need to skip over any trailing white
space.

First, define a parser combinator which takes a parser, runs it,
then skips over any whitespace characters occurring afterwards. HINT: you'll
need the `space` parser from the [Parser](Parser.hs) library.

-}

wsP :: Parser a -> Parser a
wsP p = p <* many P.space

test_wsP :: Test
test_wsP = TestList [
  P.parse (wsP P.alpha) "a" ~?= Right 'a',
  P.parse (many (wsP P.alpha)) "a b \n   \t c" ~?= Right "abc",
  P.parse (wsP P.digit) "1  2   2" ~?= Right '1',
  P.parse (wsP P.alpha) "abba" ~?= Right 'a',
  P.parse (many (wsP P.alpha)) "      " ~?= Right "",
  P.parse (many (wsP P.digit)) "  2 3 5 " ~?= Right "",
  P.parse (many (wsP P.digit)) "2  3  4  5  " ~?= Right "2345"
  ]

{- |
Use this to define a parser that accepts *only* a particular string `s`
and consumes any white space that follows. The last test case ensures
that trailing whitespace is being treated appropriately.
-}

stringP :: String -> Parser ()
stringP s = wsP (P.string s) *> pure () 

test_stringP :: Test
test_stringP = TestList [
  P.parse (stringP "a") "a" ~?= Right (),
  P.parse (stringP "a") "b" ~?= Left "No parses",
  P.parse (many (stringP "a")) "a  a" ~?= Right [(),()],
  P.parse (stringP "a") "a  a" ~?= Right ()
  ]

-- | Define a parser that will accept a particular string `s`, returning a
-- | given value `x`, and also and consume any white space that follows.

constP :: String -> a -> Parser a
constP s v = stringP s *> pure v

test_constP :: Test
test_constP = TestList [
  P.parse (constP "&" 'a')  "&  " ~?=  Right 'a',
  P.parse (many (constP "&" 'a'))  "&   &" ~?=  Right "aa",
  P.parse (constP "&" 'a') "&   &" ~?= Right 'a',
  P.parse (constP "&" 'a') "!    !" ~?= Left "No parses"
  ]

-- | We will also use `stringP` for some useful operations that parse between
-- | delimiters, consuming additional whitespace.

parens :: Parser a -> Parser a
parens x = P.between (stringP "(") x (stringP ")")

braces :: Parser a -> Parser a
braces x = P.between (stringP "{") x (stringP "}")

-- >>> P.parse (many (brackets (constP "1" 1))) "[1] [  1]   [1 ]"
-- Right [1,1,1]
brackets :: Parser a -> Parser a
brackets x = P.between (stringP "[") x (stringP "]")


test_braces :: Test
test_braces = TestList [
  P.parse (braces (many P.alpha)) "{dog}" ~?= Right "dog",
  P.parse (many (braces (many P.alpha))) "{dog}\n{cat}" ~?= Right ["dog", "cat"],
  P.parse (braces (many P.alpha)) "dog" ~?= Left "No parses",
  P.parse (braces (many P.alpha)) "{dog" ~?= Left "No parses",
  P.parse (braces (many P.alpha)) "dog}" ~?= Left "No parses"
  ]

test_brackets :: Test
test_brackets = TestList [
  P.parse (many (brackets (constP "1" 1))) "[1] [  1]   [1 ]" ~?= Right [1,1,1],
  P.parse (many (brackets (constP "1" 1))) "[1]  \n  [  1] \n  [1 ] \n\n\n" ~?= Right [1,1,1]
  ]


{- | Parsing Constants
     -----------------

Now let's write parsers for the `Value` type, except for table constants
(which we won't parse).

-}

valueP :: Parser Value
valueP = intValP <|> boolValP

-- | To do so, fill in the implementation of the four parsers above. As above, these
--   four parsers should consume any following whitespace. You can make sure that happens
--   by testing 'many' uses of the parser in a row.

-- >>> P.parse (many intValP) "1 2\n 3"
-- Right [IntVal 1,IntVal 2,IntVal 3]
intValP :: Parser Value
intValP = IntVal <$> (wsP P.int) 

test_intValP :: Test
test_intValP = TestList [
  P.parse (many intValP) "1 2\n 3" ~?= Right [IntVal 1,IntVal 2,IntVal 3],
  P.parse intValP "1" ~?= Right (IntVal 1),
  P.parse (many intValP) "1 2\n 3\n y" ~?= Right [IntVal 1, IntVal 2, IntVal 3],
  P.parse intValP "d\n 1 2" ~?= Left "No parses"
  ]

-- >>> P.parse (many boolValP) "true false\n true"
-- Right [BoolVal True,BoolVal False,BoolVal True]
boolValP :: Parser Value
boolValP = BoolVal <$> ((constP "true" True) <|> (constP "false" False))

test_boolValP :: Test
test_boolValP = TestList [
  P.parse (many boolValP) "true false\n true" ~?= Right [BoolVal True,BoolVal False,BoolVal True],
  prop_roundtrip_val (IntVal 2) ~?= True
  ]

-- | At this point you should be able to run tests using the `prop_roundtrip_val` property. 

{- | Parsing Types
     -------------

We provide you with the parser for types, which for miniDafny can only be "int", "bool", or "array<int>".

-}

typeP :: Parser Type
typeP = constP "int" TInt <|> constP "bool" TBool <|> constP "array<int>" TArrayInt

{- | Parsing Expressions
     -------------------

Next, let's parse some Mini Dafny expressions.

We've already stratified the grammar for you, so that we'll get the
appropriate precedence and associativity for the binary and unary
operators. Make sure to read the end of the parsers lecture to understand how
this code works.

However, this code *won't* work until you complete all the parts of this section.
-} 

expP :: Parser Expression
expP    = compP where
  compP   = catP `P.chainl1` opAtLevel (level Gt)
  catP    = conjP `P.chainl1` opAtLevel (level Eq)
  conjP   = sumP `P.chainl1` opAtLevel (level Conj)
  sumP    = prodP `P.chainl1` opAtLevel (level Plus)
  prodP   = uopexpP `P.chainl1` opAtLevel (level Times)
  uopexpP = baseP
      <|> Op1 <$> uopP <*> uopexpP 
  baseP = lenP
       <|> Var <$> varP
       <|> parens expP
       <|> Val <$> valueP
      -- .Length here

-- | Parse an operator at a specified precedence level
opAtLevel :: Int -> Parser (Expression -> Expression -> Expression)
opAtLevel l = flip Op2 <$> P.filter (\x -> level x == l) bopP

-- | Special Parsing for the .Length operator
lenP :: Parser Expression
lenP = (Op1 Len . Var . Name) <$> (nameP <* stringP ".Length")

test_expP :: Test
test_expP = TestList [
  P.parse expP "a.Length" ~?= Right (Op1 Len (Var (Name "a"))),
  prop_roundtrip_exp (Op1 Len (Var (Name "a"))) ~?= True
  ]

-- | A variable is a prefix followed by array indexing or just a name.

-- >>>  P.parse (many varP) "x y z"
-- Right [Name "x", Name "y", Name "z"]
-- >>> P.parse varP "y[1]"
-- Right (Proj "y" (Val (IntVal 1)))
varP :: Parser Var
varP = arrIndP <|> varNameP

varNameP :: Parser Var
varNameP = Name <$> nameP

arrIndP :: Parser Var 
arrIndP = Proj <$> nameP <*> brackets expP

test_varP :: Test
test_varP = TestList [
  P.parse varP "a.Length" ~?= Right (Name "a")
  ]

{- | 
Define an expression parser for names. Names can be any sequence of upper and
lowercase letters, digits and underscores, not beginning with a digit and not
being a reserved word. Your parser should also consume any trailing
whitespace characters.
-}

reserved :: [String]
reserved = [ "assert", "break","else","Length"
 ,"false","for","function","invariant","if","in"
 ,"return","true","method","int", "bool", "while", "requires", "ensures"]

isValid :: String -> Bool
isValid (s:ss) = notReserved (s:ss) && notDigit s 
isValid _ = False

notDigit :: Char -> Bool
notDigit = not . (\c -> Char.isDigit c)

notReserved :: String -> Bool
notReserved = not . (\s -> elem s reserved)

isValidChar :: Char -> Bool
isValidChar = (\c -> (not (Char.isSpace c)) && (Char.isAlpha c || Char.isDigit c || c == '_'))

-- >>> P.parse (many nameP) "x sfds _ int"
-- Right ["x","sfds", "_"]
nameP :: Parser Name
nameP = P.filter isValid (wsP (some (P.satisfy (isValidChar))))

test_nameP :: Test
test_nameP = TestList [
  P.parse (many nameP) "x sfds _ int" ~?= Right ["x","sfds", "_"],
  P.parse (many nameP) "       arr" ~?= Right [],
  P.parse nameP "       arr" ~?= Left "No parses",
  P.parse (many nameP) "bool dog arr err" ~?= Right [],
  P.parse (many nameP) "arr three 1two dog" ~?= Right ["arr", "three"]
  ]

-- Now write parsers for the unary and binary operators. Make sure you
--  check out the Syntax module for the list of all possible
--  operators. The tests are not exhaustive.

-- >>> P.parse (many uopP) "- -"
-- Right [Neg,Neg]
uopP :: Parser Uop
uopP = (constP "-" Neg) <|> (constP "!" Not)

test_uopP :: Test
test_uopP = TestList [
  P.parse (many uopP) "- -" ~?= Right [Neg,Neg],
  P.parse uopP "-" ~?= Right Neg,
  P.parse uopP "!" ~?= Right Not,
  P.parse uopP "!dsad" ~?= Right Not,
  P.parse uopP "=!" ~?= Left "No parses"
  ]

-- >>> P.parse (many bopP) "+ >="
-- Right [Plus,Ge]
bopP :: Parser Bop
bopP = plusP <|> minusP <|> timesP <|> divideP <|>
       moduloP <|> impliesP <|> iffP <|> neqP <|> 
       eqP <|> geP <|> gtP <|> leP <|> ltP <|>
       conjP <|> disjP
  where 
     plusP = constP "+" Plus
     minusP = constP "-" Minus
     timesP = constP "*" Times
     divideP = constP "/" Divide
     moduloP = constP "%" Modulo
     eqP = constP "==" Eq
     neqP = constP "!=" Neq
     gtP = constP ">" Gt
     geP = constP ">=" Ge 
     ltP = constP "<" Lt
     leP = constP "<=" Le
     conjP = constP "&&" Conj
     disjP = constP "||" Disj
     impliesP = constP "==>" Implies
     iffP = constP "<==>" Iff

test_bopP :: Test
test_bopP = TestList [
  P.parse (many bopP) "+ >=" ~?= Right [Plus,Ge],
  P.parse bopP "<=" ~?= Right Le,
  P.parse bopP "==>" ~?= Right Implies,
  P.parse bopP "<==>" ~?= Right Iff,
  P.parse bopP "==" ~?= Right Eq,
  P.parse bopP "!=" ~?= Right Neq,
  P.parse bopP "&&" ~?= Right Conj,
  P.parse bopP "||" ~?= Right Disj,
  P.parse bopP ">" ~?= Right Gt,
  P.parse bopP "<" ~?= Right Lt,
  P.parse bopP "-" ~?= Right Minus,
  P.parse bopP "*" ~?= Right Times,
  P.parse bopP "/   " ~?= Right Divide,
  P.parse bopP "   !=" ~?= Left "No parses"
  ]

-- | At this point you should be able to test the  `prop_roundtrip_exp` property.

{- | Parsing Statements
     ------------------

First, define a parser for bindings... 

-}

bindingP :: Parser Binding
bindingP =  (,) <$> nameP <* stringP ":" <*> typeP


test_bindingP :: Test
test_bindingP = TestList [
  P.parse bindingP "x : int" ~?= Right ("x", TInt),
  P.parse (many bindingP) "x : int y : int" ~?= Right [("x", TInt), ("y", TInt)],
  P.parse bindingP "y = bool" ~?= Left "No parses"
  ]

-- | ...and predicates...
predicateP :: Parser Predicate
predicateP = pBindP <|> pNoBindP
  where 
    pBindP = Predicate <$> (P.sepBy bindingP (stringP ",")) <* stringP "::" <*> expP
    pNoBindP = Predicate <$> (P.sepBy bindingP (stringP ",")) <*> expP

test_predicateP :: Test
test_predicateP = TestList [
  P.parse predicateP "x : int :: 0 <= i && i < a.Length ==> a[i] > 0" ~?= Right (Predicate [("x", TInt)] (Op2 (Op2 (Op2 (Val (IntVal 0)) Le (Op2 (Var (Name "i")) Conj (Var (Name "i")))) Lt (Op1 Len (Var (Name "a")))) Implies (Var (Name "a")))),
  P.parse predicateP "x : int, y : bool :: y" ~?= Right (Predicate [("x", TInt), ("y", TBool)] (Var (Name "y"))),
  P.parse predicateP ": int :: x" ~?= Left "No parses",
  P.parse predicateP "x == true" ~?= Right (Predicate [] (Op2 (Var (Name "x")) Eq (Val (BoolVal True))))
  ]

-- | Finally, define a parser for statements:

-- ifP <|> whileP
-- If (exp) Block[] else Block[] if there is no else the second block is just empty i.e Block []

statementP :: Parser Statement
statementP = declP <|> assertP <|> assignP <|> ifP <|> whileP <|> emptyP
  where 
    declP = Decl <$> (stringP "var" *> bindingP <* stringP ":=") <*> expP
    assertP = Assert <$> (stringP "assert" *> predicateP)
    assignP = Assign <$> varP <* stringP ":=" <*> expP
    ifP = elseP <|> noElseP 
      where 
        elseP = If <$> (stringP "if" *> expP) <*> blockP <* stringP "else" <*> blockP 
        noElseP = If <$> (stringP "if" *> expP) <*> blockP <*> pure (Block[])
    whileP = (\exp predicates block -> While predicates exp block)
      <$> (stringP "while" *> expP)
      <*> many (stringP "invariant" *> predicateP)
      <*> blockP
    emptyP = stringP ";" *> pure Empty

test_statementP :: Test
test_statementP = TestList [
  P.parse statementP "var x : int := e;" ~?= Right (Decl ("x",TInt) (Var (Name "e"))),
  P.parse statementP "assert x" ~?= Right (Assert (Predicate [] (Var (Name "x")))),
  P.parse statementP "x := e" ~?= Right (Assign (Name "x") (Var (Name "e"))),
  P.parse (many statementP) "x := e;" ~?= Right [(Assign (Name "x") (Var (Name "e"))), Empty],
  P.parse statementP "while x < a invariant x <= a invariant y == 0 invariant z == x + y + c {x := x + 1; z := z + 1;}" ~?= Right (While [Predicate [] (Op2 (Var (Name "x")) Le (Var (Name "a"))),Predicate [] (Op2 (Var (Name "y")) Eq (Val (IntVal 0))),Predicate [] (Op2 (Var (Name "z")) Eq (Op2 (Op2 (Var (Name "x")) Plus (Var (Name "y"))) Plus (Var (Name "c"))))] (Op2 (Var (Name "x")) Lt (Var (Name "a"))) (Block [Assign (Name "x") (Op2 (Var (Name "x")) Plus (Val (IntVal 1))),Empty,Assign (Name "z") (Op2 (Var (Name "z")) Plus (Val (IntVal 1))),Empty]))
  ]

-- | ... and one for blocks.

-- It looks like statements are separated by an Empty Statement

blockP :: Parser Block
blockP = Block <$> P.between (stringP "{") (many statementP) (stringP "}")

{- | Parsing Methods
     ---------------

   Implement parsing for methods. You will probably want to modularize it
   by implementing parsing for specifications/invariants and many bindings.

-}

-- | Specifications
specP :: Parser Specification 
specP = requiresP <|> ensuresP <|> modifiesP
  where 
    requiresP = rForAllP <|> rNoForAllP
      where 
        rNoForAllP = Requires <$> (stringP "requires" *> predicateP)
        rForAllP = Requires <$> ((stringP "requires" *> stringP "forall") *> predicateP)
    ensuresP = eForAllP <|> eNoForAllP
      where 
        eNoForAllP = Ensures <$> (stringP "ensures" *> predicateP)
        eForAllP = Ensures <$> ((stringP "ensures" *> stringP "forall") *> predicateP)
    modifiesP = Modifies <$> nameP

specsP :: Parser [Specification]
specsP = many specP

-- | Many bindings ex. (x : int, y : int)
bindingsP :: Parser [Binding]
bindingsP = (parens (P.sepBy bindingP (stringP ",")))

methodP :: Parser Method
methodP = Method <$> (stringP "method" *> nameP) <*> (bindingsP <* (stringP "returns")) <*> bindingsP <*> specsP <*> blockP


test_method :: Test
test_method = TestList [
  P.parse methodP "method Abs (r : int) returns (absR : int) { if r < 0 { absR := -r;} else {absR := r;}}" ~?= Right (Method "Abs" [("r",TInt)] [("absR",TInt)] []
              (Block [If (Op2 (Var (Name "r")) Lt (Val (IntVal 0)))
                         (Block [Assign (Name "absR") (Op1 Neg (Var (Name "r"))),Empty])
                         (Block [Assign (Name "absR") (Var (Name "r")),Empty])]))
  ]
{- | Parsing Expressions and Files
     -----------------------------

Finally, we'll export these convenience functions for calling
the parser.

-}

parseDafnyExp :: String -> Either P.ParseError Expression
parseDafnyExp = P.parse expP 

parseDafnyStat :: String -> Either P.ParseError Statement
parseDafnyStat = P.parse statementP

parseDafnyFile :: String -> IO (Either P.ParseError Method)
parseDafnyFile = P.parseFromFile (const <$> methodP <*> P.eof) 

{- File-based tests
   ----------------
-}

tParseFiles :: Test
tParseFiles = "parse files" ~: TestList [
                 "abs"  ~: p "dafny/abs.dfy"  wAbs,
                 "minVal"  ~: p "dafny/findMinVal.dfy"  wMinVal,
                 "minIndex"  ~: p "dafny/findMinIndex.dfy"  wMinIndex,                 
                 "minMax"   ~: p "dafny/minMax.dfy"   wMinMax,
                 "arraySpec" ~: p "dafny/arraySpec.dfy" wArraySpec
               ] where
   p fn ast = do
     result <- parseDafnyFile fn
     case result of
       (Left _) -> assert False
       (Right ast') -> assert (ast == ast')

{- | Unit Tests
      ---------

These unit tests summarize the tests given above.
-}

test_comb = "parsing combinators" ~: TestList [
 P.parse (wsP P.alpha) "a" ~?= Right 'a',
 P.parse (many (wsP P.alpha)) "a b \n   \t c" ~?= Right "abc",
 P.parse (stringP "a") "a" ~?= Right (),
 P.parse (stringP "a") "b" ~?= Left "No parses",
 P.parse (many (stringP "a")) "a  a" ~?= Right [(),()],
 P.parse (constP "&" 'a')  "&  " ~?=  Right 'a',
 P.parse (many (constP "&" 'a'))  "&   &" ~?=  Right "aa",
 P.parse (many (brackets (constP "1" 1))) "[1] [  1]   [1 ]" ~?= Right [1,1,1]
 ]

test_value = "parsing values" ~: TestList [
 P.parse (many intValP) "1 2\n 3" ~?= Right [IntVal 1,IntVal 2,IntVal 3],
 P.parse (many boolValP) "true false\n true" ~?= Right [BoolVal True,BoolVal False,BoolVal True]
 ]

test_exp = "parsing expressions" ~: TestList [
 P.parse (many varP) "x y z" ~?= Right [Name "x", Name "y", Name "z"],
 P.parse (many nameP) "x sfds _" ~?= Right ["x","sfds", "_"],
 P.parse (many uopP) "- -" ~?=  Right [Neg,Neg],
 P.parse (many bopP) "+ >= .." ~?= Right [Plus,Ge]
 ]

test_stat = "parsing statements" ~: TestList [
 P.parse statementP ";" ~?= Right Empty,
 P.parse statementP "x := 3" ~?= Right (Assign (Name "x") (Val (IntVal 3))),
 P.parse statementP "if x { y := true; }" ~?=
    Right (If (Var (Name "x")) (Block [Assign (Name "y") (Val $ BoolVal True), Empty]) (Block [])),
 P.parse statementP "while 0 { }" ~?=
    Right (While [] (Val (IntVal 0)) (Block []))
   ]

-- | Testing summary
--------------------

test_all :: IO Counts
test_all = runTestTT $ TestList [ test_comb, test_value, test_exp, test_stat, tParseFiles ]

