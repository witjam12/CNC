James Witt (witjam12) Michael Hartlley (harmic10)

>module Expr (Term(..), Type(..), eval, typeof)
>where

>import Data.List(nub)
>import Test.QuickCheck

Data constructor for terms. Derives show and eq.

>data Term t = T
>     | F 
>     | Z
>     | Succ (Term t)
>     | Pred (Term t)
>     | IsZero (Term t)
>     | If (Term t) (Term t) (Term t)
>     deriving (Show, Eq)

Data constructor for type. Derives show and eq.

>data Type ty = Boolean 
>             | Nat
>             deriving (Show, Eq)

Used for quickCheck

>instance Arbitrary (Term t) where
> arbitrary = elements testList

Test cases

>testList = [T,F,Z,
>            test1,test2,test3,test4,
>            test5,test6,test7,test8,
>            test9,test10,test11,test12,
>            test13]

>test1 = If F Z (Succ Z)
>test2 = IsZero (Pred (Succ Z))
>test3 = (IsZero Z)
>test4 = If T F T
>test5 = Succ (Succ Z)
>test6 = IsZero (Succ (Succ (Pred Z)))
>test7 = If test4 test5 test1
>test8 = IsZero test7
>test9 = IsZero (Pred (Succ (Succ (Succ (Pred (Succ Z))))))
>test10 = If test8 test9 test4
>test11 = Pred (Succ (Succ (Pred (Succ (Succ Z)))))
>test12 = If test10 test11 test5
>test13 = IsZero test12

Function to return the constants of terms. Not defined on stuck
terms.

>constsList(T) = T:[]
>constsList(F) = F:[]
>constsList(Z) = Z:[]
>constsList(Succ t) = (consts t)
>constsList(Pred t) = (consts t)
>constsList(IsZero t) = (consts t)
>constsList(If a b c) = (consts a) ++ (consts b) ++ (consts c)
>consts = nub.constsList

Function to return depth(size) of terms. Not defined for stuck
terms.

>size(T) = 1
>size(F) = 1
>size(Z) = 1
>size(Succ t) = (size t) + 1
>size(Pred t) = (size t) + 1
>size(IsZero t) = (size t) + 1
>size(If a b c) = (size a) + (size b) + (size c) + 1

Determines whether term is numerical or not. Returns T or F maybe
type. Not defined on stuck terms

>isNumerical Z = Just T
>isNumerical (Succ t) = isNumerical t
>isNumerical (Pred t) = isNumerical t
>isNumerical _ = Just F

Determines whether term is a value or not. Returns T or F maybe
type. Not defined on stuck terms

>isVal T = Just T
>isVal F = Just T
>isVal (IsZero t) | (isNumerical (eval2 (eval t))) == Just T = Just T
>                 | otherwise = Just F
>isVal (If T b c) = isVal b
>isVal (If F b c) = isVal c
>isVal (If a b c) = isVal (If (eval2 (eval1 a)) b c)
>isVal t | (isNumerical t) == Just T = Just T
>        | otherwise = Just F

Single step evaluator.

>eval1 T = Just T
>eval1 F = Just F
>eval1 Z = Just Z
>eval1 (If T b c) = Just b
>eval1 (If F b c) = Just c
>eval1 (If a b c) = case eval1 a of
>                     Nothing -> Nothing
>                     Just a1 -> Just (If a1 b c)
>eval1 (Succ t) = case eval1 t of
>                   Nothing -> Nothing
>                   Just t1 -> Just (Succ t1)
>eval1 (Pred Z) = Just Z
>eval1 (Pred (Succ t)) = Just t
>eval1 (Pred t) = case eval1 t of
>                   Nothing -> Nothing
>                   Just t1 -> Just (Pred t1)
>eval1 (IsZero Z) = Just T
>eval1 (IsZero (Succ t)) = Just F
>eval1 (IsZero t) | (isNumerical (eval2 (eval t))) == Just T 
>                    = case eval t of
>                          Nothing -> Nothing
>                          Just t1 -> Just (IsZero t1)
>                 | (isNumerical t) == Just F 
>                    = error "Can't call IsZero on non-NV"

eval2 pulls the term out of Maybe type because eval is defined
to accept Terms types, not Maybe types.

>eval2 (Just t) = t

Recursive big step evaluator. takes and returns constructed types

>eval t = case eval1 t of
>           Nothing -> Nothing
>           Just T -> Just T
>           Just F -> Just F
>           Just Z -> Just Z
>           Just (Succ t) -> Just (Succ (eval2 (eval t))) 
>           Just t1 -> eval2 (Just (eval t1))

Takes construced type terms and returns primitive types of terms.
Not defined for stuck terms

>typeof T = Boolean
>typeof F = Boolean
>typeof (IsZero t) | (isNumerical (eval2 (eval t))) == Just T 
>                     = Boolean
>                  | (isNumerical t) == Just F 
>                     = error ("IsZero "++ show t ++" does not type")
>typeof Z = Nat
>typeof (Succ Z) = Nat
>typeof (Succ t) = typeof t
>typeof (Pred Z) = Nat
>typeof (Pred t) = typeof t
>typeof (If T b c) = typeof b
>typeof (If F b c) = typeof c
>typeof (If a b c) = typeof (eval2 (eval (If a b c)))

typeof t = error ("term (" ++ show t ++ ") does not type")

Maps eval function to every element of testList

>evalTester = map eval testList

Maps typeof function to every element of testList

>typeTester = map typeof testList

Propositions for quickcheck. isvalProp checks if a term and the
evaluation of that term are both values.

typeprop checks if a term and the evaluation of that term have
the same type.

>isvalProp :: (Term t) -> Bool
>isvalProp t = isVal (eval2 (eval t)) == isVal t
>runtest1 = quickCheck isvalProp
>runtest12 = verboseCheck isvalProp

>typeProp :: (Term t) -> Bool
>typeProp t = typeof (eval2 (eval t)) == typeof t
>runtest2 = quickCheck typeProp
>runtest3 = verboseCheck typeProp

