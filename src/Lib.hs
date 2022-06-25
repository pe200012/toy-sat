{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

module Lib where
import           Control.Monad                  ( join )
import           Data.List                      ( find
                                                , foldl'
                                                , intercalate
                                                )
import           Data.List.NonEmpty             ( NonEmpty((:|))
                                                , nub
                                                , singleton
                                                , toList
                                                )

data Prop a = P a | N a | T | F
    deriving (Eq, Ord, Functor)

true :: Prop a -> Bool
true T = True
true _ = False

false :: Prop a -> Bool
false F = True
false _ = False

type family NegType a :: b
type instance NegType (Prop a) = Prop a
type instance NegType (Conj (Prop a)) = Disj (Prop a)
type instance NegType (Disj (Prop a)) = Conj (Prop a)

class Neg a where
    neg :: a -> NegType a

instance Neg (Prop a) where
    neg (P a) = N a
    neg (N a) = P a
    neg T     = F
    neg F     = T

instance Show a => Show (Prop a) where
    show (P a) = show a
    show (N a) = "¬" ++ show a
    show T     = "T"
    show F     = "F"

-- | conjuncture
newtype Conj a = Conj { unConj :: [a] }
  deriving (Eq, Functor, Foldable, Traversable, Applicative, Monad)

instance Neg (Conj (Prop a)) where
    neg (Conj xs) = Disj (neg <$> xs)

-- | disjunction
newtype Disj a = Disj { unDisj :: [a] }
  deriving (Eq, Functor, Foldable, Traversable, Applicative, Monad)

instance Neg (Disj (Prop a)) where
    neg (Disj xs) = Conj (neg <$> xs)

-- | conjunctive normal form
newtype CNF a = CNF { unCNF :: Conj (Disj (Prop a)) }
  deriving (Eq, Functor)

-- | disjunctive normal form
newtype DNF a = DNF { unDNF :: Disj (Conj (Prop a)) }
  deriving (Eq, Functor)

prettyprintConj :: Show a => Conj a -> String
prettyprintConj (Conj x) = case x of
    []  -> "∅"
    [a] -> show a
    _   -> "(" ++ intercalate " ∧ " (show <$> x) ++ ")"

prettyprintDisj :: Show a => Disj a -> String
prettyprintDisj (Disj x) = case x of
    []  -> "∅"
    [a] -> show a
    _   -> "(" ++ intercalate " ∨ " (show <$> x) ++ ")"

instance Show a => Show (Conj a) where
    show = prettyprintConj

instance Show a => Show (Disj a) where
    show = prettyprintDisj

instance Show a => Show (CNF a) where
    show (CNF x) = prettyprintConj x

instance Show a => Show (DNF a) where
    show (DNF x) = prettyprintDisj x

disjOne :: Eq a => Prop a -> Conj (Prop a) -> Conj (Disj (Prop a))
disjOne a (Conj x) = Conj [ if p == T then Disj [a] else Disj [a, p] | p <- x, p /= F, neg a /= p ]

disjCNF :: Eq a => Prop a -> Conj (Disj (Prop a)) -> Conj (Disj (Prop a))
disjCNF a (Conj x) = Conj [ if a `elem` y then Disj y else Disj (a : y) | Disj y <- x, neg a `notElem` y ]

disjMany :: Eq a => Conj (Prop a) -> Conj (Prop a) -> Conj (Disj (Prop a))
disjMany (Conj x) b = Conj (unConj . flip disjOne b =<< x)

disj :: Eq a => Conj (Prop a) -> Conj (Disj (Prop a)) -> Conj (Disj (Prop a))
disj (Conj x) b = Conj (unConj . flip disjCNF b =<< x)

dNFToCNF :: Eq a => DNF a -> CNF a
dNFToCNF (DNF (Disj []      )) = CNF (Conj [Disj [F]])
dNFToCNF (DNF (Disj (x : xs))) = CNF $ foldr disj (Disj . pure <$> x) xs

-- >>> dNFToCNF (DNF (Disj [Conj [P "a", P "b"], Conj [N "a", N "b"], Conj [P "a"]]))
-- (¬"b" ∨ "a")

unitClauses :: CNF a -> [Prop a]
unitClauses (CNF (Conj x)) = [ head y | Disj y <- x, null $ tail y, not $ true $ head y ]

conflict :: Eq a => [Prop a] -> Bool
conflict xs = any ((`elem` xs) . neg) xs

unitPropagate :: (Eq a, Show a) => CNF a -> CNF a
unitPropagate = go []
  where
    go vis x@(CNF (Conj ps))
        | conflict vis = CNF (Conj [Disj [F]])
        | otherwise = case unitClauses x of
            [] -> CNF $ Conj ((Disj . pure <$> vis) ++ ps)
            (filter (`notElem` vis) -> prs) ->
                go (prs ++ vis) (foldr (\pr (CNF (Conj xs)) -> CNF $ Conj [ Disj $ filter (/= neg pr) p | (Disj p) <- xs, pr `notElem` p ]) x prs)

-- >>> unitPropagate (CNF (Conj [Disj [P "a", P "b"], Disj [N "a", P "c"], Disj [N "c", P "d"], Disj [P "a"]]))
-- ("d" ∧ "c" ∧ "a")

-- >>> unitPropagate (CNF (Conj [Disj [P "a", P "b"], Disj [N "a", N "b"]]))
-- (("a" ∨ "b") ∧ (¬"a" ∨ ¬"b"))

resolve :: Eq a => Disj (Prop a) -> Disj (Prop a) -> Either (Disj (Prop a), Disj (Prop a)) (Disj (Prop a))
resolve x@(Disj a) y@(Disj b) = case find ((`elem` b) . neg) a of
    Nothing -> Left (x, y)
    Just pr ->
        let c = [ p | p <- a ++ b, p /= pr, p /= neg pr, p /= F ]
        in  case find ((`elem` c) . neg) c of
                Nothing -> Right (Disj c)
                Just _  -> Right (Disj [T])
