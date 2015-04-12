module PLRTree where

import Prelude hiding (Left, Right, last)

data PLRTree a = Empty | Perfect a (PLRTree a) (PLRTree a) | Left a (PLRTree a) (PLRTree a) | Right a (PLRTree a) (PLRTree a) deriving Show

insert :: a -> PLRTree a -> PLRTree a
insert x Empty = Perfect x Empty Empty
insert x (Perfect y Empty Empty) = Right y (Perfect x Empty Empty) Empty
insert x (Perfect y l r) = Left y (insert x l) r 
insert x (Left y l r) = case insert x l of
				Perfect y' l' r' -> Right y (Perfect y' l' r') r
				t -> Left y t r
insert x (Right y l r) = case insert x r of
				Perfect y' l' r' -> Perfect y l (Perfect y' l' r')
				t -> Right y l t

last :: PLRTree a -> a
last Empty = error "Empty!"
last (Perfect x Empty Empty) = x
last (Perfect _ _ r) = last r
last (Left _ l _) = last l
last (Right _ l Empty) = last l
last (Right _ l (Perfect _ _ _)) = last l
last (Right _ _ r) = last r

dropLast :: PLRTree a -> PLRTree a
dropLast Empty = Empty
dropLast (Perfect _ Empty Empty) = Empty
dropLast (Perfect x l r) = Right x l (dropLast r)
dropLast (Left x l r) = case dropLast l of
				Perfect y' l' r' -> Perfect x (Perfect y' l' r') r
				t -> Left x t r
dropLast (Right x _ Empty) = Perfect x Empty Empty
dropLast (Right x l (Perfect y l' r')) = Left x (dropLast l) (Perfect y l' r')
dropLast (Right x l r) = Right x l (dropLast r)

root :: PLRTree a => a
root Empty = error "Empty!"
root (Perfect x _ _) = x
root (Left x _ _) = x
root (Right x _ _) = x

setRoot :: a -> PLRTree a -> PLRTree a
setRoot _ Empty = Empty
setRoot x (Perfect _ l r) = Perfect x l r
setRoot x (Left _ l r) = Left x l r
setRoot x (Right _ l r) = Right x l r
