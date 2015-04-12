module BHeap where

import Prelude hiding (Left, Right, last, drop)
import PLRTree hiding (insert)

type BHeap a = PLRTree a

insert :: Ord a => a -> BHeap a -> BHeap a
insert x Empty = Perfect x Empty Empty
insert x (Perfect y Empty Empty) = Right (min x y) (Perfect (max x y) Empty Empty) Empty
insert x (Perfect y l r) = Left (min x y) (insert (max x y) l) r 
insert x (Left y l r) = case insert (max x y) l of
				Perfect y' l' r' -> Right (min x y) (Perfect y' l' r') r
				t -> Left (min x y) t r
insert x (Right y l r) = case insert (max x y) r of
				Perfect y' l' r' -> Perfect (min x y) l (Perfect y' l' r')
				t -> Right (min x y) l t

build :: Ord a => [a] -> BHeap a
build = foldl (flip insert) Empty
				
push :: Ord a => BHeap a -> BHeap a
push Empty = Empty
push (Perfect x Empty Empty) = Perfect x Empty Empty
push (Perfect x l r) = push' Perfect x l r
push (Left x l r) = push' Left x l r
push (Right x (Perfect y Empty Empty) Empty) = Right (min x y) (Perfect (max x y) Empty Empty) Empty
push (Right x l r) = push' Right x l r

push' :: Ord a => (a -> BHeap a -> BHeap a -> BHeap a) -> a -> BHeap a -> BHeap a -> BHeap a
push' f x l r
  | x <= rl && x <= rr = f x l r
  | x <= rl && rr <= x = f rr l (push (setRoot x r)) 
  | rl <= x && x <= rr = f rl (push (setRoot x l)) r 
  | rl <= x && rr <= x && rl <= rr = f rl (push (setRoot x l)) r 
  | otherwise = f rr l (push (setRoot x r)) 
  where rl = root l;
		rr = root r

drop :: Ord a => BHeap a -> BHeap a
drop Empty = Empty
drop (Perfect _ Empty Empty) = Empty
drop h = push (setRoot x h') 
	where x = last h;
		h' = dropLast h

flatten :: Ord a => BHeap a -> [a]
flatten Empty = []
flatten h = root h : flatten (drop h)
