import Prelude hiding (Left, Right)

data CBTree a = Empty | Perfect a (CBTree a) (CBTree a) | Left a (CBTree a) (CBTree a) | Right a (CBTree a) (CBTree a) deriving Show

insert :: Ord a => a -> CBTree a -> CBTree a
insert x Empty = Perfect x Empty Empty
insert x (Perfect y Empty Empty) = Right y (Perfect x Empty Empty) Empty
insert x (Perfect y l r) = Left y (insert x l) r 
insert x (Left y l r) = case insert x l of
				Perfect y' l' r' -> Right y (Perfect y' l' r') r
				t -> Left y t r
insert x (Right y l r) = case insert x r of
				Perfect y' l' r' -> Perfect y l (Perfect y' l' r')
				t -> Right y l t
