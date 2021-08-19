{-# LANGUAGE MultiParamTypeClasses #-}

class Addable a b where
    add :: a -> b -> a

instance Addable Int  Int where
    add x y = x + y

instance Addable Int Bool where
    add x y = if y then x + 1 else x

ex1 :: Addable Int b => b -> Int
ex1 = add (1 :: Int)

-- no parallel here

ex2 = add (1 :: Int) (1 :: Int)
