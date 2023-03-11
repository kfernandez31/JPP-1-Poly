module DensePoly() where
import PolyClass
import Representation
import Data.List(dropWhileEnd)

toCanonicalDP :: (Eq a, Num a) => DensePoly a -> DensePoly a
toCanonicalDP = P . dropWhileEnd (== 0) . unP

instance Functor DensePoly where
    fmap f = P . (map f) . unP

instance Polynomial DensePoly where
    zeroP       = P []
    constP c    = if c == 0 then zeroP else P [c]
    varP        = P [0, 1]
    evalP  cs x = foldr (\c acc -> c + x * acc) 0 $ unP cs
    shiftP n    = P . (replicate n 0 ++) . unP 
    degree      = subtract 1 . length . unP . toCanonicalDP

instance (Eq a, Num a) => Num (DensePoly a) where
    abs                  = undefined
    signum               = undefined
    negate               = toCanonicalDP . (negate <$>)
    fromInteger          = constP . fromInteger
    (+) (P p)      (P q) = toCanonicalDP $ P $ go p q where
        go cs [] = cs
        go [] ds = ds
        go (c:cs) (d:ds) = c+d : go cs ds
    (*) (P [])     _     = zeroP
    (*) (P (c:cs)) q     = P ((*c) <$> (unP q)) + shiftP 1 (P cs * q)

-- |
-- >>> let x = varP :: DensePoly Integer in x^3 - 1
-- P {unP = [-1,0,0,1]}
instance (Eq a, Num a) => Eq (DensePoly a) where
    (==) p q = nullP (p-q)

-- |
-- >>>  P [1,2] == P [1,2]
-- True

-- |
-- >>> fromInteger 0 == (zeroP :: DensePoly Int)
-- True

-- |
-- >>>  P [0,1] == P [1,0]
-- False

-- | Degree examples
-- >>> degree (zeroP :: DensePoly Int)
-- -1
-- >>> degree (constP 1 :: DensePoly Int)
-- 0
