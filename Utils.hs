module Utils where
import Representation
import Data.List(dropWhileEnd)

mapfst :: (a -> a') -> (a, b) -> (a', b)
mapfst f (a, b) = (f a, b)
mapsnd :: (b -> b') -> (a, b) -> (a, b')
mapsnd f (a, b) = (a, f b)

trd :: (a, b, c) -> c
trd (_, _, c) = c

toCanonicalDP :: (Eq a, Num a) => DensePoly a -> DensePoly a
toCanonicalDP = P . dropWhileEnd (== 0) . unP
