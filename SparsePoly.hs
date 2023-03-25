module SparsePoly(fromDP, toDP, qrP) where
import PolyClass
import Representation

toCanonicalSP :: (Eq a, Num a) => SparsePoly a -> SparsePoly a
toCanonicalSP = S . filter ((/= 0) . snd) . unS

first :: (a -> a') -> (a, b) -> (a', b)
first f (a, b) = (f a, b)
second :: (b -> b') -> (a, b) -> (a, b')
second f (a, b) = (a, f b)

trd :: (a, b, c) -> c
trd (_, _, c) = c

-- | fromDP example
-- >>> fromDP sampleDP
-- S {unS = [(3,1),(0,-1)]}
fromDP :: (Eq a, Num a) => DensePoly a -> SparsePoly a
fromDP = S . reverse . filter ((/=0) . snd) . zip [0..] . unP

toDP :: (Eq a, Num a) => SparsePoly a -> DensePoly a
toDP = P . reverse . foldr go [] . unS where
    go (e, c) acc = c:(replicate (e - length acc) 0) ++ acc

instance Functor SparsePoly where
    fmap f = S . map (second f) . unS 

instance Polynomial SparsePoly where
    zeroP                 = S []
    constP c              = if c == 0 then zeroP else S [(0,c)]
    varP                  = S [(1,1)]
    evalP  p x            = trd $ foldr (go) (-1, 0, 0) $ unS p where
        go (e, c) (e', x', acc) = (e, x'', acc + c * x'') where
            x'' = x' * x^(e - e') 
    shiftP n              = S . map (first (+n)) . unS
    degree (S ((e, _):_)) = e
    degree (S [])         = -1

instance (Eq a, Num a) => Num (SparsePoly a) where
    abs                        = undefined
    signum                     = undefined 
    negate                     = (negate <$>)
    fromInteger                = constP . fromInteger
    (+) p1              (S []) = p1
    (+) (S [])          p2     = p2
    (+) p1@(S ((e1,c1):p1')) p2@(S ((e2,c2):p2'))
        | e1 > e2   = S $ (e1,c1):(unS $ p1'' + p2)
        | e1 < e2   = S $ (e2,c2):(unS $ p2'' + p1)
        | otherwise = 
            let c = c1 + c2 in 
            if c == 0 then p1'' + p2''
            else S $ (e1,c):(unS $ p1'' + p2'')
        where (p1'', p2'') = (S p1', S p2')
    (*) p q                        = toCanonicalSP $ go p q where
        go (S [])          _ = zeroP
        go (S ((e, c):p')) q = 
            shiftP e ((*c) <$> q) + (go (S p') q)

instance (Eq a, Num a) => Eq (SparsePoly a) where
    (==) p q = nullP (p-q)

-- qrP s t | not(nullP t) = (q, r) iff s == q*t + r && degree r < degree t
qrP :: (Eq a, Fractional a) => SparsePoly a -> SparsePoly a -> (SparsePoly a, SparsePoly a)
qrP s (S [])             = error "Division by zero"
qrP s t@(S ((te, tc):_)) = go zeroP s where 
    go q (S [])          = (q, zeroP)
    go q r@(S((re, rc):r'))
        | re < te   = (q, r) 
        | otherwise = 
            let s = shiftP (re - te) (constP (rc / tc)) in
            go (q + s) (r - s * t)

-- | Division example
-- >>> let x = varP in qrP (x^2 - 1) (x - 1) == ((x + 1), 0)
-- True
