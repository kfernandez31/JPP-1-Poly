module Modulo(IntModulo) where
import Test.QuickCheck (Arbitrary (arbitrary), Positive (Positive), Positive)
import qualified Test.QuickCheck.Gen

newtype IntModulo = IntM Int deriving Show

m = 10

instance Num IntModulo where
  (IntM a) + (IntM b) = IntM (mod (a + b) m)
  (IntM a) * (IntM b) = IntM (mod (a * b) m)
  abs x = x
  signum x = IntM 1
  fromInteger x = IntM(mod (fromInteger x) m)
  negate (IntM x) = IntM (mod (m - x) m)

instance Eq IntModulo where
  (IntM a) == (IntM b) = a == b
    
instance Arbitrary IntModulo where  
    arbitrary = do
        Positive x <- arbitrary
        return $ IntM (mod x m)

