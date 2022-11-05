import Lambda.Sema (eval)
import Lambda.Syntax (Term(..), Value(..))
import Monad.Delay (Delay(..))
import Test.QuickCheck

prop_Consts :: Int -> Bool 
prop_Consts i = (eval (Const i) []) == (Now (Just (VConst i)))


main :: IO ()
main = do
  quickCheck prop_Consts
  putStrLn "Done"
