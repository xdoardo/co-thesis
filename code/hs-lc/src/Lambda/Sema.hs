module Lambda.Sema (eval) where

import Monad.Delay (Delay(..))
import Lambda.Syntax (Value(..), Term(..), Env, elookup)

eval :: Term -> Env -> Delay (Maybe Value)
eval (Const c) _ = Now (Just (VConst c))
eval (Var v) e = Now (elookup e v)
eval (Abs t) e = Now (Just (VAbs t e))
eval (App t u) e = eval t e >>= \f -> eval u e >>= \v -> apply f v

apply :: (Maybe Value) -> (Maybe Value) -> Delay (Maybe Value)
apply (Nothing) _ = Now Nothing
apply  _ (Nothing) = Now Nothing
apply (Just (VConst _)) _ = Now Nothing
apply (Just (VAbs t e)) (Just u) =  Later (beta t e u)

beta :: Term -> Env -> Value -> Delay (Maybe Value)
beta t e p = eval t (mappend [p] e)
