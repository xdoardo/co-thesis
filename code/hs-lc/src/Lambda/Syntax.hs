module Lambda.Syntax (Term(..), Env, Value(..), elookup) where

data Term = Const Int | Var Int | Abs Term | App Term Term  deriving ( Show , Eq )

type Env = [Value]

data Value = VConst Int | VAbs Term Env deriving ( Show , Eq )

elookup :: Env -> Int -> Maybe Value
elookup e i = if length e >= i then Just (e!!i) else Nothing
