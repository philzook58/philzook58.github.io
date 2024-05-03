
import Data.Maybe

data LogExprB = AndB LogExprB LogExprB | OrB LogExprB LogExprB | NotB LogExprB | VarB String

data LogExpr = And LogExpr LogExpr | Or LogExpr LogExpr | Not LogExpr | Implies LogExpr LogExpr

compile :: LogExpr -> LogExprB
compile = undefined


-- Could use Reader Monad for env
-- Maybe Monad for the possibility of failing lookup
-- and a Foldable
runLog :: [(String, Bool)] ->  LogExprB -> Bool
runLog env (AndB a b) =  (runLog env a) && (runLog env b)
runLog env (OrB a b) =  (runLog env a) || (runLog env b)
runLog env (NotB a) =  not (runLog env a)
runLog env (VarB name) = fromJust $ lookup name env


nextenv ((name, True) : rest) carry =
nextenv ((name, False) : rest) carry = 
nextenv [] True = []
nextenv [] False = []

allenvs :: [String] -> [[(String,Bool)]] 
allenvs varlist =

