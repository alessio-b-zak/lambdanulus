import Data.List
import Path

Name : Type
Name = String

LamPath : Type
LamPath = List Name

--constructNameTree : NExpr 

data Last : a -> List a -> Type where
  LHere  : Last a (a::[])
  LThere : Last a xs -> Last a (x::xs)

x : Last 3 [1,2,3]
x = LThere (LThere (LHere))


--removes all instances of the first list from the second
remove : Eq a => List a -> List a -> List a
remove = foldl (flip delete)

--should use sets instead of lists but I can't be bothered
--to download the package. Use unique names nerds.
data BaseExpr : (names : List Name) -> Type where
  Var : (n : Name) -> BaseExpr [n]
  Add : BaseExpr fstNames -> BaseExpr sndNames -> BaseExpr (fstNames ++ sndNamets)

mutual
 data NExpr : (names : List Name) -> Type where

   nameTree :  NExpr dames ->  Tree a

   Lam : (capturing_set : List Name) -> NExpr nxrp -> NExpr (remove nxrp capturing_set)
   App : (n : NExpr names) -> ElemPath (nameTree  n)-> (m : NExpr names') -> NExpr (names ++ names')

