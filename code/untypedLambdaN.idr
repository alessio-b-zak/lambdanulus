import Data.Vect
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

--need to express the fact that the ElemPath is one of the multiple paths in the list. 
-- i.e. we have a List (Tree a) and we need to say that ElemPath is a path down one of those trees

--removes all instances of the first list from the second
remove : Eq a => List a -> List a -> List a
remove = foldl (flip delete)

--should use sets instead of lists but I can't be bothered
--to download the package. Use unique names nerds.
data BaseExpr : (names : Vect n Name) -> Type where
  Var : (n : Name) -> BaseExpr [n]
  Add : BaseExpr fstNames -> BaseExpr sndNames -> BaseExpr (fstNames ++ sndNamets)

mutual
  data NExpr : (names : Vect n Name) -> Type where
    Lam : (capturing_set : Vect n Name) -> BaseExpr capturing_set -> NExpr capturing_set
    App : (n : NExpr names) -> PathListTree (nTree n) -> (m : NExpr names') -> NExpr (names ++ names')
    
--  --This function needs to deconstruct a NExpr into a tree of variable names nested by thingy
--  --Now I wish I had used DeBrujin Indices.
  calculateN :{len : Nat} -> {namings : Vect len Name} -> NExpr namings -> Nat
  calculateN {len} (Lam namings x) =  len
  calculateN (App y z m) = calculateN y

  nTree : (nexpr : NExpr someNames) -> (Vect (calculateN nexpr) (Tree Name))
  nTree (Lam someNames x) = map (Leaf) someNames
  nTree (App y z m) = ?nTree_rhs_2
