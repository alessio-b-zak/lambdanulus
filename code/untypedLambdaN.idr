import Data.Vect
import Path

Name : Type
Name = String

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
--Need to sort out the exact semantics of the expression language
data BaseExpr : (names : Vect n Name) -> Type where
  Var : (n : Name) -> BaseExpr [n]
  Const : BaseExpr []
  OtherApp : BaseExpr fstNames -> BaseExpr sndNames -> BaseExpr (fstNames ++ sndNamets)

mutual
  data NExpr : (names : Vect n Name) -> Type where
    Lam : (capturing_set : Vect n Name) -> BaseExpr capturing_set -> NExpr capturing_set
    App : (n : NExpr names) -> PathListTree (nTree n) -> (m : NExpr names') -> NExpr (names ++ names')
   
  calcNat : {len : Nat} -> {namings : Vect len Name} -> NExpr namings -> Nat
  calcNat {len} (Lam namings x) = len
  calcNat (App y z m) = calcNat y

--  --This function needs to deconstruct a NExpr into a tree of variable names nested by thingy
--  --Now I wish I had used DeBrujin Indices.
  nTree : (nexpr : NExpr someNames) -> (Vect (calcNat nexpr) (Tree Name))
  nTree (Lam someNames x) = map (Leaf) someNames
  nTree (App y (IsPathOf {i} p) second) = let initialRoots = nTree y 
                                              newPath = elemPathToPath p
                                              elemAtI = i `index` initialRoots 
                                              newElem = substituteTree elemAtI newPath (nTree second) in
                                              replaceAt i newElem initialRoots 



sf : NExpr ["x", "y"]
sf = App (Lam ["x", "y"] (OtherApp (Var "x") (Var "y"))) (IsPathOf {i=0} (EndPath  "x")) (Lam [] (Const))

                                              --updateAt i (\roots => substituteTree roots newPath (nTree second)) initialRoots
                                               -- newLeaves = (nTree second) in
--substituteTree (i `index` roots) d (nTree p)



