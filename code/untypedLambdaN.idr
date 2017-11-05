import Data.Vect

Name : Type
Name = String

public export
data Tree : (treeType : Type) -> Type where
  Branch : (x : treeType)
        -> (ts : Vect (S n) (Tree treeType))
        -> Tree treeType
  Leaf : treeType
        -> Tree treeType

public export
data Path : (tree : Tree a) -> Type where
  Nil : Path (Leaf b)
  (::) : (i : Fin (S b)) -> (Path (i `index` tees)) -> Path (Branch a tees)

public export
data ElemPath : (c : Tree treeType) -> Type where
  EndPath  : (ys : treeType) -> ElemPath (Leaf ys)
  MkPath : (c : treeType) -> ElemPath (i `index` trees)  -> ElemPath (Branch c trees)

public export
data PathListTree : (trees : Vect n (Tree a)) -> Type where
  IsPathOf : (treePath : ElemPath (i `index` trees)) -> PathListTree trees

public export
substituteTree : (receiveTr : Tree a) -> Path receiveTr -> Vect n (Tree a) -> Tree a
substituteTree (Branch x ts) (i :: y) pushTr = substituteTree (i `index` ts) y pushTr
substituteTree (Leaf x) [] [] = Leaf x
substituteTree (Leaf x) [] a@(y :: xs) = Branch x a

public export
elemPathToPath : ElemPath tree -> Path tree
elemPathToPath (EndPath ys) = Nil
elemPathToPath (MkPath {i} c x) = i :: elemPathToPath x 


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



syntax [bexpr1] "$$" [bexpr2] = OtherApp bexpr1 bexpr2
syntax [expr1] "@"[path] [expr2] = App expr1 path expr2
syntax "/"[capturing_set] "->" "{"[base_expr]"}" = Lam capturing_set base_expr
syntax "v"[expr] = Var expr
syntax "c" = /[] -> {Const}
syntax [end]";"= EndPath end
syntax  [p1] [d] "," [p2] = MkPath {i=d} p1 (p2)
syntax "q" [d] [path] = IsPathOf {i=d} (path)

sf : NExpr ["x", "y"]
sf = App (Lam ["x", "y"] (OtherApp (Var "x") (Var "y"))) (IsPathOf {i=0} (EndPath  "x")) (Lam [] (Const))

expr1 : NExpr ["x", "y"]
expr1 = /["x", "y"] -> {(v"x") $$  (v"y")}

expr2 : NExpr ["q"]
expr2 = /["q"] -> {v"q"}

expr3 : NExpr ["g", "h"]
expr3 = /["g", "h"] -> {(v"g") $$ (v"h")}

expr4 : NExpr ["z"]
expr4 = /["z"] -> {v"z"}

expr5 : NExpr ["t"]
expr5 = /["t"] -> {v"t"}

--Yes I know i had to implement the deBrujin version anyway I was too far gone leave me alone.

sf2 : NExpr ["x", "y", "q","z", "t"]
sf2 = ((expr1 @(q 1 ("y";)) expr2) @(q 1 ("y" 0 ,"q";)) expr4) -- @(q 1 ("y" 0, "q" 0, "z";)) expr5)


