module Path

import Data.Vect

public export
data Tree : (treeType : Type) -> Type where
  Branch : (x : treeType)
        -> (ts : Vect (S n) (Tree treeType))
        -> Tree treeType
  Leaf : treeType
        -> Tree treeType

public export
data ElemPath : (c : Tree treeType) -> Type where
  EndPath  : (ys : treeType) -> ElemPath (Leaf ys)
  MkPath : (c : treeType) -> ElemPath (i `index` trees)  -> ElemPath (Branch c trees)

-- exampleTree : Tree Char 
-- exampleTree = Branch 'q' [Leaf 'b']

-- pathExampleTree : ElemPath {treeType=Char} Path.exampleTree
-- pathExampleTree = MkPath {i=0} 'q' (EndPath 'b')

-- public export
-- head : Tree a -> a
-- head (Branch x n ts) = x

-- public export
-- countChildren : Tree a -> Nat
-- countChildren (Branch x n ts) = n

-- public export
-- data Path : (c : Tree a) -> Type where
--   Nil : Path c
--   (::) : (i : Fin n)
--       -> Path (i `index` trees)
--       -> Path (Branch a n trees)

-- mutual
--   data Path' : (c : Tree a) -> Type where
--     EmptyPath' : Path' c
--     MkPath' : (b : a) ->  calculateEmpty trees -> Path' (Branch b n trees) 

--   calculateEmpty : Vect n (Tree a) -> Type
--   calculateEmpty [] = Path' c
--   calculateEmpty tree@(x :: xs) = Path' (i `index` tree)

-- joinTree : (iTree : Tree a)
--         -> (rTree : Tree a)
--         -> (path : Path rTree)
--         -> Tree a
-- joinTree iTree tree [] = iTree
-- joinTree iTree (Branch x n ts) (i :: is)
--   = Branch x n (replaceAt i sub ts)
--   where
--     sub = joinTree iTree (index i ts) is

-- public export
-- subTrees : (t : Tree a) -> Vect (countChildren t) (Tree a)
-- subTrees (Branch x n ts) = ts

-- public export
-- total
-- treedex : (t : Tree a) -> Path t -> a
-- treedex (Branch x _ ts) [] = x
-- treedex (Branch x _ ts) (i :: is) = treedex (i `index` ts) is
-- -- treedex (Branch x (S k) (t :: ts)) (FZ :: is) = treedex t is
-- -- treedex (Branch x (S k) (t :: ts)) (FS i :: is) = treedex (Branch x k ts) (i :: is)

-- public export
-- treedexNilHead : (tree : Tree a) -> (treedex tree [] = head tree)
-- treedexNilHead (Branch x n ts) = Refl

-- public export
-- headPreservedByJoinTree : {tree : Tree a}
--                        -> {path : Path tree}
--                        -> (prf : treedex tree path = head iTree)
--                        -> head tree = head (joinTree iTree tree path)
-- headPreservedByJoinTree {tree = (Branch x n ts)} {path = []} prf = prf
-- headPreservedByJoinTree {tree = (Branch x n ts)} {path = (i :: is)} prf = Refl
