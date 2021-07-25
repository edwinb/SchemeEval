module ToyLang

import Data.SortedMap
import Data.IORef

public export
Name : Type
Name = String

public export
data IsVar : Name -> Nat -> List Name -> Type where
     First : IsVar n Z (n :: ns)
     Later : IsVar n i ns -> IsVar n (S i) (m :: ns)

public export
data Binder : Type -> Type where
     Lam : Binder t
     Let : t -> Binder t

public export
data PrimOp = Plus | Minus | Times | Divide

public export
data Term : List Name -> Type where
     Local : (idx : Nat) -> (0 _ : IsVar n idx vars) -> Term vars
     Global : Name -> Term vars

     Bind : (x : Name) -> Binder (Term vars) -> Term (x :: vars) -> Term vars
     App : Term vars -> Term vars -> Term vars

     Pair : Term vars -> Term vars -> Term vars
     Null : Term vars

     Val : Integer -> Term vars
     Op : PrimOp ->
          Term vars -> Term vars -> Term vars

export
Show PrimOp where
  show Plus = "+"
  show Minus = "-"
  show Times = "*"
  show Divide = "/"

export
{vars : _} -> Show (Term vars) where
  show (Local idx p) = getName vars p ++ "[" ++ show idx ++ "]"
    where
      getName : {idx : Nat} ->
                (vs : List Name) -> (0 _ : IsVar n idx vs) -> String
      getName (x :: xs) First = x
      getName (x :: xs) (Later p) = getName xs p
  show (Global n) = n
  show (Bind x Lam sc) = "\\ " ++ x ++ " => " ++ show sc
  show (Bind x (Let v) sc) = "let " ++ x ++ " = " ++ show v ++ " in " ++ show sc
  show (App f a) = "(" ++ show f ++ " " ++ show a ++ ")"
  show (Pair x y) = "(" ++ show x ++ ", " ++ show y ++ ")"
  show Null = "[]"
  show (Val x) = show x
  show (Op op x y) = "(" ++ show x ++ " " ++ show op ++ " " ++ show y ++ ")"

public export
data CaseTree : List Name -> Type where
     IfNull : {idx : Nat} -> (0 _ : IsVar n idx vars) ->
              CaseTree vars -> CaseTree (x :: vars) -> CaseTree vars
     IfZero : {idx : Nat} -> (0 _ : IsVar n idx vars) ->
              CaseTree vars -> CaseTree vars -> CaseTree vars
     STerm : Term vars -> CaseTree vars

public export
data Env : (tm : List Name -> Type) -> List Name -> Type where
     Nil : Env tm []
     (::) : Binder (tm vars) -> Env tm vars -> Env tm (x :: vars)

public export
Compiled : Type
Compiled = ()

public export
record Def where
  constructor MkDef
  args : List Name
  term : CaseTree args
  compiled : Maybe String

public export
Defs : Type
Defs = SortedMap Name Def

export
data Ref : (l : label) -> Type -> Type where
     [search l]
     MkRef : IORef a -> Ref x a

export
newRef : (x : label) -> t -> IO (Ref x t)
newRef x val
    = do ref <- newIORef val
         pure (MkRef ref)

export %inline
get : (x : label) -> {auto ref : Ref x a} -> IO a
get x {ref = MkRef io} = readIORef io

export %inline
put : (x : label) -> {auto ref : Ref x a} -> a -> IO ()
put x {ref = MkRef io} val = writeIORef io val

public export
apply : Term vars -> List (Term vars) -> Term vars
apply tm [] = tm
apply f (a :: as) = apply (App f a) as

export
zero : Term vars
zero = Null

export
suc : Term vars -> Term vars
suc t = Pair (Val 1) t

export
plusfn : CaseTree ["x", "y"]
plusfn
    = IfNull {x="k"}
             First
             (STerm (Local _ (Later First)))
             (STerm (suc (apply (Global "plus")
                                [Local _ First, Local _ (Later (Later First))])))
      
export
natToIntfn : CaseTree ["x"]
natToIntfn
    = IfNull {x="k"}
             First
             (STerm (Val 0))
             (STerm (Op Plus (Val 1) 
                        (apply (Global "natToInt") [Local _ First])))

export
intToNatfn : CaseTree ["x"]
intToNatfn
    = IfZero First 
             (STerm zero)
             (STerm (suc (apply (Global "intToNat") 
                                [Op Minus (Local _ First) (Val 1)])))

public export
defs : Defs
defs = insert "plus" (MkDef _ plusfn Nothing) $
       empty
