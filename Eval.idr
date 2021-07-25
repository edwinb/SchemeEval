module Eval

import ToyLang
import Scheme

import System

data NS : Type where

nextName : Ref NS Integer => IO Integer
nextName
    = do n <- get NS
         put NS (n + 1)
         pure n

data SVar = Bound String | Free String

Show SVar where
  show (Bound x) = x
  show (Free x) = "'" ++ x

getName : SVar -> String
getName (Bound x) = x
getName (Free x) = x

data SchVars : List Name -> Type where
     Nil : SchVars []
     (::) : SVar -> SchVars ns -> SchVars (n :: ns)

Show (SchVars ns) where
  show xs = show (toList xs)
    where
      toList : forall ns . SchVars ns -> List String
      toList [] = []
      toList (Bound x :: xs) = x :: toList xs
      toList (Free x :: xs) = "'x" :: toList xs

getSchVar : {idx : _} -> (0 _ : IsVar n idx vars) -> SchVars vars -> String
getSchVar First (Bound x :: xs) = x
getSchVar First (Free x :: xs) = "'" ++ x
getSchVar (Later p) (x :: xs) = getSchVar p xs

-- Convert a term to a scheme string. There is probably a neater way than
-- building the string then passing it to scheme, but I don't yet know what
-- it is.
toScheme : Ref NS Integer =>
           SchVars vars -> Term vars -> IO String
toScheme vs (Local idx p) = pure (getSchVar p vs)
toScheme vs (Global n) = pure n
toScheme vs (Bind x Lam sc)
    = do i <- nextName
         let x' = x ++ "-" ++ show i
         pure $ "(lambda (" ++ x' ++ ") "
                ++ !(toScheme (Bound x' :: vs) sc) ++ ")"
toScheme vs (Bind x (Let y) sc)
    = do i <- nextName
         let x' = x ++ "-" ++ show i
         pure $ "(let [(" ++ x' ++ " " ++ !(toScheme vs y) ++ ")] " ++
                !(toScheme (Bound x' :: vs) sc) ++ ")"
toScheme vs (App f a)
    = pure $ "(" ++ !(toScheme vs f) ++ " " ++
                    !(toScheme vs a) ++ ")"
toScheme vs (Pair x y)
    = pure $ "(cons " ++ !(toScheme vs x) ++ " " ++
                         !(toScheme vs y) ++ ")"
toScheme vs Null = pure "'()"
toScheme vs (Val x) = pure (show x)
toScheme vs (Op f x y)
    = pure $ "(" ++ schOp f ++ " " ++
                    !(toScheme vs x) ++ " " ++
                    !(toScheme vs y) ++ ")"
  where
    schOp : PrimOp -> String
    schOp Plus = "fx+"
    schOp Minus = "fx-"
    schOp Times = "fx*"
    schOp Divide = "fx/"

-- Convert a top level case tree to a scheme definition, with the scheme
-- expression to return if evaluating the case tree is blocked.
toSchemeCase : Ref NS Integer =>
               String -> SchVars vars -> CaseTree vars -> IO String
toSchemeCase blocked vs (IfNull p t e)
    = do i <- nextName
         let enm = "arg-" ++ show i
         pure $ 
             "(if (null? " ++ (getSchVar p vs) ++ ") " ++
                !(toSchemeCase blocked vs t) ++ " " ++
                "(if (pair? " ++ (getSchVar p vs) ++ ") " ++
                   "(let [(" ++ enm ++ " (cdr " ++ getSchVar p vs ++ "))] " ++
                    !(toSchemeCase blocked (Bound enm :: vs) e) ++ ") " ++
                blocked ++ "))"
toSchemeCase blocked vs (IfZero p t e)
    = pure $ "(if (number? " ++ (getSchVar p vs) ++ ") " ++
             "(if (eq? 0 " ++ (getSchVar p vs) ++ ") " ++
                !(toSchemeCase blocked vs t) ++ " " ++
                !(toSchemeCase blocked vs e) ++ ")" ++
                blocked ++ ")"     
toSchemeCase blocked vs (STerm t) = toScheme vs t

compileDef : Name -> (args : _) -> CaseTree args -> IO ()
compileDef n args tree
    = do i <- newRef NS 0
         argvs <- mkArgs args
         body <- toSchemeCase (mkBlocked argvs) argvs tree
         let def = "(define " ++ n ++ " " ++ bindArgs argvs body ++ ")"
         let Just _ = evalScheme def
            | Nothing => putStrLn "Oops"
         putStrLn def
         let Just res = evalScheme n
            | Nothing => putStrLn "Oops"
         debugScheme res
  where
    bindArgs : SchVars ns -> String -> String
    bindArgs [] body = body
    bindArgs (x :: xs) body
        = "(lambda (" ++ show x ++ ") " ++ bindArgs xs body ++ ")"

    showVars : SchVars ns -> String
    showVars [] = ""
    showVars [x] = show x
    showVars (x :: xs) = show x ++ " " ++ showVars xs

    mkBlocked : SchVars ns -> String
    mkBlocked argvs
        = "(vector " ++ show n ++ " " ++
              show (length args) ++ " " ++
              showVars argvs ++ ")"

    mkArgs : Ref NS Integer =>
             (ns : List Name) -> IO (SchVars ns)
    mkArgs [] = pure []
    mkArgs (x :: xs)
        = do i <- nextName
             pure $ Bound (x ++ "-" ++ show i) :: !(mkArgs xs)

-- A value is a pair of the result of running the scheme, and the scheme
-- variable names. We use the scheme variable names to turn symbols (which
-- stand for free variables) into Locals again
data Value : List Name -> Type where
     MkValue : ForeignObj -> SchVars vars -> Value vars

eval : Env Term vars -> Term vars -> IO (Value vars)
eval env tm
    = do i <- newRef NS 0
         (bind, schEnv) <- mkEnv env id
         tm' <- toScheme schEnv tm
         let Just res = evalScheme (bind tm')
           | Nothing => believe_me {a=IO ()} $ do putStrLn "Oops"
                                                  exitWith (ExitFailure 1)
                -- ^ if everything worked out, this can't happen!
                -- Place your bets...
         pure (MkValue res schEnv)
  where
    mkEnv : forall vars . Ref NS Integer =>
            Env Term vars ->
            (String -> String) ->
            IO (String -> String, SchVars vars)
    mkEnv [] k = pure (k, [])
    mkEnv (Lam :: es) k
        = do i <- nextName
             (bind, vs) <- mkEnv es k
             pure (bind, Free ("free-" ++ show i) :: vs)
    mkEnv (Let v :: es) k
        = do i <- nextName
             (bind, vs) <- mkEnv es k
             v' <- toScheme vs v
             let n = "let-var-" ++ show i
             pure (\x => "(let [(" ++ n ++ " " ++ v' ++ ")] " ++
                               bind x ++ ")",
                               Bound n :: vs)

quote' : Ref NS Integer =>
         SchVars (outer ++ vars) -> ForeignObj -> IO (Term (outer ++ vars))
quote' vs val
    = case decodeObj val of
           Null => pure Null
           Cons x y => pure (Pair !(quote' vs x) !(quote' vs y))
           IntegerVal x => pure (Val x)
           Symbol x => pure (findName vs x)
           Procedure x =>
               do i <- nextName
                  let n = "ref-" ++ show i
                  let sc = unsafeApply val (makeSymbol n)
                  sc' <- quote' {outer = n :: outer} (Bound n :: vs) sc
                  pure (Bind n Lam sc')
           Vector (fn_in :: arity_in :: args) =>
               do let StringVal fn = decodeObj fn_in
                        | _ => pure Null
                  let IntegerVal arity = decodeObj arity_in
                        | _ => pure Null
                  args' <- traverse (quote' vs) args
                  pure (apply (Global fn) args')
           _ => pure Null
  where
    findName : forall vars . SchVars vars -> Name -> Term vars
    findName [] n = Global n
    findName (x :: xs) n
        = if getName x == n
             then Local _ First
             else let Local _ p = findName xs n
                         | _ => Global n in
                      Local _ (Later p)

quote : Value vars -> IO (Term vars)
quote (MkValue val schEnv)
    = do i <- newRef NS 0
         quote' {outer = []} schEnv val

debugVal : Value vars -> IO ()
debugVal (MkValue val sch) = debugScheme val

test : IO ()
test = do -- Make a scheme function called 'plus' that implements the one
          -- in our little language
          compileDef "plus" _ plusfn

          -- and a couple of others
          compileDef "natToInt" _ natToIntfn
          compileDef "intToNat" _ intToNatfn

          -- Now lets' try evaluating it.
          -- First just dump the scheme values
          debugVal !(eval [] (suc (suc zero)))
          debugVal !(eval [] (apply (Global "plus") [suc (suc zero), suc (suc zero)]))
          debugVal !(eval {vars = ["var"]}
                        [Lam] (apply (Global "plus")
                                    [suc (suc zero),
                                     suc (suc (Local _ First))]))
          debugVal !(eval {vars = ["var"]}
                        [Let (suc zero)] (apply (Global "plus")
                                    [suc (suc zero),
                                     suc (suc (Local _ First))]))
          
          -- Now try quoting the scheme values with free variables back as
          -- terms
          putStrLn "Quoting:\n--------"

          val <- eval [] (apply (Global "plus") [suc (suc zero), suc (suc zero)])
          printLn !(quote val)

          -- Try 'plus' but blocked on the second argument
          lamval <- eval [] (Bind "var" Lam
                               (apply (Global "plus")
                                    [suc (suc zero),
                                     suc (suc (Local _ First))]))
          printLn !(quote lamval)

          -- Try 'plus' but blocked on the first argument
          lamval <- eval [] (Bind "var" Lam
                               (apply (Global "plus")
                                    [suc (suc (Local _ First)),
                                     suc (suc zero)]))
          printLn !(quote lamval)

          -- And blocked on both
          lamsval <- eval [] (Bind "x" Lam
                               (Bind "y" Lam
                                 (apply (Global "plus")
                                      [suc (suc (Local _ First)),
                                       suc (suc (Local _ (Later First)))])))
          printLn !(quote lamsval)

          -- Try it in an environment, rather than under lambdas
          envval <- eval {vars = ["x", "y"]}
                         [Let (suc zero), Lam] 
                         (apply (Global "plus")
                              [suc (suc (Local _ First)),
                               suc (suc (Local _ (Later First)))])
          printLn !(quote envval)

          -- And some nat/int conversions to try something bigger
          val <- eval [] (apply (Global "natToInt")
                             [apply (Global "plus")
                                    [apply (Global "intToNat") [Val 400000],
                                     apply (Global "intToNat") [Val 540000]]])
          printLn !(quote val)
