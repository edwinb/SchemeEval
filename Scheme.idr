module Scheme

export
data ForeignObj : Type where [external]

%foreign "scheme:blodwen-eval-scheme"
prim__evalScheme : String -> ForeignObj

%foreign "scheme:blodwen-eval-okay"
prim__evalOkay : ForeignObj -> Int

%foreign "scheme:blodwen-get-eval-result"
prim__evalResult : ForeignObj -> ForeignObj

%foreign "scheme:blodwen-debug-scheme"
prim__debugScheme : ForeignObj -> PrimIO ()

%foreign "scheme:blodwen-is-number"
prim_isNumber : ForeignObj -> Int

%foreign "scheme:blodwen-is-integer"
prim_isInteger : ForeignObj -> Int

%foreign "scheme:blodwen-is-float"
prim_isFloat : ForeignObj -> Int

%foreign "scheme:blodwen-is-char"
prim_isChar : ForeignObj -> Int

%foreign "scheme:blodwen-is-string"
prim_isString : ForeignObj -> Int

%foreign "scheme:blodwen-is-procedure"
prim_isProcedure : ForeignObj -> Int

%foreign "scheme:blodwen-is-symbol"
prim_isSymbol : ForeignObj -> Int

%foreign "scheme:blodwen-is-nil"
prim_isNil : ForeignObj -> Int

%foreign "scheme:blodwen-is-pair"
prim_isPair : ForeignObj -> Int

%foreign "scheme:blodwen-is-vector"
prim_isVector : ForeignObj -> Int

export
isNumber : ForeignObj -> Bool
isNumber x = prim_isNumber x == 1

export
isInteger : ForeignObj -> Bool
isInteger x = prim_isInteger x == 1

export
isFloat : ForeignObj -> Bool
isFloat x = prim_isFloat x == 1

export
isChar : ForeignObj -> Bool
isChar x = prim_isChar x == 1

export
isString : ForeignObj -> Bool
isString x = prim_isString x == 1

export
isProcedure : ForeignObj -> Bool
isProcedure x = prim_isProcedure x == 1

export
isSymbol : ForeignObj -> Bool
isSymbol x = prim_isSymbol x == 1

export
isNil : ForeignObj -> Bool
isNil x = prim_isNil x == 1

export
isPair : ForeignObj -> Bool
isPair x = prim_isPair x == 1

export
isVector : ForeignObj -> Bool
isVector x = prim_isVector x == 1

-- The below are all 'unsafe' because they rely on having done the relevant
-- check above first
%foreign "scheme:blodwen-id"
export
unsafeGetInteger : ForeignObj -> Integer

%foreign "scheme:blodwen-id"
export
unsafeGetString : ForeignObj -> String

%foreign "scheme:blodwen-id"
export
unsafeGetFloat : ForeignObj -> Double

%foreign "scheme:blodwen-id"
export
unsafeGetChar : ForeignObj -> Char

%foreign "scheme:car"
export
unsafeFst : ForeignObj -> ForeignObj

%foreign "scheme:cdr"
export
unsafeSnd : ForeignObj -> ForeignObj

%foreign "scheme:blodwen-apply"
export
unsafeApply : ForeignObj -> ForeignObj -> ForeignObj

%foreign "scheme:blodwen-vector-ref"
export
unsafeVectorRef : ForeignObj -> Integer -> ForeignObj

%foreign "scheme:blodwen-vector-length"
export
unsafeVectorLength : ForeignObj -> Integer

%foreign "scheme:blodwen-make-symbol"
export
makeSymbol : String -> ForeignObj

%foreign "scheme:blodwen-read-symbol"
export
unsafeReadSymbol : ForeignObj -> String

export
evalScheme : String -> Maybe ForeignObj
evalScheme exp
    = let obj = prim__evalScheme exp in
          if prim__evalOkay obj == 1
             then Just (prim__evalResult obj)
             else Nothing

export
debugScheme : ForeignObj -> IO ()
debugScheme obj = primIO $ prim__debugScheme obj

public export
data SchemeObj : Type where
     Null : SchemeObj
     Cons : ForeignObj -> ForeignObj -> SchemeObj
     IntegerVal : Integer -> SchemeObj
     FloatVal : Double -> SchemeObj
     StringVal : String -> SchemeObj
     CharVal : Char -> SchemeObj
     Symbol : String -> SchemeObj
     Procedure : ForeignObj -> SchemeObj
     Vector : List ForeignObj -> SchemeObj

export
decodeObj : ForeignObj -> SchemeObj
decodeObj obj
    = if isNil obj then Null
      else if isPair obj then Cons (unsafeFst obj) (unsafeSnd obj)
      else if isInteger obj then IntegerVal (unsafeGetInteger obj)
      else if isFloat obj then FloatVal (unsafeGetFloat obj)
      else if isString obj then StringVal (unsafeGetString obj)
      else if isChar obj then CharVal (unsafeGetChar obj)
      else if isSymbol obj then Symbol (unsafeReadSymbol obj)
      else if isProcedure obj then Procedure obj
      else if isVector obj then Vector (readVector (unsafeVectorLength obj) 0 obj)
      else Null
  where
    readVector : Integer -> Integer -> ForeignObj -> List ForeignObj
    readVector len i obj
        = if len == i
             then []
             else unsafeVectorRef obj i :: readVector len (i + 1) obj
