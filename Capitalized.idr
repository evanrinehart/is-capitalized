module Capitalized

%access export
%default total

ordN : Char -> Nat
ordN c = cast (ord c)

-- n between a and b defined as: a <= n AND n <= b
data Between : Nat -> Nat -> Nat -> Type where
  MkBetween : LTE a n -> LTE n b -> Between a b n

isBetween : (a, b, n : Nat) -> Dec (Between a b n)
isBetween a b n = case isLTE a n of
  Yes prf1 => case isLTE n b of
    Yes prf2 => Yes (MkBetween prf1 prf2)
    No contra => No (\(MkBetween bad1 bad2) => contra bad2)
  No contra => No (\(MkBetween bad1 bad2) => contra bad1)

-- c upper case defined as: ascii encoding between 65 and 90
data IsUpper : Char -> Type where
  CapitalAscii : (c : Char) -> Between 65 90 (ordN c) -> IsUpper c

isUpper' : (c : Char) -> Dec (IsUpper c)
isUpper' c = case isBetween 65 90 (ordN c) of
  Yes prf   => Yes (CapitalAscii c prf)
  No contra => No (\(CapitalAscii _ bad) => contra bad)

-- String is a primitive type, so it gets momentarily hairy
-- c begins s defined as: exists a string `rest' such that s = strCons c rest
data Begins : Char -> String -> Type where
  MkBegins : (c : Char) -> (rest : String) -> Begins c (strCons c rest)

-- type checker refuses to let us prove this normally
postulate beginsNonEmpty : Begins c "" -> Void

-- if c1 begins s and c2 begins s then c1 = c2
-- Also not provable, but use believe_me to produce Refl:c1=c2 anyway.
beginsUnique : Begins c1 s -> Begins c2 s -> c1 = c2
beginsUnique {c1} {c2} _ _ = believe_me (Refl {A=Char} {x=c1})

isNonEmpty : (s : String) -> Dec (c:Char ** Begins c s)
isNonEmpty s with (strM s)
  isNonEmpty ""             | StrNil = No (\(_ ** beginsEmpty) => beginsNonEmpty beginsEmpty)
  isNonEmpty (strCons x xs) | (StrCons x xs) = Yes (x ** MkBegins x xs)

isNonEmptyNoWith : (s : String) -> Dec (c:Char ** Begins c s)
isNonEmptyNoWith s = case strM s of
  StrNil       => No (\(_  ** beginsEmpty) => beginsNonEmpty beginsEmpty)
  StrCons x xs => Yes (x ** MkBegins x xs)

-- "s capitalized" is defined as: c begins s and c is uppercase, for some c
data IsCapitalized : String -> Type where
  MkIsCapitalized : Begins c s -> IsUpper c -> IsCapitalized s

isCapitalized : (s : String) -> Dec (IsCapitalized s)
isCapitalized s = case isNonEmpty s of
  Yes (c ** beginsCS) => case isUpper' c of
    Yes cUpper   => Yes (MkIsCapitalized beginsCS cUpper)
    No cNotUpper => No (\(MkIsCapitalized beginsDS dUpper) =>
      -- Proof that s is not capitalized, spelled out:
      -- We know that c begins s (beginsCS)
      -- We know that c uppercase would be a contradiction (cNotUpper)
      -- Assuming s *were* capitalized...
      --   i.e. exists d:Char such that d begins s and d is upper
      --   c = d (beginsUnique)
      --   Therefore c is upper too (dUpper)
      --   Which contradicts (cNotUpper)
      -- 
      -- Alternatively: if c begins s and c is not uppercase, s is not capitalized
      let Refl = beginsUnique beginsCS beginsDS in cNotUpper dUpper)
  -- Proof that empty string is not capitalized:
  -- Assuming it were capitalized, then c begins s for some c.
  -- Which contradicts the fact s is known to have no beginning.
  No noBegin => No (\(MkIsCapitalized {c} be upper) => noBegin (c ** be))
