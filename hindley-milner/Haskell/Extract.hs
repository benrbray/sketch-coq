module Extract where

import qualified Prelude

data Nat =
   O
 | S Nat

isEven :: Nat -> Prelude.Bool
isEven n =
  case n of {
   O -> Prelude.True;
   S n0 -> case n0 of {
            O -> Prelude.False;
            S p0 -> isEven p0}}

