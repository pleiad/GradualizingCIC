{-# OPTIONS --without-K --prop #-}
module MaybeProp where

open import prelude
open import Data.Maybe

just? : {X : Set} → Maybe X → Prop
just? (just _) = 𝟙
just? nothing = 𝟘

just?v : {X : Set} → (xopt : Maybe X) → just? xopt → X
just?v (just x) _ = x

