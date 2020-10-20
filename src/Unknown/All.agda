{-# OPTIONS --without-K --prop --rewriting #-}
module Unknown.All where

open import Agda.Primitive public
open import Unknown.Interface public

open import Unknown.Core
open import Unknown.Into
open import Unknown.Rel
open import Unknown.IntoRel

import Poset as P

module _ (fp : familyPack {lzero} {lzero})
         {{PB : ∀ {c} → P.Poset₀ (familyPack.B fp c)}}
         (✠B : ∀ {c} → P.Initial (familyPack.B fp c))
         where


  unknownStructure : BuildUnknown fp ✠B
  unknownStructure = record
    { unknownType = 𝕦nknown fp ✠B
    ; unknown-hSet = unknown-hSet fp ✠B
    ; ✠unk = ✠unk fp ✠B
    ; ?unk = ?unk fp ✠B
    ; intoDistr = λ {cx} → IntoDistr.intoUnkε-Distr fp ✠B cx
    ; intoDistr-down✠ = λ {cx} d {u} → IntoDistr.from-unknown-✠u fp ✠B cx d u
    ; intoCompat = λ {cx} {cy} dX dY dXY →
        IntoDistrDownCompatEq.compat fp ✠B cx cy dX dY (dXY .cxy) (dXY .distr) (dXY .down✠) (dXY .distr-eq)  }
    where
      open intoDistrData hiding (down✠)
      open intoDistrCompat
