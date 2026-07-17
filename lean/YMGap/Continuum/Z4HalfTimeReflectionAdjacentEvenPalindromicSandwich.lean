/-
# Constructive palindromic finite-kernel sandwich

The mixed predecessor/post-channel map is not itself a Gram pullback.  The
correct algebraic target is instead a common boundary coordinate: if the
fixed-interface kernel `T` is Gram and the lower and reflected-upper halves
use the same finite amplitude map `A`, then the complete contraction

    A T A^t

is again Gram.  This file proves that statement directly over `Q'`, with an
explicit transformed feature family and no square roots or choice.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedFaceCoefficientAttachment

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenPalindromicSandwich

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.SchurHadamardTransfer

local infix:50 " ≈ " => Q'.eqv

/-- Finite palindromic contraction through a common boundary index. -/
def finiteKernelSandwich
    (kernel : Nat → Nat → Q')
    (amplitude : Nat → Nat → Q') (boundaryCount : Nat)
    (left right : Nat) : Q' :=
  finSum (fun source =>
    finSum (fun target =>
      (amplitude left source * amplitude right target) *
        kernel source target) boundaryCount) boundaryCount

/-- The feature obtained by applying the half-amplitude map to one feature of
the interface Gram. -/
def finiteSandwichFeature
    (feature : Nat → Nat → Q')
    (amplitude : Nat → Nat → Q') (boundaryCount : Nat)
    (rank configuration : Nat) : Q' :=
  finSum (fun boundary =>
    amplitude configuration boundary * feature rank boundary)
    boundaryCount

private theorem finiteSandwichTerm_regroup
    (leftAmplitude rightAmplitude weight
      leftFeature rightFeature : Q') :
    (leftAmplitude * rightAmplitude) *
        (weight * (leftFeature * rightFeature)) ≈
      weight *
        ((leftAmplitude * leftFeature) *
          (rightAmplitude * rightFeature)) :=
  mul6_rearrange leftAmplitude rightAmplitude weight
    leftFeature rightFeature

private theorem finiteSandwichFeatureProduct
    (weight : Q') (left right : Nat → Q')
    (boundaryCount : Nat) :
    finSum (fun source =>
        finSum (fun target =>
          weight * (left source * right target))
          boundaryCount)
      boundaryCount ≈
    weight *
      (finSum left boundaryCount * finSum right boundaryCount) := by
  have hinner :
      finSum (fun source =>
          finSum (fun target =>
            weight * (left source * right target))
            boundaryCount)
        boundaryCount ≈
      finSum (fun source =>
          weight * finSum (fun target =>
            left source * right target) boundaryCount)
        boundaryCount := by
    apply finSum_eqv_congr
    intro source
    exact Q'.eqv_symm
      (const_mul_finSum
        (fun target => left source * right target)
        weight boundaryCount)
  have hpull :
      finSum (fun source =>
          weight * finSum (fun target =>
            left source * right target) boundaryCount)
        boundaryCount ≈
      weight * finSum (fun source =>
        finSum (fun target =>
          left source * right target) boundaryCount)
        boundaryCount :=
    Q'.eqv_symm
      (const_mul_finSum
        (fun source => finSum (fun target =>
          left source * right target) boundaryCount)
        weight boundaryCount)
  exact Q'.eqv_trans _ _ _ hinner
    (Q'.eqv_trans _ _ _ hpull
      (Q'.mul_eqv_congr_left weight _ _
        (Q'.eqv_symm
          (finSum_mul_finSum left right
            boundaryCount boundaryCount))))

/-- A finite common-coordinate sandwich of a constructive Gram is again a
constructive Gram.  Its weights are unchanged and each coordinate vector is
the finite half-amplitude transform of the original vector. -/
def finiteKernelSandwichGramRep
    {kernel : Nat → Nat → Q'} (rep : GramRep kernel)
    (amplitude : Nat → Nat → Q') (boundaryCount : Nat) :
    GramRep (finiteKernelSandwich kernel amplitude boundaryCount) where
  r := rep.r
  d := rep.d
  hd := rep.hd
  v := finiteSandwichFeature rep.v amplitude boundaryCount
  hM := by
    intro left right
    unfold finiteKernelSandwich finiteSandwichFeature
    have hsubstitute :
        finSum (fun source =>
            finSum (fun target =>
              (amplitude left source * amplitude right target) *
                kernel source target) boundaryCount)
          boundaryCount ≈
        finSum (fun source =>
            finSum (fun target =>
              finSum (fun rank =>
                rep.d rank *
                  ((amplitude left source * rep.v rank source) *
                    (amplitude right target * rep.v rank target)))
                rep.r) boundaryCount)
          boundaryCount := by
      apply finSum_eqv_congr
      intro source
      apply finSum_eqv_congr
      intro target
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left
          (amplitude left source * amplitude right target)
          (kernel source target)
          (finSum (fun rank => rep.d rank *
            (rep.v rank source * rep.v rank target)) rep.r)
          (rep.hM source target)) ?_
      refine Q'.eqv_trans _ _ _
        (const_mul_finSum
          (fun rank => rep.d rank *
            (rep.v rank source * rep.v rank target))
          (amplitude left source * amplitude right target)
          rep.r) ?_
      apply finSum_eqv_congr
      intro rank
      exact finiteSandwichTerm_regroup
        (amplitude left source) (amplitude right target)
        (rep.d rank) (rep.v rank source) (rep.v rank target)
    have hswapTargetRank :
        finSum (fun source =>
            finSum (fun target =>
              finSum (fun rank =>
                rep.d rank *
                  ((amplitude left source * rep.v rank source) *
                    (amplitude right target * rep.v rank target)))
                rep.r) boundaryCount)
          boundaryCount ≈
        finSum (fun source =>
            finSum (fun rank =>
              finSum (fun target =>
                rep.d rank *
                  ((amplitude left source * rep.v rank source) *
                    (amplitude right target * rep.v rank target)))
                boundaryCount) rep.r)
          boundaryCount := by
      apply finSum_eqv_congr
      intro source
      exact finSum_swap
        (fun target rank =>
          rep.d rank *
            ((amplitude left source * rep.v rank source) *
              (amplitude right target * rep.v rank target)))
        boundaryCount rep.r
    have hswapSourceRank :
        finSum (fun source =>
            finSum (fun rank =>
              finSum (fun target =>
                rep.d rank *
                  ((amplitude left source * rep.v rank source) *
                    (amplitude right target * rep.v rank target)))
                boundaryCount) rep.r)
          boundaryCount ≈
        finSum (fun rank =>
            finSum (fun source =>
              finSum (fun target =>
                rep.d rank *
                  ((amplitude left source * rep.v rank source) *
                    (amplitude right target * rep.v rank target)))
                boundaryCount) boundaryCount)
          rep.r :=
      finSum_swap
        (fun source rank =>
          finSum (fun target =>
            rep.d rank *
              ((amplitude left source * rep.v rank source) *
                (amplitude right target * rep.v rank target)))
            boundaryCount)
        boundaryCount rep.r
    exact Q'.eqv_trans _ _ _ hsubstitute
      (Q'.eqv_trans _ _ _ hswapTargetRank
        (Q'.eqv_trans _ _ _ hswapSourceRank
          (finSum_eqv_congr _ _ (fun rank =>
            finiteSandwichFeatureProduct
              (rep.d rank)
              (fun source =>
                amplitude left source * rep.v rank source)
              (fun target =>
                amplitude right target * rep.v rank target)
              boundaryCount) rep.r)))

/-- The complete finite reflection quadratic of a palindromic sandwich is
nonnegative, with arbitrary rational test coefficients. -/
theorem finiteKernelSandwichQuadratic_nonnegative
    {kernel : Nat → Nat → Q'} (rep : GramRep kernel)
    (amplitude : Nat → Nat → Q') (boundaryCount : Nat)
    (coefficient : Nat → Q') (configurationCount : Nat) :
    (0 : Q') ≤ gramQuadForm
      (finiteKernelSandwich kernel amplitude boundaryCount)
      coefficient configurationCount :=
  gramPSD_quadForm_nonneg
    (finiteKernelSandwichGramRep rep amplitude boundaryCount)
    coefficient configurationCount

#print axioms finiteKernelSandwichGramRep
#print axioms finiteKernelSandwichQuadratic_nonnegative

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenPalindromicSandwich
