/-
# An explicit modulus for the outer-uniform U(1) tensor-tail envelope

At fixed rational heat coupling `0 < w < 1` and fixed finite coordinate
count `dimension`, the recursive outer-cutoff-free envelope from
`BF4U1OuterCutoffUniformTensorTail` is a fixed coefficient times the
one-charge closed tail:

    tensorEnvelope(w,M,d) ≈ closedTail(w,M) * tensorCoefficient(w,d).

For a modulus it is convenient to use the strictly positive coefficient

    tensorToleranceCoefficient(w,d) = 1 + tensorCoefficient(w,d).

The retained-pair cutoff is then the already constructed
`signedChargePairCutoff` at tolerance
`ε / tensorToleranceCoefficient(w,d)`.  Cancellation of this positive
coefficient proves that every later retained charge `M` makes the full
tensor envelope at most `ε`.

This is constructive and quantitative.  It is fixed in `w` and in the
finite dimension.  In particular it does not supply a cutoff uniform as
`w` approaches `1`, nor a bound uniform in a growing number of faces.
-/

import YMGap.Continuum.BF4U1OuterCutoffUniformTensorTail

namespace YMGap.Continuum.BF4U1OuterCutoffTensorTailModulus

open YMGap.Constructive
open YMGap.Continuum.HKConvGen
open YMGap.Continuum.U1SignedChargeHeatTail
open YMGap.Continuum.BF4U1OuterCutoffUniformTensorTail

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Extracting the finite-dimensional coefficient -/

/-- The fixed finite-dimensional coefficient multiplying the one-charge
tail in the recursive tensor envelope. -/
def signedChargeTensorTailCoefficient
    (w : Q') : Nat → Q'
  | 0 => 0
  | dimension + 1 =>
      signedChargeHeatCeiling w ^ dimension +
        signedChargeHeatCeiling w *
          signedChargeTensorTailCoefficient w dimension

theorem signedChargeTensorTailCoefficient_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w) :
    ∀ dimension,
      (0 : Q') ≤
        signedChargeTensorTailCoefficient w dimension
  | 0 => Q'.le_refl' 0
  | dimension + 1 => by
      exact Q'.zero_le_add _ _
        (Q'.pow_nonneg _
          (signedChargeHeatCeiling_nonnegative hw0)
          dimension)
        (Q'.mul_nonneg _ _
          (signedChargeHeatCeiling_nonnegative hw0)
          (signedChargeTensorTailCoefficient_nonnegative
            hw0 dimension))

/-- The recursive tensor envelope is exactly one closed tail times a fixed
coefficient. -/
theorem signedChargeTensorTailEnvelope_eqv_coefficient
    (w : Q') (M : Nat) :
    ∀ dimension,
      signedChargeTensorTailEnvelope w M dimension ≈
        signedChargeClosedTail w M *
          signedChargeTensorTailCoefficient w dimension
  | 0 => by
      exact Q'.eqv_symm
        (Q'.mul_zero_eqv
          (signedChargeClosedTail w M))
  | dimension + 1 => by
      have ih :=
        signedChargeTensorTailEnvelope_eqv_coefficient
          w M dimension
      change
        signedChargeClosedTail w M *
              signedChargeHeatCeiling w ^ dimension +
            signedChargeHeatCeiling w *
              signedChargeTensorTailEnvelope w M dimension ≈
          signedChargeClosedTail w M *
            (signedChargeHeatCeiling w ^ dimension +
              signedChargeHeatCeiling w *
                signedChargeTensorTailCoefficient w dimension)
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left
          (signedChargeClosedTail w M *
            signedChargeHeatCeiling w ^ dimension)
          _ _
          (Q'.mul_eqv_congr_left
            (signedChargeHeatCeiling w)
            _ _ ih)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left
          (signedChargeClosedTail w M *
            signedChargeHeatCeiling w ^ dimension)
          _ _
          (Q'.eqv_trans _ _ _
            (Q'.eqv_symm
              (Q'.mul_assoc_eqv
                (signedChargeHeatCeiling w)
                (signedChargeClosedTail w M)
                (signedChargeTensorTailCoefficient w dimension)))
            (Q'.mul_eqv_congr_right
              (signedChargeHeatCeiling w *
                signedChargeClosedTail w M)
              (signedChargeClosedTail w M *
                signedChargeHeatCeiling w)
              (signedChargeTensorTailCoefficient w dimension)
              (Q'.mul_comm_eqv
                (signedChargeHeatCeiling w)
                (signedChargeClosedTail w M))))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left
          (signedChargeClosedTail w M *
            signedChargeHeatCeiling w ^ dimension)
          _ _
          (Q'.mul_assoc_eqv
            (signedChargeClosedTail w M)
            (signedChargeHeatCeiling w)
            (signedChargeTensorTailCoefficient w dimension))) ?_
      exact Q'.eqv_symm
        (Q'.mul_add_eqv
          (signedChargeClosedTail w M)
          (signedChargeHeatCeiling w ^ dimension)
          (signedChargeHeatCeiling w *
            signedChargeTensorTailCoefficient w dimension))

/-! ## 2. A positive coefficient and the rescaled tolerance -/

/-- Strictly positive coefficient used to divide the requested tolerance.
The extra `1` also handles `dimension = 0` without a case split. -/
def signedChargeTensorToleranceCoefficient
    (w : Q') (dimension : Nat) : Q' :=
  1 + signedChargeTensorTailCoefficient w dimension

theorem signedChargeTensorToleranceCoefficient_pos
    {w : Q'} (hw0 : (0 : Q') < w)
    (dimension : Nat) :
    (0 : Q') <
      signedChargeTensorToleranceCoefficient w dimension := by
  unfold signedChargeTensorToleranceCoefficient
  have hcoeff :=
    signedChargeTensorTailCoefficient_nonnegative
      hw0 dimension
  apply CReal.pos_of_num_pos
  have hnum :
      (0 : Int) ≤
        (signedChargeTensorTailCoefficient w dimension).num :=
    (Q'.zero_le_iff_num_nonneg _).mp hcoeff
  have hden :
      (0 : Int) <
        (signedChargeTensorTailCoefficient w dimension).den := by
    exact_mod_cast
      Q'.den_pos
        (signedChargeTensorTailCoefficient w dimension)
  show
    (0 : Int) <
      1 *
          (signedChargeTensorTailCoefficient w dimension).den +
        (signedChargeTensorTailCoefficient w dimension).num *
          1
  omega

theorem signedChargeTensorToleranceCoefficient_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w)
    (dimension : Nat) :
    (0 : Q') ≤
      signedChargeTensorToleranceCoefficient w dimension :=
  Q'.le_of_lt
    (signedChargeTensorToleranceCoefficient_pos
      hw0 dimension)

/-- The exact envelope is bounded by the closed tail times the strictly
positive tolerance coefficient. -/
theorem signedChargeTensorTailEnvelope_le_toleranceCoefficient
    {w : Q'} (hw0 : (0 : Q') < w)
    (M dimension : Nat) :
    signedChargeTensorTailEnvelope w M dimension ≤
      signedChargeClosedTail w M *
        signedChargeTensorToleranceCoefficient w dimension := by
  have he :=
    signedChargeTensorTailEnvelope_eqv_coefficient
      w M dimension
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv he) ?_
  have htail0 :=
    signedChargeClosedTail_nonnegative hw0 M
  have hcoeff :
      signedChargeTensorTailCoefficient w dimension ≤
        signedChargeTensorToleranceCoefficient w dimension := by
    unfold signedChargeTensorToleranceCoefficient
    have hadd :=
      Q'.add_le_self_of_nonneg
        (signedChargeTensorTailCoefficient w dimension)
        1
        (by decide : (0 : Q') ≤ 1)
    exact Q'.le_trans' _ _ _ hadd
      (Q'.le_of_eqv
        (Q'.add_comm_eqv
          (signedChargeTensorTailCoefficient w dimension) 1))
  exact Q'.mul_le_mul_of_nonneg_left
    _ _ _ hcoeff htail0

/-- Explicit retained-pair cutoff for the full finite-dimensional tensor
tail envelope. -/
def signedChargeTensorTailCutoff
    (w ε : Q') (dimension : Nat) : Nat :=
  signedChargePairCutoff w
    (HKConv.divPos ε
      (signedChargeTensorToleranceCoefficient w dimension))

/-- The tolerance passed to the one-charge cutoff is positive. -/
theorem signedChargeTensorRescaledTolerance_pos
    {w ε : Q'} (hε : (0 : Q') < ε)
    (dimension : Nat) :
    (0 : Q') <
      HKConv.divPos ε
        (signedChargeTensorToleranceCoefficient w dimension) :=
  HKConv.divPos_pos (CReal.num_pos_of_pos hε)

/-! ## 3. The quantitative tensor-envelope modulus -/

/-- Main modulus: at fixed `0 < w < 1` and fixed finite `dimension`, every
retained-pair stage after `signedChargeTensorTailCutoff w ε dimension`
makes the outer-cutoff-uniform tensor-tail envelope at most `ε`. -/
theorem signedChargeTensorTailEnvelope_le_of_cutoff
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    {ε : Q'} (hε : (0 : Q') < ε)
    (dimension M : Nat)
    (hM :
      signedChargeTensorTailCutoff w ε dimension ≤ M) :
    signedChargeTensorTailEnvelope w M dimension ≤ ε := by
  let coefficient :=
    signedChargeTensorToleranceCoefficient w dimension
  let δ := HKConv.divPos ε coefficient
  have hcoefficientPos :
      (0 : Q') < coefficient := by
    exact signedChargeTensorToleranceCoefficient_pos
      hw0 dimension
  have hcoefficientNum :
      0 < coefficient.num :=
    CReal.num_pos_of_pos hcoefficientPos
  have hδpos : (0 : Q') < δ := by
    exact HKConv.divPos_pos
      (CReal.num_pos_of_pos hε)
  have hM' :
      signedChargePairCutoff w δ ≤ M := by
    exact hM
  have hone :
      signedChargeClosedTail w M ≤ δ :=
    signedChargeClosedTail_le_of_cutoff
      hw0 hw1 hδpos M hM'
  have henvelope :=
    signedChargeTensorTailEnvelope_le_toleranceCoefficient
      hw0 M dimension
  have hscale :
      signedChargeClosedTail w M * coefficient ≤
        δ * coefficient :=
    Q'.mul_le_mul_of_nonneg_right
      _ _ _ hone
      (Q'.le_of_lt hcoefficientPos)
  have hcancel : δ * coefficient ≈ ε := by
    exact HKConv.divPos_mul_eqv hcoefficientNum
  exact Q'.le_trans' _ _ _ henvelope
    (Q'.le_trans' _ _ _ hscale
      (Q'.le_of_eqv hcancel))

/-- The existing outside-union mass inherits the same explicit cutoff,
uniformly in every later outer charge cutoff `K`. -/
theorem signedChargeTensorOutsideUnionMass_le_of_cutoff
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    {ε : Q'} (hε : (0 : Q') < ε)
    (dimension : Nat)
    {M K : Nat}
    (hcut :
      signedChargeTensorTailCutoff w ε dimension ≤ M)
    (hMK : M ≤ K) :
    signedChargeTensorOutsideUnionMass
        w M K dimension ≤ ε := by
  exact Q'.le_trans' _ _ _
    (signedChargeTensorOutsideUnionMass_le_envelope
      hw0 hw1 hMK dimension)
    (signedChargeTensorTailEnvelope_le_of_cutoff
      hw0 hw1 hε dimension M hcut)

/-- Finite-face-list form of the same modulus.  The cutoff sees the fixed
number of faces, but remains independent of the later outer charge cutoff
`K`. -/
theorem finiteFaceListOuterUniformTensorTail_le_of_cutoff
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    {ε : Q'} (hε : (0 : Q') < ε)
    (faces : List Nat)
    {M K : Nat}
    (hcut :
      signedChargeTensorTailCutoff
        w ε faces.length ≤ M)
    (hMK : M ≤ K) :
    signedChargeTensorOutsideUnionMass
        w M K faces.length ≤ ε :=
  signedChargeTensorOutsideUnionMass_le_of_cutoff
    hw0 hw1 hε faces.length hcut hMK

#print axioms signedChargeTensorTailCoefficient_nonnegative
#print axioms signedChargeTensorTailEnvelope_eqv_coefficient
#print axioms signedChargeTensorToleranceCoefficient_pos
#print axioms signedChargeTensorTailEnvelope_le_of_cutoff
#print axioms signedChargeTensorOutsideUnionMass_le_of_cutoff
#print axioms finiteFaceListOuterUniformTensorTail_le_of_cutoff

end YMGap.Continuum.BF4U1OuterCutoffTensorTailModulus
