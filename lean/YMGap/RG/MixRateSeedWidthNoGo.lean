/-
# V3 no-go: the proved `mixRate` seed of the r49 scale chain is not width-uniform

**Label: NO-GO for one route. NOT gap evidence; NOT a statement about the actual operator.**

The r49 capstone `RelativeDissipationScaleChain.scaleChain_afBudget_floor` takes a seed rate
`seed` with `hseed : WilsonVacuumSqContraction … (width j0) seed` and concludes the dyadic floor
`2^n (1 - r_n) ≥ (1 - seed)(seed - C·afA²/(j0+3))`. The only PROVED seed is
`wilsonVacuumSqContraction_mixRate`, with `seed = mixRate = 1 - mixFraction` and
`mixFraction = headFloor^F / prefixCap^F`, `F = (temporalFaces width).length ≥ width`.

The existing `BF4ExactSlabFixedSpatialRateWidthObstruction` already proves, unconditionally
(using `headFloor ≤ 1/32` and `prefixCap ≥ 1`, no extra hypothesis),
`mixFraction ≤ (1/32)^width` and `mixFraction ≤ ε` beyond `widthModulus ε`. This file only
transports that bound to the chain's seed slot:

* `one_sub_mixRate_lt`: `1 - mixRate(width) < ε` for every `width ≥ seedWidth ε`.
* `exists_width_one_sub_mixRate_lt`: `∀ ε > 0, ∃ width, 1 - mixRate(width) < ε`.
* `mixRate_floor_lt`: for every `Dq ≥ 0`, `(1 - mixRate)(mixRate - Dq) < ε` beyond `seedWidth ε`.
* `scaleChain_mixRate_floor_lt`: the same for the r49 budget `Dq = C·afA²·inv(j0+2)`, i.e. the
  floor delivered by the mixRate seed is below any `ε > 0` once `width j0 ≥ seedWidth ε`.
* `no_width_uniform_mixRate_floor`: no `m > 0` bounds that floor below for all widths.

This is a statement about the COMPUTED rate `mixRate`, not about the transfer operator's actual
spectral gap. Constructive, no external library; axioms within `propext`, `Quot.sound`.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialRateWidthObstruction
import YMGap.RG.RelativeDissipationScaleChain
import YMGap.Continuum.DefectRecursionPrimary

namespace YMGap.RG.MixRateSeedWidthNoGo

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
  (mixFraction mixRate mixRate_lt_one)
open YMGap.Continuum.BF4ExactSlabFixedSpatialRateWidthObstruction
  (widthModulus mixFraction_le_epsilon)
open YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory (afA)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory (NomeSchedule)
open YMGap.RG.RelativeDissipationScaleChain (inv inv_nonneg)

local infix:50 " ≈ " => Q'.eqv

/-- Width beyond which `1 - mixRate < ε` (half-tolerance of the existing modulus). -/
def seedWidth (epsilon : Q') : Nat := widthModulus (HalfPow.half * epsilon)

private theorem half_mul_lt {e : Q'} (he : (0 : Q') < e) : HalfPow.half * e < e :=
  YMGap.Continuum.ClusteringImpliesGap.lt_of_lt_of_le
    (YMGap.Continuum.ClusteringImpliesGap.mul_lt_mul_of_pos_right he
      (by decide : HalfPow.half < (1 : Q')))
    (Q'.le_of_eqv (Q'.one_mul_eqv _))

section Nome
variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))

/-- `1 - mixRate = mixFraction` (exact ring identity). -/
theorem one_sub_mixRate_eqv (width : Nat) :
    (1 : Q') - mixRate hw0 hw1 width ≈ mixFraction hw0 hw1 width :=
  YMGap.Continuum.RingNormaliser.poly_identity_of_normal_eq
    (.add (.const 1) (.neg (.add (.const 1) (.neg (.var 0))))) (.var 0)
    (by decide) (fun _ => mixFraction hw0 hw1 width)

/-- **`1 - mixRate(width) < ε` beyond `seedWidth ε` (PROVED, no extra hypothesis).** -/
theorem one_sub_mixRate_lt (epsilon : Q') (he : (0 : Q') < epsilon) (width : Nat)
    (hwidth : seedWidth epsilon ≤ width) :
    (1 : Q') - mixRate hw0 hw1 width < epsilon :=
  Q'.lt_of_le_of_lt
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (one_sub_mixRate_eqv hw0 hw1 width))
      (mixFraction_le_epsilon hw0 hw1 (HalfPow.half * epsilon)
        (ExpNeg.half_mul_pos _ he) width hwidth))
    (half_mul_lt he)

/-- **V3 no-go, existence form: `∀ ε > 0, ∃ width, 1 - mixRate(width) < ε` (PROVED).** -/
theorem exists_width_one_sub_mixRate_lt (epsilon : Q') (he : (0 : Q') < epsilon) :
    ∃ width : Nat, (1 : Q') - mixRate hw0 hw1 width < epsilon :=
  ⟨seedWidth epsilon, one_sub_mixRate_lt hw0 hw1 epsilon he _ (Nat.le_refl _)⟩

/-- `s - Dq ≤ 1` for `s ≤ 1` and `0 ≤ Dq`. -/
private theorem sub_le_one {s Dq : Q'} (hs : s ≤ (1 : Q')) (hD0 : (0 : Q') ≤ Dq) :
    s - Dq ≤ (1 : Q') := by
  have h : (0 : Q') + s ≤ Dq + 1 := Q'.add_le_add hD0 hs
  have hs' : s ≤ Dq + 1 := Q'.le_trans' _ _ _
    (Q'.le_of_eqv (YMGap.Continuum.RingNormaliser.poly_identity_of_normal_eq
      (.var 0) (.add (.const 0) (.var 0)) (by decide) (fun _ => s))) h
  exact Q'.sub_le_of_le_add hs'

/-- **Floor no-go: `(1 - mixRate)(mixRate - Dq) < ε` beyond `seedWidth ε`, any `Dq ≥ 0`.** -/
theorem mixRate_floor_lt (Dq : Q') (hD0 : (0 : Q') ≤ Dq) (epsilon : Q')
    (he : (0 : Q') < epsilon) (width : Nat) (hwidth : seedWidth epsilon ≤ width) :
    ((1 : Q') - mixRate hw0 hw1 width) * (mixRate hw0 hw1 width - Dq) < epsilon := by
  have hnn : (0 : Q') ≤ (1 : Q') - mixRate hw0 hw1 width :=
    Q'.sub_nonneg_of_le (Q'.le_of_lt (mixRate_lt_one hw0 hw1 width))
  have hle := Q'.mul_le_mul_of_nonneg_left _ _ _
    (sub_le_one (Q'.le_of_lt (mixRate_lt_one hw0 hw1 width)) hD0) hnn
  exact Q'.lt_of_le_of_lt (Q'.le_trans' _ _ _ hle (Q'.le_of_eqv (Q'.mul_one_eqv _)))
    (one_sub_mixRate_lt hw0 hw1 epsilon he width hwidth)

/-- **No width-uniform positive floor from the mixRate seed (PROVED).** -/
theorem no_width_uniform_mixRate_floor (Dq : Q') (hD0 : (0 : Q') ≤ Dq) (m : Q')
    (hm : (0 : Q') < m) :
    ¬ (∀ width : Nat,
      m ≤ ((1 : Q') - mixRate hw0 hw1 width) * (mixRate hw0 hw1 width - Dq)) := by
  intro h
  exact Int.not_lt.mpr (h (seedWidth m))
    (mixRate_floor_lt hw0 hw1 Dq hD0 m hm (seedWidth m) (Nat.le_refl _))

end Nome

/-- **r49 instance: the mixRate-seeded AF floor is below `ε` once `width j0 ≥ seedWidth ε`.** -/
theorem scaleChain_mixRate_floor_lt (ns : NomeSchedule) (width : Nat → Nat) (j0 : Nat)
    (C : Q') (hC : (0 : Q') ≤ C) (epsilon : Q') (he : (0 : Q') < epsilon)
    (hwidth : seedWidth epsilon ≤ width j0) :
    ((1 : Q') - mixRate (ns.nome_pos j0) (ns.nome_lt_one j0) (width j0)) *
      (mixRate (ns.nome_pos j0) (ns.nome_lt_one j0) (width j0) - C * (afA * afA) * inv (j0+2))
      < epsilon :=
  mixRate_floor_lt (ns.nome_pos j0) (ns.nome_lt_one j0) _
    (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hC (Q'.mul_nonneg _ _ (by decide) (by decide)))
      (inv_nonneg _))
    epsilon he (width j0) hwidth

end YMGap.RG.MixRateSeedWidthNoGo
