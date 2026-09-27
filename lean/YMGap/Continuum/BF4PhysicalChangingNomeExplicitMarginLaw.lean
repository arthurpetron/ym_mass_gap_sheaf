/-
# Explicit margin law for the changing-nome completed family

This module specializes the scale-free rational margin algebra to the actual
dependent `changingNomeDynamicFamily`.  It proves only the exact denominator
presentation of the lattice margin; comparison of that denominator with the
vanishing spacing is deliberately left as a separate typed certificate.
-/

import YMGap.Continuum.BF4PhysicalChangingNomeDynamicFamily
import YMGap.Continuum.BF4PhysicalCubeCutoffUniformGapAlgebra
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExplicitMarginBand
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorFinitePrefixResponse
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRCChannel

namespace YMGap.Continuum.BF4PhysicalChangingNomeExplicitMarginLaw

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Constructive.HalfPow
open YMGap.Continuum.BF4PhysicalCubeCompletedMarginalGap
open YMGap.Continuum.BF4PhysicalCubeAnchoredHeadBound
open YMGap.Continuum.BF4PhysicalChangingNomeDynamicFamily
open YMGap.Continuum.BF4PhysicalCubeCutoffUniformGap
open YMGap.Continuum.BF4PhysicalCubeCutoffUniformGapAlgebra
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExplicitMarginBand
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorFinitePrefixResponse
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorSameObjectRCChannel
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRCChannel
open YMGap.Continuum.PhysicalSeparatorLinearTail
open YMGap.Continuum.PhysicalSeparatorLogRate
open YMGap.Continuum.RCStrictPositivity

local infix:50 " ≈ " => Q'.eqv

/-- The explicit denominator inherited from the finite BF4 rate at the
scheduled nome. -/
def changingNomeMarginDenominator (scale : Nat) : Q' :=
  gapDenominator (changingNome scale)
    (Q'.le_of_lt (changingNome_pos scale))

theorem changingNomeMarginDenominator_pos (scale : Nat) :
    (0 : Q') < changingNomeMarginDenominator scale :=
  gapDenominator_pos (changingNome scale)
    (Q'.le_of_lt (changingNome_pos scale))

/-! The finite anchor budget now gives a concrete one-sided denominator
    lower bound.  This remains pointwise in the schedule; it does not compare
    the denominator to the vanishing spacing. -/

theorem changingNomeMarginDenominator_ge_two_add_twelve_scale (scale : Nat) :
    Q'.ofNat 2 + Q'.ofNat 12 *
        centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale
          (changingNome scale)
          (Q'.le_of_lt (changingNome_pos scale)) 1404 0 ≤
      changingNomeMarginDenominator scale := by
  let w := changingNome scale
  let hw : (0 : Q') ≤ w := Q'.le_of_lt (changingNome_pos scale)
  let scaleValue :=
    centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale w hw 1404 0
  have hbudget : Q'.ofNat 2 * scaleValue ≤ headEnergyConstant w hw :=
    YMGap.Continuum.BF4PhysicalCubeAnchoredHeadBound.headEnergyConstant_ge_two_carrierSquareScale
      w hw
  have hscaled :
      Q'.ofNat 6 * (Q'.ofNat 2 * scaleValue) ≤
        Q'.ofNat 6 * headEnergyConstant w hw :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hbudget (by decide)
  have hcoeff : Q'.ofNat 12 ≈ Q'.ofNat 6 * Q'.ofNat 2 := by decide
  have hscale_eqv :
      Q'.ofNat 12 * scaleValue ≈
        Q'.ofNat 6 * (Q'.ofNat 2 * scaleValue) := by
    refine Q'.eqv_trans _ ((Q'.ofNat 6 * Q'.ofNat 2) * scaleValue) _
      (Q'.mul_eqv_congr_right _ _ _ hcoeff) ?_
    exact Q'.mul_assoc_eqv _ _ _
  have hscaled' :
      Q'.ofNat 12 * scaleValue ≤
        Q'.ofNat 6 * headEnergyConstant w hw :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hscale_eqv) hscaled
  have hadded :
      Q'.ofNat 2 + Q'.ofNat 12 * scaleValue ≤
        Q'.ofNat 2 + Q'.ofNat 6 * headEnergyConstant w hw :=
    Q'.add_le_add_left _ _ _ hscaled'
  let x : Q' := Q'.ofNat 6 * headEnergyConstant w hw
  have htwo : Q'.ofNat 2 ≈ (1 : Q') + 1 := by decide
  have hden : Q'.ofNat 2 + x ≈ 1 + (1 + x) := by
    have hfirst : Q'.ofNat 2 + x ≈ (1 + 1) + x :=
      Q'.add_eqv_congr_right (Q'.ofNat 2) ((1 : Q') + 1) x htwo
    exact Q'.eqv_trans _ ((1 + 1) + x) _ hfirst
      (Q'.add_assoc_eqv 1 1 x)
  change Q'.ofNat 2 + Q'.ofNat 12 * scaleValue ≤
    1 + (1 + Q'.ofNat 6 * headEnergyConstant w hw)
  exact Q'.le_trans' _ _ _ hadded (Q'.le_of_eqv hden)

/-- The exact denominator expression needed by the changing-nome asymptotic
    reduction.  This is an algebraic presentation only; it does not compare
    the expression with the vanishing spacing. -/
theorem changingNomeMarginDenominator_eqv_two_add_six_headEnergy
    (scale : Nat) :
    changingNomeMarginDenominator scale ≈
      Q'.ofNat 2 + Q'.ofNat 6 *
        headEnergyConstant
          (changingNome scale)
          (Q'.le_of_lt (changingNome_pos scale)) := by
  unfold changingNomeMarginDenominator gapDenominator gapNumerator
  let x : Q' := Q'.ofNat 6 *
    headEnergyConstant (changingNome scale)
      (Q'.le_of_lt (changingNome_pos scale))
  change 1 + (1 + x) ≈ Q'.ofNat 2 + x
  refine Q'.eqv_trans _ ((1 + 1) + x) _
    (Q'.eqv_symm (Q'.add_assoc_eqv 1 1 x)) ?_
  exact Q'.add_eqv_congr_right (1 + 1) (Q'.ofNat 2) x (by decide)

/-- The changing family has an exact same-object reciprocal presentation of
its lattice margin.  No spacing comparison is included. -/
def changingNomeExplicitMarginInverseLaw :
    ExplicitMarginInverseLaw changingNomeDynamicFamily where
  denominator := changingNomeMarginDenominator
  denominator_pos := changingNomeMarginDenominator_pos
  margin_eqv_inverse := by
    intro scale
    change
      (1 - (changingNomeDynamicFamily.completedGap scale).rate) ≈
        Q'.divPos 1 (changingNomeMarginDenominator scale)
          (changingNomeMarginDenominator_pos scale)
    rw [changingNomeDynamicFamily_rate]
    let w := changingNome scale
    let hw : (0 : Q') ≤ w := Q'.le_of_lt (changingNome_pos scale)
    let numerator := gapNumerator w hw
    let denominator := gapDenominator w hw
    have hdenominator : (0 : Q') < denominator := gapDenominator_pos w hw
    have hmargin := one_sub_divPos_eqv_inverse numerator denominator hdenominator
    have hsub : (denominator - numerator) ≈ (1 : Q') := by
      show ((1 + numerator) + -numerator) ≈ (1 : Q')
      exact one_add_sub_self_eqv numerator
    refine Q'.eqv_trans _ (Q'.divPos (denominator - numerator) denominator hdenominator)
      _ hmargin ?_
    unfold Q'.divPos
    exact Q'.mul_eqv_congr_right _ _ _ hsub

/-- The remaining physical-calibration fields specialized to the concrete
changing family.  This type is intentionally not inhabited here: its fields
are exactly the two uniform denominator-versus-spacing inequalities. -/
abbrev changingNomeExplicitMarginDenominatorBand : Type 1 :=
  ExplicitMarginDenominatorBand changingNomeExplicitMarginInverseLaw

/-! The remaining B04 input can now be stated directly at the anchored
    head-energy level.  This is the smallest honest certificate below the
    generic denominator band: it asks only for two uniform product bounds on
    `2 + 6 * H(w_scale)`, with `H = S/F` the already-defined head quotient. -/

structure ChangingNomeHeadEnergyProductBand : Type 1 where
  floor : Q'
  floor_pos : (0 : Q') < floor
  ceiling : Q'
  ceiling_pos : (0 : Q') < ceiling
  lowerHeadEnergy : ∀ scale,
    (floor * changingNomeDynamicFamily.transferSpacing.spacing scale) *
        (Q'.ofNat 2 + Q'.ofNat 6 *
          headEnergyConstant
            (changingNome scale)
            (Q'.le_of_lt (changingNome_pos scale))) ≤
      (1 : Q')
  upperHeadEnergy : ∀ scale,
    (1 : Q') ≤
      (ceiling * changingNomeDynamicFamily.transferSpacing.spacing scale) *
        (Q'.ofNat 2 + Q'.ofNat 6 *
          headEnergyConstant
            (changingNome scale)
            (Q'.le_of_lt (changingNome_pos scale)))

/-! The lower product inequality is not merely a quotient-side condition.  By
    multiplying it by the positive finite floor and using the exact identity
    `F * (S / F) = S`, it forces the floor itself to be at least of the
    spacing-times-carrier-square order.  This generic scalar kernel keeps the
    expensive algebra independent of the dependent finite-sector expressions
    used by the changing-nome theorem below. -/

theorem ChangingNomeHeadEnergyProductBand.lower_floor_mul_spacing_scale_le_of_scalar
    {A H S F : Q'}
    (hA0 : (0 : Q') ≤ A)
    (hF0 : (0 : Q') ≤ F)
    (hband : A * (Q'.ofNat 2 + Q'.ofNat 6 * H) ≤ (1 : Q'))
    (hFS : F * H ≈ S) :
    Q'.ofNat 6 * (A * S) ≤ F := by
  have hsixH_le : Q'.ofNat 6 * H ≤
      Q'.ofNat 2 + Q'.ofNat 6 * H := by
    exact Q'.le_trans' _ (Q'.ofNat 6 * H + Q'.ofNat 2) _
      (Q'.add_le_self_of_nonneg _ _ (by decide))
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _))
  have hsixH_scaled : A * (Q'.ofNat 6 * H) ≤
      A * (Q'.ofNat 2 + Q'.ofNat 6 * H) := by
    exact Q'.mul_le_mul_of_nonneg_left _ _ A hsixH_le hA0
  have hsixH_le_one : A * (Q'.ofNat 6 * H) ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ hsixH_scaled hband
  have hscaled : F * (A * (Q'.ofNat 6 * H)) ≤ F := by
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ F hsixH_le_one hF0)
      (Q'.le_of_eqv (Q'.mul_one_eqv F))
  have hleft :
      Q'.ofNat 6 * (A * S) ≈ F * (A * (Q'.ofNat 6 * H)) := by
    refine Q'.eqv_trans _ (Q'.ofNat 6 * (A * (F * H))) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left (Q'.ofNat 6) _ _
        (Q'.mul_eqv_congr_left A _ _ (Q'.eqv_symm hFS))
    · refine Q'.eqv_trans _ ((Q'.ofNat 6 * A) * (F * H)) _
        (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 6) A (F * H))) ?_
      refine Q'.eqv_trans _ (((Q'.ofNat 6 * A) * F) * H) _
        (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 6 * A) F H)) ?_
      refine Q'.eqv_trans _ ((F * (Q'.ofNat 6 * A)) * H) _
        (Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_comm_eqv (Q'.ofNat 6 * A) F)) ?_
      refine Q'.eqv_trans _ ((F * (A * Q'.ofNat 6)) * H) _
        (Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_eqv_congr_left F _ _ (Q'.mul_comm_eqv (Q'.ofNat 6) A))) ?_
      refine Q'.eqv_trans _ (F * ((A * Q'.ofNat 6) * H)) _
        (Q'.mul_assoc_eqv F (A * Q'.ofNat 6) H) ?_
      exact Q'.mul_eqv_congr_left F _ _
        (Q'.mul_assoc_eqv A (Q'.ofNat 6) H)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft) hscaled

/-! The dependent specialization is kept behind four small names.  This
    avoids asking elaboration to repeatedly normalize the changing-nome
    carrier, its positive floor, and the scheduled spacing in one large
    theorem term. -/

def changingNomeBandSpacing (scale : Nat) : Q' :=
  changingNomeDynamicFamily.transferSpacing.spacing scale

def changingNomeBandFloor (scale : Nat) : Q' :=
  fixedBasePulledPositiveEdgeFloorValue
    (changingNome scale)
    (Q'.le_of_lt (changingNome_pos scale)) 1404 0

def changingNomeBandScale (scale : Nat) : Q' :=
  centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale
    (changingNome scale)
    (Q'.le_of_lt (changingNome_pos scale)) 1404 0

def changingNomeBandHeadEnergy (scale : Nat) : Q' :=
  headEnergyConstant
    (changingNome scale)
    (Q'.le_of_lt (changingNome_pos scale))

theorem ChangingNomeHeadEnergyProductBand.lower_floor_mul_spacing_mul_scale_le
    (band : ChangingNomeHeadEnergyProductBand) (scale : Nat) :
    Q'.ofNat 6 *
        ((band.floor * changingNomeBandSpacing scale) *
          changingNomeBandScale scale) ≤
      changingNomeBandFloor scale := by
  let A : Q' := band.floor * changingNomeBandSpacing scale
  let H : Q' := changingNomeBandHeadEnergy scale
  let S : Q' := changingNomeBandScale scale
  let F : Q' := changingNomeBandFloor scale
  have hA0 : (0 : Q') ≤ A := by
    dsimp [A, changingNomeBandSpacing]
    exact Q'.mul_nonneg band.floor
      (changingNomeDynamicFamily.transferSpacing.spacing scale)
      (Q'.le_of_lt band.floor_pos)
      (Q'.le_of_lt (changingNomeDynamicFamily.transferSpacing.spacing_pos scale))
  have hF0 : (0 : Q') ≤ F := by
    dsimp [F, changingNomeBandFloor]
    exact Q'.le_of_lt
      (fixedBasePulledPositiveEdgeFloorValue_pos
        (changingNome scale) (Q'.le_of_lt (changingNome_pos scale)) 1404 0)
  have hband : A * (Q'.ofNat 2 + Q'.ofNat 6 * H) ≤ (1 : Q') := by
    dsimp [A, H, changingNomeBandSpacing, changingNomeBandHeadEnergy]
    exact band.lowerHeadEnergy scale
  have hFS : F * H ≈ S := by
    dsimp [F, H, S, changingNomeBandFloor, changingNomeBandHeadEnergy,
      changingNomeBandScale]
    exact fixedBasePulledPositiveEdgeFloorValue_mul_headEnergyConstant_eqv_scale
      (changingNome scale) (Q'.le_of_lt (changingNome_pos scale))
  have hresult :=
    ChangingNomeHeadEnergyProductBand.lower_floor_mul_spacing_scale_le_of_scalar
      (A := A) (H := H) (S := S) (F := F) hA0 hF0 hband hFS
  simpa [A, S, F, changingNomeBandSpacing, changingNomeBandScale,
    changingNomeBandFloor] using hresult

private theorem floor_mul_six_spacing_scale_eqv
    (floor spacing scale : Q') :
    Q'.ofNat 6 * ((floor * spacing) * scale) ≈
      floor * (Q'.ofNat 6 * (spacing * scale)) := by
  refine Q'.eqv_trans _ ((Q'.ofNat 6 * (floor * spacing)) * scale) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 6) (floor * spacing) scale)) ?_
  refine Q'.eqv_trans _ (((Q'.ofNat 6 * floor) * spacing) * scale) _
    (Q'.mul_eqv_congr_right _ _ scale
      (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 6) floor spacing))) ?_
  refine Q'.eqv_trans _ (((floor * Q'.ofNat 6) * spacing) * scale) _
    (Q'.mul_eqv_congr_right _ _ scale
      (Q'.mul_eqv_congr_right _ _ spacing
        (Q'.mul_comm_eqv (Q'.ofNat 6) floor))) ?_
  refine Q'.eqv_trans _ ((floor * (Q'.ofNat 6 * spacing)) * scale) _
    (Q'.mul_eqv_congr_right _ _ scale
      (Q'.mul_assoc_eqv floor (Q'.ofNat 6) spacing)) ?_
  refine Q'.eqv_trans _ (floor * ((Q'.ofNat 6 * spacing) * scale)) _
    (Q'.mul_assoc_eqv floor (Q'.ofNat 6 * spacing) scale) ?_
  exact Q'.mul_eqv_congr_left floor _ _
    (Q'.mul_assoc_eqv (Q'.ofNat 6) spacing scale)

private theorem cancel_floor_of_spacing_scale
    {floor spacing scale : Q'}
    (hfloor : (0 : Q') < floor)
    (hbound : Q'.ofNat 6 * ((floor * spacing) * scale) ≤ floor) :
    Q'.ofNat 6 * (spacing * scale) ≤ (1 : Q') := by
  have htransport :
      Q'.ofNat 6 * ((floor * spacing) * scale) ≈
        floor * (Q'.ofNat 6 * (spacing * scale)) := by
    exact floor_mul_six_spacing_scale_eqv floor spacing scale
  have hright : floor ≈ floor * (1 : Q') :=
    Q'.eqv_symm (Q'.mul_one_eqv floor)
  have hcancel :
      floor * (Q'.ofNat 6 * (spacing * scale)) ≤ floor * (1 : Q') :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm htransport))
      (Q'.le_trans' _ _ _ hbound (Q'.le_of_eqv hright))
  exact Q'.le_of_mul_le_mul_left hcancel hfloor

/-- Cancelling the positive finite floor from the specialized necessary
    condition leaves a floor-independent carrier/spacing ceiling.  This is a
    necessary consequence of an inhabited product band, not an assertion that
    the product band itself exists. -/
theorem ChangingNomeHeadEnergyProductBand.spacing_mul_scale_le_of_lower_bound
    (scale : Nat)
    (hbound :
      Q'.ofNat 6 *
          ((changingNomeBandFloor scale * changingNomeBandSpacing scale) *
            changingNomeBandScale scale) ≤
        changingNomeBandFloor scale) :
    Q'.ofNat 6 *
        (changingNomeBandSpacing scale * changingNomeBandScale scale) ≤
      (1 : Q') := by
  exact cancel_floor_of_spacing_scale
    (floor := changingNomeBandFloor scale)
    (spacing := changingNomeBandSpacing scale)
    (scale := changingNomeBandScale scale)
    (by
      exact fixedBasePulledPositiveEdgeFloorValue_pos
        (changingNome scale) (Q'.le_of_lt (changingNome_pos scale)) 1404 0)
    hbound

theorem changingNomeBandScale_ge_two (scale : Nat) :
    (Q'.ofNat 2 : Q') ≤ changingNomeBandScale scale := by
  unfold changingNomeBandScale
  let states := centralPhysicalFiniteVacuumSectorIndices
    (changingNome scale) (Q'.le_of_lt (changingNome_pos scale)) 1404 0
  have hlength : 1 ≤ states.length := by
    exact Nat.succ_le_iff.mpr
      (List.length_pos_of_mem
        (zero_mem_centralPhysicalFiniteVacuumSectorIndices
          (changingNome scale) (Q'.le_of_lt (changingNome_pos scale)) 1404 0))
  have hsquare : 1 ≤ states.length * states.length := by
    simpa using Nat.mul_le_mul hlength hlength
  have hcast : (Q'.ofNat 1 : Q') ≤ Q'.ofNat (states.length * states.length) :=
    Q'.ofNat_le_ofNat hsquare
  have hadd : (1 : Q') + 1 ≤
      (1 : Q') + Q'.ofNat (states.length * states.length) :=
    Q'.add_le_add_left _ _ _ hcast
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (by decide)) hadd

/-- The present spacing schedule cannot even admit the specialized lower-bound
    certificate at scale zero: its fixed carrier-square factor is already too
    large for `spacing 0 = 1/2`.  This is a route obstruction, not a
    Yang--Mills obstruction; the schedule or normalization must be changed. -/
theorem changingNomeBand_lower_bound_scale_zero_impossible
    (hbound :
      Q'.ofNat 6 *
          ((changingNomeBandFloor 0 * changingNomeBandSpacing 0) *
            changingNomeBandScale 0) ≤
        changingNomeBandFloor 0) : False := by
  have hceiling :=
    ChangingNomeHeadEnergyProductBand.spacing_mul_scale_le_of_lower_bound
      0 hbound
  have hscale := changingNomeBandScale_ge_two 0
  have hspacing : changingNomeBandSpacing 0 = Q'.invSucc 1 := rfl
  have hinner : Q'.invSucc 1 * (Q'.ofNat 2 : Q') ≤
      Q'.invSucc 1 * changingNomeBandScale 0 := by
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ hscale
      (Q'.invSucc_nonneg 1)
  have houter : Q'.ofNat 6 * (Q'.invSucc 1 * (Q'.ofNat 2 : Q')) ≤
      Q'.ofNat 6 * (Q'.invSucc 1 * changingNomeBandScale 0) := by
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ hinner (by decide)
  have hbase : (1 : Q') <
      Q'.ofNat 6 * (Q'.invSucc 1 * (Q'.ofNat 2 : Q')) := by
    decide
  have hlt_of_lt_of_le {a b c : Q'} (hab : a < b) (hbc : b ≤ c) : a < c := by
    have e1 : a.num * (b.den : Int) < b.num * (a.den : Int) := hab
    have e2 : b.num * (c.den : Int) ≤ c.num * (b.den : Int) := hbc
    show a.num * (c.den : Int) < c.num * (a.den : Int)
    have hcdpos : (0 : Int) < (c.den : Int) := by exact_mod_cast c.den_pos
    have had : (0 : Int) ≤ (a.den : Int) := by exact_mod_cast Nat.zero_le _
    have s1 : (a.num * (c.den : Int)) * (b.den : Int)
        < (b.num * (a.den : Int)) * (c.den : Int) := by
      have hs := Int.mul_lt_mul_of_pos_right e1 hcdpos
      have hreorder :
          (a.num * (b.den : Int)) * (c.den : Int) =
            (a.num * (c.den : Int)) * (b.den : Int) := by
        rw [Int.mul_assoc, Int.mul_assoc,
          Int.mul_comm (b.den : Int) (c.den : Int)]
      rwa [hreorder] at hs
    have s2 : (b.num * (a.den : Int)) * (c.den : Int)
        ≤ (c.num * (a.den : Int)) * (b.den : Int) := by
      have hs := Int.mul_le_mul_of_nonneg_left e2 had
      have hleft :
          (a.den : Int) * (b.num * (c.den : Int)) =
            (b.num * (a.den : Int)) * (c.den : Int) := by
        rw [Int.mul_comm b.num (a.den : Int), Int.mul_assoc]
      have hright :
          (a.den : Int) * (c.num * (b.den : Int)) =
            (c.num * (a.den : Int)) * (b.den : Int) := by
        rw [Int.mul_comm c.num (a.den : Int), Int.mul_assoc]
      rwa [hleft, hright] at hs
    have schain : (a.num * (c.den : Int)) * (b.den : Int)
        < (c.num * (a.den : Int)) * (b.den : Int) :=
      Int.lt_of_lt_of_le s1 s2
    exact Int.lt_of_mul_lt_mul_right schain
      (by exact_mod_cast Nat.zero_le _)
  have hlt : (1 : Q') <
      Q'.ofNat 6 * (changingNomeBandSpacing 0 * changingNomeBandScale 0) := by
    rw [hspacing]
    exact hlt_of_lt_of_le hbase houter
  exact (Int.not_lt_of_ge hceiling) hlt

/-! The preceding contradiction identifies the repair required by the
    floor-cancellation consumer: the spacing must be normalized against the
    actual carrier scale before it is sent to zero.  The next schedule keeps
    the same completed nome/transfer family but uses a denominator indexed by
    the nonnegative carrier `6*S` and by the scale itself. -/

def changingNomeCarrierNormalizedSpacing : PhysicalSpacing where
  spacing := fun scale =>
    let carrier := Q'.ofNat 6 * changingNomeBandScale scale
    Q'.invSucc (carrier.num.toNat + scale)
  spacing_pos := fun scale => by
    exact Q'.invSucc_pos _

/-- The repaired spacing has an explicit scale envelope, independently of the
carrier numerator: its denominator is at least `scale`.  This is stronger
than the abstract spacing-to-zero witness and is still only spacing control;
it does not compare the physical gap denominator with the lattice spacing. -/
theorem changingNomeCarrierNormalizedSpacing_le_invSucc (scale : Nat) :
    changingNomeCarrierNormalizedSpacing.spacing scale ≤ Q'.invSucc scale := by
  let carrier := Q'.ofNat 6 * changingNomeBandScale scale
  let index := carrier.num.toNat + scale
  have hindex : scale ≤ index := by
    dsimp [index]
    omega
  simpa [changingNomeCarrierNormalizedSpacing, index] using
    (ExpNeg.invSucc_le_of_le hindex)

/-- The repaired spacing also pays one additive unit beyond the carrier:
`(6*S + 1) * spacing ≤ 1`.  The extra unit is the `+1` in the reciprocal
index; it is an explicit reserve for later floor/product comparisons. -/
theorem changingNomeCarrierNormalizedSpacing_carrier_plus_one_le
    (scale : Nat) :
    (Q'.ofNat 6 * changingNomeBandScale scale) *
          changingNomeCarrierNormalizedSpacing.spacing scale +
        changingNomeCarrierNormalizedSpacing.spacing scale ≤
      (1 : Q') := by
  let carrier := Q'.ofNat 6 * changingNomeBandScale scale
  let index := carrier.num.toNat + scale
  have hcarrier0 : (0 : Q') ≤ carrier := by
    dsimp [carrier]
    exact Q'.mul_nonneg _ _ (by decide)
      (Q'.le_of_lt
        (centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale_pos
          (changingNome scale)
          (Q'.le_of_lt (changingNome_pos scale)) 1404 0))
  have hcarrierNat : carrier ≤ Q'.ofNat carrier.num.toNat :=
    YMGap.Constructive.RatNat.le_ofNat_toNat carrier hcarrier0
  have hnumIndex : carrier.num.toNat ≤ index := by
    exact Nat.le_add_right _ _
  have hindexNat : Q'.ofNat carrier.num.toNat ≤ Q'.ofNat index :=
    Q'.ofNat_le_ofNat hnumIndex
  have hcarrierIndex : carrier ≤ Q'.ofNat index :=
    Q'.le_trans' _ _ _ hcarrierNat hindexNat
  have hscaled : carrier * Q'.invSucc index ≤
      Q'.ofNat index * Q'.invSucc index :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hcarrierIndex
      (Q'.le_of_lt (Q'.invSucc_pos index))
  have hsum : carrier * Q'.invSucc index + Q'.invSucc index ≤
      Q'.ofNat index * Q'.invSucc index + Q'.invSucc index :=
    Q'.add_le_add_right _ _ _ hscaled
  have hsucc : Q'.ofNat (index + 1) ≈ Q'.ofNat index + 1 := by
    refine Q'.eqv_trans _ (Q'.ofNat index + Q'.ofNat 1) _
      (Q'.ofNat_add_eqv index 1) ?_
    exact Q'.add_eqv_congr_left _ _ _ (by decide)
  have hnormEqv :
      Q'.ofNat index * Q'.invSucc index + Q'.invSucc index ≈ (1 : Q') := by
    refine Q'.eqv_trans _ ((Q'.ofNat index + 1) * Q'.invSucc index) _ ?_ ?_
    · refine Q'.eqv_trans _
        (Q'.ofNat index * Q'.invSucc index +
          (1 : Q') * Q'.invSucc index) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ _
          (Q'.eqv_symm (Q'.one_mul_eqv (Q'.invSucc index)))
      · exact Q'.eqv_symm
          (Q'.add_mul_eqv (Q'.ofNat index) 1 (Q'.invSucc index))
    · have hmul :
          (Q'.ofNat index + 1) * Q'.invSucc index ≈
            Q'.ofNat (index + 1) * Q'.invSucc index :=
        Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hsucc)
      exact Q'.eqv_trans _ _ _ hmul
        (Q'.ofNat_succ_mul_invSucc index)
  exact Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hnormEqv)

def changingNomeCarrierNormalizedSpacingToZero :
    SpacingToZero changingNomeCarrierNormalizedSpacing where
  modulus := fun epsilon => epsilon.den
  spacing_le := by
    intro epsilon hepsilon scale hscale
    let carrier := Q'.ofNat 6 * changingNomeBandScale scale
    have hindex : epsilon.den ≤ carrier.num.toNat + scale := by
      omega
    exact Q'.le_trans' _ _ _
      (ExpNeg.invSucc_le_of_le hindex)
      (HalfPow.invSucc_den_le epsilon hepsilon)

theorem changingNomeCarrierNormalizedSpacing_carrier_ceiling
    (scale : Nat) :
    Q'.ofNat 6 *
        (changingNomeCarrierNormalizedSpacing.spacing scale *
          changingNomeBandScale scale) ≤
      (1 : Q') := by
  let carrier := Q'.ofNat 6 * changingNomeBandScale scale
  let index := carrier.num.toNat + scale
  have hcarrier_pos : (0 : Q') < carrier := by
    dsimp [carrier]
    exact Q'.mul_pos (by decide)
      (centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale_pos
        (changingNome scale)
        (Q'.le_of_lt (changingNome_pos scale)) 1404 0)
  have hcarrier_nonneg : (0 : Q') ≤ carrier :=
    Q'.le_of_lt hcarrier_pos
  have hbase : carrier * Q'.invSucc carrier.num.toNat ≤ (1 : Q') :=
    ExpNeg.mul_invSucc_toNat_le_one carrier hcarrier_nonneg
  have hindex : carrier.num.toNat ≤ index := by
    exact Nat.le_add_right _ _
  have hstep : Q'.invSucc index ≤ Q'.invSucc carrier.num.toNat :=
    ExpNeg.invSucc_le_of_le hindex
  have hscaled : carrier * Q'.invSucc index ≤
      carrier * Q'.invSucc carrier.num.toNat :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hstep hcarrier_nonneg
  have hbound : carrier * Q'.invSucc index ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ hscaled hbase
  have htransport :
      Q'.ofNat 6 * (Q'.invSucc index * changingNomeBandScale scale) ≈
        carrier * Q'.invSucc index := by
    dsimp [carrier]
    refine Q'.eqv_trans _
      (Q'.ofNat 6 * (changingNomeBandScale scale * Q'.invSucc index)) _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_comm_eqv (Q'.invSucc index)
          (changingNomeBandScale scale))) ?_
    exact Q'.eqv_symm
      (Q'.mul_assoc_eqv (Q'.ofNat 6)
        (changingNomeBandScale scale) (Q'.invSucc index))
  simpa [changingNomeCarrierNormalizedSpacing, index] using
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv htransport) hbound)

/-- The repaired spacing schedule retains the same completed nome and gap
    data while replacing only the scale-to-zero schedule.  It is a concrete
    normalization scaffold; no physical-rate band is claimed. -/
def changingNomeCarrierNormalizedDynamicFamily :
    DynamicVacuumSectorCompletedFamily 0 where
  nome := changingNome
  nome_pos := changingNome_pos
  nome_lt_one := changingNome_lt_one
  transferSpacing := changingNomeCarrierNormalizedSpacing
  transferSpacingToZero := changingNomeCarrierNormalizedSpacingToZero
  completedGap := fun scale =>
    completedSectorContraction
      (changingNome_pos scale)
      (changingNome_lt_one scale)
      (changingNome_le_half scale)

theorem changingNomeCarrierNormalizedDynamicFamily_same_nome (scale : Nat) :
    changingNomeCarrierNormalizedDynamicFamily.nome scale = changingNome scale := rfl

theorem changingNomeCarrierNormalizedDynamicFamily_same_gap_rate (scale : Nat) :
    (changingNomeCarrierNormalizedDynamicFamily.completedGap scale).rate =
      cutoffUniformRate (changingNome scale)
        (Q'.le_of_lt (changingNome_pos scale)) := rfl

/-- The carrier-normalized spacing repair leaves the concrete completed
    moving-cube observable available on the repaired same-name family. -/
def changingNomeCarrierNormalizedMovingCubeChannel :
    DynamicVacuumSectorSameObjectRCChannel
      changingNomeCarrierNormalizedDynamicFamily :=
  centralPhysicalDynamicMovingCubeRCChannel
    changingNomeCarrierNormalizedDynamicFamily

/-! ## 8a. One typed bridge for the repaired same-object channel -/

/-- The carrier-normalized spacing repair keeps the same concrete completed
SU(2) observable while changing only the scale schedule.  This bridge records
the exact nome/spacing, vector, and same-object autocorrelation identifications
that a physical-rate consumer must preserve. -/
structure ChangingNomeCarrierNormalizedConcreteChannelBridge : Type 1 where
  channel : DynamicVacuumSectorSameObjectRCChannel
    changingNomeCarrierNormalizedDynamicFamily
  nome_eq : ∀ scale,
    changingNomeCarrierNormalizedDynamicFamily.nome scale = changingNome scale
  spacing_eq : ∀ scale,
    changingNomeCarrierNormalizedDynamicFamily.transferSpacing.spacing scale =
      changingNomeCarrierNormalizedSpacing.spacing scale
  vectorAt_eq : ∀ scale,
    channel.vectorAt scale =
      centralPhysicalDynamicMovingCubeVectorAt
        changingNomeCarrierNormalizedDynamicFamily scale
  autocorrelation_eq : ∀ scale time,
    channel.connectedAutocorrelation scale time =
      DynamicVacuumSectorSameObjectRCChannel.connectedAutocorrelation
        (centralPhysicalDynamicMovingCubeRCChannel
          changingNomeCarrierNormalizedDynamicFamily) scale time

/-- Construct the repaired-channel bridge from the existing inhabited
carrier-normalized family and literal moving-cube channel. -/
def changingNomeCarrierNormalizedConcreteChannelBridge :
    ChangingNomeCarrierNormalizedConcreteChannelBridge where
  channel := changingNomeCarrierNormalizedMovingCubeChannel
  nome_eq := by
    intro scale
    exact changingNomeCarrierNormalizedDynamicFamily_same_nome scale
  spacing_eq := by
    intro scale
    rfl
  vectorAt_eq := by
    intro scale
    rfl
  autocorrelation_eq := by
    intro scale time
    rfl

/-- The repaired bridge retains strict zero-time positivity at every scale. -/
theorem changingNomeCarrierNormalizedConcreteChannelBridge_zero_isPositive
    (scale : Nat) :
    RCIsPositive
      (DynamicVacuumSectorSameObjectRCChannel.connectedAutocorrelation
        changingNomeCarrierNormalizedConcreteChannelBridge.channel scale 0) :=
  centralPhysicalDynamicMovingCube_connected_zero_isPositive
    changingNomeCarrierNormalizedDynamicFamily scale

/-- The repaired bridge retains completed squared decay at every scale/time. -/
theorem changingNomeCarrierNormalizedConcreteChannelBridge_connectedSq_decay
    (scale time : Nat) :
    CReal.RCle
      (DynamicVacuumSectorSameObjectRCChannel.connectedAutocorrelationSq
        changingNomeCarrierNormalizedConcreteChannelBridge.channel scale time)
      (CReal.RCmul
        (CReal.RCscale
          ((((changingNomeCarrierNormalizedDynamicFamily.completedGap scale).rate *
              (changingNomeCarrierNormalizedDynamicFamily.completedGap scale).rate)) ^ time)
          (DynamicVacuumSectorSameObjectRCChannel.normSq
            changingNomeCarrierNormalizedConcreteChannelBridge.channel scale))
        (DynamicVacuumSectorSameObjectRCChannel.normSq
          changingNomeCarrierNormalizedConcreteChannelBridge.channel scale)) :=
  centralPhysicalDynamicMovingCube_connectedSq_decay
    changingNomeCarrierNormalizedDynamicFamily scale time

theorem changingNomeCarrierNormalizedMovingCube_zero_isPositive (scale : Nat) :
    RCIsPositive
      (DynamicVacuumSectorSameObjectRCChannel.connectedAutocorrelation
        changingNomeCarrierNormalizedMovingCubeChannel scale 0) :=
  centralPhysicalDynamicMovingCube_connected_zero_isPositive
    changingNomeCarrierNormalizedDynamicFamily scale

theorem changingNomeCarrierNormalizedMovingCube_connectedSq_decay
    (scale time : Nat) :
    CReal.RCle
      (DynamicVacuumSectorSameObjectRCChannel.connectedAutocorrelationSq
        changingNomeCarrierNormalizedMovingCubeChannel scale time)
      (CReal.RCmul
        (CReal.RCscale
          ((((changingNomeCarrierNormalizedDynamicFamily.completedGap scale).rate *
              (changingNomeCarrierNormalizedDynamicFamily.completedGap scale).rate)) ^ time)
          (changingNomeCarrierNormalizedMovingCubeChannel.normSq scale))
        (changingNomeCarrierNormalizedMovingCubeChannel.normSq scale)) :=
  centralPhysicalDynamicMovingCube_connectedSq_decay
    changingNomeCarrierNormalizedDynamicFamily scale time

theorem changingNomeCarrierNormalizedMovingCube_sampled_zero_isPositive
    (scale : Nat) :
    RCIsPositive
      (sampledConnectedAutocorrelation
        changingNomeCarrierNormalizedMovingCubeChannel scale 0) :=
  sampledConnectedAutocorrelation_zero_isPositive
    changingNomeCarrierNormalizedMovingCubeChannel scale

theorem changingNomeCarrierNormalizedMovingCube_sampled_eq_global
    (scale time : Nat) :
    sampledConnectedAutocorrelation
        changingNomeCarrierNormalizedMovingCubeChannel scale time =
      centralPhysicalCutoffCompletedInner
        (changingNomeCarrierNormalizedDynamicFamily.nome_pos scale)
        (changingNomeCarrierNormalizedDynamicFamily.nome_lt_one scale) 0
        (centralPhysicalConcreteAdaptiveCompletedMarkovPower
          (changingNomeCarrierNormalizedDynamicFamily.nome_pos scale)
          (changingNomeCarrierNormalizedDynamicFamily.nome_lt_one scale) 0
          (centralPhysicalDynamicRCLatticeSteps
            changingNomeCarrierNormalizedDynamicFamily scale time)
          (centralPhysicalVacuumSectorCylinderCompletionToGlobal
            (changingNomeCarrierNormalizedMovingCubeChannel.vectorAt scale).1))
        (centralPhysicalVacuumSectorCylinderCompletionToGlobal
          (changingNomeCarrierNormalizedMovingCubeChannel.vectorAt scale).1) :=
  sampledConnectedAutocorrelation_eq_global
    changingNomeCarrierNormalizedMovingCubeChannel scale time

theorem changingNomeCarrierNormalizedMovingCube_sampled_sq_decay
    (scale time : Nat) :
    CReal.RCle
      (sampledConnectedAutocorrelationSq
        changingNomeCarrierNormalizedMovingCubeChannel scale time)
      (CReal.RCmul
        (CReal.RCscale
          ((((changingNomeCarrierNormalizedDynamicFamily.completedGap scale).rate *
              (changingNomeCarrierNormalizedDynamicFamily.completedGap scale).rate)) ^
            (centralPhysicalDynamicRCLatticeSteps
              changingNomeCarrierNormalizedDynamicFamily scale time))
          (changingNomeCarrierNormalizedMovingCubeChannel.normSq scale))
        (changingNomeCarrierNormalizedMovingCubeChannel.normSq scale)) :=
  sampledConnectedAutocorrelationSq_decay
    changingNomeCarrierNormalizedMovingCubeChannel scale time

def changingNomeCarrierNormalizedFinitePrefixResponseCertificate
    (bound : Nat) :
    FinitePrefixResponseFloor
      changingNomeCarrierNormalizedMovingCubeChannel bound :=
  finitePrefixResponseCertificate
    changingNomeCarrierNormalizedMovingCubeChannel bound

theorem changingNomeCarrierNormalizedFinitePrefixResponseFloor_pos
    (bound : Nat) :
    (0 : Q') <
      finitePrefixResponseFloor
        changingNomeCarrierNormalizedMovingCubeChannel bound :=
  finitePrefixResponseFloor_pos
    changingNomeCarrierNormalizedMovingCubeChannel bound

theorem changingNomeCarrierNormalizedFinitePrefixResponseFloor_le_sampled_zeroTime
    (bound scale : Nat) (hscale : scale ≤ bound) :
    CReal.RCle
      (Quotient.mk CReal.crealSetoid
        (CReal.ofQ'
          (finitePrefixResponseFloor
            changingNomeCarrierNormalizedMovingCubeChannel bound)))
      (sampledConnectedAutocorrelation
        changingNomeCarrierNormalizedMovingCubeChannel scale 0) := by
  rw [sampledConnectedAutocorrelation_zero_eq_normSq]
  exact (changingNomeCarrierNormalizedFinitePrefixResponseCertificate bound).lowerNorm
    scale hscale

/-- The exact denominator law transported to the repaired spacing schedule.
    The dimensionless margin is unchanged because the completed nome and gap
    are unchanged; only the physical spacing field is replaced. -/
def changingNomeCarrierNormalizedExplicitMarginInverseLaw :
    ExplicitMarginInverseLaw changingNomeCarrierNormalizedDynamicFamily where
  denominator := changingNomeMarginDenominator
  denominator_pos := changingNomeMarginDenominator_pos
  margin_eqv_inverse := by
    intro scale
    have hmargin :
        changingNomeCarrierNormalizedDynamicFamily.latticeMargin scale ≈
          changingNomeDynamicFamily.latticeMargin scale := by
      unfold DynamicVacuumSectorCompletedFamily.latticeMargin
      rw [changingNomeCarrierNormalizedDynamicFamily_same_gap_rate,
        changingNomeDynamicFamily_rate]
      exact Q'.eqv_refl _
    exact Q'.eqv_trans _ _ _ hmargin
      (changingNomeExplicitMarginInverseLaw.margin_eqv_inverse scale)

/-- Every finite prefix of the repaired carrier-normalized family has the
    exact same-family denominator band obtained from its completed physical
    gap.  The extrema are constructive finite minima/maxima; no all-scale
    calibration is smuggled into this witness. -/
def changingNomeCarrierNormalizedFinitePrefixExplicitMarginDenominatorBand
    (bound : Nat) :
    ExplicitMarginDenominatorBand.FinitePrefixExplicitMarginDenominatorBand
      changingNomeCarrierNormalizedExplicitMarginInverseLaw bound :=
  ExplicitMarginDenominatorBand.finitePrefixExplicitMarginDenominatorBand bound

/-- The repaired finite-prefix denominator witness contracts to the matching
    finite-prefix physical-rate band on the identical completed family. -/
def changingNomeCarrierNormalizedFinitePrefixPhysicalRateBand
    (bound : Nat) :
    ExplicitMarginDenominatorBand.FinitePrefixPhysicalRateBand
      changingNomeCarrierNormalizedExplicitMarginInverseLaw bound :=
  (changingNomeCarrierNormalizedFinitePrefixExplicitMarginDenominatorBand bound).toFinitePrefixPhysicalRateBand

/-! ## 8c. Inhabited finite-prefix same-object route -/

/-- Every finite scale window carries both a positive same-object response floor
and the corresponding finite-prefix rate band on the identical repaired
completed family.  The bound is deliberately a field, so this object cannot
be mistaken for an all-scale calibration. -/
structure ChangingNomeCarrierNormalizedFinitePrefixConcreteRoute
    (bound : Nat) : Type 1 where
  channelBridge : ChangingNomeCarrierNormalizedConcreteChannelBridge
  response : FinitePrefixResponseFloor channelBridge.channel bound
  rateBand : ExplicitMarginDenominatorBand.FinitePrefixPhysicalRateBand
    changingNomeCarrierNormalizedExplicitMarginInverseLaw bound

/-- Construct the finite-prefix route at any supplied bound from the concrete
moving-cube response certificate and finite denominator extrema. -/
def changingNomeCarrierNormalizedFinitePrefixConcreteRoute
    (bound : Nat) :
    ChangingNomeCarrierNormalizedFinitePrefixConcreteRoute bound where
  channelBridge := changingNomeCarrierNormalizedConcreteChannelBridge
  response := finitePrefixResponseCertificate
    changingNomeCarrierNormalizedMovingCubeChannel bound
  rateBand := changingNomeCarrierNormalizedFinitePrefixPhysicalRateBand bound

/-- The finite-prefix route's explicit response floor bounds the same-object
zero-time autocorrelation throughout its window. -/
theorem ChangingNomeCarrierNormalizedFinitePrefixConcreteRoute.response_floor_le_zeroTime
    {bound : Nat}
    (route : ChangingNomeCarrierNormalizedFinitePrefixConcreteRoute bound)
    (scale : Nat) (hscale : scale ≤ bound) :
    CReal.RCle
      (Quotient.mk CReal.crealSetoid
        (CReal.ofQ' route.response.floor))
      (DynamicVacuumSectorSameObjectRCChannel.connectedAutocorrelation
        route.channelBridge.channel scale 0) := by
  rw [DynamicVacuumSectorSameObjectRCChannel.connectedAutocorrelation_zero_eq_normSq]
  exact route.response.lowerNorm scale hscale

/-- Enlarging the finite window can only lower its constructive gap floor. -/
theorem changingNomeCarrierNormalizedFinitePrefixGapFloor_succ_le
    (bound : Nat) :
    ExplicitMarginDenominatorBand.finitePrefixGapFloor
        changingNomeCarrierNormalizedDynamicFamily (bound + 1) ≤
      ExplicitMarginDenominatorBand.finitePrefixGapFloor
        changingNomeCarrierNormalizedDynamicFamily bound := by
  simpa [ExplicitMarginDenominatorBand.finitePrefixGapFloor,
    YMGap.Continuum.WindowedSpacingFloor.finMin] using
    (YMGap.Continuum.WindowedSpacingFloor.min'_le_right
      (changingNomeCarrierNormalizedDynamicFamily.physicalGap (bound + 1))
      (YMGap.Continuum.WindowedSpacingFloor.finMin
        changingNomeCarrierNormalizedDynamicFamily.physicalGap bound))

/-- Enlarging the finite window can only raise its constructive gap ceiling. -/
theorem changingNomeCarrierNormalizedFinitePrefixGapCeiling_le_succ
    (bound : Nat) :
    ExplicitMarginDenominatorBand.finitePrefixGapCeiling
        changingNomeCarrierNormalizedDynamicFamily bound ≤
      ExplicitMarginDenominatorBand.finitePrefixGapCeiling
        changingNomeCarrierNormalizedDynamicFamily (bound + 1) := by
  simpa [ExplicitMarginDenominatorBand.finitePrefixGapCeiling] using
    (Q'.le_runningMax_succ
      changingNomeCarrierNormalizedDynamicFamily.physicalGap bound)

/-- The minimal cofinal input below the all-scale rate band: one positive floor
    below every finite-prefix minimum and one finite ceiling above every
    finite-prefix maximum.  Its two fields are the remaining asymptotic
    estimates; the structure itself is intentionally not inhabited here. -/
structure ChangingNomeCarrierNormalizedCofinalGapCalibration : Type 1 where
  floor : Q'
  floor_pos : (0 : Q') < floor
  ceiling : Q'
  ceiling_pos : (0 : Q') < ceiling
  floor_le_prefix : ∀ bound,
    floor ≤
      ExplicitMarginDenominatorBand.finitePrefixGapFloor
        changingNomeCarrierNormalizedDynamicFamily bound
  prefix_ceiling_le : ∀ bound,
    ExplicitMarginDenominatorBand.finitePrefixGapCeiling
        changingNomeCarrierNormalizedDynamicFamily bound ≤ ceiling

/-! The cofinal-prefix presentation is equivalent to a direct pointwise
    physical-gap band.  This is a structural recoding only: it neither proves
    either all-scale estimate nor changes the completed carrier. -/

structure ChangingNomeCarrierNormalizedPhysicalGapBounds : Type 1 where
  floor : Q'
  floor_pos : (0 : Q') < floor
  ceiling : Q'
  ceiling_pos : (0 : Q') < ceiling
  floor_le_gap : ∀ scale,
    floor ≤ changingNomeCarrierNormalizedDynamicFamily.physicalGap scale
  gap_le_ceiling : ∀ scale,
    changingNomeCarrierNormalizedDynamicFamily.physicalGap scale ≤ ceiling

def ChangingNomeCarrierNormalizedCofinalGapCalibration.toPhysicalGapBounds
    (calibration : ChangingNomeCarrierNormalizedCofinalGapCalibration) :
    ChangingNomeCarrierNormalizedPhysicalGapBounds where
  floor := calibration.floor
  floor_pos := calibration.floor_pos
  ceiling := calibration.ceiling
  ceiling_pos := calibration.ceiling_pos
  floor_le_gap := by
    intro scale
    exact Q'.le_trans' _ _ _
      (calibration.floor_le_prefix scale)
      (YMGap.Continuum.WindowedSpacingFloor.finMin_le
        changingNomeCarrierNormalizedDynamicFamily.physicalGap scale scale
        (Nat.le_refl scale))
  gap_le_ceiling := by
    intro scale
    exact Q'.le_trans' _ _ _
      (Q'.le_runningMax
        changingNomeCarrierNormalizedDynamicFamily.physicalGap scale)
      (calibration.prefix_ceiling_le scale)

private theorem physicalGap_floor_le_finitePrefixGapFloor
    (floor : Q')
    (hfloor : ∀ scale,
      floor ≤ changingNomeCarrierNormalizedDynamicFamily.physicalGap scale) :
    ∀ bound,
      floor ≤
        ExplicitMarginDenominatorBand.finitePrefixGapFloor
          changingNomeCarrierNormalizedDynamicFamily bound
  | 0 => hfloor 0
  | bound + 1 => by
      unfold ExplicitMarginDenominatorBand.finitePrefixGapFloor
        YMGap.Continuum.WindowedSpacingFloor.finMin
      exact (Q'.le_min'_iff _ _ _).mpr
        ⟨hfloor (bound + 1),
          physicalGap_floor_le_finitePrefixGapFloor floor hfloor bound⟩

def ChangingNomeCarrierNormalizedPhysicalGapBounds.toCofinalGapCalibration
    (bounds : ChangingNomeCarrierNormalizedPhysicalGapBounds) :
    ChangingNomeCarrierNormalizedCofinalGapCalibration where
  floor := bounds.floor
  floor_pos := bounds.floor_pos
  ceiling := bounds.ceiling
  ceiling_pos := bounds.ceiling_pos
  floor_le_prefix :=
    physicalGap_floor_le_finitePrefixGapFloor bounds.floor
      bounds.floor_le_gap
  prefix_ceiling_le := by
    intro bound
    unfold ExplicitMarginDenominatorBand.finitePrefixGapCeiling
    exact Q'.runningMax_le_of_le bounds.gap_le_ceiling bound

/-! Once the direct pointwise bounds are supplied, the reciprocal identity
    compiles them to the raw denominator band without passing back through the
    finite-prefix presentation. -/

def ChangingNomeCarrierNormalizedPhysicalGapBounds.toExplicitMarginDenominatorBand
    (bounds : ChangingNomeCarrierNormalizedPhysicalGapBounds) :
    ExplicitMarginDenominatorBand
      changingNomeCarrierNormalizedExplicitMarginInverseLaw where
  floor := bounds.floor
  floor_pos := bounds.floor_pos
  ceiling := bounds.ceiling
  ceiling_pos := bounds.ceiling_pos
  lowerDenominator := by
    intro scale
    have hscaled := Q'.mul_le_mul_of_nonneg_right
      bounds.floor
      (changingNomeCarrierNormalizedDynamicFamily.physicalGap scale)
      (changingNomeCarrierNormalizedDynamicFamily.transferSpacing.spacing scale)
      (bounds.floor_le_gap scale)
      (Q'.le_of_lt
        (changingNomeCarrierNormalizedDynamicFamily.transferSpacing.spacing_pos scale))
    have hproduct := Q'.mul_le_mul_of_nonneg_right
      (bounds.floor *
        changingNomeCarrierNormalizedDynamicFamily.transferSpacing.spacing scale)
      (changingNomeCarrierNormalizedDynamicFamily.physicalGap scale *
        changingNomeCarrierNormalizedDynamicFamily.transferSpacing.spacing scale)
      (changingNomeCarrierNormalizedExplicitMarginInverseLaw.denominator scale)
      hscaled
      (Q'.le_of_lt
        (changingNomeCarrierNormalizedExplicitMarginInverseLaw.denominator_pos scale))
    have hone :=
      ExplicitMarginDenominatorBand.physicalGap_mul_spacing_mul_den_eqv_one
        (law := changingNomeCarrierNormalizedExplicitMarginInverseLaw) scale
    exact Q'.le_trans' _ _ _ hproduct (Q'.le_of_eqv hone)
  upperDenominator := by
    intro scale
    let gap : Q' :=
      changingNomeCarrierNormalizedDynamicFamily.physicalGap scale
    let spacing : Q' :=
      changingNomeCarrierNormalizedDynamicFamily.transferSpacing.spacing scale
    let denominator : Q' :=
      changingNomeCarrierNormalizedExplicitMarginInverseLaw.denominator scale
    have hnonneg :
        (0 : Q') ≤
          spacing * denominator :=
      Q'.mul_nonneg
        spacing denominator
        (Q'.le_of_lt
          (changingNomeCarrierNormalizedDynamicFamily.transferSpacing.spacing_pos scale))
        (Q'.le_of_lt
          (changingNomeCarrierNormalizedExplicitMarginInverseLaw.denominator_pos scale))
    have hscaled := Q'.mul_le_mul_of_nonneg_right
      gap
      bounds.ceiling
      (spacing * denominator)
      (bounds.gap_le_ceiling scale)
      hnonneg
    have honeEqv : (1 : Q') ≈
        gap * (spacing * denominator) :=
      Q'.eqv_trans _
        ((gap * spacing) * denominator) _
        (Q'.eqv_symm
          (ExplicitMarginDenominatorBand.physicalGap_mul_spacing_mul_den_eqv_one
            (law := changingNomeCarrierNormalizedExplicitMarginInverseLaw) scale))
        (Q'.mul_assoc_eqv gap spacing denominator)
    have hone : (1 : Q') ≤
        gap * (spacing * denominator) :=
      Q'.le_of_eqv honeEqv
    exact Q'.le_trans' _ _ _ hone
      (Q'.le_trans' _ _ _ hscaled
        (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_assoc_eqv
          bounds.ceiling
          spacing denominator))))

def ChangingNomeCarrierNormalizedPhysicalGapBounds.toPhysicalRateBand
    (bounds : ChangingNomeCarrierNormalizedPhysicalGapBounds) :
    DynamicVacuumSectorPhysicalRateBand
      changingNomeCarrierNormalizedDynamicFamily :=
  bounds.toExplicitMarginDenominatorBand.toPhysicalRateBand

/-! The lower raw denominator inequality is not an additional cofinal
    estimate.  The floor field already bounds the same completed family's
    physical gap, and the exact reciprocal law then contracts that bound to
    one.  Only the upper raw inequality remains in the calibration input. -/

theorem ChangingNomeCarrierNormalizedCofinalGapCalibration.lowerDenominator
    (calibration : ChangingNomeCarrierNormalizedCofinalGapCalibration)
    (scale : Nat) :
    (calibration.floor *
        changingNomeCarrierNormalizedDynamicFamily.transferSpacing.spacing scale) *
        changingNomeCarrierNormalizedExplicitMarginInverseLaw.denominator scale ≤
      (1 : Q') := by
  have hfloorGap : calibration.floor ≤
      changingNomeCarrierNormalizedDynamicFamily.physicalGap scale :=
    Q'.le_trans' _ _ _
      (calibration.floor_le_prefix scale)
      (YMGap.Continuum.WindowedSpacingFloor.finMin_le
        changingNomeCarrierNormalizedDynamicFamily.physicalGap scale scale
        (Nat.le_refl scale))
  have hscaled := Q'.mul_le_mul_of_nonneg_right
    calibration.floor
    (changingNomeCarrierNormalizedDynamicFamily.physicalGap scale)
    (changingNomeCarrierNormalizedDynamicFamily.transferSpacing.spacing scale)
    hfloorGap
    (Q'.le_of_lt
      (changingNomeCarrierNormalizedDynamicFamily.transferSpacing.spacing_pos scale))
  have hproduct := Q'.mul_le_mul_of_nonneg_right
    (calibration.floor *
      changingNomeCarrierNormalizedDynamicFamily.transferSpacing.spacing scale)
    (changingNomeCarrierNormalizedDynamicFamily.physicalGap scale *
      changingNomeCarrierNormalizedDynamicFamily.transferSpacing.spacing scale)
    (changingNomeCarrierNormalizedExplicitMarginInverseLaw.denominator scale)
    hscaled
    (Q'.le_of_lt
      (changingNomeCarrierNormalizedExplicitMarginInverseLaw.denominator_pos scale))
  have hone :=
    ExplicitMarginDenominatorBand.physicalGap_mul_spacing_mul_den_eqv_one
      (law := changingNomeCarrierNormalizedExplicitMarginInverseLaw) scale
  exact Q'.le_trans' _ _ _ hproduct (Q'.le_of_eqv hone)

/-- A cofinal-prefix calibration certificate compiles to the all-scale
    physical-rate band on the identical repaired completed family.  No
    asymptotic estimate is manufactured: the two uniform fields are explicit
    inputs to this compiler. -/
def ChangingNomeCarrierNormalizedCofinalGapCalibration.toPhysicalRateBand
    (calibration : ChangingNomeCarrierNormalizedCofinalGapCalibration) :
    DynamicVacuumSectorPhysicalRateBand
      changingNomeCarrierNormalizedDynamicFamily where
  floor := calibration.floor
  floor_pos := calibration.floor_pos
  ceiling := calibration.ceiling
  ceiling_pos := calibration.ceiling_pos
  lowerRate := by
    intro scale
    have hfloorGap : calibration.floor ≤
        changingNomeCarrierNormalizedDynamicFamily.physicalGap scale :=
      Q'.le_trans' _ _ _
        (calibration.floor_le_prefix scale)
        (YMGap.Continuum.WindowedSpacingFloor.finMin_le
          changingNomeCarrierNormalizedDynamicFamily.physicalGap scale scale
          (Nat.le_refl scale))
    have hscaled := Q'.mul_le_mul_of_nonneg_right
      calibration.floor
      (changingNomeCarrierNormalizedDynamicFamily.physicalGap scale)
      (changingNomeCarrierNormalizedDynamicFamily.transferSpacing.spacing scale)
      hfloorGap
      (Q'.le_of_lt
        (changingNomeCarrierNormalizedDynamicFamily.transferSpacing.spacing_pos scale))
    have hcollapse :
        changingNomeCarrierNormalizedDynamicFamily.physicalGap scale *
            changingNomeCarrierNormalizedDynamicFamily.transferSpacing.spacing scale ≈
          changingNomeCarrierNormalizedDynamicFamily.latticeMargin scale := by
      unfold DynamicVacuumSectorCompletedFamily.physicalGap
      exact Q'.divPos_mul_eqv _ _ _
    exact Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hcollapse)
  upperRate := by
    intro scale
    have hgapCeiling : changingNomeCarrierNormalizedDynamicFamily.physicalGap scale ≤
        calibration.ceiling :=
      Q'.le_trans' _ _ _
        (Q'.le_runningMax
          changingNomeCarrierNormalizedDynamicFamily.physicalGap scale)
        (calibration.prefix_ceiling_le scale)
    have hscaled := Q'.mul_le_mul_of_nonneg_right
      (changingNomeCarrierNormalizedDynamicFamily.physicalGap scale)
      calibration.ceiling
      (changingNomeCarrierNormalizedDynamicFamily.transferSpacing.spacing scale)
      hgapCeiling
      (Q'.le_of_lt
        (changingNomeCarrierNormalizedDynamicFamily.transferSpacing.spacing_pos scale))
    have hcollapse :
        changingNomeCarrierNormalizedDynamicFamily.latticeMargin scale ≈
          changingNomeCarrierNormalizedDynamicFamily.physicalGap scale *
            changingNomeCarrierNormalizedDynamicFamily.transferSpacing.spacing scale := by
      unfold DynamicVacuumSectorCompletedFamily.physicalGap
      exact Q'.eqv_symm (Q'.divPos_mul_eqv _ _ _)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hcollapse) hscaled

/-- The smallest honest B04 certificate for the repaired schedule.  Its two
    fields are the still-open uniform product bounds, now typed against the
    same completed nome/gap family as the carrier-normalized spacing. -/
structure ChangingNomeCarrierNormalizedHeadEnergyProductBand : Type 1 where
  floor : Q'
  floor_pos : (0 : Q') < floor
  ceiling : Q'
  ceiling_pos : (0 : Q') < ceiling
  lowerHeadEnergy : ∀ scale,
    (floor *
        changingNomeCarrierNormalizedDynamicFamily.transferSpacing.spacing scale) *
        (Q'.ofNat 2 + Q'.ofNat 6 *
          headEnergyConstant
            (changingNome scale)
            (Q'.le_of_lt (changingNome_pos scale))) ≤
      (1 : Q')
  upperHeadEnergy : ∀ scale,
    (1 : Q') ≤
      (ceiling *
        changingNomeCarrierNormalizedDynamicFamily.transferSpacing.spacing scale) *
        (Q'.ofNat 2 + Q'.ofNat 6 *
          headEnergyConstant
            (changingNome scale)
            (Q'.le_of_lt (changingNome_pos scale)))

/-! The repaired schedule has the same quotient identity as the original
    changing-nome family.  Its product certificate therefore forces the exact
    floor order required by the normalized spacing, with no re-use of the
    scale-zero contradiction from the old schedule. -/

theorem ChangingNomeCarrierNormalizedHeadEnergyProductBand.lower_floor_mul_spacing_mul_scale_le
    (band : ChangingNomeCarrierNormalizedHeadEnergyProductBand) (scale : Nat) :
    Q'.ofNat 6 *
        ((band.floor *
            changingNomeCarrierNormalizedDynamicFamily.transferSpacing.spacing scale) *
          changingNomeBandScale scale) ≤
      changingNomeBandFloor scale := by
  let A : Q' := band.floor *
    changingNomeCarrierNormalizedDynamicFamily.transferSpacing.spacing scale
  let H : Q' := changingNomeBandHeadEnergy scale
  let S : Q' := changingNomeBandScale scale
  let F : Q' := changingNomeBandFloor scale
  have hA0 : (0 : Q') ≤ A := by
    dsimp [A]
    exact Q'.mul_nonneg band.floor
      (changingNomeCarrierNormalizedDynamicFamily.transferSpacing.spacing scale)
      (Q'.le_of_lt band.floor_pos)
      (Q'.le_of_lt
        (changingNomeCarrierNormalizedDynamicFamily.transferSpacing.spacing_pos scale))
  have hF0 : (0 : Q') ≤ F := by
    dsimp [F, changingNomeBandFloor]
    exact Q'.le_of_lt
      (fixedBasePulledPositiveEdgeFloorValue_pos
        (changingNome scale) (Q'.le_of_lt (changingNome_pos scale)) 1404 0)
  have hband : A * (Q'.ofNat 2 + Q'.ofNat 6 * H) ≤ (1 : Q') := by
    dsimp [A, H]
    exact band.lowerHeadEnergy scale
  have hFS : F * H ≈ S := by
    dsimp [F, H, S, changingNomeBandFloor, changingNomeBandHeadEnergy,
      changingNomeBandScale]
    exact fixedBasePulledPositiveEdgeFloorValue_mul_headEnergyConstant_eqv_scale
      (changingNome scale) (Q'.le_of_lt (changingNome_pos scale))
  have hresult :=
    ChangingNomeHeadEnergyProductBand.lower_floor_mul_spacing_scale_le_of_scalar
      (A := A) (H := H) (S := S) (F := F) hA0 hF0 hband hFS
  simpa [A, S, F, changingNomeBandScale, changingNomeBandFloor] using hresult

def ChangingNomeCarrierNormalizedHeadEnergyProductBand.toExplicitMarginDenominatorBand
    (band : ChangingNomeCarrierNormalizedHeadEnergyProductBand) :
    ExplicitMarginDenominatorBand
      changingNomeCarrierNormalizedExplicitMarginInverseLaw where
  floor := band.floor
  floor_pos := band.floor_pos
  ceiling := band.ceiling
  ceiling_pos := band.ceiling_pos
  lowerDenominator := by
    intro scale
    have htransport :
        (band.floor *
            changingNomeCarrierNormalizedDynamicFamily.transferSpacing.spacing scale) *
            changingNomeMarginDenominator scale ≈
          (band.floor *
            changingNomeCarrierNormalizedDynamicFamily.transferSpacing.spacing scale) *
            (Q'.ofNat 2 + Q'.ofNat 6 *
              headEnergyConstant
                (changingNome scale)
                (Q'.le_of_lt (changingNome_pos scale))) :=
      Q'.mul_eqv_congr_left _ _ _
        (changingNomeMarginDenominator_eqv_two_add_six_headEnergy scale)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv htransport)
      (band.lowerHeadEnergy scale)
  upperDenominator := by
    intro scale
    have htransport :
        (band.ceiling *
            changingNomeCarrierNormalizedDynamicFamily.transferSpacing.spacing scale) *
            changingNomeMarginDenominator scale ≈
          (band.ceiling *
            changingNomeCarrierNormalizedDynamicFamily.transferSpacing.spacing scale) *
            (Q'.ofNat 2 + Q'.ofNat 6 *
              headEnergyConstant
                (changingNome scale)
                (Q'.le_of_lt (changingNome_pos scale))) :=
      Q'.mul_eqv_congr_left _ _ _
        (changingNomeMarginDenominator_eqv_two_add_six_headEnergy scale)
    exact Q'.le_trans' _ _ _ (band.upperHeadEnergy scale)
      (Q'.le_of_eqv (Q'.eqv_symm htransport))

def ChangingNomeCarrierNormalizedHeadEnergyProductBand.toPhysicalRateBand
    (band : ChangingNomeCarrierNormalizedHeadEnergyProductBand) :
    DynamicVacuumSectorPhysicalRateBand
      changingNomeCarrierNormalizedDynamicFamily :=
  band.toExplicitMarginDenominatorBand.toPhysicalRateBand

/-! ## 8b. Same-object physical-rate route -/

/-- A same-family physical-rate route keeps the repaired concrete channel and
the uniform rate band in one typed object.  The rate band is intentionally a
field: it is not inferred from the channel's dimensionless decay. -/
structure ChangingNomeCarrierNormalizedConcretePhysicalChannelRoute : Type 1 where
  channelBridge : ChangingNomeCarrierNormalizedConcreteChannelBridge
  rateBand : DynamicVacuumSectorPhysicalRateBand
    changingNomeCarrierNormalizedDynamicFamily

/-- A supplied head-energy product band enters the same-object route without
changing the completed family or its moving-cube channel. -/
def ChangingNomeCarrierNormalizedConcretePhysicalChannelRoute.ofHeadEnergyProductBand
    (band : ChangingNomeCarrierNormalizedHeadEnergyProductBand) :
    ChangingNomeCarrierNormalizedConcretePhysicalChannelRoute where
  channelBridge := changingNomeCarrierNormalizedConcreteChannelBridge
  rateBand := band.toPhysicalRateBand

/-- The same-family rate route contracts to the existing sharp continuum-gap
interface; it does not construct the continuum QFT or OS/GNS passage. -/
def ChangingNomeCarrierNormalizedConcretePhysicalChannelRoute.toContinuumGapTheorem
    (route : ChangingNomeCarrierNormalizedConcretePhysicalChannelRoute) :
    SharpContinuumObligation.ContinuumGapTheorem :=
  route.rateBand.toContinuumGapTheorem

/-- The rate route retains the concrete channel's strict zero-time response. -/
theorem ChangingNomeCarrierNormalizedConcretePhysicalChannelRoute.zero_isPositive
    (route : ChangingNomeCarrierNormalizedConcretePhysicalChannelRoute)
    (scale : Nat) :
    RCIsPositive
      (DynamicVacuumSectorSameObjectRCChannel.connectedAutocorrelation
        route.channelBridge.channel scale 0) :=
  DynamicVacuumSectorSameObjectRCChannel.connectedAutocorrelation_zero_isPositive
    route.channelBridge.channel scale

def ChangingNomeCarrierNormalizedHeadEnergyProductBand.toContinuumGapTheorem
    (band : ChangingNomeCarrierNormalizedHeadEnergyProductBand) :
    SharpContinuumObligation.ContinuumGapTheorem :=
  band.toPhysicalRateBand.toContinuumGapTheorem

/-- Compile the minimal head-energy product certificate into the existing
    same-family denominator band without changing the spacing or denominator.
    The certificate remains uninhabited until the cofinal floor-order estimate
    for `F(w_scale)` is proved. -/
def ChangingNomeHeadEnergyProductBand.toExplicitMarginDenominatorBand
    (band : ChangingNomeHeadEnergyProductBand) :
    changingNomeExplicitMarginDenominatorBand where
  floor := band.floor
  floor_pos := band.floor_pos
  ceiling := band.ceiling
  ceiling_pos := band.ceiling_pos
  lowerDenominator := by
    intro scale
    have htransport :
        (band.floor * changingNomeDynamicFamily.transferSpacing.spacing scale) *
            changingNomeMarginDenominator scale ≈
          (band.floor * changingNomeDynamicFamily.transferSpacing.spacing scale) *
            (Q'.ofNat 2 + Q'.ofNat 6 *
              headEnergyConstant
                (changingNome scale)
                (Q'.le_of_lt (changingNome_pos scale))) :=
      Q'.mul_eqv_congr_left _ _ _
        (changingNomeMarginDenominator_eqv_two_add_six_headEnergy scale)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv htransport)
      (band.lowerHeadEnergy scale)
  upperDenominator := by
    intro scale
    have htransport :
        (band.ceiling * changingNomeDynamicFamily.transferSpacing.spacing scale) *
            changingNomeMarginDenominator scale ≈
          (band.ceiling * changingNomeDynamicFamily.transferSpacing.spacing scale) *
            (Q'.ofNat 2 + Q'.ofNat 6 *
              headEnergyConstant
                (changingNome scale)
                (Q'.le_of_lt (changingNome_pos scale))) :=
      Q'.mul_eqv_congr_left _ _ _
        (changingNomeMarginDenominator_eqv_two_add_six_headEnergy scale)
    exact Q'.le_trans' _ _ _ (band.upperHeadEnergy scale)
      (Q'.le_of_eqv (Q'.eqv_symm htransport))

/-- Once the two specialized inequalities are supplied, the generic compiler
produces the physical-rate band for the same changing family. -/
def changingNomeExplicitMarginDenominatorBand_toPhysicalRateBand
    (band : changingNomeExplicitMarginDenominatorBand) :
    DynamicVacuumSectorPhysicalRateBand changingNomeDynamicFamily :=
  band.toPhysicalRateBand

/-- The specialized product certificate contracts all the way to the sharp
continuum-gap interface.  This is only a conditional compiler: the product
band remains an explicit, currently uninhabited input, and the resulting
`ContinuumGapTheorem` still carries the same changing-family physical gap. -/
def ChangingNomeHeadEnergyProductBand.toContinuumGapTheorem
    (band : ChangingNomeHeadEnergyProductBand) :
    SharpContinuumObligation.ContinuumGapTheorem :=
  (band.toExplicitMarginDenominatorBand).toContinuumGapTheorem

#print axioms changingNomeMarginDenominator
#print axioms changingNomeMarginDenominator_pos
#print axioms changingNomeMarginDenominator_ge_two_add_twelve_scale
#print axioms changingNomeMarginDenominator_eqv_two_add_six_headEnergy
#print axioms ChangingNomeHeadEnergyProductBand.lower_floor_mul_spacing_scale_le_of_scalar
#print axioms changingNomeBandSpacing
#print axioms changingNomeBandFloor
#print axioms changingNomeBandScale
#print axioms changingNomeBandHeadEnergy
#print axioms ChangingNomeHeadEnergyProductBand.lower_floor_mul_spacing_mul_scale_le
#print axioms ChangingNomeHeadEnergyProductBand.spacing_mul_scale_le_of_lower_bound
#print axioms changingNomeBandScale_ge_two
#print axioms changingNomeBand_lower_bound_scale_zero_impossible
#print axioms changingNomeCarrierNormalizedSpacing
#print axioms changingNomeCarrierNormalizedSpacingToZero
#print axioms changingNomeCarrierNormalizedSpacing_le_invSucc
#print axioms changingNomeCarrierNormalizedSpacing_carrier_plus_one_le
#print axioms changingNomeCarrierNormalizedSpacing_carrier_ceiling
#print axioms changingNomeCarrierNormalizedDynamicFamily
#print axioms changingNomeCarrierNormalizedDynamicFamily_same_nome
#print axioms changingNomeCarrierNormalizedDynamicFamily_same_gap_rate
#print axioms changingNomeCarrierNormalizedMovingCubeChannel
#print axioms changingNomeCarrierNormalizedConcreteChannelBridge
#print axioms changingNomeCarrierNormalizedConcreteChannelBridge_zero_isPositive
#print axioms changingNomeCarrierNormalizedConcreteChannelBridge_connectedSq_decay
#print axioms changingNomeCarrierNormalizedMovingCube_zero_isPositive
#print axioms changingNomeCarrierNormalizedMovingCube_connectedSq_decay
#print axioms changingNomeCarrierNormalizedMovingCube_sampled_zero_isPositive
#print axioms changingNomeCarrierNormalizedMovingCube_sampled_eq_global
#print axioms changingNomeCarrierNormalizedMovingCube_sampled_sq_decay
#print axioms changingNomeCarrierNormalizedFinitePrefixResponseCertificate
#print axioms changingNomeCarrierNormalizedFinitePrefixResponseFloor_pos
#print axioms changingNomeCarrierNormalizedFinitePrefixResponseFloor_le_sampled_zeroTime
#print axioms changingNomeCarrierNormalizedFinitePrefixExplicitMarginDenominatorBand
#print axioms changingNomeCarrierNormalizedFinitePrefixPhysicalRateBand
#print axioms changingNomeCarrierNormalizedFinitePrefixConcreteRoute
#print axioms ChangingNomeCarrierNormalizedFinitePrefixConcreteRoute.response_floor_le_zeroTime
#print axioms changingNomeCarrierNormalizedFinitePrefixGapFloor_succ_le
#print axioms changingNomeCarrierNormalizedFinitePrefixGapCeiling_le_succ
#print axioms ChangingNomeCarrierNormalizedCofinalGapCalibration.toPhysicalGapBounds
#print axioms ChangingNomeCarrierNormalizedPhysicalGapBounds.toCofinalGapCalibration
#print axioms ChangingNomeCarrierNormalizedPhysicalGapBounds.toExplicitMarginDenominatorBand
#print axioms ChangingNomeCarrierNormalizedPhysicalGapBounds.toPhysicalRateBand
#print axioms ChangingNomeCarrierNormalizedCofinalGapCalibration.lowerDenominator
#print axioms ChangingNomeCarrierNormalizedCofinalGapCalibration.toPhysicalRateBand
#print axioms changingNomeCarrierNormalizedExplicitMarginInverseLaw
#print axioms ChangingNomeCarrierNormalizedHeadEnergyProductBand.lower_floor_mul_spacing_mul_scale_le
#print axioms ChangingNomeCarrierNormalizedHeadEnergyProductBand.toExplicitMarginDenominatorBand
#print axioms ChangingNomeCarrierNormalizedHeadEnergyProductBand.toPhysicalRateBand
#print axioms ChangingNomeCarrierNormalizedConcretePhysicalChannelRoute.ofHeadEnergyProductBand
#print axioms ChangingNomeCarrierNormalizedConcretePhysicalChannelRoute.toContinuumGapTheorem
#print axioms ChangingNomeCarrierNormalizedConcretePhysicalChannelRoute.zero_isPositive
#print axioms ChangingNomeCarrierNormalizedHeadEnergyProductBand.toContinuumGapTheorem
#print axioms ChangingNomeHeadEnergyProductBand.toExplicitMarginDenominatorBand
#print axioms ChangingNomeHeadEnergyProductBand.toContinuumGapTheorem
#print axioms changingNomeExplicitMarginInverseLaw
#print axioms changingNomeExplicitMarginDenominatorBand_toPhysicalRateBand

end YMGap.Continuum.BF4PhysicalChangingNomeExplicitMarginLaw
