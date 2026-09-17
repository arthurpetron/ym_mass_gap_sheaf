/-
# The exact fundamental corner packet

Two symbolic shared-link Schur contractions retain the six-link boundary
and the original scalar probe. Unit cancellations hold in the Haar ideal,
not in the free polynomial algebra. This is a bare nine-link moment; the
separate full-action packet selection must retain all cutoff terms.
-/

import YMGap.Continuum.SU2QuaternionAdjacentPlaquetteGluing
import YMGap.Continuum.SU2QuaternionOrientedWordSelection
import YMGap.Continuum.SU2QuaternionHaarGaugeCancellation
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeHaarEndpoint

namespace YMGap.Continuum.SU2QuaternionCornerFundamentalMoment

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeHaarEndpoint
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPartialSphereGaussian
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionHeadLinearHaar
open YMGap.Continuum.SU2QuaternionAdjacentPlaquetteGluing
open YMGap.Continuum.SU2QuaternionOrientedWordSelection
open YMGap.Continuum.SU2QuaternionHaarGaugeCancellation
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionSolidZonalGaussianTransport
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry (character_supported)

local infix:50 " ≈ " => Q'.eqv
local infixl:70 " ⋄ " => PolyQuaternion.mul
local prefix:80 "bar " => PolyQuaternion.conj
private abbrev q (i : Nat) := PolyQuaternion.coordinateVariable i
private abbrev chi (p : PolyQuaternion) := characterPolynomial p.scalar 1

def face01 : PolyQuaternion := word 0 3 2 1 false false true true
def face02 : PolyQuaternion := word 0 6 5 4 false false true true
def face12 : PolyQuaternion := word 1 8 7 4 false false true true

def hexQuaternion : PolyQuaternion :=
  ((((q 3 ⋄ bar (q 2)) ⋄ q 8) ⋄ bar (q 7)) ⋄ q 5) ⋄ bar (q 6)
def hex : RatPoly := characterPolynomial hexQuaternion.scalar 1
def probe : RatPoly := polyVar 16
def insertion : RatPoly := polyMul hex (polyMul probe probe)
def bareProduct : RatPoly := polyMul (chi face01)
  (polyMul (chi face02) (polyMul (chi face12) insertion))

private theorem coeff_haar (blocks : Nat) {p r : RatPoly} (h : RatPolyCoeffEqv p r) :
    quaternionHaar blocks p ≈ quaternionHaar blocks r :=
  QuaternionHaarCarrierEqv.haar (RatPolyCoeffEqv.haarCarrier h)

private theorem chi_congr {p r : PolyQuaternion} (h : PolyQuaternionCoeffEqv p r) :
    RatPolyCoeffEqv (chi p) (chi r) := h.scalar.smul 2

private theorem chi_cycle (p r : PolyQuaternion) :
    RatPolyCoeffEqv (chi (p ⋄ r)) (chi (r ⋄ p)) :=
  (polyQuaternion_mul_scalar_cyclic p r).smul 2

private theorem chi_cycle_three (p r s : PolyQuaternion) :
    RatPolyCoeffEqv (chi ((p ⋄ r) ⋄ s)) (chi (r ⋄ (s ⋄ p))) :=
  (chi_cycle (p ⋄ r) s).trans
    ((chi_congr (PolyQuaternionCoeffEqv.mul_assoc s p r).symm).trans
      (chi_cycle (s ⋄ p) r))

private theorem double_conj (p : PolyQuaternion) :
    PolyQuaternionCoeffEqv (bar (bar p)) p := by
  have hn (r : RatPoly) : RatPolyCoeffEqv (polyNeg (polyNeg r)) r :=
    coeffEvalExpr_eqv_of_normalize_eq (.neg (.neg (.var 0))) (.var 0)
      (by decide) (fun _ => r)
  exact ⟨.refl _, hn _, hn _, hn _⟩

private theorem lift_smul (c : Q') (p : RatPoly) :
    liftHead (polySmul c p) = polySmul c (liftHead p) := by
  simp only [liftHead, polySmul, List.map_map]
  rfl

private theorem lift_chi (p : PolyQuaternion) :
    liftHead (chi p) = chi (liftQuaternion p) := lift_smul 2 _

private theorem head_inverse (p : PolyQuaternion) :
    RatPolyCoeffEqv (chi (q 0 ⋄ liftQuaternion p))
      (chi (bar (q 0) ⋄ liftQuaternion (bar p))) := by
  rw [lift_conj]
  exact (chi_congr (conjugate_product (q 0) (liftQuaternion p))).trans
    (chi_cycle (bar (liftQuaternion p)) (bar (q 0)))

private theorem schur_boundary (blocks : Nat) (p r : PolyQuaternion) (s : RatPoly) :
    quaternionHaar (blocks+1) (polyMul
      (polyMul (chi (liftQuaternion p ⋄ q 0)) (chi (bar (q 0) ⋄ liftQuaternion r)))
      (liftHead s)) ≈ schurFactor * quaternionHaar blocks (polyMul (chi (p ⋄ r)) s) := by
  have hf := quaternionHaar_polyMul_headIndependent blocks
    (polyMul (chi (liftQuaternion p ⋄ q 0)) (chi (bar (q 0) ⋄ liftQuaternion r))) (liftHead s)
    (headIndependentCheck_sound (liftHead_independent s))
  rw [drop_liftHead] at hf
  exact Q'.eqv_trans _ _ _ hf (Q'.eqv_trans _ _ _
    (coeff_haar blocks (((path_schur p r).mul_right s).trans
      (RatPolyCoeffEqv.polyMul_smul_left _ _ _))) (quaternionHaar_polySmul _ _ _))

private theorem same_head_boundary (blocks : Nat) (p r : PolyQuaternion) (s : RatPoly) :
    quaternionHaar (blocks+1) (polyMul
      (polyMul (chi (q 0 ⋄ liftQuaternion p)) (chi (q 0 ⋄ liftQuaternion r)))
      (liftHead s)) ≈ schurFactor * quaternionHaar blocks (polyMul (chi (p ⋄ bar r)) s) :=
  Q'.eqv_trans _ _ _
    (coeff_haar _ (((chi_cycle (q 0) (liftQuaternion p)).mul (head_inverse r)).mul_right _))
    (schur_boundary blocks p (bar r) s)

private theorem second_pair (u v z g : PolyQuaternion) :
    RatPolyCoeffEqv
      (polyMul (chi ((liftQuaternion u ⋄ bar (q 0)) ⋄
          bar (liftQuaternion v ⋄ bar (liftQuaternion g))))
        (chi ((q 0 ⋄ liftQuaternion z) ⋄ bar (liftQuaternion g))))
      (polyMul (chi (liftQuaternion (z ⋄ bar g) ⋄ q 0))
        (chi (bar (q 0) ⋄ liftQuaternion ((g ⋄ bar v) ⋄ u)))) := by
  have hc := (conjugate_product (liftQuaternion v) (bar (liftQuaternion g))).trans
    ((double_conj (liftQuaternion g)).mul (.refl _))
  have hleft := (chi_congr ((PolyQuaternionCoeffEqv.refl _).mul hc)).trans
    (chi_cycle_three (liftQuaternion u) (bar (q 0))
      (liftQuaternion g ⋄ bar (liftQuaternion v)))
  have hright := (chi_congr (PolyQuaternionCoeffEqv.mul_assoc
    (q 0) (liftQuaternion z) (bar (liftQuaternion g)))).trans
    (chi_cycle (q 0) (liftQuaternion z ⋄ bar (liftQuaternion g)))
  simp only [lift_mul, lift_conj]
  exact (hleft.mul hright).trans (RatPolyCoeffEqv.mul_comm _ _)

private theorem triangle_cancel (blocks : Nat) (u v z g : PolyQuaternion)
    (hg : HaarCarrierEqv blocks (polyQuaternionNorm g) polyOne) :
    HaarCarrierEqv blocks (chi ((z ⋄ bar g) ⋄ ((g ⋄ bar v) ⋄ u)))
      (chi ((u ⋄ z) ⋄ bar v)) := by
  have lift {p r : PolyQuaternion} (h : PolyQuaternionCoeffEqv p r) :
      PolyQuaternionHaarCarrierEqv blocks p r := .of_coeff h
  have ref (p : PolyQuaternion) : PolyQuaternionHaarCarrierEqv blocks p p := .refl _ _
  have hc : PolyQuaternionHaarCarrierEqv blocks
      ((z ⋄ bar g) ⋄ (g ⋄ bar v)) (z ⋄ bar v) := by
    refine (lift (PolyQuaternionCoeffEqv.mul_assoc z (bar g) (g ⋄ bar v))).trans ?_
    apply (ref z).mul
    exact (lift (PolyQuaternionCoeffEqv.mul_assoc (bar g) g (bar v)).symm).trans
      (((haarUnit_conj_mul hg).mul (ref (bar v))).trans
        (lift (PolyQuaternionCoeffEqv.one_mul (bar v))))
  have h := (lift (PolyQuaternionCoeffEqv.mul_assoc
    (z ⋄ bar g) (g ⋄ bar v) u).symm).trans (hc.mul (ref u))
  exact (character_haar_congr h.scalar 1).trans
    (RatPolyCoeffEqv.haarCarrier ((chi_cycle (z ⋄ bar v) u).trans
      (chi_congr (PolyQuaternionCoeffEqv.mul_assoc u z (bar v)).symm)))

private def corner (u v z g : PolyQuaternion) (s : RatPoly) : RatPoly :=
  let p := liftQuaternion u ⋄ bar (q 0)
  let r := liftQuaternion v ⋄ bar (liftQuaternion g)
  let t := chi ((q 0 ⋄ liftQuaternion z) ⋄ bar (liftQuaternion g))
  polyMul (polyMul (chi (q 0 ⋄ liftQuaternion p)) (chi (q 0 ⋄ liftQuaternion r)))
    (liftHead (polyMul t (liftHead s)))

private theorem corner_contraction (blocks : Nat) (u v z g : PolyQuaternion)
    (hg : HaarCarrierEqv blocks (polyQuaternionNorm g) polyOne) (s : RatPoly) :
    quaternionHaar (blocks+2) (corner u v z g s) ≈
      schurFactor * (schurFactor * quaternionHaar blocks (polyMul (chi ((u ⋄ z) ⋄ bar v)) s)) := by
  have h1 := same_head_boundary (blocks+1)
    (liftQuaternion u ⋄ bar (q 0))
    (liftQuaternion v ⋄ bar (liftQuaternion g))
    (polyMul (chi ((q 0 ⋄ liftQuaternion z) ⋄ bar (liftQuaternion g))) (liftHead s))
  have h2 := coeff_haar (blocks+1)
    ((RatPolyCoeffEqv.mul_assoc _ _ (liftHead s)).symm.trans
      ((second_pair u v z g).mul_right (liftHead s)))
  have h3 := schur_boundary blocks (z ⋄ bar g) ((g ⋄ bar v) ⋄ u) s
  have h4 : quaternionHaar blocks (polyMul (chi ((z ⋄ bar g) ⋄ ((g ⋄ bar v) ⋄ u))) s) ≈
      quaternionHaar blocks (polyMul (chi ((u ⋄ z) ⋄ bar v)) s) :=
    QuaternionHaarCarrierEqv.haar
      (HaarCarrierEqv.mul (triangle_cancel blocks u v z g hg) (HaarCarrierEqv.refl blocks s))
  exact Q'.eqv_trans _ _ _ h1 (Q'.mul_eqv_congr_left _ _ _
    (Q'.eqv_trans _ _ _ h2 (Q'.eqv_trans _ _ _ h3
      (Q'.mul_eqv_congr_left _ _ _ h4))))

private theorem square_boundary (blocks : Nat) (p : PolyQuaternion)
    (hp : HaarCarrierEqv blocks (polyQuaternionNorm p) polyOne) (s : RatPoly) :
    quaternionHaar (blocks+1) (polyMul
      (polyMul (chi (bar (q 0) ⋄ liftQuaternion p)) (chi (bar (q 0) ⋄ liftQuaternion p)))
      (liftHead s)) ≈ quaternionHaar blocks s := by
  have hc : RatPolyCoeffEqv (chi (bar (q 0) ⋄ liftQuaternion p))
      (chi (liftQuaternion (bar p) ⋄ q 0)) := by
    rw [lift_conj]
    exact (chi_congr (conjugate_product (bar (q 0)) (liftQuaternion p))).trans
      (chi_congr ((PolyQuaternionCoeffEqv.refl _).mul (double_conj (q 0))))
  have h1 := coeff_haar (blocks+1)
    ((hc.mul (.refl (chi (bar (q 0) ⋄ liftQuaternion p)))).mul_right (liftHead s))
  have h2 := schur_boundary blocks (bar p) p s
  have hu := character_haar_congr (haarUnit_conj_mul hp).scalar 1
  have h3 := QuaternionHaarCarrierEqv.haar
    (HaarCarrierEqv.mul hu (HaarCarrierEqv.refl blocks s))
  have h4 : quaternionHaar blocks (polyMul (chi PolyQuaternion.one) s) ≈
      2 * quaternionHaar blocks s :=
    Q'.eqv_trans _ _ _ (coeff_haar blocks
      ((RatPolyCoeffEqv.polyMul_smul_left 2 polyOne s).trans
        ((RatPolyCoeffEqv.one_mul s).smul 2))) (quaternionHaar_polySmul _ _ _)
  exact Q'.eqv_trans _ _ _ h1 (Q'.eqv_trans _ _ _ h2
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _ h3 h4))
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
          (by decide : schurFactor * 2 ≈ (1 : Q'))) (Q'.one_mul_eqv _)))))

private def tailU : PolyQuaternion := q 1 ⋄ bar (q 0)
private def tailV : PolyQuaternion := q 4 ⋄ bar (q 3)
private def tailZ : PolyQuaternion := q 6 ⋄ bar (q 5)
private def tailG : PolyQuaternion := q 2
private def tailHex : PolyQuaternion :=
  ((((q 1 ⋄ bar (q 0)) ⋄ q 6) ⋄ bar (q 5)) ⋄ q 3) ⋄ bar (q 4)
private def tailProbe : RatPoly := polyVar 8
private def tailInsertion : RatPoly := polyMul (chi tailHex) (polyMul tailProbe tailProbe)

private theorem tail_hex_pin :
    PolyQuaternionCoeffEqv ((tailU ⋄ tailZ) ⋄ bar tailV) tailHex := by
  have hv : PolyQuaternionCoeffEqv (bar tailV) (q 3 ⋄ bar (q 4)) :=
    (conjugate_product (q 4) (bar (q 3))).trans
      ((double_conj (q 3)).mul (.refl _))
  have hz := (PolyQuaternionCoeffEqv.mul_assoc tailU (q 6) (bar (q 5))).symm
  exact ((PolyQuaternionCoeffEqv.refl _).mul hv).trans
    ((PolyQuaternionCoeffEqv.mul_assoc (tailU ⋄ tailZ) (q 3) (bar (q 4))).symm.trans
      ((hz.mul (.refl _)).mul (.refl _)))

private theorem source_pin : RatPolyCoeffEqv bareProduct
    (corner tailU tailV tailZ tailG tailInsertion) := by
  have hu : liftQuaternion (liftQuaternion tailU) = q 3 ⋄ bar (q 2) := by
    unfold tailU
    rw [lift_mul, lift_conj, lift_mul, lift_conj]
    rfl
  have hv : liftQuaternion (liftQuaternion tailV) = q 6 ⋄ bar (q 5) := by
    unfold tailV
    rw [lift_mul, lift_conj, lift_mul, lift_conj]
    rfl
  have hz : liftQuaternion (liftQuaternion tailZ) = q 8 ⋄ bar (q 7) := by
    unfold tailZ
    rw [lift_mul, lift_conj, lift_mul, lift_conj]
    rfl
  have hg : liftQuaternion (liftQuaternion tailG) = q 4 := rfl
  have hh : liftHead (liftHead (chi tailHex)) = hex := by
    rw [lift_chi, lift_chi]
    unfold tailHex
    simp only [lift_mul, lift_conj]
    rfl
  have hs : liftHead (liftHead tailInsertion) = insertion := by
    simp only [tailInsertion, liftHead_mul, hh]
    rfl
  have hfour (a b c d : PolyQuaternion) :
      PolyQuaternionCoeffEqv (((a ⋄ b) ⋄ c) ⋄ d) (a ⋄ ((b ⋄ c) ⋄ d)) :=
    ((PolyQuaternionCoeffEqv.mul_assoc a b c).mul (.refl d)).trans
      (PolyQuaternionCoeffEqv.mul_assoc a (b ⋄ c) d)
  have h01 := chi_congr (hfour (q 0) (q 3) (bar (q 2)) (bar (q 1)))
  have h02 := chi_congr (hfour (q 0) (q 6) (bar (q 5)) (bar (q 4)))
  have h12 := chi_congr ((PolyQuaternionCoeffEqv.mul_assoc
    (q 1) (q 8) (bar (q 7))).mul (.refl (bar (q 4))))
  unfold corner
  simp only [liftHead_mul, lift_chi, lift_mul, lift_conj, hu, hv, hz, hg, hs]
  change RatPolyCoeffEqv
    (polyMul (chi face01) (polyMul (chi face02) (polyMul (chi face12) insertion)))
    (polyMul (polyMul (chi (q 0 ⋄ ((q 3 ⋄ bar (q 2)) ⋄ bar (q 1))))
      (chi (q 0 ⋄ ((q 6 ⋄ bar (q 5)) ⋄ bar (q 4)))))
      (polyMul (chi ((q 1 ⋄ (q 8 ⋄ bar (q 7))) ⋄ bar (q 4))) insertion))
  exact (h01.mul (h02.mul (h12.mul (.refl insertion)))).trans
    (RatPolyCoeffEqv.mul_assoc _ _ _).symm

private def lastPath : PolyQuaternion :=
  (((q 5 ⋄ bar (q 4)) ⋄ q 2) ⋄ bar (q 3)) ⋄ q 0

private theorem last_path_pin : RatPolyCoeffEqv (chi tailHex)
    (chi (bar (q 0) ⋄ liftQuaternion lastPath)) := by
  have hp : liftQuaternion lastPath =
      (((q 6 ⋄ bar (q 5)) ⋄ q 3) ⋄ bar (q 4)) ⋄ q 1 := by
    unfold lastPath
    simp only [lift_mul, lift_conj]
    rfl
  rw [hp]
  let t := ((q 6 ⋄ bar (q 5)) ⋄ q 3) ⋄ bar (q 4)
  have regroup : PolyQuaternionCoeffEqv tailHex ((q 1 ⋄ bar (q 0)) ⋄ t) :=
    (PolyQuaternionCoeffEqv.mul_assoc ((q 1 ⋄ bar (q 0)) ⋄ q 6) (bar (q 5)) (q 3)).mul
      (.refl (bar (q 4))) |>.trans
        (((PolyQuaternionCoeffEqv.mul_assoc (q 1 ⋄ bar (q 0)) (q 6)
          (bar (q 5) ⋄ q 3)).mul (.refl (bar (q 4)))).trans
          ((PolyQuaternionCoeffEqv.mul_assoc (q 1 ⋄ bar (q 0))
            (q 6 ⋄ (bar (q 5) ⋄ q 3)) (bar (q 4))).trans
              ((PolyQuaternionCoeffEqv.refl _).mul
                ((PolyQuaternionCoeffEqv.mul_assoc (q 6) (bar (q 5)) (q 3)).symm.mul
                  (.refl (bar (q 4)))))))
  exact (chi_congr regroup).trans (chi_cycle_three (q 1) (bar (q 0)) t)

private theorem coord_unit {blocks i : Nat} (hi : i < blocks) :
    HaarCarrierEqv blocks (polyQuaternionNorm (q i)) polyOne := haarNorm_coordinate hi

private theorem conj_unit {blocks : Nat} {p : PolyQuaternion}
    (hp : HaarCarrierEqv blocks (polyQuaternionNorm p) polyOne) :
    HaarCarrierEqv blocks (polyQuaternionNorm (bar p)) polyOne :=
  (RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_conj p)).trans hp

private theorem last_path_unit : HaarCarrierEqv 6 (polyQuaternionNorm lastPath) polyOne :=
  haarNorm_mul (haarNorm_mul (haarNorm_mul (haarNorm_mul
    (coord_unit (by decide : 5 < 6)) (conj_unit (coord_unit (by decide : 4 < 6))))
    (coord_unit (by decide : 2 < 6))) (conj_unit (coord_unit (by decide : 3 < 6))))
    (coord_unit (by decide : 0 < 6))

private theorem tail_moment :
    quaternionHaar 7 (polyMul (chi tailHex) tailInsertion) ≈ quarter := by
  have hlift : liftHead (polyMul (polyVar 4) (polyVar 4)) =
      polyMul tailProbe tailProbe := by rw [liftHead_mul]; rfl
  have hpin : RatPolyCoeffEqv (polyMul (chi tailHex) tailInsertion)
      (polyMul (polyMul (chi (bar (q 0) ⋄ liftQuaternion lastPath))
        (chi (bar (q 0) ⋄ liftQuaternion lastPath)))
          (liftHead (polyMul (polyVar 4) (polyVar 4)))) := by
    rw [hlift]
    exact (RatPolyCoeffEqv.mul_assoc _ _ _).symm.trans
      ((last_path_pin.mul last_path_pin).mul_right _)
  exact Q'.eqv_trans _ _ _ (coeff_haar 7 hpin)
    (Q'.eqv_trans _ _ _ (square_boundary 6 lastPath last_path_unit
      (polyMul (polyVar 4) (polyVar 4))) (by decide))

/-- Exact nine-block value; only the last one-coordinate square is reduced
arithmetically. The large word is contracted symbolically. -/
theorem bare_moment : quaternionHaar 9 bareProduct ≈ Q'.mkPos 1 16 (by decide) := by
  have h1 := corner_contraction 7 tailU tailV tailZ tailG
    (coord_unit (by decide : 2 < 7)) tailInsertion
  have h2 := coeff_haar 7 ((chi_congr tail_hex_pin).mul_right tailInsertion)
  exact Q'.eqv_trans _ _ _ (coeff_haar 9 source_pin)
    (Q'.eqv_trans _ _ _ h1 (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ h2 tail_moment))) (by decide)))

theorem hexQuaternion_supported : Supported 9 hexQuaternion :=
  (((((Supported.coordinate (by decide : 3 < 9)).mul
    (Supported.coordinate (by decide : 2 < 9)).conj).mul
    (Supported.coordinate (by decide : 8 < 9))).mul
    (Supported.coordinate (by decide : 7 < 9)).conj).mul
    (Supported.coordinate (by decide : 5 < 9))).mul
    (Supported.coordinate (by decide : 6 < 9)).conj

theorem hexQuaternion_unit : HaarCarrierEqv 9 (polyQuaternionNorm hexQuaternion) polyOne :=
  haarNorm_mul (haarNorm_mul (haarNorm_mul (haarNorm_mul (haarNorm_mul
    (coord_unit (by decide : 3 < 9)) (conj_unit (coord_unit (by decide : 2 < 9))))
    (coord_unit (by decide : 8 < 9))) (conj_unit (coord_unit (by decide : 7 < 9))))
    (coord_unit (by decide : 5 < 9))) (conj_unit (coord_unit (by decide : 6 < 9)))

theorem bare_supported : SupportedQuaternionBlocks 9 bareProduct := by
  have hp : SupportedQuaternionBlocks 9 probe :=
    (Supported.coordinate (by decide : 4 < 9)).scalar
  exact supported_polyMul
    (word_supported (by decide : 0 < 9) (by decide : 3 < 9)
      (by decide : 2 < 9) (by decide : 1 < 9) false false true true 1)
    (supported_polyMul
      (word_supported (by decide : 0 < 9) (by decide : 6 < 9)
        (by decide : 5 < 9) (by decide : 4 < 9) false false true true 1)
      (supported_polyMul
        (word_supported (by decide : 1 < 9) (by decide : 8 < 9)
          (by decide : 7 < 9) (by decide : 4 < 9) false false true true 1)
        (supported_polyMul (character_supported hexQuaternion_supported.scalar 1)
          (supported_polyMul hp hp))))

/-- Additional unused links integrate to one on the unchanged polynomial. -/
theorem bare_moment_extended (blocks : Nat) (hb : 9 ≤ blocks) :
    quaternionHaar blocks bareProduct ≈ Q'.mkPos 1 16 (by decide) :=
  Q'.eqv_trans _ _ _ (quaternionHaar_extend_supported_endpoint hb bareProduct bare_supported)
    bare_moment

end YMGap.Continuum.SU2QuaternionCornerFundamentalMoment

#print axioms YMGap.Continuum.SU2QuaternionCornerFundamentalMoment.bare_moment
#print axioms YMGap.Continuum.SU2QuaternionCornerFundamentalMoment.hexQuaternion_supported
#print axioms YMGap.Continuum.SU2QuaternionCornerFundamentalMoment.hexQuaternion_unit
#print axioms YMGap.Continuum.SU2QuaternionCornerFundamentalMoment.bare_supported
#print axioms YMGap.Continuum.SU2QuaternionCornerFundamentalMoment.bare_moment_extended
