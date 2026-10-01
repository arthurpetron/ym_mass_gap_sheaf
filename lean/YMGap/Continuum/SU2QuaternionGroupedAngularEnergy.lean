/-
# Total angular energy of the computed harmonic groups

The complete signed contribution at each harmonic degree is grouped before
squaring.  Distinct degree groups are orthogonal for the angular Dirichlet
pairing, so their six-plane energies reassemble the angular energy of the
original supported polynomial.  This is a finite Haar identity only.
-/

import YMGap.Continuum.SU2QuaternionGroupedHarmonicNorm
import YMGap.Continuum.QuaternionHaarHarmonicAngularEnergy

namespace YMGap.Continuum.SU2QuaternionGroupedAngularEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionHeadDegreeDifferential
open YMGap.Continuum.SU2QuaternionHaarAngularIBP
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarAngularCasimir
open YMGap.Continuum.SU2QuaternionGroupedHarmonicNorm
open YMGap.Continuum.SU2QuaternionPolynomialHarmonicExpansion
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHeadHomogeneousComponents

local infix:50 " ≈ " => Q'.eqv

def angularPairValue (blocks : Nat) (p q : RatPoly) : Q' :=
  sixValue (fun i j => quaternionHaar blocks
    (polyMul (angularDerivative i j p) (angularDerivative i j q)))

private theorem sixValue_add (f g : Nat → Nat → Q') :
    sixValue (fun i j => f i j + g i j) ≈ sixValue f + sixValue g := by
  unfold sixValue
  exact poly_identity_of_normal_eq
    (.add (.add (.var 0) (.var 6))
      (.add (.add (.var 1) (.var 7))
        (.add (.add (.var 2) (.var 8))
          (.add (.add (.var 3) (.var 9))
            (.add (.add (.var 4) (.var 10)) (.add (.var 5) (.var 11)))))))
    (.add (.add (.var 0) (.add (.var 1) (.add (.var 2)
      (.add (.var 3) (.add (.var 4) (.var 5))))))
      (.add (.var 6) (.add (.var 7) (.add (.var 8)
        (.add (.var 9) (.add (.var 10) (.var 11)))))))
    (by decide) (fun
      | 0 => f 0 1 | 1 => f 0 2 | 2 => f 0 3
      | 3 => f 1 2 | 4 => f 1 3 | 5 => f 2 3
      | 6 => g 0 1 | 7 => g 0 2 | 8 => g 0 3
      | 9 => g 1 2 | 10 => g 1 3 | _ => g 2 3)

private theorem sixValue_neg (f : Nat → Nat → Q') :
    sixValue (fun i j => -(f i j)) ≈ -(sixValue f) := by
  have h (a b c : Q') (hbc : b ≈ -c) : -a+b ≈ -(a+c) :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) hbc)
      (Q'.eqv_symm (Q'.neg_add_eqv a c))
  exact h _ _ _ (h _ _ _ (h _ _ _ (h _ _ _
    (Q'.eqv_symm (Q'.neg_add_eqv (f 1 3) (f 2 3))))))

private theorem angularPairValue_add_left (blocks : Nat) (p q r : RatPoly) :
    angularPairValue blocks (polyAdd p q) r ≈
      angularPairValue blocks p r + angularPairValue blocks q r := by
  have hplane (i j : Nat) : quaternionHaar blocks
      (polyMul (angularDerivative i j (polyAdd p q)) (angularDerivative i j r)) ≈
      quaternionHaar blocks (polyMul (angularDerivative i j p) (angularDerivative i j r)) +
        quaternionHaar blocks (polyMul (angularDerivative i j q) (angularDerivative i j r)) := by
    have hc := (angularDerivative_add i j p q).mul_right (angularDerivative i j r)
    rw [polyMul_add_left_exact] at hc
    exact Q'.eqv_trans _ _ _ (haar_of_coeff hc)
      (quaternionHaar_append blocks _ _)
  exact Q'.eqv_trans _ _ _
    (sixValue_congr _ _ (fun i j _ _ => hplane i j))
    (sixValue_add _ _)

private theorem angularPairValue_add_right (blocks : Nat) (p q r : RatPoly) :
    angularPairValue blocks p (polyAdd q r) ≈
      angularPairValue blocks p q + angularPairValue blocks p r := by
  have hplane (i j : Nat) : quaternionHaar blocks
      (polyMul (angularDerivative i j p) (angularDerivative i j (polyAdd q r))) ≈
      quaternionHaar blocks (polyMul (angularDerivative i j p) (angularDerivative i j q)) +
        quaternionHaar blocks (polyMul (angularDerivative i j p) (angularDerivative i j r)) := by
    have hc := (angularDerivative_add i j q r).mul_left (angularDerivative i j p)
    exact Q'.eqv_trans _ _ _ (haar_of_coeff hc)
      (Q'.eqv_trans _ _ _
        (haar_of_coeff (RatPolyCoeffEqv.mul_add_right _ _ _))
        (quaternionHaar_append blocks _ _))
  exact Q'.eqv_trans _ _ _
    (sixValue_congr _ _ (fun i j _ _ => hplane i j))
    (sixValue_add _ _)

private theorem angularPairValue_zero_left (blocks : Nat) (p : RatPoly) :
    angularPairValue blocks polyZero p ≈ 0 := by
  exact Q'.eqv_trans _ _ _
    (sixValue_congr _ _ (fun i j _ _ =>
      haar_of_coeff (RatPolyCoeffEqv.mul_zero_left (angularDerivative i j p))))
    (by change (sixValue fun _ _ => (0 : Q')) ≈ 0; decide)

private theorem angularPairValue_zero_right (blocks : Nat) (p : RatPoly) :
    angularPairValue blocks p polyZero ≈ 0 := by
  exact Q'.eqv_trans _ _ _
    (sixValue_congr _ _ (fun i j _ _ =>
      haar_of_coeff (RatPolyCoeffEqv.mul_zero_right (angularDerivative i j p))))
    (by change (sixValue fun _ _ => (0 : Q')) ≈ 0; decide)

private theorem angular_pair_ibp (tail : Nat) (p q : RatPoly) :
    angularPairValue (tail+1) p q ≈
      -(quaternionHaar (tail+1) (polyMul p (angularLaplacian q))) := by
  let second := fun i j => quaternionHaar (tail+1)
    (polyMul p (angularDerivative i j (angularDerivative i j q)))
  have hplane (i j : Nat) (hi : i < 4) (hj : j < 4) :
      quaternionHaar (tail+1)
          (polyMul (angularDerivative i j p) (angularDerivative i j q)) ≈
        -(second i j) := by
    have hz := quaternionHaar_weighted_angular tail hi hj p (angularDerivative i j q)
    have he : quaternionHaar (tail+1)
          (polyMul (angularDerivative i j p) (angularDerivative i j q)) + second i j ≈ 0 :=
      Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_append _ _ _)) hz
    apply q_eqv_of_sub_zero
    exact Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq (.add (.var 0) (.neg (.neg (.var 1))))
        (.add (.var 0) (.var 1)) (by decide)
        (fun k => if k = 0 then quaternionHaar (tail+1)
          (polyMul (angularDerivative i j p) (angularDerivative i j q)) else second i j)) he
  exact Q'.eqv_trans _ _ _
    (sixValue_congr _ _ (fun i j hi hj => hplane i j hi hj))
    (Q'.eqv_trans _ _ _ (sixValue_neg second)
      (Q'.neg_eqv_congr _ _ (Q'.eqv_symm (haar_six (tail+1) p _))))

private theorem haar_cross_degree_zero (tail : Nat) {n d : Nat} {p q : RatPoly}
    (hp : HasQuaternionBlockDegree 0 n p)
    (hhp : RatPolyCoeffEqv (headLaplacian p) polyZero)
    (hq : HasQuaternionBlockDegree 0 d q)
    (hhq : RatPolyCoeffEqv (headLaplacian q) polyZero) (hne : n ≠ d) :
    quaternionHaar (tail+1) (polyMul p q) ≈ 0 := by
  have hz := harmonic_cross_degree hp hhp hq hhq hne
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_partialHaarHead tail _))
    (haar_of_coeff hz)

private theorem angularPairValue_cross_degree_zero (tail : Nat) {n d : Nat}
    {p q : RatPoly} (hp : HasQuaternionBlockDegree 0 n p)
    (hhp : RatPolyCoeffEqv (headLaplacian p) polyZero)
    (hq : HasQuaternionBlockDegree 0 d q)
    (hhq : RatPolyCoeffEqv (headLaplacian q) polyZero) (hne : n ≠ d) :
    angularPairValue (tail+1) p q ≈ 0 := by
  let eigenvalue := Q'.ofNat d * (Q'.ofNat d + 2)
  have hzero := haar_cross_degree_zero tail hp hhp hq hhq hne
  have hscale : quaternionHaar (tail+1) (polyMul p (polySmul (-eigenvalue) q)) ≈ 0 :=
    Q'.eqv_trans _ _ _
      (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_right (-eigenvalue) p q))
      (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul (tail+1) (-eigenvalue) _)
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hzero)
          (Q'.mul_zero_eqv _)))
  have hlap : quaternionHaar (tail+1) (polyMul p (angularLaplacian q)) ≈ 0 :=
    Q'.eqv_trans _ _ _
      (harmonic_angularLaplacian (Nat.zero_lt_succ tail) q hq hhq p) hscale
  exact Q'.eqv_trans _ _ _ (angular_pair_ibp tail p q)
    (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ hlap) (by decide))

private theorem pair_sum_right_zero (tail n : Nat) (f : Nat → RatPoly)
    (hf : ∀ d, HasQuaternionBlockDegree 0 d (f d))
    (hh : ∀ d, RatPolyCoeffEqv (headLaplacian (f d)) polyZero) :
    ∀ ids : List Nat, n ∉ ids →
      angularPairValue (tail+1) (f n) (polySum (ids.map f)) ≈ 0
  | [], _ => angularPairValue_zero_right _ _
  | d::ds, hn => Q'.eqv_trans _ _ _
      (angularPairValue_add_right _ _ _ _)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (angularPairValue_cross_degree_zero tail (hf n) (hh n) (hf d) (hh d)
            (fun h => hn (h ▸ List.mem_cons_self)))
          (pair_sum_right_zero tail n f hf hh ds
            (fun h => hn (List.mem_cons_of_mem d h))))
        (q_add_zero_eqv 0))

private theorem pair_sum_left_zero (tail n : Nat) (f : Nat → RatPoly)
    (hf : ∀ d, HasQuaternionBlockDegree 0 d (f d))
    (hh : ∀ d, RatPolyCoeffEqv (headLaplacian (f d)) polyZero) :
    ∀ ids : List Nat, n ∉ ids →
      angularPairValue (tail+1) (polySum (ids.map f)) (f n) ≈ 0
  | [], _ => angularPairValue_zero_left _ _
  | d::ds, hn => Q'.eqv_trans _ _ _
      (angularPairValue_add_left _ _ _ _)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (angularPairValue_cross_degree_zero tail (hf d) (hh d) (hf n) (hh n)
            (fun h => hn (h.symm ▸ List.mem_cons_self)))
          (pair_sum_left_zero tail n f hf hh ds
            (fun h => hn (List.mem_cons_of_mem d h))))
        (q_add_zero_eqv 0))

private theorem pair_norm_sum (tail : Nat) (f : Nat → RatPoly)
    (hf : ∀ d, HasQuaternionBlockDegree 0 d (f d))
    (hh : ∀ d, RatPolyCoeffEqv (headLaplacian (f d)) polyZero) :
    ∀ ids : List Nat, ids.Nodup →
      angularPairValue (tail+1) (polySum (ids.map f)) (polySum (ids.map f)) ≈
        qListSum (ids.map fun d => angularPairValue (tail+1) (f d) (f d))
  | [], _ => angularPairValue_zero_left _ _
  | n::ns, hids => by
      have hn := (List.nodup_cons.mp hids).1
      have hs := (List.nodup_cons.mp hids).2
      let s := polySum (ns.map f)
      have hr := pair_sum_right_zero tail n f hf hh ns hn
      have hl := pair_sum_left_zero tail n f hf hh ns hn
      exact Q'.eqv_trans _ _ _ (angularPairValue_add_left _ _ _ _)
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr' (angularPairValue_add_right _ _ _ _)
            (angularPairValue_add_right _ _ _ _))
          (Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr'
              (Q'.add_eqv_congr' (Q'.eqv_refl _) hr)
              (Q'.add_eqv_congr' hl (pair_norm_sum tail f hf hh ns hs)))
            (poly_identity_of_normal_eq
              (.add (.add (.var 0) (.const 0)) (.add (.const 0) (.var 1)))
              (.add (.var 0) (.var 1)) (by decide)
              (fun k => if k = 0 then angularPairValue (tail+1) (f n) (f n)
                else qListSum (ns.map fun d => angularPairValue (tail+1) (f d) (f d))))))

private theorem angularSquare_carrier {blocks : Nat} (hb : 0 < blocks)
    {p q : RatPoly} (h : HaarCarrierEqv blocks p q) :
    HaarCarrierEqv blocks (angularSquare p) (angularSquare q) := by
  have hd (i j : Nat) (hi : i < 4) (hj : j < 4) :=
    angularDerivative_carrier hb hi hj h
  exact HaarCarrierEqv.add (HaarCarrierEqv.mul (hd 0 1 (by decide) (by decide)) (hd 0 1 (by decide) (by decide)))
    (HaarCarrierEqv.add (HaarCarrierEqv.mul (hd 0 2 (by decide) (by decide)) (hd 0 2 (by decide) (by decide)))
      (HaarCarrierEqv.add (HaarCarrierEqv.mul (hd 0 3 (by decide) (by decide)) (hd 0 3 (by decide) (by decide)))
        (HaarCarrierEqv.add (HaarCarrierEqv.mul (hd 1 2 (by decide) (by decide)) (hd 1 2 (by decide) (by decide)))
          (HaarCarrierEqv.add (HaarCarrierEqv.mul (hd 1 3 (by decide) (by decide)) (hd 1 3 (by decide) (by decide)))
            (HaarCarrierEqv.mul (hd 2 3 (by decide) (by decide)) (hd 2 3 (by decide) (by decide)))))))

private theorem angularSquare_pairValue (blocks : Nat) (p : RatPoly) :
    quaternionHaar blocks (angularSquare p) ≈ angularPairValue blocks p p := by
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (haar_of_coeff (RatPolyCoeffEqv.one_mul _)))
    (Q'.eqv_trans _ _ _ (haar_six blocks polyOne _)
      (sixValue_congr _ _ (fun _ _ _ _ => haar_of_coeff (RatPolyCoeffEqv.one_mul _))))

private theorem qListSum_pairValue (blocks : Nat) (f : Nat → RatPoly) :
    ∀ ids : List Nat,
    qListSum (ids.map fun d => angularPairValue blocks (f d) (f d)) ≈
      qListSum (ids.map fun d => quaternionHaar blocks (angularSquare (f d)))
  | [] => Q'.eqv_refl _
  | d::ds => Q'.add_eqv_congr' (Q'.eqv_symm (angularSquare_pairValue blocks (f d)))
      (qListSum_pairValue blocks f ds)

/-- Angular Pythagoras for a carrier represented by any finite collection of
distinct harmonic degrees. Scalar weights may be included in the harmonics;
within-degree cross terms are never discarded. This supplies the output-side
energy identity for the actual heat-smoothed polynomial. -/
theorem carrier_harmonic_sum_angular_energy (tail : Nat) (p : RatPoly)
    (f : Nat → RatPoly)
    (hf : ∀ d, HasQuaternionBlockDegree 0 d (f d))
    (hh : ∀ d, RatPolyCoeffEqv (headLaplacian (f d)) polyZero)
    (ids : List Nat) (hids : ids.Nodup)
    (hc : HaarCarrierEqv (tail+1) p (polySum (ids.map f))) :
    quaternionHaar (tail+1) (angularSquare p) ≈
      qListSum (ids.map fun d => quaternionHaar (tail+1) (angularSquare (f d))) :=
  Q'.eqv_trans _ _ _ (haar_of_carrier (angularSquare_carrier (by omega) hc))
    (Q'.eqv_trans _ _ _ (angularSquare_pairValue (tail+1) _)
      (Q'.eqv_trans _ _ _ (pair_norm_sum tail f hf hh ids hids)
        (qListSum_pairValue (tail+1) f ids)))

/-- The original polynomial's complete six-plane energy is exactly the sum of
the energies of its complete signed harmonic-degree groups. -/
theorem polynomial_angular_energy (tail : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    quaternionHaar (tail+1) (angularSquare p) ≈
      qListSum ((headDegrees (sumHarmonics (modes (tail+1) (by omega) p))).map fun d =>
        quaternionHaar (tail+1)
          (angularSquare (grouped d (modes (tail+1) (by omega) p)))) := by
  let ms := modes (tail+1) (by omega) p
  let f := fun d => grouped d ms
  let ids := headDegrees (sumHarmonics ms)
  have hc : HaarCarrierEqv (tail+1) p (polySum (ids.map f)) :=
    (polynomial_harmonic_carrier (by omega : 0 < tail+1) p hp).trans
      (RatPolyCoeffEqv.haarCarrier (headComponent_reassembly (sumHarmonics ms)).symm)
  exact Q'.eqv_trans _ _ _ (haar_of_carrier (angularSquare_carrier (by omega) hc))
    (Q'.eqv_trans _ _ _ (angularSquare_pairValue (tail+1) _)
      (Q'.eqv_trans _ _ _
        (pair_norm_sum tail f (fun d => grouped_degree d ms)
          (fun d => grouped_harmonic d ms) ids
          (YMGap.Continuum.CayleyParentInj.range_nodup _))
        (qListSum_pairValue (tail+1) f ids)))

end YMGap.Continuum.SU2QuaternionGroupedAngularEnergy

#print axioms YMGap.Continuum.SU2QuaternionGroupedAngularEnergy.polynomial_angular_energy
#print axioms YMGap.Continuum.SU2QuaternionGroupedAngularEnergy.carrier_harmonic_sum_angular_energy
