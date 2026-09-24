/-
# A computed one-block harmonic tail and its weighted Casimir bound

This leaf filters the existing constructive Fischer expansion by harmonic
degree.  The tail norm keeps the complete within-degree sums and an arbitrary
certified head-independent background.  Weighted cross-degree orthogonality
and finite reassembly pay its spectral threshold with the actual head angular
energy of the original polynomial.

No joint projector, product-heat identification, or multi-block estimate is
asserted here.
-/

import YMGap.Continuum.SU2QuaternionGroupedHeatComparison
import YMGap.Continuum.SU2QuaternionGroupedAngularEnergy
import YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct

namespace YMGap.Continuum.SU2QuaternionGroupedHarmonicTail

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
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionHeadDegreeDifferential
open YMGap.Continuum.SU2QuaternionHaarAngularIBP
open YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionFischerDecomposition
open YMGap.Continuum.SU2QuaternionPolynomialHarmonicExpansion
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionHeadHomogeneousComponents
open YMGap.Continuum.SU2QuaternionGroupedHarmonicNorm
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarAngularCasimir
open YMGap.Continuum.QuaternionHaarHarmonicAngularEnergy
open YMGap.Continuum.QuaternionHaarAngularCarrier

local infix:50 " ≈ " => Q'.eqv

/-- The computed harmonic degrees strictly above `L`. -/
def highDegrees (blocks : Nat) (hb : 0 < blocks) (L : Nat) (p : RatPoly) : List Nat :=
  (headDegrees (sumHarmonics (modes blocks hb p))).filter (fun d => decide (L < d))

/-- The actual polynomial obtained by retaining all computed groups above `L`.
Cross terms within each degree remain in `grouped`. -/
def spectralHighPart (blocks : Nat) (hb : 0 < blocks) (L : Nat) (p : RatPoly) : RatPoly :=
  let ms := modes blocks hb p
  polySum ((highDegrees blocks hb L p).map fun d => grouped d ms)

theorem highDegrees_gt {blocks L : Nat} {hb : 0 < blocks} {p : RatPoly} {d : Nat}
    (hd : d ∈ highDegrees blocks hb L p) : L < d := by
  exact of_decide_eq_true (List.mem_filter.mp hd).2

theorem spectralHighPart_supported (blocks : Nat) (hb : 0 < blocks)
    (L : Nat) (p : RatPoly) :
    SupportedQuaternionBlocks blocks (spectralHighPart blocks hb L p) := by
  unfold spectralHighPart
  let ms := modes blocks hb p
  induction highDegrees blocks hb L p with
  | nil =>
      intro t ht
      change t ∈ ([] : RatPoly) at ht
      exact False.elim (List.not_mem_nil ht)
  | cons d ds ih =>
      simpa only [polySum] using polyAdd_supported (grouped_supported d ms) ih

theorem highDegrees_nodup (blocks : Nat) (hb : 0 < blocks) (L : Nat) (p : RatPoly) :
    (highDegrees blocks hb L p).Nodup :=
  List.filter_sublist.nodup (YMGap.Continuum.CayleyParentInj.range_nodup _)

private theorem weighted_group_sum (tail : Nat) (R : RatPoly)
    (hRi : HeadQuaternionIndependent R) (f : Nat → RatPoly) : ∀ ids : List Nat,
    quaternionHaar tail
        (polyMul (polySum (ids.map fun d => partialHaarHead (polyMul (f d) (f d))))
          (dropHeadPolynomial R)) ≈
      qListSum (ids.map fun d => quaternionHaar (tail+1)
        (polyMul R (polyMul (f d) (f d))))
  | [] => by
      exact Q'.eqv_trans _ _ _
        (haar_of_coeff (RatPolyCoeffEqv.mul_zero_left _)) (Q'.eqv_refl _)
  | d::ds => by
      have hsplit : RatPolyCoeffEqv
          (polyMul
            (polyAdd (partialHaarHead (polyMul (f d) (f d)))
              (polySum (ds.map fun k => partialHaarHead (polyMul (f k) (f k)))))
            (dropHeadPolynomial R))
          (polyAdd
            (polyMul (partialHaarHead (polyMul (f d) (f d))) (dropHeadPolynomial R))
            (polyMul (polySum (ds.map fun k => partialHaarHead (polyMul (f k) (f k))))
              (dropHeadPolynomial R))) := by
        rw [polyMul_add_left_exact]
        exact RatPolyCoeffEqv.refl _
      have hterm := quaternionHaar_polyMul_headIndependent tail
        (polyMul (f d) (f d)) R hRi
      exact Q'.eqv_trans _ _ _ (haar_of_coeff hsplit)
        (Q'.eqv_trans _ _ _ (quaternionHaar_append tail _ _)
          (Q'.add_eqv_congr'
            (Q'.eqv_trans _ _ _
              (Q'.eqv_symm hterm)
              (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)))
            (weighted_group_sum tail R hRi f ds)))

/-- Weighted norm of the complete equal-degree tail groups.  This is the
diagonal norm selected by harmonic orthogonality; it is not a postulated
joint spectral projector. -/
def groupedTailNorm (tail L : Nat) (p R : RatPoly) : Q' :=
  let ms := modes (tail+1) (by omega) p
  qListSum ((highDegrees (tail+1) (by omega) L p).map fun d =>
    quaternionHaar (tail+1) (polyMul R (polyMul (grouped d ms) (grouped d ms))))

/-- The matching weighted angular energy of the same tail groups. -/
def groupedTailAngularEnergy (tail L : Nat) (p R : RatPoly) : Q' :=
  let ms := modes (tail+1) (by omega) p
  qListSum ((highDegrees (tail+1) (by omega) L p).map fun d =>
    quaternionHaar (tail+1) (polyMul R (angularSquare (grouped d ms))))

/-- The displayed grouped tail norm is the actual weighted square of the
computed high polynomial. -/
theorem spectralHighPart_norm (tail L : Nat) (p R : RatPoly)
    (hRi : HeadQuaternionIndependent R) :
    quaternionHaar (tail+1)
        (polyMul R (polyMul (spectralHighPart (tail+1) (by omega) L p)
          (spectralHighPart (tail+1) (by omega) L p))) ≈
      groupedTailNorm tail L p R := by
  let ms := modes (tail+1) (by omega) p
  let ids := highDegrees (tail+1) (by omega) L p
  let f := fun d => grouped d ms
  have hn := partial_norm_sum f (fun d => grouped_degree d ms)
    (fun d => grouped_harmonic d ms) ids
    (highDegrees_nodup (tail+1) (by omega) L p)
  have hc := quaternionHaar_polyMul_headIndependent tail
    (polyMul (spectralHighPart (tail+1) (by omega) L p)
      (spectralHighPart (tail+1) (by omega) L p)) R hRi
  unfold spectralHighPart groupedTailNorm
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
    (Q'.eqv_trans _ _ _ hc
      (Q'.eqv_trans _ _ _ (haar_of_coeff (hn.mul_right (dropHeadPolynomial R)))
        (weighted_group_sum tail R hRi f ids)))

private theorem grouped_weighted_norm_nonnegative (tail d : Nat)
    (ms : List (Mode (tail+1))) {R : RatPoly}
    (hR : Certificate (tail+1) R) :
    (0 : Q') ≤ quaternionHaar (tail+1)
      (polyMul R (polyMul (grouped d ms) (grouped d ms))) := by
  have h := hR.square_insertion_nonnegative (grouped d ms) (grouped_supported d ms)
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (haar_of_coeff
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 0)) (.var 1))
      (.mul (.var 1) (.mul (.var 0) (.var 0))) (by decide)
      (fun | 0 => grouped d ms | _ => R))))

private theorem threshold_sum_le_energy (tail L : Nat)
    (ms : List (Mode (tail+1))) {R : RatPoly}
    (hR : Certificate (tail+1) R) (hRi : HasQuaternionBlockDegree 0 0 R) :
    ∀ ids : List Nat, (∀ d, d ∈ ids → L < d) →
      Q'.ofNat ((L+1)*(L+3)) * qListSum (ids.map fun d =>
        quaternionHaar (tail+1) (polyMul R (polyMul (grouped d ms) (grouped d ms)))) ≤
      qListSum (ids.map fun d =>
        quaternionHaar (tail+1) (polyMul R (angularSquare (grouped d ms))))
  | [], _ => Q'.le_of_eqv (Q'.mul_zero_eqv _)
  | d::ds, hdegrees => by
      let nd := quaternionHaar (tail+1)
        (polyMul R (polyMul (grouped d ms) (grouped d ms)))
      let ed := quaternionHaar (tail+1) (polyMul R (angularSquare (grouped d ms)))
      have hd : L < d := hdegrees d List.mem_cons_self
      have hcas : (L+1)*(L+3) ≤ d*(d+2) :=
        Nat.mul_le_mul (by omega) (by omega)
      have hn : (0 : Q') ≤ nd := grouped_weighted_norm_nonnegative tail d ms hR
      have hterm : Q'.ofNat ((L+1)*(L+3)) * nd ≤ ed := by
        have hm := Q'.mul_le_mul_of_nonneg_right _ _ _
          (CReal.ofNat_le_ofNat hcas) hn
        have hscalar : Q'.ofNat (d*(d+2)) ≈ Q'.ofNat d * (Q'.ofNat d+2) :=
          Q'.eqv_trans _ _ _ (HeatKernelRGStep.ofNat_mul_eqv d (d+2))
            (Q'.mul_eqv_congr_left _ _ _
              (Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv d 2)
                (Q'.add_eqv_congr' (Q'.eqv_refl _) (by decide))))
        exact Q'.le_trans' _ _ _ hm (Q'.le_of_eqv (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _ hscalar)
          (Q'.eqv_symm (retained_harmonic_energy tail d R (grouped d ms)
            hRi (grouped_degree d ms) (grouped_harmonic d ms)))))
      have htail := threshold_sum_le_energy tail L ms hR hRi ds
        (fun k hk => hdegrees k (List.mem_cons_of_mem d hk))
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.mul_add_eqv (Q'.ofNat ((L+1)*(L+3))) nd _))
        (Q'.add_le_add hterm htail)

/-- The computed high-degree norm pays the first omitted SU(2) Casimir.
The background is the same certified, head-independent polynomial on both
sides.  The constant and the filtered polynomial are explicit data. -/
theorem groupedTailNorm_threshold_le_angular (tail L : Nat) (p R : RatPoly)
    (hR : Certificate (tail+1) R) (hRi : HasQuaternionBlockDegree 0 0 R) :
    Q'.ofNat ((L+1)*(L+3)) * groupedTailNorm tail L p R ≤
      groupedTailAngularEnergy tail L p R := by
  unfold groupedTailNorm groupedTailAngularEnergy
  apply threshold_sum_le_energy tail L (modes (tail+1) (by omega) p) hR hRi
  intro d hd
  exact highDegrees_gt (blocks := tail+1) (hb := by omega) (p := p) hd

private def weightedAngularPair (blocks : Nat) (R p q : RatPoly) : Q' :=
  sixValue (fun i j => quaternionHaar blocks
    (polyMul R (polyMul (angularDerivative i j p) (angularDerivative i j q))))

attribute [local irreducible] weightedAngularPair

private theorem sixValue_neg (f : Nat → Nat → Q') :
    sixValue (fun i j => -(f i j)) ≈ -(sixValue f) := by
  have h (a b c : Q') (hbc : b ≈ -c) : -a+b ≈ -(a+c) :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) hbc)
      (Q'.eqv_symm (Q'.neg_add_eqv a c))
  exact h _ _ _ (h _ _ _ (h _ _ _ (h _ _ _
    (Q'.eqv_symm (Q'.neg_add_eqv (f 1 3) (f 2 3))))))

private theorem weightedAngularPair_add_left (blocks : Nat) (R p q r : RatPoly) :
    weightedAngularPair blocks R (polyAdd p q) r ≈
      weightedAngularPair blocks R p r + weightedAngularPair blocks R q r := by
  have hplane (i j : Nat) : quaternionHaar blocks
      (polyMul R (polyMul (angularDerivative i j (polyAdd p q)) (angularDerivative i j r))) ≈
      quaternionHaar blocks (polyMul R
          (polyMul (angularDerivative i j p) (angularDerivative i j r))) +
        quaternionHaar blocks (polyMul R
          (polyMul (angularDerivative i j q) (angularDerivative i j r))) := by
    have hc := (angularDerivative_add i j p q).mul_right (angularDerivative i j r)
    rw [polyMul_add_left_exact] at hc
    have hout := hc.mul_left R
    have hsplit := RatPolyCoeffEqv.mul_add_right R
      (polyMul (angularDerivative i j p) (angularDerivative i j r))
      (polyMul (angularDerivative i j q) (angularDerivative i j r))
    exact Q'.eqv_trans _ _ _ (haar_of_coeff (hout.trans hsplit))
      (quaternionHaar_append blocks _ _)
  unfold weightedAngularPair
  exact Q'.eqv_trans _ _ _
    (sixValue_congr _ _ (fun i j _ _ => hplane i j))
    (by
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
          | 0 => quaternionHaar blocks (polyMul R (polyMul (angularDerivative 0 1 p) (angularDerivative 0 1 r)))
          | 1 => quaternionHaar blocks (polyMul R (polyMul (angularDerivative 0 2 p) (angularDerivative 0 2 r)))
          | 2 => quaternionHaar blocks (polyMul R (polyMul (angularDerivative 0 3 p) (angularDerivative 0 3 r)))
          | 3 => quaternionHaar blocks (polyMul R (polyMul (angularDerivative 1 2 p) (angularDerivative 1 2 r)))
          | 4 => quaternionHaar blocks (polyMul R (polyMul (angularDerivative 1 3 p) (angularDerivative 1 3 r)))
          | 5 => quaternionHaar blocks (polyMul R (polyMul (angularDerivative 2 3 p) (angularDerivative 2 3 r)))
          | 6 => quaternionHaar blocks (polyMul R (polyMul (angularDerivative 0 1 q) (angularDerivative 0 1 r)))
          | 7 => quaternionHaar blocks (polyMul R (polyMul (angularDerivative 0 2 q) (angularDerivative 0 2 r)))
          | 8 => quaternionHaar blocks (polyMul R (polyMul (angularDerivative 0 3 q) (angularDerivative 0 3 r)))
          | 9 => quaternionHaar blocks (polyMul R (polyMul (angularDerivative 1 2 q) (angularDerivative 1 2 r)))
          | 10 => quaternionHaar blocks (polyMul R (polyMul (angularDerivative 1 3 q) (angularDerivative 1 3 r)))
          | _ => quaternionHaar blocks (polyMul R (polyMul (angularDerivative 2 3 q) (angularDerivative 2 3 r)))))

private theorem weightedAngularPair_add_right (blocks : Nat) (R p q r : RatPoly) :
    weightedAngularPair blocks R p (polyAdd q r) ≈
      weightedAngularPair blocks R p q + weightedAngularPair blocks R p r := by
  have hcomm (x y : RatPoly) : weightedAngularPair blocks R x y ≈
      weightedAngularPair blocks R y x := by
    unfold weightedAngularPair
    exact sixValue_congr _ _ (fun i j _ _ =>
      haar_of_coeff ((RatPolyCoeffEqv.mul_comm _ _).mul_left R))
  exact Q'.eqv_trans _ _ _
    (hcomm p (polyAdd q r))
    (Q'.eqv_trans _ _ _ (weightedAngularPair_add_left blocks R q r p)
      (Q'.add_eqv_congr' (hcomm q p) (hcomm r p)))

private theorem weighted_pair_ibp (tail : Nat) (R p q : RatPoly)
    (hRi : HasQuaternionBlockDegree 0 0 R) :
    weightedAngularPair (tail+1) R p q ≈
      -(quaternionHaar (tail+1) (polyMul R (polyMul p (angularLaplacian q)))) := by
  let second := fun i j => quaternionHaar (tail+1)
    (polyMul R (polyMul p (angularDerivative i j (angularDerivative i j q))))
  have hplane (i j : Nat) (hi : i < 4) (hj : j < 4) :
      quaternionHaar (tail+1)
          (polyMul R (polyMul (angularDerivative i j p) (angularDerivative i j q))) ≈
        -(second i j) := by
    have hz := quaternionHaar_retained_background tail hi hj R p
      (angularDerivative i j q) hRi
    have he : quaternionHaar (tail+1)
          (polyMul R (polyMul (angularDerivative i j p) (angularDerivative i j q))) +
        quaternionHaar (tail+1)
          (polyMul R (polyMul p (angularDerivative i j (angularDerivative i j q)))) ≈ 0 :=
      Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_append _ _ _))
        (Q'.eqv_trans _ _ _ (haar_of_coeff
          (RatPolyCoeffEqv.mul_add_right R _ _).symm) hz)
    apply q_eqv_of_sub_zero
    exact Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq (.add (.var 0) (.neg (.neg (.var 1))))
        (.add (.var 0) (.var 1)) (by decide)
        (fun k => if k = 0 then quaternionHaar (tail+1)
          (polyMul R (polyMul (angularDerivative i j p) (angularDerivative i j q)))
          else second i j)) he
  have hsecondAssoc : sixValue second ≈ sixValue (fun i j =>
      quaternionHaar (tail+1) (polyMul (polyMul R p)
        (angularDerivative i j (angularDerivative i j q)))) :=
    sixValue_congr _ _ (fun i j _ _ => haar_of_coeff
      (RatPolyCoeffEqv.mul_assoc R p
        (angularDerivative i j (angularDerivative i j q))).symm)
  have hsecondSix : sixValue (fun i j =>
      quaternionHaar (tail+1) (polyMul (polyMul R p)
        (angularDerivative i j (angularDerivative i j q)))) ≈
      quaternionHaar (tail+1) (polyMul (polyMul R p) (angularLaplacian q)) :=
    Q'.eqv_symm (haar_six (tail+1) (polyMul R p)
      (fun i j => angularDerivative i j (angularDerivative i j q)))
  have hsecondFinal : quaternionHaar (tail+1)
      (polyMul (polyMul R p) (angularLaplacian q)) ≈
      quaternionHaar (tail+1) (polyMul R (polyMul p (angularLaplacian q))) :=
    haar_of_coeff (RatPolyCoeffEqv.mul_assoc R p (angularLaplacian q))
  have hsecond : sixValue second ≈ quaternionHaar (tail+1)
      (polyMul R (polyMul p (angularLaplacian q))) :=
    Q'.eqv_trans _ _ _ hsecondAssoc
      (Q'.eqv_trans _ _ _ hsecondSix hsecondFinal)
  unfold weightedAngularPair
  exact Q'.eqv_trans _ _ _
    (sixValue_congr _ _ (fun i j hi hj => hplane i j hi hj))
    (Q'.eqv_trans _ _ _
      (sixValue_neg second)
      (Q'.neg_eqv_congr _ _ hsecond))

private theorem weighted_cross_degree_zero (tail : Nat) (R : RatPoly) {n d : Nat}
    {p q : RatPoly} (hRi : HasQuaternionBlockDegree 0 0 R)
    (hp : HasQuaternionBlockDegree 0 n p)
    (hhp : RatPolyCoeffEqv (headLaplacian p) polyZero)
    (hq : HasQuaternionBlockDegree 0 d q)
    (hhq : RatPolyCoeffEqv (headLaplacian q) polyZero) (hne : n ≠ d) :
    weightedAngularPair (tail+1) R p q ≈ 0 := by
  have hz := harmonic_cross_degree hp hhp hq hhq hne
  have hcross : quaternionHaar (tail+1) (polyMul R (polyMul p q)) ≈ 0 := by
    have hf := quaternionHaar_polyMul_headIndependent tail (polyMul p q) R hRi
    exact Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
      (Q'.eqv_trans _ _ _ hf
        (Q'.eqv_trans _ _ _ (haar_of_coeff (hz.mul_right (dropHeadPolynomial R)))
          (haar_of_coeff (RatPolyCoeffEqv.mul_zero_left _))))
  let eigenvalue := Q'.ofNat d * (Q'.ofNat d + 2)
  have hscale : quaternionHaar (tail+1)
      (polyMul R (polyMul p (polySmul (-eigenvalue) q))) ≈ 0 := by
    exact Q'.eqv_trans _ _ _
      (haar_of_coeff ((RatPolyCoeffEqv.polyMul_smul_right (-eigenvalue) p q).mul_left R))
      (Q'.eqv_trans _ _ _
        (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_right (-eigenvalue) R _))
        (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul (tail+1) (-eigenvalue) _)
          (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hcross)
            (Q'.mul_zero_eqv _))))
  have hlap : quaternionHaar (tail+1)
      (polyMul R (polyMul p (angularLaplacian q))) ≈ 0 :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_assoc R p _).symm)
        (harmonic_angularLaplacian (Nat.zero_lt_succ tail) q hq hhq
          (polyMul R p)))
      (Q'.eqv_trans _ _ _
        (haar_of_coeff (RatPolyCoeffEqv.mul_assoc R p _)) hscale)
  exact Q'.eqv_trans _ _ _ (weighted_pair_ibp tail R p q hRi)
    (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ hlap) (by decide))

private theorem weightedPair_zero_left (blocks : Nat) (R p : RatPoly) :
    weightedAngularPair blocks R polyZero p ≈ 0 := by
  unfold weightedAngularPair
  exact Q'.eqv_trans _ _ _
    (sixValue_congr _ _ (fun i j _ _ => haar_of_coeff
      ((RatPolyCoeffEqv.mul_zero_left (angularDerivative i j p)).mul_left R)))
    (Q'.eqv_trans _ _ _
      (sixValue_congr _ _ (fun _ _ _ _ =>
        haar_of_coeff (RatPolyCoeffEqv.mul_zero_right R)))
      (by change (sixValue fun _ _ => (0 : Q')) ≈ 0; decide))

private theorem weightedPair_zero_right (blocks : Nat) (R p : RatPoly) :
    weightedAngularPair blocks R p polyZero ≈ 0 := by
  unfold weightedAngularPair
  exact Q'.eqv_trans _ _ _
    (sixValue_congr _ _ (fun i j _ _ => haar_of_coeff
      ((RatPolyCoeffEqv.mul_zero_right (angularDerivative i j p)).mul_left R)))
    (Q'.eqv_trans _ _ _
      (sixValue_congr _ _ (fun _ _ _ _ =>
        haar_of_coeff (RatPolyCoeffEqv.mul_zero_right R)))
      (by change (sixValue fun _ _ => (0 : Q')) ≈ 0; decide))

private theorem weighted_pair_sum_right_zero (tail n : Nat) (R : RatPoly)
    (hRi : HasQuaternionBlockDegree 0 0 R) (f : Nat → RatPoly)
    (hf : ∀ d, HasQuaternionBlockDegree 0 d (f d))
    (hh : ∀ d, RatPolyCoeffEqv (headLaplacian (f d)) polyZero) :
    ∀ ids : List Nat, n ∉ ids →
      weightedAngularPair (tail+1) R (f n) (polySum (ids.map f)) ≈ 0
  | [], _ => weightedPair_zero_right _ _ _
  | d::ds, hn => Q'.eqv_trans _ _ _
      (weightedAngularPair_add_right _ _ _ _ _)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (weighted_cross_degree_zero tail R hRi (hf n) (hh n) (hf d) (hh d)
            (fun h => hn (h ▸ List.mem_cons_self)))
          (weighted_pair_sum_right_zero tail n R hRi f hf hh ds
            (fun h => hn (List.mem_cons_of_mem d h))))
        (QPoly.q_add_zero_eqv 0))

private theorem weighted_pair_sum_left_zero (tail n : Nat) (R : RatPoly)
    (hRi : HasQuaternionBlockDegree 0 0 R) (f : Nat → RatPoly)
    (hf : ∀ d, HasQuaternionBlockDegree 0 d (f d))
    (hh : ∀ d, RatPolyCoeffEqv (headLaplacian (f d)) polyZero) :
    ∀ ids : List Nat, n ∉ ids →
      weightedAngularPair (tail+1) R (polySum (ids.map f)) (f n) ≈ 0
  | [], _ => weightedPair_zero_left _ _ _
  | d::ds, hn => Q'.eqv_trans _ _ _
      (weightedAngularPair_add_left _ _ _ _ _)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (weighted_cross_degree_zero tail R hRi (hf d) (hh d) (hf n) (hh n)
            (fun h => hn (h.symm ▸ List.mem_cons_self)))
          (weighted_pair_sum_left_zero tail n R hRi f hf hh ds
            (fun h => hn (List.mem_cons_of_mem d h))))
        (QPoly.q_add_zero_eqv 0))

private theorem weighted_pair_norm_sum (tail : Nat) (R : RatPoly)
    (hRi : HasQuaternionBlockDegree 0 0 R) (f : Nat → RatPoly)
    (hf : ∀ d, HasQuaternionBlockDegree 0 d (f d))
    (hh : ∀ d, RatPolyCoeffEqv (headLaplacian (f d)) polyZero) :
    ∀ ids : List Nat, ids.Nodup →
      weightedAngularPair (tail+1) R (polySum (ids.map f)) (polySum (ids.map f)) ≈
        qListSum (ids.map fun d => weightedAngularPair (tail+1) R (f d) (f d))
  | [], _ => weightedPair_zero_left _ _ _
  | n::ns, hids => by
      have hn := (List.nodup_cons.mp hids).1
      have hs := (List.nodup_cons.mp hids).2
      have hr := weighted_pair_sum_right_zero tail n R hRi f hf hh ns hn
      have hl := weighted_pair_sum_left_zero tail n R hRi f hf hh ns hn
      exact Q'.eqv_trans _ _ _ (weightedAngularPair_add_left _ _ _ _ _)
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr' (weightedAngularPair_add_right _ _ _ _ _)
            (weightedAngularPair_add_right _ _ _ _ _))
          (Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr'
              (Q'.add_eqv_congr' (Q'.eqv_refl _) hr)
              (Q'.add_eqv_congr' hl (weighted_pair_norm_sum tail R hRi f hf hh ns hs)))
            (poly_identity_of_normal_eq
              (.add (.add (.var 0) (.const 0)) (.add (.const 0) (.var 1)))
              (.add (.var 0) (.var 1)) (by decide)
              (fun k => if k = 0 then weightedAngularPair (tail+1) R (f n) (f n)
                else qListSum (ns.map fun d => weightedAngularPair (tail+1) R (f d) (f d))))))

private theorem weightedPair_carrier {blocks : Nat} (hb : 0 < blocks) (R : RatPoly)
    {p q p' q' : RatPoly} (hp : HaarCarrierEqv blocks p p')
    (hq : HaarCarrierEqv blocks q q') :
    weightedAngularPair blocks R p q ≈ weightedAngularPair blocks R p' q' := by
  unfold weightedAngularPair
  exact sixValue_congr _ _ (fun i j hi hj => haar_of_carrier
    (HaarCarrierEqv.mul (HaarCarrierEqv.refl _ R)
      (HaarCarrierEqv.mul (angularDerivative_carrier hb hi hj hp)
        (angularDerivative_carrier hb hi hj hq))))

private theorem weightedPair_square (blocks : Nat) (R p : RatPoly) :
    weightedAngularPair blocks R p p ≈
      quaternionHaar blocks (polyMul R (angularSquare p)) := by
  unfold weightedAngularPair
  exact Q'.eqv_symm (haar_six blocks R _)

private theorem weighted_sum_square (blocks : Nat) (R : RatPoly) (f : Nat → RatPoly) :
    ∀ ids : List Nat,
      qListSum (ids.map fun d => weightedAngularPair blocks R (f d) (f d)) ≈
        qListSum (ids.map fun d => quaternionHaar blocks (polyMul R (angularSquare (f d))))
  | [] => Q'.eqv_refl _
  | d::ds => Q'.add_eqv_congr' (weightedPair_square blocks R (f d))
      (weighted_sum_square blocks R f ds)

private theorem weighted_polynomial_angular_energy (tail : Nat) (p R : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p)
    (hRi : HasQuaternionBlockDegree 0 0 R) :
    quaternionHaar (tail+1) (polyMul R (angularSquare p)) ≈
      qListSum ((headDegrees (sumHarmonics (modes (tail+1) (by omega) p))).map fun d =>
        quaternionHaar (tail+1)
          (polyMul R (angularSquare (grouped d (modes (tail+1) (by omega) p))))) := by
  let ms := modes (tail+1) (by omega) p
  let f := fun d => grouped d ms
  let ids := headDegrees (sumHarmonics ms)
  have hc : HaarCarrierEqv (tail+1) p (polySum (ids.map f)) :=
    (polynomial_harmonic_carrier (by omega : 0 < tail+1) p hp).trans
      (RatPolyCoeffEqv.haarCarrier (headComponent_reassembly (sumHarmonics ms)).symm)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (weightedPair_square (tail+1) R p))
    (Q'.eqv_trans _ _ _ (weightedPair_carrier (by omega) R hc hc)
      (Q'.eqv_trans _ _ _
        (weighted_pair_norm_sum tail R hRi f (fun d => grouped_degree d ms)
          (fun d => grouped_harmonic d ms) ids
          (YMGap.Continuum.CayleyParentInj.range_nodup _))
        (weighted_sum_square (tail+1) R f ids)))

private theorem weighted_group_energy_nonnegative (tail d : Nat)
    (ms : List (Mode (tail+1))) {R : RatPoly} (hR : Certificate (tail+1) R) :
    (0 : Q') ≤ quaternionHaar (tail+1)
      (polyMul R (angularSquare (grouped d ms))) := by
  refine Q'.le_trans' _ _ _ ?_ (Q'.le_of_eqv (weightedPair_square (tail+1) R _))
  unfold weightedAngularPair
  apply sixValue_mono (fun _ _ => 0) _
  intro i j hi hj
  have h := hR.square_insertion_nonnegative (angularDerivative i j (grouped d ms))
    (angularDerivative_supported_at (by omega) (by omega) (grouped_supported d ms))
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (haar_of_coeff
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 0)) (.var 1))
      (.mul (.var 1) (.mul (.var 0) (.var 0))) (by decide)
      (fun | 0 => angularDerivative i j (grouped d ms) | _ => R))))

private theorem filtered_energy_le_all (tail L : Nat) (p : RatPoly) {R : RatPoly}
    (hR : Certificate (tail+1) R) :
    groupedTailAngularEnergy tail L p R ≤
      qListSum ((headDegrees (sumHarmonics (modes (tail+1) (by omega) p))).map fun d =>
        quaternionHaar (tail+1)
          (polyMul R (angularSquare (grouped d (modes (tail+1) (by omega) p))))) := by
  let ms := modes (tail+1) (by omega) p
  let value := fun d => quaternionHaar (tail+1)
    (polyMul R (angularSquare (grouped d ms)))
  have go : ∀ ids : List Nat,
      qListSum ((ids.filter (fun d => decide (L < d))).map value) ≤
        qListSum (ids.map value) := by
    intro ids
    induction ids with
    | nil => exact Q'.le_refl' _
    | cons d ds ih =>
        simp only [List.filter_cons]
        split
        · exact Q'.add_le_add (Q'.le_refl' _) ih
        · exact Q'.le_trans' _ _ _
            (Q'.le_of_eqv (Q'.eqv_symm (QPoly.q_zero_add_eqv _)))
            (Q'.add_le_add (weighted_group_energy_nonnegative tail d ms hR) ih)
  unfold groupedTailAngularEnergy highDegrees
  exact go _

/-- The actual high harmonic polynomial pays the first omitted Casimir using
the original polynomial's weighted angular energy.  Both sides retain the
same certified head-independent background. -/
theorem spectralHighPart_threshold_le_energy (tail L : Nat) (p R : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p)
    (hR : Certificate (tail+1) R) (hRi : HasQuaternionBlockDegree 0 0 R) :
    Q'.ofNat ((L+1)*(L+3)) * quaternionHaar (tail+1)
        (polyMul R (polyMul (spectralHighPart (tail+1) (by omega) L p)
          (spectralHighPart (tail+1) (by omega) L p))) ≤
      quaternionHaar (tail+1) (polyMul R (angularSquare p)) := by
  have hn := spectralHighPart_norm tail L p R hRi
  have ht := groupedTailNorm_threshold_le_angular tail L p R hR hRi
  have hf := filtered_energy_le_all tail L p hR
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ hn))
    (Q'.le_trans' _ _ _ ht (Q'.le_trans' _ _ _ hf
      (Q'.le_of_eqv (Q'.eqv_symm (weighted_polynomial_angular_energy tail p R hp hRi)))))

end YMGap.Continuum.SU2QuaternionGroupedHarmonicTail

#print axioms YMGap.Continuum.SU2QuaternionGroupedHarmonicTail.highDegrees
#print axioms YMGap.Continuum.SU2QuaternionGroupedHarmonicTail.spectralHighPart
#print axioms YMGap.Continuum.SU2QuaternionGroupedHarmonicTail.highDegrees_gt
#print axioms YMGap.Continuum.SU2QuaternionGroupedHarmonicTail.spectralHighPart_supported
#print axioms YMGap.Continuum.SU2QuaternionGroupedHarmonicTail.groupedTailNorm
#print axioms YMGap.Continuum.SU2QuaternionGroupedHarmonicTail.groupedTailAngularEnergy
#print axioms YMGap.Continuum.SU2QuaternionGroupedHarmonicTail.groupedTailNorm_threshold_le_angular
#print axioms YMGap.Continuum.SU2QuaternionGroupedHarmonicTail.spectralHighPart_threshold_le_energy
