/-
# Boundary-depth transport of the ORIGINAL energy / OWN variance ratio

The constructed terminal bracket compares the actual Wilson edge densities
at two depths. Its squared lower endpoint controls raw variance at the
new density's OWN mean; its squared upper endpoint controls raw energy.
Thus the partition factors cancel when transporting a reference ratio.
No absolute-value expansion of a signed observable is made. Coupling and
width dependence remain explicit; no reference rate or scaling estimate
is supplied here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalComparison
import YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard
import YMGap.Continuum.QuaternionHaarDensityVarianceComparison
import YMGap.Continuum.PositiveContractionResidual

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalEnergyComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticOrder (kineticCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (spatialCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalComparison
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard (oddVariance)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension
open YMGap.Continuum.SU2QuaternionHaarCertificateLift
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.QuaternionHaarDensityVarianceComparison
open YMGap.Continuum.PositiveContractionResidual (geometricCutoff geometric_bound)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
  (mixRate mixRate_nonnegative mixRate_lt_one)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" blocks:arg => quaternionHaar blocks
attribute [local irreducible] baseLinks spatialWeight kineticWeight terminalMessage
  energy normalizedEnergy oddMass oddVariance

private theorem support_smul {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (c : Q') :
    SupportedQuaternionBlocks blocks (polySmul c p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem support_pair {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks (blocks+blocks) p :=
  fun t ht => Nat.le_trans (hp t ht) (Nat.mul_le_mul_left 4 (Nat.le_add_right _ _))

private theorem mul_congr {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

private theorem negative_scale (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv (polySmul (-c) p) (polyNeg (polySmul c p)) :=
  ((neg_smul _).trans ((RatPolyCoeffEqv.smul_assoc (-1) c p).trans
    (RatPolyCoeffEqv.smul_coefficient (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 c)
      (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv c))) p))).symm

private theorem negative_cap (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv (polySmul (-c) p) (polyNeg (polyMul (cap c) p)) :=
  (negative_scale c p).trans (RatPolyCoeffEqv.neg (cap_mul_left c p).symm)

private theorem square_scale (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv (polySmul (c*c) p)
      (polyMul (polyMul (cap c) (cap c)) p) :=
  (cap_mul_left (c*c) p).symm.trans ((cap_mul c c).symm.mul (RatPolyCoeffEqv.refl p))

private theorem lower_product_algebra (k p q lp lq : RatPoly) (c : Q') :
    RatPolyCoeffEqv
      (polyAdd (polyMul (polyMul k p) lp)
        (polySmul (-(c*c)) (polyMul (polyMul k q) lq)))
      (polyAdd (polyMul (polyMul k (polyAdd p (polySmul (-c) q))) lp)
        (polySmul c (polyMul (polyMul k q) (polyAdd lp (polySmul (-c) lq))))) := by
  have hleft := (RatPolyCoeffEqv.refl (polyMul (polyMul k p) lp)).add
    ((negative_scale (c*c) (polyMul (polyMul k q) lq)).trans
      (RatPolyCoeffEqv.neg (square_scale c (polyMul (polyMul k q) lq))))
  have hright :=
    (((RatPolyCoeffEqv.refl k).mul
      ((RatPolyCoeffEqv.refl p).add (negative_cap c q))).mul (RatPolyCoeffEqv.refl lp)).add
      ((cap_mul_left c (polyMul (polyMul k q) (polyAdd lp (polySmul (-c) lq)))).symm.trans
        ((RatPolyCoeffEqv.refl (cap c)).mul
        ((RatPolyCoeffEqv.refl (polyMul k q)).mul
          ((RatPolyCoeffEqv.refl lp).add (negative_cap c lq)))))
  exact hleft.trans ((coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.mul (.var 0) (.var 1)) (.var 3))
      (.neg (.mul (.mul (.var 5) (.var 5)) (.mul (.mul (.var 0) (.var 2)) (.var 4)))))
    (.add (.mul (.mul (.var 0) (.add (.var 1) (.neg (.mul (.var 5) (.var 2))))) (.var 3))
      (.mul (.var 5) (.mul (.mul (.var 0) (.var 2))
        (.add (.var 3) (.neg (.mul (.var 5) (.var 4)))))))
    (by decide) (fun | 0 => k | 1 => p | 2 => q | 3 => lp | 4 => lq | _ => cap c)).trans
      hright.symm)

private theorem upper_product_algebra (k p q lp lq : RatPoly) (c : Q') :
    RatPolyCoeffEqv
      (polyAdd (polySmul (c*c) (polyMul (polyMul k q) lq))
        (polySmul (-1) (polyMul (polyMul k p) lp)))
      (polyAdd
        (polyMul (polyMul k (polyAdd (polySmul c q) (polySmul (-1) p))) (polySmul c lq))
        (polyMul (polyMul k p) (polyAdd (polySmul c lq) (polySmul (-1) lp)))) := by
  have hleft := (square_scale c (polyMul (polyMul k q) lq)).add
    (neg_smul (polyMul (polyMul k p) lp)).symm
  have hright :=
    (((RatPolyCoeffEqv.refl k).mul
      ((cap_mul_left c q).symm.add (neg_smul p).symm)).mul
        (cap_mul_left c lq).symm).add
      ((RatPolyCoeffEqv.refl (polyMul k p)).mul
        ((cap_mul_left c lq).symm.add (neg_smul lp).symm))
  exact hleft.trans ((coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.mul (.var 5) (.var 5)) (.mul (.mul (.var 0) (.var 2)) (.var 4)))
      (.neg (.mul (.mul (.var 0) (.var 1)) (.var 3))))
    (.add (.mul (.mul (.var 0) (.add (.mul (.var 5) (.var 2)) (.neg (.var 1))))
        (.mul (.var 5) (.var 4)))
      (.mul (.mul (.var 0) (.var 1)) (.add (.mul (.var 5) (.var 4)) (.neg (.var 3)))))
    (by decide) (fun | 0 => k | 1 => p | 2 => q | 3 => lp | 4 => lq | _ => cap c)).trans
      hright.symm)

/-- A positive relative bracket supplies the squared lower comparison of
the two ORIGINAL edge densities, including their kinetic and spatial factors. -/
def edgeLowerCertificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) {g h : RatPoly}
    (hg : SupportedQuaternionBlocks (N width) g)
    (hh : SupportedQuaternionBlocks (N width) h)
    (G : Certificate (N width) g) (J : Certificate (N width) h)
    (B : Bracket width g h) (hl : (0 : Q') ≤ B.lower) :
    Certificate (N width+N width)
      (polyAdd (edgeDensity w K width g)
        (polySmul (-(B.lower*B.lower)) (edgeDensity w K width h))) := by
  let V := spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK
  let C := multiplyBracket B V
  let p := polyMul (spatialWeight w K width) g
  let q := polyMul (spatialWeight w K width) h
  have hp := supported_polyMul (spatialWeight_supported w K width) hg
  have hq := supported_polyMul (spatialWeight_supported w K width) hh
  have D := certificate_extend (N width) (supported_add hp (support_smul hq (-B.lower)))
    C.lowerCertificate
  have DL : Certificate (N width+N width)
      (polyAdd (liftBoundary (N width) p)
        (polySmul (-B.lower) (liftBoundary (N width) q))) := by
    simpa only [lift_add, lift_smul] using lift_certificate (N width) C.lowerCertificate
  exact Certificate.ofCoeff
    (lower_product_algebra (kineticWeight w K width) p q
      (liftBoundary (N width) p) (liftBoundary (N width) q) B.lower)
    ((((kineticCertificate hw0 hw1 K width hK).mul D).mul
        (lift_certificate (N width) (V.mul G))).add
      (.smul B.lower hl (((kineticCertificate hw0 hw1 K width hK).mul
        (certificate_extend (N width) hq (V.mul J))).mul DL)))

/-- The upper edge comparison has the squared upper endpoint. -/
def edgeUpperCertificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) {g h : RatPoly}
    (hg : SupportedQuaternionBlocks (N width) g)
    (hh : SupportedQuaternionBlocks (N width) h)
    (G : Certificate (N width) g) (J : Certificate (N width) h)
    (B : Bracket width g h) (hu : (0 : Q') ≤ B.upper) :
    Certificate (N width+N width)
      (polyAdd (polySmul (B.upper*B.upper) (edgeDensity w K width h))
        (polySmul (-1) (edgeDensity w K width g))) := by
  let V := spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK
  let C := multiplyBracket B V
  let p := polyMul (spatialWeight w K width) g
  let q := polyMul (spatialWeight w K width) h
  have hp := supported_polyMul (spatialWeight_supported w K width) hg
  have hq := supported_polyMul (spatialWeight_supported w K width) hh
  have D := certificate_extend (N width)
    (supported_add (support_smul hq B.upper) (support_smul hp (-1))) C.upperCertificate
  have DL : Certificate (N width+N width)
      (polyAdd (polySmul B.upper (liftBoundary (N width) q))
        (polySmul (-1) (liftBoundary (N width) p))) := by
    simpa only [lift_add, lift_smul] using lift_certificate (N width) C.upperCertificate
  have U : Certificate (N width+N width)
      (polySmul B.upper (liftBoundary (N width) q)) :=
    .smul B.upper hu (lift_certificate (N width) (V.mul J))
  exact Certificate.ofCoeff
    (upper_product_algebra (kineticWeight w K width) p q
      (liftBoundary (N width) p) (liftBoundary (N width) q) B.upper)
    ((((kineticCertificate hw0 hw1 K width hK).mul D).mul U).add
      (((kineticCertificate hw0 hw1 K width hK).mul
        (certificate_extend (N width) hp (V.mul G))).mul DL))

/-- The upper density comparison controls raw original temporal energy. -/
theorem energy_upper {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) {g h f : RatPoly}
    (hg : SupportedQuaternionBlocks (N width) g)
    (hh : SupportedQuaternionBlocks (N width) h)
    (hf : SupportedQuaternionBlocks (N width) f)
    (G : Certificate (N width) g) (J : Certificate (N width) h)
    (B : Bracket width g h) (hu : (0 : Q') ≤ B.upper) :
    energy w K width g f ≤ (B.upper*B.upper)*energy w K width h f := by
  have hsq := raw_square_comparison
    (edgeUpperCertificate hw0 hw1 K width hK hg hh G J B hu) (jump_supported width hf)
  have hs : H (N width+N width)
      (polyMul (polySmul (B.upper*B.upper) (edgeDensity w K width h))
        (polyMul (jump width f) (jump width f))) ≈
      (B.upper*B.upper)*H (N width+N width)
        (polyMul (edgeDensity w K width h) (polyMul (jump width f) (jump width f))) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left _ _ _))
      (quaternionHaar_polySmul _ _ _)
  have htwo : (2 : Q')*energy w K width g f ≤
      (2 : Q')*((B.upper*B.upper)*energy w K width h f) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (energy_identity w K width hg hf))
      (Q'.le_trans' _ _ _
        (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv _)) hsq)
        (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hs
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (energy_identity w K width hh hf)))
            (poly_identity_of_normal_eq (.mul (.var 0) (.mul (.const 2) (.var 1)))
              (.mul (.const 2) (.mul (.var 0) (.var 1))) (by decide)
              (fun | 0 => B.upper*B.upper | _ => energy w K width h f))))))
  exact Q'.le_of_mul_le_mul_left htwo (by decide)

/-- Positive ORIGINAL edge mass, not a new denominator hypothesis. -/
theorem edgeMass_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) :
    (0 : Q') < H (N width+N width) (edgeDensity w K width (terminalMessage w K width n)) :=
  HeatKernelRGStep.lt_of_lt_of_le (oddMass_positive hw0 hw1 K width hK n)
    (Q'.ge_of_eqv (edge_total_mass w K width n))

/-- All supported edge diagonal moments are the existing odd-chain moments. -/
theorem edgeMoment_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    normalizedMoment (N width+N width) (edgeDensity w K width (terminalMessage w K width n)) f
        (edgeMass_positive hw0 hw1 K width hK n) ≈
      BF4ExactSlabFixedSpatialMiddlePairing.middleRatio hw0 hw1 K width hK (n+1) n f := by
  exact Q'.eqv_trans _ _ _
    (mul_congr
      (edge_marginal_pairing w K width (terminalMessage_supported w K width n) hf)
      (Q'.recipPos_eqv_congr _ _ (edgeMass_positive hw0 hw1 K width hK n)
        (oddMass_positive hw0 hw1 K width hK n) (edge_total_mass w K width n)))
    (marginal_middleRatio hw0 hw1 K width hK n f)

/-- Raw edge variance uses the SAME odd partition and its OWN interacting mean. -/
theorem rawEdgeVariance_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    rawVariance (edgeMass_positive hw0 hw1 K width hK n) f ≈
      oddMass w K width n * oddVariance hw0 hw1 K width hK n f := by
  have hm := edgeMoment_pin hw0 hw1 K width hK n hf
  have hv : normalizedVariance (N width+N width)
      (edgeDensity w K width (terminalMessage w K width n)) f
        (edgeMass_positive hw0 hw1 K width hK n) ≈
      oddVariance hw0 hw1 K width hK n f := by
    unfold normalizedVariance oddVariance
    exact Q'.add_eqv_congr' (edgeMoment_pin hw0 hw1 K width hK n (supported_polyMul hf hf))
      (Q'.neg_eqv_congr _ _ (mul_congr hm hm))
  exact mul_congr (edge_total_mass w K width n) hv

private theorem mass_cancel (Z X : Q') (hZ : (0 : Q') < Z) :
    Z*(X*Q'.recipPos Z hZ) ≈ X := by
  refine Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
    (.mul (.var 0) (.mul (.var 1) (.var 2)))
    (.mul (.var 1) (.mul (.var 0) (.var 2)))
    (by decide) (fun | 0 => Z | 1 => X | _ => Q'.recipPos Z hZ)) ?_
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_recipPos_eqv Z hZ)) (Q'.mul_one_eqv X)

/-- Transport a ratio from ANY reference depth with the explicit relative
bracket loss. Every certificate and both partitions are constructed from
the original transfer; only the reference analytic ratio is assumed. -/
theorem terminal_ratio_transport {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (s r t : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) {c : Q'} (hc : (0 : Q') ≤ c)
    (href : normalizedEnergy hw0 hw1 K width hK (s+1+t) f ≤
      c*oddVariance hw0 hw1 K width hK (s+1+t) f) :
    normalizedEnergy hw0 hw1 K width hK (s+1+r) f ≤
      (c*((1+comparisonEta hw0 hw1 width s)*(1+comparisonEta hw0 hw1 width s)))*
        oddVariance hw0 hw1 K width hK (s+1+r) f := by
  let n := s+1+r
  let m := s+1+t
  let B := terminalComparison hw0 hw1 K width hK s r t
  let g := terminalMessage w K width n
  let h := terminalMessage w K width m
  have hg := terminalMessage_supported w K width n
  have hh := terminalMessage_supported w K width m
  let G := terminalMessage_certificate hw0 hw1 K width hK n
  let J := terminalMessage_certificate hw0 hw1 K width hK m
  let PG := edgeCertificate hw0 hw1 K width hK hg G
  let PJ := edgeCertificate hw0 hw1 K width hK hh J
  let Zg := oddMass w K width n
  let Zh := oddMass w K width m
  have hZg := oddMass_positive hw0 hw1 K width hK n
  have hZh := oddMass_positive hw0 hw1 K width hK m
  let Sg := rawVariance (edgeMass_positive hw0 hw1 K width hK n) f
  let Sh := rawVariance (edgeMass_positive hw0 hw1 K width hK m) f
  have hl : (0 : Q') ≤ B.lower :=
    Q'.le_of_lt (terminalComparison_lower_positive hw0 hw1 K width hK s r t)
  have hb := massRatio_bounds hw0 hw1 K width hK
    (terminalMessage_mass_positive hw0 hw1 K width hK m) B
  have hu : (0 : Q') ≤ B.upper := Q'.le_trans' _ _ _ hl (Q'.le_trans' _ _ _ hb.1 hb.2)
  have hen := energy_upper hw0 hw1 K width hK hg hh hf G J B hu
  have hvar := raw_variance_comparison PG PJ
    (edgeMass_positive hw0 hw1 K width hK n) (edgeMass_positive hw0 hw1 K width hK m)
    (Q'.mul_nonneg _ _ hl hl) (edgeLowerCertificate hw0 hw1 K width hK hg hh G J B hl)
    (support_pair hf)
  have hSm : (0 : Q') ≤ Sh := rawVariance_nonnegative PJ (support_pair hf)
    (edgeMass_positive hw0 hw1 K width hK m)
  have hpinm := rawEdgeVariance_pin hw0 hw1 K width hK m hf
  have hpinn := rawEdgeVariance_pin hw0 hw1 K width hK n hf
  have hrefmul := Q'.mul_le_mul_of_nonneg_left _ _ Zh href (Q'.le_of_lt hZh)
  have hrefclear : Zh*normalizedEnergy hw0 hw1 K width hK m f ≈ energy w K width h f := by
    unfold normalizedEnergy
    exact mass_cancel Zh (energy w K width h f) hZh
  have hrefraw : energy w K width h f ≤ c*Sh :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hrefclear)
      (Q'.le_trans' _ _ _ hrefmul (Q'.le_of_eqv (Q'.eqv_trans _ _ _
        (poly_identity_of_normal_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
          (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
          (fun | 0 => Zh | 1 => c | _ => oddVariance hw0 hw1 K width hK m f))
        (Q'.mul_eqv_congr_left c _ _ (Q'.eqv_symm hpinm)))))
  let D := c*((1+comparisonEta hw0 hw1 width s)*(1+comparisonEta hw0 hw1 width s))
  have hraw : energy w K width g f ≤ D*Sg :=
    energy_variance_ratio_transport hl hu (comparisonEta_nonnegative hw0 hw1 width s) hc
      hSm
      (terminalComparison_relative_width hw0 hw1 K width hK s r t) hen hvar hrefraw
  have hnorm := Q'.mul_le_mul_of_nonneg_right _ _ (Q'.recipPos Zg hZg) hraw
    (Q'.le_of_lt (Q'.recipPos_pos Zg hZg))
  have hcancel : (D*Sg)*Q'.recipPos Zg hZg ≈
      D*oddVariance hw0 hw1 K width hK n f :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_eqv_congr_left D _ _ hpinn))
      (Q'.eqv_trans _ _ _
        (poly_identity_of_normal_eq
          (.mul (.mul (.var 0) (.mul (.var 2) (.var 1))) (.var 3))
          (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 3))))
          (by decide) (fun | 0 => D | 1 => oddVariance hw0 hw1 K width hK n f
                           | 2 => Zg | _ => Q'.recipPos Zg hZg))
        (Q'.mul_eqv_congr_left D _ _ (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_recipPos_eqv Zg hZg)) (Q'.mul_one_eqv _))))
  unfold normalizedEnergy
  exact Q'.le_trans' _ _ _ hnorm (Q'.le_of_eqv hcancel)

/-- ONE finite boundary depth suffices for ALL later depths. The coefficient
is independent of cutoff K and later depth r, but NOT of nome or width. -/
theorem finite_reference_all_later {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (s : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) {c : Q'} (hc : (0 : Q') ≤ c)
    (href : normalizedEnergy hw0 hw1 K width hK (s+1) f ≤
      c*oddVariance hw0 hw1 K width hK (s+1) f) (r : Nat) :
    normalizedEnergy hw0 hw1 K width hK (s+1+r) f ≤
      (c*((1+comparisonEta hw0 hw1 width s)*(1+comparisonEta hw0 hw1 width s)))*
        oddVariance hw0 hw1 K width hK (s+1+r) f :=
  terminal_ratio_transport hw0 hw1 K width hK s r 0 hf hc href

/-- A computed common prefix giving any supplied positive relative-error
budget. No heat cutoff or later boundary depth enters this threshold. -/
def comparisonOnset {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (epsilon : Q') : Nat :=
  geometricCutoff (mixRate hw0 hw1 width) (comparisonKappa hw0 hw1 width) epsilon

/-- Its budget is checked for every later prefix, retaining nome and width
dependence. The reference boundary depth in the ratio theorem is s+1. -/
theorem comparisonEta_small {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (epsilon : Q') (he : (0 : Q') < epsilon)
    (s : Nat) (hs : comparisonOnset hw0 hw1 width epsilon ≤ s) :
    comparisonEta hw0 hw1 width s ≤ epsilon :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
    (geometric_bound (mixRate_nonnegative hw0 hw1 width) (mixRate_lt_one hw0 hw1 width)
      (comparisonKappa_nonnegative hw0 hw1 width) he s hs)

#print axioms edgeLowerCertificate
#print axioms edgeUpperCertificate
#print axioms energy_upper
#print axioms edgeMass_positive
#print axioms edgeMoment_pin
#print axioms rawEdgeVariance_pin
#print axioms terminal_ratio_transport
#print axioms finite_reference_all_later
#print axioms comparisonOnset
#print axioms comparisonEta_small

end YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalEnergyComparison
