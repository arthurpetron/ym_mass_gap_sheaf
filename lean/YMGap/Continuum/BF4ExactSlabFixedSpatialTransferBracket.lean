/-
# Strict comparison-bracket refresh for the original transfer

The positive residuals f-lower*g and upper*g-f each gain the actual
rank-one floor. The same upper bound for T g converts those floors into
improvements relative to T g. Every comparison is a polynomial Haar
certificate on the original slice, not a pointwise-positivity oracle.

The denominator is the supplied strictly positive ORIGINAL V-weighted
mass of g. No sign of f or of the bracket endpoints is assumed. The rate
retains nome and width dependence; this is not physical OS or a mass gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
import YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracket

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

private theorem mul_congr {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

private theorem smul_neg (p : RatPoly) : RatPolyCoeffEqv (polySmul (-1) p) (polyNeg p) :=
  (cap_mul_left (-1) p).symm.trans
    (coeffEvalExpr_eqv_of_normalize_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
      (by decide) (fun _ => p))

private theorem negative_smul (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv (polyNeg (polySmul c p)) (polySmul (-c) p) :=
  (smul_neg _).symm.trans ((RatPolyCoeffEqv.smul_assoc (-1) c p).trans
    (RatPolyCoeffEqv.smul_coefficient
      (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 c)
        (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv c))) p))

private theorem support_smul {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (c : Q') :
    SupportedQuaternionBlocks blocks (polySmul c p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

/-- A certified comparison, with both rational endpoints retained as data. -/
structure Bracket (width : Nat) (f g : RatPoly) : Type where
  lower : Q'
  upper : Q'
  lowerCertificate : Certificate (N width) (polyAdd f (polySmul (-lower) g))
  upperCertificate : Certificate (N width) (polyAdd (polySmul upper g) (polySmul (-1) f))

/-- An existing actual polynomial interval supplies an inhabited initial bracket. -/
def ofInterval {width : Nat} {f : RatPoly} {c : Q'} (I : Interval (N width) f c) :
    Bracket width f polyOne where
  lower := -c
  upper := c
  lowerCertificate := Certificate.ofCoeff
    (((RatPolyCoeffEqv.refl f).add (RatPolyCoeffEqv.smul_coefficient
      (Q'.neg_neg_eqv c) polyOne)).trans (RatPolyCoeffEqv.add_comm _ _)) I.lower
  upperCertificate := Certificate.ofCoeff ((RatPolyCoeffEqv.refl _).add (smul_neg f)) I.upper

/-- Actual rank-one gain relative to a positive original comparison message. -/
def gain {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (g h : RatPoly) (hg : (0 : Q') < weightedMass w K width g) : Q' :=
  mixFraction hw0 hw1 width *
    (weightedMass w K width h * Q'.recipPos (weightedMass w K width g) hg)

theorem gain_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (g h : RatPoly)
    (hg : (0 : Q') < weightedMass w K width g) (H : Certificate (N width) h) :
    (0 : Q') ≤ gain hw0 hw1 K width g h hg :=
  Q'.mul_nonneg _ _ (Q'.le_of_lt (mixFraction_positive hw0 hw1 width))
    (Q'.mul_nonneg _ _ (weightedMass_nonnegative hw0 hw1 K width hK H)
      (Q'.le_of_lt (Q'.recipPos_pos _ hg)))

private theorem fraction_cancel (eta a b H L r : Q') (hab : eta*b ≈ a) (hL : L*r ≈ 1) :
    (eta*(H*r))*(b*L) ≈ a*H := by
  refine Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
    (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.mul (.var 3) (.var 4)))
    (.mul (.mul (.var 0) (.var 3)) (.mul (.var 1) (.mul (.var 4) (.var 2))))
    (by decide) (fun | 0 => eta | 1 => H | 2 => r | 3 => b | _ => L)) ?_
  exact mul_congr hab
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hL)
      (Q'.mul_one_eqv _))

private theorem gain_cancel {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (g h : RatPoly) (hg : (0 : Q') < weightedMass w K width g) :
    gain hw0 hw1 K width g h hg * (kineticCap w width * weightedMass w K width g) ≈
      kineticFloor w width * weightedMass w K width h :=
  fraction_cancel _ _ _ _ _ _ (mixFraction_mul_cap hw0 hw1 width) (Q'.mul_recipPos_eqv _ hg)

private def cancel_floor {blocks : Nat} {u v : RatPoly} {A B c : Q'}
    (hc : (0 : Q') ≤ c) (he : c*B ≈ A)
    (P : Certificate blocks (polyAdd u (polyNeg (cap A))))
    (Q : Certificate blocks (polyAdd (cap B) (polyNeg v))) :
    Certificate blocks (polyAdd u (polySmul (-c) v)) := by
  have hcap : RatPolyCoeffEqv (polyMul (cap c) (cap B)) (cap A) :=
    (cap_mul c B).trans (RatPolyCoeffEqv.smul_coefficient he polyOne)
  have hneg : RatPolyCoeffEqv (polySmul (-c) v) (polyNeg (polyMul (cap c) v)) :=
    (negative_smul c v).symm.trans (RatPolyCoeffEqv.neg (cap_mul_left c v).symm)
  exact Certificate.ofCoeff
    (((RatPolyCoeffEqv.refl u).add hneg).trans
      ((coeffEvalExpr_eqv_of_normalize_eq
        (.add (.var 0) (.neg (.mul (.var 2) (.var 1))))
        (.add (.add (.var 0) (.neg (.mul (.var 2) (.var 3))))
          (.mul (.var 2) (.add (.var 3) (.neg (.var 1)))))
        (by decide) (fun | 0 => u | 1 => v | 2 => cap c | _ => cap B)).trans
        (((RatPolyCoeffEqv.refl u).add (RatPolyCoeffEqv.neg hcap)).add (RatPolyCoeffEqv.refl _))))
    (P.add ((Certificate.constant blocks c hc).mul Q))

/-- The actual lower bound of h and upper bound of g yield a comparison
against T g, with its explicitly computed nonnegative gain. -/
def relativeFloorCertificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) {g h : RatPoly}
    (hg : SupportedQuaternionBlocks (N width) g) (hh : SupportedQuaternionBlocks (N width) h)
    (G : Certificate (N width) g) (H : Certificate (N width) h)
    (hmass : (0 : Q') < weightedMass w K width g) :
    Certificate (N width) (polyAdd (transferStep w K width h)
      (polySmul (-(gain hw0 hw1 K width g h hmass)) (transferStep w K width g))) :=
  cancel_floor (gain_nonnegative hw0 hw1 K width hK g h hmass H)
    (gain_cancel hw0 hw1 K width g h hmass)
    (transferStepLowerCertificate hw0 hw1 K width hK hh H)
    (transferStepUpperCertificate hw0 hw1 K width hK hg G)

private theorem transfer_affine (w : Q') (K width : Nat) (f g : RatPoly) (c : Q') :
    RatPolyCoeffEqv (transferStep w K width (polyAdd f (polySmul c g)))
      (polyAdd (transferStep w K width f) (polySmul c (transferStep w K width g))) :=
  (transferStep_add w K width _ _).trans
    ((RatPolyCoeffEqv.refl _).add (transferStep_smul w K width c g))

private theorem lower_collect (f g : RatPoly) (l c : Q') :
    RatPolyCoeffEqv (polyAdd (polyAdd f (polySmul (-l) g)) (polySmul (-c) g))
      (polyAdd f (polySmul (-(l+c)) g)) :=
  (RatPolyCoeffEqv.add_assoc _ _ _).trans ((RatPolyCoeffEqv.refl _).add
    ((RatPolyCoeffEqv.add_smul_same (-l) (-c) g).trans
      (RatPolyCoeffEqv.smul_coefficient (Q'.eqv_symm (Q'.neg_add_eqv_split l c)) g)))

private theorem upper_collect (f g : RatPoly) (u c : Q') :
    RatPolyCoeffEqv (polyAdd (polyAdd (polySmul u g) (polySmul (-1) f)) (polySmul (-c) g))
      (polyAdd (polySmul (u + -c) g) (polySmul (-1) f)) :=
  ((RatPolyCoeffEqv.add_comm _ _).add (RatPolyCoeffEqv.refl _)).trans
    ((RatPolyCoeffEqv.add_assoc _ _ _).trans
      (((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.add_smul_same u (-c) g)).trans
        (RatPolyCoeffEqv.add_comm _ _)))

/-- Refresh both sides of an actual certificate bracket. Its endpoints are
computed from the two residual masses, not selected from existence proofs. -/
def refresh {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) {f g : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) (hg : SupportedQuaternionBlocks (N width) g)
    (G : Certificate (N width) g) (hmass : (0 : Q') < weightedMass w K width g)
    (B : Bracket width f g) : Bracket width (transferStep w K width f) (transferStep w K width g) where
  lower := B.lower + gain hw0 hw1 K width g (polyAdd f (polySmul (-B.lower) g)) hmass
  upper := B.upper + -(gain hw0 hw1 K width g (polyAdd (polySmul B.upper g) (polySmul (-1) f)) hmass)
  lowerCertificate := Certificate.ofCoeff
    ((((transfer_affine w K width f g (-B.lower)).add (RatPolyCoeffEqv.refl _)).trans
      (lower_collect (transferStep w K width f) (transferStep w K width g) B.lower _)).symm)
    (relativeFloorCertificate hw0 hw1 K width hK hg
      (supported_add hf (support_smul hg _)) G B.lowerCertificate hmass)
  upperCertificate := Certificate.ofCoeff
    (((((transferStep_add w K width _ _).trans
      ((transferStep_smul w K width B.upper g).add (transferStep_smul w K width (-1) f))).add
        (RatPolyCoeffEqv.refl _)).trans
      (upper_collect (transferStep w K width f) (transferStep w K width g) B.upper _)).symm)
    (relativeFloorCertificate hw0 hw1 K width hK hg
      (supported_add (support_smul hg _) (support_smul hf _)) G B.upperCertificate hmass)

/-- The normalized scalar of these SAME original messages and one terminal V. -/
def massRatio (w : Q') (K width : Nat) (f g : RatPoly)
    (hmass : (0 : Q') < weightedMass w K width g) : Q' :=
  weightedMass w K width f * Q'.recipPos (weightedMass w K width g) hmass

private theorem cancel_right (c L r : Q') (h : L*r ≈ 1) : (c*L)*r ≈ c :=
  Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ h) (Q'.mul_one_eqv c))

/-- A certificate bracket controls the actual normalized V-weighted scalar.
The denominator is positive data, not an inferred sign of a signed probe. -/
theorem massRatio_bounds {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) {f g : RatPoly}
    (hmass : (0 : Q') < weightedMass w K width g) (B : Bracket width f g) :
    B.lower ≤ massRatio w K width f g hmass ∧ massRatio w K width f g hmass ≤ B.upper := by
  let A := weightedMass w K width f
  let L := weightedMass w K width g
  let r := Q'.recipPos L hmass
  have hr : (0 : Q') ≤ r := Q'.le_of_lt (Q'.recipPos_pos _ hmass)
  have hl : B.lower*L ≤ A := Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _
    (weightedMass_nonnegative hw0 hw1 K width hK B.lowerCertificate)
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (weightedMass_add w K width _ _)
      (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _ (weightedMass_smul w K width _ _)
        (Q'.neg_mul_eqv B.lower L))))))
  have hu : A ≤ B.upper*L := Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _
    (weightedMass_nonnegative hw0 hw1 K width hK B.upperCertificate)
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (weightedMass_add w K width _ _)
      (Q'.add_eqv_congr' (weightedMass_smul w K width _ _)
        (Q'.eqv_trans _ _ _ (weightedMass_smul w K width _ _)
          (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 A)
            (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv A))))))))
  exact ⟨Q'.le_trans' _ _ _ (Q'.ge_of_eqv (cancel_right B.lower L r (Q'.mul_recipPos_eqv _ hmass)))
      (Q'.mul_le_mul_of_nonneg_right _ _ r hl hr),
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ r hu hr)
      (Q'.le_of_eqv (cancel_right B.upper L r (Q'.mul_recipPos_eqv _ hmass)))⟩

end YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracket

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracket.gain
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracket.ofInterval
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracket.gain_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracket.relativeFloorCertificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracket.refresh
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracket.massRatio
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracket.massRatio_bounds
