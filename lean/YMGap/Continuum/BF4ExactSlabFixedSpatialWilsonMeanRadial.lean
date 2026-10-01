/-
# Original Wilson radial energy about its SAME interacting mean

An exact Young square eliminates the unevaluated mixed radial moment.
For the literal fundamental trace f, actual odd mean c, chordal moments
L=H_edge[r]/Z and R=H_edge[r^2]/Z, and any supplied t >= 0,

  t*E/Z <= t^2*Var_odd(f) + (t+c^2)*R + t*(4-c^2)*L.

The original action, terminal depth, edge law and odd partition remain.
This is a finite one-loop estimate, not a signed-family scaling bound.
The mean correction and quartic/variance comparison are not assumed small.
-/

import YMGap.Continuum.QuaternionHaarRadialMeanYoung
import YMGap.Continuum.QuaternionHaarNormalizedMomentLinear
import YMGap.Continuum.QuaternionHaarIntervalSecondMoment
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonQuarticIncrement
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonMeanRadial

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
  (cap cap_mul_left cap_mul SquareBound character_squareBound characterBound)
open YMGap.Continuum.QuaternionHaarIntervalSecondMoment
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.QuaternionHaarNormalizedMomentCongruence
open YMGap.Continuum.QuaternionHaarNormalizedMomentLinear
open YMGap.Continuum.QuaternionHaarRadialMeanYoung
open YMGap.Continuum.QuaternionHaarWordDifference
open YMGap.Continuum.QuaternionHaarUnitScalarSquare (Supported)
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord (wordWith)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (orientedLink)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonKineticIncrement (upperOriented)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLinkQuartic
  (lower_supported upper_supported lower_unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard (oddVariance)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonRadialIncrement
  (wilson_energy_radial_cleared)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonQuarticIncrement
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks terminalMessage oddMass

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
variable (K width : Nat) (hK : headCutoff w ≤ K) (depth : Nat)

private def edgePositive :
    (0 : Q') < quaternionHaar (N width+N width)
      (edgeDensity w K width (terminalMessage w K width depth)) :=
  HeatKernelRGStep.lt_of_lt_of_le (oddMass_positive hw0 hw1 K width hK depth)
    (Q'.ge_of_eqv (edge_total_mass w K width depth))

/-- Normalize only by the ORIGINAL odd partition. -/
def edgeMoment (p : RatPoly) : Q' :=
  quaternionHaar (N width+N width)
    (polyMul (edgeDensity w K width (terminalMessage w K width depth)) p) *
      Q'.recipPos (oddMass w K width depth)
        (oddMass_positive hw0 hw1 K width hK depth)

private theorem normalized_edge_pin (p : RatPoly) :
    normalizedMoment (N width+N width)
      (edgeDensity w K width (terminalMessage w K width depth)) p
      (edgePositive hw0 hw1 K width hK depth) ≈
      edgeMoment hw0 hw1 K width hK depth p :=
  Q'.mul_eqv_congr_left _ _ _ (Q'.recipPos_eqv_congr _ _
    (edgePositive hw0 hw1 K width hK depth)
    (oddMass_positive hw0 hw1 K width hK depth) (edge_total_mass w K width depth))

/-- Every supported lower-end moment is the SAME odd one-slice moment. -/
theorem edgeMoment_pin {p : RatPoly} (hp : SupportedQuaternionBlocks (N width) p) :
    edgeMoment hw0 hw1 K width hK depth p ≈
      middleRatio hw0 hw1 K width hK (depth+1) depth p :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
    (edge_marginal_pairing w K width (terminalMessage_supported w K width depth) hp))
    (marginal_middleRatio hw0 hw1 K width hK depth p)

/-- This is the computed mean of the original edge law, not a new center. -/
def mean (f : RatPoly) : Q' :=
  normalizedMoment (N width+N width)
    (edgeDensity w K width (terminalMessage w K width depth)) f
    (edgePositive hw0 hw1 K width hK depth)

theorem mean_pin {f : RatPoly} (hf : SupportedQuaternionBlocks (N width) f) :
    mean hw0 hw1 K width hK depth f ≈
      middleRatio hw0 hw1 K width hK (depth+1) depth f :=
  Q'.eqv_trans _ _ _ (normalized_edge_pin hw0 hw1 K width hK depth f)
    (edgeMoment_pin hw0 hw1 K width hK depth hf)

private theorem haar_neg (n : Nat) : ∀ p : RatPoly,
    quaternionHaar n (polyNeg p) ≈ -(quaternionHaar n p)
  | [] => by change (0 : Q') ≈ -0; decide
  | u::ps => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv u.2 _) (haar_neg n ps))
      (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem normalized_neg {n : Nat} {W p : RatPoly}
    (hW : (0 : Q') < quaternionHaar n W) :
    normalizedMoment n W (polyNeg p) hW ≈ -(normalizedMoment n W p hW) :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
    (Q'.eqv_trans _ _ _ (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.neg (.var 1))) (.neg (.mul (.var 0) (.var 1)))
      (by decide) (fun | 0 => W | _ => p))) (haar_neg n _)))
    (Q'.neg_mul_eqv _ _)

private theorem normalized_cap_mul {n : Nat} {W : RatPoly}
    (hW : (0 : Q') < quaternionHaar n W) (a : Q') (p : RatPoly) :
    normalizedMoment n W (polyMul (cap a) p) hW ≈
      a*normalizedMoment n W p hW :=
  Q'.eqv_trans _ _ _
    (normalizedMoment_congr hW hW (RatPolyCoeffEqv.refl W) (cap_mul_left a p))
    (normalizedMoment_smul hW)

/-- Completing the square directly in the same edge law. No density floor
or sign/size of the interacting mean is used. -/
private theorem own_displacement_pin {n : Nat} {W f : RatPoly}
    (hW : (0 : Q') < quaternionHaar n W) :
    normalizedMoment n W
      (polyMul (displacement (normalizedMoment n W f hW) f)
        (displacement (normalizedMoment n W f hW) f)) hW ≈
      normalizedVariance n W f hW := by
  let c := normalizedMoment n W f hW
  have hexp : RatPolyCoeffEqv
      (polyMul (displacement c f) (displacement c f))
      (polyAdd (polyMul f f)
        (polyAdd (polyNeg (polyMul (cap 2) (polyMul (cap c) f)))
          (polyMul (cap c) (cap c)))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.add (.var 0) (.neg (.var 1))) (.add (.var 0) (.neg (.var 1))))
      (.add (.mul (.var 1) (.var 1))
        (.add (.neg (.mul (.const 2) (.mul (.var 0) (.var 1))))
          (.mul (.var 0) (.var 0)))) (by decide) (fun | 0 => cap c | _ => f)
  have hc : normalizedMoment n W (polyMul (cap c) (cap c)) hW ≈ c*c :=
    Q'.eqv_trans _ _ _ (normalized_cap_mul hW c (cap c))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (normalizedMoment_smul hW))
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left c _ _ (Q'.mul_eqv_congr_left c _ _ (normalizedMoment_one hW)))
          (Q'.mul_eqv_congr_left c _ _ (Q'.mul_one_eqv c))))
  have hx : normalizedMoment n W (polyMul (cap 2) (polyMul (cap c) f)) hW ≈
      2*(c*c) :=
    Q'.eqv_trans _ _ _ (normalized_cap_mul hW 2 _)
      (Q'.mul_eqv_congr_left 2 _ _ (normalized_cap_mul hW c f))
  have h := Q'.eqv_trans _ _ _
    (normalizedMoment_congr hW hW (RatPolyCoeffEqv.refl W) hexp)
    (Q'.eqv_trans _ _ _ (normalizedMoment_add hW)
      (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _ (normalizedMoment_add hW)
        (Q'.add_eqv_congr' (Q'.eqv_trans _ _ _ (normalized_neg hW)
          (Q'.neg_eqv_congr _ _ hx)) hc))))
  exact Q'.eqv_trans _ _ _ h (poly_identity_of_normal_eq
    (.add (.var 0) (.add (.neg (.mul (.const 2) (.mul (.var 1) (.var 1))))
      (.mul (.var 1) (.var 1))))
    (.add (.var 0) (.neg (.mul (.var 1) (.var 1)))) (by decide)
    (fun | 0 => normalizedMoment n W (polyMul f f) hW | _ => c))

/-- The lower-end square at the ACTUAL mean is exactly SAME oddVariance. -/
theorem centered_edge_square_pin {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    edgeMoment hw0 hw1 K width hK depth
      (polyMul (displacement (mean hw0 hw1 K width hK depth f) f)
        (displacement (mean hw0 hw1 K width hK depth f) f)) ≈
      oddVariance hw0 hw1 K width hK depth f := by
  have hmean := mean_pin hw0 hw1 K width hK depth hf
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (normalized_edge_pin hw0 hw1 K width hK depth _))
    (Q'.eqv_trans _ _ _ (own_displacement_pin (edgePositive hw0 hw1 K width hK depth))
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (normalized_edge_pin hw0 hw1 K width hK depth _)
          (edgeMoment_pin hw0 hw1 K width hK depth (supported_polyMul hf hf)))
        (Q'.neg_eqv_congr _ _ (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _ hmean) (Q'.mul_eqv_congr_left _ _ _ hmean)))))

private theorem norm_supported {n : Nat} {p : PolyQuaternion} (hp : Supported n p) :
    SupportedQuaternionBlocks n (polyQuaternionNorm p) :=
  supported_add (supported_polyMul hp.scalar hp.scalar)
    (supported_add (supported_polyMul hp.iPart hp.iPart)
      (supported_add (supported_polyMul hp.jPart hp.jPart) (supported_polyMul hp.kPart hp.kPart)))

private def normCertificate {n : Nat} {p : PolyQuaternion} (hp : Supported n p) :
    Certificate n (polyQuaternionNorm p) :=
  (Certificate.square p.scalar hp.scalar).add
    ((Certificate.square p.iPart hp.iPart).add
      ((Certificate.square p.jPart hp.jPart).add (Certificate.square p.kPart hp.kPart)))

/-- The ACTUAL odd mean has square at most four. The sharp cap comes from
the same literal Haar-unit word and the same positive edge certificate. -/
theorem mean_square_le_four (loop : SourceLoop width) :
    mean hw0 hw1 K width hK depth (sourceCharacter width loop.edges 1)*
      mean hw0 hw1 K width hK depth (sourceCharacter width loop.edges 1) ≤ (4 : Q') := by
  let W := edgeDensity w K width (terminalMessage w K width depth)
  let f := sourceCharacter width loop.edges 1
  have hf := sourceCharacter_supported width loop.edges 1
  have hf2 : SupportedQuaternionBlocks (N width+N width) f :=
    fun u hu => Nat.le_trans (hf u hu) (Nat.mul_le_mul_left 4 (Nat.le_add_right _ _))
  have hp := word_supported (orientedLink width) loop.edges
    (fun e he => lower_supported (loop.physical e he))
  have hu := word_unit (orientedLink width) loop.edges
    (fun e he => lower_unit (loop.physical e he))
  have P : SquareBound (N width+N width) f 4 :=
    SquareBound.changeCap (by decide : characterBound 1 ≈ (4 : Q'))
      (character_squareBound (SquareBound.scalar hp hu) 1)
  have H := edgeCertificate hw0 hw1 K width hK (terminalMessage_supported w K width depth)
    (terminalMessage_certificate hw0 hw1 K width hK depth)
  have hvar := normalizedVariance_nonnegative H (edgePositive hw0 hw1 K width hK depth) hf2
  exact Q'.le_trans' _ _ _ (Q'.le_of_sub_nonneg hvar)
    (Interval.normalized_square_le P H (edgePositive hw0 hw1 K width hK depth))

theorem radial_coefficient_nonnegative (loop : SourceLoop width) :
    (0 : Q') ≤ 4+ -(mean hw0 hw1 K width hK depth (sourceCharacter width loop.edges 1)*
      mean hw0 hw1 K width hK depth (sourceCharacter width loop.edges 1)) :=
  Q'.sub_nonneg_of_le (mean_square_le_four hw0 hw1 K width hK depth loop)

attribute [local irreducible] mean edgeMoment sourceCharacter wordChordal
  normalizedEnergy energy edgeDensity oddVariance

private theorem distribute_three (A B C P Q R a : Q') :
    (A*P+B*Q+C*R)*a ≈ A*(P*a)+B*(Q*a)+C*(R*a) :=
  poly_identity_of_normal_eq
    (.mul (.add (.add (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (.mul (.var 4) (.var 5))) (.var 6))
    (.add (.add (.mul (.var 0) (.mul (.var 1) (.var 6)))
      (.mul (.var 2) (.mul (.var 3) (.var 6)))) (.mul (.var 4) (.mul (.var 5) (.var 6))))
    (by decide) (fun | 0 => A | 1 => P | 2 => B | 3 => Q | 4 => C | 5 => R | _ => a)

/-- Eliminate the mixed radial term under the ORIGINAL law. All constants
and the actual mean remain explicit; no moment is factorized. -/
theorem wilson_energy_mean_moments (loop : SourceLoop width) (t : Q') (ht : (0 : Q') ≤ t) :
    t*normalizedEnergy hw0 hw1 K width hK depth (sourceCharacter width loop.edges 1) ≤
      (t*t)*oddVariance hw0 hw1 K width hK depth (sourceCharacter width loop.edges 1) +
      (t+mean hw0 hw1 K width hK depth (sourceCharacter width loop.edges 1)*
        mean hw0 hw1 K width hK depth (sourceCharacter width loop.edges 1))*
        edgeMoment hw0 hw1 K width hK depth (polyMul (wordChordal width loop) (wordChordal width loop)) +
      (t*(4+ -(mean hw0 hw1 K width hK depth (sourceCharacter width loop.edges 1)*
        mean hw0 hw1 K width hK depth (sourceCharacter width loop.edges 1))))*
        edgeMoment hw0 hw1 K width hK depth (wordChordal width loop) := by
  let W := edgeDensity w K width (terminalMessage w K width depth)
  let f := sourceCharacter width loop.edges 1
  let r := wordChordal width loop
  let c := mean hw0 hw1 K width hK depth f
  let a := Q'.recipPos (oddMass w K width depth) (oddMass_positive hw0 hw1 K width hK depth)
  have hf := sourceCharacter_supported width loop.edges 1
  have hf2 : SupportedQuaternionBlocks (N width+N width) f :=
    fun u hu => Nat.le_trans (hf u hu) (Nat.mul_le_mul_left 4 (Nat.le_add_right _ _))
  have hd := difference_supported
    (word_supported (orientedLink width) loop.edges (fun e he => lower_supported (loop.physical e he)))
    (word_supported (upperOriented width) loop.edges (fun e he => upper_supported (loop.physical e he)))
  have hr : SupportedQuaternionBlocks (N width+N width) r := by
    unfold r wordChordal
    exact norm_supported hd
  have hR : Certificate (N width+N width) r := by
    unfold r wordChordal
    exact normCertificate hd
  have hW := edgeCertificate hw0 hw1 K width hK (terminalMessage_supported w K width depth)
    (terminalMessage_certificate hw0 hw1 K width hK depth)
  have he2 := Q'.le_trans' _ _ _ (wilson_energy_radial_cleared hw0 hw1 K width hK depth loop)
    (Q'.le_of_eqv (radial_moment_split w K width depth loop))
  have he : energy w K width (terminalMessage w K width depth) f ≤
      mixedRadialMoment w K width depth loop + quaternionHaar (N width+N width) (polyMul W (polyMul r r)) := by
    exact Q'.le_of_mul_le_mul_left
      (Q'.le_trans' _ _ _ he2 (Q'.ge_of_eqv (Q'.mul_add_eqv _ _ _))) (by decide)
  have hy := weighted_young_moments hW hf2 hr hR c t ht
  have h := Q'.mul_le_mul_of_nonneg_right _ _ a
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ t he ht) hy)
    (Q'.le_of_lt (Q'.recipPos_pos _ (oddMass_positive hw0 hw1 K width hK depth)))
  have hright : ((t*t)*quaternionHaar (N width+N width) (polyMul W
        (polyMul (displacement c f) (displacement c f))) +
      (t+c*c)*quaternionHaar (N width+N width) (polyMul W (polyMul r r)) +
      (t*(4+ -(c*c)))*quaternionHaar (N width+N width) (polyMul W r))*a ≈
      (t*t)*edgeMoment hw0 hw1 K width hK depth (polyMul (displacement c f) (displacement c f)) +
      (t+c*c)*edgeMoment hw0 hw1 K width hK depth (polyMul r r) +
      (t*(4+ -(c*c)))*edgeMoment hw0 hw1 K width hK depth r := by
    unfold edgeMoment
    exact distribute_three (t*t) (t+c*c) (t*(4+ -(c*c))) _ _ _ a
  have hcenter : edgeMoment hw0 hw1 K width hK depth
      (polyMul (displacement c f) (displacement c f)) ≈
      oddVariance hw0 hw1 K width hK depth f :=
    centered_edge_square_pin hw0 hw1 K width hK depth hf
  have hbound : (t*energy w K width (terminalMessage w K width depth) f)*a ≤
      (t*t)*oddVariance hw0 hw1 K width hK depth f +
      (t+c*c)*edgeMoment hw0 hw1 K width hK depth (polyMul r r) +
      (t*(4+ -(c*c)))*edgeMoment hw0 hw1 K width hK depth r :=
    Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hright
      (Q'.add_eqv_congr_right _ _ _ (Q'.add_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_left (t*t) _ _ hcenter)))))
  have hleft : (t*energy w K width (terminalMessage w K width depth) f)*a ≈
      t*normalizedEnergy hw0 hw1 K width hK depth f := by
    unfold normalizedEnergy
    exact Q'.mul_assoc_eqv _ _ _
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft) hbound

#print axioms edgeMoment
#print axioms edgeMoment_pin
#print axioms mean
#print axioms mean_pin
#print axioms centered_edge_square_pin
#print axioms mean_square_le_four
#print axioms radial_coefficient_nonnegative
#print axioms wilson_energy_mean_moments

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonMeanRadial
