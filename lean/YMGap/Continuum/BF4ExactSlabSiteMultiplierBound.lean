/-
# Fixed-slice multiplication is bounded in the ORIGINAL selected OS form

A supported fixed-slice polynomial a with the existing algebraic certificate
for c-a^2 gives the finite reflected estimate Q(a*p) <= c*Q(p). Here Q uses
the literal slab reflection and the COMPLETE selected heat action. The proof
dresses p by the lower action and applies the existing conditional-square
positivity to (c-a^2) times the original fixed action. Locality is required of
that weight, not of the square features in its certificate.

No ordinary-Haar norm is substituted for the OS form, and no interacting
factor is deleted. The nome/cutoff and selected-list reflection guards are
explicit. This is a finite numerator estimate; normalized regulator limits,
the actual completed multiplier, and canonical OS/QFT realization are separate
consumers. No multiplication on arbitrary OS-null states is assumed.
-/

import YMGap.Continuum.BF4ExactSlabSiteSelectedHeatAction
import YMGap.Continuum.QuaternionHaarPolynomialSquareBound
import YMGap.Constructive.Soundness

namespace YMGap.Continuum.BF4ExactSlabSiteMultiplierBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabSpatialChannelReflection
open YMGap.Continuum.BF4ExactSlabSiteHaarFactorization
open YMGap.Continuum.BF4ExactSlabSiteBoundaryReflection
open YMGap.Continuum.BF4ExactSlabSiteConditionalSquare
open YMGap.Continuum.BF4ExactSlabSiteWeightedSquare
open YMGap.Continuum.BF4ExactSlabSiteSelectedHeatAction
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry

local infix:50 " ≈ " => Q'.eqv

private theorem support_smul {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (c : Q') :
    SupportedQuaternionBlocks blocks (polySmul c p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem haar_neg (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks (polyNeg p) ≈ -(quaternionHaar blocks p)
  | [] => by change (0 : Q') ≈ -0; decide
  | t::rest => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono blocks t.1))
        (haar_neg blocks rest))
      (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

/-- A certified fixed-slice insertion remains nonnegative against the full
selected reflected action. Its certificate features need not be fixed-local. -/
theorem selectedAction_fixed_weight_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K radius : Nat) (hK : headCutoff w ≤ K) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges (adjacentEvenExtent radius))
    (hreflection : ((lowerFaceIds radius ids).map
      (slabFaceReflectId (adjacentEvenExtent radius))).Perm (upperFaceIds radius ids))
    (p b : RatPoly) (hp : OneSided radius p)
    (hs : SupportedQuaternionBlocks (blockCount radius) p)
    (hb : SupportedQuaternionBlocks (blockCount radius) b)
    (lb : Local radius .fixed b) (cert : Certificate (blockCount radius) b) :
    (0 : Q') ≤ quaternionHaar (blockCount radius)
      (polyMul (polyMul
        (polyMul (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) p) p)
        (selectedHeat w K radius ids)) b) := by
  let d := polyMul p (lowerHeat w K radius ids)
  let W := polyMul b (fixedHeat w K radius ids)
  have hd : SupportedQuaternionBlocks (blockCount radius) d :=
    supported_polyMul hs (lowerHeat_supported w K radius ids)
  have hW : SupportedQuaternionBlocks (blockCount radius) W :=
    supported_polyMul hb (fixedHeat_supported w K radius ids)
  have lW : Local radius .fixed W := lb.mul (fixedHeat_local w K radius ids hids)
  have hnonneg := certified_weighted_nonnegative radius d W
    (hp.mul (lowerHeat_oneSided w K radius ids)) hd hW lW
    (cert.mul (fixedHeatCertificate hw0 hw1 K radius hK ids hids))
  let core := polyMul (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) d) d
  have hcore : SupportedQuaternionBlocks (blockCount radius) core :=
    supported_polyMul (reflectCorrectedSlabPolynomial_support _ _) hd
  have hswap : RatPolyCoeffEqv (polyMul core W)
      (polyMul (polyMul core (fixedHeat w K radius ids)) b) :=
    ((RatPolyCoeffEqv.mul_comm b (fixedHeat w K radius ids)).mul_left core).trans
      (RatPolyCoeffEqv.mul_assoc core (fixedHeat w K radius ids) b).symm
  have hpin := (PaddedPolynomialCoeffEqv.of_coeff hswap).trans
    ((selectedAction_dressing w K radius ids hids hreflection p).mul
      (PaddedPolynomialCoeffEqv.refl _ b))
  exact Q'.le_trans' _ _ _ hnonneg (Q'.le_of_eqv (hpin.haar
    (supported_polyMul hcore hW)
    (supported_polyMul
      (supported_polyMul
        (supported_polyMul (reflectCorrectedSlabPolynomial_support _ _) hs)
        (selectedHeat_supported w K radius ids)) hb)))

/-- The exact same-action OS numerator bound for multiplication by a fixed-slice
observable. SquareBound supplies the supported polynomial and its actual cap certificate. -/
theorem selectedAction_multiplier_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K radius : Nat) (hK : headCutoff w ≤ K) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges (adjacentEvenExtent radius))
    (hreflection : ((lowerFaceIds radius ids).map
      (slabFaceReflectId (adjacentEvenExtent radius))).Perm (upperFaceIds radius ids))
    (p a : RatPoly) (hp : OneSided radius p)
    (hs : SupportedQuaternionBlocks (blockCount radius) p)
    (ha : Local radius .fixed a) {c : Q'} (A : SquareBound (blockCount radius) a c) :
    quaternionHaar (blockCount radius)
      (polyMul (polyMul
        (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) (polyMul a p))
        (polyMul a p)) (selectedHeat w K radius ids)) ≤
    c * quaternionHaar (blockCount radius)
      (polyMul (polyMul (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) p) p)
        (selectedHeat w K radius ids)) := by
  let F := polyMul (polyMul
    (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) p) p)
    (selectedHeat w K radius ids)
  have hF : SupportedQuaternionBlocks (blockCount radius) F :=
    supported_polyMul (supported_polyMul (reflectCorrectedSlabPolynomial_support _ _) hs)
      (selectedHeat_supported w K radius ids)
  have hgap : SupportedQuaternionBlocks (blockCount radius) (gap c a) :=
    supported_add (support_smul (supported_one _) c)
      (support_neg (supported_polyMul A.support A.support))
  have lgap : Local radius .fixed (gap c a) :=
    ((BlockLocal.one (blockCount radius) (fun b => blockSide radius b = .fixed)).smul c).add
      (ha.mul ha).neg
  have hnonneg := selectedAction_fixed_weight_nonnegative hw0 hw1 K radius hK ids
    hids hreflection p (gap c a) hp hs hgap lgap A.certificate
  have haReflection := (boundary_reflection ha).mul
    (show ReflectionImage (adjacentEvenExtent radius) p
      (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) p) from .refl _ _)
  have hmultPoly : PaddedPolynomialCoeffEqv (blockCount radius)
      (polyMul (polyMul
        (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) (polyMul a p))
        (polyMul a p)) (selectedHeat w K radius ids))
      (polyMul F (polyMul a a)) := by
    refine ((PaddedPolynomialCoeffEqv.mul haReflection
      (PaddedPolynomialCoeffEqv.refl _ (polyMul a p))).mul
      (PaddedPolynomialCoeffEqv.refl _ (selectedHeat w K radius ids))).trans ?_
    exact PaddedPolynomialCoeffEqv.of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2))) (.var 3))
      (.mul (.mul (.mul (.var 1) (.var 2)) (.var 3)) (.mul (.var 0) (.var 0)))
      (by decide) (fun
        | 0 => a
        | 1 => reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) p
        | 2 => p
        | _ => selectedHeat w K radius ids))
  have hmult := hmultPoly.haar
    (supported_polyMul
      (supported_polyMul (reflectCorrectedSlabPolynomial_support _ _)
        (supported_polyMul A.support hs)) (selectedHeat_supported w K radius ids))
    (supported_polyMul hF (supported_polyMul A.support A.support))
  have hexpand : RatPolyCoeffEqv (polyMul F (gap c a))
      (polyAdd (polySmul c F) (polyNeg (polyMul F (polyMul a a)))) :=
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.add (.var 1) (.neg (.mul (.var 2) (.var 2)))))
      (.add (.mul (.var 1) (.var 0)) (.neg (.mul (.var 0) (.mul (.var 2) (.var 2)))))
      (by decide) (fun | 0 => F | 1 => cap c | _ => a)).trans
      ((cap_mul_left c F).add (RatPolyCoeffEqv.refl _))
  have hscalar := Q'.eqv_trans _ _ _ (haar_of_coeff hexpand)
    (Q'.eqv_trans _ _ _ (quaternionHaar_append (blockCount radius) _ _)
      (Q'.add_eqv_congr' (quaternionHaar_polySmul (blockCount radius) c F)
        (Q'.eqv_trans _ _ _ (haar_neg (blockCount radius) _)
          (Q'.neg_eqv_congr _ _ (Q'.eqv_symm hmult)))))
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hnonneg (Q'.le_of_eqv hscalar))

#print axioms selectedAction_fixed_weight_nonnegative
#print axioms selectedAction_multiplier_bound

end YMGap.Continuum.BF4ExactSlabSiteMultiplierBound
