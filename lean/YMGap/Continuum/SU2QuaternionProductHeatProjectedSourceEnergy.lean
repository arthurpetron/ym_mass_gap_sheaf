/-
# Exact inactive-coordinate reduction of the FULL weighted heat energy

Let q=P_F a. When the observable f, not necessarily the complete source a,
is independent of the inactive family F, the original weighted energy equals
the full-product energy with source q. Every inactive-independent moment is
preserved as well. No inactive residual survives this exact FULL-energy
reduction. The signed projected-source correction is still retained.

This is finite polynomial/Haar algebra and a projected angular estimate,
not a same-variance scaling bound or continuum survival theorem.
-/

import YMGap.Continuum.SU2QuaternionProductHeatInactiveBilinear
import YMGap.Continuum.SU2QuaternionProductHeatAngularDefect

namespace YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatInactiveProjection
open YMGap.Continuum.SU2QuaternionProductHeatInactiveBilinear
open YMGap.Continuum.SU2QuaternionProductHeatAngularDefect
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2HeatCutoffCasimirBound
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

private theorem haar_neg (n : Nat) (p : RatPoly) :
    quaternionHaar n (polyNeg p) ≈ -(quaternionHaar n p) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (QuaternionHaarAngularCarrier.neg_smul p))
    (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul n (-1) p)
      (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
        (by decide) (fun _ => quaternionHaar n p)))

def sourceMoment (n : Nat) (w : Q') (K : Nat) (ids : List Nat) (a p : RatPoly) : Q' :=
  quaternionHaar n (polyMul (polyMul a p) (productMap n w K ids a))

def sourceEnergy (n : Nat) (w : Q') (K : Nat) (ids : List Nat) (a f : RatPoly) : Q' :=
  sourceMoment n w K ids a (polyMul f f) +
    -(quaternionHaar n (polyMul (polyMul a f) (productMap n w K ids (polyMul a f))))

/-- The signed correction is computed from the actual projected source;
it is not set to zero or bounded by an eigenvector premise. -/
def sourceCorrection (n : Nat) (w : Q') (K : Nat) (ids : List Nat) (a f : RatPoly) : Q' :=
  quaternionHaar n (polyMul (polyMul a (polyMul f f))
    (polyAdd (productMap n w K ids a) (polyNeg a)))

private theorem project_source_test (F : List Nat) (a p : RatPoly)
    (hp : ∀ i, i ∈ F → QuaternionBlockIndependent i p) :
    RatPolyCoeffEqv (familyProject F (polyMul a p)) (polyMul (familyProject F a) p) :=
  (familyProject_congr F (RatPolyCoeffEqv.mul_comm a p)).trans
    ((familyProject_mul_of_independent F p a hp).trans (RatPolyCoeffEqv.mul_comm _ _))

/-- Partition, first and second moments all reduce by the SAME identity.
Only the insertion p is required to be inactive-independent, not the source. -/
theorem sourceMoment_project (n : Nat) (w : Q') (K : Nat) (ids F : List Nat)
    (hids : ∀ i, i ∈ ids → i < n) (hF : ∀ i, i ∈ F → i < n)
    (hnot : ∀ i, i ∈ F → i ∉ ids) (hcover : (F++ids).Perm (List.range n))
    (a p : RatPoly) (ha : SupportedQuaternionBlocks n a)
    (hp : SupportedQuaternionBlocks n p)
    (hind : ∀ i, i ∈ F → QuaternionBlockIndependent i p) :
    sourceMoment n w K ids a p ≈
      sourceMoment n w K (List.range n) (familyProject F a) p :=
  Q'.eqv_trans _ _ _
    (productMap_inactive_to_full_bilinear n w K ids F hids hF hnot hcover
      a (polyMul a p) ha (supported_polyMul ha hp))
    (haar_of_coeff ((project_source_test F a p hind).mul_right _))

/-- Exact FULL-energy projection. Applying an unweighted estimate before
this identity would unnecessarily retain an inactive residual. -/
theorem sourceEnergy_project (n : Nat) (w : Q') (K : Nat) (ids F : List Nat)
    (hids : ∀ i, i ∈ ids → i < n) (hF : ∀ i, i ∈ F → i < n)
    (hnot : ∀ i, i ∈ F → i ∉ ids) (hcover : (F++ids).Perm (List.range n))
    (a f : RatPoly) (ha : SupportedQuaternionBlocks n a)
    (hf : SupportedQuaternionBlocks n f)
    (hind : ∀ i, i ∈ F → QuaternionBlockIndependent i f) :
    sourceEnergy n w K ids a f ≈
      sourceEnergy n w K (List.range n) (familyProject F a) f := by
  have hmoment := sourceMoment_project n w K ids F hids hF hnot hcover a (polyMul f f)
    ha (supported_polyMul hf hf)
    (fun i hi => quaternionBlockIndependent_polyMul (hind i hi) (hind i hi))
  have htest := project_source_test F a f hind
  have hmap := productMap_congr n w K (List.range n) htest
  have hcross := Q'.eqv_trans _ _ _
    (productMap_inactive_to_full_pairing n w K ids F hids hF hnot hcover
      (polyMul a f) (supported_polyMul ha hf))
    (haar_of_coeff (htest.mul hmap))
  exact Q'.add_eqv_congr' hmoment (Q'.neg_eqv_congr _ _ hcross)

private theorem correction_expand (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (a f : RatPoly) : sourceCorrection n w K ids a f ≈
      sourceMoment n w K ids a (polyMul f f) +
        -(quaternionHaar n (polyMul (polyMul a f) (polyMul a f))) := by
  have hc : RatPolyCoeffEqv
      (polyMul (polyMul a (polyMul f f)) (polyAdd (productMap n w K ids a) (polyNeg a)))
      (polyAdd (polyMul (polyMul a (polyMul f f)) (productMap n w K ids a))
        (polyNeg (polyMul (polyMul a f) (polyMul a f)))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.add (.var 2) (.neg (.var 0))))
      (.add (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.var 2))
        (.neg (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))))
      (by decide) (fun | 0 => a | 1 => f | _ => productMap n w K ids a)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hc)
    (Q'.eqv_trans _ _ _ (quaternionHaar_append n _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (haar_neg n _)))

theorem sourceEnergy_split (n : Nat) (w : Q') (K : Nat) (ids : List Nat) (a f : RatPoly) :
    sourceEnergy n w K ids a f ≈
      (quaternionHaar n (polyMul (polyMul a f) (polyMul a f)) +
        -(quaternionHaar n (polyMul (polyMul a f) (productMap n w K ids (polyMul a f))))) +
      sourceCorrection n w K ids a f := by
  exact Q'.eqv_trans _ _ _ (by
    unfold sourceEnergy
    exact poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.var 2)))
      (.add (.add (.var 1) (.neg (.var 2))) (.add (.var 0) (.neg (.var 1))))
      (by decide) (fun | 0 => sourceMoment n w K ids a (polyMul f f)
                       | 1 => quaternionHaar n (polyMul (polyMul a f) (polyMul a f))
                       | _ => quaternionHaar n
                           (polyMul (polyMul a f) (productMap n w K ids (polyMul a f)))))
    (Q'.add_eqv_congr' (Q'.eqv_refl _) (correction_expand n w K ids a f).symm)

/-- The actual projected-source bound has NO inactive residual. Its signed
source correction and the derivatives of the complete projected source remain. -/
theorem sourceEnergy_le_projectedAngular_add_correction (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat) (hK : sufficientCutoff w ≤ K)
    (ids F : List Nat) (hids : ∀ i, i ∈ ids → i < tail+1)
    (hF : ∀ i, i ∈ F → i < tail+1) (hnot : ∀ i, i ∈ F → i ∉ ids)
    (hcover : (F++ids).Perm (List.range (tail+1))) (a f : RatPoly)
    (ha : SupportedQuaternionBlocks (tail+1) a) (hf : SupportedQuaternionBlocks (tail+1) f)
    (hind : ∀ i, i ∈ F → QuaternionBlockIndependent i f) :
    sourceEnergy (tail+1) w K ids a f ≤
      (2*((1 : Q')-w)) * finSum (fun i => quaternionHaar (tail+1)
        (blockAngularSquare i (polyMul (familyProject F a) f))) (tail+1) +
      sourceCorrection (tail+1) w K (List.range (tail+1)) (familyProject F a) f := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (sourceEnergy_project (tail+1) w K ids F hids hF hnot hcover a f ha hf hind)
      (sourceEnergy_split (tail+1) w K (List.range (tail+1)) (familyProject F a) f)))
    (Q'.add_le_add_right _ _ _ (productMap_range_defect_le_two_angular tail hw0 hw1 K hK
      (polyMul (familyProject F a) f) (supported_polyMul (familyProject_supported F ha) hf)))

end YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy

#print axioms YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy.sourceMoment_project
#print axioms YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy.sourceEnergy_project
#print axioms YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy.sourceEnergy_split
#print axioms YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy.sourceEnergy_le_projectedAngular_add_correction
