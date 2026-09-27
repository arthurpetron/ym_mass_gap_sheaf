/-
# Signed conditional covariance with shared exterior variables

Only the selected original coordinates are copied into the auxiliary slice.
The exterior insertion is retained ONCE, and the conditional moments remain
polynomials in the common exterior variables. No normalization, positivity,
rate, completed-operator estimate or continuum conclusion is asserted.

The next consumer is the crossed four-copy shared-face determinant: this
module supplies its uncrossed mixed replica identity for the actual Haar
functional, not an assumed integration interface.
-/

import YMGap.Continuum.SU2QuaternionPartialSwapPairing
import YMGap.Continuum.QuaternionHaarAngularCarrier

namespace YMGap.Continuum.SU2QuaternionFamilyCovarianceReplica

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini (SupportedQuaternionBlocks)
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
  (QuaternionBlockIndependent)
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionPartialSliceSwap
open YMGap.Continuum.SU2QuaternionPartialSwapPairing
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

abbrev replica (n : Nat) (ids : List Nat) (p : RatPoly) : RatPoly :=
  reindexQuaternionPolynomial (swap n ids) p

def difference (n : Nat) (ids : List Nat) (p : RatPoly) : RatPoly :=
  polyAdd p (polyNeg (replica n ids p))

/-- Division-free covariance numerator; all four moments share the exterior. -/
def covarianceNumerator (ids : List Nat) (K f g : RatPoly) : RatPoly :=
  polyAdd
    (polyMul (familyProject ids K) (familyProject ids (polyMul K (polyMul f g))))
    (polyNeg (polyMul (familyProject ids (polyMul K f))
      (familyProject ids (polyMul K g))))

def mixedEnergy (n : Nat) (ids : List Nat) (K f g : RatPoly) : RatPoly :=
  polyMul (polyMul K (replica n ids K))
    (polyMul (difference n ids f) (difference n ids g))

/-- The exterior insertion is not copied, squared, or integrated separately. -/
theorem spectator_pairing (n : Nat) (ids : List Nat) (r p q : RatPoly)
    (hr : SupportedQuaternionBlocks n r)
    (hp : SupportedQuaternionBlocks n p) (hq : SupportedQuaternionBlocks n q)
    (hind : ∀ i, i ∈ ids → QuaternionBlockIndependent i r)
    (hnodup : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n) :
    quaternionHaar (n+n) (polyMul r (polyMul p (replica n ids q))) ≈
      quaternionHaar n (polyMul r
        (polyMul (familyProject ids p) (familyProject ids q))) := by
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _).symm)
    (Q'.eqv_trans _ _ _
      (partialSwap_familyProject_pairing n ids (polyMul r p) q
        (supported_polyMul hr hp) hq hnodup hids)
      (haar_of_coeff (((familyProject_mul_of_independent ids r p hind).mul_right _).trans
        (RatPolyCoeffEqv.mul_assoc _ _ _))))

theorem pair_add_congr {n m : Nat} (r : RatPoly) {a b c d : RatPoly}
    (ha : quaternionHaar n (polyMul r a) ≈ quaternionHaar m (polyMul r c))
    (hb : quaternionHaar n (polyMul r b) ≈ quaternionHaar m (polyMul r d)) :
    quaternionHaar n (polyMul r (polyAdd a b)) ≈
      quaternionHaar m (polyMul r (polyAdd c d)) :=
  Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_add_right n r a b)
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' ha hb)
      (Q'.eqv_symm (quaternionHaar_polyMul_add_right m r c d)))

private theorem haar_neg (n : Nat) : ∀ p : RatPoly,
    quaternionHaar n (polyNeg p) ≈ -quaternionHaar n p
  | [] => Q'.eqv_refl _
  | t::p => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv _ _) (haar_neg n p))
      (Q'.eqv_symm (Q'.neg_add_eqv _ _))

private theorem pair_neg (n : Nat) (r p : RatPoly) :
    quaternionHaar n (polyMul r (polyNeg p)) ≈
      -quaternionHaar n (polyMul r p) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.var 0) (.neg (.var 1))) (.neg (.mul (.var 0) (.var 1)))
    (by decide) (fun | 0 => r | _ => p))) (haar_neg n _)

theorem pair_neg_congr {n m : Nat} (r : RatPoly) {a b : RatPoly}
    (h : quaternionHaar n (polyMul r a) ≈ quaternionHaar m (polyMul r b)) :
    quaternionHaar n (polyMul r (polyNeg a)) ≈
      quaternionHaar m (polyMul r (polyNeg b)) :=
  Q'.eqv_trans _ _ _ (pair_neg n r a)
    (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ h) (Q'.eqv_symm (pair_neg m r b)))

private def expansion (n : Nat) (ids : List Nat) (K f g : RatPoly) : RatPoly :=
  polyAdd
    (polyAdd (polyMul (polyMul K (polyMul f g)) (replica n ids K))
      (polyMul K (replica n ids (polyMul K (polyMul f g)))))
    (polyAdd (polyNeg (polyMul (polyMul K f) (replica n ids (polyMul K g))))
      (polyNeg (polyMul (polyMul K g) (replica n ids (polyMul K f)))))

theorem mixedEnergy_expansion (n : Nat) (ids : List Nat) (K f g : RatPoly) :
    RatPolyCoeffEqv (mixedEnergy n ids K f g) (expansion n ids K f g) := by
  dsimp only [mixedEnergy, difference, expansion, replica]
  simp only [reindexQuaternionPolynomial_mul]
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.var 1))
      (.mul (.add (.var 2) (.neg (.var 3))) (.add (.var 4) (.neg (.var 5)))))
    (.add
      (.add (.mul (.mul (.var 0) (.mul (.var 2) (.var 4))) (.var 1))
        (.mul (.var 0) (.mul (.var 1) (.mul (.var 3) (.var 5)))))
      (.add (.neg (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 5))))
        (.neg (.mul (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 3))))))
    (by decide)
    (fun | 0 => K | 1 => replica n ids K | 2 => f | 3 => replica n ids f
         | 4 => g | _ => replica n ids g)

/-- Exact signed mixed replica identity, valid also for jointly dependent
tests. No single-block assumption is needed until the crossed determinant. -/
theorem mixed_identity (n : Nat) (ids : List Nat) (K f g r : RatPoly)
    (hK : SupportedQuaternionBlocks n K)
    (hf : SupportedQuaternionBlocks n f) (hg : SupportedQuaternionBlocks n g)
    (hr : SupportedQuaternionBlocks n r)
    (hind : ∀ i, i ∈ ids → QuaternionBlockIndependent i r)
    (hnodup : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n) :
    quaternionHaar (n+n) (polyMul r (mixedEnergy n ids K f g)) ≈
      quaternionHaar n (polyMul r
        (polyAdd (covarianceNumerator ids K f g) (covarianceNumerator ids K f g))) := by
  have hfg := supported_polyMul hK (supported_polyMul hf hg)
  have hKf := supported_polyMul hK hf
  have hKg := supported_polyMul hK hg
  have h₁ := spectator_pairing n ids r (polyMul K (polyMul f g)) K hr hfg hK hind hnodup hids
  have h₂ := spectator_pairing n ids r K (polyMul K (polyMul f g)) hr hK hfg hind hnodup hids
  have h₃ := spectator_pairing n ids r (polyMul K f) (polyMul K g) hr hKf hKg hind hnodup hids
  have h₄ := spectator_pairing n ids r (polyMul K g) (polyMul K f) hr hKg hKf hind hnodup hids
  refine Q'.eqv_trans _ _ _ (haar_of_coeff ((mixedEnergy_expansion n ids K f g).mul_left r))
    (Q'.eqv_trans _ _ _
      (pair_add_congr r (pair_add_congr r h₁ h₂)
        (pair_add_congr r (pair_neg_congr r h₃) (pair_neg_congr r h₄))) ?_)
  exact haar_of_coeff ((coeffEvalExpr_eqv_of_normalize_eq
    (.add (.add (.mul (.var 1) (.var 0)) (.mul (.var 0) (.var 1)))
      (.add (.neg (.mul (.var 2) (.var 3))) (.neg (.mul (.var 3) (.var 2)))))
    (.add (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 2) (.var 3))))
      (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 2) (.var 3)))))
    (by decide)
    (fun | 0 => familyProject ids K | 1 => familyProject ids (polyMul K (polyMul f g))
         | 2 => familyProject ids (polyMul K f) | _ => familyProject ids (polyMul K g))).mul_left r)

#print axioms spectator_pairing
#print axioms pair_add_congr
#print axioms pair_neg_congr
#print axioms mixedEnergy_expansion
#print axioms mixed_identity

end YMGap.Continuum.SU2QuaternionFamilyCovarianceReplica
