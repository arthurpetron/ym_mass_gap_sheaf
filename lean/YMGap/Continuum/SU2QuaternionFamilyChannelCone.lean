/-
# Positive-cone control of the actual conditional channel quadratic

Only the selected coordinates are independently copied. Every other coordinate
is shared by the two endpoints. The actual positive product kernel therefore
gives mixed positivity for certified positive sources, despite the signs of
individual Gram-channel polynomials. The cone pair c*p-d, c*p+d then controls
the SAME channel quadratic of d by c^2 times that of p.

No partial productMap is substituted for conditional heat. No normalized
variance, scaling bound or physical spectral conclusion is asserted.
-/

import YMGap.Continuum.SU2QuaternionPartialSwapPairing
import YMGap.Continuum.SU2QuaternionProductHeatContraction
import YMGap.Continuum.SU2QuaternionProductHeatGramLocality
import YMGap.Continuum.SU2QuaternionFamilyChannelLoss
import YMGap.Continuum.QuaternionHaarRelativeAngularBound

namespace YMGap.Continuum.SU2QuaternionFamilyChannelCone

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularSupport (polySmul_supported)
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatContraction
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatGramLocality
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionFamilyChannelLoss
open YMGap.Continuum.SU2QuaternionPartialSwapPairing
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarRelativeAngularBound

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

/-- The bilinear extension of the existing conditional channel quadratic. -/
def familyChannelPair (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (u v : RatPoly) : Q' :=
  channelSum (productChannels n w K ids) (fun c => H n
    (polyMul (familyProject ids (polyMul u c))
      (familyProject ids (polyMul v c))))

theorem familyChannelPair_self (n : Nat) (w : Q') (K : Nat)
    (ids : List Nat) (p : RatPoly) :
    familyChannelPair n w K ids p p = familyChannelQuadratic n w K ids p := rfl

private theorem channel_term_pair (n : Nat) (ids : List Nat) (u v c : RatPoly)
    (hu : SupportedQuaternionBlocks n u) (hv : SupportedQuaternionBlocks n v)
    (hc : SupportedQuaternionBlocks n c)
    (hci : ∀ j, j < n → j ∉ ids → QuaternionBlockIndependent j c)
    (hn : ids.Nodup) (hids : ∀ j, j ∈ ids → j < n) :
    H (n+n) (polyMul (polyMul c (liftBoundary n c))
      (polyMul u (reindexQuaternionPolynomial (SU2QuaternionPartialSliceSwap.swap n ids) v))) ≈
    H n (polyMul (familyProject ids (polyMul u c))
      (familyProject ids (polyMul v c))) := by
  let s := SU2QuaternionPartialSliceSwap.swap n ids
  have hr := SU2QuaternionPartialSliceSwap.reindex_to_lift n ids c hc hci
  have hfirst : HaarCarrierEqv (n+n)
      (polyMul c (liftBoundary n c)) (polyMul c (reindexQuaternionPolynomial s c)) :=
    HaarCarrierEqv.mul_left c hr.symm
  have ha : RatPolyCoeffEqv
      (polyMul (polyMul c (reindexQuaternionPolynomial s c))
        (polyMul u (reindexQuaternionPolynomial s v)))
      (polyMul (polyMul u c) (reindexQuaternionPolynomial s (polyMul v c))) := by
    rw [reindexQuaternionPolynomial_mul]
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (.mul (.mul (.var 2) (.var 0)) (.mul (.var 3) (.var 1))) (by decide)
      (fun | 0 => c | 1 => reindexQuaternionPolynomial s c
           | 2 => u | _ => reindexQuaternionPolynomial s v)
  exact Q'.eqv_trans _ _ _
    (haar_of_carrier (HaarCarrierEqv.mul_right _ hfirst))
    (Q'.eqv_trans _ _ _ (haar_of_coeff ha)
      (partialSwap_familyProject_pairing n ids (polyMul u c) (polyMul v c)
        (supported_polyMul hu hc) (supported_polyMul hv hc) hn hids))

private theorem channel_kernel_pair (n : Nat) (ids : List Nat) (u v : RatPoly)
    (hu : SupportedQuaternionBlocks n u) (hv : SupportedQuaternionBlocks n v)
    (hn : ids.Nodup) (hids : ∀ j, j ∈ ids → j < n) :
    ∀ cs : List GramChannel,
      (∀ c, c ∈ cs → SupportedQuaternionBlocks n c.2) →
      (∀ c, c ∈ cs → ∀ j, j < n → j ∉ ids → QuaternionBlockIndependent j c.2) →
      H (n+n) (polyMul (channelKernel n cs)
        (polyMul u (reindexQuaternionPolynomial (SU2QuaternionPartialSliceSwap.swap n ids) v))) ≈
      channelSum cs (fun c => H n (polyMul
        (familyProject ids (polyMul u c)) (familyProject ids (polyMul v c))))
  | [], _, _ => haar_of_coeff (RatPolyCoeffEqv.mul_zero_left _)
  | c::cs, hc, hi => by
      let test := polyMul u
        (reindexQuaternionPolynomial (SU2QuaternionPartialSliceSwap.swap n ids) v)
      have hs : H (n+n) (polyMul
          (polySmul c.1 (polyMul c.2 (liftBoundary n c.2))) test) ≈
          c.1 * H n (polyMul (familyProject ids (polyMul u c.2))
            (familyProject ids (polyMul v c.2))) :=
        Q'.eqv_trans _ _ _
          (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left c.1 _ test))
          (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul _ _ _)
            (Q'.mul_eqv_congr_left _ _ _
              (channel_term_pair n ids u v c.2 hu hv
                (hc c List.mem_cons_self) (hi c List.mem_cons_self) hn hids)))
      change H (n+n) (polyMul (polyAdd _ _) test) ≈ _
      rw [polyMul_add_left_exact]
      exact Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
        (Q'.add_eqv_congr' hs (channel_kernel_pair n ids u v hu hv hn hids cs
          (fun d hd => hc d (List.mem_cons_of_mem c hd))
          (fun d hd => hi d (List.mem_cons_of_mem c hd))))

/-- Exact original-kernel identification, with all unselected variables
shared. This is not a pairing of the partial productMap. -/
theorem familyChannelPair_eq_conditionalKernel (n : Nat) (w : Q') (K : Nat)
    (ids : List Nat) (hn : ids.Nodup) (hids : ∀ j, j ∈ ids → j < n)
    (u v : RatPoly) (hu : SupportedQuaternionBlocks n u)
    (hv : SupportedQuaternionBlocks n v) :
    familyChannelPair n w K ids u v ≈
      H (n+n) (polyMul (productHeat n w K ids)
        (polyMul u (reindexQuaternionPolynomial (SU2QuaternionPartialSliceSwap.swap n ids) v))) := by
  apply Q'.eqv_symm
  exact Q'.eqv_trans _ _ _
    (haar_of_carrier (HaarCarrierEqv.mul_right _ (productHeat_gram_carrier n w K ids hids)))
    (channel_kernel_pair n ids u v hu hv hn hids _
      (productChannels_supported n w K ids hids)
      (fun c hc j _ hj => productChannels_independent n w K ids j hj c hc))

/-- Mixed positivity comes from the actual conditional positive kernel;
the individual channel polynomials may be signed. -/
theorem familyChannelPair_nonnegative (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) (hK : headCutoff w ≤ K)
    (ids : List Nat) (hn : ids.Nodup) (hids : ∀ j, j ∈ ids → j < n)
    (u v : RatPoly) (hu : SupportedQuaternionBlocks n u)
    (hv : SupportedQuaternionBlocks n v) (U : Certificate n u) (V : Certificate n v) :
    (0 : Q') ≤ familyChannelPair n w K ids u v := by
  have hv' : SupportedQuaternionBlocks (n+n) v :=
    fun t ht => Nat.le_trans (hv t ht) (Nat.mul_le_mul_left 4 (by omega))
  have C := (productHeatCertificate n hw0 hw1 K hK ids hids).mul
    ((certificate_extend n hu U).mul
      (reindex_certificate (SU2QuaternionPartialSliceSwap.swap n ids) hv'
        (certificate_extend n hv V)))
  exact Q'.le_trans' _ _ _ C.haar_nonnegative
    (Q'.ge_of_eqv (familyChannelPair_eq_conditionalKernel n w K ids hn hids u v hu hv))

private theorem haar_neg (n : Nat) : ∀ p : RatPoly,
    H n (polyNeg p) ≈ -(H n p)
  | [] => by change (0 : Q') ≈ -0; decide
  | t::ts => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono n t.1)) (haar_neg n ts))
      (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem projected_cone_pair (n : Nat) (ids : List Nat) (p d h : RatPoly) (c : Q') :
    H n (polyMul
      (familyProject ids (polyMul (polyAdd (polyMul (cap c) p) (polyNeg d)) h))
      (familyProject ids (polyMul (polyAdd (polyMul (cap c) p) d) h))) ≈
      (c*c) * H n (polyMul (familyProject ids (polyMul p h))
        (familyProject ids (polyMul p h))) +
      -(H n (polyMul (familyProject ids (polyMul d h))
        (familyProject ids (polyMul d h)))) := by
  let a := familyProject ids (polyMul p h)
  let b := familyProject ids (polyMul d h)
  have hscale : RatPolyCoeffEqv (familyProject ids (polyMul (polyMul (cap c) p) h))
      (polyMul (cap c) a) :=
    (familyProject_congr ids (RatPolyCoeffEqv.mul_assoc _ _ _)).trans
      (familyProject_mul_of_independent ids (cap c) (polyMul p h)
        (fun j _ => quaternionBlockIndependent_polySmul c (quaternionBlockIndependent_polyOne j)))
  have hneg : RatPolyCoeffEqv (familyProject ids (polyMul (polyNeg d) h)) (polyNeg b) :=
    (familyProject_congr ids (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.neg (.var 0)) (.var 1)) (.neg (.mul (.var 0) (.var 1)))
      (by decide) (fun | 0 => d | _ => h))).trans (familyProject_neg ids _)
  have hm : RatPolyCoeffEqv
      (familyProject ids (polyMul (polyAdd (polyMul (cap c) p) (polyNeg d)) h))
      (polyAdd (polyMul (cap c) a) (polyNeg b)) := by
    rw [polyMul_add_left_exact, familyProject_add]
    exact hscale.add hneg
  have hp : RatPolyCoeffEqv
      (familyProject ids (polyMul (polyAdd (polyMul (cap c) p) d) h))
      (polyAdd (polyMul (cap c) a) b) := by
    rw [polyMul_add_left_exact, familyProject_add]
    exact hscale.add (.refl _)
  have hid : RatPolyCoeffEqv
      (polyMul (polyAdd (polyMul (cap c) a) (polyNeg b))
        (polyAdd (polyMul (cap c) a) b))
      (polyAdd (polySmul (c*c) (polyMul a a)) (polyNeg (polyMul b b))) :=
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.add (.mul (.var 0) (.var 1)) (.neg (.var 2)))
        (.add (.mul (.var 0) (.var 1)) (.var 2)))
      (.add (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
        (.neg (.mul (.var 2) (.var 2)))) (by decide)
      (fun | 0 => cap c | 1 => a | _ => b)).trans
      ((((cap_mul c c).mul_right _).trans (cap_mul_left (c*c) _)).add (.refl _))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff ((hm.mul hp).trans hid))
    (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
      (Q'.add_eqv_congr' (quaternionHaar_polySmul _ _ _) (haar_neg _ _)))

private theorem channel_cone_sum (n : Nat) (ids : List Nat) (p d : RatPoly) (c : Q') :
    ∀ cs : List GramChannel,
      channelSum cs (fun h => H n (polyMul
        (familyProject ids (polyMul (polyAdd (polyMul (cap c) p) (polyNeg d)) h))
        (familyProject ids (polyMul (polyAdd (polyMul (cap c) p) d) h)))) ≈
      (c*c) * channelSum cs (fun h => H n (polyMul
        (familyProject ids (polyMul p h)) (familyProject ids (polyMul p h)))) +
      -(channelSum cs (fun h => H n (polyMul
        (familyProject ids (polyMul d h)) (familyProject ids (polyMul d h)))))
  | [] => Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_zero_eqv (c*c)))
      (Q'.eqv_symm (QPoly.q_add_zero_eqv _))
  | h::hs => by
      let A := fun h => H n (polyMul (familyProject ids (polyMul p h)) (familyProject ids (polyMul p h)))
      let B := fun h => H n (polyMul (familyProject ids (polyMul d h)) (familyProject ids (polyMul d h)))
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left h.1 _ _ (projected_cone_pair n ids p d h.2 c))
          (channel_cone_sum n ids p d c hs))
        (poly_identity_of_normal_eq
          (.add (.mul (.var 0) (.add (.mul (.var 1) (.var 2)) (.neg (.var 3))))
            (.add (.mul (.var 1) (.var 4)) (.neg (.var 5))))
          (.add (.mul (.var 1) (.add (.mul (.var 0) (.var 2)) (.var 4)))
            (.neg (.add (.mul (.var 0) (.var 3)) (.var 5)))) (by decide)
          (fun | 0 => h.1 | 1 => c*c | 2 => A h.2 | 3 => B h.2
               | 4 => channelSum hs A | _ => channelSum hs B))

/-- Positive-cone domination gives a bound on the SAME conditional quadratic.
No positivity is required of d or of any individual signed channel. -/
theorem familyChannelQuadratic_le_of_cone (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) (hK : headCutoff w ≤ K)
    (ids : List Nat) (hn : ids.Nodup) (hids : ∀ j, j ∈ ids → j < n)
    (p d : RatPoly) (hp : SupportedQuaternionBlocks n p)
    (hd : SupportedQuaternionBlocks n d) (c : Q')
    (U : Certificate n (polyAdd (polyMul (cap c) p) (polyNeg d)))
    (V : Certificate n (polyAdd (polyMul (cap c) p) d)) :
    familyChannelQuadratic n w K ids d ≤ (c*c) * familyChannelQuadratic n w K ids p := by
  have hc : SupportedQuaternionBlocks n (cap c) := polySmul_supported (supported_one n) c
  have hm : SupportedQuaternionBlocks n (polyNeg d) := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    exact hd s hs
  have h := familyChannelPair_nonnegative n hw0 hw1 K hK ids hn hids _ _
    (supported_add (supported_polyMul hc hp) hm)
    (supported_add (supported_polyMul hc hp) hd) U V
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ h
    (Q'.le_of_eqv (channel_cone_sum n ids p d c _)))

#print axioms familyChannelPair
#print axioms familyChannelPair_self
#print axioms familyChannelPair_eq_conditionalKernel
#print axioms familyChannelPair_nonnegative
#print axioms familyChannelQuadratic_le_of_cone

end YMGap.Continuum.SU2QuaternionFamilyChannelCone
