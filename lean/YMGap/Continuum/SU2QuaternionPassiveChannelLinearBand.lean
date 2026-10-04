/-
# Linear local-band credit for the actual passive channel square

The two positive source bands are compared through one *mixed* moment.  The
upper comparison keeps the original full-heat second moment, while the lower
comparison keeps the partial-swap Gram channel square.  Only the spectator is
independent of active blocks; the full source need not be.  No false equality
between a passive channel square and a passive source moment is used.
-/

import YMGap.Continuum.SU2QuaternionPassiveChannelMomentFactorization
import YMGap.Continuum.SU2QuaternionProductHeatPositiveOrder
import YMGap.Continuum.SU2QuaternionProductHeatInactiveProjection

namespace YMGap.Continuum.SU2QuaternionPassiveChannelLinearBand

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (polynomialProduct_perm)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularSupport (polySmul_supported)
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHeadChainComposition (partialHaarHeads_congr)
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionPartialSliceSwap
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatInactiveProjection
open YMGap.Continuum.SU2QuaternionProductHeatDualForm
open YMGap.Continuum.SU2QuaternionProductHeatPositiveOrder
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy (sourceMoment)
open YMGap.Continuum.SU2QuaternionFamilyChannelCone
open YMGap.Continuum.SU2QuaternionFamilyHeatGramPositiveWeight
open YMGap.Continuum.SU2QuaternionPassiveChannelMomentFactorization
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

private theorem support_neg {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) : SupportedQuaternionBlocks n (polyNeg p) := by
  intro t ht
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ht
  exact hp r hr

private theorem haar_neg (n : Nat) (p : RatPoly) : H n (polyNeg p) ≈ -(H n p) := by
  have h := quaternionHaar_polySmul n (-1) p
  exact Q'.eqv_trans _ _ _
    (haar_of_coeff (YMGap.Continuum.QuaternionHaarAngularCarrier.neg_smul p))
    (Q'.eqv_trans _ _ _ h
      (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
        (by decide) (fun _ => H n p)))

private theorem familyChannelPair_add_right (n : Nat) (w : Q') (K : Nat)
    (ids : List Nat) (hn : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n)
    (a b c : RatPoly) (ha : SupportedQuaternionBlocks n a)
    (hb : SupportedQuaternionBlocks n b) (hc : SupportedQuaternionBlocks n c) :
    familyChannelPair n w K ids a (polyAdd b c) ≈
      familyChannelPair n w K ids a b + familyChannelPair n w K ids a c := by
  let s := swap n ids
  let k := productHeat n w K ids
  have hshape : RatPolyCoeffEqv
      (polyMul k (polyMul a
        (reindexQuaternionPolynomial s (polyAdd b c))))
      (polyAdd (polyMul k (polyMul a (reindexQuaternionPolynomial s b)))
        (polyMul k (polyMul a (reindexQuaternionPolynomial s c)))) := by
    rw [reindexQuaternionPolynomial_add]
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.var 1) (.add (.var 2) (.var 3))))
      (.add (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.mul (.var 0) (.mul (.var 1) (.var 3))))
      (by decide) (fun | 0 => k | 1 => a
                       | 2 => reindexQuaternionPolynomial s b
                       | _ => reindexQuaternionPolynomial s c)
  exact Q'.eqv_trans _ _ _
    (familyChannelPair_eq_conditionalKernel n w K ids hn hids _ _ ha
      (supported_add hb hc))
    (Q'.eqv_trans _ _ _ (haar_of_coeff hshape)
      (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
        (Q'.add_eqv_congr'
          (familyChannelPair_eq_conditionalKernel n w K ids hn hids _ _ ha hb).symm
          (familyChannelPair_eq_conditionalKernel n w K ids hn hids _ _ ha hc).symm)))

private theorem familyChannelPair_smul_right (n : Nat) (w : Q') (K : Nat)
    (ids : List Nat) (hn : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n)
    (a b : RatPoly) (ha : SupportedQuaternionBlocks n a)
    (hb : SupportedQuaternionBlocks n b) (v : Q') :
    familyChannelPair n w K ids a (polySmul v b) ≈
      v * familyChannelPair n w K ids a b := by
  let s := swap n ids
  let k := productHeat n w K ids
  have hshape : RatPolyCoeffEqv
      (polyMul k (polyMul a (reindexQuaternionPolynomial s (polySmul v b))))
      (polySmul v (polyMul k (polyMul a (reindexQuaternionPolynomial s b)))) := by
    rw [reindexQuaternionPolynomial_smul]
    exact ((RatPolyCoeffEqv.polyMul_smul_right v a _).mul_left k).trans
      (RatPolyCoeffEqv.polyMul_smul_right v k _)
  exact Q'.eqv_trans _ _ _
    (familyChannelPair_eq_conditionalKernel n w K ids hn hids _ _ ha
      (polySmul_supported hb v))
    (Q'.eqv_trans _ _ _ (haar_of_coeff hshape)
      (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul _ _ _)
        (Q'.mul_eqv_congr_left _ _ _
          (familyChannelPair_eq_conditionalKernel n w K ids hn hids _ _ ha hb).symm)))

private theorem familyChannelPair_neg_right (n : Nat) (w : Q') (K : Nat)
    (ids : List Nat) (hn : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n)
    (a b : RatPoly) (ha : SupportedQuaternionBlocks n a)
    (hb : SupportedQuaternionBlocks n b) :
    familyChannelPair n w K ids a (polyNeg b) ≈
      -(familyChannelPair n w K ids a b) := by
  let s := swap n ids
  let k := productHeat n w K ids
  have hshape : RatPolyCoeffEqv
      (polyMul k (polyMul a (reindexQuaternionPolynomial s (polyNeg b))))
      (polyNeg (polyMul k (polyMul a (reindexQuaternionPolynomial s b)))) := by
    rw [reindexQuaternionPolynomial_neg]
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.var 1) (.neg (.var 2))))
      (.neg (.mul (.var 0) (.mul (.var 1) (.var 2))))
      (by decide) (fun | 0 => k | 1 => a | _ => reindexQuaternionPolynomial s b)
  exact Q'.eqv_trans _ _ _
    (familyChannelPair_eq_conditionalKernel n w K ids hn hids _ _ ha
      (support_neg hb))
    (Q'.eqv_trans _ _ _ (haar_of_coeff hshape)
      (Q'.eqv_trans _ _ _ (haar_neg _ _)
        (Q'.neg_eqv_congr _ _
          (familyChannelPair_eq_conditionalKernel n w K ids hn hids _ _ ha hb).symm)))

/-- A passive-slice mixed pair with an active-independent spectator is exactly
the original full-heat mixed pairing.  The source in the first leg may depend
on every block. -/
theorem familyChannelPair_spectator_full (n : Nat) (w : Q') (K : Nat)
    (active passive : List Nat) (hpassive : passive.Nodup)
    (hpassive_lt : ∀ i, i ∈ passive → i < n)
    (hcover : (passive++active).Perm (List.range n))
    (a R : RatPoly) (ha : SupportedQuaternionBlocks n a)
    (hR : SupportedQuaternionBlocks n R)
    (hRi : ∀ i, i < n → i ∉ passive → QuaternionBlockIndependent i R) :
    familyChannelPair n w K passive a R ≈
      kineticPair n w K (List.range n) a R := by
  let s := swap n passive
  let k := productHeat n w K passive
  have hswap := reindex_to_lift n passive R hR hRi
  have hkernel : H (n+n) (polyMul k (polyMul a
      (reindexQuaternionPolynomial s R))) ≈
      H (n+n) (polyMul k (polyMul a (liftBoundary n R))) :=
    Q'.eqv_trans _ _ _
      (haar_of_coeff (RatPolyCoeffEqv.mul_assoc k a _).symm)
      (Q'.eqv_trans _ _ _
        (haar_of_carrier (HaarCarrierEqv.mul_left (polyMul k a) hswap))
        (haar_of_coeff (RatPolyCoeffEqv.mul_assoc k a _)))
  have hpair : familyChannelPair n w K passive a R ≈
      kineticPair n w K passive a R :=
    Q'.eqv_trans _ _ _
      (familyChannelPair_eq_conditionalKernel n w K passive hpassive
        hpassive_lt a R ha hR)
      (Q'.eqv_trans _ _ _ hkernel
        (Q'.eqv_trans _ _ _
          (productMap_pairing n w K passive a R).symm
          (kineticPair_symm n w K passive hpassive_lt R a hR ha)))
  have hactive : ∀ i, i ∈ active → i < n := fun i hi =>
    List.mem_range.mp (hcover.mem_iff.mp (List.mem_append_right passive hi))
  have hcover' : (active++passive).Perm (List.range n) :=
    List.perm_append_comm.trans hcover
  have hnd : (active++passive).Nodup :=
    hcover'.symm.nodup (CayleyParentInj.range_nodup n)
  have hall : ∀ i, i ∈ active++passive → i < n := fun i hi =>
    List.mem_range.mp (hcover'.mem_iff.mp hi)
  have hAi : ∀ i, i ∈ active → QuaternionBlockIndependent i R := fun i hi =>
    hRi i (hactive i hi) (fun hip =>
      (List.nodup_append.mp hnd).2.2 i hi i hip rfl)
  have hd := productMap_drop_independent_prefix n w K passive active
    hnd hall R hR hAi
  have hp : RatPolyCoeffEqv (productMap n w K (active++passive) R)
      (productMap n w K (List.range n) R) :=
    partialHaarHeads_congr n ((polynomialProduct_perm _ hcover').mul_right R)
  have hfull : kineticPair n w K passive a R ≈
      kineticPair n w K (List.range n) a R :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm (hd a ha))
      (haar_of_coeff (hp.mul_left a))
  exact Q'.eqv_trans _ _ _ hpair hfull

/-- The local source band pays the full original uncentered moment with only
one upper factor and the conditional channel square with only one lower
factor.  In particular, the full source `q` is never replaced by `R`. -/
theorem channelSquare_sourceMoment_linear_band {n : Nat} {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : headCutoff w ≤ K) (active passive : List Nat)
    (hpassive : passive.Nodup)
    (hpassive_lt : ∀ i, i ∈ passive → i < n)
    (hcover : (passive++active).Perm (List.range n))
    (q R f : RatPoly) (hq : SupportedQuaternionBlocks n q)
    (hR : SupportedQuaternionBlocks n R)
    (hf : SupportedQuaternionBlocks n f)
    (CQ : Certificate n q)
    (l u : Q') (hl : (0 : Q') ≤ l) (hu : (0 : Q') ≤ u)
    (CL : Certificate n (polyAdd q (polyNeg (polySmul l R))))
    (CU : Certificate n (polyAdd (polySmul u R) (polyNeg q)))
    (hRi : ∀ i, i < n → i ∉ passive → QuaternionBlockIndependent i R)
    (hfi : ∀ i, i ∈ passive → QuaternionBlockIndependent i f) :
    l * sourceMoment n w K (List.range n) q (polyMul f f) ≤
      u * channelSquare n w K passive q (polyMul f f) := by
  let e := polyMul f f
  let a := polyMul q e
  let d := polyAdd q (polyNeg (polySmul l R))
  let B := kineticPair n w K (List.range n) a R
  have he := supported_polyMul hf hf
  have ha := supported_polyMul hq he
  have Ca : Certificate n a := CQ.mul (Certificate.square f hf)
  have hd : SupportedQuaternionBlocks n d :=
    supported_add hq (support_neg (polySmul_supported hR l))
  have hei : ∀ i, i ∈ passive → QuaternionBlockIndependent i e := fun i hi =>
    quaternionBlockIndependent_polyMul (hfi i hi) (hfi i hi)
  have hsource : sourceMoment n w K (List.range n) q e ≈
      kineticPair n w K (List.range n) a q := rfl
  have hupper := kineticPair_mono_left n hw0 hw1 K hK (List.range n)
    (fun i hi => List.mem_range.mp hi) CU ha Ca
  have hupper' : sourceMoment n w K (List.range n) q e ≤ u*B :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hsource)
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv (kineticPair_symm n w K (List.range n)
          (fun i hi => List.mem_range.mp hi) a q ha hq))
        (Q'.le_trans' _ _ _ hupper
        (Q'.le_trans' _ _ _
          (Q'.le_of_eqv (kineticPair_smul_left n w K (List.range n) u R a))
          (Q'.le_of_eqv (Q'.mul_eqv_congr_left u _ _
            (kineticPair_symm n w K (List.range n)
              (fun i hi => List.mem_range.mp hi) R a hR ha))))))
  have hpositive : (0 : Q') ≤ familyChannelPair n w K passive a d :=
    familyChannelPair_nonnegative n hw0 hw1 K hK passive hpassive hpassive_lt
      a d ha hd Ca CL
  have hlinear : familyChannelPair n w K passive a d ≈
      familyChannelPair n w K passive a q +
        -(l*familyChannelPair n w K passive a R) :=
    Q'.eqv_trans _ _ _
      (familyChannelPair_add_right n w K passive hpassive hpassive_lt
        a q (polyNeg (polySmul l R)) ha hq
        (support_neg (polySmul_supported hR l)))
      (Q'.add_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _
          (familyChannelPair_neg_right n w K passive hpassive hpassive_lt
            a (polySmul l R) ha (polySmul_supported hR l))
          (Q'.neg_eqv_congr _ _
            (familyChannelPair_smul_right n w K passive hpassive hpassive_lt
              a R ha hR l))))
  have hmix := familyChannelPair_spectator_full n w K active passive
    hpassive hpassive_lt hcover a R ha hR hRi
  have hcross := weighted_cross_pin n w K passive hpassive hpassive_lt
    q e hq he hei
  have hself : familyChannelPair n w K passive a q ≈
      channelSquare n w K passive q e := by
    have hk := familyChannelPair_eq_conditionalKernel n w K passive
      hpassive hpassive_lt a q ha hq
    have hreorder : H (n+n) (polyMul (productHeat n w K passive)
        (polyMul a (reindexQuaternionPolynomial (swap n passive) q))) ≈
        H (n+n) (polyMul (productHeat n w K passive)
          (polyMul (polyMul q (reindexQuaternionPolynomial (swap n passive) q)) e)) :=
      haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.var 0) (.mul (.mul (.var 1) (.var 3)) (.var 2)))
        (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3)))
        (by decide) (fun | 0 => productHeat n w K passive
                         | 1 => q
                         | 2 => reindexQuaternionPolynomial (swap n passive) q
                         | _ => e))
    have hsum : channelSum (productChannels n w K passive) (fun c =>
        H n (polyMul (polyMul (familyProject passive (polyMul q c))
          (familyProject passive (polyMul q c))) e)) ≈
        channelSquare n w K passive q e := by
      unfold channelSquare
      exact Q'.eqv_refl _
    exact Q'.eqv_trans _ _ _ hk
      (Q'.eqv_trans _ _ _ hreorder (Q'.eqv_trans _ _ _ hcross hsum))
  have hlower : l*B ≤ channelSquare n w K passive q e :=
    Q'.le_of_sub_nonneg
      (Q'.le_trans' _ _ _ hpositive
        (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hlinear
          (Q'.add_eqv_congr'
            hself (Q'.neg_eqv_congr _ _
              (Q'.mul_eqv_congr_left l _ _ hmix))))))
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ l hupper' hl
  have hmiddle : l*(u*B) ≈ u*(l*B) :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2)))
      (by decide) (fun | 0 => l | 1 => u | _ => B)
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hmiddle)
      (Q'.mul_le_mul_of_nonneg_left _ _ u hlower hu))

end YMGap.Continuum.SU2QuaternionPassiveChannelLinearBand

#print axioms YMGap.Continuum.SU2QuaternionPassiveChannelLinearBand.familyChannelPair_spectator_full
#print axioms YMGap.Continuum.SU2QuaternionPassiveChannelLinearBand.channelSquare_sourceMoment_linear_band
