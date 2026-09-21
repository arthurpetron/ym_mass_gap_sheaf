/-
# Spatial decay under actual heterogeneous original backgrounds

Face nomes and representation cutoffs may vary independently. A single
explicit small-nome ceiling W controls the relative collar cost and signed
connected coefficients. Existing geometric core counts then give the SAME
distance budget at W, relative to the actual varying-action partition square.

No replacement homogeneous law is used. The guard remains strong-coupling;
this does not construct a scaling trajectory, survival or a continuum gap.
-/
import YMGap.Continuum.BF4ExactSlabHeterogeneousRootedResummation
import YMGap.Continuum.BF4ExactSlabTwoProbeDistanceDecay

namespace YMGap.Continuum.BF4ExactSlabHeterogeneousDistanceDecay

set_option autoImplicit false
open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabHeterogeneousHeatComparison (factor partition)
open YMGap.Continuum.BF4ExactSlabHeterogeneousConnectedExpansion
open YMGap.Continuum.BF4ExactSlabHeterogeneousRootedResummation
open YMGap.Continuum.BF4ExactSlabTwoProbeCoreCount
open YMGap.Continuum.BF4ExactSlabTwoProbeTailBudget (allInside_weight allInside_floor connecting_weight_tail twoProbeBudget)
open YMGap.Continuum.BF4ExactSlabTwoProbeDistanceDecay (distanceBudget minimumCoreSize connecting_core_size_floor)
open YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal (ProbeCarrier)
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabDetachedFaceRegion
open YMGap.Continuum.BF4ExactSlabRelativePartitionBound (removalFloor)
open YMGap.Continuum.BF4ExactSlabConnectedCoefficientBound (pairedHeatRate)
open YMGap.Continuum.BF4ExactSlabMixedAction
open YMGap.Continuum.BF4ExactSlabMixedRelativePartition
open YMGap.Continuum.BF4ExactSlabMixedFiniteBoundaryBudget
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.FiniteWeightedGramSOS (listQSum_mul_right)
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.QuaternionHaarBiadditive (abs_product_bound)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation:max "blocks" extent:max => List.length (boundaryCompleteSlabLinks extent)

private theorem remove_positive_factor {R x b : Q'} (hR : (0 : Q') < R) (h : R*x ≤ b) :
    x ≤ Q'.recipPos R hR*b := by
  let i := Q'.recipPos R hR
  have hi : i*R ≈ 1 := Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv R hR)
  have he : i*(R*x) ≈ x := Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv i R x))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ x hi) (Q'.one_mul_eqv x))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv he)
    (Q'.mul_le_mul_of_nonneg_left _ _ i h (Q'.le_of_lt (Q'.recipPos_pos R hR)))

private theorem abs_sum_bound {A : Type} (f g : A → Q') : ∀ xs : List A,
    (∀ x, x ∈ xs → Q'.abs (f x) ≤ g x) → Q'.abs (listQSum f xs) ≤ listQSum g xs
  | [], _ => by change Q'.abs (0 : Q') ≤ 0; decide
  | x::xs, h => Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _)
    (Q'.add_le_add (h x List.mem_cons_self) (abs_sum_bound f g xs (fun y hy => h y (List.mem_cons_of_mem x hy))))

variable (w : Nat → Q') (K : Nat → Nat) (extent : Nat) {W : Q'}
  (hW0 : (0 : Q') ≤ W) (hW1 : W ≤ (1 : Q'))
  (hw0 : ∀ id, id ∈ slabPhysicalFaceEdges extent → (0 : Q') ≤ w id)
  (hwW : ∀ id, id ∈ slabPhysicalFaceEdges extent → w id ≤ W)
  (hsmall : heatRatio W ≤ HalfPow.half) (hd : heatRemainderBound W < 1)

include hW0 hW1 hw0 hwW hsmall hd

/-- Per-core estimate with the exact heterogeneous spectator and ambient Z^2. -/
theorem resummed_geometric_bound (p q : RatPoly) (c d : Q') (links : List Z4Link)
    (P : Interval (blocks extent) p c) (Q : Interval (blocks extent) q d)
    (ambient anchor : List Nat) (hn : ambient.Nodup)
    (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent)
    (ha : anchor ∈ selections ambient) :
    Q'.abs (connectedCoefficient w K extent p q anchor *
      partitionSquare w K extent (detachedIds extent links anchor ambient)) ≤
      (((c*d+c*d)*probePrefactor W hd links.length)*(adjustedCoreRate W hd)^anchor.length)*
        partitionSquare w K extent ambient := by
  let collar := collarIds extent links anchor ambient
  let detached := detachedIds extent links anchor ambient
  let R := mixedRemovalFloor W (fun _ => true) collar
  let hR := mixedRemovalFloor_pos hd (fun _ => true) collar
  let i := Q'.recipPos R hR
  let M := (c*d+c*d)*(pairedHeatRate W)^anchor.length
  let Z := partitionSquare w K extent ambient
  let z := partitionSquare w K extent detached
  let value := connectedCoefficient w K extent p q anchor * z
  have hM : (0 : Q') ≤ M := BF4ExactSlabResummedCoefficientBound.anchorCap_nonnegative hW0 P.nonnegative Q.nonnegative _
  have hsq : Q'.abs z ≤ z := by
    change Q'.abs (_ * _) ≤ _ * _
    rw [ExpNeg.abs_of_nonneg (SumOfSquares.q_mul_self_nonneg _)]
    exact Q'.le_refl' _
  have hres : Q'.abs value ≤ M*z := abs_product_bound
    (connectedCoefficient_bound w K extent hw0 hwW hW1 hsmall p q c d P Q anchor
      (fun id hi => hphys id (selected_mem ha id hi))) hsq
  have hpart : R*z ≤ Z := by
    have h := BF4ExactSlabHeterogeneousHeatComparison.relative_square_floor
      w K extent hw0 hwW hW1 hsmall (Q'.le_of_lt hd) collar detached
      (fun id hi => hphys id (collar_mem hi)) (fun id hi => hphys id (detached_mem hi))
    have he : partition w K extent (collar++detached) ≈ partition w K extent ambient :=
      haar_of_coeff (polynomialProduct_perm (factor w K extent) (region_partition extent links anchor ambient))
    have he2 : partition w K extent (collar++detached) * partition w K extent (collar++detached) ≈ Z :=
      Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ he) (Q'.mul_eqv_congr_left _ _ _ he)
    change mixedRemovalFloor W (fun _ => true) collar * z ≤ Z
    rw [allInside_floor]
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv he2)
  have hclear : R*Q'.abs value ≤ M*Z :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ R hres (Q'.le_of_lt hR))
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.var 1) (.var 2))) (.mul (.var 1) (.mul (.var 0) (.var 2)))
        (by decide) (fun | 0 => R | 1 => M | _ => z)))
        (Q'.mul_le_mul_of_nonneg_left _ _ M hpart hM))
  have hrel : Q'.abs value ≤ ((c*d+c*d)*normalizedCoreWeight W hd extent links (fun _ => true) ambient anchor)*Z := by
    unfold normalizedCoreWeight
    rw [allInside_weight]
    exact Q'.le_trans' _ _ _ (remove_positive_factor hR hclear) (Q'.le_of_eqv
      (poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3)))
        (.mul (.mul (.var 1) (.mul (.var 2) (.var 0))) (.var 3)) (by decide)
        (fun | 0 => i | 1 => c*d+c*d | 2 => (pairedHeatRate W)^anchor.length | _ => Z)))
  have hc : (0 : Q') ≤ c*d+c*d := Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ P.nonnegative Q.nonnegative)
    (Q'.mul_nonneg _ _ P.nonnegative Q.nonnegative)
  have hg := Q'.mul_le_mul_of_nonneg_right _ _ Z
    (Q'.mul_le_mul_of_nonneg_left _ _ (c*d+c*d)
      (normalizedCoreWeight_geometric_bound hW0 hd extent links (fun _ => true) ambient anchor hn hphys) hc)
    (SumOfSquares.q_mul_self_nonneg _)
  exact Q'.le_trans' _ _ _ hrel (Q'.le_trans' _ _ _ hg (Q'.ge_of_eqv
    (Q'.mul_eqv_congr_right _ _ Z (Q'.mul_assoc_eqv _ _ _))))

theorem connectedNumerator_distance_bound (hs : entropyRate 625 (adjustedCoreRate W hd) < 1)
    (p q : RatPoly) (c d : Q') (Ip : Interval (blocks extent) p c) (Iq : Interval (blocks extent) q d)
    (left right : List Z4Link) (P : ProbeCarrier left) (Q : ProbeCarrier right)
    (hl : LinkLocal extent left p) (hr : LinkLocal extent right q)
    (ambient : List Nat) (hn : ambient.Nodup)
    (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent) :
    Q'.abs (connectedNumerator w K extent ambient p q) ≤
      distanceBudget P Q W hd hs c d * partitionSquare w K extent ambient := by
  let r := adjustedCoreRate W hd
  let A := (c*d+c*d)*probePrefactor W hd (left++right).length
  let Z := partitionSquare w K extent ambient
  let anchors := connectingAnchors extent left right ambient
  have hsum : Q'.abs (listQSum (fun ids => connectedCoefficient w K extent p q ids *
      partitionSquare w K extent (detachedIds extent (left++right) ids ambient)) anchors) ≤
      listQSum (fun ids => (A*r^ids.length)*Z) anchors := by
    apply abs_sum_bound
    intro ids hi
    exact resummed_geometric_bound w K extent hW0 hW1 hw0 hwW hsmall hd p q c d (left++right) Ip Iq
      ambient ids hn hphys (connecting_selected hi)
  have hfactor : listQSum (fun ids => (A*r^ids.length)*Z) anchors ≈
      (A*listQSum (fun ids => r^ids.length) anchors)*Z :=
    Q'.eqv_trans _ _ _ (listQSum_mul_right _ Z anchors)
      (Q'.mul_eqv_congr_right _ _ Z (listQSum_mul_left A _ anchors))
  have ha : (0 : Q') ≤ A := Q'.mul_nonneg _ _
    (Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ Ip.nonnegative Iq.nonnegative)
      (Q'.mul_nonneg _ _ Ip.nonnegative Iq.nonnegative)) (probePrefactor_nonnegative W hd _)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr
    (connectedNumerator_connecting_expansion w K extent p q left right Ip.support Iq.support hl hr ambient hn)))
    (Q'.le_trans' _ _ _ hsum (Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor)
      (Q'.mul_le_mul_of_nonneg_right _ _ Z (Q'.mul_le_mul_of_nonneg_left _ _ A
        (connecting_weight_tail (adjustedCoreRate_nonnegative hW0 hd) hs P Q extent ambient (minimumCoreSize P Q)
          hn hphys (connecting_core_size_floor P Q extent ambient hn hphys)) ha)
        (SumOfSquares.q_mul_self_nonneg _))))

end YMGap.Continuum.BF4ExactSlabHeterogeneousDistanceDecay

#print axioms YMGap.Continuum.BF4ExactSlabHeterogeneousDistanceDecay.resummed_geometric_bound
#print axioms YMGap.Continuum.BF4ExactSlabHeterogeneousDistanceDecay.connectedNumerator_distance_bound
