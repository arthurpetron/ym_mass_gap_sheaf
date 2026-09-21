/-
# Centered plaquette coercivity under the SAME arbitrary selected action

Subtracting any rational constant leaves retained-background coefficient
detection unchanged. The existing finite duals and their bounded-interference
norm therefore control the shifted source square with the same constants.
Choosing the actual interacting mean gives a variance floor for every signed
fundamental-plaquette span under any duplicate-free physical action list.

This includes selected finite chains, unlike the full-cube Ward specialization.
The constants depend on nome; no completed OS or scaling identification follows
without the literal chart and limiting pins.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteAffinePairing
import YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryDualFamily

namespace YMGap.Continuum.BF4ExactSlabPlaquetteAffineCoercivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabSelectedStarVariance
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation (finiteValue)
open YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryErasure
open YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryWindow
open YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryDual
open YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryDualPairing
open YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryDualFamily
open YMGap.Continuum.BF4ExactSlabPlaquetteAffinePairing
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
private abbrev blocks (extent : Nat) := (boundaryCompleteSlabLinks extent).length

def affineSource (extent : Nat) (c : Z4Plaq → Q') (qs : List Z4Plaq) (m : Q') : RatPoly :=
  shifted (sourceSpan extent c qs) m

theorem affineSource_supported (extent : Nat) (c : Z4Plaq → Q') (qs : List Z4Plaq) (m : Q') :
    SupportedQuaternionBlocks (blocks extent) (affineSource extent c qs m) :=
  shifted_supported (sourceSpan_supported extent c qs) m

def affineEnergy (w : Q') (K extent : Nat) (ids : List Nat)
    (c : Z4Plaq → Q') (qs : List Z4Plaq) (m : Q') : Q' :=
  quaternionHaar (blocks extent) (polyMul (polynomialProduct (faceHeatPolynomial w K extent) ids)
    (polyMul (affineSource extent c qs m) (affineSource extent c qs m)))

def affineError {w : Q'} (hw0 : (0 : Q') < w) (K extent : Nat) (ids : List Nat)
    (k : Nat) (c : Z4Plaq → Q') (qs : List Z4Plaq) (m : Q') : Q' :=
  listQSum (fun p => c p * quaternionHaar (blocks extent)
    (polyMul (restHeat w K extent ids p) (polyMul (faceCharacter extent p)
      (polyMul (residualPolynomial hw0 K extent ids p k) (affineSource extent c qs m))))) qs

private theorem qmul {a b c d : Q'} (h : a ≈ b) (j : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ j)

theorem affineEnergy_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (c : Z4Plaq → Q') (qs : List Z4Plaq) (m : Q') :
    (0 : Q') ≤ affineEnergy w K extent ids c qs m :=
  ((headProduct_certificate hw0 hw1 K extent hK ids hids).mul
    (.square _ (affineSource_supported extent c qs m))).haar_nonnegative

/-- Every rational center leaves the detected coefficient budget unchanged. -/
theorem affine_family_pairing {w : Q'} (hw0 : (0 : Q') < w) (K extent : Nat) (ids : List Nat)
    (qs : List Z4Plaq) (hn : qs.Nodup)
    (hqs : ∀ p, p ∈ qs → p ∈ boundaryCompleteSlabPlaquettes extent) (c : Z4Plaq → Q')
    (m : Q') (k : Nat) :
    quaternionHaar (blocks extent) (polyMul (polynomialProduct (faceHeatPolynomial w K extent) ids)
      (polyMul (dualFamily hw0 K extent ids k c qs) (affineSource extent c qs m))) +
      affineError hw0 K extent ids k c qs m ≈ familyBudget w K extent ids c qs := by
  let A := polynomialProduct (faceHeatPolynomial w K extent) ids
  let F := affineSource extent c qs m
  let d := fun p => dualTest hw0 K extent ids p k
  let e := fun p => quaternionHaar (blocks extent) (polyMul (restHeat w K extent ids p)
    (polyMul (faceCharacter extent p) (polyMul (residualPolynomial hw0 K extent ids p k) F)))
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
    (pair_sum_left (blocks extent) A c d F qs) (Q'.eqv_refl _)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (listQSum_add
    (fun p => c p*quaternionHaar (blocks extent) (polyMul A (polyMul (d p) F))) (fun p => c p*e p) qs)) ?_
  apply listQSum_congr_on _ _ qs
  intro p hp
  have hs := fullAction_shifted_pairing hw0 K extent ids (hqs p hp) k (qs.map (fun q => (c q,q))) m
  have hc := Q'.eqv_trans _ _ _ hs (qmul (coefficientAt_map p c qs hn hp) (Q'.eqv_refl _))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_add_eqv (c p) _ _))
    (Q'.eqv_trans _ _ _ (qmul (Q'.eqv_refl _) hc) (Q'.eqv_symm (Q'.mul_assoc_eqv (c p) (c p) _)))

theorem affine_family_error_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) (hnodup : ids.Nodup)
    (qs : List Z4Plaq) (hqs : ∀ p, p ∈ qs → p ∈ boundaryCompleteSlabPlaquettes extent)
    (c : Z4Plaq → Q') (m : Q') (k : Nat) :
    2*lower w*affineError hw0 K extent ids k c qs m ≤
      (rate hw0)^k * (lower w*familyBudget w K extent ids c qs +
        Q'.ofNat qs.length*affineEnergy w K extent ids c qs m) := by
  let L := lower w
  let r := (rate hw0)^k
  let E := affineEnergy w K extent ids c qs m
  let b := fun p => c p*c p*quaternionHaar (blocks extent) (restHeat w K extent ids p)
  let e := fun p => quaternionHaar (blocks extent) (polyMul (restHeat w K extent ids p)
    (polyMul (faceCharacter extent p)
      (polyMul (residualPolynomial hw0 K extent ids p k) (affineSource extent c qs m))))
  have hpoint : ∀ p, p ∈ qs → 2*L*(c p*e p) ≤ r*(L*b p+E) := by
    intro p hp
    exact error_young (c p) (Q'.le_of_lt (lower_positive hw0 hw1))
      (Q'.pow_nonneg _ (rate_nonnegative hw0 hw1) k)
      (headProduct_certificate hw0 hw1 K extent hK (boundaryRest extent ids p)
        (fun id hi => hids id (boundaryRest_mem hi).1)).haar_nonnegative
      (affineEnergy_nonnegative hw0 hw1 K extent hK ids hids c qs m)
      (fullAction_pairing_error hw0 hw1 K extent hK ids hids hnodup (hqs p hp) k
        (affineSource extent c qs m) (affineSource_supported extent c qs m))
  have hs := Z4FiniteCylinderQuadraticStability.listQSum_mono _ _ qs hpoint
  have hrhs : listQSum (fun p => r*(L*b p+E)) qs ≈
      r*(L*familyBudget w K extent ids c qs + Q'.ofNat qs.length*E) :=
    Q'.eqv_trans _ _ _ (listQSum_mul_left r _ qs)
      (qmul (Q'.eqv_refl _) (Q'.eqv_trans _ _ _ (listQSum_add _ _ qs)
        (Q'.add_eqv_congr' (listQSum_mul_left L b qs)
          (Q'.eqv_trans _ _ _ (RationalFiniteSparseGram.listQSum_const E qs) (Q'.mul_comm_eqv E _)))))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (listQSum_mul_left (2*L) (fun p => c p*e p) qs))
    (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv hrhs))

/-- The same finite dual norm bound applies to the shifted source. Its
residual vanishes by the existing explicit geometric modulus. -/
theorem affine_family_coercivity {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) (hnodup : ids.Nodup)
    (qs : List Z4Plaq) (hn : qs.Nodup)
    (hqs : ∀ p, p ∈ qs → p ∈ boundaryCompleteSlabPlaquettes extent) (c : Z4Plaq → Q') (m : Q') :
    lower w * familyBudget w K extent ids c qs ≤ 600 * affineEnergy w K extent ids c qs m := by
  let A := polynomialProduct (faceHeatPolynomial w K extent) ids
  let D := QuaternionHaarWeightedCauchySchwarz.weightedGNSData (blocks extent) A
    (headProduct_certificate hw0 hw1 K extent hK ids hids)
  let F : D.V := ⟨affineSource extent c qs m, affineSource_supported extent c qs m⟩
  let tests : Nat → D.V := fun k => ⟨dualFamily hw0 K extent ids k c qs, dualFamily_supported hw0 K extent ids k c qs⟩
  have pin (f g : D.V) : D.B f g ≈ quaternionHaar (blocks extent) (polyMul A (polyMul f.val g.val)) :=
    haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)
  have hnorm (k : Nat) : lower w*D.B (tests k) (tests k) ≤
      (600+(rate hw0)^k*Q'.ofNat qs.length)*familyBudget w K extent ids c qs :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (qmul (Q'.eqv_refl _) (pin (tests k) (tests k))))
      (family_norm_bound hw0 hw1 K extent hK ids hids hnodup qs hn hqs c k)
  have hpair (k : Nat) : D.B (tests k) F + affineError hw0 K extent ids k c qs m ≈ familyBudget w K extent ids c qs :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (pin (tests k) F) (Q'.eqv_refl _))
      (affine_family_pairing hw0 K extent ids qs hn hqs c m k)
  have herror (k : Nat) : 2*lower w*affineError hw0 K extent ids k c qs m ≤
      (rate hw0)^k*(lower w*familyBudget w K extent ids c qs+Q'.ofNat qs.length*D.B F F) :=
    Q'.le_trans' _ _ _ (affine_family_error_bound hw0 hw1 K extent hK ids hids hnodup qs hqs c m k)
      (Q'.ge_of_eqv (qmul (Q'.eqv_refl _) (Q'.add_eqv_congr' (Q'.eqv_refl _) (qmul (Q'.eqv_refl _) (pin F F)))))
  have h := GNSFiniteDualCoercivity.coercivity_of_finite_tests D F tests
    (fun k => affineError hw0 K extent ids k c qs m) (familyBudget w K extent ids c qs)
    (lower w) 600 (Q'.ofNat qs.length) (rate hw0)
    (familyBudget_nonnegative hw0 hw1 K extent hK ids hids c qs)
    (Q'.le_of_lt (lower_positive hw0 hw1)) (by decide)
    (CReal.ofNat_le_ofNat (Nat.zero_le qs.length))
    (rate_nonnegative hw0 hw1) (rate_lt_one hw0 hw1) hnorm hpair herror
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (qmul (Q'.eqv_refl _) (pin F F)))

/-- One bound for every rational center under the actual selected action. -/
theorem affine_partition_coercivity {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) (hnodup : ids.Nodup)
    (qs : List Z4Plaq) (hn : qs.Nodup)
    (hqs : ∀ p, p ∈ qs → p ∈ boundaryCompleteSlabPlaquettes extent) (c : Z4Plaq → Q') (m : Q') :
    lower w * quaternionHaar (blocks extent) (polynomialProduct (faceHeatPolynomial w K extent) ids) *
      listQSum (fun p => c p*c p) qs ≤ (600*upper w)*affineEnergy w K extent ids c qs m := by
  have h1 := Q'.mul_le_mul_of_nonneg_left _ _ (lower w)
    (partition_coefficient_budget hw0 hw1 K extent hK ids hids hnodup qs c) (Q'.le_of_lt (lower_positive hw0 hw1))
  have he : lower w*(upper w*familyBudget w K extent ids c qs) ≈ upper w*(lower w*familyBudget w K extent ids c qs) :=
    poly_identity_of_normal_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => lower w | 1 => upper w | _ => familyBudget w K extent ids c qs)
  have h2 := Q'.mul_le_mul_of_nonneg_left _ _ (upper w)
    (affine_family_coercivity hw0 hw1 K extent hK ids hids hnodup qs hn hqs c m) (Q'.le_of_lt (upper_positive hw0))
  have hf : upper w*(600*affineEnergy w K extent ids c qs m) ≈ (600*upper w)*affineEnergy w K extent ids c qs m :=
    poly_identity_of_normal_eq (.mul (.var 0) (.mul (.const 600) (.var 1)))
      (.mul (.mul (.const 600) (.var 0)) (.var 1)) (by decide)
      (fun | 0 => upper w | _ => affineEnergy w K extent ids c qs m)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _))
    (Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ (Q'.le_of_eqv he) (Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv hf))))

/-- Actual interacting centering, with the SAME original partition cancelled
before any volume-dependent lower bound can enter the constant. -/
theorem normalized_variance_coercivity {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) (hnodup : ids.Nodup)
    (qs : List Z4Plaq) (hn : qs.Nodup)
    (hqs : ∀ p, p ∈ qs → p ∈ boundaryCompleteSlabPlaquettes extent) (c : Z4Plaq → Q') :
    lower w * listQSum (fun p => c p*c p) qs ≤
      (600*upper w) * normalizedVariance (blocks extent)
        (polynomialProduct (faceHeatPolynomial w K extent) ids) (sourceSpan extent c qs)
        (selectedMass_positive hw0 hw1 K extent hK ids hids) := by
  let A := polynomialProduct (faceHeatPolynomial w K extent) ids
  let Z := quaternionHaar (blocks extent) A
  let hZ := selectedMass_positive hw0 hw1 K extent hK ids hids
  let r := Q'.recipPos Z hZ
  let F := sourceSpan extent c qs
  let m := normalizedMoment (blocks extent) A F hZ
  let B := listQSum (fun p => c p*c p) qs
  have hp : ((lower w*Z)*B)*r ≈ lower w*B :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 3))
      (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
      (by decide) (fun | 0 => lower w | 1 => Z | 2 => B | _ => r))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_recipPos_eqv Z hZ)) (Q'.mul_one_eqv _))
  have hraw := Q'.mul_le_mul_of_nonneg_right _ _ r
    (affine_partition_coercivity hw0 hw1 K extent hK ids hids hnodup qs hn hqs c m)
    (Q'.le_of_lt (Q'.recipPos_pos Z hZ))
  have hmean := own_mean_pin (headProduct_certificate hw0 hw1 K extent hK ids hids)
    (sourceSpan_supported extent c qs) hZ
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hp)
    (Q'.le_trans' _ _ _ hraw (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.mul_eqv_congr_left _ _ _ hmean))))

/-- The constructive positive denominator depends on nome only. -/
theorem varianceDenominator_positive {w : Q'} (hw0 : (0 : Q') < w) :
    (0 : Q') < 600*upper w := Q'.mul_pos (by decide) (upper_positive hw0)

def varianceFloor (w : Q') (hw0 : (0 : Q') < w) : Q' :=
  lower w * Q'.recipPos (600*upper w) (varianceDenominator_positive hw0)

theorem varianceFloor_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    (0 : Q') < varianceFloor w hw0 :=
  Q'.mul_pos (lower_positive hw0 hw1) (Q'.recipPos_pos _ (varianceDenominator_positive hw0))

/-- Uniform in physical selected list, extent, signed family and late cutoff
at each fixed strict nome; every coefficient remains inside the actual F. -/
theorem normalized_variance_floor {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) (hnodup : ids.Nodup)
    (qs : List Z4Plaq) (hn : qs.Nodup)
    (hqs : ∀ p, p ∈ qs → p ∈ boundaryCompleteSlabPlaquettes extent) (c : Z4Plaq → Q') :
    varianceFloor w hw0 * listQSum (fun p => c p*c p) qs ≤
      normalizedVariance (blocks extent) (polynomialProduct (faceHeatPolynomial w K extent) ids)
        (sourceSpan extent c qs) (selectedMass_positive hw0 hw1 K extent hK ids hids) := by
  let d := 600*upper w
  let r := Q'.recipPos d (varianceDenominator_positive hw0)
  let B := listQSum (fun p => c p*c p) qs
  have hp : d*((lower w*r)*B) ≈ lower w*B :=
    Q'.eqv_trans _ ((d*r)*(lower w*B)) _
      (poly_identity_of_normal_eq (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3)))
        (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))) (by decide)
        (fun | 0 => d | 1 => lower w | 2 => r | _ => B))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_recipPos_eqv d (varianceDenominator_positive hw0))) (Q'.one_mul_eqv _))
  exact Q'.le_of_mul_le_mul_left
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hp)
      (normalized_variance_coercivity hw0 hw1 K extent hK ids hids hnodup qs hn hqs c))
    (varianceDenominator_positive hw0)

/-- Literal finiteValue moments, at the SAME original action and cutoff.
This is the finite input needed by the existing selected-chain chart limits. -/
theorem finiteValue_variance_floor {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) (hnodup : ids.Nodup)
    (qs : List Z4Plaq) (hn : qs.Nodup)
    (hqs : ∀ p, p ∈ qs → p ∈ boundaryCompleteSlabPlaquettes extent) (c : Z4Plaq → Q') (stage : Nat) :
    varianceFloor w hw0 * listQSum (fun p => c p*c p) qs ≤
      finiteValue w hw0 hw1 extent ids hids (polyMul (sourceSpan extent c qs) (sourceSpan extent c qs)) stage +
      -(finiteValue w hw0 hw1 extent ids hids (sourceSpan extent c qs) stage *
        finiteValue w hw0 hw1 extent ids hids (sourceSpan extent c qs) stage) := by
  have hm := normalizedMoment_finiteValue hw0 hw1 extent ids hids (sourceSpan extent c qs) stage
  have hs := normalizedMoment_finiteValue hw0 hw1 extent ids hids
    (polyMul (sourceSpan extent c qs) (sourceSpan extent c qs)) stage
  exact Q'.le_trans' _ _ _
    (normalized_variance_floor hw0 hw1 (headCutoff w+stage) extent (Nat.le_add_right _ _) ids hids hnodup qs hn hqs c)
    (Q'.le_of_eqv (Q'.add_eqv_congr' hs (Q'.neg_eqv_congr _ _ (qmul hm hm))))

end YMGap.Continuum.BF4ExactSlabPlaquetteAffineCoercivity

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteAffineCoercivity.affineSource_supported
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteAffineCoercivity.affineEnergy_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteAffineCoercivity.affine_family_pairing
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteAffineCoercivity.affine_family_error_bound
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteAffineCoercivity.affine_family_coercivity
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteAffineCoercivity.affine_partition_coercivity
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteAffineCoercivity.normalized_variance_coercivity
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteAffineCoercivity.varianceDenominator_positive
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteAffineCoercivity.varianceFloor_positive
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteAffineCoercivity.normalized_variance_floor
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteAffineCoercivity.finiteValue_variance_floor
