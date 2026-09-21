/-
# Global six-direction Ward energy on the complete physical-link family

Every physical plaquette is counted exactly four times. The local positive
energy floor therefore sums without a volume loss. The upper bound sums the
six already-constructed direction costs and retains the SAME whole signed
observable, full action, actual variance and common partition.
Eliminating the common coefficient budget gives an explicit positive rational
floor for that centered variance, at every extent and late cutoff.

These are original-measure Ward estimates, not OS transfer energy estimates.
Nome dependence remains explicit; no continuum uniformity is asserted.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteAngularCoercivity
import YMGap.Continuum.BF4ExactSlabWardIncidenceCover
import YMGap.Continuum.BF4ExactSlabPlaquetteGradientCost
import YMGap.Continuum.RationalWardResponseCoercivity

namespace YMGap.Continuum.BF4ExactSlabPlaquetteAngularFamily

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabWardFamilyCost
open YMGap.Continuum.BF4ExactSlabWardGradientEnergy
open YMGap.Continuum.BF4ExactSlabPlaquetteWardEnergy
open YMGap.Continuum.BF4ExactSlabPlaquetteGradient
open YMGap.Continuum.BF4ExactSlabPlaquetteGradientCost
open YMGap.Continuum.BF4ExactSlabPlaquetteAngularCoercivity
open YMGap.Continuum.BF4ExactSlabWardIncidenceCover
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabLocalWardScoreBound
open YMGap.Continuum.AngularProductBudget
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.QuaternionHaarIntervalSecondMoment
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
private abbrev blocks (extent : Nat) : Nat := (boundaryCompleteSlabLinks extent).length

private theorem listQSum_le_termwise {A : Type} (left right : A → Q') :
    ∀ xs : List A, (∀ x, x ∈ xs → left x ≤ right x) →
      listQSum left xs ≤ listQSum right xs
  | [], _ => Q'.le_refl' 0
  | x :: xs, h => Q'.add_le_add (h x List.mem_cons_self)
      (listQSum_le_termwise left right xs (fun y hy => h y (List.mem_cons_of_mem x hy)))

private theorem listQSum_sixValue {Index : Type} (f : Index → Nat → Nat → Q') (xs : List Index) :
    listQSum (fun l => sixValue (f l)) xs ≈ sixValue (fun i j => listQSum (fun l => f l i j) xs) := by
  have h (a b : Index → Q') (v : Q') (hb : listQSum b xs ≈ v) :
      listQSum (fun l => a l+b l) xs ≈ listQSum a xs+v :=
    Q'.eqv_trans _ _ _ (listQSum_add a b xs) (Q'.add_eqv_congr' (Q'.eqv_refl _) hb)
  exact h _ _ _ (h _ _ _ (h _ _ _ (h _ _ _ (listQSum_add (fun l => f l 1 3) (fun l => f l 2 3) xs))))

private theorem listSix_pin (f : Nat → Nat → Q') (g : Q' → Q') :
    listQSum g [f 0 1, f 0 2, f 0 3, f 1 2, f 1 3, f 2 3] ≈
      sixValue (fun i j => g (f i j)) :=
  Q'.add_eqv_congr' (Q'.eqv_refl _)
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.eqv_of_eq (Q'.add_zero' _))))))

private theorem six_square_le (f : Nat → Nat → Q') :
    sixValue f * sixValue f ≤ 6 * sixValue (fun i j => f i j*f i j) := by
  have h := BF4PhysicalFiniteVacuumSectorPathLengthEnergy.listQSum_square_le_length_mul_squareSum
    [f 0 1, f 0 2, f 0 3, f 1 2, f 1 3, f 2 3]
  have hs := listSix_pin f (fun x => x)
  have hsq := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hs)
    (Q'.mul_eqv_congr_left _ _ _ hs)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hsq)
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.mul_eqv_congr_left 6 _ _ (listSix_pin f (fun x => x*x)))))

private theorem six_const (c : Q') : sixValue (fun _ _ => c) ≈ 6*c :=
  poly_identity_of_normal_eq
    (.add (.var 0) (.add (.var 0) (.add (.var 0) (.add (.var 0) (.add (.var 0) (.var 0))))))
    (.mul (.const 6) (.var 0)) (by decide) (fun _ => c)

/-- The factor 36 is six-direction Cauchy--Schwarz plus six identical bounds;
the previous 600 is the 25-star, six-face, four-edge cost. -/
def responseCostCoefficient (w : Q') : Q' := 21600*(scoreCoefficient w*scoreCoefficient w)

theorem responseCostCoefficient_positive {w : Q'} (hw0 : (0 : Q') < w) :
    (0 : Q') < responseCostCoefficient w := by
  have hv : (0 : Q') < incidentValueCap w :=
    HeatKernelRGStep.lt_of_lt_of_le (by decide : (0 : Q') < 1)
      (value_le (one_le_faceValueCap hw0) (Nat.zero_le 6))
  have hd : (0 : Q') ≤ incidentDerivativeCap w :=
    derivativeBudget_nonnegative (one_le_faceValueCap hw0) (faceAngularCap_nonnegative hw0) 6
  have hc : (0 : Q') < scoreCoefficient w :=
    Q'.pos_add_nonneg (Q'.mul_pos hv (by decide))
      (Q'.mul_nonneg _ _ (by decide) (Q'.mul_nonneg _ _ hd (by decide)))
  exact Q'.mul_pos (by decide) (Q'.mul_pos hc hc)

/-- Positive, extent- and cutoff-independent variance comparison denominator. -/
def varianceCost (w : Q') : Q' :=
  (costCoefficient w*costCoefficient w)*responseCostCoefficient w

theorem varianceCost_positive {w : Q'} (hw0 : (0 : Q') < w) :
    (0 : Q') < varianceCost w :=
  Q'.mul_pos (Q'.mul_pos (costCoefficient_positive hw0) (costCoefficient_positive hw0))
    (responseCostCoefficient_positive hw0)

/-- Explicit positive floor, with dependence on the nome retained as data. -/
def varianceFloor (w : Q') (hw0 : (0 : Q') < w) : Q' :=
  ((4*floorCoefficient w)*(4*floorCoefficient w))*
    Q'.recipPos (varianceCost w) (varianceCost_positive hw0)

theorem varianceFloor_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    (0 : Q') < varianceFloor w hw0 :=
  Q'.mul_pos
    (Q'.mul_pos (Q'.mul_pos (by decide) (floorCoefficient_positive hw0 hw1))
      (Q'.mul_pos (by decide) (floorCoefficient_positive hw0 hw1)))
    (Q'.recipPos_pos _ (varianceCost_positive hw0))

variable (w : Q') (K extent : Nat)
local notation "W" => polynomialProduct (faceHeatPolynomial w K extent) (slabPhysicalFaceEdges extent)

/-- Six directions and all physical links, in the ORIGINAL common partition. -/
def totalEnergy (c : Nat → Q') (hW : (0 : Q') < quaternionHaar (blocks extent) W) : Q' :=
  sixValue (fun i j => energySum w K extent i j c (allPhysicalLinks extent) hW)

theorem totalEnergy_nonnegative (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hK : headCutoff w ≤ K) (c : Nat → Q') (hW : (0 : Q') < quaternionHaar (blocks extent) W) :
    (0 : Q') ≤ totalEnergy w K extent c hW := by
  have h := sixValue_mono (fun _ _ => 0)
    (fun i j => energySum w K extent i j c (allPhysicalLinks extent) hW)
    (fun _ _ hi hj => energySum_nonnegative w K extent hw0 hw1 hK hi hj c _ hW)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (by decide : sixValue (fun _ _ => (0 : Q')) ≈ 0)) h

/-- Exact fourfold coverage supplies the lower estimate on the whole family.
Neither its size nor the extent appears in the positive coefficient. -/
theorem totalEnergy_coercivity (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hK : headCutoff w ≤ K) (c : Nat → Q') :
    let hW := fullPartition_positive w K extent hw0 hw1 hK
    (4*floorCoefficient w)*coefficientSquares extent c ≤
      costCoefficient w * totalEnergy w K extent c hW := by
  let hW := fullPartition_positive w K extent hw0 hw1 hK
  let C : PhysicalLink extent → Q' := fun l => listQSum (fun id => c id*c id) (incidentIds extent l.val)
  let e : PhysicalLink extent → Nat → Nat → Q' := fun l i j =>
    linkEnergy w K extent l.val l.property i j (observable extent c) hW
  have ht := listQSum_le_termwise (fun l => floorCoefficient w*C l)
    (fun l => costCoefficient w*sixValue (e l)) (allPhysicalLinks extent)
    (fun l _ => incident_normalized_energy_coercivity w K extent l.val l.property hw0 hw1 hK c)
  have hlhs : listQSum (fun l => floorCoefficient w*C l) (allPhysicalLinks extent) ≈
      (4*floorCoefficient w)*coefficientSquares extent c :=
    Q'.eqv_trans _ _ _ (listQSum_mul_left _ C _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (coefficient_square_incidence_eq_four extent c))
        (poly_identity_of_normal_eq (.mul (.var 0) (.mul (.const 4) (.var 1)))
          (.mul (.mul (.const 4) (.var 0)) (.var 1)) (by decide)
          (fun n => if n = 0 then floorCoefficient w else coefficientSquares extent c)))
  have hrhs : listQSum (fun l => costCoefficient w*sixValue (e l)) (allPhysicalLinks extent) ≈
      costCoefficient w * totalEnergy w K extent c hW :=
    Q'.eqv_trans _ _ _ (listQSum_mul_left _ _ _)
      (Q'.mul_eqv_congr_left _ _ _ (listQSum_sixValue e _))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hlhs) (Q'.le_trans' _ _ _ ht (Q'.le_of_eqv hrhs))

/-- The same actual energy is bounded by the actual centered variance and
coefficient budget. No energy or variance is introduced as a supplied field. -/
theorem totalEnergy_squared_le (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hK : headCutoff w ≤ K) (c : Nat → Q') :
    let hW := fullPartition_positive w K extent hw0 hw1 hK
    let E := totalEnergy w K extent c hW
    E*E ≤ normalizedVariance (blocks extent) W (observable extent c) hW *
      (responseCostCoefficient w*coefficientSquares extent c) := by
  let hW := fullPartition_positive w K extent hw0 hw1 hK
  let e := fun i j => energySum w K extent i j c (allPhysicalLinks extent) hW
  let V := normalizedVariance (blocks extent) W (observable extent c) hW
  let B := coefficientSquares extent c
  let C := scoreCoefficient w
  let b := V*(Q'.ofNat 25*((24*(C*C))*B))
  have hb := sixValue_mono (fun i j => e i j*e i j) (fun _ _ => b)
    (fun _ _ hi hj => energy_squared_le_explicit_cost extent w K hw0 hw1 hK hi hj c _ (allPhysicalLinks_nodup extent))
  have he : 6*(6*b) ≈ V*(responseCostCoefficient w*B) :=
    poly_identity_of_normal_eq
      (.mul (.const 6) (.mul (.const 6) (.mul (.var 0)
        (.mul (.const 25) (.mul (.mul (.const 24) (.mul (.var 1) (.var 1))) (.var 2))))))
      (.mul (.var 0) (.mul (.mul (.const 21600) (.mul (.var 1) (.var 1))) (.var 2)))
      (by decide) (fun | 0 => V | 1 => C | _ => B)
  exact Q'.le_trans' _ _ _ (six_square_le e)
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ 6 hb (by decide))
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_eqv_congr_left 6 _ _ (six_const b))) (Q'.le_of_eqv he)))

/-- Coercivity of the ACTUAL centered variance of every signed fundamental-
plaquette sum. Both coefficients depend only on the fixed strict nome; the
same formula holds at every extent and every cutoff above `headCutoff w`.
This is ordinary original-action variance, not an OS quotient norm. -/
theorem variance_coercivity (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hK : headCutoff w ≤ K) (c : Nat → Q') :
    let hW := fullPartition_positive w K extent hw0 hw1 hK
    ((4*floorCoefficient w)*(4*floorCoefficient w))*coefficientSquares extent c ≤
      ((costCoefficient w*costCoefficient w)*responseCostCoefficient w)*
        normalizedVariance (blocks extent) W (observable extent c) hW := by
  let hW := fullPartition_positive w K extent hw0 hw1 hK
  exact RationalWardResponseCoercivity.response_coercivity
    (4*floorCoefficient w) (costCoefficient w) (responseCostCoefficient w)
    (coefficientSquares extent c)
    (normalizedVariance (blocks extent) W (observable extent c) hW)
    (totalEnergy w K extent c hW)
    (Q'.mul_nonneg _ _ (by decide) (Q'.le_of_lt (floorCoefficient_positive hw0 hw1)))
    (Q'.le_of_lt (costCoefficient_positive hw0))
    (Q'.mul_nonneg _ _ (by decide) (SumOfSquares.q_mul_self_nonneg _))
    (listQSum_nonnegative_on _ _ (fun _ _ => SumOfSquares.q_mul_self_nonneg _))
    (normalizedVariance_nonnegative
      (headProduct_certificate hw0 hw1 K extent hK (slabPhysicalFaceEdges extent) (fun _ h => h))
      hW (observable_supported extent c))
    (totalEnergy_nonnegative w K extent hw0 hw1 hK c hW)
    (totalEnergy_coercivity w K extent hw0 hw1 hK c)
    (totalEnergy_squared_le w K extent hw0 hw1 hK c)

/-- The positive rational witness supplies a literal variance floor for the
whole signed observable, in the original measure and normalization. -/
theorem variance_floor (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hK : headCutoff w ≤ K) (c : Nat → Q') :
    let hW := fullPartition_positive w K extent hw0 hw1 hK
    varianceFloor w hw0 * coefficientSquares extent c ≤
      normalizedVariance (blocks extent) W (observable extent c) hW := by
  let a := (4*floorCoefficient w)*(4*floorCoefficient w)
  let b := coefficientSquares extent c
  let d := varianceCost w
  let r := Q'.recipPos d (varianceCost_positive hw0)
  have hp : d*((a*r)*b) ≈ a*b :=
    Q'.eqv_trans _ ((d*r)*(a*b)) _
      (poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3)))
        (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
        (by decide) (fun | 0 => d | 1 => a | 2 => r | _ => b))
      (Q'.eqv_trans _ (1*(a*b)) _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_recipPos_eqv d (varianceCost_positive hw0)))
        (Q'.one_mul_eqv _))
  exact Q'.le_of_mul_le_mul_left
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hp) (variance_coercivity w K extent hw0 hw1 hK c))
    (varianceCost_positive hw0)

end YMGap.Continuum.BF4ExactSlabPlaquetteAngularFamily

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteAngularFamily.totalEnergy_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteAngularFamily.totalEnergy_coercivity
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteAngularFamily.totalEnergy_squared_le
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteAngularFamily.variance_coercivity
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteAngularFamily.responseCostCoefficient_positive
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteAngularFamily.varianceCost_positive
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteAngularFamily.varianceFloor_positive
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteAngularFamily.variance_floor
