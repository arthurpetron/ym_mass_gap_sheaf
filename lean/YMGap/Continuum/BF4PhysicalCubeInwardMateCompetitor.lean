/-
# A competing physical jump defeats a uniform direct inward-mate floor

The six-face profiles are source (2k+14,0,0,0,0,0), its literal inward
mate (2k+13,1,1,1,1,1), and competitor (2k+12,2,2,2,2,2).
Both targets have exactly the same boundary mask against this source.
Their SU(2) heat dimensions and Casimirs give a geometric upper bound on
the mate/competitor entry ratio. No assertion about the full spectral gap
is a consequence of a small selected transition probability.

Exact arithmetic pilot: computations/bf4_cube_inward_mate_competitor.py.
-/

import YMGap.Continuum.BF4PhysicalCubeKernelFactorization
import YMGap.Continuum.BF4PhysicalVacuumSectorCubeClassification
import YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio

namespace YMGap.Continuum.BF4PhysicalCubeInwardMateCompetitor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalCubeBoundaryMask
open YMGap.Continuum.BF4PhysicalCubeDifferenceBoundary
open YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryKernel
open YMGap.Continuum.BF4PhysicalCubeKernelFactorization
open YMGap.Continuum.BF4PhysicalVacuumSectorCubeClassification
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeIncidence
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateHeatBound
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateOrbits
open YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-- Distinguished face zero; the other five cube faces carry `low`. -/
def profile (high low : Nat) : EdgeLabelling := fun face =>
  if face = 0 then high else if face ∈ centralLowerCubeFaceIds then low else 0

def source (k : Nat) : EdgeLabelling := profile (2 * k + 14) 0
def mate (k : Nat) : EdgeLabelling := profile (2 * k + 13) 1
def competitor (k : Nat) : EdgeLabelling := profile (2 * k + 12) 2

theorem profile_zero_off (a b face : Nat) (hf : face ∉ centralLowerCubeFaceIds) :
    profile a b face = 0 := by
  have hz : face ≠ 0 := fun h => hf (by subst face; decide)
  simp [profile, hz, hf]

theorem profile_bounded (a b K : Nat) (ha : a ≤ K) (hb : b ≤ K) (face : Nat) :
    profile a b face ≤ K := by
  unfold profile
  split
  · exact ha
  · split
    · exact hb
    · exact Nat.zero_le K

theorem source_mate (k : Nat) :
    centralLowerCubeEvenInwardMatePhysical (source k) = mate k := by
  funext face
  by_cases hf : face ∈ centralLowerCubeFaceIds
  · simp only [centralLowerCubeEvenInwardMatePhysical, hf, ↓reduceIte,
      source, mate, profile]
    by_cases hz : face = 0 <;> simp [hz, evenInwardMateLabel]
  · rw [centralLowerCubeEvenInwardMatePhysical, if_neg hf]
    exact Eq.trans (profile_zero_off _ _ face hf) (profile_zero_off _ _ face hf).symm

private theorem fusion_sum (a b : Nat) : fusionOK a b (a + b) = true := by
  rw [fusionOK_eq_true_iff]
  constructor
  · exact Nat.le_trans (Nat.sub_le _ _) (Nat.max_le.mpr ⟨by omega, by omega⟩)
  · exact ⟨Nat.le_refl _, by omega⟩

private theorem transfer_split (high a b c : Nat) (hab : a + b = high)
    (h : fusionOK high 0 c = true) : fusionOK a b c = true := by
  rw [fusionOK_eq_true_iff] at h
  simp only [Nat.max_zero, Nat.min_zero, Nat.sub_zero] at h
  have hc : c = high := by omega
  rw [hc, ← hab]
  exact fusion_sum a b

private theorem transfer_zero (b c : Nat) (h : fusionOK 0 0 c = true) :
    fusionOK b b c = true := by
  rw [fusionOK_eq_true_iff] at h
  have hc : c = 0 := by omega
  rw [hc]
  exact fusionOK_zero_diag_self b

/-- Every edge channel permitted by the one-face source is permitted by
any split of its high label between the distinguished face and the other five. -/
theorem split_admissible (high a b : Nat) (hab : a + b = high)
    (boundary : EdgeLabelling) (hs : cubeEdgeAdmissibleB (profile high 0) boundary = true) :
    cubeEdgeAdmissibleB (profile a b) boundary = true := by
  apply List.all_eq_true.mpr
  intro e he
  have h := List.all_eq_true.mp hs e he
  simp only [cubeDifferenceEdges, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0 <;> subst e
  all_goals simp only [profile, centralLowerCubeFaceIds, List.mem_cons,
    Nat.reduceEqDiff, ↓reduceIte, or_true, true_or] at h ⊢
  all_goals first | exact transfer_split high a b _ hab h | exact transfer_zero b _ h

/-- Equality of the full Boolean masks, including every forbidden boundary. -/
theorem mate_competitor_mask (k : Nat) (boundary : EdgeLabelling) :
    cubeKernelAllowedB (source k) (mate k) boundary =
      cubeKernelAllowedB (source k) (competitor k) boundary := by
  cases hs : cubeEdgeAdmissibleB (source k) boundary with
  | false => simp [cubeKernelAllowedB, hs]
  | true =>
      have hm := split_admissible (2 * k + 14) (2 * k + 13) 1 (by omega) boundary hs
      have hc := split_admissible (2 * k + 14) (2 * k + 12) 2 (by omega) boundary hs
      simp only [cubeKernelAllowedB, mate, competitor, hm, hc]

theorem mate_competitor_overlap (w : Q') (K k : Nat) :
    cubeBoundaryOverlap w K (source k) (mate k) =
      cubeBoundaryOverlap w K (source k) (competitor k) := by
  unfold cubeBoundaryOverlap
  congr 1
  funext boundary
  rw [mate_competitor_mask]

private theorem dim_product (a b : Nat) (x y : Q') :
    (Q'.ofNat a * x) * (Q'.ofNat b * y) ≈ Q'.ofNat (a * b) * (x * y) := by
  show ((Q'.ofNat a * x) * (Q'.ofNat b * y)).num *
      ((Q'.ofNat (a * b) * (x * y)).den : Int) =
    (Q'.ofNat (a * b) * (x * y)).num *
      (((Q'.ofNat a * x) * (Q'.ofNat b * y)).den : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  simp only [Q'.ofNat, Q'.den]
  rw [show Int.ofNat (a * b) = Int.ofNat a * Int.ofNat b from rfl]
  push_cast
  ac_rfl

/-- Finite products expose their dimension and Casimir sums, without division. -/
private theorem heat_product (w : Q') (state : EdgeLabelling) : ∀ ids : List Nat,
    eliminateLinks (fun face => coeffW w (state face)) ids ≈
      Q'.ofNat ((ids.map (fun face => state face + 1)).foldr (· * ·) 1) *
        qpow w ((ids.map (fun face => c4 (state face))).foldr (· + ·) 0)
  | [] => by exact Q'.eqv_refl _
  | face :: ids => by
      simp only [eliminateLinks, List.map_cons, List.foldr_cons]
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (heat_product w state ids)) ?_
      refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (Q'.mul_eqv_congr_left _ _ _
        (qpow_add w (c4 (state face)) _)))
      exact dim_product _ _ _ _

theorem profile_heat (w : Q') (a b : Nat) :
    halfHeat w (profile a b) ≈
      Q'.ofNat ((a + 1) * ((b + 1) * ((b + 1) * ((b + 1) * ((b + 1) * (b + 1)))))) *
        qpow w (c4 a + (c4 b + (c4 b + (c4 b + (c4 b + c4 b))))) := by
  have h := heat_product w (profile a b) (centralLowerFaceIds 0)
  have ids : centralLowerFaceIds 0 =
      [0, 1, 3, 9, 10, 12, 18, 19, 21, 27, 28, 30, 36, 37, 39, 45, 46, 48,
        54, 55, 57, 63, 64, 66] := by decide
  rw [ids] at h
  simpa [profile, centralLowerCubeFaceIds, c4_zero, Nat.add_zero, Nat.mul_one] using h

theorem mate_heat (w : Q') (k : Nat) :
    halfHeat w (mate k) ≈ Q'.ofNat (32 * (2 * k + 14)) * qpow w (c4 (2 * k + 13) + 15) := by
  simpa [mate, c4, Nat.mul_comm, Nat.add_assoc] using profile_heat w (2 * k + 13) 1

theorem competitor_heat (w : Q') (k : Nat) :
    halfHeat w (competitor k) ≈ Q'.ofNat (243 * (2 * k + 13)) * qpow w (c4 (2 * k + 12) + 40) := by
  simpa [competitor, c4, Nat.mul_comm, Nat.add_assoc] using profile_heat w (2 * k + 12) 2

theorem casimir_payment (k : Nat) :
    c4 (2 * k + 13) + 15 = (4 * k + 2) + (c4 (2 * k + 12) + 40) := by
  simp only [c4, Nat.add_mul, Nat.mul_add]
  omega

theorem dimension_comparison (k : Nat) : 32 * (2 * k + 14) ≤ 243 * (2 * k + 13) := by omega

private theorem swap_factors (a b c : Q') : a * (b * c) ≈ b * (a * c) :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _))
      (Q'.mul_assoc_eqv _ _ _))

/-- SU(2) Casimir payment: the direct mate loses at least `4k+2` heat powers
against the admissible competing target. No cutoff or row-size estimate. -/
theorem heat_comparison {w : Q'} (hw : (0 : Q') ≤ w) (k : Nat) :
    halfHeat w (mate k) ≤ qpow w (4 * k + 2) * halfHeat w (competitor k) := by
  have hm := mate_heat w k
  rw [casimir_payment] at hm
  have he := Q'.eqv_trans _ _ _ hm (Q'.mul_eqv_congr_left _ _ _
    (qpow_add w (4 * k + 2) (c4 (2 * k + 12) + 40)))
  have hd := CReal.ofNat_le_ofNat (dimension_comparison k)
  have hp := Q'.mul_nonneg _ _ (qpow_nonneg w hw (4 * k + 2))
    (qpow_nonneg w hw (c4 (2 * k + 12) + 40))
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv he) (Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hd hp) ?_)
  exact Q'.le_of_eqv (Q'.eqv_trans _ _ _ (swap_factors _ _ _)
    (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (competitor_heat w k))))

private theorem product_nonneg {w : Q'} (hw : (0 : Q') ≤ w) (state : EdgeLabelling) :
    ∀ ids : List Nat, (0 : Q') ≤ eliminateLinks (fun face => coeffW w (state face)) ids
  | [] => by change (0 : Q') ≤ 1; decide
  | face :: ids => Q'.mul_nonneg _ _ (coeffW_nonneg hw _) (product_nonneg hw state ids)

private theorem overlap_nonneg {w : Q'} (hw : (0 : Q') ≤ w) (K : Nat) (s t : EdgeLabelling) :
    (0 : Q') ≤ cubeBoundaryOverlap w K s t := by
  apply listQSum_nonnegative_on
  intro boundary _
  apply Q'.mul_nonneg _ _ (product_nonneg hw boundary _)
  exact CReal.ofNat_le_ofNat (Nat.zero_le _)

/-- Upper comparison of entries of the ORIGINAL reflected physical kernel. -/
theorem kernel_comparison {w : Q'} (hw : (0 : Q') ≤ w) (K k : Nat) (hK : 2 * k + 14 ≤ K) :
    centralPhysicalReflectedKernel w K 0 (source k) (mate k) ≤
      qpow w (4 * k + 2) * centralPhysicalReflectedKernel w K 0 (source k) (competitor k) := by
  have hs := profile_bounded (2 * k + 14) 0 K hK (by omega)
  have hm := profile_bounded (2 * k + 13) 1 K (by omega) (by omega)
  have hc := profile_bounded (2 * k + 12) 2 K (by omega) (by omega)
  have em := cubePhysicalKernel_eq_heat_overlap w K (source k) (mate k) hs hm
    (profile_zero_off _ _) (profile_zero_off _ _)
  have ec := cubePhysicalKernel_eq_heat_overlap w K (source k) (competitor k) hs hc
    (profile_zero_off _ _) (profile_zero_off _ _)
  rw [mate_competitor_overlap] at em
  have h := Q'.mul_le_mul_of_nonneg_right _ _ (cubeBoundaryOverlap w K (source k) (competitor k))
    (Q'.mul_le_mul_of_nonneg_left _ _ (halfHeat w (source k))
      (heat_comparison hw k) (product_nonneg hw _ _)) (overlap_nonneg hw K _ _)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv em) (Q'.le_trans' _ _ _ h ?_)
  apply Q'.le_of_eqv
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (swap_factors _ _ _)) ?_
  exact Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
    (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm ec))

end YMGap.Continuum.BF4PhysicalCubeInwardMateCompetitor

#print axioms YMGap.Continuum.BF4PhysicalCubeInwardMateCompetitor.profile
#print axioms YMGap.Continuum.BF4PhysicalCubeInwardMateCompetitor.profile_zero_off
#print axioms YMGap.Continuum.BF4PhysicalCubeInwardMateCompetitor.profile_bounded
#print axioms YMGap.Continuum.BF4PhysicalCubeInwardMateCompetitor.source
#print axioms YMGap.Continuum.BF4PhysicalCubeInwardMateCompetitor.mate
#print axioms YMGap.Continuum.BF4PhysicalCubeInwardMateCompetitor.competitor
#print axioms YMGap.Continuum.BF4PhysicalCubeInwardMateCompetitor.source_mate
#print axioms YMGap.Continuum.BF4PhysicalCubeInwardMateCompetitor.split_admissible
#print axioms YMGap.Continuum.BF4PhysicalCubeInwardMateCompetitor.mate_competitor_mask
#print axioms YMGap.Continuum.BF4PhysicalCubeInwardMateCompetitor.mate_competitor_overlap
#print axioms YMGap.Continuum.BF4PhysicalCubeInwardMateCompetitor.profile_heat
#print axioms YMGap.Continuum.BF4PhysicalCubeInwardMateCompetitor.mate_heat
#print axioms YMGap.Continuum.BF4PhysicalCubeInwardMateCompetitor.competitor_heat
#print axioms YMGap.Continuum.BF4PhysicalCubeInwardMateCompetitor.casimir_payment
#print axioms YMGap.Continuum.BF4PhysicalCubeInwardMateCompetitor.dimension_comparison
#print axioms YMGap.Continuum.BF4PhysicalCubeInwardMateCompetitor.heat_comparison
#print axioms YMGap.Continuum.BF4PhysicalCubeInwardMateCompetitor.kernel_comparison
