/-
# Exact aggregate seed geometry on the original odd marginal

The active-plus-fringe label family is a permutation of every retained
coordinate. Summing the actual density-multiplied seed defects therefore
recovers nu*(sum q_i-Phi) under arbitrary Haar insertions. The zero-mean
full-projection residue is removed only by its proved Haar-carrier equality,
never by a false raw coefficient equality.

These pins connect the concrete finite seeds to same-marginal norm bounds.
No approximation tolerance, signed-cost budget or physical gap is assumed.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeed
import YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredHaarTelescope
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyErasure

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSeedFamily

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight marginalWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeed
open YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredHaarTelescope
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyErasure (labels labels_nodup labels_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (retained_coordinate_partition)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex (carrier_of_supported)
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights (perm_of_nodup_mem_iff_constructive)
open YMGap.Continuum.QuaternionHaarSquareCertificate

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks

private theorem range_nodup (count : Nat) : (List.range count).Nodup := by
  induction count with
  | zero => exact List.nodup_nil
  | succ count ih =>
      rw [List.range_succ]
      refine List.nodup_append.mpr
        ⟨ih, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro i hi j hj he
      have hj' : j = count := List.mem_singleton.mp hj
      rw [he, hj'] at hi
      exact absurd (List.mem_range.mp hi) (Nat.lt_irrefl count)

theorem labels_perm_range (width : Nat) : (labels width).Perm (List.range (N width)) := by
  apply perm_of_nodup_mem_iff_constructive _ _ (labels_nodup width) (range_nodup _)
  intro i
  constructor
  · intro hi
    exact List.mem_range.mpr (labels_lt width i hi)
  · intro hi
    exact List.mem_append.mpr (retained_coordinate_partition width i (List.mem_range.mp hi)).1

private theorem sum_perm {ps qs : List RatPoly} (hp : ps.Perm qs) :
    RatPolyCoeffEqv (polySum ps) (polySum qs) := by
  induction hp with
  | nil => exact .refl _
  | cons p _ ih => exact (RatPolyCoeffEqv.refl p).add ih
  | swap p q ps =>
      exact coeffEvalExpr_eqv_of_normalize_eq
        (.add (.var 0) (.add (.var 1) (.var 2)))
        (.add (.var 1) (.add (.var 0) (.var 2))) (by decide)
        (fun | 0 => q | 1 => p | _ => polySum ps)
  | trans _ _ h1 h2 => exact h1.trans h2

theorem sum_supported {A : Type} {blocks : Nat} (f : A → RatPoly) :
    ∀ ids : List A, (∀ i, i ∈ ids → SupportedQuaternionBlocks blocks (f i)) →
      SupportedQuaternionBlocks blocks (polySum (ids.map f))
  | [], _ => by intro t ht; cases ht
  | i::ids, hf => supported_add (hf i List.mem_cons_self)
      (sum_supported f ids (fun j hj => hf j (List.mem_cons_of_mem i hj)))

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) : SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ht
  exact hp r hr

private theorem sum_defect {A : Type} (nu : RatPoly) (q tau : A → RatPoly) :
    ∀ ids : List A,
    RatPolyCoeffEqv (polySum (ids.map (fun i => polyAdd (polyMul nu (q i)) (polyNeg (tau i)))))
      (polyAdd (polyMul nu (polySum (ids.map q))) (polyNeg (polySum (ids.map tau))))
  | [] => ((RatPolyCoeffEqv.add_zero _).trans (RatPolyCoeffEqv.mul_zero_right nu)).symm
  | i::ids => by
      change RatPolyCoeffEqv
        (polyAdd (polyAdd (polyMul nu (q i)) (polyNeg (tau i)))
          (polySum (ids.map _))) _
      exact ((RatPolyCoeffEqv.refl _).add (sum_defect nu q tau ids)).trans
        (coeffEvalExpr_eqv_of_normalize_eq
          (.add (.add (.mul (.var 0) (.var 1)) (.neg (.var 2)))
            (.add (.mul (.var 0) (.var 3)) (.neg (.var 4))))
          (.add (.mul (.var 0) (.add (.var 1) (.var 3)))
            (.neg (.add (.var 2) (.var 4)))) (by decide)
          (fun | 0 => nu | 1 => q i | 2 => tau i
               | 3 => polySum (ids.map q) | _ => polySum (ids.map tau)))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)

def familySeeds (k : Nat) (f : RatPoly) (i : Nat) : RatPoly :=
  seed hw0 hw1 K width hK n i k (piece w K width n i f)

def familyTests (k : Nat) (f : RatPoly) (i : Nat) : RatPoly :=
  test hw0 hw1 K width hK n i k (piece w K width n i f)

def rawSum (k : Nat) (f : RatPoly) : RatPoly :=
  polySum ((labels width).map (familyTests hw0 hw1 K width hK n k f))

def defectSum (k : Nat) (f : RatPoly) : RatPoly :=
  polySum ((labels width).map (fun i => defect hw0 hw1 K width hK n i k (piece w K width n i f)))

def rawError (k : Nat) (f : RatPoly) : RatPoly :=
  polyAdd (rawSum hw0 hw1 K width hK n k f) (polyNeg (centeredObservable w K width n f))

theorem familySeeds_supported (k i : Nat) {f : RatPoly} (hf : SupportedQuaternionBlocks (N width) f) :
    SupportedQuaternionBlocks (N width) (familySeeds hw0 hw1 K width hK n k f i) :=
  seed_supported hw0 hw1 K width hK n i k (piece_supported w K width n i hf)

theorem familyTests_supported (k i : Nat) {f : RatPoly} (hf : SupportedQuaternionBlocks (N width) f) :
    SupportedQuaternionBlocks (N width) (familyTests hw0 hw1 K width hK n k f i) :=
  test_supported hw0 hw1 K width hK n i k (piece_supported w K width n i hf)

theorem rawSum_supported (k : Nat) {f : RatPoly} (hf : SupportedQuaternionBlocks (N width) f) :
    SupportedQuaternionBlocks (N width) (rawSum hw0 hw1 K width hK n k f) :=
  sum_supported _ _ (fun i _ => familyTests_supported hw0 hw1 K width hK n k i hf)

theorem defectSum_supported (k : Nat) {f : RatPoly} (hf : SupportedQuaternionBlocks (N width) f) :
    SupportedQuaternionBlocks (N width) (defectSum hw0 hw1 K width hK n k f) :=
  sum_supported _ _ (fun i _ => defect_supported hw0 hw1 K width hK n i k
    (piece_supported w K width n i hf))

theorem rawError_supported (k : Nat) {f : RatPoly} (hf : SupportedQuaternionBlocks (N width) f) :
    SupportedQuaternionBlocks (N width) (rawError hw0 hw1 K width hK n k f) :=
  supported_add (rawSum_supported hw0 hw1 K width hK n k hf)
    (support_neg (centeredObservable_supported w K width n hf))

/-- The only endpoint transport uses the proved same-Haar zero-mean identity. -/
theorem density_error_pin (k : Nat) {f : RatPoly} (hf : SupportedQuaternionBlocks (N width) f) :
    HaarCarrierEqv (N width)
      (polyMul (marginalWeight w K width n) (rawError hw0 hw1 K width hK n k f))
      (defectSum hw0 hw1 K width hK n k f) := by
  let nu := marginalWeight w K width n
  let qs := familyTests hw0 hw1 K width hK n k f
  let ts := fun i => piece w K width n i f
  have hp : RatPolyCoeffEqv (polySum ((labels width).map ts)) (pieceSum w K width n f) :=
    sum_perm ((labels_perm_range width).map ts)
  have ht : HaarCarrierEqv (N width) (polySum ((labels width).map ts)) (source w K width n f) :=
    (RatPolyCoeffEqv.haarCarrier hp).trans (carrier_of_supported (pieceSum_supported w K width n hf)
      (source_supported w K width n hf) (pieceSum_source w K width n hf))
  have hd := sum_defect nu qs ts (labels width)
  have he : RatPolyCoeffEqv
      (polyMul nu (rawError hw0 hw1 K width hK n k f))
      (polyAdd (polyMul nu (rawSum hw0 hw1 K width hK n k f))
        (polyNeg (source w K width n f))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
      (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 0) (.var 2))))
      (by decide) (fun
        | 0 => nu
        | 1 => rawSum hw0 hw1 K width hK n k f
        | _ => centeredObservable w K width n f)
  exact (RatPolyCoeffEqv.haarCarrier he).trans
    ((HaarCarrierEqv.add (.refl _ _) (HaarCarrierEqv.neg ht.symm)).trans
      (RatPolyCoeffEqv.haarCarrier hd.symm))

theorem density_error_square (k : Nat) {f : RatPoly} (hf : SupportedQuaternionBlocks (N width) f) :
    quaternionHaar (N width) (polyMul
      (polyMul (marginalWeight w K width n) (rawError hw0 hw1 K width hK n k f))
      (polyMul (marginalWeight w K width n) (rawError hw0 hw1 K width hK n k f))) ≈
    quaternionHaar (N width) (polyMul (defectSum hw0 hw1 K width hK n k f)
      (defectSum hw0 hw1 K width hK n k f)) := by
  have h := density_error_pin hw0 hw1 K width hK n k hf
  exact Q'.eqv_trans _ _ _ (h _)
    (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)) (h _))

end YMGap.Continuum.BF4ExactSlabFixedSpatialSeedFamily

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSeedFamily.labels_perm_range
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSeedFamily.sum_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSeedFamily.familySeeds
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSeedFamily.familyTests
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSeedFamily.familySeeds_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSeedFamily.familyTests_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSeedFamily.rawSum_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSeedFamily.defectSum_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSeedFamily.rawError_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSeedFamily.density_error_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSeedFamily.density_error_square
