/-
# A nonzero, original-source-pinned early fringe pairing

Join the full three-face heat moment to the actual numeric Haar telescope
of the original centered source. Subtracting twice the active probe from
the tester leaves that pairing unchanged by conditional centering.
The probe is auxiliary and not gauge-invariant. This is neither a physical
excitation nor a spectral-gap statement.
-/

import YMGap.Continuum.BF4ExactSlabWidthOneSource
import YMGap.Continuum.BF4ExactSlabWidthOnePacketMoment

namespace YMGap.Continuum.BF4ExactSlabWidthOneFringeMoment

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq qpow)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabWidthOneGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredHaarTelescope (piece piece_centered)
open YMGap.Continuum.BF4ExactSlabWidthOneSource (probe probe_supported probe_independent)
open YMGap.Continuum.BF4ExactSlabWidthOnePacketMoment
  (tester tester_supported tester_first_independent tester_project_two_zero packet_moment)
open YMGap.Continuum.SU2QuaternionCornerFundamentalMoment (hex insertion)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarBlockProjection (project project_fixed project_selfAdjoint)
open YMGap.Continuum.QuaternionHaarSquareCertificate

local notation "N" => List.length (baseLinks 1)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks spatialWeight

private theorem support_smul {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (c : Q') :
    SupportedQuaternionBlocks blocks (polySmul c p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

/-- The shift removes a constant character value, not an action factor. -/
def shiftedTester : RatPoly := polyAdd tester (polySmul (-2) probe)

theorem shiftedTester_supported : SupportedQuaternionBlocks N shiftedTester :=
  supported_add (by rw [baseLinks_length]; exact tester_supported)
    (support_smul probe_supported (-2))

/-- Exact source pairing, for every rational nome and every cutoff K >= 1. -/
theorem source_pair (w : Q') (K : Nat) (hK : 1 ≤ K) :
    quaternionHaar N (polyMul (piece w K 1 0 2 probe) tester) ≈
      Q'.mkPos 1 2 (by decide) * qpow w 9 := by
  have ht : SupportedQuaternionBlocks N tester := by
    rw [baseLinks_length]
    exact tester_supported
  have h := BF4ExactSlabWidthOneSource.piece_test w K tester ht
    (tester_first_independent 0 (Or.inl rfl))
    (tester_first_independent 1 (Or.inr rfl)) tester_project_two_zero
  have he : RatPolyCoeffEqv (polyMul (polyMul (spatialWeight w K 1) probe) tester)
      (polyMul (spatialWeight w K 1) insertion) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 1)))
      (.mul (.var 0) (.mul (.var 2) (.mul (.var 1) (.var 1))))
      (by decide) (fun | 0 => spatialWeight w K 1 | 1 => probe | _ => hex)
  exact Q'.eqv_trans _ _ _ h
    (Q'.eqv_trans _ _ _ (haar_of_coeff he)
      (by rw [baseLinks_length]; exact packet_moment w K hK))

/-- The original active probe is invisible to this fringe piece. -/
theorem source_probe_zero (w : Q') (K : Nat) :
    quaternionHaar N (polyMul (piece w K 1 0 2 probe) probe) ≈ 0 := by
  have hi : 2 < N := by rw [baseLinks_length]; decide
  have hp := project_fixed 2 probe (probe_independent 2 (by decide))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (haar_of_coeff (hp.mul_left _)))
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (project_selfAdjoint N 2 hi _ probe))
      (haar_of_coeff (((piece_centered w K 1 0 2 probe).mul_right probe).trans
        (RatPolyCoeffEqv.mul_zero_left probe))))

/-- Apply the adapted-tester theorem before shifting: the shifted tester
itself does NOT have zero conditional projection in block two. -/
theorem shifted_source_pair (w : Q') (K : Nat) (hK : 1 ≤ K) :
    quaternionHaar N (polyMul (piece w K 1 0 2 probe) shiftedTester) ≈
      Q'.mkPos 1 2 (by decide) * qpow w 9 := by
  have he := (RatPolyCoeffEqv.mul_add_right (piece w K 1 0 2 probe) tester
    (polySmul (-2) probe)).trans
      ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.polyMul_smul_right _ _ _))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff he)
    (Q'.eqv_trans _ _ _ (quaternionHaar_append N _ _)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (source_pair w K hK)
          (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul N _ _)
            (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (source_probe_zero w K))
              (Q'.mul_zero_eqv _))))
        (Q'.eqv_of_eq (Q'.add_zero' _))))

end YMGap.Continuum.BF4ExactSlabWidthOneFringeMoment

#print axioms YMGap.Continuum.BF4ExactSlabWidthOneFringeMoment.shiftedTester
#print axioms YMGap.Continuum.BF4ExactSlabWidthOneFringeMoment.shiftedTester_supported
#print axioms YMGap.Continuum.BF4ExactSlabWidthOneFringeMoment.source_pair
#print axioms YMGap.Continuum.BF4ExactSlabWidthOneFringeMoment.source_probe_zero
#print axioms YMGap.Continuum.BF4ExactSlabWidthOneFringeMoment.shifted_source_pair
