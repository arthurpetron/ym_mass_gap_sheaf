/-
# All-label harmonic selection for the original two-link heat kernel

Specialize only the auxiliary coefficients of the four-word solid mode.
Its head degree and zero Laplacian survive. Exact polynomial-valued Haar
orthogonality then removes EVERY label different from the input harmonic
degree, including lower labels. No retained physical link is fixed.

The actual finite heat packet reduces to its one diagonal character pairing,
or vanishes if the cutoff excludes that degree. The diagonal reproducing
factor is NOT supplied here. Thus this is not yet the full heat-propagation
identity, a finite-time interacting energy estimate, or a physical gap.
-/

import YMGap.Continuum.SU2QuaternionTailEvaluationDifferential
import YMGap.Continuum.SU2QuaternionRelativeHeatVacuum

namespace YMGap.Continuum.SU2QuaternionRelativeHarmonicSelection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonic
open YMGap.Continuum.SU2QuaternionHarmonicDegreeSelection
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
open YMGap.Continuum.SU2QuaternionPartialSphereGaussian
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionTailEvaluation
open YMGap.Continuum.SU2QuaternionTailEvaluationDifferential
open YMGap.Continuum.SU2QuaternionRelativeCharacterSelection
open YMGap.Continuum.SU2QuaternionRelativeHeatTransmission
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.RGTransport (qpow c4 dimQ)
open YMGap.Continuum.SU2CharacterVacuumHaar

local infix:50 " ≈ " => Q'.eqv

/-- The solid two-link representative is harmonic at every label, before
any boundary Haar integration. Only auxiliary quaternion coefficients are
specialized; the two physical links remain variables. -/
theorem relativeSolid_harmonic (spin : Nat) :
    RatPolyCoeffEqv (headLaplacian (relativeSolid spin)) polyZero := by
  have hh := laplacian_exposedSolidZonalCharacter_zero false true false false spin
  exact (solid_specialization spin).symm.headLaplacian.trans
    ((evaluate_headLaplacian 8 auxiliaryUnits (by decide) _).trans
      (evaluate_congr 8 auxiliaryUnits hh))

/-- Full off-diagonal annihilation, with every tail coefficient retained.
The test may be any head-homogeneous harmonic polynomial, not just a chosen
coordinate, trace-free quadratic, character, or positive combination. -/
theorem relativeSolid_harmonic_offDiagonal {spin degree : Nat} {p : RatPoly}
    (hp : HasQuaternionBlockDegree 0 degree p)
    (hh : RatPolyCoeffEqv (headLaplacian p) polyZero) (hne : spin ≠ degree) :
    RatPolyCoeffEqv (partialHaarHead (polyMul (relativeSolid spin) p)) polyZero := by
  let s := evaluateTail 8 auxiliaryUnits
    (exposedSolidZonalCharacter false true false false spin)
  have hs : HasQuaternionBlockDegree 0 spin s :=
    evaluate_headDegree 8 auxiliaryUnits (by decide)
      (exposedSolidZonalCharacter_blockDegree false true false false 0 (by decide) spin)
  have hl : RatPolyCoeffEqv (headLaplacian s) polyZero :=
    (evaluate_headLaplacian 8 auxiliaryUnits (by decide) _).trans
      (evaluate_congr 8 auxiliaryUnits
        (laplacian_exposedSolidZonalCharacter_zero false true false false spin))
  have hz : RatPolyCoeffEqv (partialHaarHead (polyMul s p)) polyZero := by
    by_cases hlt : degree < spin
    · exact partialHaarHead_harmonic_lower_degree hs hl hp hlt
    · exact (partialHaarHead_congr (RatPolyCoeffEqv.mul_comm s p)).trans
        (partialHaarHead_harmonic_lower_degree hp hh hs (by omega))
  exact (partialHaarHead_congr ((solid_specialization spin).mul_right p)).symm.trans hz

private theorem lifted_independent (r : RatPoly) :
    HeadQuaternionIndependent (liftHead r) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  rfl

/-- The ordinary character in the ACTUAL kernel, with an arbitrary retained
boundary. Both physical quaternion radii are removed only by proved Haar
carrier equalities. -/
theorem character_harmonic_boundary_zero (tailBlocks : Nat) (hb : 0 < tailBlocks)
    {spin degree : Nat} {p : RatPoly}
    (hp : HasQuaternionBlockDegree 0 degree p)
    (hh : RatPolyCoeffEqv (headLaplacian p) polyZero) (hne : spin ≠ degree)
    (boundary : RatPoly) :
    quaternionHaar (tailBlocks+1)
      (polyMul (polyMul (relativeCharacter spin) p) (liftHead boundary)) ≈ 0 := by
  have hc := haar_of_carrier
    (((solid_character_pin (tailBlocks+1) (by omega) spin).symm.mul_right p).mul_right
      (liftHead boundary))
  have hf := quaternionHaar_polyMul_headIndependent tailBlocks
    (polyMul (relativeSolid spin) p) (liftHead boundary) (lifted_independent boundary)
  rw [drop_liftHead] at hf
  exact Q'.eqv_trans _ _ _ hc (Q'.eqv_trans _ _ _ hf
    (haar_of_coeff ((relativeSolid_harmonic_offDiagonal hp hh hne).mul_right boundary)))

private theorem sum_insert (blocks : Nat) (f : Nat → RatPoly) (p : RatPoly) :
    ∀ xs : List Nat,
    quaternionHaar blocks (polyMul (finitePolySum f xs) p) ≈
      listQSum (fun s => quaternionHaar blocks (polyMul (f s) p)) xs
  | [] => Q'.eqv_refl _
  | s::xs => by
    change quaternionHaar blocks (polyMul (polyAdd (f s) (finitePolySum f xs)) p) ≈ _
    rw [polyMul_add_left_exact]
    exact Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (sum_insert blocks f p xs))

private theorem sum_congr (f g : Nat → Q') : ∀ xs : List Nat,
    (∀ s, s ∈ xs → f s ≈ g s) → listQSum f xs ≈ listQSum g xs
  | [], _ => Q'.eqv_refl _
  | s::xs, h => Q'.add_eqv_congr' (h s List.mem_cons_self)
      (sum_congr f g xs (fun t ht => h t (List.mem_cons_of_mem s ht)))

private theorem sum_append (f : Nat → Q') : ∀ xs ys : List Nat,
    listQSum f (xs++ys) ≈ listQSum f xs + listQSum f ys
  | [], _ => Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' _))
  | _::xs, ys => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (sum_append f xs ys)) (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))

private theorem sum_pick (degree : Nat) (value : Q') : ∀ count,
    listQSum (fun s => if s = degree then value else 0) (List.range count) ≈
      if degree < count then value else 0
  | 0 => by simp only [List.range_zero, listQSum, Nat.not_lt_zero, if_false]; exact Q'.eqv_refl _
  | count+1 => by
    rw [List.range_succ]
    refine Q'.eqv_trans _ _ _ (sum_append _ _ _) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (sum_pick degree value count)
      (Q'.eqv_of_eq (Q'.add_zero' _))) ?_
    by_cases hlt : degree < count
    · simp only [if_pos hlt, if_pos (by omega : degree < count+1),
        if_neg (by omega : count ≠ degree)]
      exact Q'.eqv_of_eq (Q'.add_zero' value)
    · by_cases he : count = degree
      · subst count
        simp only [Nat.lt_irrefl, if_false, Nat.lt_succ_self, if_true]
        exact Q'.eqv_of_eq (Q'.zero_add' value)
      · simp only [if_neg hlt, if_neg he, if_neg (by omega : ¬ degree < count+1)]
        exact Q'.eqv_refl _

/-- The full original packet selects exactly the input harmonic degree.
The remaining diagonal Haar pairing is explicit, not assumed to reproduce p.
The cutoff guard and every nome coefficient remain visible. -/
theorem heat_harmonic_diagonal (tailBlocks : Nat) (hb : 0 < tailBlocks)
    (w : Q') (K degree : Nat) {p : RatPoly}
    (hp : HasQuaternionBlockDegree 0 degree p)
    (hh : RatPolyCoeffEqv (headLaplacian p) polyZero) (boundary : RatPoly) :
    quaternionHaar (tailBlocks+1)
      (polyMul (polyMul (relativeHeat w K) p) (liftHead boundary)) ≈
      if degree ≤ K then coeffW w degree * quaternionHaar (tailBlocks+1)
        (polyMul (polyMul (relativeCharacter degree) p) (liftHead boundary)) else 0 := by
  let value := coeffW w degree * quaternionHaar (tailBlocks+1)
    (polyMul (polyMul (relativeCharacter degree) p) (liftHead boundary))
  refine Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_assoc (tailBlocks+1) _ _ _)
    (Q'.eqv_trans _ _ _ (sum_insert (tailBlocks+1) _ _ (List.range (K+1))) ?_)
  have hs : listQSum (fun s => quaternionHaar (tailBlocks+1)
      (polyMul (polySmul (coeffAt (heatKernelPacket K w) s) (relativeCharacter s))
        (polyMul p (liftHead boundary)))) (List.range (K+1)) ≈
      listQSum (fun s => if s = degree then value else 0) (List.range (K+1)) := by
    apply sum_congr
    intro s hmem
    rw [coeffAt_heatKernelPacket (List.mem_range.mp hmem)]
    refine Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left _ _ _))
      (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul _ _ _) ?_)
    by_cases he : s = degree
    · subst s
      rw [if_pos rfl]
      exact Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_symm (quaternionHaar_polyMul_assoc (tailBlocks+1) _ _ _))
    · rw [if_neg he]
      exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_polyMul_assoc (tailBlocks+1) _ _ _))
          (character_harmonic_boundary_zero tailBlocks hb hp hh he boundary)))
        (Q'.mul_zero_eqv _)
  exact Q'.eqv_trans _ _ _ hs
    (by simpa only [Nat.lt_succ_iff] using sum_pick degree value (K+1))

private theorem power_one : ∀ n, qpow (1 : Q') n ≈ 1
  | 0 => Q'.eqv_refl _
  | n+1 => Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (power_one n)) (Q'.one_mul_eqv _)

private theorem coefficient_nome_scaling (w : Q') (degree : Nat) :
    coeffW w degree ≈ qpow w (degree*(degree+2)) * coeffW 1 degree := by
  have hunit : coeffW 1 degree ≈ dimQ degree :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (power_one (c4 degree)))
      (Q'.mul_one_eqv _)
  exact Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
    (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hunit))

/-- Exact Casimir nome dependence for the original finite kernel pairings.
The reference at nome one is the SAME finite packet, not an assumed identity
operator or delta distribution. No normalization of its diagonal is used. -/
theorem heat_harmonic_nome_scaling (tailBlocks : Nat) (hb : 0 < tailBlocks)
    (w : Q') (K degree : Nat) {p : RatPoly}
    (hp : HasQuaternionBlockDegree 0 degree p)
    (hh : RatPolyCoeffEqv (headLaplacian p) polyZero) (boundary : RatPoly) :
    quaternionHaar (tailBlocks+1)
      (polyMul (polyMul (relativeHeat w K) p) (liftHead boundary)) ≈
      qpow w (degree*(degree+2)) * quaternionHaar (tailBlocks+1)
        (polyMul (polyMul (relativeHeat 1 K) p) (liftHead boundary)) := by
  have hw := heat_harmonic_diagonal tailBlocks hb w K degree hp hh boundary
  have hunit := heat_harmonic_diagonal tailBlocks hb 1 K degree hp hh boundary
  by_cases hK : degree ≤ K
  · rw [if_pos hK] at hw hunit
    exact Q'.eqv_trans _ _ _ hw
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (coefficient_nome_scaling w degree))
        (Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
          (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hunit))))
  · rw [if_neg hK] at hw hunit
    exact Q'.eqv_trans _ _ _ hw (Q'.eqv_symm
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hunit) (Q'.mul_zero_eqv _)))

end YMGap.Continuum.SU2QuaternionRelativeHarmonicSelection

#print axioms YMGap.Continuum.SU2QuaternionRelativeHarmonicSelection.relativeSolid_harmonic
#print axioms YMGap.Continuum.SU2QuaternionRelativeHarmonicSelection.relativeSolid_harmonic_offDiagonal
#print axioms YMGap.Continuum.SU2QuaternionRelativeHarmonicSelection.character_harmonic_boundary_zero
#print axioms YMGap.Continuum.SU2QuaternionRelativeHarmonicSelection.heat_harmonic_diagonal
#print axioms YMGap.Continuum.SU2QuaternionRelativeHarmonicSelection.heat_harmonic_nome_scaling
