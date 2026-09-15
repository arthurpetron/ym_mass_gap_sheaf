/-
# Exact quadratic transmission through the ORIGINAL relative heat kernel

The trace-free quadratic U_i U_j - delta_ij |U|^2/4 has degree two,
not degree one. Every full packet with K >= 2 transmits it by w^8.
All higher spins vanish by the existing harmonic degree-selection theorem;
the three low-spin moments are finite coefficient identities. Every retained
link remains in an arbitrary polynomial insertion, on the same Haar carrier.

This supplies the quadratic sector of a local polynomial inverse calculation.
It does not commute multiplication through the heat operator, discard action
factors using U, identify an original plaquette expression, or establish an
OS-state preimage. Full original boundary-state comparison, thermodynamic
time zero, spacing control and the continuum/Clay theorem remain open.
-/

import YMGap.Continuum.SU2QuaternionRelativeHeatVacuum
import YMGap.Constructive.Sqrt

namespace YMGap.Continuum.SU2QuaternionQuadraticHeatTransmission

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
open YMGap.Continuum.SU2QuaternionPartialSphereGaussian
open YMGap.Continuum.SU2QuaternionTailEvaluation
open YMGap.Continuum.SU2QuaternionExposedHeatCutoffSelection
open YMGap.Continuum.SU2QuaternionRelativeCharacterSelection
open YMGap.Continuum.SU2QuaternionRelativeHeatTransmission
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2CharacterVacuumHaar

local infix:50 " ≈ " => Q'.eqv

/-- The original coordinate polynomials, with their literal monomial padding. -/
def coordinatePair (i j : Fin 4) : RatPoly :=
  polyMul (polyVar i.val) (polyVar j.val)

def radius : RatPoly := polyAdd (coordinatePair 0 0) (polyAdd (coordinatePair 1 1)
  (polyAdd (coordinatePair 2 2) (coordinatePair 3 3)))

def quarter : Q' := Q'.mkPos 1 4 (by decide)
def third : Q' := Q'.mkPos 1 3 (by decide)

def quadratic (i j : Fin 4) : RatPoly :=
  polyAdd (coordinatePair i j) (polySmul (if i = j then -quarter else 0) radius)

theorem quadratic_degree (i j : Fin 4) : headDegreeBound (quadratic i j) = 2 := by
  revert i j
  decide +kernel

/-- The trace is retained explicitly; it cannot be treated as a degree-two mode. -/
theorem quadratic_trace_decomposition (i j : Fin 4) :
    RatPolyCoeffEqv (polyAdd (quadratic i j) (polySmul (if i = j then quarter else 0) radius))
      (coordinatePair i j) := by
  apply RatPolyCoeffEqv.of_canon_termwise
  revert i j
  decide +kernel

private theorem quadratic_specialization (i j : Fin 4) :
    RatPolyCoeffEqv (evaluateTail 8 auxiliaryUnits (quadratic i j)) (quadratic i j) := by
  apply RatPolyCoeffEqv.of_canon_termwise
  revert i j
  decide +kernel

/-- The only low-spin contribution is spin two, with the exact Schur factor 1/3. -/
theorem low_spin_partial (spin : Fin 3) (i j : Fin 4) :
    RatPolyCoeffEqv (partialHaarHead (polyMul (relativeCharacter spin.val) (quadratic i j)))
      (if spin.val = 2 then polySmul third (quadratic i j) else polyZero) := by
  apply RatPolyCoeffEqv.of_canon_termwise
  revert spin i j
  decide +kernel

theorem high_spin_partial_zero (spin : Nat) (hs : 2 < spin) (i j : Fin 4) :
    RatPolyCoeffEqv (partialHaarHead (polyMul (relativeSolid spin) (quadratic i j))) polyZero := by
  have hz := exposedSolid_partialHaar_zero false true false false spin (quadratic i j)
    (by rw [quadratic_degree]; exact hs)
  have hp := (evaluate_mul 8 auxiliaryUnits _ _).trans
    ((solid_specialization spin).mul (quadratic_specialization i j))
  exact (partialHaarHead_congr hp).symm.trans (partialHaarHead_evaluate_zero 4 auxiliaryUnits hz)

private theorem lifted_independent (r : RatPoly) : HeadQuaternionIndependent (liftHead r) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
  rfl

private theorem low_spin_boundary (tailBlocks : Nat) (spin : Fin 3) (i j : Fin 4) (r : RatPoly) :
    quaternionHaar (tailBlocks+1) (polyMul
      (polyMul (relativeCharacter spin.val) (quadratic i j)) (liftHead r)) ≈
      (if spin.val = 2 then third * quaternionHaar tailBlocks (polyMul (quadratic i j) r) else 0) := by
  have hf := quaternionHaar_polyMul_headIndependent tailBlocks
    (polyMul (relativeCharacter spin.val) (quadratic i j)) (liftHead r) (lifted_independent r)
  rw [drop_liftHead] at hf
  refine Q'.eqv_trans _ _ _ hf (Q'.eqv_trans _ _ _
    (haar_of_coeff ((low_spin_partial spin i j).mul_right r)) ?_)
  split
  · exact Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left _ _ _))
      (quaternionHaar_polySmul _ _ _)
  · exact Q'.eqv_refl _

/-- All ordinary characters, not a selected-spin replacement of the action. -/
theorem character_quadratic_boundary (tailBlocks : Nat) (hb : 0 < tailBlocks)
    (spin : Nat) (i j : Fin 4) (r : RatPoly) :
    quaternionHaar (tailBlocks+1) (polyMul
      (polyMul (relativeCharacter spin) (quadratic i j)) (liftHead r)) ≈
      (if spin = 2 then third * quaternionHaar tailBlocks (polyMul (quadratic i j) r) else 0) := by
  match spin with
  | 0 => exact low_spin_boundary tailBlocks 0 i j r
  | 1 => exact low_spin_boundary tailBlocks 1 i j r
  | 2 => exact low_spin_boundary tailBlocks 2 i j r
  | spin+3 =>
    have hc := haar_of_carrier ((((solid_character_pin (tailBlocks+1) (by omega) (spin+3)).symm).mul_right
      (quadratic i j)).mul_right (liftHead r))
    have hf := quaternionHaar_polyMul_headIndependent tailBlocks
      (polyMul (relativeSolid (spin+3)) (quadratic i j)) (liftHead r) (lifted_independent r)
    rw [drop_liftHead] at hf
    exact Q'.eqv_trans _ _ _ hc (Q'.eqv_trans _ _ _ hf
      (haar_of_coeff ((high_spin_partial_zero (spin+3) (by omega) i j).mul_right r)))

private theorem sum_insert (blocks : Nat) (f : Nat → RatPoly) (p : RatPoly) : ∀ xs : List Nat,
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

private theorem sum_spin_two (value : Q') : ∀ k,
    listQSum (fun s => if s = 2 then value else 0) (List.range (k+3)) ≈ value
  | 0 => by
    change (0 : Q') + (0 + (value + 0)) ≈ value
    rw [Q'.zero_add', Q'.zero_add', Q'.add_zero']
    exact Q'.eqv_refl _
  | k+1 => by
    rw [show k+1+3 = (k+3)+1 by omega, List.range_succ]
    refine Q'.eqv_trans _ _ _ (sum_append _ _ _) ?_
    have hz : listQSum (fun s => if s = 2 then value else 0) [k+3] ≈ 0 := by
      simp only [listQSum, if_neg (show k+3 ≠ 2 by omega), Q'.add_zero']
      exact Q'.eqv_refl _
    exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (sum_spin_two value k) hz)
      (Q'.eqv_of_eq (Q'.add_zero' _))

theorem quadratic_heat_coefficient (w : Q') : coeffW w 2 * third ≈ qpow w 8 := by
  change (3 * qpow w 8) * third ≈ qpow w 8
  exact Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
    (.mul (.mul (.const 3) (.var 0)) (.var 1)) (.mul (.mul (.const 3) (.var 1)) (.var 0))
    (by decide) (fun | 0 => qpow w 8 | _ => third))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (by decide : (3 : Q') * third ≈ 1))
      (Q'.one_mul_eqv _))

/-- Same full finite packet and all retained insertions, uniformly for K >= 2.
The coupling dependence is the explicit w^8, not the degree-one w^3. -/
theorem quadratic_heat_transmission (tailBlocks : Nat) (hb : 0 < tailBlocks)
    (w : Q') (K : Nat) (hK : 2 ≤ K) (i j : Fin 4) (r : RatPoly) :
    quaternionHaar (tailBlocks+1) (polyMul
      (polyMul (relativeHeat w K) (quadratic i j)) (liftHead r)) ≈
      qpow w 8 * quaternionHaar tailBlocks (polyMul (quadratic i j) r) := by
  let value := quaternionHaar tailBlocks (polyMul (quadratic i j) r)
  refine Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_assoc (tailBlocks+1) _ _ _)
    (Q'.eqv_trans _ _ _ (sum_insert (tailBlocks+1) _ _ (List.range (K+1))) ?_)
  have ht : listQSum (fun s => quaternionHaar (tailBlocks+1) (polyMul
      (polySmul (coeffAt (heatKernelPacket K w) s) (relativeCharacter s))
      (polyMul (quadratic i j) (liftHead r)))) (List.range (K+1)) ≈
      listQSum (fun s => if s = 2 then qpow w 8 * value else 0) (List.range (K+1)) := by
    apply sum_congr
    intro s hmem
    rw [coeffAt_heatKernelPacket (List.mem_range.mp hmem)]
    refine Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left _ _ _))
      (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul _ _ _) ?_)
    have hp := Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_polyMul_assoc (tailBlocks+1) _ _ _))
      (character_quadratic_boundary tailBlocks hb s i j r)
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hp) ?_
    cases (inferInstance : Decidable (s = 2)) with
    | isTrue he =>
      subst s
      rw [if_pos rfl]
      exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
        (Q'.mul_eqv_congr_right _ _ _ (quadratic_heat_coefficient w))
    | isFalse he =>
      simp only [if_neg he]
      exact Q'.mul_zero_eqv _
  refine Q'.eqv_trans _ _ _ ht ?_
  rw [show K+1 = (K-2)+3 by omega]
  exact sum_spin_two _ (K-2)

private theorem power_positive {w : Q'} (hw : (0 : Q') < w) : ∀ n, (0 : Q') < qpow w n
  | 0 => by change (0 : Q') < 1; decide
  | n+1 => Q'.mul_pos (power_positive hw n) hw

def inverseRate (w : Q') (hw : (0 : Q') < w) : Q' :=
  Q'.recipPos (qpow w 8) (power_positive hw 8)

theorem inverseRate_positive (w : Q') (hw : (0 : Q') < w) : (0 : Q') < inverseRate w hw :=
  Q'.recipPos_pos _ _

def quadraticInverse (w : Q') (hw : (0 : Q') < w) (i j : Fin 4) : RatPoly :=
  polySmul (inverseRate w hw) (quadratic i j)

/-- An actual polynomial preimage for the relative one-link kernel, not for
the interacting OS time transfer. No witness is erased into Prop. -/
theorem quadratic_inverse_transmission (tailBlocks : Nat) (hb : 0 < tailBlocks)
    (w : Q') (hw : (0 : Q') < w) (K : Nat) (hK : 2 ≤ K) (i j : Fin 4) (r : RatPoly) :
    quaternionHaar (tailBlocks+1) (polyMul
      (polyMul (relativeHeat w K) (quadraticInverse w hw i j)) (liftHead r)) ≈
      quaternionHaar tailBlocks (polyMul (quadratic i j) r) := by
  have hscale := ((RatPolyCoeffEqv.polyMul_smul_right (inverseRate w hw) (relativeHeat w K)
    (quadratic i j)).mul_right (liftHead r)).trans (RatPolyCoeffEqv.polyMul_smul_left _ _ _)
  refine Q'.eqv_trans _ _ _ (haar_of_coeff hscale)
    (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul _ _ _) ?_)
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
    (quadratic_heat_transmission tailBlocks hb w K hK i j r)) ?_
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv _ _))) (Q'.one_mul_eqv _))

/-- At cutoff one the SAME full relative kernel annihilates every quadratic
mode, even for positive w. The K >= 2 guard above is substantive. -/
theorem cutoff_one_quadratic_zero (tailBlocks : Nat) (hb : 0 < tailBlocks)
    (w : Q') (i j : Fin 4) (r : RatPoly) :
    quaternionHaar (tailBlocks+1) (polyMul
      (polyMul (relativeHeat w 1) (quadratic i j)) (liftHead r)) ≈ 0 := by
  refine Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_assoc (tailBlocks+1) _ _ _)
    (Q'.eqv_trans _ _ _ (sum_insert (tailBlocks+1) _ _ (List.range 2)) ?_)
  have hz (s : Nat) (hs : s ∈ List.range 2) :
      quaternionHaar (tailBlocks+1) (polyMul
        (polySmul (coeffAt (heatKernelPacket 1 w) s) (relativeCharacter s))
        (polyMul (quadratic i j) (liftHead r))) ≈ 0 := by
    have hne : s ≠ 2 := by have h := List.mem_range.mp hs; omega
    have h := character_quadratic_boundary tailBlocks hb s i j r
    rw [if_neg hne] at h
    exact Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left _ _ _))
      (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul _ _ _)
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
          (Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_polyMul_assoc (tailBlocks+1) _ _ _)) h))
          (Q'.mul_zero_eqv _)))
  exact Q'.add_eqv_congr' (hz 0 (by decide)) (Q'.add_eqv_congr' (hz 1 (by decide)) (Q'.eqv_refl _))

/-- A nonzero original Haar polynomial is lost at K=1; this is not an OS norm. -/
theorem off_diagonal_haar_norm :
    quaternionHaar 1 (polyMul (quadratic 0 1) (quadratic 0 1)) ≈ Q'.mkPos 1 24 (by decide) := by
  decide +kernel

/-- A literal test of the SAME two-link kernel: multiplying the two known
degree-one images gives the wrong image of U_0 U_1. This is ordinary Haar,
not an example asserting failure of any original OS estimate. -/
theorem heat_not_multiplicative :
    ¬ quaternionHaar 2 (polyMul
      (polyMul (relativeHeat HalfPow.half 2) (coordinatePair 0 1)) (liftHead (coordinatePair 0 1))) ≈
      quaternionHaar 1 (polyMul
        (polyMul (polySmul (qpow HalfPow.half 3) (polyVar 0))
          (polySmul (qpow HalfPow.half 3) (polyVar 1))) (coordinatePair 0 1)) := by
  decide +kernel

end YMGap.Continuum.SU2QuaternionQuadraticHeatTransmission

#print axioms YMGap.Continuum.SU2QuaternionQuadraticHeatTransmission.coordinatePair
#print axioms YMGap.Continuum.SU2QuaternionQuadraticHeatTransmission.radius
#print axioms YMGap.Continuum.SU2QuaternionQuadraticHeatTransmission.quarter
#print axioms YMGap.Continuum.SU2QuaternionQuadraticHeatTransmission.third
#print axioms YMGap.Continuum.SU2QuaternionQuadraticHeatTransmission.quadratic
#print axioms YMGap.Continuum.SU2QuaternionQuadraticHeatTransmission.quadratic_degree
#print axioms YMGap.Continuum.SU2QuaternionQuadraticHeatTransmission.quadratic_trace_decomposition
#print axioms YMGap.Continuum.SU2QuaternionQuadraticHeatTransmission.low_spin_partial
#print axioms YMGap.Continuum.SU2QuaternionQuadraticHeatTransmission.high_spin_partial_zero
#print axioms YMGap.Continuum.SU2QuaternionQuadraticHeatTransmission.character_quadratic_boundary
#print axioms YMGap.Continuum.SU2QuaternionQuadraticHeatTransmission.quadratic_heat_coefficient
#print axioms YMGap.Continuum.SU2QuaternionQuadraticHeatTransmission.quadratic_heat_transmission
#print axioms YMGap.Continuum.SU2QuaternionQuadraticHeatTransmission.inverseRate
#print axioms YMGap.Continuum.SU2QuaternionQuadraticHeatTransmission.inverseRate_positive
#print axioms YMGap.Continuum.SU2QuaternionQuadraticHeatTransmission.quadraticInverse
#print axioms YMGap.Continuum.SU2QuaternionQuadraticHeatTransmission.quadratic_inverse_transmission
#print axioms YMGap.Continuum.SU2QuaternionQuadraticHeatTransmission.cutoff_one_quadratic_zero
#print axioms YMGap.Continuum.SU2QuaternionQuadraticHeatTransmission.off_diagonal_haar_norm
#print axioms YMGap.Continuum.SU2QuaternionQuadraticHeatTransmission.heat_not_multiplicative
