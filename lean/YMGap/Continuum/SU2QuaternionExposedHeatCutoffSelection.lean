/-
# Exact cutoff saturation of an original four-link heat insertion

The actual all-spin four-link character has a homogeneous harmonic solid
representative. Against a fixed polynomial multiplier, every spin above its
explicit head-degree bound has EXACTLY zero original 116-link Haar value.
Consequently the actual heat-packet pairing stabilizes at that bound, for
every rational heat parameter and all sixteen orientations. Its cutoff
limit is the explicitly computed rational value at the bound.

Scope: one exposed four-link heat insertion with a FIXED multiplier. The
full slab also changes its other face heat factors and boundary carrier as
the cutoff grows. No stabilization of that changing family, physical time,
strict gap, thermodynamic or continuum limit is asserted here.
-/

import YMGap.Continuum.SU2QuaternionHarmonicDegreeSelection
import YMGap.Continuum.SU2QuaternionSolidZonalGaussianTransport
import YMGap.Continuum.BF4ExactSlabReflectedSquareHaarForm

namespace YMGap.Continuum.SU2QuaternionExposedHeatCutoffSelection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonic
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHarmonicDegreeSelection
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.BondMovingStep

local infix:50 " ≈ " => Q'.eqv

/-- A computable bound, including short exponent lists and zero terms. -/
def headDegreeBound : RatPoly → Nat
  | [] => 0
  | t :: p => max (quaternionBlockDegree t.1 0) (headDegreeBound p)

theorem headDegreeBound_spec : ∀ p : RatPoly, ∀ term, term ∈ p →
    quaternionBlockDegree term.1 0 ≤ headDegreeBound p
  | [], _, h => False.elim (List.not_mem_nil h)
  | t :: p, term, h => by
    rcases List.mem_cons.mp h with rfl | ht
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (headDegreeBound_spec p term ht) (Nat.le_max_right _ _)

/-- The solid four-link mode vanishes before ANY tail coefficient is lost. -/
theorem exposedSolid_partialHaar_zero (r0 r1 r2 r3 : Bool) (spin : Nat) (p : RatPoly)
    (hs : headDegreeBound p < spin) :
    RatPolyCoeffEqv (partialHaarHead (polyMul
      (exposedSolidZonalCharacter r0 r1 r2 r3 spin) p)) polyZero :=
  partialHaarHead_harmonic_degree_bound
    (exposedSolidZonalCharacter_blockDegree r0 r1 r2 r3 0 (by decide) spin)
    (laplacian_exposedSolidZonalCharacter_zero r0 r1 r2 r3 spin) p
    (fun term ht => Nat.lt_of_le_of_lt (headDegreeBound_spec p term ht) hs)

private theorem haar_weighted (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks p = ratWeightedSum (quaternionHaarMono blocks) p
  | [] => rfl
  | _ :: p => by simp only [quaternionHaar, ratWeightedSum, haar_weighted blocks p]

/-- ORIGINAL character, not just its harmonic representative, on the SAME
116-link Haar carrier, with the entire multiplier retained. -/
theorem exposedCharacter_haar_zero (r0 r1 r2 r3 : Bool) (spin : Nat) (p : RatPoly)
    (hs : headDegreeBound p < spin) :
    quaternionHaar 116 (polyMul
      (characterPolynomial (exposedFourWord r0 r1 r2 r3).scalar spin) p) ≈ 0 := by
  let solid := exposedSolidZonalCharacter r0 r1 r2 r3 spin
  let ordinary := characterPolynomial (exposedFourWord r0 r1 r2 r3).scalar spin
  have hz : quaternionHaar 115 (partialHaarHead (polyMul solid p)) ≈ 0 := by
    rw [haar_weighted]
    exact exposedSolid_partialHaar_zero r0 r1 r2 r3 spin p hs (quaternionHaarMono 115)
  have hc := exposedSolidZonalCharacter_eq_character_116 r0 r1 r2 r3 spin p
  exact Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_comm 116 ordinary p)
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm hc)
      (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_comm 116 p solid)
        (Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_partialHaarHead 115 _)) hz)))

def exposedHeatPolynomial (r0 r1 r2 r3 : Bool) (w : Q') (K : Nat) : RatPoly :=
  finitePolySum (fun spin => polySmul (coeffAt (heatKernelPacket K w) spin)
    (characterPolynomial (exposedFourWord r0 r1 r2 r3).scalar spin)) (List.range (K + 1))

def exposedHeatPairing (r0 r1 r2 r3 : Bool) (w : Q') (K : Nat) (p : RatPoly) : Q' :=
  quaternionHaar 116 (polyMul (exposedHeatPolynomial r0 r1 r2 r3 w K) p)

private theorem sum_insert {A : Type} (f : A → RatPoly) (p : RatPoly) : ∀ xs : List A,
    quaternionHaar 116 (polyMul (finitePolySum f xs) p) ≈
      listQSum (fun a => quaternionHaar 116 (polyMul (f a) p)) xs
  | [] => Q'.eqv_refl _
  | a :: xs => by
    change quaternionHaar 116 (polyMul (polyAdd (f a) (finitePolySum f xs)) p) ≈ _
    rw [polyMul_add_left_exact]
    exact Q'.eqv_trans _ _ _ (quaternionHaar_append 116 _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (sum_insert f p xs))

private theorem sum_congr {A : Type} (f g : A → Q') : ∀ xs : List A,
    (∀ a, a ∈ xs → f a ≈ g a) → listQSum f xs ≈ listQSum g xs
  | [], _ => Q'.eqv_refl _
  | a :: xs, h => Q'.add_eqv_congr' (h a List.mem_cons_self)
      (sum_congr f g xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

theorem exposedHeatPairing_sum (r0 r1 r2 r3 : Bool) (w : Q') (K : Nat) (p : RatPoly) :
    exposedHeatPairing r0 r1 r2 r3 w K p ≈
      listQSum (fun spin => coeffW w spin * quaternionHaar 116 (polyMul
        (characterPolynomial (exposedFourWord r0 r1 r2 r3).scalar spin) p)) (List.range (K + 1)) := by
  refine Q'.eqv_trans _ _ _ (sum_insert _ p _) ?_
  apply sum_congr
  intro spin hs
  rw [coeffAt_heatKernelPacket (List.mem_range.mp hs)]
  refine Q'.eqv_trans _ _ _ ?_ (quaternionHaar_polySmul 116 (coeffW w spin) _)
  rw [haar_weighted, haar_weighted]
  exact RatPolyCoeffEqv.polyMul_smul_left _ _ _ (quaternionHaarMono 116)

private theorem sum_append {A : Type} (f : A → Q') : ∀ xs ys : List A,
    listQSum f (xs ++ ys) ≈ listQSum f xs + listQSum f ys
  | [], _ => Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' _))
  | _ :: xs, ys => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (sum_append f xs ys)) (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))

private theorem sum_stable (f : Nat → Q') (N : Nat) (hz : ∀ j, N < j → f j ≈ 0) :
    ∀ extra, listQSum f (List.range (N + 1 + extra)) ≈ listQSum f (List.range (N + 1))
  | 0 => Q'.eqv_refl _
  | extra + 1 => by
    rw [Nat.add_succ, List.range_succ]
    refine Q'.eqv_trans _ _ _ (sum_append f _ _) ?_
    have ht : listQSum f [N + 1 + extra] ≈ 0 := Q'.eqv_trans _ _ _
      (Q'.eqv_of_eq (Q'.add_zero' _)) (hz _ (by omega))
    exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (sum_stable f N hz extra) ht)
      (Q'.eqv_of_eq (Q'.add_zero' _))

/-- An exact, parameter-independent saturation index for this FIXED
polynomial pairing. This is not a uniform spectral bound. -/
theorem exposedHeatPairing_stable (r0 r1 r2 r3 : Bool) (w : Q') (K : Nat) (p : RatPoly)
    (hK : headDegreeBound p ≤ K) :
    exposedHeatPairing r0 r1 r2 r3 w K p ≈
      exposedHeatPairing r0 r1 r2 r3 w (headDegreeBound p) p := by
  have hs := sum_stable
    (fun spin => coeffW w spin * quaternionHaar 116 (polyMul
      (characterPolynomial (exposedFourWord r0 r1 r2 r3).scalar spin) p)) (headDegreeBound p)
    (fun spin hspin => Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
      (exposedCharacter_haar_zero r0 r1 r2 r3 spin p hspin)) (Q'.mul_zero_eqv _))
    (K - headDegreeBound p)
  have hindex : headDegreeBound p + 1 + (K - headDegreeBound p) = K + 1 := by omega
  rw [hindex] at hs
  exact Q'.eqv_trans _ _ _ (exposedHeatPairing_sum r0 r1 r2 r3 w K p)
    (Q'.eqv_trans _ _ _ hs (Q'.eqv_symm (exposedHeatPairing_sum r0 r1 r2 r3 w (headDegreeBound p) p)))

/-- The limit is a specified rational value embedded into CReal. The
computable headDegreeBound is its exact stabilization modulus. -/
def exposedHeatPairingLimit (r0 r1 r2 r3 : Bool) (w : Q') (p : RatPoly) : CReal :=
  CReal.ofQ' (exposedHeatPairing r0 r1 r2 r3 w (headDegreeBound p) p)

theorem exposedHeatPairingLimit_exact (r0 r1 r2 r3 : Bool) (w : Q') (K : Nat) (p : RatPoly)
    (hK : headDegreeBound p ≤ K) (precision : Nat) :
    exposedHeatPairing r0 r1 r2 r3 w K p ≈ (exposedHeatPairingLimit r0 r1 r2 r3 w p).approx precision :=
  exposedHeatPairing_stable r0 r1 r2 r3 w K p hK

end YMGap.Continuum.SU2QuaternionExposedHeatCutoffSelection

#print axioms YMGap.Continuum.SU2QuaternionExposedHeatCutoffSelection.headDegreeBound
#print axioms YMGap.Continuum.SU2QuaternionExposedHeatCutoffSelection.headDegreeBound_spec
#print axioms YMGap.Continuum.SU2QuaternionExposedHeatCutoffSelection.exposedSolid_partialHaar_zero
#print axioms YMGap.Continuum.SU2QuaternionExposedHeatCutoffSelection.exposedCharacter_haar_zero
#print axioms YMGap.Continuum.SU2QuaternionExposedHeatCutoffSelection.exposedHeatPolynomial
#print axioms YMGap.Continuum.SU2QuaternionExposedHeatCutoffSelection.exposedHeatPairing
#print axioms YMGap.Continuum.SU2QuaternionExposedHeatCutoffSelection.exposedHeatPairing_sum
#print axioms YMGap.Continuum.SU2QuaternionExposedHeatCutoffSelection.exposedHeatPairing_stable
#print axioms YMGap.Continuum.SU2QuaternionExposedHeatCutoffSelection.exposedHeatPairingLimit
#print axioms YMGap.Continuum.SU2QuaternionExposedHeatCutoffSelection.exposedHeatPairingLimit_exact
