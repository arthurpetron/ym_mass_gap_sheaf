/-
# Exact relative heat transmission at every cutoff containing spin one

Sum ALL original packet coefficients. Orthogonality proves that the
fundamental coordinate is transmitted by w^3, with an arbitrary retained
boundary polynomial. No small-nome premise or discarded-spin estimate is
used. This is the two-link kernel, not the full plaquette background and
not a spectral bound for an interacting lattice theory.
-/

import YMGap.Continuum.SU2QuaternionRelativeCharacterSelection

namespace YMGap.Continuum.SU2QuaternionRelativeHeatTransmission

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionRelativeCharacterSelection
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2CharacterVacuumHaar

local infix:50 " ≈ " => Q'.eqv

/-- The original packet, including spin zero and every spin through K. -/
def relativeHeat (w : Q') (K : Nat) : RatPoly :=
  finitePolySum (fun spin => polySmul (coeffAt (heatKernelPacket K w) spin)
    (relativeCharacter spin)) (List.range (K+1))

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

private theorem sum_fundamental (value : Q') : ∀ k,
    listQSum (fun s => if s = 1 then value else 0) (List.range (k+2)) ≈ value
  | 0 => by
    change (0 : Q') + (value + 0) ≈ value
    rw [Q'.zero_add', Q'.add_zero']
    exact Q'.eqv_refl _
  | k+1 => by
    rw [show k+1+2 = (k+2)+1 by omega, List.range_succ]
    refine Q'.eqv_trans _ _ _ (sum_append _ _ _) ?_
    have hz : listQSum (fun s => if s = 1 then value else 0) [k+2] ≈ 0 := by
      simp only [listQSum, if_neg (show k+2 ≠ 1 by omega), Q'.add_zero']
      exact Q'.eqv_refl _
    exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (sum_fundamental value k) hz)
      (Q'.eqv_of_eq (Q'.add_zero' _))

theorem fundamental_heat_coefficient (w : Q') : coeffW w 1 * HalfPow.half ≈ qpow w 3 := by
  change (2 * qpow w 3) * HalfPow.half ≈ qpow w 3
  exact Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv _ _))
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (show (2 : Q') * HalfPow.half ≈ 1 by decide))
          (Q'.one_mul_eqv _))))

/-- Same two-link ordinary heat kernel, all K >= 1, every rational nome,
all carrier sizes retaining V, and an arbitrary polynomial boundary. -/
theorem coordinate_transmission (tailBlocks : Nat) (hb : 0 < tailBlocks)
    (w : Q') (K : Nat) (hK : 1 ≤ K) (i : Fin 4) (boundary : RatPoly) :
    quaternionHaar (tailBlocks+1) (polyMul
      (polyMul (relativeHeat w K) (polyVar i.val)) (liftHead boundary)) ≈
      qpow w 3 * quaternionHaar tailBlocks (polyMul (polyVar i.val) boundary) := by
  let value := quaternionHaar tailBlocks (polyMul (polyVar i.val) boundary)
  have hs := sum_insert (tailBlocks+1)
    (fun s => polySmul (coeffAt (heatKernelPacket K w) s) (relativeCharacter s))
    (polyMul (polyVar i.val) (liftHead boundary)) (List.range (K+1))
  refine Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_assoc (tailBlocks+1) _ _ _)
    (Q'.eqv_trans _ _ _ hs ?_)
  have ht : listQSum (fun s => quaternionHaar (tailBlocks+1) (polyMul
      (polySmul (coeffAt (heatKernelPacket K w) s) (relativeCharacter s))
      (polyMul (polyVar i.val) (liftHead boundary)))) (List.range (K+1)) ≈
      listQSum (fun s => if s = 1 then qpow w 3 * value else 0) (List.range (K+1)) := by
    apply sum_congr
    intro s hmem
    rw [coeffAt_heatKernelPacket (List.mem_range.mp hmem)]
    refine Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left _ _ _))
      (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul _ _ _) ?_)
    have hp := Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_polyMul_assoc (tailBlocks+1) _ _ _))
      (character_coordinate_boundary tailBlocks hb s i boundary)
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hp) ?_
    by_cases he : s = 1
    · subst s
      rw [if_pos rfl]
      exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
        (Q'.mul_eqv_congr_right _ _ _ (fundamental_heat_coefficient w))
    · simp only [if_neg he]
      exact Q'.mul_zero_eqv _
  refine Q'.eqv_trans _ _ _ ht ?_
  have hn : K+1 = (K-1)+2 := by omega
  rw [hn]
  exact sum_fundamental _ (K-1)

end YMGap.Continuum.SU2QuaternionRelativeHeatTransmission

#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatTransmission.relativeHeat
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatTransmission.fundamental_heat_coefficient
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatTransmission.coordinate_transmission
