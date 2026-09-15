/-
# Whole original crossing packets are bounded by the original OS norm

Increasing the crossing cutoff bounds the ENTIRE retained packet by the
original full-action quadratic form. Bulk cutoff removal and multiplication
by the SAME original partition reciprocal preserve that bound, with constant
one independent of the packet cutoff. No sum of individual coefficient
bounds, replacement law, or positive channel-uniform floor is used.

The final bound-passing rule uses the already constructed dense packet
reconstruction; it constructs no new limit from erased witnesses. Physical
transfer, volume/spacing-uniform gap and continuum/Clay remain open.
-/

import YMGap.Continuum.BF4ExactSlabIntrinsicChannelCompletion

namespace YMGap.Continuum.BF4ExactSlabWholePacketNormBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm
open YMGap.Continuum.BF4ExactSlabOriginalInterfaceCoercivity
open YMGap.Continuum.BF4ExactSlabMixedInterfacePin
open YMGap.Continuum.BF4ExactSlabOriginalActionReciprocal
open YMGap.Continuum.BF4ExactSlabPolynomialExpectation
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabChannelSquareBulkLimit
open YMGap.Continuum.BF4ExactSlabOriginalChannelReconstruction
open YMGap.Continuum.BF4ExactSlabIntrinsicChannelOrder
open YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity
open YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {half : Nat}

local notation "actualTree" N => BF4ExactSlabLocalSquareExpansion.LocalSquareExpansion.tree
  (interfaceExpansion (Q'.le_of_lt hw0) N half)

theorem wholePacket_finite_bound (e : PlaquetteExpression half) (N K : Nat) (hNK : N ≤ K) :
    energySequence w K half (lower e) (actualTree N) ≤ originalQuadratic w K e :=
  Q'.le_trans' _ _ _ (Q'.ge_of_eqv (mixed_energy_pin w w (Q'.le_of_lt hw0) K N e))
    (Q'.le_trans' _ _ _ (mixed_cutoff_mono w w (Q'.le_of_lt hw0) K N K e hNK)
      (Q'.le_of_eqv (mixed_original_diagonal w (Q'.le_of_lt hw0) K e)))

theorem wholePacket_bulk_bound (e : PlaquetteExpression half) (N : Nat) :
    leEv (channelPacket w hw0 hw1 e N)
      (numeratorLimit w hw0 hw1 (boundaryCompleteSlabLinks (centralExtent half)).length (centralExtent half)
        (slabPhysicalFaceEdges (centralExtent half)) (reflectedInsertion e)) := by
  apply leEv_of_ofQ'_limit_le
    (energy_converges w hw0 hw1 half (lower e) (actualTree N)
      (interfaceExpansion (Q'.le_of_lt hw0) N half).weightsNonnegative)
    (numerator_converges w hw0 hw1 _ _ _ (reflectedInsertion e))
  intro epsilon he
  exact ⟨N, fun K hK => Q'.le_trans' _ _ _ (wholePacket_finite_bound w hw0 e N K hK)
    (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt he))⟩

/-- The same original reciprocal normalizes every packet. -/
def normalizedPacket (e : PlaquetteExpression half) (N : Nat) : CReal :=
  CReal.mul (actionReciprocal w hw0 hw1 half) (channelPacket w hw0 hw1 e N)

theorem normalizedPacket_norm_bound (e : PlaquetteExpression half) (N : Nat) :
    leEv (normalizedPacket w hw0 hw1 e N) (form w hw0 hw1 e e) :=
  leEv_trans (leEv_mul_nonneg_left (reciprocal_nonnegative w hw0 hw1 half)
    (wholePacket_bulk_bound w hw0 hw1 e N))
    (leEv_of_equiv ((CRealAlg.cmul_comm _ _).trans (expectation_reflection_eq_upper w e e hw0 hw1)))

theorem normalizedPacket_nonnegative (e : PlaquetteExpression half) (N : Nat) :
    leEv czero (normalizedPacket w hw0 hw1 e N) :=
  leEv_ofQ'_of_approx_ge (fun n => Q'.mul_nonneg _ _
    (Q'.le_of_lt (actionReciprocal_approx_pos w hw0 hw1 half n))
    (energyLimit_nonnegative w hw0 hw1 half (lower e) (actualTree N)
      (interfaceExpansion (Q'.le_of_lt hw0) N half).weightsNonnegative n))

/-- Uniform upper bounds for these actual packets pass to the original
dense OS norm by the existing reconstruction, not an assumed resolution. -/
theorem normalizedPacket_reconstruction_bound (e : PlaquetteExpression half) (B : CReal)
    (h : ∀ N, leEv (normalizedPacket w hw0 hw1 e N) B) : leEv (form w hw0 hw1 e e) B :=
  leEv_trans (leEv_of_equiv ((CRealAlg.cmul_comm _ _).trans
    (expectation_reflection_eq_upper w e e hw0 hw1)).symm)
    (leEv_of_convergesTo_le
      (convergesTo_const_mul (actionReciprocal w hw0 hw1 half) (channelPacket_converges w hw0 hw1 e))
      (convergesTo_const B) h)

end YMGap.Continuum.BF4ExactSlabWholePacketNormBound

#print axioms YMGap.Continuum.BF4ExactSlabWholePacketNormBound.wholePacket_finite_bound
#print axioms YMGap.Continuum.BF4ExactSlabWholePacketNormBound.wholePacket_bulk_bound
#print axioms YMGap.Continuum.BF4ExactSlabWholePacketNormBound.normalizedPacket
#print axioms YMGap.Continuum.BF4ExactSlabWholePacketNormBound.normalizedPacket_norm_bound
#print axioms YMGap.Continuum.BF4ExactSlabWholePacketNormBound.normalizedPacket_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabWholePacketNormBound.normalizedPacket_reconstruction_bound
