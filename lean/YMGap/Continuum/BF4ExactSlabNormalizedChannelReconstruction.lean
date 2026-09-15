/-
# Computed ORIGINAL normalized channel-packet reconstruction

The actual channel squares approximate the SAME original normalized OS
form with explicit crossing and numerical cutoffs. Reflection of the
observable is compared at a common original finite bulk cutoff before
passing to numerical representatives; equivalent reals are not treated
as identical rational streams. Normalization uses the original reciprocal
and its computed finite-volume ceiling.

This is not a volume-uniform estimate: its tolerance depends explicitly
on that reciprocal ceiling. It supplies the finite-volume input to a
volume/time diagonal, not transfer injectivity or a continuum/Clay result.
-/

import YMGap.Continuum.BF4ExactSlabWholePacketNormBound

namespace YMGap.Continuum.BF4ExactSlabNormalizedChannelReconstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabOriginalActionReciprocal
open YMGap.Continuum.BF4ExactSlabOriginalChannelReconstruction
open YMGap.Continuum.BF4ExactSlabWholePacketNormBound
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

private theorem half_chain (a b c epsilon : Q')
    (hab : a ≤ b + HalfPow.half*epsilon) (hbc : b ≤ c + HalfPow.half*epsilon) :
    a ≤ c + epsilon :=
  Q'.le_trans' _ _ _ hab (Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ hbc)
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _)
      (Q'.add_eqv_congr_left _ _ _ (ExpNeg.two_halves epsilon)))))

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {half : Nat}

local notation "blocks" => List.length (boundaryCompleteSlabLinks (centralExtent half))
local notation "faces" => slabPhysicalFaceEdges (centralExtent half)
local notation "originalLimit" e => numeratorLimit w hw0 hw1 blocks (centralExtent half) faces (reflectedInsertion e)
local notation "ceiling" => reciprocalCeiling w hw0 hw1 half

def reflectionApproxCutoff (e : PlaquetteExpression half) (epsilon : Q') : Nat :=
  max (numeratorCutoff w (centralExtent half) faces (reflectedInsertion e) (HalfPow.half*epsilon))
    (numeratorCutoff w (centralExtent half) faces (polyMul (upper e) (lower e)) (HalfPow.half*epsilon))

/-- Literal finite reflection controls the two different original limit streams. -/
theorem reflected_raw_approx_close (e : PlaquetteExpression half)
    (epsilon : Q') (he : (0 : Q') < epsilon) (n : Nat)
    (hn : reflectionApproxCutoff w e epsilon ≤ n) :
    (originalLimit e).approx n ≤ (rawLimit w hw0 hw1 e e).approx n + epsilon ∧
    (rawLimit w hw0 hw1 e e).approx n ≤ (originalLimit e).approx n + epsilon := by
  have hr := numerator_approx_close w hw0 hw1 blocks (centralExtent half) faces
    (reflectedInsertion e) (HalfPow.half*epsilon) (ExpNeg.half_mul_pos epsilon he) n n
    (Nat.le_trans (Nat.le_max_left _ _) hn) (Nat.le_trans (Nat.le_max_left _ _) hn)
  have hu := numerator_approx_close w hw0 hw1 blocks (centralExtent half) faces
    (polyMul (upper e) (lower e)) (HalfPow.half*epsilon) (ExpNeg.half_mul_pos epsilon he) n n
    (Nat.le_trans (Nat.le_max_right _ _) hn) (Nat.le_trans (Nat.le_max_right _ _) hn)
  have hp := reflected_upper_numerator w n e e
  exact ⟨half_chain _ _ _ epsilon hr.2 (Q'.le_trans' _ _ _ (Q'.le_of_eqv hp) hu.1),
    half_chain _ _ _ epsilon hu.2 (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hp) hr.1)⟩

/-- The original partition reciprocal makes this explicitly volume-dependent. -/
def normalizedTolerance (epsilon : Q') : Q' :=
  Q'.divPos epsilon ceiling (reciprocalCeiling_pos w hw0 hw1 half)

theorem normalizedTolerance_positive {epsilon : Q'} (he : (0 : Q') < epsilon) :
    (0 : Q') < normalizedTolerance w hw0 hw1 (half := half) epsilon :=
  Q'.divPos_pos _ _ _ he

theorem normalizedTolerance_budget (epsilon : Q') :
    Q'.eqv (ceiling * normalizedTolerance w hw0 hw1 (half := half) epsilon) epsilon :=
  Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.divPos_mul_eqv _ _ _)

def normalizedCutoff (e : PlaquetteExpression half) (epsilon : Q') : Nat :=
  channelCutoff w e (HalfPow.half * normalizedTolerance w hw0 hw1 (half := half) epsilon)

def normalizedApproxCutoff (e : PlaquetteExpression half) (N : Nat) (epsilon : Q') : Nat :=
  max (channelApproxCutoff w hw0 hw1 e N
    (HalfPow.half * normalizedTolerance w hw0 hw1 (half := half) epsilon))
    (reflectionApproxCutoff w e (HalfPow.half * normalizedTolerance w hw0 hw1 (half := half) epsilon))

private theorem normalized_step (a b lambda B delta epsilon : Q')
    (hl : (0 : Q') ≤ lambda) (hB : lambda ≤ B) (hd : (0 : Q') ≤ delta)
    (hbudget : Q'.eqv (B*delta) epsilon) (hab : a ≤ b+delta) : lambda*a ≤ lambda*b+epsilon :=
  Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hab hl)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_add_eqv _ _ _))
      (Q'.add_le_add_left _ _ _ (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ hB hd) (Q'.le_of_eqv hbudget))))

/-- Computed crossing and representative cutoffs for the ORIGINAL OS norm. -/
theorem normalizedPacket_form_approx_close (e : PlaquetteExpression half)
    (epsilon : Q') (he : (0 : Q') < epsilon) (N n : Nat)
    (hN : normalizedCutoff w hw0 hw1 e epsilon ≤ N)
    (hn : normalizedApproxCutoff w hw0 hw1 e N epsilon ≤ n) :
    (normalizedPacket w hw0 hw1 e N).approx n ≤ (form w hw0 hw1 e e).approx n + epsilon ∧
    (form w hw0 hw1 e e).approx n ≤ (normalizedPacket w hw0 hw1 e N).approx n + epsilon := by
  let delta := normalizedTolerance w hw0 hw1 (half := half) epsilon
  have hd : (0 : Q') < delta := normalizedTolerance_positive w hw0 hw1 he
  have hc := channelPacket_original_approx_close w hw0 hw1 e (HalfPow.half*delta)
    (ExpNeg.half_mul_pos delta hd) N n hN (Nat.le_trans (Nat.le_max_left _ _) hn)
  have hr := reflected_raw_approx_close w hw0 hw1 e (HalfPow.half*delta)
    (ExpNeg.half_mul_pos delta hd) n (Nat.le_trans (Nat.le_max_right _ _) hn)
  have hforward := normalized_step _ _ _ ceiling delta epsilon
    (Q'.le_of_lt (actionReciprocal_approx_pos w hw0 hw1 half n))
    (actionReciprocal_approx_le w hw0 hw1 half n) (Q'.le_of_lt hd)
    (normalizedTolerance_budget w hw0 hw1 epsilon) (half_chain _ _ _ delta hc.1 hr.1)
  have hback := normalized_step _ _ _ ceiling delta epsilon
    (Q'.le_of_lt (actionReciprocal_approx_pos w hw0 hw1 half n))
    (actionReciprocal_approx_le w hw0 hw1 half n) (Q'.le_of_lt hd)
    (normalizedTolerance_budget w hw0 hw1 epsilon) (half_chain _ _ _ delta hr.2 hc.2)
  exact ⟨Q'.le_trans' _ _ _ hforward
      (Q'.le_of_eqv (Q'.add_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _))),
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)) hback⟩

def normalizedReconstructionCertificate (e : PlaquetteExpression half)
    (epsilon : Q') (he : (0 : Q') < epsilon) :
    Σ' N₀ : Nat, Σ' M : Nat → Nat, ∀ N n : Nat, N₀ ≤ N → M N ≤ n →
      ((normalizedPacket w hw0 hw1 e N).approx n ≤ (form w hw0 hw1 e e).approx n + epsilon ∧
       (form w hw0 hw1 e e).approx n ≤ (normalizedPacket w hw0 hw1 e N).approx n + epsilon) :=
  ⟨normalizedCutoff w hw0 hw1 e epsilon, fun N => normalizedApproxCutoff w hw0 hw1 e N epsilon,
    fun N n hN hn => normalizedPacket_form_approx_close w hw0 hw1 e epsilon he N n hN hn⟩

theorem normalizedPacket_converges (e : PlaquetteExpression half) :
    ConvergesTo (normalizedPacket w hw0 hw1 e) (form w hw0 hw1 e e) :=
  fun epsilon he => ⟨normalizedCutoff w hw0 hw1 e epsilon, fun N hN =>
    ⟨normalizedApproxCutoff w hw0 hw1 e N epsilon, fun n hn =>
      normalizedPacket_form_approx_close w hw0 hw1 e epsilon he N n hN hn⟩⟩

end YMGap.Continuum.BF4ExactSlabNormalizedChannelReconstruction

#print axioms YMGap.Continuum.BF4ExactSlabNormalizedChannelReconstruction.reflectionApproxCutoff
#print axioms YMGap.Continuum.BF4ExactSlabNormalizedChannelReconstruction.reflected_raw_approx_close
#print axioms YMGap.Continuum.BF4ExactSlabNormalizedChannelReconstruction.normalizedTolerance
#print axioms YMGap.Continuum.BF4ExactSlabNormalizedChannelReconstruction.normalizedTolerance_positive
#print axioms YMGap.Continuum.BF4ExactSlabNormalizedChannelReconstruction.normalizedTolerance_budget
#print axioms YMGap.Continuum.BF4ExactSlabNormalizedChannelReconstruction.normalizedCutoff
#print axioms YMGap.Continuum.BF4ExactSlabNormalizedChannelReconstruction.normalizedApproxCutoff
#print axioms YMGap.Continuum.BF4ExactSlabNormalizedChannelReconstruction.normalizedPacket_form_approx_close
#print axioms YMGap.Continuum.BF4ExactSlabNormalizedChannelReconstruction.normalizedReconstructionCertificate
#print axioms YMGap.Continuum.BF4ExactSlabNormalizedChannelReconstruction.normalizedPacket_converges
