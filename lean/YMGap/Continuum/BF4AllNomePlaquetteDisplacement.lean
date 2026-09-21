/-
# Actual completed plaquette displacement with a linear time bound

Embed the literal difference between a face presentation and its physical
advance in the EXISTING fixed-width JointCompletion. Its unit coefficient
vanishes exactly. Its reflected squared norm is at most the Wilson squared
increment: time contraction bounds the advanced diagonal by the original.
Thus strict padding gives `||displacement(n)||² <= 384*n*(1-w)`.

No completed subtraction operation or equality of whole Wilson/face carriers
is assumed. This is a fixed-spacing bound on an actual embedded vector, not
positive-time survival, spatial convergence or a continuum mass gap.
-/
import YMGap.Continuum.BF4AllNomeCompletedPlaquetteIncrement

namespace YMGap.Continuum.BF4AllNomePlaquetteDisplacement

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceCharacter (faceSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime
  (physicalTime physicalTime_zero physicalTime_unit unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointLimits (jointPairing)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette (plaquetteLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonActivePadding (source_edges_active_after_padding)
open YMGap.Continuum.BF4WilsonJointFunctionalLaws (equiv_sub)
open YMGap.Continuum.BF4WilsonAllNomeTimeIncrement
open YMGap.Continuum.BF4WilsonAllNomePlaquetteTimePin

attribute [local irreducible] jointPairing completedInner

private theorem fourTerm_bound {a b c : CReal} (hc : leEv c a) :
    leEv (sub (sub a b) (sub b c)) (mul (ofQ' 2) (sub a b)) := by
  have h := leEv_add (leEv_refl (sub a b)) (leEv_add hc (leEv_refl (neg b)))
  have hleft : Equiv (sub (sub a b) (sub b c)) (add (sub a b) (sub c b)) :=
    SumOfSquares.Equiv_of_approx_eqv (fun k =>
      poly_identity_of_normal_eq
        (.add (.add (.var 0) (.neg (.var 1))) (.neg (.add (.var 1) (.neg (.var 2)))))
        (.add (.add (.var 0) (.neg (.var 1))) (.add (.var 2) (.neg (.var 1))))
        (by decide) (fun | 0 => a.approx k | 1 => b.approx k | _ => c.approx k))
  have hright : Equiv (add (sub a b) (sub a b)) (mul (ofQ' 2) (sub a b)) :=
    SumOfSquares.Equiv_of_approx_eqv (fun k =>
      poly_identity_of_normal_eq (.add (.var 0) (.var 0)) (.mul (.const 2) (.var 0))
        (by decide) (fun _ => (sub a b).approx k))
  exact leEv_trans (leEv_of_equiv hleft) (leEv_trans h (leEv_of_equiv hright))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (width : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width)

local notation "x" => faceSpan width face hf
local notation "J" => jointPairing hw0 hw1 width
local notation "B" => completedInner hw0 hw1 width
local notation "loop" => plaquetteLoop face hf

/-- A literal vector on the existing completion, with no new carrier. -/
def displacementVector (n : Nat) : JointCompletion hw0 hw1 width :=
  jointEmbedSpan hw0 hw1 width (differenceSpan x (physicalTime n x))

/-- The constant/mean direction cancels from the original signed difference. -/
theorem displacement_orthogonal (n : Nat) :
    B (displacementVector hw0 hw1 width face hf n) (jointCompletedUnit hw0 hw1 width) = RCzero := by
  change B (jointEmbedSpan hw0 hw1 width _) (jointEmbedSpan hw0 hw1 width (unit width)) = RCzero
  rw [completedInner_embedSpan]
  apply Quotient.sound
  have ht : Equiv (J (physicalTime n x) (unit width)) (J x (unit width)) := by
    simpa only [physicalTime_unit] using jointPairing_time_balance hw0 hw1 width n x (unit width)
  exact (jointPairing_difference_left hw0 hw1 width x (physicalTime n x) (unit width)).trans
    ((equiv_sub (Equiv.refl _) ht).trans (sub_self_eqv_zero _))

/-- Reflected norm control uses the actual transfer contraction; an ordinary
two-time square is not silently identified with an OS squared norm. -/
theorem displacement_norm_le_increment (n : Nat) :
    RCle (B (displacementVector hw0 hw1 width face hf n)
        (displacementVector hw0 hw1 width face hf n))
      (Quotient.mk crealSetoid (timeIncrement hw0 hw1 loop n)) := by
  change RCle (B (jointEmbedSpan hw0 hw1 width _) (jointEmbedSpan hw0 hw1 width _)) _
  rw [completedInner_embedSpan]
  have hd := jointPairing_difference_diagonal hw0 hw1 width x (physicalTime n x)
  have hs := equiv_sub (Equiv.refl (sub (J x x) (J x (physicalTime n x))))
    (equiv_sub (jointPairing_symm hw0 hw1 width (physicalTime n x) x)
      (Equiv.refl (J (physicalTime n x) (physicalTime n x))))
  have hc := fourTerm_bound (b := J x (physicalTime n x))
    (jointPairing_advance_contraction hw0 hw1 width n x)
  have h0 : Equiv (J x x) (BF4WilsonAllNomeMomentConvexity.lagMoment hw0 hw1 loop 0) := by
    simpa only [physicalTime_zero] using jointPairing_lag hw0 hw1 width face hf 0
  have hp := equiv_sub h0 (jointPairing_lag hw0 hw1 width face hf n)
  have he := (Pivot2.mul_congr_right (A := ofQ' 2) hp).trans (timeIncrement_pin hw0 hw1 loop n).symm
  exact leEv_trans (leEv_of_equiv (hd.trans hs)) (leEv_trans hc (leEv_of_equiv he))

theorem displacement_norm_nonnegative (n : Nat) :
    RCle RCzero (B (displacementVector hw0 hw1 width face hf n)
      (displacementVector hw0 hw1 width face hf n)) :=
  completedInner_nonnegative hw0 hw1 width _

theorem displacement_nome_bound
    (hactive : ∀ e, e ∈ (loop).edges → (baseLinks width).idxOf e.link ∈ activeBlocks width)
    (n : Nat) :
    RCle (B (displacementVector hw0 hw1 width face hf n)
        (displacementVector hw0 hw1 width face hf n))
      (Quotient.mk crealSetoid (ofQ' (384 * Q'.ofNat n * (1 + -w)))) := by
  refine RCle_trans (displacement_norm_le_increment hw0 hw1 width face hf n) ?_
  refine leEv_trans (timeIncrement_nome_bound hw0 hw1 loop hactive n) ?_
  apply leEv_of_equiv
  apply SumOfSquares.Equiv_of_approx_eqv
  intro k
  exact poly_identity_of_normal_eq
    (.mul (.var 0) (.mul (.mul (.const 24) (.mul (.const 4) (.const 4))) (.var 1)))
    (.mul (.mul (.const 384) (.var 0)) (.var 1)) (by decide)
    (fun | 0 => Q'.ofNat n | _ => 1 + -w)

/-- A fixed base plaquette at every strictly larger width, retaining each
width's own original state, completed carrier and time operator. -/
theorem padded_displacement_nome_bound {base : Nat} (hwidth : base < width)
    (hfbase : face ∈ spatialFaces base) (n : Nat) :
    RCle (B (displacementVector hw0 hw1 width face hf n)
        (displacementVector hw0 hw1 width face hf n))
      (Quotient.mk crealSetoid (ofQ' (384 * Q'.ofNat n * (1 + -w)))) := by
  apply displacement_nome_bound hw0 hw1 width face hf ?_ n
  intro e he
  exact source_edges_active_after_padding hwidth (plaquetteLoop face hfbase) e he

end YMGap.Continuum.BF4AllNomePlaquetteDisplacement

#print axioms YMGap.Continuum.BF4AllNomePlaquetteDisplacement.displacementVector
#print axioms YMGap.Continuum.BF4AllNomePlaquetteDisplacement.displacement_orthogonal
#print axioms YMGap.Continuum.BF4AllNomePlaquetteDisplacement.displacement_norm_le_increment
#print axioms YMGap.Continuum.BF4AllNomePlaquetteDisplacement.displacement_norm_nonnegative
#print axioms YMGap.Continuum.BF4AllNomePlaquetteDisplacement.displacement_nome_bound
#print axioms YMGap.Continuum.BF4AllNomePlaquetteDisplacement.padded_displacement_nome_bound
