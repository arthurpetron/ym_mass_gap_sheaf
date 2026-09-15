/-
# ORIGINAL channel packets approximate actual thermodynamic translated norms

At the existing nome 1/1024, the translated presentation, its enlarged
finite slab, the original reciprocal and its actual crossing-channel tree
give a rational sample. Three computed choices control volume error,
crossing truncation and numerical precision. The resulting interval bounds
the norm of the EXISTING completedTime operator applied to the original
dense state, including the actual twoStepTransfer at lag two.

The finite channel index/type and normalization vary with volume. No
persistent thermodynamic coefficient functional, zero transfer kernel,
range-density, physical scaling or continuum/Clay closure follows here.
-/

import YMGap.Continuum.BF4ExactSlabNormalizedChannelReconstruction
import YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponseCertificate

namespace YMGap.Continuum.BF4ExactSlabThermodynamicTranslatedChannelPacket

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra (PlaquetteExpression)
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm (form formCauchy formModulus)
open YMGap.Continuum.BF4ExactSlabWholePacketNormBound
open YMGap.Continuum.BF4ExactSlabNormalizedChannelReconstruction
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate
open YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility (enlarge)
open YMGap.Continuum.BF4ExactSlabThermodynamicPresentation
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeStates
open YMGap.Continuum.BF4ExactSlabThermodynamicReflectedForm
open YMGap.Continuum.BF4ExactSlabThermodynamicReflectedObservable
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime
open YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponseCertificate (two_error_interval)

def normRepresentative (lag : Nat) (p : Presentation) : CReal :=
  formLimit (translate lag p).expression (translate lag p).expression

/-- This is the existing geometric operator and original completed inner product. -/
theorem norm_pin (lag : Nat) (p : Presentation) :
    completedInner (completedTime lag (embedPresentation p)) (completedTime lag (embedPresentation p)) =
      Quotient.mk crealSetoid (normRepresentative lag p) := by
  rw [completedTime_embedPresentation, timeState_pin, completedInner_embedPresentation, pairing_embed]
  exact Quotient.sound (presentedForm_sameBase (translate lag p).expression (translate lag p).expression)

def finiteExpression (lag : Nat) (p : Presentation) (margin : Nat) :
    PlaquetteExpression ((translate lag p).base+margin) :=
  enlarge margin (translate lag p).expression

def packet (lag : Nat) (p : Presentation) (margin N : Nat) : CReal :=
  normalizedPacket nome nome_pos nome_lt_one (finiteExpression lag p margin) N

/-- Rational evaluation of the actual normalized finite channel-square packet. -/
def sample (lag : Nat) (p : Presentation) (margin N index : Nat) : Q' :=
  (packet lag p margin N).approx index

def volumeCutoff (lag : Nat) (p : Presentation) (delta : Q') : Nat :=
  formVolumeModulus (translate lag p).expression (translate lag p).expression delta

def crossingCutoff (lag : Nat) (p : Presentation) (margin : Nat) (delta : Q') : Nat :=
  normalizedCutoff nome nome_pos nome_lt_one (finiteExpression lag p margin) delta

def numericalCutoff (lag : Nat) (p : Presentation) (margin N : Nat) (delta : Q') : Nat :=
  max (normalizedApproxCutoff nome nome_pos nome_lt_one (finiteExpression lag p margin) N delta)
    (formModulus nome nome_pos nome_lt_one (finiteExpression lag p margin) (finiteExpression lag p margin) delta)

/-- Volume, original form regularity and crossing error each cost delta. -/
theorem sample_interval (lag : Nat) (p : Presentation) (delta : Q') (hd : (0 : Q') < delta)
    (margin N index : Nat) (hm : volumeCutoff lag p delta ≤ margin)
    (hN : crossingCutoff lag p margin delta ≤ N)
    (hi : numericalCutoff lag p margin N delta ≤ index) :
    leEv (ofQ' (sample lag p margin N index + -((delta+delta)+delta))) (normRepresentative lag p) ∧
      leEv (normRepresentative lag p) (ofQ' (sample lag p margin N index + ((delta+delta)+delta))) := by
  have hform := two_error_interval
    (formCauchy nome nome_pos nome_lt_one (finiteExpression lag p margin) (finiteExpression lag p margin))
    delta hd (form_error_le (translate lag p).expression (translate lag p).expression delta hd margin hm)
    index (Nat.le_trans (Nat.le_max_right _ _) hi)
  have hpacket := normalizedPacket_form_approx_close nome nome_pos nome_lt_one
    (finiteExpression lag p margin) delta hd N index hN (Nat.le_trans (Nat.le_max_left _ _) hi)
  constructor
  · apply leEv_trans (y := ofQ' ((form nome nome_pos nome_lt_one
      (finiteExpression lag p margin) (finiteExpression lag p margin)).approx index + -(delta+delta))) ?_ hform.1
    apply leEv_ofQ'_of_approx_ge
    intro n
    exact Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (-((delta+delta)+delta)) hpacket.1)
      (Q'.le_of_eqv (RingNormaliser.poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 1)) (.neg (.add (.add (.var 1) (.var 1)) (.var 1))))
        (.add (.var 0) (.neg (.add (.var 1) (.var 1)))) (by decide)
        (fun | 0 => (form nome nome_pos nome_lt_one
          (finiteExpression lag p margin) (finiteExpression lag p margin)).approx index | _ => delta)))
  · apply leEv_trans hform.2
    apply leEv_le_ofQ'_of_approx_le
    intro n
    exact Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (delta+delta) hpacket.2)
      (Q'.le_of_eqv (RingNormaliser.poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 1)) (.add (.var 1) (.var 1)))
        (.add (.var 0) (.add (.add (.var 1) (.var 1)) (.var 1))) (by decide)
        (fun | 0 => sample lag p margin N index | _ => delta)))

def tolerance (epsilon : Q') : Q' := Q'.divPos epsilon 3 (by decide)

theorem tolerance_positive {epsilon : Q'} (he : (0 : Q') < epsilon) :
    (0 : Q') < tolerance epsilon := Q'.divPos_pos _ _ _ he

theorem tolerance_budget (epsilon : Q') :
    Q'.eqv ((tolerance epsilon+tolerance epsilon)+tolerance epsilon) epsilon :=
  Q'.eqv_trans _ _ _
    (RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 0)) (.var 0)) (.mul (.var 0) (.const 3)) (by decide)
      (fun _ => tolerance epsilon)) (Q'.divPos_mul_eqv _ _ _)

private theorem interval_budget (x : CReal) (s delta epsilon : Q')
    (hb : Q'.eqv ((delta+delta)+delta) epsilon)
    (h : leEv (ofQ' (s + -((delta+delta)+delta))) x ∧
      leEv x (ofQ' (s + ((delta+delta)+delta)))) :
    leEv (ofQ' (s + -epsilon)) x ∧ leEv x (ofQ' (s + epsilon)) :=
  ⟨leEv_trans (leEv_ofQ'_of_approx_ge (fun _ => Q'.le_of_eqv
      (Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ (Q'.eqv_symm hb))))) h.1,
    leEv_trans h.2 (leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_of_eqv
      (Q'.add_eqv_congr_left _ _ _ hb)))⟩

/-- Every index is returned as data, with no search or choice on real equality. -/
def approximationCertificate (lag : Nat) (p : Presentation) (epsilon : Q') (he : (0 : Q') < epsilon) :
    Σ' margin : Nat, Σ' N : Nat, Σ' index : Nat,
      leEv (ofQ' (sample lag p margin N index + -epsilon)) (normRepresentative lag p) ∧
        leEv (normRepresentative lag p) (ofQ' (sample lag p margin N index + epsilon)) := by
  let delta := tolerance epsilon
  let margin := volumeCutoff lag p delta
  let N := crossingCutoff lag p margin delta
  let index := numericalCutoff lag p margin N delta
  have h := sample_interval lag p delta (tolerance_positive he) margin N index
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
  exact ⟨margin, N, index, interval_budget (normRepresentative lag p)
    (sample lag p margin N index) delta epsilon (tolerance_budget epsilon) h⟩

def computedSample (lag : Nat) (p : Presentation) (epsilon : Q') : Q' :=
  let delta := tolerance epsilon
  let margin := volumeCutoff lag p delta
  let N := crossingCutoff lag p margin delta
  sample lag p margin N (numericalCutoff lag p margin N delta)

theorem computedSample_interval (lag : Nat) (p : Presentation) (epsilon : Q') (he : (0 : Q') < epsilon) :
    leEv (ofQ' (computedSample lag p epsilon + -epsilon)) (normRepresentative lag p) ∧
      leEv (normRepresentative lag p) (ofQ' (computedSample lag p epsilon + epsilon)) := by
  let delta := tolerance epsilon
  let margin := volumeCutoff lag p delta
  let N := crossingCutoff lag p margin delta
  let index := numericalCutoff lag p margin N delta
  exact interval_budget (normRepresentative lag p) (sample lag p margin N index) delta epsilon
    (tolerance_budget epsilon) (sample_interval lag p delta (tolerance_positive he)
      margin N index (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))

/-- Same-object norm certificate for every dense presentation and integer lag. -/
theorem completedTime_norm_interval (lag : Nat) (p : Presentation) (epsilon : Q') (he : (0 : Q') < epsilon) :
    RCle (Quotient.mk crealSetoid (ofQ' (computedSample lag p epsilon + -epsilon)))
        (completedInner (completedTime lag (embedPresentation p)) (completedTime lag (embedPresentation p))) ∧
      RCle (completedInner (completedTime lag (embedPresentation p)) (completedTime lag (embedPresentation p)))
        (Quotient.mk crealSetoid (ofQ' (computedSample lag p epsilon + epsilon))) := by
  rw [norm_pin]
  exact computedSample_interval lag p epsilon he

theorem twoStepTransfer_norm_interval (p : Presentation) (epsilon : Q') (he : (0 : Q') < epsilon) :
    RCle (Quotient.mk crealSetoid (ofQ' (computedSample 2 p epsilon + -epsilon)))
        (completedInner (twoStepTransfer (embedPresentation p)) (twoStepTransfer (embedPresentation p))) ∧
      RCle (completedInner (twoStepTransfer (embedPresentation p)) (twoStepTransfer (embedPresentation p)))
        (Quotient.mk crealSetoid (ofQ' (computedSample 2 p epsilon + epsilon))) :=
  completedTime_norm_interval 2 p epsilon he

end YMGap.Continuum.BF4ExactSlabThermodynamicTranslatedChannelPacket

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTranslatedChannelPacket.normRepresentative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTranslatedChannelPacket.norm_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTranslatedChannelPacket.finiteExpression
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTranslatedChannelPacket.packet
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTranslatedChannelPacket.sample
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTranslatedChannelPacket.volumeCutoff
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTranslatedChannelPacket.crossingCutoff
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTranslatedChannelPacket.numericalCutoff
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTranslatedChannelPacket.sample_interval
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTranslatedChannelPacket.tolerance
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTranslatedChannelPacket.tolerance_positive
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTranslatedChannelPacket.tolerance_budget
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTranslatedChannelPacket.approximationCertificate
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTranslatedChannelPacket.computedSample
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTranslatedChannelPacket.computedSample_interval
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTranslatedChannelPacket.completedTime_norm_interval
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTranslatedChannelPacket.twoStepTransfer_norm_interval
