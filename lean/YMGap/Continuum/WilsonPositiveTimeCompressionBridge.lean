/-
The actual non-unit two-slice ReferenceWeight in the positive-time compression
interface.

The construction below uses only `halfReferenceWeight 2`, its repaired
tensor-character carrier, and its genuine period-two Wilson swap.  No auxiliary
toy sector is adjoined.  The whole Wilson GNS datum is used as the positive-time
carrier.  The exact one-character identity proves the weighted transfer Gram
law, so this is an inhabitant of `PositiveTimeCompression` whose raw transfer
map is genuinely nonidentity.

There is nevertheless no strict transfer eigenvalue.  The repaired character
equivalence remembers only `a(0)*a(1)`, which the swap fixes.  Consequently the
raw nonidentity is radical-null and the completed compressed transfer is
exactly the identity.  We isolate the minimal honesty law omitted from the
compression interface--the projection must respect ambient carrier
equivalence--and prove that every compression of this equivalence-trivial ambient
time action satisfying that law is quotient-trivial.  Thus a `0 < lambda < 1`
mode cannot be obtained from the present two-slice carrier without adding a
genuinely larger physical character space.

All identities are exact over `Q'`; axiom dependencies are contained in
`{propext, Quot.sound}`.
-/

import YMGap.Continuum.TwoSliceCharacterReflection
import YMGap.Continuum.PositiveTimeCompressedTransfer

namespace YMGap.Continuum.WilsonPositiveTimeCompressionBridge

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.E2ProductFunctional
open YMGap.Continuum.FiniteVolume
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.ObservableMeasure
open YMGap.Continuum.PositiveTimeCompressedTransfer
open YMGap.Continuum.ReferenceWeightTimeGeometry
open YMGap.Continuum.ReferenceWeightTransferConstruction
open YMGap.Continuum.TwoSliceCharacterReflection
open YMGap.Continuum.WilsonGNS

local infix:50 " ≈ " => Q'.eqv

/-- Carrier equivalence implies the GNS radical relation. -/
private theorem radical_of_veq (D : GNSData) {a b : D.V}
    (h : D.veq a b) : D.rad a b := by
  have hsub : D.veq (D.sub a b) (D.sub b b) :=
    D.add_congr h (D.veq_refl (D.neg b))
  exact Q'.eqv_trans _ _ _ (D.B_diag_congr hsub) (D.rad_refl b)

/-! ## The actual interacting Wilson carrier and its ambient time action -/

/-- The Wilson datum constructed from the non-unit `halfReferenceWeight 2` and
the exact tensor-character carrier. -/
abbrev twoSliceWilson : WilsonGNSData (prodAlg (fun _ => realEdge) 2) :=
  twoSliceSwapCharacterGeometry.toWilsonGNSData twoSlice_elin_congr
    twoSlice_elin_add twoSlice_elin_smul twoSlice_hconj

/-- Its actual rational GNS datum. -/
abbrev twoSliceGNS : GNSData := twoSliceWilson.toGNSData

/-- The period-two observable swap as an ambient isometric time action.  For a
two-point time circle the inverse is the same swap; the slice reflection can be
chosen as the identity and still conjugates time to its inverse. -/
def twoSliceAmbientTimeReflection : AmbientTimeReflection where
  space := twoSliceGNS
  tau := swap01
  tauInv := swap01
  theta := id
  tau_map_veq := twoSliceSwapCharacterGeometry.map_veq
  tau_map_add := twoSliceSwapCharacterGeometry.map_add
  tau_map_neg := twoSliceSwapCharacterGeometry.map_neg
  tau_map_smul := twoSliceSwapCharacterGeometry.map_smul
  tau_left_inv := by
    intro a
    rw [swap01_involutive]
    exact twoSliceGNS.veq_refl a
  tau_right_inv := by
    intro a
    rw [swap01_involutive]
    exact twoSliceGNS.veq_refl a
  tau_isometry :=
    twoSliceSwapCharacterGeometry.wilsonForm_translation_invariant
      twoSlice_elin_congr twoSlice_elin_add twoSlice_elin_smul twoSlice_hconj
  theta_involutive := fun a => twoSliceGNS.veq_refl a
  theta_time_inverse := fun a => twoSliceGNS.veq_refl (swap01 a)

/-- Although the raw swap is nonidentity, ambient time is the identity in the
actual tensor-character carrier equivalence. -/
theorem ambient_time_veq_identity (a : twoSliceGNS.V) :
    twoSliceAmbientTimeReflection.space.veq
      (twoSliceAmbientTimeReflection.tau a) a :=
  twoSlice_swap_veq a

/-! ## The actual Wilson positive-time compression -/

/-- The whole interacting Wilson carrier as its own positive-time subspace.
The projection and embedding are identities and the residual is zero.  The
load-bearing transfer Gram law is exactly the previously derived one-character
Wilson identity, not an assumed operator property. -/
def twoSlicePositiveTimeCompression :
    PositiveTimeTransfer twoSliceAmbientTimeReflection where
  positive := twoSliceGNS
  embed := id
  project := id
  transfer := swap01
  residual := fun _ => twoSliceGNS.zero
  embed_form := fun a b => Q'.eqv_refl (twoSliceGNS.B a b)
  reflected_form := fun a b => Q'.eqv_refl (twoSliceGNS.B a b)
  project_embed := fun a => twoSliceGNS.veq_refl a
  transfer_projected_time := fun a => twoSliceGNS.veq_refl (swap01 a)
  transfer_map_veq := twoSliceSwapCharacterGeometry.map_veq
  transfer_map_zero := twoSlice_swap_veq twoSliceGNS.zero
  transfer_map_add := twoSliceSwapCharacterGeometry.map_add
  transfer_map_neg := twoSliceSwapCharacterGeometry.map_neg
  transfer_map_smul := twoSliceSwapCharacterGeometry.map_smul
  compressed_decomposition := by
    intro a
    exact twoSliceGNS.veq_symm (twoSliceGNS.add_zero (swap01 a))
  compressed_orthogonal := by
    intro a
    exact Q'.eqv_trans _ _ _
      (twoSliceGNS.B_symm (swap01 a) twoSliceGNS.zero)
      (twoSliceGNS.B_zero_left (swap01 a))
  modeCount := 1
  coordinate := fun a _ => twoSliceCharacter a
  modeWeight := fun _ => 1
  modeWeight_nonneg := fun _ => by decide
  transfer_weightedGram := by
    intro a b
    refine Q'.eqv_trans _ _ _
      (twoSlice_reflected_form_eqv_product a b) ?_
    change
      (twoSliceCharacter a * twoSliceCharacter b) ≈
        (0 + 1 * (twoSliceCharacter a * twoSliceCharacter b))
    exact Q'.eqv_symm (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left 0
        (1 * (twoSliceCharacter a * twoSliceCharacter b))
        (twoSliceCharacter a * twoSliceCharacter b)
        (Q'.one_mul_eqv (twoSliceCharacter a * twoSliceCharacter b)))
      (QPoly.q_zero_add_eqv (twoSliceCharacter a * twoSliceCharacter b)))

/-- The raw transfer really is nonidentity on Wilson observable
representatives. -/
theorem twoSlice_raw_transfer_nonidentity :
    twoSlicePositiveTimeCompression.transfer ≠ id := by
  intro h
  have hne := twoSlice_swap_raw_nontrivial
  change id ≠ swap01 at hne
  exact hne h.symm

/-- The exact physical identity surviving in the compression: its transfer
form is the one-mode Wilson character product. -/
theorem twoSlice_transfer_form_is_character_product
    (a b : twoSliceGNS.V) :
    twoSliceGNS.B (twoSlicePositiveTimeCompression.transfer a) b ≈
      twoSliceCharacter a * twoSliceCharacter b :=
  twoSlice_reflected_form_eqv_product a b

/-! ## Minimal honest projection law and the quotient-triviality no-go -/

/-- A projection used in a GNS compression must respect the ambient carrier
equivalence.  Without this law a `project` can distinguish representatives of
the same carrier-equivalence class and manufacture spurious compressed
dynamics. -/
structure CarrierCompatibleProjection
    (C : PositiveTimeTransfer twoSliceAmbientTimeReflection) : Type where
  project_map_veq : ∀ {a b},
    twoSliceAmbientTimeReflection.space.veq a b →
      C.positive.veq (C.project a) (C.project b)

/-- Once the projection is carrier-compatible, equivalence-trivial ambient time
forces the representative compressed transfer to be the identity modulo the
positive carrier equivalence. -/
theorem transfer_veq_identity_of_carrierCompatible
    {C : PositiveTimeTransfer twoSliceAmbientTimeReflection}
    (P : CarrierCompatibleProjection C) (a : C.positive.V) :
    C.positive.veq (C.transfer a) a := by
  refine C.positive.veq_trans (C.transfer_projected_time a) ?_
  refine C.positive.veq_trans
    (P.project_map_veq (ambient_time_veq_identity (C.embed a))) ?_
  exact C.project_embed a

/-- Therefore no genuinely strict scalar mode can satisfy the transfer
eigen-equation.  `scalar_separates` is the constructive non-vacuity condition
that multiplication by the proposed eigenvalue actually changes the mode. -/
theorem no_strict_mode_of_carrierCompatible
    {C : PositiveTimeTransfer twoSliceAmbientTimeReflection}
    (P : CarrierCompatibleProjection C) (a : C.positive.V) (lam : Q')
    (scalar_separates :
      ¬ C.positive.veq (C.positive.smul lam a) a)
    (eigen : C.positive.veq (C.transfer a) (C.positive.smul lam a)) : False := by
  apply scalar_separates
  exact C.positive.veq_trans (C.positive.veq_symm eigen)
    (transfer_veq_identity_of_carrierCompatible P a)

/-- The actual identity projection satisfies the missing honesty law. -/
def twoSliceProjectionCarrierCompatible :
    CarrierCompatibleProjection twoSlicePositiveTimeCompression where
  project_map_veq := fun h => h

/-- Hence the actual compressed transfer is already the identity in its
positive carrier equivalence. -/
theorem twoSlice_transfer_veq_identity (a : twoSliceGNS.V) :
    twoSliceGNS.veq (twoSlicePositiveTimeCompression.transfer a) a :=
  transfer_veq_identity_of_carrierCompatible
    twoSliceProjectionCarrierCompatible a

/-! ## Collapse on the completed GNS space -/

/-- A pointwise carrier-equivalence to the identity makes the compressed
operator exactly the identity on every completion class, not only on dense
embeddings. -/
theorem completedTransfer_eq_id_of_transfer_veq
    {A : AmbientTimeReflection} (C : PositiveTimeTransfer A)
    (hT : ∀ a : C.positive.V, C.positive.veq (C.transfer a) a) :
    C.completedTransfer = id := by
  funext x
  refine Quotient.inductionOn x ?_
  intro u
  apply Quotient.sound
  intro eps heps
  refine ⟨0, fun n _ => ?_⟩
  exact Q'.le_trans' _ 0 eps
    (Q'.le_of_eqv (radical_of_veq C.positive (hT (u.seq n))))
    (Q'.le_of_lt heps)

/-- The completed transfer produced from the actual non-unit two-slice Wilson
weight is exactly the identity.  Thus raw nonidentity does not yield a mass
gap or a nontrivial completed transfer. -/
theorem twoSlice_completedTransfer_eq_id :
    twoSlicePositiveTimeCompression.completedTransfer = id :=
  completedTransfer_eq_id_of_transfer_veq
    twoSlicePositiveTimeCompression twoSlice_transfer_veq_identity

/-! ## The actual character mode and failure of a strict eigenvalue -/

/-- The unit-amplitude character observable in the actual Wilson carrier. -/
def twoSliceWilsonCharacterMode : twoSliceGNS.V := characterRep 1

/-- Its Wilson norm is exactly one. -/
theorem twoSliceWilsonCharacterMode_norm_one :
    twoSliceGNS.B twoSliceWilsonCharacterMode twoSliceWilsonCharacterMode ≈ 1 :=
  twoSlice_character_unit_norm

/-- Consequently its radical quotient class is nonzero. -/
theorem twoSliceWilsonCharacterMode_qmk_ne_zero :
    twoSliceGNS.qmk twoSliceWilsonCharacterMode ≠
      twoSliceGNS.qmk twoSliceGNS.zero := by
  intro h
  have hr : twoSliceGNS.rad twoSliceWilsonCharacterMode twoSliceGNS.zero :=
    Quotient.exact h
  have hz : twoSliceGNS.B twoSliceWilsonCharacterMode
      twoSliceWilsonCharacterMode ≈ 0 :=
    (twoSliceGNS.rad_zero_iff twoSliceWilsonCharacterMode).mp hr
  have honezero : (1 : Q') ≈ 0 :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm twoSliceWilsonCharacterMode_norm_one) hz
  exact (by decide : ¬ ((1 : Q') ≈ 0)) honezero

/-- The proposed exact rational eigenvalue lies strictly between zero and the
vacuum eigenvalue. -/
theorem half_strict_window :
    (0 : Q') < Q'.mkPos 1 2 (by decide) ∧
      Q'.mkPos 1 2 (by decide) < (1 : Q') := by
  decide

/-- The exact candidate `1/2` strictly separates the nonzero character mode
from itself under scalar multiplication. -/
theorem half_scaled_characterMode_ne_mode :
    ¬ twoSliceGNS.veq
      (twoSliceGNS.smul (Q'.mkPos 1 2 (by decide))
        twoSliceWilsonCharacterMode)
      twoSliceWilsonCharacterMode := by
  change ¬
    (twoSliceCharacter
      (characterRep
        (Q'.mkPos 1 2 (by decide) *
          twoSliceCharacter (characterRep 1)))).eqv
      (twoSliceCharacter (characterRep 1))
  decide

/-- Therefore the actual Wilson character mode is not an eigenmode at
`lambda = 1/2`; the obstruction follows from quotient-trivial time, not from a
failed numerical estimate. -/
theorem no_half_eigen_on_Wilson_characterMode :
    ¬ twoSliceGNS.veq
      (twoSlicePositiveTimeCompression.transfer twoSliceWilsonCharacterMode)
      (twoSliceGNS.smul (Q'.mkPos 1 2 (by decide))
        twoSliceWilsonCharacterMode) := by
  intro eigen
  exact no_strict_mode_of_carrierCompatible
    twoSliceProjectionCarrierCompatible twoSliceWilsonCharacterMode
    (Q'.mkPos 1 2 (by decide)) half_scaled_characterMode_ne_mode eigen

/-- The raw observable separating identity from swap becomes the same radical
class after time translation.  This pinpoints exactly where the apparent raw
dynamics disappears. -/
theorem raw_swap_nontriviality_is_radical_null :
    twoSliceGNS.qmk
        (twoSlicePositiveTimeCompression.transfer witnessObs) =
      twoSliceGNS.qmk witnessObs := by
  apply Quotient.sound
  exact twoSlice_swap_rad witnessObs

end YMGap.Continuum.WilsonPositiveTimeCompressionBridge

#print axioms YMGap.Continuum.WilsonPositiveTimeCompressionBridge.twoSliceAmbientTimeReflection
#print axioms YMGap.Continuum.WilsonPositiveTimeCompressionBridge.twoSlicePositiveTimeCompression
#print axioms YMGap.Continuum.WilsonPositiveTimeCompressionBridge.twoSlice_raw_transfer_nonidentity
#print axioms YMGap.Continuum.WilsonPositiveTimeCompressionBridge.transfer_veq_identity_of_carrierCompatible
#print axioms YMGap.Continuum.WilsonPositiveTimeCompressionBridge.no_strict_mode_of_carrierCompatible
#print axioms YMGap.Continuum.WilsonPositiveTimeCompressionBridge.twoSlice_completedTransfer_eq_id
#print axioms YMGap.Continuum.WilsonPositiveTimeCompressionBridge.twoSliceWilsonCharacterMode_qmk_ne_zero
#print axioms YMGap.Continuum.WilsonPositiveTimeCompressionBridge.no_half_eigen_on_Wilson_characterMode
#print axioms YMGap.Continuum.WilsonPositiveTimeCompressionBridge.raw_swap_nontriviality_is_radical_null
