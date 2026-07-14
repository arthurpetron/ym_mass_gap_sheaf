/-
# SU(2) two-mode fidelity fence and corrected ReferenceWeight target

The exact Peter--Weyl block in `SU2PeterWeylWilsonBlock` is a two-boundary
calculation: the kernel is `K(g h^{-1})`, double Haar integration supplies the
Schur factor, and the retained reflected form is `diag(1,1/8)`.  It must not be
identified with the different one-variable reweighting

    E_K(p) = int K(g) p(g) dg.

This file makes that normalization distinction kernel-visible.  Under the
one-variable state the literal characters satisfy

    E_K(chi_0 chi_1) = 1/4,     E_K(chi_1 chi_1) = 1,

whereas the two-boundary Schur block has cross term zero and fundamental norm
`1/8`.  Hence there is no form-preserving map which sends the two retained
modes literally to `chi_0, chi_1` in the one-variable state.  This is not an
objection to the internally consistent double-Haar block; it is a fence
against a false `ReferenceWeight` embedding.

The second fence records why the state-preserving action of
`ReferenceWeightTimeGeometry` cannot itself be the strict `1/8` transfer: an
ambient isometry cannot have an `eighth` eigenvector of nonzero norm.  The
physical transfer must instead be a positive-time compression.

Finally `TwoBoundaryReferenceWeightPositiveTimeRealization` states the minimal
corrected target.  It requires (1) an actual interacting `ReferenceWeight`
Wilson form as the ambient Euclidean form, (2) an explicit two-boundary
reflection whose positive-time compression realizes the exact two-mode block,
and (3) a compressed transfer intertwining the same two modes.  It does not
manufacture an independent two-mode GNS and does not confuse the ambient
invariant action with its positive-time compression.

All calculations are exact rationals, with no proof placeholder,
nonconstructive choice, native evaluator, measured constant, or custom axiom.
-/

import YMGap.Continuum.SU2PeterWeylWilsonBlockCompleted
import YMGap.Continuum.SU2SharedLinkFactorizationObstruction
import YMGap.Continuum.PositiveTimeCompressedTransfer
import YMGap.Continuum.ReferenceWeightTimeGeometry

namespace YMGap.Continuum.SU2PeterWeylReferenceWeightFidelityFence

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.FiniteVolume
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.ObservableMeasure
open YMGap.Continuum.SU2ClassPolynomialAlgebra
open YMGap.Continuum.SU2ClassPolynomialChebUniqueness
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.SU2SharedLinkFactorizationObstruction
open YMGap.Continuum.WilsonGNS

local infix:50 " ≈ " => Q'.eqv

/-! ## Exact one-variable normalization fence -/

/-- The literal vacuum/fundamental cross term of the two-boundary Schur block
is not the corresponding one-variable Wilson moment. -/
theorem oneVariable_cross_mismatch :
    ¬ (wilsonModeGNS.B vacuumMode fundamentalMode ≈
      wilsonMoment (pmul chi0 chi1)) := by
  decide

/-- The literal fundamental norm of the two-boundary Schur block is not the
one-variable Wilson norm of `chi_1`. -/
theorem oneVariable_fundamental_norm_mismatch :
    ¬ (wilsonModeGNS.B fundamentalMode fundamentalMode ≈
      wilsonMoment (pmul chi1 chi1)) := by
  decide

/-- A proposed literal identification of the exact two-boundary mode block
with the one-variable reweighted Haar state.  The `observable` map is allowed
to do anything away from the two basis modes; only the two literal images and
form preservation are requested. -/
structure LiteralOneVariableCharacterEmbedding : Type where
  observable : ModeVec → Poly
  vacuum_literal : observable vacuumMode = chi0
  fundamental_literal : observable fundamentalMode = chi1
  form_preserving : ∀ a b,
    wilsonModeGNS.B a b ≈ wilsonMoment (pmul (observable a) (observable b))

/-- No literal same-form embedding exists.  This refutes only the
one-variable identification; it does not refute the double-Haar
`K(g h^{-1})` construction from which `wilsonModeGNS` was derived. -/
theorem no_literal_oneVariable_character_embedding :
    ¬ Nonempty LiteralOneVariableCharacterEmbedding := by
  intro h
  obtain ⟨E⟩ := h
  apply oneVariable_cross_mismatch
  simpa [E.vacuum_literal, E.fundamental_literal] using
    E.form_preserving vacuumMode fundamentalMode

/-! ## An invariant ambient action is not the strict transfer -/

/-- An isometric ambient time action cannot act by `1/8` on a vector whose
norm is `1/8`.  Thus the state-preserving `ReferenceTranslationAction` in
`ReferenceWeightTimeGeometry` cannot directly be the nontrivial transfer of
the retained fundamental mode; a positive-time compression is essential. -/
theorem ambient_isometry_cannot_be_fundamental_transfer
    (A : PositiveTimeCompressedTransfer.AmbientTimeReflection) (a : A.space.V)
    (hnorm : A.space.B a a ≈ eighth)
    (heigen : A.space.veq (A.tau a) (A.space.smul eighth a)) : False := by
  have hdiag : A.space.B (A.tau a) (A.tau a) ≈
      A.space.B (A.space.smul eighth a) (A.space.smul eighth a) :=
    A.space.B_diag_congr heigen
  have hscale :
      A.space.B (A.space.smul eighth a) (A.space.smul eighth a) ≈
        eighth * (eighth * A.space.B a a) := by
    refine Q'.eqv_trans _ _ _
      (A.space.B_smul_left eighth a (A.space.smul eighth a)) ?_
    exact Q'.mul_eqv_congr_left eighth _ _
      (A.space.B_smul_right eighth a a)
  have hbad : eighth ≈ eighth * (eighth * eighth) := by
    refine Q'.eqv_trans _ (A.space.B a a) _ (Q'.eqv_symm hnorm) ?_
    refine Q'.eqv_trans _ (A.space.B (A.tau a) (A.tau a)) _
      (Q'.eqv_symm (A.tau_isometry a a)) ?_
    refine Q'.eqv_trans _
      (A.space.B (A.space.smul eighth a) (A.space.smul eighth a)) _ hdiag ?_
    exact Q'.eqv_trans _ _ _ hscale
      (Q'.mul_eqv_congr_left eighth _ _
        (Q'.mul_eqv_congr_left eighth _ _ hnorm))
  exact (by decide : ¬ (eighth ≈ eighth * (eighth * eighth))) hbad

/-! ## Minimal corrected two-boundary ReferenceWeight target -/

/-- The actual Wilson GNS datum obtained from a `ReferenceWeight`, named once
so the corrected two-boundary interface below remains readable. -/
abbrev referenceWilsonData
    {A : ObsAlg} (R : ReferenceWeight A) (M : WilsonGNSData.CarrierModule A)
    (elin_congr : ∀ {a b}, M.veq a b → (R.E_Λ a).eqv (R.E_Λ b))
    (elin_add : ∀ a b, (R.E_Λ (M.add a b)).eqv (R.E_Λ a + R.E_Λ b))
    (elin_smul : ∀ (s : Q') (a), (R.E_Λ (M.smul s a)).eqv (s * R.E_Λ a))
    (hconj : ∀ a b,
      (R.E_Λ (A.mul (A.star a) b)).eqv
        (R.E_Λ (A.mul (A.star b) a))) : WilsonGNSData A :=
  WilsonGNSData.ofReferenceWeight R M elin_congr elin_add elin_smul hconj

/-- Minimal fidelity interface for the missing physical bridge.

Here `A` must be the intended two-boundary/double-Haar observable algebra, not
the one-variable polynomial algebra fenced above.  Its ordinary interacting
Wilson form `E_Lambda(a* b)` is embedded into the ambient Euclidean space by
`ambientObservable`/`ambient_reference_form`.  Reflection remains the separate
map `ambient.theta`: `positive_reflected_form` and `reflected_schur_form` say
that reflecting the boundary observable and compressing gives exactly the
retained Schur block.  `compression_intertwines` then identifies the physical
compressed transfer with the exact rational `sameStateTransfer`.

The interface deliberately keeps ambient Euclidean time in
`PositiveTimeCompression.ambient` and the physical transfer in
`PositiveTimeCompression.transfer`; their distinction is forced by
`ambient_isometry_cannot_be_fundamental_transfer`. -/
structure TwoBoundaryReferenceWeightPositiveTimeRealization
    {A : ObsAlg} (R : ReferenceWeight A) (M : WilsonGNSData.CarrierModule A)
    (elin_congr : ∀ {a b}, M.veq a b → (R.E_Λ a).eqv (R.E_Λ b))
    (elin_add : ∀ a b, (R.E_Λ (M.add a b)).eqv (R.E_Λ a + R.E_Λ b))
    (elin_smul : ∀ (s : Q') (a), (R.E_Λ (M.smul s a)).eqv (s * R.E_Λ a))
    (hconj : ∀ a b,
      (R.E_Λ (A.mul (A.star a) b)).eqv
        (R.E_Λ (A.mul (A.star b) a))) : Type 2 where
  ambient : PositiveTimeCompressedTransfer.AmbientTimeReflection
  compression : PositiveTimeCompressedTransfer.PositiveTimeCompression ambient
  ambientObservable : A.carrier → ambient.space.V
  boundaryObservable : ModeVec → A.carrier
  state : ModeVec → compression.positive.V
  vacuum_is_unit : boundaryObservable vacuumMode = A.one
  ambient_reference_form : ∀ x y,
    ambient.space.B (ambientObservable x) (ambientObservable y) ≈
      (referenceWilsonData R M elin_congr elin_add elin_smul hconj).B
        x y
  state_embeds : ∀ a, ambient.space.veq (compression.embed (state a))
    (ambientObservable (boundaryObservable a))
  positive_reflected_form : ∀ a b,
    compression.positive.B (state a) (state b) ≈
      ambient.space.B
        (ambient.theta (ambientObservable (boundaryObservable a)))
        (ambientObservable (boundaryObservable b))
  reflected_schur_form : ∀ a b,
    ambient.space.B
        (ambient.theta (ambientObservable (boundaryObservable a)))
        (ambientObservable (boundaryObservable b)) ≈
      wilsonModeGNS.B a b
  state_map_veq : ∀ {a b}, modeEqv a b →
    compression.positive.veq (state a) (state b)
  state_map_smul : ∀ s a,
    compression.positive.veq (state (modeSmul s a))
      (compression.positive.smul s (state a))
  compression_intertwines : ∀ a,
    compression.positive.veq (compression.transfer (state a))
      (state (sameStateTransfer a))

namespace TwoBoundaryReferenceWeightPositiveTimeRealization

variable
    {A : ObsAlg} {R : ReferenceWeight A} {M : WilsonGNSData.CarrierModule A}
    {elin_congr : ∀ {a b}, M.veq a b → (R.E_Λ a).eqv (R.E_Λ b)}
    {elin_add : ∀ a b, (R.E_Λ (M.add a b)).eqv (R.E_Λ a + R.E_Λ b)}
    {elin_smul : ∀ (s : Q') (a), (R.E_Λ (M.smul s a)).eqv (s * R.E_Λ a)}
    {hconj : ∀ a b,
      (R.E_Λ (A.mul (A.star a) b)).eqv
        (R.E_Λ (A.mul (A.star b) a))}
    (X : TwoBoundaryReferenceWeightPositiveTimeRealization
      R M elin_congr elin_add elin_smul hconj)

/-- Any corrected realization supplies a nonzero vacuum state, derived from
the same interacting Wilson form rather than postulated independently. -/
theorem vacuum_state_form_nonzero :
    ¬ (X.compression.positive.B (X.state vacuumMode) (X.state vacuumMode) ≈ 0) := by
  intro hzero
  have hmode : wilsonModeGNS.B vacuumMode vacuumMode ≈ 0 :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm (X.reflected_schur_form vacuumMode vacuumMode))
      (Q'.eqv_trans _ _ _
        (Q'.eqv_symm (X.positive_reflected_form vacuumMode vacuumMode)) hzero)
  exact (by decide : ¬ (wilsonModeGNS.B vacuumMode vacuumMode ≈ 0)) hmode

/-- Any corrected realization supplies a nonzero fundamental state, again
as a theorem from the common form. -/
theorem fundamental_state_form_nonzero :
    ¬ (X.compression.positive.B (X.state fundamentalMode)
      (X.state fundamentalMode) ≈ 0) := by
  intro hzero
  have hmode : wilsonModeGNS.B fundamentalMode fundamentalMode ≈ 0 :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (X.reflected_schur_form fundamentalMode fundamentalMode))
      (Q'.eqv_trans _ _ _
        (Q'.eqv_symm
          (X.positive_reflected_form fundamentalMode fundamentalMode)) hzero)
  exact (by decide :
    ¬ (wilsonModeGNS.B fundamentalMode fundamentalMode ≈ 0)) hmode

/-- The vacuum is a fixed vector of the *compressed* transfer. -/
theorem compressed_vacuum_eigen :
    X.compression.positive.veq
      (X.compression.transfer (X.state vacuumMode)) (X.state vacuumMode) :=
  X.compression.positive.veq_trans (X.compression_intertwines vacuumMode)
    (X.state_map_veq vacuum_eigen)

/-- The fundamental state has exact eigenvalue `1/8` for the compressed
transfer. -/
theorem compressed_fundamental_eighth_eigen :
    X.compression.positive.veq
      (X.compression.transfer (X.state fundamentalMode))
      (X.compression.positive.smul eighth (X.state fundamentalMode)) :=
  X.compression.positive.veq_trans
    (X.compression_intertwines fundamentalMode)
    (X.compression.positive.veq_trans
      (X.state_map_veq fundamental_eighth_eigen)
      (X.state_map_smul eighth fundamentalMode))

end TwoBoundaryReferenceWeightPositiveTimeRealization

end YMGap.Continuum.SU2PeterWeylReferenceWeightFidelityFence

#print axioms YMGap.Continuum.SU2PeterWeylReferenceWeightFidelityFence.oneVariable_cross_mismatch
#print axioms YMGap.Continuum.SU2PeterWeylReferenceWeightFidelityFence.oneVariable_fundamental_norm_mismatch
#print axioms YMGap.Continuum.SU2PeterWeylReferenceWeightFidelityFence.no_literal_oneVariable_character_embedding
#print axioms YMGap.Continuum.SU2PeterWeylReferenceWeightFidelityFence.ambient_isometry_cannot_be_fundamental_transfer
#print axioms YMGap.Continuum.SU2PeterWeylReferenceWeightFidelityFence.TwoBoundaryReferenceWeightPositiveTimeRealization.vacuum_state_form_nonzero
#print axioms YMGap.Continuum.SU2PeterWeylReferenceWeightFidelityFence.TwoBoundaryReferenceWeightPositiveTimeRealization.fundamental_state_form_nonzero
#print axioms YMGap.Continuum.SU2PeterWeylReferenceWeightFidelityFence.TwoBoundaryReferenceWeightPositiveTimeRealization.compressed_vacuum_eigen
#print axioms YMGap.Continuum.SU2PeterWeylReferenceWeightFidelityFence.TwoBoundaryReferenceWeightPositiveTimeRealization.compressed_fundamental_eighth_eigen
