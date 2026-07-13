/-
The exact `1/2` positive-time compression, connected to the finite spectral
layer without confusing juxtaposition with operator-spectrum compatibility.

`SpectralGapData` has no field relating `op` to `model`: any transfer operator,
including the identity, can be packaged with the same one-mode model and the
same positive gap margin.  This file first makes that interface fence explicit.

For the repaired rational compression it then supplies the missing constructive
link.  The vacuum and excitation are nonzero, orthogonal, and span the rational
dense carrier; the completed operator fixes the vacuum and sends the nonzero
excitation to exactly `1/2` times itself.  The `SpectralModel` contains only the
excited mode, as required for a connected correlator, while the vacuum
eigenvalue `1` is recorded separately by the compatibility certificate.

All constants and identities are exact over `Q'`.  No spectral conclusion is
inferred from an unlinked `SpectralGapData` package.
-/

import YMGap.Continuum.PositiveTimeCompressedTransferHalf

namespace YMGap.Continuum.PositiveTimeCompressedSpectralGapHalf

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.PositiveTimeCompressedTransfer
open YMGap.Continuum.PositiveTimeCompressedTransferHalf

local infix:50 " ≈ " => Q'.eqv

/-! ## The connected one-excited-mode spectral datum -/

/-- The connected spectral model has one positive-weight excited mode at the
exact transfer eigenvalue `1/2`.  The vacuum is deliberately not listed. -/
def halfExcitedSpectralModel : SpectralModel where
  k := 1
  w := fun _ => 1
  lam := fun _ => halfMode
  w_nonneg := fun _ => by decide
  lam_nonneg := fun _ => Q'.le_of_lt halfMode_pos

/-- The exact excited separator is `1/2 < 1`. -/
def halfExcitedLocatedGap : LocatedSpectralGap halfExcitedSpectralModel where
  sep := halfMode
  sep_lt_one := halfMode_lt_one
  bound := fun _ => Q'.le_refl' halfMode

/-- The separator is strictly positive as well as strictly below the vacuum
eigenvalue.  In particular this avoids the zero-eigenvalue/infinite-energy
artifact of a saturated compression. -/
theorem half_separator_window :
    (0 : Q') < halfExcitedLocatedGap.sep ∧
      halfExcitedLocatedGap.sep < (1 : Q') :=
  ⟨halfMode_pos, halfMode_lt_one⟩

/-- The eigenvalue-gap margin is exactly `1/2`. -/
theorem half_gapMargin_eqv_halfMode :
    halfExcitedLocatedGap.gapMargin ≈ halfMode := by
  decide

/-- Hence the exact finite transfer-eigenvalue mass margin is positive. -/
theorem half_gapMargin_pos :
    (0 : Q') < halfExcitedLocatedGap.gapMargin :=
  halfExcitedLocatedGap.gapMargin_pos

/-! ## The `SpectralGapData` underdetermination fence -/

/-- The current spectral interface accepts the same half-gap model beside an
arbitrary transfer operator.  This constructor is intentionally named
`unlinked`: it does not assert that `op` has the displayed eigenvalue. -/
def unlinkedHalfGapData {D : GNSData} {H : CompleteGNSHilbert D}
    (op : TransferOperator H) : SpectralGapData H where
  op := op
  model := halfExcitedSpectralModel
  gap := halfExcitedLocatedGap

/-- Kernel-visible interface fence: every operator can be repackaged with the
same `1/2` model and positive margin, while its operator field remains exactly
the supplied operator. -/
theorem arbitrary_operator_accepts_unlinked_half_gap
    {D : GNSData} {H : CompleteGNSHilbert D} (op : TransferOperator H) :
    ∃ G : SpectralGapData H,
      G.op = op ∧ G.model = halfExcitedSpectralModel ∧
        G.gap.sep = halfMode :=
  ⟨unlinkedHalfGapData op, rfl, rfl, rfl⟩

/-- The identity operator packaged with the claimed half-gap model. -/
def identityUnlinkedHalfGapData :
    SpectralGapData halfPositivePlane.gnsComplete :=
  unlinkedHalfGapData halfPositivePlane.idTransfer

/-- On the nonzero excited vector the identity package does not realize its
displayed model eigenvalue `1/2`.  Thus a bare `SpectralGapData` cannot by itself
justify an operator mass-gap claim. -/
theorem identity_unlinked_not_excited_eigen :
    identityUnlinkedHalfGapData.op.T
        (embedV halfPositivePlane halfExcitedMode) ≠
      embedV halfPositivePlane
        (halfPositivePlane.smul
          (identityUnlinkedHalfGapData.model.lam 0) halfExcitedMode) := by
  intro h
  apply rationalHalf_completed_nonidentity
  exact Eq.trans rationalHalf_completed_excited_eigen h.symm

/-! ## A sharp dense two-mode compatibility certificate -/

/-- Compatibility missing from `SpectralGapData` for an exact rational
two-mode transfer.  The finite `model` is the connected/excited spectrum, so it
has one entry.  Vacuum information is carried separately.  The rational dense
carrier is required to be spanned by the two representatives; both quotient
classes are nonzero and distinct; and both completed eigen-equations are tied
to `G.op` explicitly.

This certificate is deliberately stronger than a lone eigenvector witness but
does not pretend that the existing completion API already contains a general
constructive spectral theorem. -/
structure DenseTwoModeSpectralCompatibility {D : GNSData}
    (G : SpectralGapData D.gnsComplete) : Type where
  vacuumRep : D.V
  excitedRep : D.V
  operator_vacuum : G.op.vacuum = embedV D vacuumRep
  vacuum_ne_zero : D.qmk vacuumRep ≠ D.qmk D.zero
  excited_ne_zero : D.qmk excitedRep ≠ D.qmk D.zero
  excited_ne_vacuum : D.qmk excitedRep ≠ D.qmk vacuumRep
  vacuum_excited_orthogonal : D.B vacuumRep excitedRep ≈ 0
  connected_model_one_mode : G.model.k = 1
  connected_weight_pos : (0 : Q') < G.model.w 0
  vacuum_eigen : G.op.T (embedV D vacuumRep) = embedV D vacuumRep
  excited_eigen :
    G.op.T (embedV D excitedRep) =
      embedV D (D.smul (G.model.lam 0) excitedRep)
  rational_dense_span : ∀ a : D.V, ∃ alpha beta : Q',
    D.veq a
      (D.add (D.smul alpha vacuumRep) (D.smul beta excitedRep))

/-! ## Exact realization by the repaired compression -/

/-- The repaired compression and its connected model, packaged in the existing
spectral interface.  Its operator/model compatibility is proved separately
below rather than inferred from this definition. -/
def rationalHalfSpectralGapData :
    SpectralGapData halfPositivePlane.gnsComplete :=
  unlinkedHalfGapData rationalHalfTransferOperator

/-- The concrete vacuum class is nonzero. -/
theorem halfVacuum_qmk_ne_zero_qmk :
    halfPositivePlane.qmk halfVacuumMode ≠
      halfPositivePlane.qmk halfPositivePlane.zero := by
  intro h
  have hr : halfPositivePlane.rad halfVacuumMode halfPositivePlane.zero :=
    Quotient.exact h
  have hnot :
      ¬ halfPositivePlane.rad halfVacuumMode halfPositivePlane.zero := by
    unfold GNSData.rad GNSData.sub halfPositivePlane sextupleLine weightedLine
      gnsProduct unitQGNS halfVacuumMode
    decide
  exact hnot hr

/-- The two concrete representatives are orthogonal in the positive-time Gram
form. -/
theorem halfVacuum_excited_orthogonal :
    halfPositivePlane.B halfVacuumMode halfExcitedMode ≈ 0 := by
  change (1 * ((1 : Q') * 0) + 6 * ((0 : Q') * 1)) ≈ 0
  decide

/-- Every rational positive-time representative is exactly a vacuum/excited
linear combination. -/
theorem halfModes_span_dense (a : halfPositivePlane.V) :
    ∃ alpha beta : Q',
      halfPositivePlane.veq a
        (halfPositivePlane.add
          (halfPositivePlane.smul alpha halfVacuumMode)
          (halfPositivePlane.smul beta halfExcitedMode)) := by
  refine ⟨a.1, a.2, ?_⟩
  change
    a.1 ≈ a.1 * 1 + a.2 * 0 ∧
      a.2 ≈ a.1 * 0 + a.2 * 1
  constructor
  · exact Q'.eqv_symm
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.mul_one_eqv a.1) (QPoly.q_mul_zero a.2))
        (QPoly.q_add_zero_eqv a.1))
  · exact Q'.eqv_symm
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (QPoly.q_mul_zero a.1) (Q'.mul_one_eqv a.2))
        (QPoly.q_zero_add_eqv a.2))

/-- The exact operator/model compatibility missing from the base interface.
The vacuum eigenvalue is `1`; the nonzero excited eigenvalue is the model's
exact `1/2`; and these two modes span the rational dense carrier. -/
def rationalHalfDenseTwoModeCompatibility :
    DenseTwoModeSpectralCompatibility rationalHalfSpectralGapData where
  vacuumRep := halfVacuumMode
  excitedRep := halfExcitedMode
  operator_vacuum := rfl
  vacuum_ne_zero := halfVacuum_qmk_ne_zero_qmk
  excited_ne_zero := halfExcited_qmk_ne_zero_qmk
  excited_ne_vacuum := halfExcited_qmk_ne_vacuum_qmk
  vacuum_excited_orthogonal := halfVacuum_excited_orthogonal
  connected_model_one_mode := rfl
  connected_weight_pos := by decide
  vacuum_eigen := rationalHalf_completed_vacuum_eigen
  excited_eigen := rationalHalf_completed_excited_eigen
  rational_dense_span := halfModes_span_dense

/-- The model eigenvalue linked to the concrete nonzero excitation is exactly
`1/2`, strictly between zero and one. -/
theorem rationalHalf_linked_excited_window :
    (0 : Q') < rationalHalfSpectralGapData.model.lam 0 ∧
      rationalHalfSpectralGapData.model.lam 0 < (1 : Q') :=
  ⟨halfMode_pos, halfMode_lt_one⟩

/-- Explicit completed eigenvector linkage, exposed without projection through
the compatibility record. -/
theorem rationalHalf_linked_excited_eigen :
    rationalHalfSpectralGapData.op.T
        (embedV halfPositivePlane halfExcitedMode) =
      embedV halfPositivePlane
        (halfPositivePlane.smul
          (rationalHalfSpectralGapData.model.lam 0) halfExcitedMode) :=
  rationalHalfDenseTwoModeCompatibility.excited_eigen

/-- Explicit vacuum eigenvalue-one linkage. -/
theorem rationalHalf_linked_vacuum_eigen :
    rationalHalfSpectralGapData.op.T
        (embedV halfPositivePlane halfVacuumMode) =
      embedV halfPositivePlane halfVacuumMode :=
  rationalHalfDenseTwoModeCompatibility.vacuum_eigen

/-- The packaged mass margin is exactly `1/2`.  Unlike the generic
`SpectralGapData.massGap_pos`, this package also carries the separate
operator-link certificate above. -/
theorem rationalHalf_massGap_eqv_halfMode :
    rationalHalfSpectralGapData.massGap ≈ halfMode := by
  decide

theorem rationalHalf_massGap_pos :
    (0 : Q') < rationalHalfSpectralGapData.massGap :=
  rationalHalfSpectralGapData.massGap_pos

/-- The connected correlator of the linked excited model has the existing
constructive geometric decay at ratio `1/2`. -/
theorem rationalHalf_connected_decay (n : Nat) :
    corr rationalHalfSpectralGapData.model n ≤
      (corr rationalHalfSpectralGapData.model 0) * halfMode ^ n :=
  rationalHalfSpectralGapData.gap.decay n

end YMGap.Continuum.PositiveTimeCompressedSpectralGapHalf

#print axioms YMGap.Continuum.PositiveTimeCompressedSpectralGapHalf.halfExcitedLocatedGap
#print axioms YMGap.Continuum.PositiveTimeCompressedSpectralGapHalf.arbitrary_operator_accepts_unlinked_half_gap
#print axioms YMGap.Continuum.PositiveTimeCompressedSpectralGapHalf.identity_unlinked_not_excited_eigen
#print axioms YMGap.Continuum.PositiveTimeCompressedSpectralGapHalf.halfModes_span_dense
#print axioms YMGap.Continuum.PositiveTimeCompressedSpectralGapHalf.rationalHalfDenseTwoModeCompatibility
#print axioms YMGap.Continuum.PositiveTimeCompressedSpectralGapHalf.rationalHalf_linked_excited_eigen
#print axioms YMGap.Continuum.PositiveTimeCompressedSpectralGapHalf.rationalHalf_massGap_pos
