/-
# SAME original thermodynamic correlations of actual translated states

The completed centered pairing at any two integer lags is identified with
the limit of original finite-slab connected correlations of the literal bulk
placements. The common padding is computed as max(s,t). The existing boundary
error and Cauchy moduli are retained, including dependence on both lags and
the observable support. No alternative probability law or matrix is inserted.

Symmetry, positivity and sharp Cauchy--Schwarz hold for this two-time family.
They do not say that its value depends only on s+t, or that an operator has
these moments. Time homogeneity, OS-null descent and a strict physical gap
are still open. The geometric rate below is a boundary-error rate, not decay
in time separation. Nome 1/1024 and lattice spacing remain fixed.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicTimeStates

namespace YMGap.Continuum.BF4ExactSlabThermodynamicTimeCorrelations

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra (PlaquetteExpression)
open YMGap.Continuum.BF4ExactSlabPlaquetteBulkEmbedding (bulkAtTime)
open YMGap.Continuum.BF4ExactSlabThermodynamicPresentation
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeStates
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicConnectedCovariance
open YMGap.Continuum.BF4ExactSlabThermodynamicCovarianceRate
open YMGap.Continuum.BF4ExactSlabCharacterThermodynamicLimit (rate)
open YMGap.Continuum.BF4ExactSlabExpressionExpectationDecay (boxSize)

def timeCovariance (s t : Nat) (p q : Presentation) : RC :=
  completedInner (centeredTimeState s p).val (centeredTimeState t q).val

def timeCovarianceRepresentative (s t : Nat) (p q : Presentation) :
    Σ' r : CReal, QCauchy r.approx ×' (timeCovariance s t p q = Quotient.mk crealSetoid r) :=
  centeredPairingRepresentative (translate s p) (translate t q)

theorem timeCovariance_symm (s t : Nat) (p q : Presentation) :
    timeCovariance s t p q = timeCovariance t s q p := completedInner_symm _ _

theorem timeCovariance_nonnegative (s : Nat) (p : Presentation) :
    RCle RCzero (timeCovariance s s p p) := completedInner_nonnegative _

theorem timeCovariance_cauchySchwarz (s t : Nat) (p q : Presentation) :
    RCle (RCmul (timeCovariance s t p q) (timeCovariance s t p q))
      (RCmul (timeCovariance s s p p) (timeCovariance t t q q)) :=
  completedInner_cauchySchwarz _ _

theorem timeCovariance_comp_left (s u t : Nat) (p q : Presentation) :
    timeCovariance u t (translate s p) q = timeCovariance (s+u) t p q := by
  unfold timeCovariance
  rw [centeredTimeState_comp]

/-- Every common padding realizes the SAME two-time completed covariance. -/
theorem timeCovariance_bulk {base : Nat} (padding : Nat) (s t : Fin (padding+1))
    (e f : PlaquetteExpression base) :
    timeCovariance s.val t.val ⟨base,e⟩ ⟨base,f⟩ =
      Quotient.mk crealSetoid (covarianceLimit (bulkAtTime padding s e) (bulkAtTime padding t f)) := by
  have h := centered_inner_sameBase (bulkAtTime padding s e) (bulkAtTime padding t f)
  rw [timeState_bulk padding s e, timeState_bulk padding t f] at h
  exact h

theorem timeCovarianceRepresentative_bulk {base : Nat} (padding : Nat) (s t : Fin (padding+1))
    (e f : PlaquetteExpression base) :
    Equiv (timeCovarianceRepresentative s.val t.val ⟨base,e⟩ ⟨base,f⟩).1
      (covarianceLimit (bulkAtTime padding s e) (bulkAtTime padding t f)) :=
  Quotient.exact ((timeCovarianceRepresentative s.val t.val ⟨base,e⟩ ⟨base,f⟩).2.2.symm.trans
    (timeCovariance_bulk padding s t e f))

theorem timeCovariance_bulk_error {base : Nat} (padding : Nat) (s t : Fin (padding+1))
    (e f : PlaquetteExpression base) (margin : Nat) :
    leEv (CReal.abs (CReal.sub (timeCovarianceRepresentative s.val t.val ⟨base,e⟩ ⟨base,f⟩).1
      (covarianceSequence (bulkAtTime padding s e) (bulkAtTime padding t f) margin)))
      (ofQ' (covarianceAmplitude (bulkAtTime padding s e) (bulkAtTime padding t f) *
        rate^(margin+1-boxSize (base+padding)))) :=
  leEv_trans (leEv_of_equiv (abs_equiv_congr
    (CReal.sub_congr_left (timeCovarianceRepresentative_bulk padding s t e f))))
    (covariance_geometric_bound (bulkAtTime padding s e) (bulkAtTime padding t f) margin)

/-- The finite-volume sequence uses the original law on one computed common slab. -/
def timeCovarianceSequence {base : Nat} (s t : Nat) (e f : PlaquetteExpression base) : Nat → CReal :=
  covarianceSequence
    (bulkAtTime (max s t) ⟨s, Nat.lt_succ_of_le (Nat.le_max_left _ _)⟩ e)
    (bulkAtTime (max s t) ⟨t, Nat.lt_succ_of_le (Nat.le_max_right _ _)⟩ f)

def timeCovarianceVolumeModulus {base : Nat} (s t : Nat) (e f : PlaquetteExpression base) : Q' → Nat :=
  covarianceVolumeModulus
    (bulkAtTime (max s t) ⟨s, Nat.lt_succ_of_le (Nat.le_max_left _ _)⟩ e)
    (bulkAtTime (max s t) ⟨t, Nat.lt_succ_of_le (Nat.le_max_right _ _)⟩ f)

theorem timeCovariance_converges {base : Nat} (s t : Nat) (e f : PlaquetteExpression base) :
    ConvergesTo (timeCovarianceSequence s t e f)
      (timeCovarianceRepresentative s t ⟨base,e⟩ ⟨base,f⟩).1 :=
  convergesTo_limit_congr (covariance_converges _ _)
    (timeCovarianceRepresentative_bulk (max s t)
      ⟨s, Nat.lt_succ_of_le (Nat.le_max_left _ _)⟩
      ⟨t, Nat.lt_succ_of_le (Nat.le_max_right _ _)⟩ e f).symm

/-- Computable original volume-error modulus; it names and retains both time lags. -/
theorem timeCovariance_error_le {base : Nat} (s t : Nat) (e f : PlaquetteExpression base)
    (epsilon : Q') (he : (0 : Q') < epsilon) (margin : Nat)
    (hm : timeCovarianceVolumeModulus s t e f epsilon ≤ margin) :
    leEv (CReal.abs (CReal.sub (timeCovarianceRepresentative s t ⟨base,e⟩ ⟨base,f⟩).1
      (timeCovarianceSequence s t e f margin))) (ofQ' epsilon) :=
  leEv_trans (leEv_of_equiv (abs_equiv_congr
    (CReal.sub_congr_left (timeCovarianceRepresentative_bulk (max s t)
      ⟨s, Nat.lt_succ_of_le (Nat.le_max_left _ _)⟩
      ⟨t, Nat.lt_succ_of_le (Nat.le_max_right _ _)⟩ e f))))
    (covariance_error_le _ _ epsilon he margin hm)

end YMGap.Continuum.BF4ExactSlabThermodynamicTimeCorrelations

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeCorrelations.timeCovariance
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeCorrelations.timeCovarianceRepresentative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeCorrelations.timeCovariance_symm
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeCorrelations.timeCovariance_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeCorrelations.timeCovariance_cauchySchwarz
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeCorrelations.timeCovariance_comp_left
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeCorrelations.timeCovariance_bulk
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeCorrelations.timeCovarianceRepresentative_bulk
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeCorrelations.timeCovariance_bulk_error
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeCorrelations.timeCovarianceSequence
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeCorrelations.timeCovarianceVolumeModulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeCorrelations.timeCovariance_converges
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeCorrelations.timeCovariance_error_le
