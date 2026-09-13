/-
# Constructed mixed-pairing limits for ORIGINAL thermodynamic OS sequences

A positive-polynomial size cap on the original action passes to its own
thermodynamic limit. One Cauchy anchor therefore gives a computed norm
ceiling; the same-form continuity estimate constructs the outer pairing
rate. Presented-form QCauchy data supply inner regularity.

This returns an actual CReal and its QCauchy modulus, with no boundedness,
convergence or representative-selection premise. Quotient descent follows
in the completed-inner module. None of these size bounds is a gap estimate.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicPairingContinuity
import YMGap.Constructive.CRealCanonicalReciprocalIndex

namespace YMGap.Continuum.BF4ExactSlabThermodynamicPairingLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicPresentation
open YMGap.Continuum.BF4ExactSlabThermodynamicLowerFunctional
open YMGap.Continuum.BF4ExactSlabThermodynamicLowerAlgebra
open YMGap.Continuum.BF4ExactSlabThermodynamicReflectedForm
open YMGap.Continuum.BF4ExactSlabThermodynamicReflectedObservable
open YMGap.Continuum.BF4ExactSlabThermodynamicReflectedBilinear
open YMGap.Continuum.BF4ExactSlabThermodynamicNullQuotient
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicPairingContinuity
open YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity (pairingTolerance pairingTolerance_pos)
open YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility (enlarge)
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate

private theorem four_bound {A B : CReal} {a b : Q'}
    (hA : leEv A (ofQ' a)) (hB : leEv B (ofQ' b)) :
    leEv (CReal.add (CReal.add A A) (CReal.add B B)) (ofQ' ((a + a) + (b + b))) := by
  have h := leEv_add (leEv_add hA hA) (leEv_add hB hB)
  rw [ofQ'_add, ofQ'_add, ofQ'_add] at h
  exact h

local notation "D" => seminorm

def diagonalCeiling (p : Presentation) : Q' :=
  BF4ExactSlabPlaquetteUniformSquareBound.bound p.expression

theorem diagonalCeiling_nonnegative (p : Presentation) : (0 : Q') ≤ diagonalCeiling p :=
  BF4ExactSlabPlaquetteUniformSquareBound.bound_nonnegative p.expression

theorem diagonal_le_ceiling (p : Presentation) :
    leEv (presentedForm p p) (ofQ' (diagonalCeiling p)) := by
  have hb : leEv (formLimit p.expression p.expression) (ofQ' (diagonalCeiling p)) := by
    apply leEv_of_convergesTo_le (form_converges p.expression p.expression) (convergesTo_const _)
    intro margin
    have h := BF4ExactSlabPlaquetteUniformMomentBound.form_bound nome nome_pos nome_lt_one
      (enlarge margin p.expression)
    have hcap : BF4ExactSlabPlaquetteUniformSquareBound.bound (enlarge margin p.expression) =
        diagonalCeiling p :=
      BF4ExactSlabPlaquetteUniformSquareBound.bound_bulkAtTime margin ⟨0, Nat.zero_lt_succ _⟩ p.expression
    rw [hcap] at h
    exact h
  exact leEv_trans (leEv_of_equiv (presentedForm_sameBase p.expression p.expression)) hb

def normBase (X : (D).Cauchy) : Nat := X.modulus 1

def normCeiling (X : (D).Cauchy) : Q' :=
  (1 + 1) + (diagonalCeiling (X.seq (normBase X)) +
    diagonalCeiling (X.seq (normBase X)))

theorem normCeiling_nonnegative (X : (D).Cauchy) : (0 : Q') ≤ normCeiling X :=
  Q'.zero_le_add _ _ (by decide)
    (Q'.zero_le_add _ _ (diagonalCeiling_nonnegative _) (diagonalCeiling_nonnegative _))

theorem diagonal_anchor_bound (e anchor : Presentation) :
    leEv (presentedForm e e)
      (CReal.add
        (CReal.add (distSq e anchor) (distSq e anchor))
        (CReal.add (presentedForm anchor anchor) (presentedForm anchor anchor))) := by
  have he : qadd (subtract (embed e) (embed anchor)) (embed anchor) = embed e := by
    unfold subtract
    rw [qadd_assoc, neg_add, qadd_comm, zero_add]
  have h := pairing_add_bound (subtract (embed e) (embed anchor)) (embed anchor)
  rw [he] at h
  exact h

theorem diagonal_le_normCeiling (X : (D).Cauchy) (n : Nat) (hn : normBase X ≤ n) :
    leEv (presentedForm (X.seq n) (X.seq n)) (ofQ' (normCeiling X)) := by
  let anchor := X.seq (normBase X)
  have hdist : leEv (distSq (X.seq n) anchor) (ofQ' 1) :=
    X.isCauchy 1 (by decide) n (normBase X) hn (Nat.le_refl _)
  exact leEv_trans (diagonal_anchor_bound (X.seq n) anchor)
    (four_bound hdist (diagonal_le_ceiling anchor))

def pairCeiling (X Y : (D).Cauchy) : Q' := Q'.max' (normCeiling X) (normCeiling Y)

theorem pairCeiling_nonnegative (X Y : (D).Cauchy) : (0 : Q') ≤ pairCeiling X Y :=
  Q'.le_trans' _ _ _ (normCeiling_nonnegative X) (Q'.le_max'_left _ _)

def pairSequence (X Y : (D).Cauchy) (n : Nat) : CReal := presentedForm (X.seq n) (Y.seq n)

def pairDelta (X Y : (D).Cauchy) (epsilon : Q') : Q' :=
  pairingTolerance (pairCeiling X Y) (pairCeiling_nonnegative X Y) epsilon

def rawRate (X Y : (D).Cauchy) (epsilon : Q') : Nat :=
  max (max (normBase X) (normBase Y))
    (max (X.modulus (pairDelta X Y epsilon)) (Y.modulus (pairDelta X Y epsilon)))

theorem pairSequence_raw_bound (X Y : (D).Cauchy) : LeRatBound (pairSequence X Y) (rawRate X Y) := by
  intro epsilon he m n hm hn
  let B := pairCeiling X Y
  let hB := pairCeiling_nonnegative X Y
  let delta := pairDelta X Y epsilon
  have hd : (0 : Q') < delta := pairingTolerance_pos B hB he
  have hXbase : normBase X ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hn
  have hYbase : normBase Y ≤ m :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hm
  have hXm : X.modulus delta ≤ m := Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hm
  have hXn : X.modulus delta ≤ n := Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hn
  have hYm : Y.modulus delta ≤ m := Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hm
  have hYn : Y.modulus delta ≤ n := Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hn
  exact pairing_close (X.seq m) (X.seq n) (Y.seq m) (Y.seq n) B hB epsilon he
    (X.isCauchy delta hd m n hXm hXn) (Y.isCauchy delta hd m n hYm hYn)
    (leRat_mono (diagonal_le_normCeiling Y m hYbase) (Q'.le_max'_right _ _))
    (leRat_mono (diagonal_le_normCeiling X n hXbase) (Q'.le_max'_left _ _))

def pairRate (X Y : (D).Cauchy) : Q' → Nat := closedRate canonicalReciprocalIndexData (rawRate X Y)

theorem pairRate_antitone (X Y : (D).Cauchy) : MmonoPred (pairRate X Y) :=
  closedRate_mmonoPred canonicalReciprocalIndexData (rawRate X Y)

theorem pairSequence_bound (X Y : (D).Cauchy) : LeRatBound (pairSequence X Y) (pairRate X Y) :=
  LeRatBound.closed canonicalReciprocalIndexData (pairSequence_raw_bound X Y)

def pairReg (X Y : (D).Cauchy) (n : Nat) (epsilon : Q') : Nat :=
  (presentedFormCauchy (X.seq n) (Y.seq n)).M epsilon

theorem pairSequence_regular (X Y : (D).Cauchy) : RegPred (pairSequence X Y) (pairReg X Y) :=
  fun n => (presentedFormCauchy (X.seq n) (Y.seq n)).bound

/-- Diagonal limit constructed from explicit outer and inner moduli. -/
def representativeInner (X Y : (D).Cauchy) : CReal :=
  completeLimitFromRate (pairSequence X Y) (pairRate X Y) (pairReg X Y)
    (pairSequence_regular X Y) (pairSequence_bound X Y)

theorem pairSequence_converges (X Y : (D).Cauchy) :
    ConvergesTo (pairSequence X Y) (representativeInner X Y) :=
  convergesTo_completeLimitFromRate _ _ _ (pairSequence_regular X Y)
    (pairSequence_bound X Y) (pairRate_antitone X Y)

private def diagonalCauchy (s : Nat → CReal) (M : Q' → Nat) (reg : Nat → Q' → Nat)
    (hr : RegPred s reg) (hb : LeRatBound s M) :
    QCauchy (completeLimitFromRate s M reg hr hb).approx where
  M := fun epsilon => (HalfPow.half * (HalfPow.half * epsilon)).den
  bound := by
    intro epsilon he i j hi hj
    rcases Nat.le_total i j with hij | hji
    · exact diagSeqR_directed s M reg hr hb epsilon he i j hij hi
    · exact (diagSeqR_directed s M reg hr hb epsilon he j i hji hj).symm

/-- The completed representative itself retains an explicit approximation modulus. -/
def representativeInnerCauchy (X Y : (D).Cauchy) : QCauchy (representativeInner X Y).approx :=
  diagonalCauchy (pairSequence X Y) (pairRate X Y) (pairReg X Y)
    (pairSequence_regular X Y) (pairSequence_bound X Y)

end YMGap.Continuum.BF4ExactSlabThermodynamicPairingLimit

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPairingLimit.diagonalCeiling
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPairingLimit.diagonalCeiling_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPairingLimit.diagonal_le_ceiling
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPairingLimit.normBase
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPairingLimit.normCeiling
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPairingLimit.normCeiling_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPairingLimit.diagonal_anchor_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPairingLimit.diagonal_le_normCeiling
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPairingLimit.pairCeiling
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPairingLimit.pairCeiling_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPairingLimit.pairSequence
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPairingLimit.pairDelta
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPairingLimit.rawRate
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPairingLimit.pairSequence_raw_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPairingLimit.pairRate
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPairingLimit.pairRate_antitone
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPairingLimit.pairSequence_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPairingLimit.pairReg
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPairingLimit.pairSequence_regular
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPairingLimit.representativeInner
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPairingLimit.pairSequence_converges
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPairingLimit.representativeInnerCauchy
