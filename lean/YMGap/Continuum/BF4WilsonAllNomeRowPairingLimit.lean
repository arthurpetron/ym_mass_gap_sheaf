/-
# Pairing convergence for represented rows on the original all-nome carrier

The generic diagonal construction retains a rational norm ceiling for each
supplied representative. Actual completed-distance convergence and completed
pairing continuity yield a computed two-slot modulus. Uniform row norm bounds
pass to the same represented limit, without selecting quotient representatives.
-/

import YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity
import YMGap.Continuum.BF4WilsonAllNomeCauchyRows
import YMGap.Continuum.RationalScalarTwoSidedError

namespace YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeCauchyRows
open YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity (pairing_close)
open YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity
  (pairingTolerance pairingTolerance_pos)
open YMGap.Continuum.CRealSeminormPairingCompletion
  (normCeiling normCeiling_nonnegative completedInner_diagonal_le_normCeiling
   representativeInner representativeInnerCauchy)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "PD" => pairingData hw0 hw1 (width := width)
local notation "P" => distanceData hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "Z" => completedZero hw0 hw1 width
local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)

private theorem completedNeg_zero : completedNeg hw0 hw1 Z = Z := by
  have h := completedNeg_add hw0 hw1 Z
  rw [completedAdd_zero hw0 hw1] at h
  exact h

theorem completedSub_zero (x : V) : completedSub hw0 hw1 x Z = x := by
  unfold completedSub
  rw [completedNeg_zero, completedAdd_zero]

theorem dist_zero (x : V) : completedDist hw0 hw1 x Z = B x x := by
  unfold completedDist
  rw [completedSub_zero]

def rowNormCap (R : RepresentedCauchy hw0 hw1 (width := width)) : Q' :=
  (1+1)+(normCeiling PD (CRealSeminormCauchyRows.diagonalCauchy P R)+
    normCeiling PD (CRealSeminormCauchyRows.diagonalCauchy P R))

theorem rowNormCap_nonnegative (R : RepresentedCauchy hw0 hw1 (width := width)) :
    (0 : Q')≤rowNormCap hw0 hw1 R :=
  Q'.zero_le_add _ _ (Q'.zero_le_add _ _ Q'.zero_le_one Q'.zero_le_one)
    (Q'.zero_le_add _ _ (normCeiling_nonnegative PD _) (normCeiling_nonnegative PD _))

theorem row_norm_bound (R : RepresentedCauchy hw0 hw1 (width := width))
    (n : Nat) (hn : limitRate hw0 hw1 R 1≤n) :
    RCle (B (rowPoint hw0 hw1 R n) (rowPoint hw0 hw1 R n))
      (rat (rowNormCap hw0 hw1 R)) := by
  have hd := limit_bound hw0 hw1 R 1 (by decide) n hn
  have hc := completedInner_diagonal_le_normCeiling PD
    (CRealSeminormCauchyRows.diagonalCauchy P R)
  have h := completedDist_triangle hw0 hw1 (rowPoint hw0 hw1 R n)
    (limit hw0 hw1 R) Z
  rw [dist_zero,dist_zero] at h
  exact RCle_trans h (RCadd_le_add (RCadd_le_add hd hd) (RCadd_le_add hc hc))

def pairCap (R S : RepresentedCauchy hw0 hw1 (width := width)) : Q' :=
  Q'.max' (rowNormCap hw0 hw1 S)
    (normCeiling PD (CRealSeminormCauchyRows.diagonalCauchy P R))

theorem pairCap_nonnegative (R S : RepresentedCauchy hw0 hw1 (width := width)) :
    (0 : Q')≤pairCap hw0 hw1 R S :=
  Q'.le_trans' _ _ _ (rowNormCap_nonnegative hw0 hw1 S) (Q'.le_max'_left _ _)

/-- Explicit two-row pairing modulus, constructed from both supplied row moduli. -/
def pairingModulus (R S : RepresentedCauchy hw0 hw1 (width := width))
    (epsilon : Q') : Nat :=
  let delta := pairingTolerance (pairCap hw0 hw1 R S)
    (pairCap_nonnegative hw0 hw1 R S) epsilon
  max (limitRate hw0 hw1 S 1)
    (max (limitRate hw0 hw1 R delta) (limitRate hw0 hw1 S delta))

theorem row_pairing_bound (R S : RepresentedCauchy hw0 hw1 (width := width))
    (epsilon : Q') (he : (0 : Q')<epsilon)
    (n : Nat) (hn : pairingModulus hw0 hw1 R S epsilon≤n) :
    RCle (B (rowPoint hw0 hw1 R n) (rowPoint hw0 hw1 S n))
      (RCadd (B (limit hw0 hw1 R) (limit hw0 hw1 S)) (rat epsilon)) ∧
    RCle (B (limit hw0 hw1 R) (limit hw0 hw1 S))
      (RCadd (B (rowPoint hw0 hw1 R n) (rowPoint hw0 hw1 S n)) (rat epsilon)) := by
  let cap := pairCap hw0 hw1 R S
  let hcap := pairCap_nonnegative hw0 hw1 R S
  let delta := pairingTolerance cap hcap epsilon
  have hd : (0 : Q')<delta := pairingTolerance_pos cap hcap he
  have hn1 : limitRate hw0 hw1 S 1≤n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hnR : limitRate hw0 hw1 R delta≤n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hn
  have hnS : limitRate hw0 hw1 S delta≤n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hn
  have hy : RCle (B (rowPoint hw0 hw1 S n) (rowPoint hw0 hw1 S n)) (rat cap) :=
    RCle_trans (row_norm_bound hw0 hw1 S n hn1)
      (leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_max'_left _ _))
  have hx : RCle (B (limit hw0 hw1 R) (limit hw0 hw1 R)) (rat cap) :=
    RCle_trans (completedInner_diagonal_le_normCeiling PD
      (CRealSeminormCauchyRows.diagonalCauchy P R))
      (leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_max'_right _ _))
  exact pairing_close hw0 hw1 _ _ _ _ cap hcap epsilon he
    (limit_bound hw0 hw1 R delta hd n hnR)
    (limit_bound hw0 hw1 S delta hd n hnS) hy hx

def pairingRepresentative (R S : RepresentedCauchy hw0 hw1 (width := width)) : CReal :=
  representativeInner PD (CRealSeminormCauchyRows.diagonalCauchy P R)
    (CRealSeminormCauchyRows.diagonalCauchy P S)

def pairingRepresentativeCauchy (R S : RepresentedCauchy hw0 hw1 (width := width)) :
    QCauchy (pairingRepresentative hw0 hw1 R S).approx :=
  representativeInnerCauchy PD (CRealSeminormCauchyRows.diagonalCauchy P R)
    (CRealSeminormCauchyRows.diagonalCauchy P S)

theorem pairingRepresentative_pin (R S : RepresentedCauchy hw0 hw1 (width := width)) :
    Quotient.mk crealSetoid (pairingRepresentative hw0 hw1 R S) =
      B (limit hw0 hw1 R) (limit hw0 hw1 S) := rfl

/-- An arbitrary completed-real rowwise upper bound survives the SAME limit. -/
theorem rowLimit_norm_bound (R : RepresentedCauchy hw0 hw1 (width := width))
    (M : RC)
    (h : ∀ n, RCle (B (rowPoint hw0 hw1 R n) (rowPoint hw0 hw1 R n)) M) :
    RCle (B (limit hw0 hw1 R) (limit hw0 hw1 R)) M := by
  apply RationalScalarTwoSidedError.le_of_all_errors
  intro epsilon he
  let n := pairingModulus hw0 hw1 R R epsilon
  exact RCle_trans (row_pairing_bound hw0 hw1 R R epsilon he n (Nat.le_refl n)).2
    (RCadd_le_add (h n) (RCle_refl _))

/-- Constant supplied representatives recover their original completion class. -/
def constantRows (X : (D).Cauchy) : RepresentedCauchy hw0 hw1 (width := width) where
  row := fun _ => X
  modulus := fun _ => 0
  isCauchy := by
    intro epsilon he m n _ _
    change RCle (completedDist hw0 hw1
      (Quotient.mk (D).completionSetoid X)
      (Quotient.mk (D).completionSetoid X)) (rat epsilon)
    rw [(completedDist_zero_iff hw0 hw1 _ _).mpr rfl]
    exact leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_of_lt he)

theorem constantRows_point (X : (D).Cauchy) (n : Nat) :
    rowPoint hw0 hw1 (constantRows hw0 hw1 X) n =
      Quotient.mk (D).completionSetoid X := rfl

theorem limit_constantRows (X : (D).Cauchy) :
    limit hw0 hw1 (constantRows hw0 hw1 X) =
      Quotient.mk (D).completionSetoid X := by
  apply limit_unique hw0 hw1 (constantRows hw0 hw1 X)
    (Quotient.mk (D).completionSetoid X) (fun _ => 0)
  intro epsilon he n _
  rw [constantRows_point, (completedDist_zero_iff hw0 hw1 _ _).mpr rfl]
  exact leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_of_lt he)

end YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit

#print axioms YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit.completedSub_zero
#print axioms YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit.dist_zero
#print axioms YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit.rowNormCap
#print axioms YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit.rowNormCap_nonnegative
#print axioms YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit.row_norm_bound
#print axioms YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit.pairCap
#print axioms YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit.pairCap_nonnegative
#print axioms YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit.pairingModulus
#print axioms YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit.row_pairing_bound
#print axioms YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit.pairingRepresentative
#print axioms YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit.pairingRepresentativeCauchy
#print axioms YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit.pairingRepresentative_pin
#print axioms YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit.rowLimit_norm_bound
#print axioms YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit.constantRows
#print axioms YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit.constantRows_point
#print axioms YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit.limit_constantRows
