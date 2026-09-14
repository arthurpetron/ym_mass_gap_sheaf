/-
# Pairing convergence and closed norm bounds for ORIGINAL represented rows

The diagonal Cauchy representatives compute rational norm ceilings. The
original squared-distance triangle bounds a tail of each row family.
Completed pairing continuity then supplies an explicit two-slot rate.
The limit scalar is the pairing of the SAME constructed row limits, with
its CReal representative and scalar Cauchy modulus retained. Uniform row
norm bounds pass to those limits; no representative selection is used.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicCompletedPairingContinuity
import YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows
import YMGap.Continuum.BF4ExactSlabThermodynamicRelaxation
import YMGap.Continuum.RationalScalarTwoSidedError

namespace YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows
open YMGap.Continuum.BF4ExactSlabThermodynamicPairingLimit (representativeInner representativeInnerCauchy)
open YMGap.Continuum.BF4ExactSlabThermodynamicRelaxation (normCap normCap_nonnegative norm_le_cap)
open YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity (pairingTolerance pairingTolerance_pos)
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedPairingContinuity (pairing_close)

local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)

theorem dist_zero (x : Completion) : completedDist x completedZero=completedInner x x := by
  unfold completedDist
  rw [completedSub_zero]

def rowNormCap (R : CauchyRows) : Q' :=
  (1+1)+(normCap (diagonalCauchy R)+normCap (diagonalCauchy R))

theorem rowNormCap_nonnegative (R : CauchyRows) : (0 : Q')≤rowNormCap R :=
  Q'.zero_le_add _ _ (Q'.zero_le_add _ _ Q'.zero_le_one Q'.zero_le_one)
    (Q'.zero_le_add _ _ (normCap_nonnegative _) (normCap_nonnegative _))

theorem row_norm_bound (R : CauchyRows) (n : Nat) (hn : rowLimitRate R 1≤n) :
    RCle (completedInner (rowPoint R n) (rowPoint R n)) (rat (rowNormCap R)) := by
  have hd := rowLimit_bound R 1 (by decide) n hn
  have hc := norm_le_cap (diagonalCauchy R)
  have h := completedDist_triangle (rowPoint R n) (rowLimit R) completedZero
  rw [dist_zero,dist_zero] at h
  exact RCle_trans h (RCadd_le_add (RCadd_le_add hd hd) (RCadd_le_add hc hc))

def pairCap (R S : CauchyRows) : Q' := Q'.max' (rowNormCap S) (normCap (diagonalCauchy R))

theorem pairCap_nonnegative (R S : CauchyRows) : (0 : Q')≤pairCap R S :=
  Q'.le_trans' _ _ _ (rowNormCap_nonnegative S) (Q'.le_max'_left _ _)

def pairingModulus (R S : CauchyRows) (epsilon : Q') : Nat :=
  let delta := pairingTolerance (pairCap R S) (pairCap_nonnegative R S) epsilon
  max (rowLimitRate S 1) (max (rowLimitRate R delta) (rowLimitRate S delta))

theorem row_pairing_bound (R S : CauchyRows) (epsilon : Q') (he : (0 : Q')<epsilon)
    (n : Nat) (hn : pairingModulus R S epsilon≤n) :
    RCle (completedInner (rowPoint R n) (rowPoint S n))
      (RCadd (completedInner (rowLimit R) (rowLimit S)) (rat epsilon)) ∧
    RCle (completedInner (rowLimit R) (rowLimit S))
      (RCadd (completedInner (rowPoint R n) (rowPoint S n)) (rat epsilon)) := by
  let B := pairCap R S
  let hB := pairCap_nonnegative R S
  let delta := pairingTolerance B hB epsilon
  have hd : (0 : Q')<delta := pairingTolerance_pos B hB he
  have hn1 : rowLimitRate S 1≤n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hnR : rowLimitRate R delta≤n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hn
  have hnS : rowLimitRate S delta≤n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hn
  have hy : RCle (completedInner (rowPoint S n) (rowPoint S n)) (rat B) :=
    RCle_trans (row_norm_bound S n hn1)
      (leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_max'_left _ _))
  have hx : RCle (completedInner (rowLimit R) (rowLimit R)) (rat B) :=
    RCle_trans (norm_le_cap (diagonalCauchy R))
      (leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_max'_right _ _))
  exact pairing_close _ _ _ _ B hB epsilon he
    (rowLimit_bound R delta hd n hnR) (rowLimit_bound S delta hd n hnS) hy hx

def pairingRepresentative (R S : CauchyRows) : CReal :=
  representativeInner (diagonalCauchy R) (diagonalCauchy S)

def pairingRepresentativeCauchy (R S : CauchyRows) : QCauchy (pairingRepresentative R S).approx :=
  representativeInnerCauchy (diagonalCauchy R) (diagonalCauchy S)

theorem pairingRepresentative_pin (R S : CauchyRows) :
    Quotient.mk crealSetoid (pairingRepresentative R S)=completedInner (rowLimit R) (rowLimit S) := rfl

def pairingCertificate (R S : CauchyRows) :
    Σ' s : CReal, Σ' _cs : QCauchy s.approx,
      {rate : Q' → Nat // Quotient.mk crealSetoid s=completedInner (rowLimit R) (rowLimit S) ∧
        ∀ epsilon : Q',(0 : Q')<epsilon → ∀ n,rate epsilon≤n →
          RCle (completedInner (rowPoint R n) (rowPoint S n)) (RCadd (Quotient.mk crealSetoid s) (rat epsilon)) ∧
          RCle (Quotient.mk crealSetoid s) (RCadd (completedInner (rowPoint R n) (rowPoint S n)) (rat epsilon))} :=
  ⟨pairingRepresentative R S,pairingRepresentativeCauchy R S,
    ⟨pairingModulus R S,⟨rfl,row_pairing_bound R S⟩⟩⟩

/-- The SAME norm at the constructed limit inherits every uniform row upper bound. -/
theorem rowLimit_norm_bound (R : CauchyRows) (M : Q')
    (h : ∀ n,RCle (completedInner (rowPoint R n) (rowPoint R n)) (rat M)) :
    RCle (completedInner (rowLimit R) (rowLimit R)) (rat M) := by
  apply RationalScalarTwoSidedError.le_of_all_errors
  intro epsilon he
  let n := pairingModulus R R epsilon
  exact RCle_trans (row_pairing_bound R R epsilon he n (Nat.le_refl n)).2
    (RCadd_le_add (h n) (RCle_refl _))

end YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingLimit

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingLimit.dist_zero
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingLimit.rowNormCap
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingLimit.rowNormCap_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingLimit.row_norm_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingLimit.pairCap
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingLimit.pairCap_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingLimit.pairingModulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingLimit.row_pairing_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingLimit.pairingRepresentative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingLimit.pairingRepresentativeCauchy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingLimit.pairingRepresentative_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingLimit.pairingCertificate
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingLimit.rowLimit_norm_bound
