/-
# Computed logarithmic passage for the finite selected-entropy payment

The supplied finite inequality is the one already produced for the COMPLETE
original action under its literal selected Haar schedule. Here A and its OWN
selected partition Z remain opaque rational values. The existing faithful
binary logarithm is used at the SAME approximation index as both entropy
partial sums. All three errors are paid by a computed retained cutoff.

This scalar join neither changes the original density nor divides by Z. The
positive partition window is explicit, and the actual original specialization
must produce it. No log-integral premise, response-relative payment, physical
scaling or spectral conclusion is introduced.
-/

import YMGap.Continuum.BF4SelectedEntropyBudget
import YMGap.Continuum.RegularizedLogFiniteCoercivity
import YMGap.Continuum.RegularizedLogBinaryIdentification
import YMGap.Constructive.CRealExplicitSqueeze

namespace YMGap.Continuum.BF4SelectedEntropyLogBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2HeatJacobiActiveFactorCount (activeFactorCount)
open YMGap.Continuum.RegularizedLogPolynomial (partialSum modulus)
open YMGap.Continuum.RegularizedLogFiniteCoercivity (third)
open YMGap.Continuum.RegularizedLogBinaryReduction (binaryReduction)
open YMGap.Continuum.RebasedExpShiftSupportReduction (dyadicLogValue)
open YMGap.Continuum.BF4SelectedEntropyBudget (errorBudget error_coefficient_le)
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv
private abbrev PE := PolyExpr
local instance : Add PE := ⟨.add⟩
local instance : Mul PE := ⟨.mul⟩
local instance (n : Nat) : OfNat PE n := ⟨.const (Int.ofNat n)⟩

private theorem qr (a b : PE) (h : RingNormaliser.normalize a = RingNormaliser.normalize b)
    (rho : Nat → Q') : RingNormaliser.eval rho a ≈ RingNormaliser.eval rho b :=
  poly_identity_of_normal_eq a b h rho

private theorem tc {a b c : Q'} (h : a ≈ b) (k : b ≈ c) : a ≈ c :=
  Q'.eqv_trans _ _ _ h k

/-- The actual binary-log expression; the third remains the literal rational
one-third, rather than a freely supplied log(3). -/
def logBound (q Z : Q') (hZ0 : (0 : Q') < Z) (hZ1 : Z ≤ 1) (F : Nat) : CReal :=
  CReal.mul (CReal.ofQ' (256*(1-q)))
    (CReal.add
      (CReal.neg (CReal.mul (CReal.ofQ' Z) (dyadicLogValue (binaryReduction Z hZ0 hZ1))))
      (CReal.mul (CReal.ofQ' (3*Q'.ofNat F*Z))
        (CReal.neg (CReal.mul (CReal.ofQ' third)
          (dyadicLogValue (binaryReduction third (by decide) (by decide)))))))

/-- All-factor finite error and both scalar identification errors are distinct. -/
def totalBudget (q : Q') (L F : Nat) : Nat := 256+768*F+errorBudget q L F

theorem totalBudget_ofNat (q : Q') (L F : Nat) :
    Q'.ofNat (totalBudget q L F) ≈ 256+768*Q'.ofNat F+Q'.ofNat (errorBudget q L F) :=
  tc (Q'.ofNat_add_eqv _ _)
    (Q'.add_eqv_congr' (tc (Q'.ofNat_add_eqv _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (ClusterCount.ofNat_mul_eqv 768 F)))
      (Q'.eqv_refl _))

/-- Computed Type-level cutoff, retaining an entropy degree of at least one. -/
def logRate (q : Q') (L F : Nat) (epsilon : Q') : Nat :=
  max 1 (max
    (RegularizedLogBinaryIdentification.identificationRate
      (epsilon*Q'.invSucc (totalBudget q L F)))
    (modulus (epsilon*Q'.invSucc (totalBudget q L F))))

theorem logRate_one_le (q : Q') (L F : Nat) (epsilon : Q') :
    1 ≤ logRate q L F epsilon := Nat.le_max_left _ _

private theorem coefficient_bounds {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q')) :
    (0 : Q') ≤ 256*(1-q) ∧ 256*(1-q) ≤ 256 := by
  have hg1 : 1-q ≤ (1 : Q') := Q'.le_trans' _ _ _
    (Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg (Q'.le_of_lt hq0)))
    (Q'.le_of_eqv (by decide : (1 : Q')+ -(0 : Q') ≈ 1))
  exact ⟨Q'.mul_nonneg _ _ (by decide) (Q'.le_of_lt (HKPos.one_sub_pos hq1)),
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ (256 : Q') hg1 (by decide))
      (Q'.le_of_eqv (Q'.mul_one_eqv 256))⟩

private theorem weighted_coefficient_bound {q Z : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q')) (hZ0 : (0 : Q') < Z) (hZ1 : Z ≤ 1)
    (F : Nat) : (256*(1-q))*(3*Q'.ofNat F*Z) ≤ 768*Q'.ofNat F := by
  have hf0 := ClusterCount.ofNat_nonneg F
  have hb0 : (0 : Q') ≤ 3*Q'.ofNat F := Q'.mul_nonneg _ _ (by decide) hf0
  have hb : 3*Q'.ofNat F*Z ≤ 3*Q'.ofNat F :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hZ1 hb0)
      (Q'.le_of_eqv (Q'.mul_one_eqv _))
  have hbZ0 := Q'.mul_nonneg _ _ hb0 (Q'.le_of_lt hZ0)
  have hp : (256 : Q')*(3*Q'.ofNat F) ≈ 768*Q'.ofNat F :=
    qr (.mul (.const 256) (.mul (.const 3) (.var 0)))
      (.mul (.const 768) (.var 0)) (by decide) (fun _ => Q'.ofNat F)
  exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _
    (coefficient_bounds hq0 hq1).2 hbZ0)
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ (256 : Q') hb (by decide))
      (Q'.le_of_eqv hp))

private theorem budget_payment (q : Q') (L F : Nat) (epsilon : Q')
    (he : (0 : Q') < epsilon) :
    Q'.ofNat (totalBudget q L F)*(epsilon*Q'.invSucc (totalBudget q L F)) ≤ epsilon := by
  let B := totalBudget q L F
  have hB : Q'.ofNat B*Q'.invSucc B ≤ (1 : Q') := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (ClusterCount.ofNat_le_ofNat (Nat.le_succ B)) (Q'.invSucc_nonneg B))
    (Q'.le_of_eqv (Q'.ofNat_succ_mul_invSucc B))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv
    (qr (.var 0*(.var 1*.var 2)) (.var 1*(.var 0*.var 2)) (by decide)
      (fun | 0 => Q'.ofNat B | 1 => epsilon | _ => Q'.invSucc B)))
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hB (Q'.le_of_lt he))
      (Q'.le_of_eqv (Q'.mul_one_eqv epsilon)))

/-- SAME-index logarithmic payment for the already produced finite inequality.
A and Z are not identified with a different integral or normalization. -/
theorem log_approx {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (Z : Q') (hZ0 : (0 : Q') < Z) (hZ1 : Z ≤ 1) (L F : Nat) (A : Q')
    (hfinite : ∀ N : Nat, 1 ≤ N → A ≤ (256*(1-q))*(partialSum Z N+
      3*partialSum third N*Q'.ofNat F*Z+
      (Q'.ofNat L+3*Q'.ofNat (activeFactorCount q-1)*Q'.ofNat F)*Q'.invSucc N))
    (epsilon : Q') (he : (0 : Q') < epsilon) (N : Nat)
    (hN : logRate q L F epsilon ≤ N) :
    A ≤ (logBound q Z hZ0 hZ1 F).approx N+epsilon := by
  let delta := epsilon*Q'.invSucc (totalBudget q L F)
  let c := (256 : Q')*(1-q)
  let b := 3*Q'.ofNat F*Z
  let e := c*(Q'.ofNat L+3*Q'.ofNat (activeFactorCount q-1)*Q'.ofNat F)*Q'.invSucc N
  let lZ := CReal.neg (CReal.mul (CReal.ofQ' Z) (dyadicLogValue (binaryReduction Z hZ0 hZ1)))
  let lT := CReal.neg (CReal.mul (CReal.ofQ' third)
    (dyadicLogValue (binaryReduction third (by decide) (by decide))))
  have hd : (0 : Q') < delta := Q'.mul_pos he (Q'.invSucc_pos _)
  have hn1 : 1 ≤ N := Nat.le_trans (logRate_one_le q L F epsilon) hN
  have hnInner : max (RegularizedLogBinaryIdentification.identificationRate delta)
      (modulus delta) ≤ N := Nat.le_trans (Nat.le_max_right _ _) hN
  have hnLog : RegularizedLogBinaryIdentification.identificationRate delta ≤ N :=
    Nat.le_trans (Nat.le_max_left _ _) hnInner
  have hnTail : modulus delta ≤ N := Nat.le_trans (Nat.le_max_right _ _) hnInner
  have hinv : Q'.invSucc N ≤ delta := Q'.le_trans' _ _ _
    (ExpNeg.invSucc_le_of_le hnTail) (HalfPow.invSucc_den_le delta hd)
  have hc := coefficient_bounds hq0 hq1
  have hb0 : (0 : Q') ≤ b := Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (by decide) (ClusterCount.ofNat_nonneg F)) (Q'.le_of_lt hZ0)
  have hZ := (RegularizedLogBinaryIdentification.value_binaryLog_approx Z hZ0 hZ1
    delta hd N hnLog).1
  have hT := (RegularizedLogBinaryIdentification.value_binaryLog_approx third (by decide) (by decide)
    delta hd N hnLog).1
  have hcomp : c*(partialSum Z N+b*partialSum third N) ≤
      c*((lZ.approx N+delta)+b*(lT.approx N+delta)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ c
      (Q'.add_le_add hZ (Q'.mul_le_mul_of_nonneg_left _ _ b hT hb0)) hc.1
  have heBound : e ≤ Q'.ofNat (errorBudget q L F)*delta :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _
      (error_coefficient_le hq0 hq1 L F) (Q'.invSucc_nonneg N))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hinv (ClusterCount.ofNat_nonneg _))
  have herr : (c*delta+(c*b)*delta)+e ≤
      (256*delta+(768*Q'.ofNat F)*delta)+Q'.ofNat (errorBudget q L F)*delta :=
    Q'.add_le_add (Q'.add_le_add
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hc.2 (Q'.le_of_lt hd))
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (weighted_coefficient_bound hq0 hq1 hZ0 hZ1 F)
        (Q'.le_of_lt hd))) heBound
  have hcollect : (256*delta+(768*Q'.ofNat F)*delta)+Q'.ofNat (errorBudget q L F)*delta ≈
      Q'.ofNat (totalBudget q L F)*delta :=
    tc (qr ((256*.var 0+(768*.var 1)*.var 0)+.var 2*.var 0)
      ((256+768*.var 1+.var 2)*.var 0) (by decide)
      (fun | 0 => delta | 1 => Q'.ofNat F | _ => Q'.ofNat (errorBudget q L F)))
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (totalBudget_ofNat q L F)))
  have hsmall : (c*delta+(c*b)*delta)+e ≤ epsilon := Q'.le_trans' _ _ _ herr
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hcollect) (budget_payment q L F epsilon he))
  have hstart : (256*(1-q))*(partialSum Z N+3*partialSum third N*Q'.ofNat F*Z+
      (Q'.ofNat L+3*Q'.ofNat (activeFactorCount q-1)*Q'.ofNat F)*Q'.invSucc N) ≈
      c*(partialSum Z N+b*partialSum third N)+e :=
    qr (.var 0*((.var 1+3*.var 2*.var 3*.var 4)+.var 5*.var 6))
      (.var 0*(.var 1+(3*.var 3*.var 4)*.var 2)+(.var 0*.var 5)*.var 6)
      (by decide) (fun
        | 0 => c
        | 1 => partialSum Z N
        | 2 => partialSum third N
        | 3 => Q'.ofNat F
        | 4 => Z
        | 5 => Q'.ofNat L+3*Q'.ofNat (activeFactorCount q-1)*Q'.ofNat F
        | _ => Q'.invSucc N)
  have hend : c*((lZ.approx N+delta)+b*(lT.approx N+delta))+e ≈
      (logBound q Z hZ0 hZ1 F).approx N+((c*delta+(c*b)*delta)+e) :=
    qr (.var 0*((.var 1+.var 2)+.var 3*(.var 4+.var 2))+.var 5)
      (.var 0*(.var 1+.var 3*.var 4)+((.var 0*.var 2+(.var 0*.var 3)*.var 2)+.var 5))
      (by decide) (fun | 0 => c | 1 => lZ.approx N | 2 => delta | 3 => b | 4 => lT.approx N | _ => e)
  exact Q'.le_trans' _ _ _ (hfinite N hn1)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hstart)
      (Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ e hcomp)
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv hend)
          (Q'.add_le_add_left _ _ _ hsmall))))

/-- Witness-bearing sound eventual order, with the same computed cutoff. -/
def log_bound {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (Z : Q') (hZ0 : (0 : Q') < Z) (hZ1 : Z ≤ 1) (L F : Nat) (A : Q')
    (hfinite : ∀ N : Nat, 1 ≤ N → A ≤ (256*(1-q))*(partialSum Z N+
      3*partialSum third N*Q'.ofNat F*Z+
      (Q'.ofNat L+3*Q'.ofNat (activeFactorCount q-1)*Q'.ofNat F)*Q'.invSucc N)) :
    CReal.ExplicitLeEv (CReal.ofQ' A) (logBound q Z hZ0 hZ1 F) where
  modulus := logRate q L F
  bound := log_approx hq0 hq1 Z hZ0 hZ1 L F A hfinite

end YMGap.Continuum.BF4SelectedEntropyLogBound

#print axioms YMGap.Continuum.BF4SelectedEntropyLogBound.logBound
#print axioms YMGap.Continuum.BF4SelectedEntropyLogBound.totalBudget
#print axioms YMGap.Continuum.BF4SelectedEntropyLogBound.totalBudget_ofNat
#print axioms YMGap.Continuum.BF4SelectedEntropyLogBound.logRate
#print axioms YMGap.Continuum.BF4SelectedEntropyLogBound.logRate_one_le
#print axioms YMGap.Continuum.BF4SelectedEntropyLogBound.log_approx
#print axioms YMGap.Continuum.BF4SelectedEntropyLogBound.log_bound
