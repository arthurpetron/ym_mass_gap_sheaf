/-
# Exact kernel of the completed quaternion adjoint matrix

The represented three-by-three matrix is faithful on the EXISTING completed
central-sign cosets.  A fixed rational row probe selects the sign; equality of
completed matrices is used only to verify this choice propositionally.  No
completed-point equality test, representative choice, compact SO(3), Haar
extension, or Yang--Mills transfer estimate is asserted.
-/

import YMGap.RepTheory.RationalQuaternionCompletedAdjointMatrix
import YMGap.RepTheory.RationalQuaternionNormRepair
import YMGap.RepTheory.RationalQuaternionCompletedDistance

namespace YMGap.RepTheory.RationalQuaternionCompletedAdjointKernel

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.RepTheory.RationalQuaternion
open YMGap.RepTheory.RationalQuaternionNormRepair
open YMGap.RepTheory.RationalQuaternionCauchyGroup
open YMGap.RepTheory.RationalQuaternionCompletedDistance
open YMGap.RepTheory.RationalQuaternionCompletedSignQuotient
open YMGap.RepTheory.RationalQuaternionCompletedAdjointMatrix
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.CRealSeminormCompletion

local infix:50 " ≈ " => Q'.eqv
local instance : Add PolyExpr := ⟨.add⟩
local instance : Mul PolyExpr := ⟨.mul⟩
local instance : Neg PolyExpr := ⟨.neg⟩
local instance (n : Nat) : OfNat PolyExpr n := ⟨.const (Int.ofNat n)⟩

private def gap (q : UnitNorm) : Q' :=
  3 + -(rawEntry q.val 0 0 + rawEntry q.val 1 1 + rawEntry q.val 2 2)

private theorem gap_formula (q : UnitNorm) :
    gap q ≈ 4*(1 + -(q.val.r*q.val.r)) := by
  let R : PolyExpr := .var 0
  let I : PolyExpr := .var 1
  let J : PolyExpr := .var 2
  let K : PolyExpr := .var 3
  let N : PolyExpr := ((R*R+I*I)+(J*J+K*K))
  let T : PolyExpr :=
    (((R*R+I*I)+ -(J*J))+ -(K*K))+
    (((R*R+ -(I*I))+J*J)+ -(K*K))+
    (((R*R+ -(I*I))+ -(J*J))+K*K)
  have h : gap q ≈ 4*(1 + -(q.val.r*q.val.r)) +
      (normSq q.val + -1) := by
    have hp := poly_identity_of_normal_eq
      ((.const 3 : PolyExpr)+ -T)
      ((.const 4)*(1+ -(R*R))+(N+ -1))
      (by decide)
      (fun | 0 => q.val.r | 1 => q.val.i | 2 => q.val.j | _ => q.val.k)
    change gap q ≈ 4*(1 + -(q.val.r*q.val.r)) +
      (normSq q.val + -1) at hp
    exact hp
  have hn : normSq q.val + -1 ≈ 0 := by
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ q.unitNorm)
      (Q'.add_neg_self_eqv 1)
  exact Q'.eqv_trans _ _ _ h
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ hn)
      (QPoly.q_add_zero_eqv _))

private theorem chord_positive_formula (q : UnitNorm) :
    chord q unitOne + chord q unitOne ≈ 4*(1 + -q.val.r) := by
  let R : PolyExpr := .var 0
  let I : PolyExpr := .var 1
  let J : PolyExpr := .var 2
  let K : PolyExpr := .var 3
  let N : PolyExpr := ((R*R+I*I)+(J*J+K*K))
  let D : PolyExpr :=
    (((R+ -1)*(R+ -1)+(I+ -0)*(I+ -0))+
      ((J+ -0)*(J+ -0)+(K+ -0)*(K+ -0)))
  have hp := poly_identity_of_normal_eq
    (D+D) ((.const 4)*(1+ -R)+(.const 2)*(N+ -1))
    (by decide)
    (fun | 0 => q.val.r | 1 => q.val.i | 2 => q.val.j | _ => q.val.k)
  have h : chord q unitOne + chord q unitOne ≈
      4*(1 + -q.val.r)+2*(normSq q.val + -1) := by
    change chord q unitOne + chord q unitOne ≈
      4*(1 + -q.val.r)+2*(normSq q.val + -1) at hp
    exact hp
  have hn : normSq q.val + -1 ≈ 0 := by
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ q.unitNorm)
      (Q'.add_neg_self_eqv 1)
  exact Q'.eqv_trans _ _ _ h
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left _ _ _ hn)
          (by decide : (2:Q')*0 ≈ 0)))
      (QPoly.q_add_zero_eqv _))

private theorem chord_negative_formula (q : UnitNorm) :
    chord q unitNegativeOne + chord q unitNegativeOne ≈ 4*(1 + q.val.r) := by
  let R : PolyExpr := .var 0
  let I : PolyExpr := .var 1
  let J : PolyExpr := .var 2
  let K : PolyExpr := .var 3
  let N : PolyExpr := ((R*R+I*I)+(J*J+K*K))
  let D : PolyExpr :=
    (((R+ -(-1))*(R+ -(-1))+(I+ -0)*(I+ -0))+
      ((J+ -0)*(J+ -0)+(K+ -0)*(K+ -0)))
  have hp := poly_identity_of_normal_eq
    (D+D) ((.const 4)*(1+R)+(.const 2)*(N+ -1))
    (by decide)
    (fun | 0 => q.val.r | 1 => q.val.i | 2 => q.val.j | _ => q.val.k)
  have h : chord q unitNegativeOne + chord q unitNegativeOne ≈
      4*(1 + q.val.r)+2*(normSq q.val + -1) := by
    change chord q unitNegativeOne + chord q unitNegativeOne ≈
      4*(1 + q.val.r)+2*(normSq q.val + -1) at hp
    exact hp
  have hn : normSq q.val + -1 ≈ 0 := by
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ q.unitNorm)
      (Q'.add_neg_self_eqv 1)
  exact Q'.eqv_trans _ _ _ h
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left _ _ _ hn)
          (by decide : (2:Q')*0 ≈ 0)))
      (QPoly.q_add_zero_eqv _))

private theorem scalar_abs_le_one (q : UnitNorm) : Q'.abs q.val.r ≤ 1 := by
  have hs : q.val.r*q.val.r ≤ (1 : Q') :=
    Q'.le_trans' _ _ _
      (coordinate_square_le q.val 0)
      (Q'.le_of_eqv q.unitNorm)
  have ha : Q'.abs q.val.r * Q'.abs q.val.r ≈ q.val.r*q.val.r := by
    unfold Q'.abs
    split
    · exact Q'.eqv_refl _
    · exact poly_identity_of_normal_eq
        ((- (.var 0))*(- (.var 0))) ((.var 0)*(.var 0))
        (by decide) (fun _ => q.val.r)
  exact CReal.le_of_sq_le_sq (by decide) (Q'.abs_nonneg _)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv ha)
      (Q'.le_trans' _ _ _ hs (by decide : (1 : Q') ≤ 1*1)))

attribute [local irreducible] gap chord rawEntry

private theorem gap_controls_positive (q : UnitNorm) (hr : (0 : Q') ≤ q.val.r) :
    chord q unitOne + chord q unitOne ≤ gap q := by
  have hr1 : q.val.r ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ (Q'.le_abs_self _) (scalar_abs_le_one q)
  have hd : (0 : Q') ≤ 1 + -q.val.r := Q'.sub_nonneg_of_le hr1
  have hterm : (0 : Q') ≤ 4*(q.val.r*(1 + -q.val.r)) :=
    Q'.mul_nonneg _ _ (by decide)
      (Q'.mul_nonneg _ _ hr hd)
  have hi : gap q ≈ (chord q unitOne + chord q unitOne) +
      4*(q.val.r*(1 + -q.val.r)) := by
    have hp : 4*(1 + -(q.val.r*q.val.r)) ≈
        4*(1 + -q.val.r)+4*(q.val.r*(1 + -q.val.r)) := by
      let R : PolyExpr := .var 0
      let F : PolyExpr := .const 4
      let U : PolyExpr := .const 1
      have hh := poly_identity_of_normal_eq
        (F*(U+ -(R*R)))
        (F*(U+ -R)+F*(R*(U+ -R)))
        (by decide) (fun _ => q.val.r)
      change 4*(1 + -(q.val.r*q.val.r)) ≈
        4*(1 + -q.val.r)+4*(q.val.r*(1 + -q.val.r)) at hh
      exact hh
    exact Q'.eqv_trans _ _ _ (gap_formula q)
      (Q'.eqv_trans _ _ _ hp
        (Q'.add_eqv_congr_right _ _ _
          (Q'.eqv_symm (chord_positive_formula q))))
  exact Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg _ _ hterm)
    (Q'.ge_of_eqv hi)

private theorem gap_controls_negative (q : UnitNorm) (hr : q.val.r ≤ (0 : Q')) :
    chord q unitNegativeOne + chord q unitNegativeOne ≤ gap q := by
  have hr0 : (0 : Q') ≤ -q.val.r := by
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (by decide : -(0:Q') ≈ 0))
      (Q'.neg_le_neg hr)
  have hr1 : -q.val.r ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ (Q'.neg_le_abs _) (scalar_abs_le_one q)
  have hd : (0 : Q') ≤ 1 + q.val.r := by
    have h := Q'.sub_nonneg_of_le hr1
    have hdEq : 1 + -(-q.val.r) ≈ 1 + q.val.r :=
      Q'.add_eqv_congr_left _ _ _ (Q'.neg_neg_eqv q.val.r)
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv hdEq)
  have hterm : (0 : Q') ≤ 4*((-q.val.r)*(1 + q.val.r)) :=
    Q'.mul_nonneg _ _ (by decide)
      (Q'.mul_nonneg _ _ hr0 hd)
  have hi : gap q ≈ (chord q unitNegativeOne + chord q unitNegativeOne) +
      4*((-q.val.r)*(1 + q.val.r)) := by
    have hp : 4*(1 + -(q.val.r*q.val.r)) ≈
        4*(1 + q.val.r)+4*((-q.val.r)*(1 + q.val.r)) := by
      let R : PolyExpr := .var 0
      let F : PolyExpr := .const 4
      let U : PolyExpr := .const 1
      have hh := poly_identity_of_normal_eq
        (F*(U+ -(R*R)))
        (F*(U+R)+F*((-R)*(U+R)))
        (by decide) (fun _ => q.val.r)
      change 4*(1 + -(q.val.r*q.val.r)) ≈
        4*(1 + q.val.r)+4*((-q.val.r)*(1 + q.val.r)) at hh
      exact hh
    exact Q'.eqv_trans _ _ _ (gap_formula q)
      (Q'.eqv_trans _ _ _ hp
        (Q'.add_eqv_congr_right _ _ _
          (Q'.eqv_symm (chord_negative_formula q))))
  exact Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg _ _ hterm)
    (Q'.ge_of_eqv hi)

private theorem matrix_trace_tail (X : CauchyPoint)
    (hmat : representation (Quotient.mk chordSeminorm.completionSetoid X) = matrixOne)
    (e : Q') (he : (0 : Q') < e) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n → gap (X.seq n) ≤ e := by
  have hdiag (i : Fin 3) :
      representation (Quotient.mk chordSeminorm.completionSetoid X) i i =
        matrixOne i i := congrFun (congrFun hmat i) i
  have h0 : CReal.Equiv (rowEntry X 0 0) (CReal.ofQ' 1) :=
    Quotient.exact ((representation_mk X 0 0).symm.trans (hdiag 0))
  have h1 : CReal.Equiv (rowEntry X 1 1) (CReal.ofQ' 1) :=
    Quotient.exact ((representation_mk X 1 1).symm.trans (hdiag 1))
  have h2 : CReal.Equiv (rowEntry X 2 2) (CReal.ofQ' 1) :=
    Quotient.exact ((representation_mk X 2 2).symm.trans (hdiag 2))
  let d := HalfPow.half*(HalfPow.half*e)
  have hd : (0 : Q') < d := ExpNeg.half_mul_pos _
    (ExpNeg.half_mul_pos e he)
  obtain ⟨N0, hN0⟩ := h0 d hd
  obtain ⟨N1, hN1⟩ := h1 d hd
  obtain ⟨N2, hN2⟩ := h2 d hd
  refine ⟨max N0 (max N1 N2), fun n hn => ?_⟩
  have hn0 : N0 ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hn1 : N1 ≤ n := Nat.le_trans (Nat.le_max_left _ _)
    (Nat.le_trans (Nat.le_max_right _ _) hn)
  have hn2 : N2 ≤ n := Nat.le_trans (Nat.le_max_right _ _)
    (Nat.le_trans (Nat.le_max_right _ _) hn)
  have hs := Q'.add_le_add
    (Q'.add_le_add (hN0 n hn0).2 (hN1 n hn1).2)
    (hN2 n hn2).2
  have hi : (1+1)+(1:Q') ≈ 3 := by decide
  let a := (rowEntry X 0 0).approx n
  let b := (rowEntry X 1 1).approx n
  let c := (rowEntry X 2 2).approx n
  have hj : ((rowEntry X 0 0).approx n+d)+
      ((rowEntry X 1 1).approx n+d)+
      ((rowEntry X 2 2).approx n+d) ≈
      (((rowEntry X 0 0).approx n+
        (rowEntry X 1 1).approx n)+
        (rowEntry X 2 2).approx n)+((d+d)+d) := by
    exact poly_identity_of_normal_eq
      ((((.var 0 + .var 3)+(.var 1 + .var 3))+
        (.var 2 + .var 3)))
      ((((.var 0 + .var 1)+.var 2)+
        ((.var 3 + .var 3)+.var 3)))
      (by decide) (fun | 0 => a | 1 => b | 2 => c | _ => d)
  have hk : (0 : Q') ≤ d := Q'.le_of_lt hd
  have hd2 : d+d ≈ HalfPow.half*e := ExpNeg.two_halves _
  have hd4 : (d+d)+(d+d) ≈ e :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ hd2)
        (Q'.add_eqv_congr_left _ _ _ hd2))
      (ExpNeg.two_halves e)
  have hd3 : (d+d)+d ≤ e :=
    Q'.le_trans' _ _ _
      (Q'.add_le_add_left (d+d) d (d+d)
        (Q'.add_le_self_of_nonneg d d hk))
      (Q'.le_of_eqv hd4)
  have ht' : 3 ≤ ((a+b)+c)+e := by
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hi)
      (Q'.le_trans' _ _ _ hs
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv hj)
          (Q'.add_le_add_left _ _ _ hd3)))
  have ht : 3 ≤ (rawEntry (X.seq n).val 0 0 +
      rawEntry (X.seq n).val 1 1 +
      rawEntry (X.seq n).val 2 2)+e := by
    simpa only [a,b,c,rowEntry_approx] using ht'
  have hgap : gap (X.seq n) ≤ e := by
    have hh : gap (X.seq n) ≈
        (3 + -((rawEntry (X.seq n).val 0 0 +
          rawEntry (X.seq n).val 1 1 +
          rawEntry (X.seq n).val 2 2))) := by
      unfold gap
      exact Q'.eqv_refl _
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hh)
      (Q'.sub_le_of_le_add ht)
  exact hgap

private theorem probe_choice_close (X : CauchyPoint)
    (hmat : representation (Quotient.mk chordSeminorm.completionSetoid X) = matrixOne) :
    ∀ e : Q', (0 : Q') < e → ∃ N : Nat, ∀ n : Nat, N ≤ n →
      chord (X.seq n) (if chord (rowProbe X) unitOne ≤ Q'.mkPos 1 2 (by decide)
        then unitOne else unitNegativeOne) ≤ e := by
  intro e he
  let sixteenth : Q' := Q'.mkPos 1 16 (by decide)
  let half : Q' := Q'.mkPos 1 2 (by decide)
  obtain ⟨M1,hM1⟩ := matrix_trace_tail X hmat sixteenth (by decide)
  obtain ⟨M2,hM2⟩ := matrix_trace_tail X hmat e he
  let N := max (X.modulus (Q'.mkPos 1 16 (by decide))) (max M1 M2)
  refine ⟨N, fun n hn => ?_⟩
  have hrow : chord (rowProbe X) (X.seq n) ≤ sixteenth :=
    rowApproximation_bound X (Q'.mkPos 1 16 (by decide))
      (by decide) n (Nat.le_trans (Nat.le_max_left _ _) hn)
  have hfixed : gap (X.seq n) ≤ sixteenth :=
    hM1 n (Nat.le_trans (Nat.le_max_left _ _)
      (Nat.le_trans (Nat.le_max_right _ _) hn))
  have hsmall : gap (X.seq n) ≤ e :=
    hM2 n (Nat.le_trans (Nat.le_max_right _ _)
      (Nat.le_trans (Nat.le_max_right _ _) hn))
  have hsep : ∀ s : UnitNorm,
      chord (X.seq n) s + chord (X.seq n) s ≤ sixteenth →
      chord (rowProbe X) s ≤ half := by
    intro s hnear
    have hsym : chord (X.seq n) s ≤ sixteenth :=
      Q'.le_trans' _ _ _
        (Q'.add_le_self_of_nonneg _ _ (chord_nonnegative (X.seq n) s)) hnear
    have ht := chord_triangle (rowProbe X) (X.seq n) s
    have hu := Q'.add_le_add (Q'.add_le_add hrow hrow)
      (Q'.add_le_add hsym hsym)
    exact Q'.le_trans' _ _ _ ht
      (Q'.le_trans' _ _ _ hu (by decide))
  if hr : (0 : Q') ≤ (X.seq n).val.r then
    have hprobe : chord (rowProbe X) unitOne ≤ half :=
      hsep unitOne (Q'.le_trans' _ _ _
        (gap_controls_positive (X.seq n) hr) hfixed)
    change chord (X.seq n)
      (if chord (rowProbe X) unitOne ≤ half then unitOne else unitNegativeOne) ≤ e
    rw [if_pos hprobe]
    exact Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg _ _ (chord_nonnegative (X.seq n) unitOne))
      (Q'.le_trans' _ _ _ (gap_controls_positive (X.seq n) hr) hsmall)
  else
    have hr' : (X.seq n).val.r ≤ (0 : Q') := Q'.nonpos_of_not_nonneg hr
    have hnegative : chord (rowProbe X) unitNegativeOne ≤ half :=
      hsep unitNegativeOne (Q'.le_trans' _ _ _
        (gap_controls_negative (X.seq n) hr') hfixed)
    have hnot : ¬ chord (rowProbe X) unitOne ≤ half := by
      intro hp
      have hp' : chord unitOne (rowProbe X) ≤ half :=
        Q'.le_trans' _ _ _ (Q'.le_of_eqv (chord_symm _ _)) hp
      have ht := chord_triangle unitOne (rowProbe X) unitNegativeOne
      have hu := Q'.add_le_add (Q'.add_le_add hp' hp')
        (Q'.add_le_add hnegative hnegative)
      have hbad : chord unitOne unitNegativeOne ≤ (2:Q') :=
        Q'.le_trans' _ _ _ ht (Q'.le_trans' _ _ _ hu (by decide))
      exact (by
        unfold chord
        decide : ¬ chord unitOne unitNegativeOne ≤ (2:Q')) hbad
    change chord (X.seq n)
      (if chord (rowProbe X) unitOne ≤ half then unitOne else unitNegativeOne) ≤ e
    rw [if_neg hnot]
    exact Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg _ _
        (chord_nonnegative (X.seq n) unitNegativeOne))
      (Q'.le_trans' _ _ _ (gap_controls_negative (X.seq n) hr') hsmall)

private theorem row_kernel_sign (X : CauchyPoint)
    (hmat : representation (Quotient.mk chordSeminorm.completionSetoid X) = matrixOne) :
    (Quotient.mk chordSeminorm.completionSetoid X : Point) =
      if chord (rowProbe X) unitOne ≤ Q'.mkPos 1 2 (by decide)
        then includeSign .positive else includeSign .negative := by
  let s : UnitNorm := if chord (rowProbe X) unitOne ≤ Q'.mkPos 1 2 (by decide)
    then unitOne else unitNegativeOne
  have he : CReal.Equiv (representativeDist X (chordSeminorm.constant s)) czero := by
    intro e he
    obtain ⟨N,hN⟩ := probe_choice_close X hmat e he
    refine ⟨N, fun n hn => ⟨?_, ?_⟩⟩
    · change chord (X.seq n) s ≤ (0:Q')+e
      exact Q'.le_trans' _ _ _ (hN n hn) (Q'.ge_of_eqv (QPoly.q_zero_add_eqv _))
    · change (0:Q') ≤ chord (X.seq n) s+e
      exact Q'.le_trans' _ _ _ (chord_nonnegative _ _)
        (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he))
  have hpoint : (Quotient.mk chordSeminorm.completionSetoid X : Point) = embed s :=
    Quotient.sound ⟨closeOfZero X (chordSeminorm.constant s) he⟩
  if hp : chord (rowProbe X) unitOne ≤ Q'.mkPos 1 2 (by decide) then
    simpa [s,hp,includeSign,UnitNorm.includeSign] using hpoint
  else
    simpa [s,hp,includeSign,UnitNorm.includeSign] using hpoint

/-- The actual completed adjoint kernel consists of precisely the two
embedded central signs, with no representative or compactness assumption. -/
theorem representation_kernel_iff (x : Point) :
    representation x = matrixOne ↔
      x = includeSign .positive ∨ x = includeSign .negative := by
  constructor
  · refine Quotient.inductionOn x ?_
    intro X h
    have hs := row_kernel_sign X h
    if hp : chord (rowProbe X) unitOne ≤ Q'.mkPos 1 2 (by decide) then
      exact Or.inl (by simpa [hp] using hs)
    else
      exact Or.inr (by simpa [hp] using hs)
  · intro h
    rcases h with h | h
    · rw [h]; exact representation_sign .positive
    · rw [h]; exact representation_sign .negative

/-- Reverse kernel membership produces the existing Type-valued central-sign
witness; its sign was chosen from a fixed rational sample. -/
def coverKernelSignWitness :
    signQuotientPresentation.RepresentationKernelHasGammaWitness
      coverRepresentation := by
  intro x h
  have hs : x = includeSign .positive ∨ x = includeSign .negative :=
    (representation_kernel_iff x).mp h
  apply kernelSignWitness x
  rcases hs with hpos | hneg
  · rw [hpos]
    exact signCentralSubgroup.centralCosetEquivalent_one_of_witness
      ⟨QuaternionSign.positive, rfl⟩
  · rw [hneg]
    exact signCentralSubgroup.centralCosetEquivalent_one_of_witness
      ⟨QuaternionSign.negative, rfl⟩

/-- The EXISTING quotient representation is faithful to its literal matrix
image.  This is algebraic sign descent, not an SO(3) topology claim. -/
theorem quotientRepresentation_faithful : quotientRepresentation.Faithful :=
  signQuotientPresentation.descendFaithful_of_kernelGammaWitness
    coverRepresentation coverRepresentation_kills_signs coverKernelSignWitness

/-- Matrix equality is EXACTLY equality of completed sign cosets. -/
theorem representation_eq_iff_coset (x y : Point) :
    representation x = representation y ↔
      signQuotientGroup.Equivalent x y := by
  constructor
  · intro h
    apply quotientRepresentation_faithful
    change (quotientRepresentation.toFun (signQuotientHom.toFun x)).matrix =
      (quotientRepresentation.toFun (signQuotientHom.toFun y)).matrix
    rw [quotientRepresentation_matrix, quotientRepresentation_matrix]
    exact h
  · exact representation_coset_congr x y

#print axioms representation_kernel_iff
#print axioms coverKernelSignWitness
#print axioms quotientRepresentation_faithful
#print axioms representation_eq_iff_coset

end YMGap.RepTheory.RationalQuaternionCompletedAdjointKernel
