/-
# Represented completeness for constructive-real squared seminorms

This file proves the diagonal core of completeness for an arbitrary
`CReal`-valued `SquaredSeminorm`.  An outer Cauchy family is supplied together
with one inner Cauchy representative for every outer point and an explicit
Type-level rate comparing every pair of representatives.  The diagonal is an
explicit `SquaredSeminorm.Cauchy`, and the supplied outer family converges to
it with displayed outer and inner rates.

This is represented completeness.  It does not claim that an arbitrary
quotient-valued sequence admits such a family of representatives: producing
those representatives from quotient points would require a choice operation.
No ordinary GNS carrier or Hilbert-space interpretation is used here.
-/

import YMGap.Continuum.CRealSeminormCompletion
import YMGap.Constructive.ExpNeg
import YMGap.Constructive.HalfPow

namespace YMGap.Continuum.CRealSeminormPresentedCompleteness

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.CRealSeminormCompletion

local infix:50 " ≈ " => Q'.eqv

/-- The exact rational budget produced by two nested squared triangles. -/
def treeBudget (t : Q') : Q' :=
  (t + t) + (((t + t) + (t + t)) + ((t + t) + (t + t)))

private theorem two_mul (t : Q') : (t + t).eqv ((2 : Q') * t) := by
  have e2 : (2 : Q') = (1 : Q') + 1 := by decide
  rw [e2]
  exact Q'.eqv_symm
    (Q'.eqv_trans _ _ _ (QPoly.q_add_mul 1 1 t)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right (1 * t) t (1 * t) (Q'.one_mul_eqv t))
        (Q'.add_eqv_congr_left t (1 * t) t (Q'.one_mul_eqv t))))

theorem treeBudget_eqv_ten (t : Q') : treeBudget t ≈ (10 : Q') * t := by
  have e2 : (t + t).eqv ((2 : Q') * t) := two_mul t
  have e4 : ((t + t) + (t + t)).eqv ((4 : Q') * t) := by
    refine Q'.eqv_trans _ _ _ (QPoly.q_add_congr e2 e2) ?_
    refine Q'.eqv_trans _ _ _ (two_mul ((2 : Q') * t)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv 2 2 t)) ?_
    exact Q'.mul_eqv_congr_right ((2 : Q') * 2) (4 : Q') t (by decide)
  have e8 : (((t + t) + (t + t)) + ((t + t) + (t + t))).eqv ((8 : Q') * t) := by
    refine Q'.eqv_trans _ _ _ (QPoly.q_add_congr e4 e4) ?_
    refine Q'.eqv_trans _ _ _ (two_mul ((4 : Q') * t)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv 2 4 t)) ?_
    exact Q'.mul_eqv_congr_right ((2 : Q') * 4) (8 : Q') t (by decide)
  refine Q'.eqv_trans _ _ _ (QPoly.q_add_congr e2 e8) ?_
  refine Q'.eqv_trans _ _ _
    (QPoly.q_add_congr (Q'.mul_comm_eqv 2 t) (Q'.mul_comm_eqv 8 t)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_add_eqv t 2 8)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left t ((2 : Q') + 8) (10 : Q') (by decide)) ?_
  exact Q'.mul_comm_eqv t 10

/-- Explicit rate at which the ten-copy diagonal budget is below `epsilon`. -/
def diagonalRate (epsilon : Q') : Nat := (epsilon * Q'.invSucc 9).den

theorem diagonalRate_spec (epsilon : Q') (he : (0 : Q') < epsilon)
    (k : Nat) (hk : diagonalRate epsilon ≤ k) :
    (10 : Q') * Q'.invSucc k ≤ epsilon := by
  have hd : (0 : Q') < epsilon * Q'.invSucc 9 :=
    Q'.mul_pos he (Q'.invSucc_pos 9)
  have hi : Q'.invSucc k ≤ epsilon * Q'.invSucc 9 :=
    Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hk)
      (HalfPow.invSucc_den_le (epsilon * Q'.invSucc 9) hd)
  have hm := Q'.mul_le_mul_of_nonneg_left (Q'.invSucc k)
    (epsilon * Q'.invSucc 9) (10 : Q') hi (by decide)
  apply Q'.le_trans' _ _ _ hm
  apply Q'.le_of_eqv
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv (10 : Q') epsilon (Q'.invSucc 9))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right ((10 : Q') * epsilon) (epsilon * (10 : Q'))
      (Q'.invSucc 9) (Q'.mul_comm_eqv 10 epsilon)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv epsilon 10 (Q'.invSucc 9)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left epsilon ((10 : Q') * Q'.invSucc 9) 1 (by decide)) ?_
  exact Q'.mul_one_eqv epsilon

variable (D : SquaredSeminorm)

/-- A represented regular-rate Cauchy family of points of `D.Completion`.
`pt p` is the supplied representative of the `p`th point; `bridge p q` is
the explicit inner index after which those representatives are within the
regular outer budget `1/(min p q + 1)`. -/
structure PresentedCauchy where
  pt : Nat → D.Cauchy
  bridge : Nat → Nat → Nat
  regular : ∀ p q n, bridge p q ≤ n →
    leEv (D.distSq ((pt p).seq n) ((pt q).seq n))
      (ofQ' (Q'.invSucc (min p q)))

namespace PresentedCauchy

variable {D : SquaredSeminorm} (X : PresentedCauchy D)

def diagonalIndex (k : Nat) : Nat := (X.pt k).modulus (Q'.invSucc k)

def diagonalSeq (k : Nat) : D.Carrier := (X.pt k).seq (X.diagonalIndex k)

private theorem threeHop (w0 p q w3 : D.Carrier) (t : Q')
    (h0 : leEv (D.distSq w0 p) (ofQ' t))
    (h1 : leEv (D.distSq p q) (ofQ' t))
    (h2 : leEv (D.distSq q w3) (ofQ' t)) :
    leEv (D.distSq w0 w3) (ofQ' (treeBudget t)) := by
  have hp3 : leEv (D.distSq p w3)
      (add (add (ofQ' t) (ofQ' t)) (add (ofQ' t) (ofQ' t))) :=
    leEv_trans (D.distSq_triangle p q w3)
      (leEv_add (leEv_add h1 h1) (leEv_add h2 h2))
  have h := leEv_trans (D.distSq_triangle w0 p w3)
    (leEv_add (leEv_add h0 h0) (leEv_add hp3 hp3))
  simpa only [ofQ'_add, treeBudget] using h

theorem diagonal_cauchy_le (p q : Nat) (hpq : p ≤ q) :
    leEv (D.distSq (X.diagonalSeq p) (X.diagonalSeq q))
      (ofQ' (treeBudget (Q'.invSucc p))) := by
  let n := max (max (X.diagonalIndex p) (X.diagonalIndex q)) (X.bridge p q)
  apply threeHop (X.diagonalSeq p) ((X.pt p).seq n) ((X.pt q).seq n)
    (X.diagonalSeq q) (Q'.invSucc p)
  · exact (X.pt p).isCauchy _ (Q'.invSucc_pos p) _ _ (Nat.le_refl _)
      (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
  · simpa only [Nat.min_eq_left hpq] using
      X.regular p q n (Nat.le_max_right _ _)
  · have h := (X.pt q).isCauchy (Q'.invSucc q) (Q'.invSucc_pos q) n
      (X.diagonalIndex q)
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) (Nat.le_refl _)
    exact leEv_trans h (leEv_of_le (ofQ'_le_ofQ' (ExpNeg.invSucc_le_of_le hpq)))

/-- The explicit diagonal representative of the represented outer family. -/
def diagonal : D.Cauchy where
  seq := X.diagonalSeq
  modulus := diagonalRate
  isCauchy := by
    intro epsilon he p q hp hq
    rcases Nat.le_total p q with hpq | hqp
    · exact leEv_trans (X.diagonal_cauchy_le p q hpq)
        (leEv_of_le (ofQ'_le_ofQ'
          (Q'.le_trans' _ _ _ (Q'.le_of_eqv (treeBudget_eqv_ten _))
            (diagonalRate_spec epsilon he p hp))))
    · exact leEv_trans
        (leEv_of_equiv (D.distSq_symm (X.diagonalSeq p) (X.diagonalSeq q)))
        (leEv_trans (X.diagonal_cauchy_le q p hqp)
          (leEv_of_le (ofQ'_le_ofQ'
            (Q'.le_trans' _ _ _ (Q'.le_of_eqv (treeBudget_eqv_ten _))
              (diagonalRate_spec epsilon he q hq)))))

/-- Explicit inner comparison index used in convergence to the diagonal. -/
def convergenceInnerRate (p n : Nat) : Nat :=
  max (max n (X.diagonalIndex n))
    (max ((X.pt p).modulus (Q'.invSucc p)) (X.bridge p n))

def convergenceOuterRate (p : Nat) : Nat :=
  max p ((X.pt p).modulus (Q'.invSucc p))

theorem diagonal_convergence_le (p n : Nat)
    (hn : X.convergenceOuterRate p ≤ n) :
    leEv (D.distSq ((X.pt p).seq n) (X.diagonalSeq n))
      (ofQ' (treeBudget (Q'.invSucc p))) := by
  have hpn : p ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hmod : (X.pt p).modulus (Q'.invSucc p) ≤ n :=
    Nat.le_trans (Nat.le_max_right _ _) hn
  let k := X.convergenceInnerRate p n
  apply threeHop ((X.pt p).seq n) ((X.pt p).seq k) ((X.pt n).seq k)
    (X.diagonalSeq n) (Q'.invSucc p)
  · exact (X.pt p).isCauchy _ (Q'.invSucc_pos p) n k
      hmod
      (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
  · simpa only [Nat.min_eq_left hpn] using X.regular p n k
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
  · have h := (X.pt n).isCauchy (Q'.invSucc n) (Q'.invSucc_pos n) k
      (X.diagonalIndex n)
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) (Nat.le_refl _)
    exact leEv_trans h (leEv_of_le (ofQ'_le_ofQ' (ExpNeg.invSucc_le_of_le hpn)))

/-- The represented outer family converges to the explicit diagonal.  The
outer rate is `diagonalRate`; the inner comparison is the displayed
`convergenceInnerRate`. -/
theorem convergesToDiagonal (epsilon : Q') (he : (0 : Q') < epsilon)
    (p : Nat) (hp : diagonalRate epsilon ≤ p) (n : Nat)
    (hn : X.convergenceOuterRate p ≤ n) :
    leEv (D.distSq ((X.pt p).seq n) (X.diagonal.seq n)) (ofQ' epsilon) :=
  leEv_trans (X.diagonal_convergence_le p n hn)
    (leEv_of_le (ofQ'_le_ofQ'
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (treeBudget_eqv_ten _))
        (diagonalRate_spec epsilon he p hp))))

end PresentedCauchy

/-! ## Arbitrary outer modulus by constructive cofinal reindexing -/

/-- A represented outer Cauchy family with an arbitrary Type-level modulus.
The additional `bridge` is the explicit inner stage at which the displayed
comparison of the supplied representatives is valid. -/
structure GeneralPresentedCauchy where
  pt : Nat → D.Cauchy
  modulus : Q' → Nat
  bridge : Q' → Nat → Nat → Nat
  cauchy : ∀ epsilon, (0 : Q') < epsilon → ∀ p q,
    modulus epsilon ≤ p → modulus epsilon ≤ q → ∀ n,
    bridge epsilon p q ≤ n →
      leEv (D.distSq ((pt p).seq n) ((pt q).seq n)) (ofQ' epsilon)

namespace GeneralPresentedCauchy

variable {D : SquaredSeminorm} (X : GeneralPresentedCauchy D)

private def phiAux (modulus : Q' → Nat) : Nat → Nat
  | 0 => modulus (Q'.invSucc 0)
  | k + 1 => max (phiAux modulus k + 1) (modulus (Q'.invSucc (k + 1)))

def phi (k : Nat) : Nat := phiAux X.modulus k

theorem phi_succ_eq (k : Nat) :
    X.phi (k + 1) = max (X.phi k + 1) (X.modulus (Q'.invSucc (k + 1))) := rfl

theorem phi_lt_succ (k : Nat) : X.phi k < X.phi (k + 1) := by
  rw [X.phi_succ_eq k]
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)

theorem phi_mono {a b : Nat} (h : a ≤ b) : X.phi a ≤ X.phi b := by
  induction b with
  | zero => exact Nat.le_of_eq (by cases Nat.le_zero.mp h; rfl)
  | succ b ih =>
    rcases Nat.lt_or_ge a (b + 1) with hlt | hge
    · exact Nat.le_trans (ih (Nat.lt_succ_iff.mp hlt))
        (Nat.le_of_lt (X.phi_lt_succ b))
    · exact Nat.le_of_eq (by cases Nat.le_antisymm h hge; rfl)

theorem self_le_phi (k : Nat) : k ≤ X.phi k := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
      exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt ih (X.phi_lt_succ k))

theorem phi_ge_modulus (k : Nat) :
    X.modulus (Q'.invSucc k) ≤ X.phi k := by
  cases k with
  | zero => exact Nat.le_refl _
  | succ k => rw [X.phi_succ_eq k]; exact Nat.le_max_right _ _

/-- The arbitrary-modulus represented family, constructively reindexed to the
regular rate consumed by `PresentedCauchy.diagonal`. -/
def regularReindex : PresentedCauchy D where
  pt k := X.pt (X.phi k)
  bridge p q := X.bridge (Q'.invSucc (min p q)) (X.phi p) (X.phi q)
  regular p q n hn := by
    have hp : X.modulus (Q'.invSucc (min p q)) ≤ X.phi p :=
      Nat.le_trans (X.phi_ge_modulus (min p q))
        (X.phi_mono (Nat.min_le_left p q))
    have hq : X.modulus (Q'.invSucc (min p q)) ≤ X.phi q :=
      Nat.le_trans (X.phi_ge_modulus (min p q))
        (X.phi_mono (Nat.min_le_right p q))
    exact X.cauchy _ (Q'.invSucc_pos _) _ _ hp hq n hn

/-- Explicit diagonal limit representative for an arbitrary-modulus represented
outer family. -/
def diagonal : D.Cauchy := X.regularReindex.diagonal

private def quarter (epsilon : Q') : Q' :=
  HalfPow.half * (HalfPow.half * epsilon)

private theorem quarter_pos {epsilon : Q'} (he : (0 : Q') < epsilon) :
    (0 : Q') < quarter epsilon :=
  ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos epsilon he)

/-- Fixed cofinal pivot used to compare an original outer point to the
regularly reindexed family and then to its diagonal. -/
def convergencePivot (epsilon : Q') : Nat :=
  max (diagonalRate (quarter epsilon)) (X.modulus (quarter epsilon))

def convergenceOuterRate (epsilon : Q') : Nat := X.modulus (quarter epsilon)

def convergenceInnerRate (epsilon : Q') (p : Nat) : Nat :=
  let k := X.convergencePivot epsilon
  max (X.regularReindex.convergenceOuterRate k)
    (X.bridge (quarter epsilon) p (X.phi k))

/-- Arbitrary-modulus represented convergence to the explicit diagonal.  Both
the outer and inner rates are data; no representative is extracted from a
quotient point. -/
theorem convergesToDiagonal (epsilon : Q') (he : (0 : Q') < epsilon)
    (p : Nat) (hp : X.convergenceOuterRate epsilon ≤ p)
    (n : Nat) (hn : X.convergenceInnerRate epsilon p ≤ n) :
    leEv (D.distSq ((X.pt p).seq n) (X.diagonal.seq n)) (ofQ' epsilon) := by
  let t := quarter epsilon
  let k := X.convergencePivot epsilon
  have ht : (0 : Q') < t := quarter_pos he
  have hkdiag : diagonalRate t ≤ k := Nat.le_max_left _ _
  have hkmod : X.modulus t ≤ k := Nat.le_max_right _ _
  have hphik : X.modulus t ≤ X.phi k :=
    Nat.le_trans hkmod (X.self_le_phi k)
  have hnreg : X.regularReindex.convergenceOuterRate k ≤ n :=
    Nat.le_trans (Nat.le_max_left _ _) hn
  have hnbridge : X.bridge t p (X.phi k) ≤ n :=
    Nat.le_trans (Nat.le_max_right _ _) hn
  have ha : leEv (D.distSq ((X.pt p).seq n) ((X.pt (X.phi k)).seq n)) (ofQ' t) :=
    X.cauchy t ht p (X.phi k) hp hphik n hnbridge
  have hb : leEv (D.distSq ((X.pt (X.phi k)).seq n) (X.diagonal.seq n)) (ofQ' t) :=
    X.regularReindex.convergesToDiagonal t ht k hkdiag n hnreg
  have htri := leEv_trans
    (D.distSq_triangle ((X.pt p).seq n) ((X.pt (X.phi k)).seq n) (X.diagonal.seq n))
    (leEv_add (leEv_add ha ha) (leEv_add hb hb))
  have hbudget : ((t + t) + (t + t)).eqv epsilon := by
    have hh : (t + t).eqv (HalfPow.half * epsilon) :=
      ExpNeg.two_halves (HalfPow.half * epsilon)
    exact Q'.eqv_trans _ _ _ (QPoly.q_add_congr hh hh) (ExpNeg.two_halves epsilon)
  exact leEv_trans htri (leEv_of_le (ofQ'_le_ofQ' (Q'.le_of_eqv hbudget)))

end GeneralPresentedCauchy

end YMGap.Continuum.CRealSeminormPresentedCompleteness

#print axioms YMGap.Continuum.CRealSeminormPresentedCompleteness.treeBudget_eqv_ten
#print axioms YMGap.Continuum.CRealSeminormPresentedCompleteness.diagonalRate_spec
#print axioms YMGap.Continuum.CRealSeminormPresentedCompleteness.PresentedCauchy.diagonal_cauchy_le
#print axioms YMGap.Continuum.CRealSeminormPresentedCompleteness.PresentedCauchy.diagonal
#print axioms YMGap.Continuum.CRealSeminormPresentedCompleteness.PresentedCauchy.diagonal_convergence_le
#print axioms YMGap.Continuum.CRealSeminormPresentedCompleteness.PresentedCauchy.convergesToDiagonal
#print axioms YMGap.Continuum.CRealSeminormPresentedCompleteness.GeneralPresentedCauchy.phi_mono
#print axioms YMGap.Continuum.CRealSeminormPresentedCompleteness.GeneralPresentedCauchy.regularReindex
#print axioms YMGap.Continuum.CRealSeminormPresentedCompleteness.GeneralPresentedCauchy.diagonal
#print axioms YMGap.Continuum.CRealSeminormPresentedCompleteness.GeneralPresentedCauchy.convergesToDiagonal
