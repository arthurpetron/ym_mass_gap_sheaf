/-
# The first two-term near-stretched Racah family

Put `n=u+4` and consider external labels `(n,2,n)`, final label
`2n-4`, and the left/right channels whose two contraction orders are all
one.  Both intermediate labels are `n`.  The Racah support is exactly the
two adjacent indices `2n-1,2n`; their signed sum telescopes to one exact
factorial amplitude, and the dimension-absorbed squared kernel is

  `u^2 / (u+6)^2`.

All labels are strictly positive and all four contractions are nonzero.
-/

import YMGap.Continuum.SU2OrderedRacahStretchedSquare

namespace YMGap.Continuum.SU2OrderedRacahNearStretchedTwoTerm

set_option maxHeartbeats 3000000
set_option maxRecDepth 24000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionBratteli
open YMGap.Continuum.TreeGraphBoundProgress
open YMGap.Continuum.SixJKernel
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2OrderedRacahCollapsedHahnCarrier

local infix:50 " ≈ " => Q'.eqv

def nearN (u : Nat) : Nat := u + 4
def nearD (u : Nat) : Nat := 2 * u + 6
def nearT0 (u : Nat) : Nat := 2 * u + 7
def nearT1 (u : Nat) : Nat := 2 * u + 8

def nearTerm0 (u : Nat) : Q' :=
  ⟨-Int.ofNat (fact (nearT1 u)), fact (u + 2) * fact (u + 2) - 1⟩

def nearTerm1 (u : Nat) : Q' :=
  Q'.mkN (fact (2 * u + 9)) (fact (u + 3) * fact (u + 3) - 1)

def nearRacahAmplitude (u : Nat) : Q' :=
  ⟨-Int.ofNat (u * (u + 4) * fact (2 * u + 8)),
    fact (u + 3) * fact (u + 3) - 1⟩

def nearKernelClosed (u : Nat) : Q' :=
  Q'.mkN (u * u) ((u + 6) * (u + 6) - 1)

def nearLeftChannel (u : Nat) :
    FixedLeftCGChannel (nearN u) 2 (nearN u) (nearD u) where
  k := 1
  k_le := by unfold nearN; omega
  r := 1
  r_le := by unfold nearN; omega
  degree_eq := by unfold nearN nearD; omega

def nearRightChannel (u : Nat) :
    FixedRightCGChannel (nearN u) 2 (nearN u) (nearD u) where
  p := 1
  p_le := by unfold nearN; omega
  r := 1
  r_le := by unfold nearN; omega
  degree_eq := by unfold nearN nearD; omega

theorem near_intermediates (u : Nat) :
    (nearLeftChannel u).intermediate = nearN u ∧
    (nearRightChannel u).intermediate = nearN u := by
  constructor
  · change nearN u + 2 - 2 * 1 = nearN u
    unfold nearN
    omega
  · change 2 + nearN u - 2 * 1 = nearN u
    unfold nearN
    omega

/-! ## Physical guard and exact two-point support -/

theorem near_valid6 (u : Nat) :
    valid6 (nearN u) 2 (nearN u) (nearD u) (nearN u) (nearN u) = true := by
  have hsmall : fusionOK (nearN u) 2 (nearN u) = true :=
    (fusionOK_iff_ladder (nearN u) 2 (nearN u)).2
      ⟨1, by unfold nearN; omega, by omega, by unfold nearN; omega⟩
  have hlarge : fusionOK (nearN u) (nearD u) (nearN u) = true :=
    (fusionOK_iff_ladder (nearN u) (nearD u) (nearN u)).2
      ⟨u + 3, by unfold nearN; omega, by unfold nearD; omega,
        by unfold nearN nearD; omega⟩
  unfold valid6
  simp only [hsmall, hlarge, Bool.true_and]

theorem near_racah_parameters (u : Nat) :
    (nearN u + 2 + nearN u) / 2 = u + 5 ∧
    (nearN u + nearD u + nearN u) / 2 = nearT0 u ∧
    (nearN u + 2 + nearN u) / 2 = u + 5 ∧
    (nearN u + nearD u + nearN u) / 2 = nearT0 u ∧
    (nearN u + 2 + nearN u + nearD u) / 2 = nearT1 u ∧
    (2 + nearN u + nearD u + nearN u) / 2 = nearT1 u ∧
    (nearN u + nearN u + nearN u + nearN u) / 2 = nearT1 u := by
  unfold nearN nearD nearT0 nearT1
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor <;> omega

theorem near_tGuard_at_T0 (u : Nat) :
    tGuard (u + 5) (nearT0 u) (u + 5) (nearT0 u)
      (nearT1 u) (nearT1 u) (nearT1 u) (nearT0 u) = true := by
  unfold tGuard nearT0 nearT1
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨?_, by omega⟩
  refine ⟨?_, by omega⟩
  refine ⟨?_, by omega⟩
  refine ⟨?_, by omega⟩
  refine ⟨?_, by omega⟩
  exact ⟨by omega, by omega⟩

theorem near_tGuard_at_T1 (u : Nat) :
    tGuard (u + 5) (nearT0 u) (u + 5) (nearT0 u)
      (nearT1 u) (nearT1 u) (nearT1 u) (nearT1 u) = true := by
  unfold tGuard nearT0 nearT1
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨?_, by omega⟩
  refine ⟨?_, by omega⟩
  refine ⟨?_, by omega⟩
  refine ⟨?_, by omega⟩
  refine ⟨?_, by omega⟩
  exact ⟨by omega, by omega⟩

theorem near_racahSummand_twohot (u t : Nat) :
    racahSummand
      ((nearN u + 2 + nearN u) / 2)
      ((nearN u + nearD u + nearN u) / 2)
      ((nearN u + 2 + nearN u) / 2)
      ((nearN u + nearD u + nearN u) / 2)
      ((nearN u + 2 + nearN u + nearD u) / 2)
      ((2 + nearN u + nearD u + nearN u) / 2)
      ((nearN u + nearN u + nearN u + nearN u) / 2) t ≈
      (if t = nearT0 u then nearTerm0 u else 0) +
        (if t = nearT1 u then nearTerm1 u else 0) := by
  have hp := near_racah_parameters u
  rw [hp.1, hp.2.1, hp.2.2.2.2.1,
    hp.2.2.2.2.2.1, hp.2.2.2.2.2.2]
  by_cases h0 : t = nearT0 u
  · subst t
    rw [if_pos rfl, if_neg (by unfold nearT0 nearT1; omega)]
    unfold racahSummand
    rw [if_pos (near_tGuard_at_T0 u)]
    have h1 : nearT0 u - (u + 5) = u + 2 := by
      unfold nearT0
      omega
    have h2 : nearT1 u - nearT0 u = 1 := by
      unfold nearT0 nearT1
      omega
    have hpar : nearT0 u % 2 = 1 := by
      unfold nearT0
      omega
    unfold sevenFacts
    rw [hpar]
    simp only [Nat.sub_self, h1, h2]
    have ht : fact (nearT1 u) = (nearT0 u + 1) * fact (nearT0 u) := by
      rw [show nearT1 u = nearT0 u + 1 by unfold nearT0 nearT1; omega]
      rfl
    rw [show fact 0 = 1 by rfl, show fact 1 = 1 by rfl]
    simp only [Nat.mul_one]
    refine Q'.eqv_trans _ (nearTerm0 u) _ ?_
      (Q'.eqv_symm (Q'.eqv_of_eq (Q'.add_zero' (nearTerm0 u))))
    unfold nearTerm0
    show _ * (_ : Int) = _ * (_ : Int)
    rw [ht]
    rw [show fact (nearT0 u + 1) = (nearT0 u + 1) * fact (nearT0 u) by rfl]
    simp only [Q'.den]
    push_cast
    simp only [Int.mul_neg, Int.neg_mul, Int.mul_one]
    ac_rfl
  · by_cases h1t : t = nearT1 u
    · subst t
      rw [if_neg (by unfold nearT0 nearT1; omega), if_pos rfl]
      unfold racahSummand
      rw [if_pos (near_tGuard_at_T1 u)]
      have h1 : nearT1 u - (u + 5) = u + 3 := by
        unfold nearT1
        omega
      have h2 : nearT1 u - nearT0 u = 1 := by
        unfold nearT0 nearT1
        omega
      have hpar : nearT1 u % 2 = 0 := by
        unfold nearT1
        omega
      unfold sevenFacts
      rw [hpar]
      simp only [Nat.sub_self, h1, h2]
      rw [show fact 0 = 1 by rfl, show fact 1 = 1 by rfl]
      simp only [Nat.mul_one]
      refine Q'.eqv_trans _ (nearTerm1 u) _ ?_
        (Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' (nearTerm1 u))))
      unfold nearTerm1 Q'.mkN
      show _ * (_ : Int) = _ * (_ : Int)
      rw [show nearT1 u + 1 = 2 * u + 9 by unfold nearT1; omega]
      simp only [Q'.den]
      ac_rfl
    · rw [if_neg h0, if_neg h1t]
      unfold racahSummand
      rw [if_neg]
      · exact Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' 0))
      · intro hg
        unfold tGuard at hg
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
        have : t = nearT0 u ∨ t = nearT1 u := by
          unfold nearT0 nearT1 at *
          omega
        exact this.elim h0 h1t

private theorem mkN_den_of_pred (n d : Nat) (hd : 0 < d) :
    (Q'.mkN n (d - 1)).den = d := by
  change d - 1 + 1 = d
  omega

private theorem signed_den_of_pred (z : Int) (d : Nat) (hd : 0 < d) :
    ((⟨z, d - 1⟩ : Q').den) = d := by
  change d - 1 + 1 = d
  omega

private theorem fact_u3 (u : Nat) :
    fact (u + 3) = (u + 3) * fact (u + 2) := by
  rw [show u + 3 = (u + 2) + 1 by omega]
  rfl

private theorem fact_2u9 (u : Nat) :
    fact (2 * u + 9) = (2 * u + 9) * fact (2 * u + 8) := by
  rw [show 2 * u + 9 = (2 * u + 8) + 1 by omega]
  rfl

private theorem fact_u6 (u : Nat) :
    fact (u + 6) = (u + 6) * (u + 5) * (u + 4) * fact (u + 3) := by
  rw [show u + 6 = (u + 5) + 1 by omega]
  change (u + 6) * fact (u + 5) = _
  rw [show u + 5 = (u + 4) + 1 by omega]
  change (u + 6) * ((u + 5) * fact (u + 4)) = _
  rw [show u + 4 = (u + 3) + 1 by omega]
  change (u + 6) * ((u + 5) * ((u + 4) * fact (u + 3))) = _
  simp only [show u + 3 + 1 = u + 4 by omega,
    show u + 4 + 1 = u + 5 by omega,
    show u + 5 + 1 = u + 6 by omega]
  ac_rfl

private theorem near_int_telescope (u : Nat) (F G : Int) :
    -F * (((u : Int) + 3) * G * (((u : Int) + 3) * G)) +
        ((2 * (u : Int) + 9) * F) * (G * G) =
      -((u : Int) * ((u : Int) + 4) * F) * (G * G) := by
  have hpoly :
      (2 * (u : Int) + 9) - ((u : Int) + 3) * ((u : Int) + 3) =
        -((u : Int) * ((u : Int) + 4)) := by
    simp only [Int.sub_eq_add_neg, Int.add_mul, Int.mul_add, Int.neg_add]
    omega
  have hneg :
      -F * (((u : Int) + 3) * G * (((u : Int) + 3) * G)) =
        (F * (G * G)) * (-(((u : Int) + 3) * ((u : Int) + 3))) := by
    simp only [Int.mul_neg, Int.neg_mul]
    ac_rfl
  have hpos :
      ((2 * (u : Int) + 9) * F) * (G * G) =
        (F * (G * G)) * (2 * (u : Int) + 9) := by
    ac_rfl
  calc
    _ = (F * (G * G)) * (-(((u : Int) + 3) * ((u : Int) + 3))) +
        (F * (G * G)) * (2 * (u : Int) + 9) := by rw [hneg, hpos]
    _ = (F * (G * G)) *
        (-(((u : Int) + 3) * ((u : Int) + 3)) +
          (2 * (u : Int) + 9)) :=
      (Int.mul_add (F * (G * G))
        (-(((u : Int) + 3) * ((u : Int) + 3)))
        (2 * (u : Int) + 9)).symm
    _ = F * (G * G) *
        ((2 * (u : Int) + 9) - ((u : Int) + 3) * ((u : Int) + 3)) := by
      congr 1
    _ = F * (G * G) * (-((u : Int) * ((u : Int) + 4))) := by rw [hpoly]
    _ = _ := by simp only [Int.mul_neg, Int.neg_mul]; ac_rfl

theorem near_terms_telescope (u : Nat) :
    nearTerm0 u + nearTerm1 u ≈ nearRacahAmplitude u := by
  have h2 : 0 < fact (u + 2) * fact (u + 2) :=
    Nat.mul_pos (fact_pos _) (fact_pos _)
  have h3 : 0 < fact (u + 3) * fact (u + 3) :=
    Nat.mul_pos (fact_pos _) (fact_pos _)
  unfold nearTerm0 nearTerm1 nearRacahAmplitude nearT1
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.add_num_cast, Q'.add_den_cast,
    Int.neg_mul, Int.mul_neg, Int.neg_neg]
  rw [signed_den_of_pred _ _ h2, mkN_den_of_pred _ _ h3,
    signed_den_of_pred _ _ h3]
  simp only [Q'.mkN]
  rw [fact_u3 u, fact_2u9 u]
  push_cast
  simp only [Int.natCast_mul, Int.natCast_add, Int.ofNat_eq_natCast]
  have hu3 : (u : Int) + 1 + 1 + 1 = (u : Int) + 3 := by omega
  have hcast2 : ((2 : Nat) : Int) = 2 := rfl
  have hcast9 : ((9 : Nat) : Int) = 9 := rfl
  have hcast4 : ((4 : Nat) : Int) = 4 := rfl
  rw [hu3, hcast2, hcast9, hcast4]
  have hnum :
      -(↑(fact (2 * u + 8)) *
          (((u : Int) + 3) * ↑(fact (u + 2)) *
            (((u : Int) + 3) * ↑(fact (u + 2))))) +
        (2 * (u : Int) + 9) * ↑(fact (2 * u + 8)) *
          (↑(fact (u + 2)) * ↑(fact (u + 2))) =
      -((u : Int) * ((u : Int) + 4) * ↑(fact (2 * u + 8))) *
        (↑(fact (u + 2)) * ↑(fact (u + 2))) := by
    refine Eq.trans ?_ (near_int_telescope u (fact (2 * u + 8) : Int)
      (fact (u + 2) : Int))
    simp only [Int.neg_mul]
  rw [hnum]
  simp only [Int.neg_mul, Int.mul_neg]
  ac_rfl

theorem near_racahSum_eq_amplitude (u : Nat) :
    racahSum (nearN u) 2 (nearN u) (nearN u) (nearD u) (nearN u) ≈
      nearRacahAmplitude u := by
  unfold racahSum
  let N :=
    (nearN u + 2 + nearN u + nearN u + nearD u + nearN u) / 2 + 1
  have hcongr := finSum_eqv_congr _ _
    (fun t => near_racahSummand_twohot u t) N
  have h0 : nearT0 u < N := by
    unfold N nearN nearD nearT0
    omega
  have h1 : nearT1 u < N := by
    unfold N nearN nearD nearT1
    omega
  have hsum0 :=
    YMGap.Continuum.SU2TransvectantGeneralCoefficient.finSum_onehot_value
      (nearTerm0 u) N (nearT0 u) h0
  have hsum1 :=
    YMGap.Continuum.SU2TransvectantGeneralCoefficient.finSum_onehot_value
      (nearTerm1 u) N (nearT1 u) h1
  refine Q'.eqv_trans _ _ _ hcongr ?_
  refine Q'.eqv_trans _
    (finSum (fun t => if t = nearT0 u then nearTerm0 u else 0) N +
      finSum (fun t => if t = nearT1 u then nearTerm1 u else 0) N) _
    (finSum_add _ _ N) ?_
  exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hsum0 hsum1)
    (near_terms_telescope u)

/-! ## Triangle factors and exact kernel cancellation -/

theorem near_triSq_small (u : Nat) :
    triSq (nearN u) 2 (nearN u) =
      Q'.mkN (fact (u + 3)) (fact (u + 6) - 1) := by
  have h1 : (nearN u + 2 - nearN u) / 2 = 1 := by
    unfold nearN
    omega
  have h2 : (nearN u + nearN u - 2) / 2 = u + 3 := by
    unfold nearN
    omega
  have h3 : (2 + nearN u - nearN u) / 2 = 1 := by
    unfold nearN
    omega
  have h4 : (nearN u + 2 + nearN u) / 2 + 1 = u + 6 := by
    unfold nearN
    omega
  unfold triSq triSqNum triSqDen
  rw [h1, h2, h3, h4]
  simp only [fact, Nat.zero_add, Nat.one_mul, Nat.mul_one]

theorem near_triSq_large (u : Nat) :
    triSq (nearN u) (nearD u) (nearN u) =
      Q'.mkN (fact (u + 3) * fact (u + 3))
        (fact (2 * u + 8) - 1) := by
  have h1 : (nearN u + nearD u - nearN u) / 2 = u + 3 := by
    unfold nearN nearD
    omega
  have h2 : (nearN u + nearN u - nearD u) / 2 = 1 := by
    unfold nearN nearD
    omega
  have h3 : (nearD u + nearN u - nearN u) / 2 = u + 3 := by
    unfold nearN nearD
    omega
  have h4 : (nearN u + nearD u + nearN u) / 2 + 1 = 2 * u + 8 := by
    unfold nearN nearD
    omega
  unfold triSq triSqNum triSqDen
  rw [h1, h2, h3, h4]
  simp only [fact, Nat.zero_add, Nat.one_mul, Nat.mul_one]

private theorem near_factorial_product_cancel (u : Nat) :
    Q'.ofNat (u + 5) * Q'.ofNat (u + 5) *
      (Q'.mkN (fact (u + 3)) (fact (u + 6) - 1) *
        Q'.mkN (fact (u + 3) * fact (u + 3))
          (fact (2 * u + 8) - 1) *
        Q'.mkN (fact (u + 3)) (fact (u + 6) - 1) *
        Q'.mkN (fact (u + 3) * fact (u + 3))
          (fact (2 * u + 8) - 1)) *
      (nearRacahAmplitude u * nearRacahAmplitude u) ≈ nearKernelClosed u := by
  have h6 : 0 < fact (u + 6) := fact_pos _
  have h8 : 0 < fact (2 * u + 8) := fact_pos _
  have h3 : 0 < fact (u + 3) * fact (u + 3) :=
    Nat.mul_pos (fact_pos _) (fact_pos _)
  have hk : 0 < (u + 6) * (u + 6) := Nat.mul_pos (by omega) (by omega)
  unfold nearRacahAmplitude nearKernelClosed
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast, Int.mul_one]
  rw [mkN_den_of_pred (fact (u + 3)) _ h6,
    mkN_den_of_pred (fact (u + 3) * fact (u + 3)) _ h8,
    signed_den_of_pred _ _ h3, mkN_den_of_pred _ _ hk]
  simp only [Q'.mkN]
  rw [fact_u6 u]
  push_cast
  simp only [Int.natCast_mul, Int.natCast_add,
    Int.ofNat_eq_natCast, Int.neg_mul, Int.mul_neg, Int.neg_neg]
  have hu4 : (u : Int) + 1 + 1 + 1 + 1 = (u : Int) + 4 := by omega
  have hu5 : (u : Int) + 4 + 1 = (u : Int) + 5 := by omega
  have hu6 : (u : Int) + 5 + 1 = (u : Int) + 6 := by omega
  have hcast4 : ((4 : Nat) : Int) = 4 := rfl
  rw [hu4, hu5, hu6, hcast4]
  ac_rfl

/-- **First genuinely two-term symbolic Racah kernel.** -/
theorem near_racahKernel_closed (u : Nat) :
    racahKernel6 (nearN u) 2 (nearN u) (nearD u) (nearN u) (nearN u) ≈
      nearKernelClosed u := by
  unfold racahKernel6
  rw [if_pos (near_valid6 u)]
  have hsum := near_racahSum_eq_amplitude u
  have hprod :
      racahSum (nearN u) 2 (nearN u) (nearN u) (nearD u) (nearN u) *
          racahSum (nearN u) 2 (nearN u) (nearN u) (nearD u) (nearN u) ≈
        nearRacahAmplitude u * nearRacahAmplitude u := by
    exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hsum)
      (Q'.mul_eqv_congr_left _ _ _ hsum)
  rw [show dimRep (nearN u) = u + 5 by unfold dimRep nearN; omega,
    near_triSq_small u, near_triSq_large u]
  refine Q'.eqv_trans _
    (Q'.ofNat (u + 5) * Q'.ofNat (u + 5) *
      (Q'.mkN (fact (u + 3)) (fact (u + 6) - 1) *
        Q'.mkN (fact (u + 3) * fact (u + 3))
          (fact (2 * u + 8) - 1) *
        Q'.mkN (fact (u + 3)) (fact (u + 6) - 1) *
        Q'.mkN (fact (u + 3) * fact (u + 3))
          (fact (2 * u + 8) - 1)) *
      (nearRacahAmplitude u * nearRacahAmplitude u)) _ ?_
    (near_factorial_product_cancel u)
  exact Q'.mul_eqv_congr_left _ _ _ hprod

end YMGap.Continuum.SU2OrderedRacahNearStretchedTwoTerm

#print axioms YMGap.Continuum.SU2OrderedRacahNearStretchedTwoTerm.near_valid6
#print axioms YMGap.Continuum.SU2OrderedRacahNearStretchedTwoTerm.near_racahSummand_twohot
#print axioms YMGap.Continuum.SU2OrderedRacahNearStretchedTwoTerm.near_terms_telescope
#print axioms YMGap.Continuum.SU2OrderedRacahNearStretchedTwoTerm.near_racahSum_eq_amplitude
#print axioms YMGap.Continuum.SU2OrderedRacahNearStretchedTwoTerm.near_racahKernel_closed
