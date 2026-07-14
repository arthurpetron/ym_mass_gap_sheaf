/-
# Exact Racah square on the stretched all-positive family

At maximal output degree `d = a+b+c`, both ordered trivalent trees have
contraction order zero.  Their unique intermediate labels are `a+b` and
`b+c`.  This file proves, for all natural `a,b,c`, that the two maps agree,
that the faithful dimension-absorbed Racah kernel is exactly one, and that
the collapsed signed factorial carrier satisfies the complete Racah square.

For positive `a,b,c` every external and intermediate label is positive, so
this is a genuinely interior infinite family rather than a zero-leg boundary.
-/

import YMGap.Continuum.SU2OrderedRightGramOrthogonality

namespace YMGap.Continuum.SU2OrderedRacahStretchedSquare

set_option maxHeartbeats 2400000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionBratteli
open YMGap.Continuum.TreeGraphBoundProgress
open YMGap.Continuum.SixJKernel
open YMGap.Continuum.SU2TransvectantLinearity
open YMGap.Continuum.SU2TransvectantGeneralCoefficient
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantMixedRecouplingGNSCompleted
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2OrderedRacahGuardedHahnCarrier
open YMGap.Continuum.SU2OrderedRacahCollapsedHahnCarrier
open YMGap.Continuum.SU2OrderedRacahInteriorSchurBridge
open YMGap.Continuum.SU2OrderedRightGramOrthogonality
open YMGap.Continuum.SU2TransvectantAllLabelGramCompleted
open YMGap.Continuum.SU2TransvectantAllLabelGNSIsometryCompleted

local infix:50 " ≈ " => Q'.eqv

def stretchedD (a b c : Nat) : Nat := a + b + c
def stretchedE (a b : Nat) : Nat := a + b
def stretchedF (b c : Nat) : Nat := b + c
def stretchedDen (a b c : Nat) : Nat := fact c * fact a * fact b

def stretchedRacahAmplitude (a b c : Nat) : Q' :=
  let T := stretchedD a b c
  ⟨(if T % 2 = 0 then (1 : Int) else -1) * Int.ofNat (fact (T + 1)),
    stretchedDen a b c - 1⟩

/-- The unique order-zero left channel at maximal output degree. -/
def stretchedLeftChannel (a b c : Nat) :
    FixedLeftCGChannel a b c (stretchedD a b c) where
  k := 0
  k_le := Nat.zero_le _
  r := 0
  r_le := Nat.zero_le _
  degree_eq := by unfold stretchedD; omega

/-- The unique order-zero right channel, repackaged with the same `stretchedD`. -/
def stretchedRightChannel' (a b c : Nat) :
    FixedRightCGChannel a b c (stretchedD a b c) := by
  simpa only [stretchedD] using stretchedRightChannel a b c

theorem stretched_intermediates (a b c : Nat) :
    (stretchedLeftChannel a b c).intermediate = stretchedE a b ∧
    (stretchedRightChannel' a b c).intermediate = stretchedF b c := by
  constructor <;> rfl

/-! ## One-term Racah evaluation -/

theorem stretched_valid6 (a b c : Nat) :
    valid6 a b c (stretchedD a b c) (stretchedE a b) (stretchedF b c) = true := by
  have hab : fusionOK a b (stretchedE a b) = true :=
    (fusionOK_iff_ladder a b (stretchedE a b)).2
      ⟨0, by omega, by omega, by unfold stretchedE; omega⟩
  have haDf : fusionOK a (stretchedD a b c) (stretchedF b c) = true :=
    (fusionOK_iff_ladder a (stretchedD a b c) (stretchedF b c)).2
      ⟨a, by omega, by unfold stretchedD; omega,
        by unfold stretchedD stretchedF; omega⟩
  have hcbf : fusionOK c b (stretchedF b c) = true :=
    (fusionOK_iff_ladder c b (stretchedF b c)).2
      ⟨0, by omega, by omega, by unfold stretchedF; omega⟩
  have hcDe : fusionOK c (stretchedD a b c) (stretchedE a b) = true :=
    (fusionOK_iff_ladder c (stretchedD a b c) (stretchedE a b)).2
      ⟨c, by omega, by unfold stretchedD; omega,
        by unfold stretchedD stretchedE; omega⟩
  unfold valid6
  simp only [hab, haDf, hcbf, hcDe, Bool.true_and]

theorem stretched_racah_parameters (a b c : Nat) :
    (a + b + stretchedE a b) / 2 = stretchedE a b ∧
    (a + stretchedD a b c + stretchedF b c) / 2 = stretchedD a b c ∧
    (c + b + stretchedF b c) / 2 = stretchedF b c ∧
    (c + stretchedD a b c + stretchedE a b) / 2 = stretchedD a b c ∧
    (a + b + c + stretchedD a b c) / 2 = stretchedD a b c ∧
    (b + stretchedE a b + stretchedD a b c + stretchedF b c) / 2 =
      a + 2 * b + c ∧
    (a + stretchedE a b + c + stretchedF b c) / 2 = stretchedD a b c := by
  unfold stretchedD stretchedE stretchedF
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

theorem stretched_tGuard_at_D (a b c : Nat) :
    tGuard (stretchedE a b) (stretchedD a b c) (stretchedF b c)
      (stretchedD a b c) (stretchedD a b c) (a + 2 * b + c)
      (stretchedD a b c) (stretchedD a b c) = true := by
  unfold tGuard stretchedD stretchedE stretchedF
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨?_, by omega⟩
  refine ⟨?_, by omega⟩
  refine ⟨?_, by omega⟩
  refine ⟨?_, by omega⟩
  refine ⟨?_, by omega⟩
  exact ⟨by omega, by omega⟩

theorem stretched_racahSummand_onehot (a b c t : Nat) :
    racahSummand
      ((a + b + stretchedE a b) / 2)
      ((a + stretchedD a b c + stretchedF b c) / 2)
      ((c + b + stretchedF b c) / 2)
      ((c + stretchedD a b c + stretchedE a b) / 2)
      ((a + b + c + stretchedD a b c) / 2)
      ((b + stretchedE a b + stretchedD a b c + stretchedF b c) / 2)
      ((a + stretchedE a b + c + stretchedF b c) / 2) t ≈
      (if t = stretchedD a b c then stretchedRacahAmplitude a b c else 0) := by
  have hp := stretched_racah_parameters a b c
  rw [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1,
    hp.2.2.2.2.1, hp.2.2.2.2.2.1, hp.2.2.2.2.2.2]
  by_cases ht : t = stretchedD a b c
  · subst t
    rw [if_pos rfl]
    unfold racahSummand
    rw [if_pos (stretched_tGuard_at_D a b c)]
    have h1 : stretchedD a b c - stretchedE a b = c := by
      unfold stretchedD stretchedE
      omega
    have h2 : stretchedD a b c - stretchedF b c = a := by
      unfold stretchedD stretchedF
      omega
    have h3 : a + 2 * b + c - stretchedD a b c = b := by
      unfold stretchedD
      omega
    unfold stretchedRacahAmplitude stretchedDen sevenFacts
    simp only [Nat.sub_self, fact, Nat.mul_one]
    rw [h1, h2, h3]
    exact Q'.eqv_refl _
  · rw [if_neg ht]
    unfold racahSummand
    rw [if_neg]
    · exact Q'.eqv_refl 0
    · intro hg
      unfold tGuard at hg
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
      exact ht (by omega)

theorem stretched_racahSum_eq_amplitude (a b c : Nat) :
    racahSum a b (stretchedE a b) c (stretchedD a b c)
        (stretchedF b c) ≈ stretchedRacahAmplitude a b c := by
  unfold racahSum
  have hcongr := finSum_eqv_congr _ _
    (fun t => stretched_racahSummand_onehot a b c t)
    ((a + b + stretchedE a b + c + stretchedD a b c + stretchedF b c) / 2 + 1)
  have hinside : stretchedD a b c <
      (a + b + stretchedE a b + c + stretchedD a b c + stretchedF b c) / 2 + 1 := by
    unfold stretchedD stretchedE stretchedF
    omega
  exact Q'.eqv_trans _ _ _ hcongr
    (YMGap.Continuum.SU2TransvectantGeneralCoefficient.finSum_onehot_value
      (stretchedRacahAmplitude a b c)
      ((a + b + stretchedE a b + c + stretchedD a b c + stretchedF b c) / 2 + 1)
      (stretchedD a b c) hinside)

/-! ## Exact factorial cancellation -/

private theorem mkN_den_of_pred (n d : Nat) (hd : 0 < d) :
    (Q'.mkN n (d - 1)).den = d := by
  change d - 1 + 1 = d
  omega

private theorem signed_den_of_pred (z : Int) (d : Nat) (hd : 0 < d) :
    ((⟨z, d - 1⟩ : Q').den) = d := by
  change d - 1 + 1 = d
  omega

theorem stretched_triSq_ab (a b : Nat) :
    triSq a b (stretchedE a b) =
      Q'.mkN (fact a * fact b) (fact (stretchedE a b + 1) - 1) := by
  have h1 : (a + b - stretchedE a b) / 2 = 0 := by
    unfold stretchedE
    omega
  have h2 : (a + stretchedE a b - b) / 2 = a := by
    unfold stretchedE
    omega
  have h3 : (b + stretchedE a b - a) / 2 = b := by
    unfold stretchedE
    omega
  have h4 : (a + b + stretchedE a b) / 2 + 1 = stretchedE a b + 1 := by
    unfold stretchedE
    omega
  unfold triSq triSqNum triSqDen
  rw [h1, h2, h3, h4]
  simp only [fact, Nat.one_mul]

theorem stretched_triSq_aDf (a b c : Nat) :
    triSq a (stretchedD a b c) (stretchedF b c) =
      Q'.mkN (fact a * fact (stretchedF b c))
        (fact (stretchedD a b c + 1) - 1) := by
  have h1 : (a + stretchedD a b c - stretchedF b c) / 2 = a := by
    unfold stretchedD stretchedF
    omega
  have h2 : (a + stretchedF b c - stretchedD a b c) / 2 = 0 := by
    unfold stretchedD stretchedF
    omega
  have h3 : (stretchedD a b c + stretchedF b c - a) / 2 = stretchedF b c := by
    unfold stretchedD stretchedF
    omega
  have h4 : (a + stretchedD a b c + stretchedF b c) / 2 + 1 =
      stretchedD a b c + 1 := by
    unfold stretchedD stretchedF
    omega
  unfold triSq triSqNum triSqDen
  rw [h1, h2, h3, h4]
  simp only [fact, Nat.mul_one]

theorem stretched_triSq_cb (b c : Nat) :
    triSq c b (stretchedF b c) =
      Q'.mkN (fact c * fact b) (fact (stretchedF b c + 1) - 1) := by
  have h1 : (c + b - stretchedF b c) / 2 = 0 := by
    unfold stretchedF
    omega
  have h2 : (c + stretchedF b c - b) / 2 = c := by
    unfold stretchedF
    omega
  have h3 : (b + stretchedF b c - c) / 2 = b := by
    unfold stretchedF
    omega
  have h4 : (c + b + stretchedF b c) / 2 + 1 = stretchedF b c + 1 := by
    unfold stretchedF
    omega
  unfold triSq triSqNum triSqDen
  rw [h1, h2, h3, h4]
  simp only [fact, Nat.one_mul]

theorem stretched_triSq_cDe (a b c : Nat) :
    triSq c (stretchedD a b c) (stretchedE a b) =
      Q'.mkN (fact c * fact (stretchedE a b))
        (fact (stretchedD a b c + 1) - 1) := by
  have h1 : (c + stretchedD a b c - stretchedE a b) / 2 = c := by
    unfold stretchedD stretchedE
    omega
  have h2 : (c + stretchedE a b - stretchedD a b c) / 2 = 0 := by
    unfold stretchedD stretchedE
    omega
  have h3 : (stretchedD a b c + stretchedE a b - c) / 2 = stretchedE a b := by
    unfold stretchedD stretchedE
    omega
  have h4 : (c + stretchedD a b c + stretchedE a b) / 2 + 1 =
      stretchedD a b c + 1 := by
    unfold stretchedD stretchedE
    omega
  unfold triSq triSqNum triSqDen
  rw [h1, h2, h3, h4]
  simp only [fact, Nat.mul_one]

private theorem stretched_factorial_product_cancel (a b c : Nat) :
    Q'.ofNat (stretchedE a b + 1) * Q'.ofNat (stretchedF b c + 1) *
      (Q'.mkN (fact a * fact b) (fact (stretchedE a b + 1) - 1) *
        Q'.mkN (fact a * fact (stretchedF b c))
          (fact (stretchedD a b c + 1) - 1) *
        Q'.mkN (fact c * fact b) (fact (stretchedF b c + 1) - 1) *
        Q'.mkN (fact c * fact (stretchedE a b))
          (fact (stretchedD a b c + 1) - 1)) *
      (stretchedRacahAmplitude a b c * stretchedRacahAmplitude a b c) ≈ 1 := by
  have hE : 0 < fact (stretchedE a b + 1) := fact_pos _
  have hF : 0 < fact (stretchedF b c + 1) := fact_pos _
  have hD : 0 < fact (stretchedD a b c + 1) := fact_pos _
  have hA : 0 < stretchedDen a b c := by
    unfold stretchedDen
    exact Nat.mul_pos (Nat.mul_pos (fact_pos _) (fact_pos _)) (fact_pos _)
  unfold stretchedRacahAmplitude
  show _ * ((1 : Q').den : Int) = (1 : Q').num * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast, Int.mul_one, Int.one_mul]
  rw [mkN_den_of_pred (fact a * fact b) _ hE,
    mkN_den_of_pred (fact c * fact b) _ hF,
    mkN_den_of_pred (fact a * fact (stretchedF b c)) _ hD,
    mkN_den_of_pred (fact c * fact (stretchedE a b)) _ hD,
    signed_den_of_pred _ _ hA]
  simp only [Q'.mkN, fact]
  unfold stretchedDen stretchedE stretchedF
  by_cases hpar : stretchedD a b c % 2 = 0
  · rw [if_pos hpar]
    unfold stretchedD
    push_cast
    simp only [Int.one_mul, Int.ofNat_eq_natCast, Int.natCast_mul,
      Int.natCast_add, Int.natCast_one]
    ac_rfl
  · rw [if_neg hpar]
    unfold stretchedD
    push_cast
    simp only [Int.neg_mul, Int.mul_neg, Int.neg_neg, Int.one_mul,
      Int.ofNat_eq_natCast, Int.natCast_mul, Int.natCast_add, Int.natCast_one]
    ac_rfl

/-- The faithful squared Racah kernel is exactly one on every stretched
tetrahedron `{a,b,a+b; c,a+b+c,b+c}`. -/
theorem stretched_racahKernel_eq_one (a b c : Nat) :
    racahKernel6 a b c (stretchedD a b c) (stretchedE a b)
        (stretchedF b c) ≈ 1 := by
  unfold racahKernel6
  rw [if_pos (stretched_valid6 a b c)]
  have hsum := stretched_racahSum_eq_amplitude a b c
  have hprod :
      racahSum a b (stretchedE a b) c (stretchedD a b c) (stretchedF b c) *
          racahSum a b (stretchedE a b) c (stretchedD a b c) (stretchedF b c) ≈
        stretchedRacahAmplitude a b c * stretchedRacahAmplitude a b c := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hsum)
      (Q'.mul_eqv_congr_left _ _ _ hsum)
  rw [show dimRep (stretchedE a b) = stretchedE a b + 1 by rfl,
    show dimRep (stretchedF b c) = stretchedF b c + 1 by rfl,
    stretched_triSq_ab a b, stretched_triSq_aDf a b c,
    stretched_triSq_cb b c, stretched_triSq_cDe a b c]
  refine Q'.eqv_trans _
    (Q'.ofNat (stretchedE a b + 1) * Q'.ofNat (stretchedF b c + 1) *
      (Q'.mkN (fact a * fact b) (fact (stretchedE a b + 1) - 1) *
        Q'.mkN (fact a * fact (stretchedF b c))
          (fact (stretchedD a b c + 1) - 1) *
        Q'.mkN (fact c * fact b) (fact (stretchedF b c + 1) - 1) *
        Q'.mkN (fact c * fact (stretchedE a b))
          (fact (stretchedD a b c + 1) - 1)) *
      (stretchedRacahAmplitude a b c * stretchedRacahAmplitude a b c)) _ ?_
    (stretched_factorial_product_cancel a b c)
  exact Q'.mul_eqv_congr_left _ _ _ hprod

/-! ## Equality of the two order-zero trivalent trees -/

theorem stretched_triLeft_coefficient (a b c i j k s : Nat) :
    triLeft a b c (stretchedD a b c) (stretchedE a b)
        (mono i) (mono j) (mono k) s ≈
      (if s = (i + j) + k then (1 : Q') else 0) := by
  have hin : couplingOrder a b (stretchedE a b) = 0 := by
    unfold couplingOrder stretchedE
    omega
  have hout : couplingOrder (stretchedE a b) c (stretchedD a b c) = 0 := by
    unfold couplingOrder stretchedE stretchedD
    omega
  have htprod : BForm2Eqv
      (tprod (transvect a b 0 (tprod (mono i) (mono j))) (mono k))
      (tprod (mono (i + j)) (mono k)) := by
    intro x y
    exact Q'.mul_eqv_congr_right _ _ _
      (by simpa only [mono] using transvect_zero_monomial a b i j x)
  unfold triLeft
  rw [hin, hout]
  exact Q'.eqv_trans _ _ _
    (transvect_congr (stretchedE a b) c 0 htprod s)
    (by simpa using transvect_zero_monomial (stretchedE a b) c (i + j) k s)

theorem stretched_triRight_coefficient (a b c i j k s : Nat) :
    triRight a b c (stretchedD a b c) (stretchedF b c)
        (mono i) (mono j) (mono k) s ≈
      (if s = i + (j + k) then (1 : Q') else 0) := by
  have hin : couplingOrder b c (stretchedF b c) = 0 := by
    unfold couplingOrder stretchedF
    omega
  have hout : couplingOrder a (stretchedF b c) (stretchedD a b c) = 0 := by
    unfold couplingOrder stretchedF stretchedD
    omega
  have htprod : BForm2Eqv
      (tprod (mono i) (transvect b c 0 (tprod (mono j) (mono k))))
      (tprod (mono i) (mono (j + k))) := by
    intro x y
    exact Q'.mul_eqv_congr_left _ _ _
      (by simpa only [mono] using transvect_zero_monomial b c j k y)
  unfold triRight
  rw [hin, hout]
  exact Q'.eqv_trans _ _ _
    (transvect_congr a (stretchedF b c) 0 htprod s)
    (by simpa using transvect_zero_monomial a (stretchedF b c) i (j + k) s)

/-- At maximal output degree the two bracketings are literally the same
ordinary polynomial product on the complete physical monomial box. -/
theorem stretched_triMaps_eqv (a b c : Nat) :
    TriMapEqv a b c (stretchedD a b c)
      (triLeft a b c (stretchedD a b c) (stretchedE a b))
      (triRight a b c (stretchedD a b c) (stretchedF b c)) := by
  intro i hi j hj k hk s hs
  refine Q'.eqv_trans _ (if s = (i + j) + k then (1 : Q') else 0) _
    (stretched_triLeft_coefficient a b c i j k s) ?_
  rw [Nat.add_assoc]
  exact Q'.eqv_symm (stretched_triRight_coefficient a b c i j k s)

/-- The two derived invariant Gram weights coincide on the stretched family. -/
theorem stretched_channel_weights_eq (a b c : Nat) :
    triLeftChannelWeight a b c (stretchedD a b c) (stretchedE a b) ≈
      triRightChannelWeight a b c (stretchedD a b c) (stretchedF b c) := by
  exact triMapInner_diagonal_congr_all_labels a b c (stretchedD a b c)
    (triLeft a b c (stretchedD a b c) (stretchedE a b))
    (triRight a b c (stretchedD a b c) (stretchedF b c))
    (stretched_triMaps_eqv a b c)

/-- The collapsed signed threefold carrier is the common stretched Gram
weight.  This uses the already-derived factorial carrier identity, followed
only by the order-zero map identity above. -/
theorem stretched_collapsed_cross_eq_right_weight (a b c : Nat) :
    collapsedFactorialCrossSum (stretchedLeftChannel a b c)
        (stretchedRightChannel' a b c) ≈
      triRightChannelWeight a b c (stretchedD a b c) (stretchedF b c) := by
  refine Q'.eqv_trans _
    (triCrossChannelWeight (stretchedLeftChannel a b c)
      (stretchedRightChannel' a b c)) _
    (Q'.eqv_symm (triCrossChannelWeight_eq_collapsedFactorialCrossSum
      (stretchedLeftChannel a b c) (stretchedRightChannel' a b c))) ?_
  change triMapInner a b c (stretchedD a b c)
      (triLeft a b c (stretchedD a b c) (stretchedE a b))
      (triRight a b c (stretchedD a b c) (stretchedF b c)) ≈
    triMapInner a b c (stretchedD a b c)
      (triRight a b c (stretchedD a b c) (stretchedF b c))
      (triRight a b c (stretchedD a b c) (stretchedF b c))
  exact triMapInner_congr_left (stretched_triMaps_eqv a b c)

/-- **Complete collapsed Racah square on the three-parameter stretched
family.**  In particular, restricting to `0<a,0<b,0<c` gives an infinite
family with every external and intermediate label strictly positive. -/
theorem stretched_collapsedRacahSquare (a b c : Nat) :
    CollapsedRacahSquareAt (stretchedLeftChannel a b c)
      (stretchedRightChannel' a b c) := by
  unfold CollapsedRacahSquareAt
  change
    collapsedFactorialCrossSum (stretchedLeftChannel a b c)
          (stretchedRightChannel' a b c) *
        collapsedFactorialCrossSum (stretchedLeftChannel a b c)
          (stretchedRightChannel' a b c) ≈
      triLeftChannelWeight a b c (stretchedD a b c) (stretchedE a b) *
        (triRightChannelWeight a b c (stretchedD a b c) (stretchedF b c) *
          racahKernel6 a b c (stretchedD a b c) (stretchedE a b)
            (stretchedF b c))
  let W := triRightChannelWeight a b c (stretchedD a b c) (stretchedF b c)
  have hC := stretched_collapsed_cross_eq_right_weight a b c
  have hW := stretched_channel_weights_eq a b c
  have hP := stretched_racahKernel_eq_one a b c
  have hleft :
      collapsedFactorialCrossSum (stretchedLeftChannel a b c)
          (stretchedRightChannel' a b c) *
        collapsedFactorialCrossSum (stretchedLeftChannel a b c)
          (stretchedRightChannel' a b c) ≈ W * W := by
    exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hC)
      (Q'.mul_eqv_congr_left _ _ _ hC)
  refine Q'.eqv_trans _ _ _ hleft ?_
  refine Q'.eqv_trans _
    (triLeftChannelWeight a b c (stretchedD a b c) (stretchedE a b) * W) _
    (Q'.mul_eqv_congr_right W _ W (Q'.eqv_symm hW)) ?_
  exact Q'.mul_eqv_congr_left _ _ _
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_one_eqv W))
      (Q'.mul_eqv_congr_left W 1 _ (Q'.eqv_symm hP)))

theorem stretched_labels_positive {a b c : Nat}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 < stretchedD a b c ∧ 0 < stretchedE a b ∧ 0 < stretchedF b c := by
  unfold stretchedD stretchedE stretchedF
  omega

end YMGap.Continuum.SU2OrderedRacahStretchedSquare

#print axioms YMGap.Continuum.SU2OrderedRacahStretchedSquare.stretched_valid6
#print axioms YMGap.Continuum.SU2OrderedRacahStretchedSquare.stretched_racah_parameters
#print axioms YMGap.Continuum.SU2OrderedRacahStretchedSquare.stretched_tGuard_at_D
#print axioms YMGap.Continuum.SU2OrderedRacahStretchedSquare.stretched_racahSummand_onehot
#print axioms YMGap.Continuum.SU2OrderedRacahStretchedSquare.stretched_racahSum_eq_amplitude
#print axioms YMGap.Continuum.SU2OrderedRacahStretchedSquare.stretched_racahKernel_eq_one
#print axioms YMGap.Continuum.SU2OrderedRacahStretchedSquare.stretched_triMaps_eqv
#print axioms YMGap.Continuum.SU2OrderedRacahStretchedSquare.stretched_channel_weights_eq
#print axioms YMGap.Continuum.SU2OrderedRacahStretchedSquare.stretched_collapsed_cross_eq_right_weight
#print axioms YMGap.Continuum.SU2OrderedRacahStretchedSquare.stretched_collapsedRacahSquare
