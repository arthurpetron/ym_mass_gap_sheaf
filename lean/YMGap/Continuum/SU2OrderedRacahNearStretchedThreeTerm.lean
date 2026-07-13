/-
# The first all-positive three-term near-stretched Racah family

The middle-label-three support fence shows that the next all-positive family
cannot yet have three summands.  The first symmetric choice that does is

  `(a,b,c;d;e,f) = (n,4,n; 2n-4; n,n)`,  with `n=u+8`.

All four contraction orders are two.  The Racah support consists exactly of
the three adjacent indices `2n-2,2n-1,2n`.  Its signed factorial sum reduces
to a quartic amplitude, and the dimension/triangle cancellation gives the
exact squared kernel

  `((u^3-u^2-124u-452) / ((u+8)(u+10)(u+11)))^2`.
-/

import YMGap.Continuum.SU2OrderedRacahMiddleThreeFence
import YMGap.Continuum.IntRingNormaliser

namespace YMGap.Continuum.SU2OrderedRacahNearStretchedThreeTerm

set_option maxHeartbeats 1000000
set_option maxRecDepth 28000

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

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul,
               Int.mul_add, Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg,
               Int.one_mul, Int.mul_one, Int.zero_mul, Int.mul_zero,
               Int.add_zero, Int.zero_add] <;> ac_rfl))

def threeN (u : Nat) : Nat := u + 8
def threeD (u : Nat) : Nat := 2 * u + 12
def threeT0 (u : Nat) : Nat := 2 * u + 14
def threeT1 (u : Nat) : Nat := 2 * u + 15
def threeT2 (u : Nat) : Nat := 2 * u + 16

/-- The cubic numerator of the signed inverse coefficient. -/
def threeCoeffNum (u : Nat) : Int :=
  let U : Int := Int.ofNat u
  U * U * U - U * U - 124 * U - 452

/-- The factored quartic appearing before triangle cancellation. -/
def threeQuartic (u : Nat) : Int :=
  (Int.ofNat u + 7) * threeCoeffNum u

def threeTerm0 (u : Nat) : Q' :=
  Q'.mkN (fact (threeT1 u))
    (fact (u + 4) * fact (u + 4) * 2 * 2 * 2 - 1)

def threeTerm1 (u : Nat) : Q' :=
  ⟨-Int.ofNat (fact (threeT2 u)),
    fact (u + 5) * fact (u + 5) - 1⟩

def threeTerm2 (u : Nat) : Q' :=
  Q'.mkN (fact (2 * u + 17))
    (fact (u + 6) * 2 * fact (u + 6) * 2 - 1)

def threeRacahAmplitude (u : Nat) : Q' :=
  ⟨threeQuartic u * Int.ofNat (fact (threeT1 u)),
    8 * (fact (u + 6) * fact (u + 6)) - 1⟩

/-- The exact signed inverse coefficient predicted by the unsquared
dimension/triangle/Racah cancellation. -/
def threeInverseCoeffClosed (u : Nat) : Q' :=
  ⟨threeCoeffNum u, (u + 8) * (u + 10) * (u + 11) - 1⟩

/-- The exact dimension-absorbed Racah kernel. -/
def threeKernelClosed (u : Nat) : Q' :=
  threeInverseCoeffClosed u * threeInverseCoeffClosed u

/-- The all-order-two left channel. -/
def threeLeftChannel (u : Nat) :
    FixedLeftCGChannel (threeN u) 4 (threeN u) (threeD u) where
  k := 2
  k_le := by unfold threeN; omega
  r := 2
  r_le := by unfold threeN; omega
  degree_eq := by unfold threeN threeD; omega

/-- The all-order-two right channel. -/
def threeRightChannel (u : Nat) :
    FixedRightCGChannel (threeN u) 4 (threeN u) (threeD u) where
  p := 2
  p_le := by unfold threeN; omega
  r := 2
  r_le := by unfold threeN; omega
  degree_eq := by unfold threeN threeD; omega

/-- All four contractions are exactly order two. -/
theorem three_contraction_orders (u : Nat) :
    (threeLeftChannel u).k = 2 ∧ (threeLeftChannel u).r = 2 ∧
    (threeRightChannel u).p = 2 ∧ (threeRightChannel u).r = 2 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Both intermediate labels are `n`. -/
theorem three_intermediates (u : Nat) :
    (threeLeftChannel u).intermediate = threeN u ∧
    (threeRightChannel u).intermediate = threeN u := by
  constructor
  · change threeN u + 4 - 2 * 2 = threeN u
    unfold threeN
    omega
  · change 4 + threeN u - 2 * 2 = threeN u
    unfold threeN
    omega

/-! ## Admissibility and exact three-point support -/

theorem three_valid6 (u : Nat) :
    valid6 (threeN u) 4 (threeN u) (threeD u)
      (threeN u) (threeN u) = true := by
  have hsmall : fusionOK (threeN u) 4 (threeN u) = true :=
    (fusionOK_iff_ladder (threeN u) 4 (threeN u)).2
      ⟨2, by unfold threeN; omega, by omega, by unfold threeN; omega⟩
  have hlarge : fusionOK (threeN u) (threeD u) (threeN u) = true :=
    (fusionOK_iff_ladder (threeN u) (threeD u) (threeN u)).2
      ⟨u + 6, by unfold threeN; omega, by unfold threeD; omega,
        by unfold threeN threeD; omega⟩
  unfold valid6
  simp only [hsmall, hlarge, Bool.true_and]

theorem three_racah_parameters (u : Nat) :
    (threeN u + 4 + threeN u) / 2 = u + 10 ∧
    (threeN u + threeD u + threeN u) / 2 = threeT0 u ∧
    (threeN u + 4 + threeN u) / 2 = u + 10 ∧
    (threeN u + threeD u + threeN u) / 2 = threeT0 u ∧
    (threeN u + 4 + threeN u + threeD u) / 2 = threeT2 u ∧
    (4 + threeN u + threeD u + threeN u) / 2 = threeT2 u ∧
    (threeN u + threeN u + threeN u + threeN u) / 2 = threeT2 u := by
  unfold threeN threeD threeT0 threeT2
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

theorem three_tGuard_at_T0 (u : Nat) :
    tGuard (u + 10) (threeT0 u) (u + 10) (threeT0 u)
      (threeT2 u) (threeT2 u) (threeT2 u) (threeT0 u) = true := by
  unfold tGuard threeT0 threeT2
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨?_, by omega⟩
  refine ⟨?_, by omega⟩
  refine ⟨?_, by omega⟩
  refine ⟨?_, by omega⟩
  refine ⟨?_, by omega⟩
  exact ⟨by omega, by omega⟩

theorem three_tGuard_at_T1 (u : Nat) :
    tGuard (u + 10) (threeT0 u) (u + 10) (threeT0 u)
      (threeT2 u) (threeT2 u) (threeT2 u) (threeT1 u) = true := by
  unfold tGuard threeT0 threeT1 threeT2
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨?_, by omega⟩
  refine ⟨?_, by omega⟩
  refine ⟨?_, by omega⟩
  refine ⟨?_, by omega⟩
  refine ⟨?_, by omega⟩
  exact ⟨by omega, by omega⟩

theorem three_tGuard_at_T2 (u : Nat) :
    tGuard (u + 10) (threeT0 u) (u + 10) (threeT0 u)
      (threeT2 u) (threeT2 u) (threeT2 u) (threeT2 u) = true := by
  unfold tGuard threeT0 threeT2
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨?_, by omega⟩
  refine ⟨?_, by omega⟩
  refine ⟨?_, by omega⟩
  refine ⟨?_, by omega⟩
  refine ⟨?_, by omega⟩
  exact ⟨by omega, by omega⟩

theorem three_tGuard_bounds (u t : Nat)
    (h : tGuard (u + 10) (threeT0 u) (u + 10) (threeT0 u)
      (threeT2 u) (threeT2 u) (threeT2 u) t = true) :
    threeT0 u ≤ t ∧ t ≤ threeT2 u := by
  unfold tGuard at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  unfold threeT0 threeT2 at *
  constructor <;> omega

private theorem three_racahSummand_at_T0 (u : Nat) :
    racahSummand (u + 10) (threeT0 u) (u + 10) (threeT0 u)
      (threeT2 u) (threeT2 u) (threeT2 u) (threeT0 u) ≈ threeTerm0 u := by
  unfold racahSummand
  rw [if_pos (three_tGuard_at_T0 u)]
  have hs : threeT0 u - (u + 10) = u + 4 := by unfold threeT0; omega
  have hp : threeT2 u - threeT0 u = 2 := by unfold threeT0 threeT2; omega
  have hpar : threeT0 u % 2 = 0 := by unfold threeT0; omega
  have hnum : threeT0 u + 1 = threeT1 u := by unfold threeT0 threeT1; omega
  unfold sevenFacts
  rw [hpar]
  rw [if_pos rfl]
  simp only [Nat.sub_self, hs, hp]
  rw [show fact 0 = 1 by rfl, show fact 2 = 2 by decide]
  simp only [Nat.mul_one, hnum]
  simp only [Int.one_mul]
  unfold threeTerm0 Q'.mkN
  exact Q'.eqv_refl _

private theorem three_racahSummand_at_T1 (u : Nat) :
    racahSummand (u + 10) (threeT0 u) (u + 10) (threeT0 u)
      (threeT2 u) (threeT2 u) (threeT2 u) (threeT1 u) ≈ threeTerm1 u := by
  unfold racahSummand
  rw [if_pos (three_tGuard_at_T1 u)]
  have hs : threeT1 u - (u + 10) = u + 5 := by unfold threeT1; omega
  have hl : threeT1 u - threeT0 u = 1 := by unfold threeT0 threeT1; omega
  have hp : threeT2 u - threeT1 u = 1 := by unfold threeT1 threeT2; omega
  have hpar : threeT1 u % 2 = 1 := by unfold threeT1; omega
  have hnum : threeT1 u + 1 = threeT2 u := by unfold threeT1 threeT2; omega
  unfold sevenFacts
  rw [hpar]
  rw [if_neg (by omega)]
  simp only [hs, hl, hp]
  rw [show fact 1 = 1 by rfl]
  simp only [Nat.mul_one, Int.neg_one_mul, hnum]
  unfold threeTerm1
  exact Q'.eqv_refl _

private theorem three_racahSummand_at_T2 (u : Nat) :
    racahSummand (u + 10) (threeT0 u) (u + 10) (threeT0 u)
      (threeT2 u) (threeT2 u) (threeT2 u) (threeT2 u) ≈ threeTerm2 u := by
  unfold racahSummand
  rw [if_pos (three_tGuard_at_T2 u)]
  have hs : threeT2 u - (u + 10) = u + 6 := by unfold threeT2; omega
  have hl : threeT2 u - threeT0 u = 2 := by unfold threeT0 threeT2; omega
  have hpar : threeT2 u % 2 = 0 := by unfold threeT2; omega
  have hnum : threeT2 u + 1 = 2 * u + 17 := by unfold threeT2; omega
  unfold sevenFacts
  rw [hpar]
  rw [if_pos rfl]
  simp only [Nat.sub_self, hs, hl]
  rw [show fact 0 = 1 by rfl, show fact 2 = 2 by decide]
  simp only [Nat.mul_one, hnum]
  simp only [Int.one_mul]
  unfold threeTerm2 Q'.mkN
  exact Q'.eqv_refl _

theorem three_racahSummand_threehot (u t : Nat) :
    racahSummand
      ((threeN u + 4 + threeN u) / 2)
      ((threeN u + threeD u + threeN u) / 2)
      ((threeN u + 4 + threeN u) / 2)
      ((threeN u + threeD u + threeN u) / 2)
      ((threeN u + 4 + threeN u + threeD u) / 2)
      ((4 + threeN u + threeD u + threeN u) / 2)
      ((threeN u + threeN u + threeN u + threeN u) / 2) t ≈
      (if t = threeT0 u then threeTerm0 u else 0) +
        (if t = threeT1 u then threeTerm1 u else 0) +
        (if t = threeT2 u then threeTerm2 u else 0) := by
  have hp := three_racah_parameters u
  rw [hp.1, hp.2.1, hp.2.2.2.2.1,
    hp.2.2.2.2.2.1, hp.2.2.2.2.2.2]
  by_cases h0 : t = threeT0 u
  · subst t
    rw [if_pos rfl, if_neg (by unfold threeT0 threeT1; omega),
      if_neg (by unfold threeT0 threeT2; omega)]
    refine Q'.eqv_trans _ (threeTerm0 u) _ (three_racahSummand_at_T0 u) ?_
    exact Q'.eqv_symm (Q'.eqv_of_eq (by
      rw [Q'.add_zero', Q'.add_zero']))
  · by_cases h1 : t = threeT1 u
    · subst t
      rw [if_neg (by unfold threeT0 threeT1; omega), if_pos rfl,
        if_neg (by unfold threeT1 threeT2; omega)]
      refine Q'.eqv_trans _ (threeTerm1 u) _ (three_racahSummand_at_T1 u) ?_
      exact Q'.eqv_symm (Q'.eqv_of_eq (by
        rw [Q'.zero_add', Q'.add_zero']))
    · by_cases h2 : t = threeT2 u
      · subst t
        rw [if_neg (by unfold threeT0 threeT2; omega),
          if_neg (by unfold threeT1 threeT2; omega), if_pos rfl]
        refine Q'.eqv_trans _ (threeTerm2 u) _ (three_racahSummand_at_T2 u) ?_
        exact Q'.eqv_symm (Q'.eqv_of_eq (by
          rw [Q'.zero_add', Q'.zero_add']))
      · rw [if_neg h0, if_neg h1, if_neg h2]
        unfold racahSummand
        rw [if_neg]
        · exact Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' 0))
        · intro hg
          have hb := three_tGuard_bounds u t hg
          unfold threeT0 threeT1 threeT2 at *
          omega

/-! ## The exact signed three-term telescope -/

private theorem mkN_den_of_pred (n d : Nat) (hd : 0 < d) :
    (Q'.mkN n (d - 1)).den = d := by
  change d - 1 + 1 = d
  omega

private theorem signed_den_of_pred (z : Int) (d : Nat) (hd : 0 < d) :
    ((⟨z, d - 1⟩ : Q').den) = d := by
  change d - 1 + 1 = d
  omega

private theorem fact_u5 (u : Nat) :
    fact (u + 5) = (u + 5) * fact (u + 4) := by
  rw [show u + 5 = (u + 4) + 1 by omega]
  rfl

private theorem fact_u6 (u : Nat) :
    fact (u + 6) = (u + 6) * (u + 5) * fact (u + 4) := by
  rw [show u + 6 = (u + 5) + 1 by omega]
  change (u + 6) * fact (u + 5) = _
  rw [fact_u5 u]
  ac_rfl

private theorem fact_u6_from_u5 (u : Nat) :
    fact (u + 6) = (u + 6) * fact (u + 5) := by
  rw [show u + 6 = (u + 5) + 1 by omega]
  rfl

private theorem fact_2u16 (u : Nat) :
    fact (2 * u + 16) = (2 * u + 16) * fact (2 * u + 15) := by
  rw [show 2 * u + 16 = (2 * u + 15) + 1 by omega]
  rfl

private theorem fact_2u17 (u : Nat) :
    fact (2 * u + 17) =
      (2 * u + 17) * (2 * u + 16) * fact (2 * u + 15) := by
  rw [show 2 * u + 17 = (2 * u + 16) + 1 by omega]
  change (2 * u + 17) * fact (2 * u + 16) = _
  rw [fact_2u16 u]
  simp only [show 2 * u + 16 + 1 = 2 * u + 17 by omega]
  ac_rfl

private abbrev PE := YMGap.Continuum.RingNormaliser.PolyExpr
private def px : PE := .var 0
private def pc (z : Int) : PE := .const z
private def pa (x y : PE) : PE := .add x y
private def pm (x y : PE) : PE := .mul x y
private def pn (x : PE) : PE := .neg x
private def ps (x y : PE) : PE := pa x (pn y)

private def threePolyL : PE :=
  pa
    (ps
      (pm (pm (pa px (pc 6)) (pa px (pc 5)))
        (pm (pa px (pc 6)) (pa px (pc 5))))
      (pm (pm (pc 8) (pa (pm (pc 2) px) (pc 16)))
        (pm (pa px (pc 6)) (pa px (pc 6)))))
    (pm (pm (pc 2) (pa (pm (pc 2) px) (pc 17)))
      (pa (pm (pc 2) px) (pc 16)))

private def threePolyR : PE :=
  pm (pa px (pc 7))
    (ps (ps (ps (pm (pm px px) px) (pm px px)) (pm (pc 124) px))
      (pc 452))

private theorem threePoly_normal :
    YMGap.Continuum.RingNormaliser.normalize threePolyL =
      YMGap.Continuum.RingNormaliser.normalize threePolyR := by decide

private theorem three_int_telescope (u : Nat) :
    (((Int.ofNat u + 6) * (Int.ofNat u + 5)) *
        ((Int.ofNat u + 6) * (Int.ofNat u + 5))) -
      (8 * (2 * Int.ofNat u + 16)) *
        ((Int.ofNat u + 6) * (Int.ofNat u + 6)) +
      (2 * (2 * Int.ofNat u + 17)) * (2 * Int.ofNat u + 16) =
      threeQuartic u := by
  have h := YMGap.Continuum.IntRingNormaliser.poly_identity_of_normal_eq
    threePolyL threePolyR threePoly_normal (fun _ => Int.ofNat u)
  simpa only [threePolyL, threePolyR, px, pc, pa, pm, pn, ps,
    YMGap.Continuum.IntRingNormaliser.eval, threeQuartic, threeCoeffNum,
    Int.sub_eq_add_neg] using h

private def threeCommonDen (u : Nat) : Nat :=
  8 * (fact (u + 6) * fact (u + 6))

private def threeScaledNum0 (u : Nat) : Int :=
  let U : Int := Int.ofNat u
  ((U + 6) * (U + 5) * ((U + 6) * (U + 5))) *
    Int.ofNat (fact (threeT1 u))

private def threeScaledNum1 (u : Nat) : Int :=
  let U : Int := Int.ofNat u
  (-1 : Int) *
    (8 * (2 * U + 16) * ((U + 6) * (U + 6))) *
      Int.ofNat (fact (threeT1 u))

private def threeScaledNum2 (u : Nat) : Int :=
  let U : Int := Int.ofNat u
  (2 * (2 * U + 17) * (2 * U + 16)) *
    Int.ofNat (fact (threeT1 u))

private def threeScaledTerm0 (u : Nat) : Q' :=
  ⟨threeScaledNum0 u, threeCommonDen u - 1⟩

private def threeScaledTerm1 (u : Nat) : Q' :=
  ⟨threeScaledNum1 u, threeCommonDen u - 1⟩

private def threeScaledTerm2 (u : Nat) : Q' :=
  ⟨threeScaledNum2 u, threeCommonDen u - 1⟩

private theorem threeTerm0_eq_scaled (u : Nat) :
    threeTerm0 u ≈ threeScaledTerm0 u := by
  have h4 : 0 < fact (u + 4) * fact (u + 4) * 2 * 2 * 2 :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos
      (Nat.mul_pos (fact_pos _) (fact_pos _)) (by omega)) (by omega)) (by omega)
  have h6 : 0 < threeCommonDen u := by
    unfold threeCommonDen
    exact Nat.mul_pos (by omega) (Nat.mul_pos (fact_pos _) (fact_pos _))
  unfold threeTerm0 threeScaledTerm0 threeScaledNum0 threeT1
  show _ * (_ : Int) = _ * (_ : Int)
  rw [mkN_den_of_pred _ _ h4, signed_den_of_pred _ _ h6]
  simp only [Q'.mkN]
  unfold threeCommonDen
  rw [fact_u6 u]
  have hu5 : (((u + 5 : Nat) : Int)) = (u : Int) + 5 := by push_cast; omega
  have hu6 : (((u + 6 : Nat) : Int)) = (u : Int) + 6 := by push_cast; omega
  simp only [Int.natCast_mul, Int.ofNat_eq_natCast]
  rw [hu5, hu6]
  rw [show ((8 : Nat) : Int) = 8 by rfl,
    show ((2 : Nat) : Int) = 2 by rfl]
  rw [show (8 : Int) = 2 * 2 * 2 by decide]
  ac_rfl

private theorem threeTerm1_eq_scaled (u : Nat) :
    threeTerm1 u ≈ threeScaledTerm1 u := by
  have h5 : 0 < fact (u + 5) * fact (u + 5) :=
    Nat.mul_pos (fact_pos _) (fact_pos _)
  have h6 : 0 < threeCommonDen u := by
    unfold threeCommonDen
    exact Nat.mul_pos (by omega) (Nat.mul_pos (fact_pos _) (fact_pos _))
  unfold threeTerm1 threeScaledTerm1 threeScaledNum1 threeT1 threeT2
  show _ * (_ : Int) = _ * (_ : Int)
  rw [signed_den_of_pred _ _ h5, signed_den_of_pred _ _ h6]
  unfold threeCommonDen
  rw [fact_u6_from_u5 u, fact_2u16 u]
  have hu6 : (((u + 6 : Nat) : Int)) = (u : Int) + 6 := by push_cast; omega
  have h2u16 : (((2 * u + 16 : Nat) : Int)) = 2 * (u : Int) + 16 := by
    push_cast
    omega
  simp only [Int.natCast_mul, Int.ofNat_eq_natCast, Int.neg_mul]
  rw [hu6, h2u16]
  rw [show ((8 : Nat) : Int) = 8 by rfl]
  congr 1
  ac_rfl

private theorem threeTerm2_eq_scaled (u : Nat) :
    threeTerm2 u ≈ threeScaledTerm2 u := by
  have h4 : 0 < fact (u + 6) * 2 * fact (u + 6) * 2 :=
    Nat.mul_pos (Nat.mul_pos
      (Nat.mul_pos (fact_pos _) (by omega)) (fact_pos _)) (by omega)
  have h6 : 0 < threeCommonDen u := by
    unfold threeCommonDen
    exact Nat.mul_pos (by omega) (Nat.mul_pos (fact_pos _) (fact_pos _))
  unfold threeTerm2 threeScaledTerm2 threeScaledNum2 threeT1
  show _ * (_ : Int) = _ * (_ : Int)
  rw [mkN_den_of_pred _ _ h4, signed_den_of_pred _ _ h6]
  simp only [Q'.mkN]
  unfold threeCommonDen
  rw [fact_2u17 u]
  have h2u16 : (((2 * u + 16 : Nat) : Int)) = 2 * (u : Int) + 16 := by
    push_cast
    omega
  have h2u17 : (((2 * u + 17 : Nat) : Int)) = 2 * (u : Int) + 17 := by
    push_cast
    omega
  simp only [Int.natCast_mul, Int.ofNat_eq_natCast]
  rw [h2u16, h2u17]
  rw [show ((8 : Nat) : Int) = 8 by rfl,
    show ((2 : Nat) : Int) = 2 by rfl]
  rw [show (8 : Int) = 2 * 2 * 2 by decide]
  ac_rfl

private theorem signed_same_den_add (z w : Int) (d : Nat) (hd : 0 < d) :
    (⟨z, d - 1⟩ : Q') + ⟨w, d - 1⟩ ≈ ⟨z + w, d - 1⟩ := by
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.add_num_cast, Q'.add_den_cast]
  rw [signed_den_of_pred _ _ hd, signed_den_of_pred _ _ hd,
    signed_den_of_pred _ _ hd]
  simp only [Int.add_mul]
  ac_rfl

private theorem three_scaled_nums_sum (u : Nat) :
    threeScaledNum0 u + threeScaledNum1 u + threeScaledNum2 u =
      threeQuartic u * Int.ofNat (fact (threeT1 u)) := by
  have hpoly := three_int_telescope u
  unfold threeScaledNum0 threeScaledNum1 threeScaledNum2
  simp only [Int.sub_eq_add_neg] at hpoly
  calc
    _ = ((((Int.ofNat u + 6) * (Int.ofNat u + 5)) *
          ((Int.ofNat u + 6) * (Int.ofNat u + 5)) +
        -(8 * (2 * Int.ofNat u + 16) *
          ((Int.ofNat u + 6) * (Int.ofNat u + 6))) +
        2 * (2 * Int.ofNat u + 17) * (2 * Int.ofNat u + 16)) *
          Int.ofNat (fact (threeT1 u))) := by
      simp only [Int.add_mul, Int.neg_mul]
      ac_rfl
    _ = threeQuartic u * Int.ofNat (fact (threeT1 u)) := by rw [hpoly]

theorem three_terms_telescope (u : Nat) :
    threeTerm0 u + threeTerm1 u + threeTerm2 u ≈
      threeRacahAmplitude u := by
  have hden : 0 < threeCommonDen u := by
    unfold threeCommonDen
    exact Nat.mul_pos (by omega) (Nat.mul_pos (fact_pos _) (fact_pos _))
  have h01 := signed_same_den_add (threeScaledNum0 u)
    (threeScaledNum1 u) (threeCommonDen u) hden
  have h012 := signed_same_den_add
    (threeScaledNum0 u + threeScaledNum1 u) (threeScaledNum2 u)
    (threeCommonDen u) hden
  have hscaled : threeScaledTerm0 u + threeScaledTerm1 u +
      threeScaledTerm2 u ≈ threeRacahAmplitude u := by
    refine Q'.eqv_trans _
      (⟨threeScaledNum0 u + threeScaledNum1 u,
        threeCommonDen u - 1⟩ + threeScaledTerm2 u) _ ?_ ?_
    · exact Q'.add_eqv_congr_right _ _ _ (by
        simpa only [threeScaledTerm0, threeScaledTerm1] using h01)
    refine Q'.eqv_trans _
      ⟨threeScaledNum0 u + threeScaledNum1 u + threeScaledNum2 u,
        threeCommonDen u - 1⟩ _ ?_ ?_
    · simpa only [threeScaledTerm2] using h012
    unfold threeRacahAmplitude threeCommonDen
    rw [three_scaled_nums_sum u]
    exact Q'.eqv_refl _
  exact Q'.eqv_trans _
    (threeScaledTerm0 u + threeScaledTerm1 u + threeScaledTerm2 u) _
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr' (threeTerm0_eq_scaled u) (threeTerm1_eq_scaled u))
      (threeTerm2_eq_scaled u)) hscaled

theorem three_racahSum_eq_amplitude (u : Nat) :
    racahSum (threeN u) 4 (threeN u) (threeN u) (threeD u) (threeN u) ≈
      threeRacahAmplitude u := by
  unfold racahSum
  let N :=
    (threeN u + 4 + threeN u + threeN u + threeD u + threeN u) / 2 + 1
  have hcongr := finSum_eqv_congr _ _
    (fun t => three_racahSummand_threehot u t) N
  have h0 : threeT0 u < N := by
    unfold N threeN threeD threeT0
    omega
  have h1 : threeT1 u < N := by
    unfold N threeN threeD threeT1
    omega
  have h2 : threeT2 u < N := by
    unfold N threeN threeD threeT2
    omega
  have hsum0 :=
    YMGap.Continuum.SU2TransvectantGeneralCoefficient.finSum_onehot_value
      (threeTerm0 u) N (threeT0 u) h0
  have hsum1 :=
    YMGap.Continuum.SU2TransvectantGeneralCoefficient.finSum_onehot_value
      (threeTerm1 u) N (threeT1 u) h1
  have hsum2 :=
    YMGap.Continuum.SU2TransvectantGeneralCoefficient.finSum_onehot_value
      (threeTerm2 u) N (threeT2 u) h2
  have houter := finSum_add
    (fun t =>
      (if t = threeT0 u then threeTerm0 u else 0) +
        (if t = threeT1 u then threeTerm1 u else 0))
    (fun t => if t = threeT2 u then threeTerm2 u else 0) N
  have hinner := finSum_add
    (fun t => if t = threeT0 u then threeTerm0 u else 0)
    (fun t => if t = threeT1 u then threeTerm1 u else 0) N
  refine Q'.eqv_trans _ _ _ hcongr ?_
  refine Q'.eqv_trans _
    (finSum (fun t =>
      (if t = threeT0 u then threeTerm0 u else 0) +
        (if t = threeT1 u then threeTerm1 u else 0)) N +
      finSum (fun t => if t = threeT2 u then threeTerm2 u else 0) N) _
    houter ?_
  refine Q'.eqv_trans _
    ((finSum (fun t => if t = threeT0 u then threeTerm0 u else 0) N +
      finSum (fun t => if t = threeT1 u then threeTerm1 u else 0) N) +
      finSum (fun t => if t = threeT2 u then threeTerm2 u else 0) N) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ _ hinner
  · exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.add_eqv_congr' hsum0 hsum1) hsum2)
      (three_terms_telescope u)

/-! ## Triangle factors and the exact squared kernel -/

theorem three_triSq_small (u : Nat) :
    triSq (threeN u) 4 (threeN u) =
      Q'.mkN (4 * fact (u + 6)) (fact (u + 11) - 1) := by
  have h1 : (threeN u + 4 - threeN u) / 2 = 2 := by
    unfold threeN
    omega
  have h2 : (threeN u + threeN u - 4) / 2 = u + 6 := by
    unfold threeN
    omega
  have h3 : (4 + threeN u - threeN u) / 2 = 2 := by
    unfold threeN
    omega
  have h4 : (threeN u + 4 + threeN u) / 2 + 1 = u + 11 := by
    unfold threeN
    omega
  unfold triSq triSqNum triSqDen
  rw [h1, h2, h3, h4, show fact 2 = 2 by decide]
  ac_rfl

theorem three_triSq_large (u : Nat) :
    triSq (threeN u) (threeD u) (threeN u) =
      Q'.mkN (2 * (fact (u + 6) * fact (u + 6)))
        (fact (2 * u + 15) - 1) := by
  have h1 : (threeN u + threeD u - threeN u) / 2 = u + 6 := by
    unfold threeN threeD
    omega
  have h2 : (threeN u + threeN u - threeD u) / 2 = 2 := by
    unfold threeN threeD
    omega
  have h3 : (threeD u + threeN u - threeN u) / 2 = u + 6 := by
    unfold threeN threeD
    omega
  have h4 : (threeN u + threeD u + threeN u) / 2 + 1 =
      2 * u + 15 := by
    unfold threeN threeD
    omega
  unfold triSq triSqNum triSqDen
  rw [h1, h2, h3, h4, show fact 2 = 2 by decide]
  ac_rfl

private theorem fact_u11 (u : Nat) :
    fact (u + 11) =
      (u + 11) * (u + 10) * (u + 9) * (u + 8) * (u + 7) *
        fact (u + 6) := by
  have h7 : fact (u + 7) = (u + 7) * fact (u + 6) := by
    rw [show u + 7 = (u + 6) + 1 by omega]
    rfl
  have h8 : fact (u + 8) = (u + 8) * fact (u + 7) := by
    rw [show u + 8 = (u + 7) + 1 by omega]
    rfl
  have h9 : fact (u + 9) = (u + 9) * fact (u + 8) := by
    rw [show u + 9 = (u + 8) + 1 by omega]
    rfl
  have h10 : fact (u + 10) = (u + 10) * fact (u + 9) := by
    rw [show u + 10 = (u + 9) + 1 by omega]
    rfl
  have h11 : fact (u + 11) = (u + 11) * fact (u + 10) := by
    rw [show u + 11 = (u + 10) + 1 by omega]
    rfl
  rw [h11, h10, h9, h8, h7]
  ac_rfl

private theorem three_unsquared_factorial_cancel (u : Nat) :
    Q'.ofNat (u + 9) *
      (Q'.mkN (4 * fact (u + 6)) (fact (u + 11) - 1) *
        Q'.mkN (2 * (fact (u + 6) * fact (u + 6)))
          (fact (2 * u + 15) - 1)) *
      threeRacahAmplitude u ≈ threeInverseCoeffClosed u := by
  have h11 : 0 < fact (u + 11) := fact_pos _
  have h15 : 0 < fact (2 * u + 15) := fact_pos _
  have h8 : 0 < 8 * (fact (u + 6) * fact (u + 6)) :=
    Nat.mul_pos (by omega) (Nat.mul_pos (fact_pos _) (fact_pos _))
  have hden : 0 < (u + 8) * (u + 10) * (u + 11) :=
    Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  unfold threeRacahAmplitude threeInverseCoeffClosed threeQuartic threeT1
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast]
  rw [mkN_den_of_pred _ _ h11, mkN_den_of_pred _ _ h15,
    signed_den_of_pred _ _ h8, signed_den_of_pred _ _ hden]
  simp only [Q'.mkN]
  rw [fact_u11 u]
  push_cast
  simp only [Int.natCast_mul, Int.ofNat_eq_natCast]
  simp only [show (u : Int) + 1 + 1 + 1 + 1 + 1 + 1 + 1 =
      (u : Int) + 7 by omega,
    show ((2 : Nat) : Int) = 2 by rfl,
    show ((4 : Nat) : Int) = 4 by rfl]
  rw [show (8 : Int) = 2 * 4 by decide]
  ac_rfl

theorem three_racahKernel_closed (u : Nat) :
    racahKernel6 (threeN u) 4 (threeN u) (threeD u)
      (threeN u) (threeN u) ≈ threeKernelClosed u := by
  unfold racahKernel6
  rw [if_pos (three_valid6 u)]
  have hsum := three_racahSum_eq_amplitude u
  let B := Q'.ofNat (u + 9) *
    (Q'.mkN (4 * fact (u + 6)) (fact (u + 11) - 1) *
      Q'.mkN (2 * (fact (u + 6) * fact (u + 6)))
        (fact (2 * u + 15) - 1)) *
    threeRacahAmplitude u
  have hB : B ≈ threeInverseCoeffClosed u := by
    simpa only [B] using three_unsquared_factorial_cancel u
  rw [show dimRep (threeN u) = u + 9 by unfold dimRep threeN; omega,
    three_triSq_small u, three_triSq_large u]
  have hrearrange :
      Q'.ofNat (u + 9) * Q'.ofNat (u + 9) *
          (Q'.mkN (4 * fact (u + 6)) (fact (u + 11) - 1) *
            Q'.mkN (2 * (fact (u + 6) * fact (u + 6)))
              (fact (2 * u + 15) - 1) *
            Q'.mkN (4 * fact (u + 6)) (fact (u + 11) - 1) *
            Q'.mkN (2 * (fact (u + 6) * fact (u + 6)))
              (fact (2 * u + 15) - 1)) *
          (threeRacahAmplitude u * threeRacahAmplitude u) ≈ B * B := by
    unfold B
    ring_qeqv
  have hsquare : B * B ≈ threeKernelClosed u := by
    unfold threeKernelClosed
    exact Q'.eqv_trans _
      (threeInverseCoeffClosed u * B) _
      (Q'.mul_eqv_congr_right _ _ _ hB)
      (Q'.mul_eqv_congr_left _ _ _ hB)
  refine Q'.eqv_trans _
    (Q'.ofNat (u + 9) * Q'.ofNat (u + 9) *
      (Q'.mkN (4 * fact (u + 6)) (fact (u + 11) - 1) *
        Q'.mkN (2 * (fact (u + 6) * fact (u + 6)))
          (fact (2 * u + 15) - 1) *
        Q'.mkN (4 * fact (u + 6)) (fact (u + 11) - 1) *
        Q'.mkN (2 * (fact (u + 6) * fact (u + 6)))
          (fact (2 * u + 15) - 1)) *
      (threeRacahAmplitude u * threeRacahAmplitude u)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_trans _
        (threeRacahAmplitude u *
          racahSum (threeN u) 4 (threeN u) (threeN u)
            (threeD u) (threeN u)) _
        (Q'.mul_eqv_congr_right _ _ _ hsum)
        (Q'.mul_eqv_congr_left _ _ _ hsum))
  · exact Q'.eqv_trans _ _ _ hrearrange hsquare

end YMGap.Continuum.SU2OrderedRacahNearStretchedThreeTerm

#print axioms YMGap.Continuum.SU2OrderedRacahNearStretchedThreeTerm.three_valid6
#print axioms YMGap.Continuum.SU2OrderedRacahNearStretchedThreeTerm.three_racahSummand_threehot
#print axioms YMGap.Continuum.SU2OrderedRacahNearStretchedThreeTerm.three_terms_telescope
#print axioms YMGap.Continuum.SU2OrderedRacahNearStretchedThreeTerm.three_racahSum_eq_amplitude
#print axioms YMGap.Continuum.SU2OrderedRacahNearStretchedThreeTerm.three_racahKernel_closed
