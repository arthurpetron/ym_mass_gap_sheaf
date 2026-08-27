/-
# The physical SU(2) Schur recoupling kernel

The canonical strand switch cannot in general be decoded after its recoupling
microdata are compressed to one fixed fusion tree: different strand pairings
can produce the same crossed channel sums.  The correct replacement is
therefore weighted recoupling, not a deterministic permutation of canonical
channel labels.

This module constructs that weighted object directly from the already proved
physical representation theory.  Every proof-carrying left channel has an
exact finite Schur expansion in the canonical right channels.  The right
channels are pairwise orthogonal by the SU(2) pair-Casimir theorem.  Pairing
the expansion with the left channel therefore gives the finite Parseval law

  leftWeight = sum_q rightWeight(q) * schurCoeff(q)^2.

After division by the strictly positive left weight, these summands form an
explicit nonnegative normalized rational kernel.  No factorial Racah formula
is assumed: identifying this physical kernel with `racahKernel6` remains the
separate explicit closed-form theorem isolated by the ordered-Racah campaign.

Constructive contract: Mathlib-free, exact `Q'` arithmetic, finite recursion,
no choice, no `Classical`, no `sorry`, and no new axiom.
-/

import YMGap.Continuum.SU2OrderedRacahCasimirCapstone
import YMGap.Continuum.SU2OrderedLeftCasimirPairing
import YMGap.Continuum.SU2TransvectantAdmissibleSurjectivity

namespace YMGap.Continuum.SU2PhysicalSchurRecouplingKernel

set_option maxHeartbeats 2400000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionBratteli
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantLinearity
open YMGap.Continuum.SU2TransvectantFactorialSeed
open YMGap.Continuum.SU2TransvectantFactorialRecurrence
open YMGap.Continuum.SU2TransvectantGeneralCoefficient
open YMGap.Continuum.SU2TransvectantAdmissibleExtremal
open YMGap.Continuum.SU2TransvectantAdmissibleSurjectivity
open YMGap.Continuum.SU2TransvectantMixedRecouplingGNSCompleted
open YMGap.Continuum.SU2TransvectantAllLabelGramCompleted
open YMGap.Continuum.SU2TransvectantCentralChannelEquation
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2DirectRightFixedOutputEnumeration
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2FixedLeftRightAssociatorSchur
open YMGap.Continuum.SU2FixedLeftRightOrderedAssociatorBridge
open YMGap.Continuum.SU2OrderedFundamentalFRows
open YMGap.Continuum.SU2OrderedRacahCollapsedHahnCarrier
open YMGap.Continuum.SU2OrderedRacahCasimirCapstone
open YMGap.Continuum.SU2OrderedRacahInteriorSchurBridge
open YMGap.Continuum.SU2OrderedRightGramOrthogonality
open YMGap.Continuum.SU2OrderedRightGramCasimirOrthogonality
open YMGap.Continuum.SU2OrderedLeftCasimirPairing
open YMGap.Continuum.SU2GeneralHahnCumulativeTransform
open YMGap.Continuum.SixJKernel
open YMGap.Continuum.PentagonRelation

local infix:50 " ≈ " => Q'.eqv

private theorem eqv_zero_iff_num_zero (x : Q') :
    x ≈ 0 ↔ x.num = 0 := by
  constructor
  · intro h
    have h' : x.num * (1 : Int) = (0 : Int) * (x.den : Int) := h
    simpa only [Int.mul_one, Int.zero_mul] using h'
  · intro h
    unfold Q'.eqv
    change x.num * (1 : Int) = (0 : Int) * (x.den : Int)
    rw [h]
    simp only [Int.zero_mul]

private theorem mul_not_eqv_zero {x y : Q'}
    (hx : ¬ x ≈ 0) (hy : ¬ y ≈ 0) : ¬ x * y ≈ 0 := by
  intro hxy
  have hnum : x.num * y.num = 0 :=
    (eqv_zero_iff_num_zero (x * y)).mp hxy
  rcases Int.mul_eq_zero.mp hnum with hx0 | hy0
  · exact hx ((eqv_zero_iff_num_zero x).mpr hx0)
  · exact hy ((eqv_zero_iff_num_zero y).mpr hy0)

private theorem self_mul_pos_of_not_eqv_zero (x : Q') (hx : ¬ x ≈ 0) :
    (0 : Q') < x * x := by
  apply CReal.pos_of_num_pos
  rw [Q'.mul_num_cast]
  have hn : x.num ≠ 0 := fun h => hx ((eqv_zero_iff_num_zero x).mpr h)
  rcases Int.lt_or_gt_of_ne hn with hneg | hpos
  · have hp : 0 < (-x.num) * (-x.num) :=
      Int.mul_pos (Int.neg_pos.mpr hneg) (Int.neg_pos.mpr hneg)
    simpa only [Int.neg_mul, Int.mul_neg, Int.neg_neg] using hp
  · exact Int.mul_pos hpos hpos

private theorem tvBinomQ_pos_of_le (n i : Nat) (hi : i ≤ n) :
    (0 : Q') < tvBinomQ n i := by
  unfold tvBinomQ
  rw [if_pos hi]
  apply CReal.pos_of_num_pos
  change (0 : Int) < Int.ofNat (tvFact n)
  exact Int.natCast_pos.mpr (tvFact_pos n)

private theorem symMonomialNormSq_pos_of_le (n i : Nat) (hi : i ≤ n) :
    (0 : Q') < symMonomialNormSq n i := by
  unfold symMonomialNormSq
  rw [if_pos hi]
  apply CReal.pos_of_num_pos
  change (0 : Int) < Int.ofNat (tvFact i * tvFact (n - i))
  exact Int.natCast_pos.mpr
    (Nat.mul_pos (tvFact_pos i) (tvFact_pos (n - i)))

private theorem term_le_finSum (g : Nat → Q')
    (hg : ∀ i, (0 : Q') ≤ g i) :
    ∀ n k, k < n → g k ≤ RationalTail.finSum g n
  | 0, k, hk => by omega
  | n + 1, k, hk => by
      rw [RationalTail.finSum_succ]
      by_cases hkn : k = n
      · subst k
        have hsum : (0 : Q') ≤ RationalTail.finSum g n :=
          YMGap.RG.finSum_nonneg _ hg n
        exact Q'.le_trans' _ (g n + RationalTail.finSum g n) _
          (Q'.add_le_self_of_nonneg _ _ hsum)
          (Q'.le_of_eqv (Q'.add_comm_eqv _ _))
      · exact Q'.le_trans' _ _ _ (term_le_finSum g hg n k (by omega))
          (Q'.add_le_self_of_nonneg _ _ (hg n))

private theorem diagonal_term_le (a b c d : Nat)
    (L : BForm → BForm → BForm → BForm)
    (i j k s : Nat) (hi : i < a + 1) (hj : j < b + 1)
    (hk : k < c + 1) (hs : s < d + 1) :
    triDiagonalSummand a b c d L i j k s ≤
      triMapInner a b c d L L := by
  let S := fun i j k s => triDiagonalSummand a b c d L i j k s
  have hS : ∀ i j k s, (0 : Q') ≤ S i j k s :=
    fun i j k s => triDiagonalSummand_nonneg a b c d L i j k s
  have h1 : S i j k s ≤ RationalTail.finSum (fun u => S i j k u) (d + 1) :=
    term_le_finSum _ (hS i j k) (d + 1) s hs
  have h2 : RationalTail.finSum (fun u => S i j k u) (d + 1) ≤
      RationalTail.finSum
        (fun v => RationalTail.finSum (fun u => S i j v u) (d + 1))
        (c + 1) :=
    term_le_finSum _
      (fun v => YMGap.RG.finSum_nonneg _ (hS i j v) (d + 1))
      (c + 1) k hk
  have h3 : RationalTail.finSum
        (fun v => RationalTail.finSum (fun u => S i j v u) (d + 1))
        (c + 1) ≤
      RationalTail.finSum
        (fun w => RationalTail.finSum
          (fun v => RationalTail.finSum (fun u => S i w v u) (d + 1))
          (c + 1))
        (b + 1) :=
    term_le_finSum _
      (fun w => YMGap.RG.finSum_nonneg _
        (fun v => YMGap.RG.finSum_nonneg _ (hS i w v) (d + 1))
        (c + 1))
      (b + 1) j hj
  have h4 : RationalTail.finSum
        (fun w => RationalTail.finSum
          (fun v => RationalTail.finSum (fun u => S i w v u) (d + 1))
          (c + 1))
        (b + 1) ≤
      RationalTail.finSum
        (fun x => RationalTail.finSum
          (fun w => RationalTail.finSum
            (fun v => RationalTail.finSum (fun u => S x w v u) (d + 1))
            (c + 1))
          (b + 1))
        (a + 1) :=
    term_le_finSum _
      (fun x => YMGap.RG.finSum_nonneg _
        (fun w => YMGap.RG.finSum_nonneg _
          (fun v => YMGap.RG.finSum_nonneg _ (hS x w v) (d + 1))
          (c + 1))
        (b + 1))
      (a + 1) i hi
  exact Q'.le_trans' _ _ _ h1
    (Q'.le_trans' _ _ _ h2
      (Q'.le_trans' _ _ _ h3 (by simpa only [S, triMapInner] using h4)))

/-! ## 1. Strict positivity of every physical left channel -/

theorem fixedLeft_inner_fusionOK {a b c d : Nat}
    (q : FixedLeftCGChannel a b c d) :
    fusionOK a b q.intermediate = true := by
  apply (YMGap.Continuum.FusionBratteli.fusionOK_iff_ladder
    a b q.intermediate).mpr
  have hk := Nat.le_min.mp q.k_le
  refine ⟨q.k, hk.1, hk.2, ?_⟩
  unfold FixedLeftCGChannel.intermediate
  omega

theorem fixedLeft_outer_fusionOK {a b c d : Nat}
    (q : FixedLeftCGChannel a b c d) :
    fusionOK q.intermediate c d = true := by
  apply (YMGap.Continuum.FusionBratteli.fusionOK_iff_ladder
    q.intermediate c d).mpr
  have hr := Nat.le_min.mp q.r_le
  refine ⟨q.r, hr.1, hr.2, ?_⟩
  have hd := q.degree_eq
  unfold FixedLeftCGChannel.intermediate at hd ⊢
  omega

/-- A physical left channel has an explicit nonzero nested extremal pivot.
The first transvectant uses its highest Cayley branch, and its highest output
then supplies the highest Cayley branch of the outer transvectant. -/
theorem fixedLeft_nonzero_monomial_pivot {a b c d : Nat}
    (q : FixedLeftCGChannel a b c d) :
    ¬ triLeft a b c d q.intermediate
      (mono a) (mono (b - q.k)) (mono (c - q.r)) d ≈ 0 := by
  have hk := Nat.le_min.mp q.k_le
  have hr := Nat.le_min.mp q.r_le
  let alpha := extremalCoeff a q.k
  let carrier : BForm2 :=
    tprod (mono q.intermediate) (mono (c - q.r))
  have hinner := transvect_extremal_form a b q.k hk.1 hk.2
  have htprod : BForm2Eqv
      (tprod
        (transvect a b q.k (tprod (mono a) (mono (b - q.k))))
        (mono (c - q.r)))
      (bscale alpha carrier) := by
    intro x y
    have hx := hinner x
    have he : a + b - 2 * q.k = q.intermediate := by
      unfold FixedLeftCGChannel.intermediate
      rfl
    rw [he] at hx
    refine Q'.eqv_trans _
      ((alpha * mono q.intermediate x) * mono (c - q.r) y) _
      (Q'.mul_eqv_congr_right _ _ _ hx) ?_
    exact Q'.mul_assoc_eqv _ _ _
  have hcongr := transvect_congr q.intermediate c q.r htprod d
  have hscale := transvect_scale q.intermediate c q.r alpha carrier d
  have hext0 := transvect_extremal q.r q.intermediate c hr.1 hr.2
  have hdegree : q.intermediate + c - 2 * q.r = d := by
    have hd := q.degree_eq
    unfold FixedLeftCGChannel.intermediate at hd ⊢
    exact hd
  have hext : transvect q.intermediate c q.r carrier d ≈
      extremalCoeff q.intermediate q.r := by
    have hvalue :
        transvect q.intermediate c q.r carrier d =
          transvect q.intermediate c q.r carrier
            (q.intermediate + c - 2 * q.r) :=
      congrArg (transvect q.intermediate c q.r carrier) hdegree.symm
    rw [hvalue]
    simpa only [carrier] using hext0
  have hcoeff : triLeft a b c d q.intermediate
      (mono a) (mono (b - q.k)) (mono (c - q.r)) d ≈
        alpha * extremalCoeff q.intermediate q.r := by
    unfold triLeft
    rw [fixedLeft_inner_couplingOrder q, fixedLeft_outer_couplingOrder q]
    exact Q'.eqv_trans _ _ _ hcongr
      (Q'.eqv_trans _ _ _ hscale
        (Q'.mul_eqv_congr_left alpha _ _ hext))
  intro hzero
  have hproduct : alpha * extremalCoeff q.intermediate q.r ≈ 0 :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm hcoeff) hzero
  exact mul_not_eqv_zero
    (by simpa only [alpha] using extremalCoeff_not_eqv_zero a q.k hk.1)
    (extremalCoeff_not_eqv_zero q.intermediate q.r hr.1)
    hproduct

/-- Every proof-carrying physical left channel has strictly positive exact
Hilbert--Schmidt weight. -/
theorem left_channel_weight_pos_all {a b c d : Nat}
    (q : FixedLeftCGChannel a b c d) :
    (0 : Q') < triLeftChannelWeight a b c d q.intermediate := by
  let C : Q' := triLeft a b c d q.intermediate
    (mono a) (mono (b - q.k)) (mono (c - q.r)) d
  have hC : ¬ C ≈ 0 := by
    simpa only [C] using fixedLeft_nonzero_monomial_pivot q
  have hsq : (0 : Q') < C * C := self_mul_pos_of_not_eqv_zero C hC
  have ha : (0 : Q') < tvBinomQ a a :=
    tvBinomQ_pos_of_le a a (Nat.le_refl a)
  have hb : (0 : Q') < tvBinomQ b (b - q.k) :=
    tvBinomQ_pos_of_le b (b - q.k) (Nat.sub_le b q.k)
  have hc : (0 : Q') < tvBinomQ c (c - q.r) :=
    tvBinomQ_pos_of_le c (c - q.r) (Nat.sub_le c q.r)
  have hd : (0 : Q') < symMonomialNormSq d d :=
    symMonomialNormSq_pos_of_le d d (Nat.le_refl d)
  have hsummand : (0 : Q') < triDiagonalSummand a b c d
      (triLeft a b c d q.intermediate)
      a (b - q.k) (c - q.r) d := by
    unfold triDiagonalSummand
    exact Q'.mul_pos
      (Q'.mul_pos (Q'.mul_pos (Q'.mul_pos ha hb) hc) hd) hsq
  have hle := diagonal_term_le a b c d
    (triLeft a b c d q.intermediate)
    a (b - q.k) (c - q.r) d
    (by omega) (by omega) (by omega) (by omega)
  exact Q'.pos_of_lt_of_le hsummand (by
    simpa only [triLeftChannelWeight] using hle)

/-! ## 2. Head-recursive finite sums matching the Schur row -/

/-- A finite sum in the same head-recursive orientation as `finiteDot`. -/
def finiteHeadSum : Nat → (Nat → Q') → Q'
  | 0, _ => 0
  | N + 1, f => f 0 + finiteHeadSum N (fun q => f (q + 1))

theorem finiteHeadSum_eqv_congr (N : Nat) (f g : Nat → Q')
    (h : ∀ q, q < N → f q ≈ g q) :
    finiteHeadSum N f ≈ finiteHeadSum N g := by
  induction N generalizing f g with
  | zero => exact Q'.eqv_refl 0
  | succ N ih =>
      simp only [finiteHeadSum]
      exact Q'.add_eqv_congr'
        (h 0 (by omega))
        (ih (fun q => f (q + 1)) (fun q => g (q + 1))
          (fun q hq => h (q + 1) (by omega)))

theorem finiteDot_eqv_congr_right (N : Nat)
    (row x y : Nat → Q')
    (h : ∀ q, q < N → x q ≈ y q) :
    finiteDot N row x ≈ finiteDot N row y := by
  induction N generalizing row x y with
  | zero => exact Q'.eqv_refl 0
  | succ N ih =>
      simp only [finiteDot]
      exact Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left (row 0) _ _ (h 0 (by omega)))
        (ih (fun q => row (q + 1)) (fun q => x (q + 1))
          (fun q => y (q + 1)) (fun q hq => h (q + 1) (by omega)))

theorem finiteDot_eq_finiteHeadSum_products (N : Nat)
    (row x : Nat → Q') :
    finiteDot N row x ≈ finiteHeadSum N (fun q => row q * x q) := by
  induction N generalizing row x with
  | zero => exact Q'.eqv_refl 0
  | succ N ih =>
      simp only [finiteDot, finiteHeadSum]
      exact Q'.add_eqv_congr' (Q'.eqv_refl _)
        (ih (fun q => row (q + 1)) (fun q => x (q + 1)))

theorem finiteHeadSum_mul_const (N : Nat) (f : Nat → Q') (c : Q') :
    finiteHeadSum N f * c ≈ finiteHeadSum N (fun q => f q * c) := by
  induction N generalizing f with
  | zero => exact Q'.zero_mul_eqv c
  | succ N ih =>
      simp only [finiteHeadSum]
      exact Q'.eqv_trans _ _ _
        (Q'.add_mul_eqv (f 0) (finiteHeadSum N (fun q => f (q + 1))) c)
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (ih (fun q => f (q + 1))))

/-! ## 3. Physical raw and normalized recoupling kernels -/

def physicalSchurRawKernelAt {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) : Q' :=
  let K := fixedLeftRightDiagonalCoeff qL qR 0
  (K * K) * triRightChannelWeight a b c d qR.intermediate

theorem physicalSchurRawKernelAt_nonnegative {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) :
    (0 : Q') ≤ physicalSchurRawKernelAt qL qR := by
  unfold physicalSchurRawKernelAt
  exact Q'.mul_nonneg _ _
    (qMulSelf_nonneg (fixedLeftRightDiagonalCoeff qL qR 0))
    (triRightChannelWeight_nonneg_all a b c d qR.intermediate)

def physicalSchurRawRowMass {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d) : Q' :=
  finiteHeadSum (fixedRightChannels a b c d).length
    (fun q => physicalSchurRawKernelAt qL (enumeratedRightChannel qL q))

/-- **Finite physical Parseval identity.**  The actual Schur row, together
with all-label pair-Casimir orthogonality of the right channels, decomposes
the exact left-channel norm into the weighted sum of squared recoupling
coefficients. -/
theorem physicalSchurRawRowMass_eq_leftWeight {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d) :
    physicalSchurRawRowMass qL ≈
      triLeftChannelWeight a b c d qL.intermediate := by
  let N := (fixedRightChannels a b c d).length
  let qR : Nat → FixedRightCGChannel a b c d :=
    fun q => enumeratedRightChannel qL q
  let K : Nat → Q' := fun q => fixedLeftRightDiagonalCoeff qL (qR q) 0
  let W : Nat → Q' :=
    fun q => triRightChannelWeight a b c d (qR q).intermediate
  let L := triLeft a b c d qL.intermediate
  let R : Nat → BForm → BForm → BForm → BForm :=
    fun q => triRight a b c d (qR q).intermediate
  have hexpand : triMapInner a b c d L L ≈
      triMapInner a b c d
        (rightChannelPrefix a b c d N (fun q => (qR q).p) K) L := by
    exact triMapInner_congr_left
      (by simpa only [N, qR, K, L, enumeratedRightChannel] using
        fixedLeft_directRightFixedOutput_schur qL)
  have hdot : triMapInner a b c d
        (rightChannelPrefix a b c d N (fun q => (qR q).p) K) L ≈
      finiteDot N K (fun q => triMapInner a b c d (R q) L) := by
    simpa only [R, qR, FixedRightCGChannel.intermediate,
      rightChannelLabel] using
      triMapInner_rightChannelPrefix a b c d N (fun q => (qR q).p) K L
  have hpairs : finiteDot N K (fun q => triMapInner a b c d (R q) L) ≈
      finiteDot N K (fun q => K q * W q) := by
    apply finiteDot_eqv_congr_right
    intro q hq
    exact Q'.eqv_trans _ _ _
      (triMapInner_symm a b c d (R q) L)
      (by simpa only [L, R, K, W, qR] using
        fixedLeft_schur_pairing_all qL q hq)
  have hsum : finiteDot N K (fun q => K q * W q) ≈
      physicalSchurRawRowMass qL := by
    refine Q'.eqv_trans _
      (finiteHeadSum N (fun q => K q * (K q * W q))) _
      (finiteDot_eq_finiteHeadSum_products N K (fun q => K q * W q)) ?_
    exact finiteHeadSum_eqv_congr N _ _ (fun q hq => by
      exact Q'.eqv_symm (Q'.mul_assoc_eqv (K q) (K q) (W q)))
  have hleft : triLeftChannelWeight a b c d qL.intermediate ≈
      physicalSchurRawRowMass qL := by
    simpa only [triLeftChannelWeight, L] using
      Q'.eqv_trans _ _ _ hexpand
        (Q'.eqv_trans _ _ _ hdot (Q'.eqv_trans _ _ _ hpairs hsum))
  exact Q'.eqv_symm hleft

/-- The normalized physical recoupling probability from one left channel to
one right channel. -/
def physicalSchurRecouplingKernelAt {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) : Q' :=
  Q'.divPos (physicalSchurRawKernelAt qL qR)
    (triLeftChannelWeight a b c d qL.intermediate)
    (left_channel_weight_pos_all qL)

theorem physicalSchurRecouplingKernelAt_nonnegative {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) :
    (0 : Q') ≤ physicalSchurRecouplingKernelAt qL qR := by
  unfold physicalSchurRecouplingKernelAt Q'.divPos
  exact Q'.mul_nonneg _ _
    (physicalSchurRawKernelAt_nonnegative qL qR)
    (Q'.le_of_lt (Q'.recipPos_pos _ _))

def physicalSchurRecouplingRowMass {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d) : Q' :=
  finiteHeadSum (fixedRightChannels a b c d).length
    (fun q => physicalSchurRecouplingKernelAt qL
      (enumeratedRightChannel qL q))

/-- **The physical SU(2) Schur kernel is row-normalized at every label.**
This is the weighted recoupling replacement for a false deterministic
permutation of canonical channel labels. -/
theorem physicalSchurRecouplingKernel_row_normalized {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d) :
    physicalSchurRecouplingRowMass qL ≈ 1 := by
  let WL := triLeftChannelWeight a b c d qL.intermediate
  let hWL := left_channel_weight_pos_all qL
  let r := Q'.recipPos WL hWL
  have hpull := finiteHeadSum_mul_const
    (fixedRightChannels a b c d).length
    (fun q => physicalSchurRawKernelAt qL (enumeratedRightChannel qL q)) r
  have hmass := physicalSchurRawRowMass_eq_leftWeight qL
  refine Q'.eqv_trans _ (physicalSchurRawRowMass qL * r) _ ?_ ?_
  · exact Q'.eqv_symm (by
      simpa only [physicalSchurRecouplingRowMass,
        physicalSchurRecouplingKernelAt, Q'.divPos, WL, hWL, r] using hpull)
  · exact Q'.eqv_trans _ (WL * r) _
      (Q'.mul_eqv_congr_right _ _ r hmass)
      (by simpa only [r] using Q'.mul_recipPos_eqv WL hWL)

/-! ## 4. Exact fence against conflating physical and factorial kernels -/

/-- The unnormalised physical Schur weight equals left weight times the
explicit factorial Racah kernel exactly when the previously isolated
arbitrary-label Racah-square residual holds. -/
theorem physicalSchurRawKernel_eq_leftWeight_mul_racah_iff
    {a b c d : Nat} (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) :
    physicalSchurRawKernelAt qL qR ≈
        triLeftChannelWeight a b c d qL.intermediate *
          racahKernel6 a b c d qL.intermediate qR.intermediate ↔
      CollapsedRacahSquareAt qL qR := by
  let K := fixedLeftRightDiagonalCoeff qL qR 0
  let WR := triRightChannelWeight a b c d qR.intermediate
  let WL := triLeftChannelWeight a b c d qL.intermediate
  let P := racahKernel6 a b c d qL.intermediate qR.intermediate
  have hcap := collapsedRacahSquare_iff_explicit_inverse_kernel_identity qL qR
  constructor
  · intro hraw
    apply hcap.mpr
    exact Q'.eqv_trans _ ((K * K) * WR) _
      (by simpa only [WL, P, WR, K, physicalSchurRawKernelAt] using
        Q'.eqv_symm hraw)
      (Q'.mul_comm_eqv (K * K) WR)
  · intro hsquare
    have h := hcap.mp hsquare
    exact Q'.eqv_trans _ (WR * (K * K)) _
      (by simpa only [physicalSchurRawKernelAt, K, WR] using
        Q'.mul_comm_eqv (K * K) WR)
      (by simpa only [WL, P, WR, K] using Q'.eqv_symm h)

/-- **Exact physical/factorial identification frontier.**  The unconditional
normalized physical Schur kernel equals `racahKernel6` at a channel pair iff
the explicit factorial-square residual holds there.  Thus Parseval
normalization is already closed, while the factorial closed form remains
honestly and precisely separated. -/
theorem physicalSchurRecouplingKernel_eq_racah_iff
    {a b c d : Nat} (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) :
    physicalSchurRecouplingKernelAt qL qR ≈
        racahKernel6 a b c d qL.intermediate qR.intermediate ↔
      CollapsedRacahSquareAt qL qR := by
  let WL := triLeftChannelWeight a b c d qL.intermediate
  let P := racahKernel6 a b c d qL.intermediate qR.intermediate
  let raw := physicalSchurRawKernelAt qL qR
  let hWL := left_channel_weight_pos_all qL
  have hrawIff := physicalSchurRawKernel_eq_leftWeight_mul_racah_iff qL qR
  constructor
  · intro hnormalized
    apply hrawIff.mp
    refine Q'.eqv_trans _
      (physicalSchurRecouplingKernelAt qL qR * WL) _ ?_ ?_
    · exact Q'.eqv_symm (by
        simpa only [physicalSchurRecouplingKernelAt, raw, WL, hWL] using
          Q'.divPos_mul_eqv raw WL hWL)
    · exact Q'.eqv_trans _ (P * WL) _
        (Q'.mul_eqv_congr_right _ _ WL (by simpa only [P] using hnormalized))
        (Q'.mul_comm_eqv P WL)
  · intro hsquare
    have hraw := hrawIff.mpr hsquare
    apply Q'.mul_left_cancel_of_pos hWL
    refine Q'.eqv_trans _
      (physicalSchurRecouplingKernelAt qL qR * WL) _ ?_ ?_
    · exact Q'.mul_comm_eqv WL (physicalSchurRecouplingKernelAt qL qR)
    refine Q'.eqv_trans _ raw _
      (by simpa only [physicalSchurRecouplingKernelAt, raw, WL, hWL] using
        Q'.divPos_mul_eqv raw WL hWL) ?_
    simpa only [WL, P] using hraw

/-! ## 5. A fractional audit on the fundamental block -/

private def threeQuarters : Q' := Q'.mkPos 3 4 (by decide)

theorem fundamental_physicalSchurKernel_values :
    physicalSchurRecouplingKernelAt
        fundamentalFixedLeftSinglet fundamentalFixedRightSinglet ≈
          YMGap.Continuum.PentagonRelation.oneQuarter ∧
    physicalSchurRecouplingKernelAt
        fundamentalFixedLeftSinglet fundamentalFixedRightTriplet ≈ threeQuarters ∧
    physicalSchurRecouplingKernelAt
        fundamentalFixedLeftTriplet fundamentalFixedRightSinglet ≈ threeQuarters ∧
    physicalSchurRecouplingKernelAt
        fundamentalFixedLeftTriplet fundamentalFixedRightTriplet ≈
          YMGap.Continuum.PentagonRelation.oneQuarter := by
  decide

end YMGap.Continuum.SU2PhysicalSchurRecouplingKernel

#print axioms YMGap.Continuum.SU2PhysicalSchurRecouplingKernel.fixedLeft_nonzero_monomial_pivot
#print axioms YMGap.Continuum.SU2PhysicalSchurRecouplingKernel.left_channel_weight_pos_all
#print axioms YMGap.Continuum.SU2PhysicalSchurRecouplingKernel.physicalSchurRawKernelAt_nonnegative
#print axioms YMGap.Continuum.SU2PhysicalSchurRecouplingKernel.physicalSchurRawRowMass_eq_leftWeight
#print axioms YMGap.Continuum.SU2PhysicalSchurRecouplingKernel.physicalSchurRecouplingKernelAt_nonnegative
#print axioms YMGap.Continuum.SU2PhysicalSchurRecouplingKernel.physicalSchurRecouplingKernel_row_normalized
#print axioms YMGap.Continuum.SU2PhysicalSchurRecouplingKernel.physicalSchurRawKernel_eq_leftWeight_mul_racah_iff
#print axioms YMGap.Continuum.SU2PhysicalSchurRecouplingKernel.physicalSchurRecouplingKernel_eq_racah_iff
#print axioms YMGap.Continuum.SU2PhysicalSchurRecouplingKernel.fundamental_physicalSchurKernel_values
