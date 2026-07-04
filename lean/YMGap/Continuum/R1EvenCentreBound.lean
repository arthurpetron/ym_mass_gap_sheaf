/-
Track B / local-CLT — the PROVED even-centre variance bound `V(even N) ≤ 3/2`
(`2·dmomNfull ≤ 3·acNfull`), the residual of the even (comfortable) cell of R1.

# What this file PROVES (axiom-clean, no `sorry`)

For every even centre `N = 2m` (`m ≥ 1`), `0 ≤ w ≤ 1/2`:

    `centreBound` :  2·dmomNfull w (2m)  ≤  3·acNfull w (2m)   (i.e. `⟨D²⟩_{2m} ≤ 3/2`).

This closes the theta-layer residual of the even cell of R1 with a LOOSE constant `3/2`
(margin `1` in the cell algebra) — no infinite theta needed.

## The argument (all elementary and constructive)

`2·dmomNfull − 3·acNfull = Σ_p (2·D_p² − 3)·μ_p`, `D_p = N − 2p`, `μ_p = coeffW(w,p)·coeffW(w,N−p)`.
For even `N = 2m` the central term `p = m` (`D = 0`) contributes `−3·μ_m` (the dominant negative);
every `|D| ≥ 2` term is positive.  Bounding each off-central `μ_p ≤ (1/4)^{|m−p|²}·μ_m` by the
ρ-graded super-log-concavity (`DiscreteLaplaceMargin.coeffW_rect_graded`, ρ = 1/4 on `w ≤ 1/2`),
reflecting the symmetric sum onto its forward tail, and dominating that tail by a geometric series
(ratio `1/10`, closed at `Σ ≤ 3/2` — a uniform-in-`m` invariant) gives
`Σ_p (2D²−3)μ_p ≤ μ_m·(2·Σ_{k≥1}(8k²−3)(1/4)^{k²} − 3) < 0`, hence `2·dmomNfull ≤ 3·acNfull`.

The `w = 0` degenerate coupling is handled separately (all moments vanish for `N ≥ 1`).

# Axiom gate (AGENTS.md Rule 1 / Rule 8)

Every load-bearing declaration is axiom-checked at file end; permitted output is
`propext` / `Quot.sound` only (via the `Q'` setoid).  No `Classical.*`, no `native_decide`, no
`sorry`, no custom `axiom`.  All witnesses are `Type`-level / `Q'`-valued data.
-/
import YMGap.Continuum.DiscreteLaplaceMargin
import YMGap.Continuum.EnvelopeClosure
import YMGap.Continuum.CubeRatioBounds

namespace YMGap.Continuum.R1EvenCentreBound

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.MeanComplementCovariance
open YMGap.Continuum.AutoconvGershgorin
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.CircleFourierPowerModel
open YMGap.Continuum.AcNReserveAnalytic
open YMGap.Continuum.FusionCoreStepRoundA
open YMGap.Continuum.FusionCoreStepRoundC
open YMGap.Continuum.DiscreteLaplaceMargin

theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

/-- Cancellation-free ring closer for `Q'.eqv`. -/
local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg, Int.neg_add,
               Int.neg_neg, Int.one_mul, Int.mul_one];
             ac_rfl))

/-- distance |m-p| in Nat. -/
def edp (m p : Nat) : Nat := (m - p) + (p - m)

theorem edp_self (m : Nat) : edp m m = 0 := by unfold edp; omega

theorem two_mul_sub (a b : Nat) : 2 * a - 2 * b = 2 * (a - b) := by omega

-- four_sq
theorem four_sq (d : Nat) : (2 * d) * (2 * d) = 4 * (d * d) := by
  rw [Nat.mul_mul_mul_comm]

theorem dsq_eq (m p : Nat) : dsq p (2 * m) = 4 * (edp m p * edp m p) := by
  show (2 * m - 2 * p) * (2 * m - 2 * p) + (2 * p - 2 * m) * (2 * p - 2 * m)
      = 4 * (edp m p * edp m p)
  rcases Nat.le_total p m with h | h
  · have e1 : 2 * m - 2 * p = 2 * (m - p) := two_mul_sub m p
    have e2 : 2 * p - 2 * m = 0 := by omega
    have e3 : edp m p = m - p := by unfold edp; omega
    rw [e1, e2, e3]
    rw [four_sq]
    omega
  · have e1 : 2 * p - 2 * m = 2 * (p - m) := two_mul_sub p m
    have e2 : 2 * m - 2 * p = 0 := by omega
    have e3 : edp m p = p - m := by unfold edp; omega
    rw [e1, e2, e3]
    rw [four_sq]
    omega

theorem ofNat_mul_eqv (a b : Nat) :
    (Q'.ofNat (a * b)).eqv (Q'.ofNat a * Q'.ofNat b) := by
  have hd1 : ((Q'.ofNat a * Q'.ofNat b).den : Int) = 1 := by rw [Q'.mul_den_cast]; rfl
  have hd2 : ((Q'.ofNat (a * b)).den : Int) = 1 := rfl
  show ((a * b : Nat) : Int) * ((Q'.ofNat a * Q'.ofNat b).den : Int)
     = (Q'.ofNat a * Q'.ofNat b).num * ((Q'.ofNat (a * b)).den : Int)
  rw [hd1, hd2]
  show ((a * b : Nat) : Int) * 1 = ((a : Int) * (b : Int)) * 1
  rw [Int.mul_one, Int.mul_one]; exact Int.natCast_mul a b

-- qpow-4 identity: ofNat(4^n) * qpow quarter n ≃ 1
theorem qpow_quarter_inv (n : Nat) :
    (Q'.ofNat (4 ^ n) * qpow quarter n).eqv 1 := by
  induction n with
  | zero =>
      show (Q'.ofNat (4 ^ 0) * qpow quarter 0).eqv 1
      exact Q'.eqv_trans _ _ _ (Q'.mul_one_eqv _) (by decide)
  | succ k ih =>
      show (Q'.ofNat (4 ^ (k + 1)) * qpow quarter (k + 1)).eqv 1
      have hpow : (4 : Nat) ^ (k + 1) = 4 * 4 ^ k := by rw [Nat.pow_succ]; omega
      have hqp : qpow quarter (k + 1) = qpow quarter k * quarter := rfl
      rw [hpow, hqp]
      -- (ofNat 4 * ofNat(4^k)) * (qpow quarter k * quarter)
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (Q'.ofNat (4 * 4 ^ k)) (Q'.ofNat 4 * Q'.ofNat (4 ^ k))
          (qpow quarter k * quarter) (ofNat_mul_eqv 4 (4 ^ k))) ?_
      -- reassociate to (ofNat(4^k) * qpow quarter k) * (ofNat 4 * quarter)
      have hrew : ((Q'.ofNat 4 * Q'.ofNat (4 ^ k)) * (qpow quarter k * quarter)).eqv
          ((Q'.ofNat (4 ^ k) * qpow quarter k) * (Q'.ofNat 4 * quarter)) := by
        ring_qeqv
      refine Q'.eqv_trans _ _ _ hrew ?_
      have h4q : (Q'.ofNat 4 * quarter).eqv 1 := by decide
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ h4q) ?_
      exact Q'.eqv_trans _ _ _ (Q'.mul_one_eqv _) ih

/-! ## Finite-sum reflection machinery. -/

theorem fsum_shift_cons (g : Nat → Q') :
    ∀ n, (fsum g (n + 1)).eqv (g 0 + fsum (fun i => g (i + 1)) n)
  | 0 => by
    show ((0 : Q') + g 0).eqv (g 0 + (0 : Q'))
    refine Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.zero_add' (g 0))) ?_
    exact Q'.eqv_symm (Q'.eqv_of_eq (Q'.add_zero' (g 0)))
  | n + 1 => by
    show (fsum g (n + 1) + g (n + 1)).eqv
        (g 0 + (fsum (fun i => g (i + 1)) n + g (n + 1)))
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (g (n + 1)) (fsum_shift_cons g n)) ?_
    exact Q'.add_assoc_eqv (g 0) (fsum (fun i => g (i + 1)) n) (g (n + 1))

/-- Split a partial sum at `a`: `Σ_{p<a+b} h = Σ_{p<a} h + Σ_{k<b} h(a+k)`. -/
theorem fsum_split (h : Nat → Q') (a : Nat) :
    ∀ b, (fsum h (a + b)).eqv (fsum h a + fsum (fun k => h (a + k)) b)
  | 0 => by
    show (fsum h a).eqv (fsum h a + (0 : Q'))
    exact Q'.eqv_symm (Q'.eqv_of_eq (Q'.add_zero' (fsum h a)))
  | b + 1 => by
    show (fsum h (a + b) + h (a + b)).eqv
        (fsum h a + (fsum (fun k => h (a + k)) b + h (a + b)))
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (h (a + b)) (fsum_split h a b)) ?_
    exact Q'.add_assoc_eqv (fsum h a) (fsum (fun k => h (a + k)) b) (h (a + b))

/-- Reversal of a partial sum over `[0,n]`: `Σ_{p≤n} G(n-p) = Σ_{k≤n} G(k)`. -/
theorem revSum (G : Nat → Q') :
    ∀ n, (fsum (fun p => G (n - p)) (n + 1)).eqv (fsum G (n + 1))
  | 0 => Q'.eqv_refl _
  | n + 1 => by
    refine Q'.eqv_trans _ _ _ (fsum_shift_cons (fun p => G ((n + 1) - p)) (n + 1)) ?_
    -- G((n+1)-0) + Σ_{i<n+1} G((n+1)-(i+1))
    have hcongr : (fsum (fun i => G ((n + 1) - (i + 1))) (n + 1)).eqv
        (fsum (fun i => G (n - i)) (n + 1)) := by
      refine fsum_eqv_congr _ _ (fun i => ?_) (n + 1)
      exact Q'.eqv_of_eq (congrArg G (by omega))
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hcongr) ?_
    have hib : (fsum (fun i => G (n - i)) (n + 1)).eqv (fsum G (n + 1)) := revSum G n
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hib) ?_
    -- G(n+1-0) + fsum G (n+1) ; note (n+1)-0 = n+1
    show (G (n + 1) + fsum G (n + 1)).eqv (fsum G (n + 1) + G (n + 1))
    exact Q'.add_comm_eqv (G (n + 1)) (fsum G (n + 1))

/-! ## Nat exponential bounds for the geometric tail. -/

theorem sqBound : ∀ k, (k + 2) * (k + 2) ≤ 4 * 16 ^ k
  | 0 => by decide
  | k + 1 => by
    have ih := sqBound k
    have h1 : k + 3 ≤ 4 * (k + 2) := by omega
    have h2 : (k + 3) * (k + 3) ≤ (4 * (k + 2)) * (4 * (k + 2)) := Nat.mul_le_mul h1 h1
    have h3 : (4 * (k + 2)) * (4 * (k + 2)) = 16 * ((k + 2) * (k + 2)) := by
      rw [Nat.mul_mul_mul_comm]
    have h4 : 16 * ((k + 2) * (k + 2)) ≤ 16 * (4 * 16 ^ k) := Nat.mul_le_mul_left 16 ih
    have h5 : (16 : Nat) ^ (k + 1) = 16 * 16 ^ k := by rw [Nat.pow_succ]; omega
    have e6 : ((k + 1) + 2) = (k + 3) := by omega
    rw [e6, h5]
    omega

theorem pow4_eq : ∀ k, (4 : Nat) ^ (2 * k + 3) = 64 * 16 ^ k
  | 0 => by decide
  | k + 1 => by
    have ih := pow4_eq k
    have h5 : (16 : Nat) ^ (k + 1) = 16 * 16 ^ k := by rw [Nat.pow_succ]; omega
    have he : (4 : Nat) ^ (2 * (k + 1) + 3) = 16 * 4 ^ (2 * k + 3) := by
      rw [show 2 * (k + 1) + 3 = (2 * k + 3) + 2 by omega, Nat.pow_add,
        show (4:Nat)^2 = 16 from rfl]
      omega
    rw [he, ih, h5]; omega

theorem natTail (k : Nat) : 2 * (8 * (k + 2) * (k + 2) - 3) ≤ 4 ^ (2 * k + 3) := by
  have hs := sqBound k
  have hp := pow4_eq k
  rw [hp]
  -- 2*(8(k+2)² - 3) ≤ 16(k+2)² ≤ 64·16^k
  have : 2 * (8 * (k + 2) * (k + 2) - 3) ≤ 16 * ((k + 2) * (k + 2)) := by
    have : 8 * (k + 2) * (k + 2) = 8 * ((k + 2) * (k + 2)) := by rw [Nat.mul_assoc]
    omega
  omega

/-! ## The geometric tail bound `Σ_{k<m} bpos k ≤ 3/2`. -/

def tenth : Q' := Q'.mkPos 1 10 (by decide)
def ten9 : Q' := Q'.mkPos 10 9 (by decide)
def threeHalf : Q' := Q'.mkPos 3 2 (by decide)
def half' : Q' := Q'.mkPos 1 2 (by decide)

/-- `bpos k = (8(k+1)²−3)·(1/4)^{(k+1)²}` — the (positive) `k`-th tail term. -/
def bpos (k : Nat) : Q' :=
  Q'.ofNat (8 * (k + 1) * (k + 1) - 3) * qpow quarter ((k + 1) * (k + 1))

theorem quarter_nonneg : (0 : Q') ≤ quarter := by decide

theorem bpos_nonneg (k : Nat) : (0 : Q') ≤ bpos k :=
  Q'.mul_nonneg _ _ (ofNatNonneg _) (qpow_nonneg quarter quarter_nonneg _)

theorem sq_succ (a : Nat) : (a + 1) * (a + 1) = a * a + 2 * a + 1 := by
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]; omega

/-- The geometric ratio bound `bpos (k+1) ≤ (1/10)·bpos k`. -/
theorem bpos_ratio (k : Nat) : bpos (k + 1) ≤ tenth * bpos k := by
  have hqn : (0 : Q') ≤ qpow quarter ((k + 1) * (k + 1)) :=
    qpow_nonneg quarter quarter_nonneg _
  have hqpos3 : (0 : Q') ≤ qpow quarter (2 * k + 3) :=
    qpow_nonneg quarter quarter_nonneg _
  -- (k+2)² = (k+1)² + (2k+3)
  have hexp : (k + 2) * (k + 2) = (k + 1) * (k + 1) + (2 * k + 3) := by
    rw [sq_succ (k + 1)]; rw [sq_succ k]; omega
  -- sub-step (a): ofNat(8(k+2)²-3) * qpow quarter (2k+3) ≤ 1/2
  have hle2 : Q'.ofNat 2 * Q'.ofNat (8 * (k + 2) * (k + 2) - 3)
      ≤ Q'.ofNat (4 ^ (2 * k + 3)) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (ofNat_mul_eqv 2 (8 * (k + 2) * (k + 2) - 3)))
      (CReal.ofNat_le_ofNat (natTail k))
  have hmul3 : (Q'.ofNat 2 * Q'.ofNat (8 * (k + 2) * (k + 2) - 3)) * qpow quarter (2 * k + 3)
      ≤ Q'.ofNat (4 ^ (2 * k + 3)) * qpow quarter (2 * k + 3) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hle2 hqpos3
  have hmul3' : Q'.ofNat 2
      * (Q'.ofNat (8 * (k + 2) * (k + 2) - 3) * qpow quarter (2 * k + 3)) ≤ 1 := by
    refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv ?_)
      (Q'.le_trans' _ _ _ hmul3 (Q'.le_of_eqv (qpow_quarter_inv (2 * k + 3))))
    exact Q'.mul_assoc_eqv (Q'.ofNat 2)
      (Q'.ofNat (8 * (k + 2) * (k + 2) - 3)) (qpow quarter (2 * k + 3))
  have hZhalf : Q'.ofNat (8 * (k + 2) * (k + 2) - 3) * qpow quarter (2 * k + 3) ≤ half' := by
    have hstep : half' * (Q'.ofNat 2
        * (Q'.ofNat (8 * (k + 2) * (k + 2) - 3) * qpow quarter (2 * k + 3))) ≤ half' * 1 :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ hmul3' (by decide)
    have eL : (half' * (Q'.ofNat 2
        * (Q'.ofNat (8 * (k + 2) * (k + 2) - 3) * qpow quarter (2 * k + 3)))).eqv
        (Q'.ofNat (8 * (k + 2) * (k + 2) - 3) * qpow quarter (2 * k + 3)) := by
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv half' (Q'.ofNat 2)
          (Q'.ofNat (8 * (k + 2) * (k + 2) - 3) * qpow quarter (2 * k + 3)))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (half' * Q'.ofNat 2) 1
          (Q'.ofNat (8 * (k + 2) * (k + 2) - 3) * qpow quarter (2 * k + 3)) (by decide)) ?_
      exact Q'.one_mul_eqv _
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv eL)
      (Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv (Q'.mul_one_eqv half')))
  -- sub-step (b): 1/2 ≤ tenth * ofNat(8(k+1)²-3)
  have hY5 : Q'.ofNat 5 ≤ Q'.ofNat (8 * (k + 1) * (k + 1) - 3) := by
    refine CReal.ofNat_le_ofNat ?_
    have hone : 1 ≤ (k + 1) * (k + 1) :=
      Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.succ_ne_zero k) (Nat.succ_ne_zero k))
    have hassoc : 8 * (k + 1) * (k + 1) = 8 * ((k + 1) * (k + 1)) := by rw [Nat.mul_assoc]
    omega
  have hbhalf : half' ≤ tenth * Q'.ofNat (8 * (k + 1) * (k + 1) - 3) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (by decide : half'.eqv (tenth * Q'.ofNat 5)))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hY5 (by decide))
  have hscalar : Q'.ofNat (8 * (k + 2) * (k + 2) - 3) * qpow quarter (2 * k + 3)
      ≤ tenth * Q'.ofNat (8 * (k + 1) * (k + 1) - 3) :=
    Q'.le_trans' _ _ _ hZhalf hbhalf
  -- assemble  (bpos (k+1) is defeq to the `k+2` form)
  show Q'.ofNat (8 * (k + 2) * (k + 2) - 3) * qpow quarter ((k + 2) * (k + 2))
      ≤ tenth * (Q'.ofNat (8 * (k + 1) * (k + 1) - 3) * qpow quarter ((k + 1) * (k + 1)))
  have hqsplit : (qpow quarter ((k + 2) * (k + 2))).eqv
      (qpow quarter ((k + 1) * (k + 1)) * qpow quarter (2 * k + 3)) := by
    rw [hexp]; exact HeatKernelRGStep.qpow_add quarter ((k + 1) * (k + 1)) (2 * k + 3)
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ hqsplit)) ?_
  have erear : (Q'.ofNat (8 * (k + 2) * (k + 2) - 3)
      * (qpow quarter ((k + 1) * (k + 1)) * qpow quarter (2 * k + 3))).eqv
      ((Q'.ofNat (8 * (k + 2) * (k + 2) - 3) * qpow quarter (2 * k + 3))
        * qpow quarter ((k + 1) * (k + 1))) := by ring_qeqv
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv erear) ?_
  have hstep2 : (Q'.ofNat (8 * (k + 2) * (k + 2) - 3) * qpow quarter (2 * k + 3))
      * qpow quarter ((k + 1) * (k + 1))
      ≤ (tenth * Q'.ofNat (8 * (k + 1) * (k + 1) - 3)) * qpow quarter ((k + 1) * (k + 1)) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hscalar hqn
  refine Q'.le_trans' _ _ _ hstep2 ?_
  have erear2 : ((tenth * Q'.ofNat (8 * (k + 1) * (k + 1) - 3))
      * qpow quarter ((k + 1) * (k + 1))).eqv
      (tenth * (Q'.ofNat (8 * (k + 1) * (k + 1) - 3) * qpow quarter ((k + 1) * (k + 1)))) := by
    ring_qeqv
  exact Q'.le_of_eqv erear2

/-- Tail invariant `Σ_{k<m} bpos k + (10/9)·bpos m ≤ 3/2`. -/
theorem bpos_invariant : ∀ m, fsum bpos m + ten9 * bpos m ≤ threeHalf
  | 0 => by
    show (0 : Q') + ten9 * bpos 0 ≤ threeHalf
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.zero_add' _))) ?_
    -- ten9 * bpos 0 = (10/9)*(5/4) = 25/18 ≤ 27/18
    have hb0 : bpos 0 = Q'.ofNat 5 * qpow quarter 1 := rfl
    rw [hb0]
    exact (by decide : ten9 * (Q'.ofNat 5 * qpow quarter 1) ≤ threeHalf)
  | m + 1 => by
    have ih := bpos_invariant m
    -- Σ_{k<m+1} = Σ_{k<m} + bpos m ; ratio bpos(m+1) ≤ tenth*bpos m
    have hr := bpos_ratio m
    show (fsum bpos m + bpos m) + ten9 * bpos (m + 1) ≤ threeHalf
    -- ten9 * bpos(m+1) ≤ ten9 * (tenth * bpos m)
    have h1 : ten9 * bpos (m + 1) ≤ ten9 * (tenth * bpos m) :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ hr (by decide)
    have h2 : (fsum bpos m + bpos m) + ten9 * bpos (m + 1)
        ≤ (fsum bpos m + bpos m) + ten9 * (tenth * bpos m) :=
      Q'.add_le_add_left _ _ _ h1
    refine Q'.le_trans' _ _ _ h2 ?_
    -- (Σ + bpos m) + ten9*(tenth*bpos m) ≃ Σ + (10/9)*bpos m  (since 1 + (10/9)(1/10) = 10/9)
    have erear : ((fsum bpos m + bpos m) + ten9 * (tenth * bpos m)).eqv
        (fsum bpos m + ten9 * bpos m) := by
      -- bpos m + ten9*(tenth*bpos m) ≃ ten9 * bpos m, then reassoc
      have hnum : ((1 : Q') + ten9 * tenth).eqv ten9 := by decide
      have hcoef : (bpos m + ten9 * (tenth * bpos m)).eqv (ten9 * bpos m) := by
        have hd : (bpos m + ten9 * (tenth * bpos m)).eqv ((1 + ten9 * tenth) * bpos m) := by
          ring_qeqv
        exact Q'.eqv_trans _ _ _ hd (Q'.mul_eqv_congr_right _ _ _ hnum)
      refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (fsum bpos m) (bpos m) (ten9 * (tenth * bpos m))) ?_
      exact Q'.add_eqv_congr_left _ _ _ hcoef
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv erear) ih

theorem tailBound (m : Nat) : fsum bpos m ≤ threeHalf := by
  have hnn : (0 : Q') ≤ ten9 * bpos m :=
    Q'.mul_nonneg _ _ (by decide) (bpos_nonneg m)
  exact Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg (fsum bpos m) (ten9 * bpos m) hnn) (bpos_invariant m)

/-! ## Signed arithmetic helpers. -/

theorem le_of_add_le_add_right' {a b c : Q'} (h : a + c ≤ b + c) : a ≤ b := by
  have h2 : (a + c) + -c ≤ (b + c) + -c := Q'.add_le_add_right _ _ (-c) h
  have ea : ((a + c) + -c).eqv a := by
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a c (-c)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left a _ _ (Q'.add_neg_self_eqv c)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' a)
  have eb : ((b + c) + -c).eqv b := by
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv b c (-c)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left b _ _ (Q'.add_neg_self_eqv c)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' b)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv ea) (Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv eb))

/-- `P + S ≤ R + Q → P + -Q ≤ R + -S`. -/
theorem flip_sub {P Q R S : Q'} (h : P + S ≤ R + Q) : P + -Q ≤ R + -S := by
  have eL : ((P + -Q) + (Q + S)).eqv (P + S) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv P (-Q) (Q + S)) ?_
    refine Q'.add_eqv_congr_left P _ _ ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv (-Q) Q S)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ S (Q'.neg_add_self_eqv Q)) ?_
    exact Q'.eqv_of_eq (Q'.zero_add' S)
  have eR : ((R + -S) + (Q + S)).eqv (R + Q) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv R (-S) (Q + S)) ?_
    refine Q'.add_eqv_congr_left R _ _ ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv (-S) Q S)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ S (Q'.add_comm_eqv (-S) Q)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv Q (-S) S) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left Q (-S + S) 0 (Q'.neg_add_self_eqv S)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' Q)
  have key : (P + -Q) + (Q + S) ≤ (R + -S) + (Q + S) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv eL) (Q'.le_trans' _ _ _ h (Q'.ge_of_eqv eR))
  exact le_of_add_le_add_right' key

/-- `3·b + κ·a ≤ 3·a + κ·b` from `a ≤ b` and `3 ≤ κ` (sign-free rearrangement core). -/
theorem coreMono {a b κ : Q'} (hab : a ≤ b) (h3κ : Q'.ofNat 3 ≤ κ) :
    Q'.ofNat 3 * b + κ * a ≤ Q'.ofNat 3 * a + κ * b := by
  -- t := b + -a ≥ 0, b ≃ a + t
  have ht : (0 : Q') ≤ b + -a := by
    have := Q'.add_le_add_right a b (-a) hab
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.add_neg_self_eqv a)) this
  have hbt : b.eqv (a + (b + -a)) := Q'.eqv_symm (q_add_add_neg_cancel a b)
  -- 3t ≤ κt
  have h3t : Q'.ofNat 3 * (b + -a) ≤ κ * (b + -a) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ h3κ ht
  -- rewrite both sides via b ≃ a + t
  have eL : (Q'.ofNat 3 * b + κ * a).eqv
      ((Q'.ofNat 3 * a + κ * a) + Q'.ofNat 3 * (b + -a)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (κ * a) (Q'.mul_eqv_congr_left (Q'.ofNat 3) _ _ hbt)) ?_
    -- 3*(a+t) + κa ≃ (3a + κa) + 3t
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (κ * a) (Q'.mul_add_eqv (Q'.ofNat 3) a (b + -a))) ?_
    ring_qeqv
  have eR : (Q'.ofNat 3 * a + κ * b).eqv
      ((Q'.ofNat 3 * a + κ * a) + κ * (b + -a)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_left κ _ _ hbt)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (Q'.mul_add_eqv κ a (b + -a))) ?_
    ring_qeqv
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv eL) (Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv eR))
  exact Q'.add_le_add_left _ _ _ h3t

/-! ## `2·T ≃ T + T` and the general reflection identity. -/

theorem two_mul_eqv (T : Q') : (Q'.ofNat 2 * T).eqv (T + T) := by
  have h : (Q'.ofNat 2).eqv (1 + 1) := by decide
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ T h) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (1 + 1) T) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv T 1 1) ?_
  exact Q'.add_eqv_congr' (Q'.mul_one_eqv T) (Q'.mul_one_eqv T)

/-- The left half is the forward tail (reversal). -/
theorem leftHalf_eq (G : Nat → Q') : ∀ m,
    (fsum (fun p => G (edp m p)) m).eqv (fsum (fun k => G (k + 1)) m)
  | 0 => Q'.eqv_refl _
  | m + 1 => by
    have hc : (fsum (fun p => G (edp (m + 1) p)) (m + 1)).eqv
        (fsum (fun p => G ((m + 1) - p)) (m + 1)) := by
      refine fsum_eqv_congr_lt _ _ (m + 1) (fun p hp => ?_)
      exact Q'.eqv_of_eq (congrArg G (by unfold edp; omega))
    refine Q'.eqv_trans _ _ _ hc ?_
    have hF : (fsum (fun p => G ((m + 1) - p)) (m + 1)).eqv
        (fsum (fun p => (fun x => G (x + 1)) (m - p)) (m + 1)) := by
      refine fsum_eqv_congr_lt _ _ (m + 1) (fun p hp => ?_)
      exact Q'.eqv_of_eq (congrArg G (by omega))
    refine Q'.eqv_trans _ _ _ hF ?_
    exact revSum (fun x => G (x + 1)) m

/-- The reflection identity for a symmetric-about-`m` sum. -/
theorem reflect_sum (G : Nat → Q') (m : Nat) :
    (fsum (fun p => G (edp m p)) (2 * m + 1)).eqv
      (G 0 + Q'.ofNat 2 * fsum (fun k => G (k + 1)) m) := by
  have hidx : 2 * m + 1 = (m + 1) + m := by omega
  rw [hidx]
  refine Q'.eqv_trans _ _ _ (fsum_split (fun p => G (edp m p)) (m + 1) m) ?_
  have hA : (fsum (fun p => G (edp m p)) (m + 1)).eqv
      (fsum (fun k => G (k + 1)) m + G 0) := by
    show (fsum (fun p => G (edp m p)) m + G (edp m m)).eqv
        (fsum (fun k => G (k + 1)) m + G 0)
    exact Q'.add_eqv_congr' (leftHalf_eq G m) (Q'.eqv_of_eq (congrArg G (edp_self m)))
  have hB : (fsum (fun k => G (edp m (m + 1 + k))) m).eqv (fsum (fun k => G (k + 1)) m) := by
    refine fsum_eqv_congr _ _ (fun k => ?_) m
    exact Q'.eqv_of_eq (congrArg G (by unfold edp; omega))
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hA hB) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv (fsum (fun k => G (k + 1)) m) (G 0) (fsum (fun k => G (k + 1)) m)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv (G 0) (fsum (fun k => G (k + 1)) m))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv (fsum (fun k => G (k + 1)) m)
      (fsum (fun k => G (k + 1)) m) (G 0))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_comm_eqv (fsum (fun k => G (k + 1)) m + fsum (fun k => G (k + 1)) m) (G 0)) ?_
  exact Q'.add_eqv_congr_left (G 0) _ _ (Q'.eqv_symm (two_mul_eqv (fsum (fun k => G (k + 1)) m)))

/-! ## The reflected coefficient sequence `Gc`. -/

theorem coeffCancel (A x : Q') : (x + -(A + x)).eqv (-A) := by
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left x _ _ (Q'.neg_add_eqv A x)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left x _ _ (Q'.add_comm_eqv (-A) (-x))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv x (-x) (-A))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ (-A) (Q'.add_neg_self_eqv x)) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' (-A))

/-- `Gc d = (3 − 8d²)·(1/4)^{d²}` in signed form. -/
def Gc (d : Nat) : Q' :=
  Q'.ofNat 3 * qpow quarter (d * d) + -(Q'.ofNat (8 * d * d) * qpow quarter (d * d))

theorem Gc_zero : (Gc 0).eqv (Q'.ofNat 3) := by
  show (Q'.ofNat 3 * qpow quarter (0 * 0) + -(Q'.ofNat (8 * 0 * 0) * qpow quarter (0 * 0))).eqv
      (Q'.ofNat 3)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.mul_one_eqv (Q'.ofNat 3))
      (Q'.neg_eqv_congr _ 0 (Q'.zero_mul_eqv _))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ 0 ?_) (Q'.eqv_of_eq (Q'.add_zero' _))
  show (-(0 : Q')).eqv 0
  decide

theorem Gc_succ (k : Nat) : (Gc (k + 1)).eqv (-(bpos k)) := by
  -- Gc(k+1) = 3·Q + -(ofNat(8(k+1)²)·Q) ; bpos k = ofNat(8(k+1)²-3)·Q,  Q = qpow quarter ((k+1)²)
  have hW : 8 * (k + 1) * (k + 1) = (8 * (k + 1) * (k + 1) - 3) + 3 := by
    have : 8 * (k + 1) * (k + 1) = 8 * ((k + 1) * (k + 1)) := by rw [Nat.mul_assoc]
    have hone : 1 ≤ (k + 1) * (k + 1) :=
      Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.succ_ne_zero k) (Nat.succ_ne_zero k))
    omega
  -- coefficient identity  3 + -(ofNat(8(k+1)²)) ≃ -(ofNat(8(k+1)²-3))
  have hcoef : (Q'.ofNat 3 + -(Q'.ofNat (8 * (k + 1) * (k + 1)))).eqv
      (-(Q'.ofNat (8 * (k + 1) * (k + 1) - 3))) := by
    have hsplit : (Q'.ofNat (8 * (k + 1) * (k + 1))).eqv
        (Q'.ofNat (8 * (k + 1) * (k + 1) - 3) + Q'.ofNat 3) := by
      rw [hW]; exact Q'.ofNat_add_eqv (8 * (k + 1) * (k + 1) - 3) 3
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (Q'.ofNat 3) _ _ (Q'.neg_eqv_congr _ _ hsplit)) ?_
    exact coeffCancel (Q'.ofNat (8 * (k + 1) * (k + 1) - 3)) (Q'.ofNat 3)
  -- assemble
  show (Q'.ofNat 3 * qpow quarter ((k + 1) * (k + 1))
      + -(Q'.ofNat (8 * (k + 1) * (k + 1)) * qpow quarter ((k + 1) * (k + 1)))).eqv
      (-(Q'.ofNat (8 * (k + 1) * (k + 1) - 3) * qpow quarter ((k + 1) * (k + 1))))
  -- factor Q = qpow quarter ((k+1)²)
  have hfac : (Q'.ofNat 3 * qpow quarter ((k + 1) * (k + 1))
      + -(Q'.ofNat (8 * (k + 1) * (k + 1)) * qpow quarter ((k + 1) * (k + 1)))).eqv
      ((Q'.ofNat 3 + -(Q'.ofNat (8 * (k + 1) * (k + 1))))
        * qpow quarter ((k + 1) * (k + 1))) := by ring_qeqv
  refine Q'.eqv_trans _ _ _ hfac ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (qpow quarter ((k + 1) * (k + 1))) hcoef) ?_
  -- -(ofNat W')·Q ≃ -(ofNat W' · Q)
  exact Q'.neg_mul_eqv _ _

/-! ## The central-domination majorant `μ_p ≤ (1/4)^{|m-p|²}·μ_m`. -/

theorem majorant {w : Q'} (hw0 : (0 : Q') < w) (hwh : w ≤ wH) (m : Nat) (p : Nat)
    (hp : p ≤ 2 * m) :
    coeffW w p * coeffW w (2 * m - p)
      ≤ qpow quarter (edp m p * edp m p) * (coeffW w m * coeffW w m) := by
  rcases Nat.le_total p m with hpm | hmp
  · -- p ≤ m
    have hrect := coeffW_rect_graded hw0 hwh (m - p) (m - p) p
    have e1 : p + (m - p) = m := by omega
    have e2 : p + (m - p) + (m - p) = 2 * m - p := by omega
    have e3 : edp m p = m - p := by unfold edp; omega
    rw [e2, e1] at hrect
    rw [e3]
    exact hrect
  · -- m ≤ p
    have hrect := coeffW_rect_graded hw0 hwh (p - m) (p - m) (m - (p - m))
    have e1 : (m - (p - m)) + (p - m) = m := by omega
    have e2 : (m - (p - m)) + (p - m) + (p - m) = p := by omega
    have e3 : m - (p - m) = 2 * m - p := by omega
    have e4 : edp m p = p - m := by unfold edp; omega
    rw [e2, e1] at hrect
    rw [e4, ← e3]
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)) hrect

/-! ## Per-term lower bound `Gc(edp p)·μ_m ≤ e_p`. -/

theorem termLb {w : Q'} (hw0 : (0 : Q') < w) (hwh : w ≤ wH) (m : Nat) (p : Nat)
    (hp : p ≤ 2 * m) :
    Gc (edp m p) * (coeffW w m * coeffW w m)
      ≤ Q'.ofNat 3 * (coeffW w p * coeffW w (2 * m - p))
        + -(Q'.ofNat 2 * (Q'.ofNat (dsq p (2 * m)) * (coeffW w p * coeffW w (2 * m - p)))) := by
  have hmaj := majorant hw0 hwh m p hp
  -- a := mu p, b := Bq·mum, κ := ofNat(8·edp²)
  -- Nat: 2·dsq = 8·edp·edp
  have hnat2 : 2 * dsq p (2 * m) = 8 * edp m p * edp m p := by
    rw [dsq_eq m p, Nat.mul_assoc 8 (edp m p) (edp m p)]; omega
  -- convert e-term coefficient:  2·(ofNat dsq · a) ≃ ofNat(8edp²) · a
  have hκ : (Q'.ofNat 2 * (Q'.ofNat (dsq p (2 * m)) * (coeffW w p * coeffW w (2 * m - p)))).eqv
      (Q'.ofNat (8 * edp m p * edp m p) * (coeffW w p * coeffW w (2 * m - p))) := by
    have e1 : (Q'.ofNat 2 * (Q'.ofNat (dsq p (2 * m)) * (coeffW w p * coeffW w (2 * m - p)))).eqv
        ((Q'.ofNat 2 * Q'.ofNat (dsq p (2 * m))) * (coeffW w p * coeffW w (2 * m - p))) :=
      Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
    refine Q'.eqv_trans _ _ _ e1 (Q'.mul_eqv_congr_right _ _ _ ?_)
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (ofNat_mul_eqv 2 (dsq p (2 * m)))) ?_
    exact Q'.eqv_of_eq (congrArg Q'.ofNat hnat2)
  -- rewrite e-term into κ-form
  have heE : (Q'.ofNat 3 * (coeffW w p * coeffW w (2 * m - p))
        + -(Q'.ofNat 2 * (Q'.ofNat (dsq p (2 * m)) * (coeffW w p * coeffW w (2 * m - p))))).eqv
      (Q'.ofNat 3 * (coeffW w p * coeffW w (2 * m - p))
        + -(Q'.ofNat (8 * edp m p * edp m p) * (coeffW w p * coeffW w (2 * m - p)))) :=
    Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ hκ)
  -- rewrite eps = Gc·mum into κ-form
  have heps : (Gc (edp m p) * (coeffW w m * coeffW w m)).eqv
      (Q'.ofNat 3 * (qpow quarter (edp m p * edp m p) * (coeffW w m * coeffW w m))
        + -(Q'.ofNat (8 * edp m p * edp m p)
          * (qpow quarter (edp m p * edp m p) * (coeffW w m * coeffW w m)))) := by
    show ((Q'.ofNat 3 * qpow quarter (edp m p * edp m p)
        + -(Q'.ofNat (8 * edp m p * edp m p) * qpow quarter (edp m p * edp m p)))
        * (coeffW w m * coeffW w m)).eqv _
    ring_qeqv
  -- core inequality  3b + -(κb) ≤ 3a + -(κa)
  have hcore : Q'.ofNat 3 * (qpow quarter (edp m p * edp m p) * (coeffW w m * coeffW w m))
      + -(Q'.ofNat (8 * edp m p * edp m p)
        * (qpow quarter (edp m p * edp m p) * (coeffW w m * coeffW w m)))
      ≤ Q'.ofNat 3 * (coeffW w p * coeffW w (2 * m - p))
        + -(Q'.ofNat (8 * edp m p * edp m p) * (coeffW w p * coeffW w (2 * m - p))) := by
    -- flip_sub of coreMono: need a ≤ b and 3 ≤ κ (edp ≠ 0) OR a ≃ b (edp = 0)
    rcases Nat.eq_zero_or_pos (edp m p) with h0 | hpos
    · -- edp = 0 : a ≃ b, κ = 0
      have hab' : (coeffW w p * coeffW w (2 * m - p)).eqv
          (qpow quarter (edp m p * edp m p) * (coeffW w m * coeffW w m)) := by
        rw [h0]
        -- qpow quarter 0 = 1 ; and p = m so mu p = mum
        have hpm : p = m := by unfold edp at h0; omega
        rw [hpm]
        have e2m : 2 * m - m = m := by omega
        rw [e2m]
        exact Q'.eqv_symm (Q'.one_mul_eqv _)
      refine Q'.le_of_eqv ?_
      exact Q'.add_eqv_congr' (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hab'))
        (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hab')))
    · -- edp ≥ 1 : coreMono + flip_sub
      have h3κ : Q'.ofNat 3 ≤ Q'.ofNat (8 * edp m p * edp m p) := by
        refine CReal.ofNat_le_ofNat ?_
        have : 1 ≤ edp m p * edp m p :=
          Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
        have hassoc : 8 * edp m p * edp m p = 8 * (edp m p * edp m p) := by rw [Nat.mul_assoc]
        omega
      have hcm := coreMono hmaj h3κ
      exact flip_sub hcm
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heps) (Q'.le_trans' _ _ _ hcore (Q'.ge_of_eqv heE))

/-! ## The master bound for `0 < w`. -/

theorem centreBound_pos {w : Q'} (hw0 : (0 : Q') < w) (hwh : w ≤ wH) (m : Nat) :
    Q'.ofNat 2 * dmomNfull w (2 * m) ≤ Q'.ofNat 3 * acNfull w (2 * m) := by
  have hw0' : (0 : Q') ≤ w := Q'.le_of_lt hw0
  -- abbreviations for the two summand sequences
  -- eSeq p = 3·μ_p − 2·(dsq_p·μ_p) ;  epsSeq p = Gc(edp p)·μ_m
  have hmum_nn : (0 : Q') ≤ coeffW w m * coeffW w m :=
    Q'.mul_nonneg _ _ (coeffW_nonneg hw0' m) (coeffW_nonneg hw0' m)
  -- (1)  Σ eSeq ≃ 3·acNfull + −(2·dmomNfull)
  have hEsum : (fsum (fun p => Q'.ofNat 3 * (coeffW w p * coeffW w (2 * m - p))
        + -(Q'.ofNat 2 * (Q'.ofNat (dsq p (2 * m)) * (coeffW w p * coeffW w (2 * m - p)))))
        (2 * m + 1)).eqv
      (Q'.ofNat 3 * acNfull w (2 * m) + -(Q'.ofNat 2 * dmomNfull w (2 * m))) := by
    refine Q'.eqv_trans _ _ _ (fsum_add _ _ (2 * m + 1)) ?_
    refine Q'.add_eqv_congr' ?_ ?_
    · exact Q'.eqv_symm (fsum_const_mul (Q'.ofNat 3)
        (fun p => coeffW w p * coeffW w (2 * m - p)) (2 * m + 1))
    · refine Q'.eqv_trans _ _ _ (fsum_neg _ (2 * m + 1)) ?_
      refine Q'.neg_eqv_congr _ _ ?_
      exact Q'.eqv_symm (fsum_const_mul (Q'.ofNat 2)
        (fun p => Q'.ofNat (dsq p (2 * m)) * (coeffW w p * coeffW w (2 * m - p))) (2 * m + 1))
  -- (2)  Σ epsSeq ≥ 0
  have hEpsNonneg : (0 : Q') ≤ fsum (fun p => Gc (edp m p) * (coeffW w m * coeffW w m)) (2 * m + 1) := by
    -- Σ (Gc(edp p)·μ_m) ≃ (Σ Gc(edp p))·μ_m ≃ (Gc 0 + 2·Σ Gc(k+1))·μ_m
    have hfac : (fsum (fun p => Gc (edp m p) * (coeffW w m * coeffW w m)) (2 * m + 1)).eqv
        ((fsum (fun p => Gc (edp m p)) (2 * m + 1)) * (coeffW w m * coeffW w m)) :=
      Q'.eqv_symm (fsum_mul_const (fun p => Gc (edp m p)) (coeffW w m * coeffW w m) (2 * m + 1))
    have hrefl : (fsum (fun p => Gc (edp m p)) (2 * m + 1)).eqv
        (Q'.ofNat 3 + -(Q'.ofNat 2 * fsum bpos m)) := by
      refine Q'.eqv_trans _ _ _ (reflect_sum Gc m) ?_
      -- Gc 0 + 2·Σ Gc(k+1) ≃ 3 + 2·(−Σ bpos) = 3 + −(2·Σ bpos)
      have hsucc : (fsum (fun k => Gc (k + 1)) m).eqv (-(fsum bpos m)) := by
        refine Q'.eqv_trans _ _ _ (fsum_eqv_congr _ _ (fun k => Gc_succ k) m) ?_
        exact fsum_neg bpos m
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' Gc_zero
        (Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _ hsucc)) ?_
      exact Q'.add_eqv_congr_left _ _ _ (Q'.mul_neg_eqv (Q'.ofNat 2) (fsum bpos m))
    -- 0 ≤ 3 + −(2·Σ bpos)
    have hpos3 : (0 : Q') ≤ Q'.ofNat 3 + -(Q'.ofNat 2 * fsum bpos m) := by
      have h2t : Q'.ofNat 2 * fsum bpos m ≤ Q'.ofNat 3 := by
        refine Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_left _ _ _ (tailBound m) (by decide)) ?_
        exact Q'.le_of_eqv (by decide : (Q'.ofNat 2 * threeHalf).eqv (Q'.ofNat 3))
      have hadd := Q'.add_le_add_right (Q'.ofNat 2 * fsum bpos m) (Q'.ofNat 3)
        (-(Q'.ofNat 2 * fsum bpos m)) h2t
      exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.add_neg_self_eqv (Q'.ofNat 2 * fsum bpos m))) hadd
    refine Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv hfac)
    refine Q'.le_trans' _ _ _ ?_
      (Q'.ge_of_eqv (Q'.mul_eqv_congr_right _ _ _ hrefl))
    exact Q'.mul_nonneg _ _ hpos3 hmum_nn
  -- (3)  Σ epsSeq ≤ Σ eSeq (termwise)
  have hmono : fsum (fun p => Gc (edp m p) * (coeffW w m * coeffW w m)) (2 * m + 1)
      ≤ fsum (fun p => Q'.ofNat 3 * (coeffW w p * coeffW w (2 * m - p))
        + -(Q'.ofNat 2 * (Q'.ofNat (dsq p (2 * m)) * (coeffW w p * coeffW w (2 * m - p)))))
        (2 * m + 1) :=
    fsum_mono_lt (2 * m + 1) (fun p hp => termLb hw0 hwh m p (by omega))
  -- combine: 0 ≤ Σ eps ≤ Σ e ≃ 3ac − 2dmom
  have hchain : (0 : Q') ≤ Q'.ofNat 3 * acNfull w (2 * m) + -(Q'.ofNat 2 * dmomNfull w (2 * m)) :=
    Q'.le_trans' _ _ _ hEpsNonneg (Q'.le_trans' _ _ _ hmono (Q'.le_of_eqv hEsum))
  -- 2dmom ≤ 3ac
  have hadd := Q'.add_le_add_right 0
    (Q'.ofNat 3 * acNfull w (2 * m) + -(Q'.ofNat 2 * dmomNfull w (2 * m)))
    (Q'.ofNat 2 * dmomNfull w (2 * m)) hchain
  -- (3ac + −2dmom) + 2dmom ≃ 3ac ; 0 + 2dmom ≃ 2dmom
  refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.zero_add' _))) ?_
  refine Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv ?_)
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _ (Q'.neg_add_self_eqv (Q'.ofNat 2 * dmomNfull w (2 * m)))) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' _)

/-! ## The `w ≃ 0` degenerate case. -/

theorem qpow_zero_of_zero {w : Q'} (hw : w.eqv 0) (j : Nat) : (qpow w (j + 1)).eqv 0 := by
  show (qpow w j * w).eqv 0
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hw) ?_
  exact Q'.mul_zero_eqv _

theorem coeffW_zero {w : Q'} (hw : w.eqv 0) (k : Nat) (hk : 1 ≤ k) : (coeffW w k).eqv 0 := by
  show (dimQ k * qpow w (c4 k)).eqv 0
  have hc4 : 1 ≤ c4 k := by
    show 1 ≤ k * (k + 2)
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hq : (qpow w (c4 k)).eqv 0 := by
    have hce : c4 k = (c4 k - 1) + 1 := by omega
    rw [hce]; exact qpow_zero_of_zero hw (c4 k - 1)
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hq) ?_
  exact Q'.mul_zero_eqv _

theorem mu_zero {w : Q'} (hw : w.eqv 0) (m p : Nat) (hm : 1 ≤ m) :
    (coeffW w p * coeffW w (2 * m - p)).eqv 0 := by
  rcases Nat.eq_zero_or_pos p with hp0 | hp1
  · subst hp0
    have h2 : 1 ≤ 2 * m - 0 := by omega
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (coeffW_zero hw (2 * m - 0) h2)) ?_
    exact Q'.mul_zero_eqv _
  · refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (coeffW_zero hw p hp1)) ?_
    exact Q'.zero_mul_eqv _

theorem fsum_zero_fun : ∀ n, (fsum (fun _ => (0 : Q')) n).eqv 0
  | 0 => Q'.eqv_refl 0
  | n + 1 => by
      show (fsum (fun _ => (0 : Q')) n + 0).eqv 0
      exact Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.add_zero' _)) (fsum_zero_fun n)

theorem dmomNfull_zero {w : Q'} (hw : w.eqv 0) (m : Nat) (hm : 1 ≤ m) :
    (dmomNfull w (2 * m)).eqv 0 := by
  show (fsum (fun p => Q'.ofNat (dsq p (2 * m)) * (coeffW w p * coeffW w (2 * m - p)))
      (2 * m + 1)).eqv 0
  refine Q'.eqv_trans _ _ _
    (fsum_eqv_congr _ (fun _ => 0) (fun p => ?_) (2 * m + 1)) (fsum_zero_fun (2 * m + 1))
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (mu_zero hw m p hm)) ?_
  exact Q'.mul_zero_eqv _

theorem pos_or_zero {w : Q'} (hw : (0 : Q') ≤ w) : (0 : Q') < w ∨ w.eqv 0 := by
  by_cases hnum : w.num = 0
  · right
    have h1 : ((0 : Q').den : Int) = 1 := rfl
    have h2 : (0 : Q').num = 0 := rfl
    show w.num * ((0 : Q').den : Int) = (0 : Q').num * (w.den : Int)
    rw [h1, h2, hnum]; simp
  · left
    have hn : (0 : Int) ≤ w.num := (Q'.zero_le_iff_num_nonneg w).mp hw
    exact CReal.pos_of_num_pos (by omega)

/-! ## The combined central-variance bound (constant `3/2`). -/

theorem centreBound {w : Q'} (hw : (0 : Q') ≤ w) (hwh : w ≤ wH) (m : Nat) (hm : 1 ≤ m) :
    Q'.ofNat 2 * dmomNfull w (2 * m) ≤ Q'.ofNat 3 * acNfull w (2 * m) := by
  rcases pos_or_zero hw with hpos | hzero
  · exact centreBound_pos hpos hwh m
  · have hd0 : (dmomNfull w (2 * m)).eqv 0 := dmomNfull_zero hzero m hm
    have hac : (0 : Q') ≤ acNfull w (2 * m) := acN_nonneg hw (2 * m + 1) (2 * m)
    have hL : (Q'.ofNat 2 * dmomNfull w (2 * m)).eqv 0 :=
      Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hd0) (Q'.mul_zero_eqv _)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hL) (Q'.mul_nonneg _ _ (by decide) hac)

end YMGap.Continuum.R1EvenCentreBound

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.R1EvenCentreBound.reflect_sum
#print axioms YMGap.Continuum.R1EvenCentreBound.tailBound
#print axioms YMGap.Continuum.R1EvenCentreBound.majorant
#print axioms YMGap.Continuum.R1EvenCentreBound.termLb
#print axioms YMGap.Continuum.R1EvenCentreBound.centreBound_pos
#print axioms YMGap.Continuum.R1EvenCentreBound.centreBound
