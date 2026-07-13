/-
The exact finite double-sum form of the fixed-cutoff harmonic weight drift.

The determinant is opened without separately bounding either normalizer.  Its
rectangular kernel is then split into a square core and one boundary column;
the square core admits the canonical `(i,j)+(j,i)` antisymmetrization.  A
closed diagonal counterexample records that the most direct coefficient-two
pairwise allocation is false, so the eventual estimate must redistribute
budget across distinct index pairs rather than prove each symmetrized pair in
isolation.
-/

import YMGap.Continuum.HarmonicWeightDriftFence

namespace YMGap.Continuum.HarmonicDriftAntisymmetry

set_option maxHeartbeats 800000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one];
             ac_rfl))

def oldDiag (k s : Nat) : Q' :=
  coeffW (harmW k) s * coeffW (harmW k) s

def oldAdj (k s : Nat) : Q' :=
  coeffW (harmW k) s * coeffW (harmW k) (s + 1)

/-- Rectangular covariance kernel: adjacent index `i<Ncut k`, diagonal index
`j≤Ncut k`. -/
def driftKernel (k i j : Nat) : Q' :=
  oldAdj k i * oldDiag k j *
    (driftAdjFactor k i - driftSqFactor k j)

private theorem rect_sub_eq (F G : Nat → Nat → Q') (m n : Nat) :
    fsum (fun i => fsum (F i) n) m +
        -(fsum (fun i => fsum (G i) n) m) ≈
      fsum (fun i => fsum (fun j => F i j + -(G i j)) n) m := by
  have hneg : -(fsum (fun i => fsum (G i) n) m) ≈
      fsum (fun i => fsum (fun j => -(G i j)) n) m := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (CubeRatioBounds.fsum_neg (fun i => fsum (G i) n) m)) ?_
    exact CubeRatioBounds.fsum_eqv_congr _ _ (fun i =>
      Q'.eqv_symm (CubeRatioBounds.fsum_neg (G i) n)) m
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (fsum (fun i => fsum (F i) n) m) _ _ hneg) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (CubeRatioBounds.fsum_add
      (fun i => fsum (F i) n)
      (fun i => fsum (fun j => -(G i j)) n) m)) ?_
  exact CubeRatioBounds.fsum_eqv_congr _ _ (fun i =>
    Q'.eqv_symm (CubeRatioBounds.fsum_add (F i) (fun j => -(G i j)) n)) m

private theorem product_diff_factor (a d F G : Q') :
    (a * F) * d + -(a * (d * G)) ≈ (a * d) * (F + -G) := by
  have hL0 : (a * F) * d ≈ (a * d) * F := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv a F d) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left a _ _ (Q'.mul_comm_eqv F d)) ?_
    exact Q'.eqv_symm (Q'.mul_assoc_eqv a d F)
  have hL1 : -(a * (d * G)) ≈ -((a * d) * G) :=
    Q'.neg_eqv_congr _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv a d G))
  have hR : (a * d) * (F + -G) ≈
      (a * d) * F + -((a * d) * G) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (a * d) F (-G)) ?_
    exact Q'.add_eqv_congr_left _ _ _ (Q'.mul_neg_eqv (a * d) G)
  exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hL0 hL1) (Q'.eqv_symm hR)

/-- **Exact rectangular covariance sum.** -/
theorem harmonicWeightCross_eq_kernelSum (k : Nat) :
    harmonicWeightCross k ≈
      fsum (fun i => fsum (fun j => driftKernel k i j) (Ncut k + 1))
        (Ncut k) := by
  let FA := fun i => oldAdj k i * driftAdjFactor k i
  let D := fun j => oldDiag k j
  let A := fun i => oldAdj k i
  let FD := fun j => oldDiag k j * driftSqFactor k j
  have hAD := FusionCoreStepRoundB.fsum_mul_fsum FA D (Ncut k) (Ncut k + 1)
  have hDA := FusionCoreStepRoundB.fsum_mul_fsum A FD (Ncut k) (Ncut k + 1)
  have hAD' : harmonicDriftA k * harmonicD k ≈
      fsum (fun i => fsum (fun j => FA i * D j) (Ncut k + 1)) (Ncut k) := by
    simpa [FA, D, harmonicDriftA, harmonicD, oldAdj, oldDiag] using hAD
  have hDA' : harmonicA k * harmonicDriftD k ≈
      fsum (fun i => fsum (fun j => A i * FD j) (Ncut k + 1)) (Ncut k) := by
    simpa [A, FD, harmonicA, harmonicDriftD, oldAdj, oldDiag] using hDA
  have hprod : harmonicDriftA k * harmonicD k - harmonicA k * harmonicDriftD k ≈
      fsum (fun i => fsum (fun j => (FA i * D j) + -(A i * FD j))
        (Ncut k + 1)) (Ncut k) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hAD' (Q'.neg_eqv_congr _ _ hDA')) ?_
    exact rect_sub_eq _ _ (Ncut k) (Ncut k + 1)
  refine Q'.eqv_trans _ _ _ (harmonicWeightCross_eq_driftCovariance k) ?_
  refine Q'.eqv_trans _ _ _ hprod ?_
  exact CubeRatioBounds.fsum_eqv_congr _ _ (fun i =>
    CubeRatioBounds.fsum_eqv_congr _ _ (fun j => by
      unfold FA D A FD driftKernel
      exact product_diff_factor (oldAdj k i) (oldDiag k j)
        (driftAdjFactor k i) (driftSqFactor k j)) (Ncut k + 1)) (Ncut k)

/-! ## Square-core antisymmetrization and the terminal column -/

def driftCore (k : Nat) : Q' :=
  fsum (fun i => fsum (fun j => driftKernel k i j) (Ncut k)) (Ncut k)

def driftBoundary (k : Nat) : Q' :=
  fsum (fun i => driftKernel k i (Ncut k)) (Ncut k)

theorem harmonicWeightCross_eq_core_add_boundary (k : Nat) :
    harmonicWeightCross k ≈ driftCore k + driftBoundary k := by
  refine Q'.eqv_trans _ _ _ (harmonicWeightCross_eq_kernelSum k) ?_
  have hsplit :
      fsum (fun i => fsum (fun j => driftKernel k i j) (Ncut k + 1)) (Ncut k) ≈
        fsum (fun i =>
          fsum (fun j => driftKernel k i j) (Ncut k) +
            driftKernel k i (Ncut k)) (Ncut k) := by
    exact CubeRatioBounds.fsum_eqv_congr _ _ (fun _ => Q'.eqv_refl _) (Ncut k)
  refine Q'.eqv_trans _ _ _ hsplit ?_
  exact Q'.eqv_trans _ _ _
    (CubeRatioBounds.fsum_add
      (fun i => fsum (fun j => driftKernel k i j) (Ncut k))
      (fun i => driftKernel k i (Ncut k)) (Ncut k))
    (Q'.eqv_refl _)

def driftPairKernel (k i j : Nat) : Q' :=
  driftKernel k i j + driftKernel k j i

private theorem rect_add_eq (F G : Nat → Nat → Q') (n : Nat) :
    fsum (fun i => fsum (F i) n) n + fsum (fun i => fsum (G i) n) n ≈
      fsum (fun i => fsum (fun j => F i j + G i j) n) n := by
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (CubeRatioBounds.fsum_add
      (fun i => fsum (F i) n) (fun i => fsum (G i) n) n)) ?_
  exact CubeRatioBounds.fsum_eqv_congr _ _ (fun i =>
    Q'.eqv_symm (CubeRatioBounds.fsum_add (F i) (G i) n)) n

/-- Twice the square core is exactly the sum of the symmetrized pair kernel. -/
theorem driftCore_twice_eq_pairSum (k : Nat) :
    driftCore k + driftCore k ≈
      fsum (fun i => fsum (fun j => driftPairKernel k i j) (Ncut k))
        (Ncut k) := by
  have hswap := CubeRatioBounds.fsum_swap
    (fun i j => driftKernel k i j) (Ncut k) (Ncut k)
  unfold driftCore
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _ hswap) ?_
  exact rect_add_eq
    (fun i j => driftKernel k i j)
    (fun i j => driftKernel k j i) (Ncut k)

/-- The common-factor form of a symmetrized pair.  This is the exact kernel
where any quantitative cancellation estimate must act. -/
def driftPairFactored (k i j : Nat) : Q' :=
  (coeffW (harmW k) i * coeffW (harmW k) j) *
    ((coeffW (harmW k) (i + 1) * coeffW (harmW k) j) *
        (driftAdjFactor k i - driftSqFactor k j) +
      (coeffW (harmW k) (j + 1) * coeffW (harmW k) i) *
        (driftAdjFactor k j - driftSqFactor k i))

theorem driftPairKernel_eq_factored (k i j : Nat) :
    driftPairKernel k i j ≈ driftPairFactored k i j := by
  let ci := coeffW (harmW k) i
  let cj := coeffW (harmW k) j
  let cip := coeffW (harmW k) (i + 1)
  let cjp := coeffW (harmW k) (j + 1)
  let Xi := driftAdjFactor k i - driftSqFactor k j
  let Xj := driftAdjFactor k j - driftSqFactor k i
  have hi : (ci * cip) * (cj * cj) * Xi ≈
      (ci * cj) * ((cip * cj) * Xi) := by
    ring_qeqv
  have hj : (cj * cjp) * (ci * ci) * Xj ≈
      (ci * cj) * ((cjp * ci) * Xj) := by
    ring_qeqv
  unfold driftPairKernel driftKernel driftPairFactored oldAdj oldDiag
  change ((ci * cip) * (cj * cj) * Xi) + ((cj * cjp) * (ci * ci) * Xj) ≈
    (ci * cj) * ((cip * cj) * Xi + (cjp * ci) * Xj)
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hi hj) ?_
  exact Q'.eqv_symm
    (Q'.mul_add_eqv (ci * cj) ((cip * cj) * Xi) ((cjp * ci) * Xj))

/-! ## A machine-checked fence against pointwise coefficient-two allocation -/

def twoInvSq (k : Nat) : Q' :=
  Q'.ofNat 2 * invSqTerm 2 (by decide) k

/-- The canonical product-of-normalizers budget kernel.  Its double sum is
`(2/(k+2)^2) D_old D_mid`. -/
def driftBudgetKernel (k i j : Nat) : Q' :=
  twoInvSq k * (oldDiag k i * (oldDiag k j * driftSqFactor k j))

/-- **Pointwise antisymmetrization is too strong.**  Even the diagonal pair
`i=j=0` at `k=3` exceeds its exact coefficient-two share.  Thus the true
determinant estimate must transfer negative off-diagonal mass into the
positive diagonal sector; the pair factorization alone does not close it. -/
theorem coefficient_two_pairwise_fails_k3_i0 :
    not (driftPairKernel 3 0 0 ≤
      driftBudgetKernel 3 0 0 + driftBudgetKernel 3 0 0) := by
  unfold driftPairKernel driftKernel driftBudgetKernel twoInvSq oldAdj oldDiag
    driftAdjFactor driftSqFactor driftRatio harmW harmU
    ReciprocalBernoulliUpper.oneSub unit invSqTerm coeffW dimQ c4
    Q'.divPos Q'.recipPos qpow
  decide

/-! ## Terminal-column control -/

theorem harmW_mono_step (k : Nat) : harmW k ≤ harmW (k + 1) := by
  have hu : harmU (k + 1) ≤ harmU k := by
    unfold harmU
    exact unit_antitone (by omega) (by omega) (by omega)
  unfold harmW ReciprocalBernoulliUpper.oneSub
  exact Q'.add_le_add_left (1 : Q') _ _ (Q'.neg_le_neg hu)

theorem one_le_driftRatio (k : Nat) : (1 : Q') ≤ driftRatio k := by
  have hmul : harmW k * (1 : Q') ≤ harmW k * driftRatio k := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_one_eqv (harmW k)))
      (Q'.le_trans' _ _ _ (harmW_mono_step k)
        (Q'.le_of_eqv (harmW_step_eqv k)))
  exact Q'.le_of_mul_le_mul_left hmul (harmW_pos k)

private theorem one_le_qpow_local {q : Q'} (hq : (1 : Q') ≤ q) :
    ∀ n, (1 : Q') ≤ qpow q n
  | 0 => Q'.le_refl' 1
  | n + 1 => by
      have hq0 : (0 : Q') ≤ q := Q'.le_trans' _ _ _ (by decide) hq
      have hi0 : (0 : Q') ≤ qpow q n := qpow_nonneg q hq0 n
      have hs : qpow q n * (1 : Q') ≤ qpow q n * q :=
        Q'.mul_le_mul_of_nonneg_left _ _ _ hq hi0
      exact Q'.le_trans' _ _ _ (one_le_qpow_local hq n)
        (Q'.le_trans' _ _ _
          (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_one_eqv _))) hs)

private theorem qpow_exp_mono_one_le {q : Q'} (hq : (1 : Q') ≤ q)
    {a b : Nat} (hab : a ≤ b) : qpow q a ≤ qpow q b := by
  obtain ⟨d, rfl⟩ := Nat.le.dest hab
  have hq0 : (0 : Q') ≤ q := Q'.le_trans' _ _ _ (by decide) hq
  have hp0 : (0 : Q') ≤ qpow q a := qpow_nonneg q hq0 a
  have hone : (1 : Q') ≤ qpow q d := one_le_qpow_local hq d
  have hs : qpow q a * (1 : Q') ≤ qpow q a * qpow q d :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hone hp0
  exact Q'.le_trans' _ _ _
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_one_eqv _))) hs)
    (Q'.le_of_eqv (Q'.eqv_symm (qpow_add q a d)))

private theorem c4_mono_local {i j : Nat} (h : i ≤ j) : c4 i ≤ c4 j := by
  unfold c4
  exact Nat.mul_le_mul h (by omega)

private theorem driftAdjFactor_eq_pow (k i : Nat) :
    driftAdjFactor k i ≈
      qpow (driftRatio k) (c4 i + c4 (i + 1)) := by
  unfold driftAdjFactor
  exact Q'.eqv_symm (qpow_add (driftRatio k) (c4 i) (c4 (i + 1)))

private theorem driftSqFactor_eq_pow (k i : Nat) :
    driftSqFactor k i ≈ qpow (driftRatio k) (c4 i + c4 i) := by
  unfold driftSqFactor
  exact Q'.eqv_symm (qpow_add (driftRatio k) (c4 i) (c4 i))

theorem driftAdjFactor_le_terminalSq {k i : Nat} (hi : i < Ncut k) :
    driftAdjFactor k i ≤ driftSqFactor k (Ncut k) := by
  have hiN : i ≤ Ncut k := Nat.le_of_lt hi
  have hi1N : i + 1 ≤ Ncut k := hi
  have he : c4 i + c4 (i + 1) ≤ c4 (Ncut k) + c4 (Ncut k) :=
    Nat.add_le_add (c4_mono_local hiN) (c4_mono_local hi1N)
  have hp := qpow_exp_mono_one_le (one_le_driftRatio k) he
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (driftAdjFactor_eq_pow k i))
    (Q'.le_trans' _ _ _ hp (Q'.ge_of_eqv (driftSqFactor_eq_pow k (Ncut k))))

theorem driftKernel_terminal_nonpos {k i : Nat} (hi : i < Ncut k) :
    driftKernel k i (Ncut k) ≤ (0 : Q') := by
  have hdiff : driftAdjFactor k i - driftSqFactor k (Ncut k) ≤ (0 : Q') :=
    FusionCoreStepRoundE.q_add_neg_nonpos (driftAdjFactor_le_terminalSq hi)
  have hcoef : (0 : Q') ≤ oldAdj k i * oldDiag k (Ncut k) := by
    exact Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _
        (coeffW_nonneg (harmW_nonneg k) i)
        (coeffW_nonneg (harmW_nonneg k) (i + 1)))
      (Q'.mul_nonneg _ _
        (coeffW_nonneg (harmW_nonneg k) (Ncut k))
        (coeffW_nonneg (harmW_nonneg k) (Ncut k)))
  unfold driftKernel
  exact Q'.mul_nonpos_of_nonneg_nonpos hcoef hdiff

private theorem fsum_nonpos_upto (f : Nat → Q') : ∀ n,
    (∀ i, i < n → f i ≤ (0 : Q')) → fsum f n ≤ (0 : Q')
  | 0, _ => Q'.le_refl' 0
  | n + 1, hf => by
      have hprev := fsum_nonpos_upto f n (fun i hi => hf i (by omega))
      have h := Q'.add_le_add hprev (hf n (by omega))
      exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (QPoly.q_zero_add_eqv 0))

theorem driftBoundary_nonpos (k : Nat) : driftBoundary k ≤ (0 : Q') := by
  unfold driftBoundary
  exact fsum_nonpos_upto _ (Ncut k)
    (fun i hi => driftKernel_terminal_nonpos hi)

/-- The entire terminal column is favorable and may be discarded in an upper
bound.  This is exact cutoff control, with no `+2/+4` leakage payment. -/
theorem harmonicWeightCross_le_core (k : Nat) :
    harmonicWeightCross k ≤ driftCore k := by
  have hsum : driftCore k + driftBoundary k ≤ driftCore k + (0 : Q') :=
    Q'.add_le_add_left (driftCore k) _ _ (driftBoundary_nonpos k)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (harmonicWeightCross_eq_core_add_boundary k))
    (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv (QPoly.q_add_zero_eqv _)))

/-! ## The local geometric-midpoint identity and a reserve fence -/

/-- Consecutive diagonal drift factors have the adjacent factor as their
exact geometric midpoint. -/
theorem driftAdjFactor_sq_eq_neighbors (k i : Nat) :
    driftAdjFactor k i * driftAdjFactor k i ≈
      driftSqFactor k i * driftSqFactor k (i + 1) := by
  unfold driftAdjFactor driftSqFactor
  ring_qeqv

def driftPairBudget (k i j : Nat) : Q' :=
  driftBudgetKernel k i j + driftBudgetKernel k j i

def driftPairResidual (k i j : Nat) : Q' :=
  driftPairKernel k i j - driftPairBudget k i j

/-- A nearest-neighbor reserve transfer is not uniform.  At `k=8`, the
positive diagonal excess at mode one and both ordered `(1,2)` cells still
have positive total residual.  Any telescoping flux must reach beyond the
adjacent band. -/
theorem nearest_neighbor_reserve_fails_k8_i1 :
    not (driftPairResidual 8 1 1 +
        driftPairResidual 8 1 2 + driftPairResidual 8 2 1 ≤ (0 : Q')) := by
  unfold driftPairResidual driftPairBudget driftPairKernel driftKernel
    driftBudgetKernel twoInvSq oldAdj oldDiag driftAdjFactor driftSqFactor
    driftRatio harmW harmU ReciprocalBernoulliUpper.oneSub unit invSqTerm
    coeffW dimQ c4 Q'.divPos Q'.recipPos qpow
  decide

/-! ## Global reserve-transfer identity -/

def driftPairBudgetSum (k : Nat) : Q' :=
  fsum (fun i => fsum (fun j => driftPairBudget k i j) (Ncut k)) (Ncut k)

def driftPairResidualSum (k : Nat) : Q' :=
  fsum (fun i => fsum (fun j => driftPairResidual k i j) (Ncut k)) (Ncut k)

def driftBudgetSum (k : Nat) : Q' :=
  fsum (fun i => fsum (fun j => driftBudgetKernel k i j) (Ncut k)) (Ncut k)

/-- Symmetrizing the oriented product budget exactly doubles its total. -/
theorem driftPairBudgetSum_eq_twice (k : Nat) :
    driftPairBudgetSum k ≈ driftBudgetSum k + driftBudgetSum k := by
  have hswap := CubeRatioBounds.fsum_swap
    (fun i j => driftBudgetKernel k i j) (Ncut k) (Ncut k)
  unfold driftPairBudgetSum driftPairBudget driftBudgetSum
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm
    (rect_add_eq
      (fun i j => driftBudgetKernel k i j)
      (fun i j => driftBudgetKernel k j i) (Ncut k))) ?_
  exact Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm hswap)

/-- **Exact global reserve transfer.**  The unpaid coefficient-two core is
the total symmetrized residual: every positive diagonal excess and every
negative distinct-pair reserve occur in this one equality.  Together with
`harmonicWeightCross_le_core`, proving this residual nonpositive is sufficient
without paying the favorable terminal column. -/
theorem core_twice_sub_pairBudget_eq_residual (k : Nat) :
    (driftCore k + driftCore k) - driftPairBudgetSum k ≈
      driftPairResidualSum k := by
  have hpairs := driftCore_twice_eq_pairSum k
  have hrect := rect_sub_eq
    (fun i j => driftPairKernel k i j)
    (fun i j => driftPairBudget k i j) (Ncut k) (Ncut k)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ (-(driftPairBudgetSum k)) hpairs) ?_
  unfold driftPairBudgetSum driftPairResidualSum driftPairResidual
  exact hrect

def oldDiagPrefix (k : Nat) : Q' := fsum (fun i => oldDiag k i) (Ncut k)

def driftDiagPrefix (k : Nat) : Q' :=
  fsum (fun j => oldDiag k j * driftSqFactor k j) (Ncut k)

/-- The oriented coefficient-two budget is exactly the product of the two
diagonal prefixes. -/
theorem driftBudgetSum_eq_prefixProduct (k : Nat) :
    driftBudgetSum k ≈
      twoInvSq k * (oldDiagPrefix k * driftDiagPrefix k) := by
  let H := fun i j => oldDiag k i * (oldDiag k j * driftSqFactor k j)
  have hprod := FusionCoreStepRoundB.fsum_mul_fsum
    (fun i => oldDiag k i)
    (fun j => oldDiag k j * driftSqFactor k j) (Ncut k) (Ncut k)
  have hscaled : twoInvSq k * (oldDiagPrefix k * driftDiagPrefix k) ≈
      twoInvSq k * fsum (fun i => fsum (H i) (Ncut k)) (Ncut k) := by
    exact Q'.mul_eqv_congr_left (twoInvSq k) _ _ (by
      unfold oldDiagPrefix driftDiagPrefix H
      exact hprod)
  have hpull : twoInvSq k * fsum (fun i => fsum (H i) (Ncut k)) (Ncut k) ≈
      fsum (fun i => fsum (fun j => twoInvSq k * H i j) (Ncut k))
        (Ncut k) := by
    refine Q'.eqv_trans _ _ _
      (CubeRatioBounds.fsum_const_mul (twoInvSq k)
        (fun i => fsum (H i) (Ncut k)) (Ncut k)) ?_
    exact CubeRatioBounds.fsum_eqv_congr _ _ (fun i =>
      CubeRatioBounds.fsum_const_mul (twoInvSq k) (H i) (Ncut k)) (Ncut k)
  refine Q'.eqv_symm (Q'.eqv_trans _ _ _ hscaled ?_)
  refine Q'.eqv_trans _ _ _ hpull ?_
  unfold driftBudgetSum driftBudgetKernel H
  exact Q'.eqv_refl _

theorem driftBudgetSum_le_fullProduct (k : Nat) :
    driftBudgetSum k ≤ twoInvSq k * (harmonicD k * harmonicMidD k) := by
  have hOld0 : (0 : Q') ≤ oldDiagPrefix k := by
    unfold oldDiagPrefix oldDiag
    exact fsum_nonneg (fun i => Q'.mul_nonneg _ _
      (coeffW_nonneg (harmW_nonneg k) i)
      (coeffW_nonneg (harmW_nonneg k) i)) (Ncut k)
  have hDrift0 : (0 : Q') ≤ driftDiagPrefix k := by
    unfold driftDiagPrefix oldDiag driftSqFactor
    exact fsum_nonneg (fun i => Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _
        (coeffW_nonneg (harmW_nonneg k) i)
        (coeffW_nonneg (harmW_nonneg k) i))
      (Q'.mul_nonneg _ _
        (qpow_nonneg _ (Q'.le_of_lt (driftRatio_pos k)) _)
        (qpow_nonneg _ (Q'.le_of_lt (driftRatio_pos k)) _))) (Ncut k)
  have hOld : oldDiagPrefix k ≤ harmonicD k := by
    unfold oldDiagPrefix harmonicD coordNormSq oldDiag
    exact AFRateCalibration.fsum_le_of_le
      (fun i => Q'.mul_nonneg _ _
        (coeffW_nonneg (harmW_nonneg k) i)
        (coeffW_nonneg (harmW_nonneg k) i)) (by omega)
  have hDrift : driftDiagPrefix k ≤ harmonicMidD k := by
    have hpre : driftDiagPrefix k ≤ harmonicDriftD k := by
      unfold driftDiagPrefix harmonicDriftD oldDiag driftSqFactor
      exact AFRateCalibration.fsum_le_of_le
        (fun i => Q'.mul_nonneg _ _
          (Q'.mul_nonneg _ _
            (coeffW_nonneg (harmW_nonneg k) i)
            (coeffW_nonneg (harmW_nonneg k) i))
          (Q'.mul_nonneg _ _
            (qpow_nonneg _ (Q'.le_of_lt (driftRatio_pos k)) _)
            (qpow_nonneg _ (Q'.le_of_lt (driftRatio_pos k)) _))) (by omega)
    exact Q'.le_trans' _ _ _ hpre
      (Q'.le_of_eqv (Q'.eqv_symm (harmonicMidD_eq_driftSum k)))
  have hprod : oldDiagPrefix k * driftDiagPrefix k ≤ harmonicD k * harmonicMidD k :=
    Q'.mul_le_mul_of_nonneg hOld hDrift
      (Q'.le_of_lt (harmonicD_pos k)) hDrift0
  have hscale := Q'.mul_le_mul_of_nonneg_left _ _ (twoInvSq k) hprod (by
    unfold twoInvSq
    exact Q'.mul_nonneg _ _ (by decide) (invSqTerm_nonneg 2 (by decide) k))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (driftBudgetSum_eq_prefixProduct k)) hscale

end YMGap.Continuum.HarmonicDriftAntisymmetry

#print axioms YMGap.Continuum.HarmonicDriftAntisymmetry.harmonicWeightCross_eq_kernelSum
#print axioms YMGap.Continuum.HarmonicDriftAntisymmetry.harmonicWeightCross_eq_core_add_boundary
#print axioms YMGap.Continuum.HarmonicDriftAntisymmetry.driftCore_twice_eq_pairSum
#print axioms YMGap.Continuum.HarmonicDriftAntisymmetry.driftPairKernel_eq_factored
#print axioms YMGap.Continuum.HarmonicDriftAntisymmetry.coefficient_two_pairwise_fails_k3_i0
#print axioms YMGap.Continuum.HarmonicDriftAntisymmetry.harmW_mono_step
#print axioms YMGap.Continuum.HarmonicDriftAntisymmetry.one_le_driftRatio
#print axioms YMGap.Continuum.HarmonicDriftAntisymmetry.driftAdjFactor_le_terminalSq
#print axioms YMGap.Continuum.HarmonicDriftAntisymmetry.driftKernel_terminal_nonpos
#print axioms YMGap.Continuum.HarmonicDriftAntisymmetry.driftBoundary_nonpos
#print axioms YMGap.Continuum.HarmonicDriftAntisymmetry.harmonicWeightCross_le_core
#print axioms YMGap.Continuum.HarmonicDriftAntisymmetry.driftAdjFactor_sq_eq_neighbors
#print axioms YMGap.Continuum.HarmonicDriftAntisymmetry.nearest_neighbor_reserve_fails_k8_i1
#print axioms YMGap.Continuum.HarmonicDriftAntisymmetry.driftPairBudgetSum_eq_twice
#print axioms YMGap.Continuum.HarmonicDriftAntisymmetry.core_twice_sub_pairBudget_eq_residual
#print axioms YMGap.Continuum.HarmonicDriftAntisymmetry.driftBudgetSum_eq_prefixProduct
#print axioms YMGap.Continuum.HarmonicDriftAntisymmetry.driftBudgetSum_le_fullProduct
