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

end YMGap.Continuum.HarmonicDriftAntisymmetry

#print axioms YMGap.Continuum.HarmonicDriftAntisymmetry.harmonicWeightCross_eq_kernelSum
#print axioms YMGap.Continuum.HarmonicDriftAntisymmetry.harmonicWeightCross_eq_core_add_boundary
#print axioms YMGap.Continuum.HarmonicDriftAntisymmetry.driftCore_twice_eq_pairSum
#print axioms YMGap.Continuum.HarmonicDriftAntisymmetry.driftPairKernel_eq_factored
#print axioms YMGap.Continuum.HarmonicDriftAntisymmetry.coefficient_two_pairwise_fails_k3_i0
