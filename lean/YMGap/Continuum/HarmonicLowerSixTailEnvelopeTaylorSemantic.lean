/-
# Structured Taylor semantics for the lower-six E8/E9 envelopes

The E8 and E9 cleared numerators share the same factorial-square scale.
This module names the small structured factors (Taylor prefix, step
coefficient, and common denominator) before the generated coefficient grids
are reconciled row by row.
-/

import YMGap.Continuum.HarmonicLowerSixTailSlopeFloorPhysicalBridge
import YMGap.Continuum.HarmonicLowerSixTailSecondFluxLocalBound
import YMGap.Continuum.RawGridSemanticTransport

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeTaylorSemantic

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.CoreBResidualSimplex
open YMGap.Continuum.HarmonicLowerSixTailSecondFluxLocalBound
open YMGap.Continuum.HarmonicLowerSixTailTaylorNineCertificate
open YMGap.Continuum.HarmonicLowerSixSecondFluxSign
open YMGap.Continuum.HarmonicLowerSixTailPaymentAssembly
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFlux
open YMGap.Continuum.TensorBernsteinHomogeneousCertificate

local infix:50 " ≈ " => Q'.eqv

abbrev PE := RingNormaliser.PolyExpr

def envelopeSemanticN : PE := .var 0
def envelopeSemanticD : PE := .var 1
def envelopeSemanticOne : PE := .const 1
def envelopeSemanticNsucc : PE :=
  .add envelopeSemanticN envelopeSemanticOne
def envelopeSemanticDsucc : PE :=
  .add envelopeSemanticD envelopeSemanticOne
def envelopeSemanticR : PE :=
  .add (.pow envelopeSemanticD 2) (.const (-1))

def envelopeSemanticJ (x : PE) : PE :=
  .add
    (.add
      (.add
        (.add
          (.add
            (.add
              (.add
                (.add
                  (.add
                    (.mul (.mul (.const 192) x)
                      (.pow envelopeSemanticD 4))
                    (.mul (.mul (.const 384) (.pow x 3))
                      (.pow envelopeSemanticD 3)))
                  (.neg (.mul (.mul (.const 6) x)
                    (.pow envelopeSemanticD 3))))
                (.neg (.mul (.mul (.const 384) (.pow x 5))
                  (.pow envelopeSemanticD 2))))
              (.mul (.mul (.const 576) (.pow x 4))
                (.pow envelopeSemanticD 2)))
            (.mul (.mul (.const 184) (.pow x 3))
              (.pow envelopeSemanticD 2)))
          (.mul (.mul (.const 224) (.pow x 5))
            envelopeSemanticD))
        (.neg (.mul (.const 256) (.pow x 7))))
      (.mul (.const 576) (.pow x 6)))
    (.mul (.const 3) (.pow envelopeSemanticD 3))

def envelopeSemanticP (x : PE) : PE :=
  .add
    (.add
      (.add
        (.add
          (.neg (.mul (.mul (.const 15750) x)
            (.pow envelopeSemanticD 4)))
          (.neg (.mul (.mul (.const 45560) (.pow x 3))
            (.pow envelopeSemanticD 3))))
        (.mul (.mul (.const 10976) (.pow x 5))
          (.pow envelopeSemanticD 2)))
      (.neg (.mul (.mul (.const 30848) (.pow x 7))
        envelopeSemanticD)))
    (.neg (.mul (.const 4608) (.pow x 9)))

/-- Polynomial `K=P(D,n+1)-60D^2J(D,n+1)` in `(n,D)` order. -/
def envelopeSemanticStep : PE :=
  .add (envelopeSemanticP envelopeSemanticNsucc)
    (.neg
      (.mul (.const 60)
        (.mul (.pow envelopeSemanticD 2)
          (envelopeSemanticJ envelopeSemanticNsucc))))

def envelopeSemanticRho (D N : Q') : Nat → Q'
  | 0 => N
  | 1 => D
  | _ => 0

private theorem envelopeSemanticP_Nsucc_eval (D N : Q') :
    RingNormaliser.eval (envelopeSemanticRho D N)
        (envelopeSemanticP envelopeSemanticNsucc) ≈
      lowerSixHermiteSecondFluxPoly D (N + 1) := by
  unfold envelopeSemanticP envelopeSemanticNsucc envelopeSemanticN
    envelopeSemanticD envelopeSemanticOne envelopeSemanticRho
    lowerSixHermiteSecondFluxPoly
  exact Q'.eqv_refl _

private theorem envelopeSemanticJ_Nsucc_eval (D N : Q') :
    RingNormaliser.eval (envelopeSemanticRho D N)
        (envelopeSemanticJ envelopeSemanticNsucc) ≈
      lowerSixDiscreteHermiteFluxPoly D (N + 1) := by
  unfold envelopeSemanticJ envelopeSemanticNsucc envelopeSemanticN
    envelopeSemanticD envelopeSemanticOne envelopeSemanticRho
    lowerSixDiscreteHermiteFluxPoly
  exact Q'.eqv_refl _

private theorem envelopeSemanticJ_N_eval (D N : Q') :
    RingNormaliser.eval (envelopeSemanticRho D N)
        (envelopeSemanticJ envelopeSemanticN) ≈
      lowerSixDiscreteHermiteFluxPoly D N := by
  unfold envelopeSemanticJ envelopeSemanticN envelopeSemanticD
    envelopeSemanticRho lowerSixDiscreteHermiteFluxPoly
  exact Q'.eqv_refl _

theorem envelopeSemanticStep_eval (D N : Q') :
    RingNormaliser.eval (envelopeSemanticRho D N)
        envelopeSemanticStep ≈
      lowerSixHermiteSecondFluxPoly D (N + 1) +
        -(Q'.ofNat 60 * RingNormaliser.qpow D 2 *
          lowerSixDiscreteHermiteFluxPoly D (N + 1)) := by
  unfold envelopeSemanticStep
  let J := RingNormaliser.eval (envelopeSemanticRho D N)
    (envelopeSemanticJ envelopeSemanticNsucc)
  let J' := lowerSixDiscreteHermiteFluxPoly D (N + 1)
  have hJ : J ≈ J' := envelopeSemanticJ_Nsucc_eval D N
  have hmul :
      Q'.ofNat 60 * (RingNormaliser.qpow D 2 * J) ≈
        (Q'.ofNat 60 * RingNormaliser.qpow D 2) * J' :=
    Q'.eqv_trans _ (Q'.ofNat 60 * (RingNormaliser.qpow D 2 * J')) _
      (Q'.mul_eqv_congr_left (Q'.ofNat 60) _ _
        (Q'.mul_eqv_congr_left (RingNormaliser.qpow D 2) _ _ hJ))
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv (Q'.ofNat 60) (RingNormaliser.qpow D 2) J'))
  exact Q'.add_eqv_congr'
    (envelopeSemanticP_Nsucc_eval D N)
    (Q'.neg_eqv_congr _ _ hmul)

/-- Swap the public Taylor expressions from `(D,n)` variable order into the
raw-certificate convention `(n,D)`. -/
def envelopeSemanticSwapDN : Nat → PE
  | 0 => envelopeSemanticD
  | 1 => envelopeSemanticN
  | _ => .const 0

def envelopeSemanticPrefix8 : PE :=
  substitute envelopeSemanticSwapDN (tailTaylor9Prefix 8)

def envelopeSemanticPrefix9 : PE :=
  substitute envelopeSemanticSwapDN tailTaylor9ClearedExpr

private theorem envelopeSemanticEval_env_congr
    (e : PE) (rho sigma : Nat → Q')
    (h : ∀ i, rho i ≈ sigma i) :
    RingNormaliser.eval rho e ≈ RingNormaliser.eval sigma e := by
  induction e with
  | const _ => exact Q'.eqv_refl _
  | var i => exact h i
  | add a b ha hb => exact Q'.add_eqv_congr' ha hb
  | mul a b ha hb =>
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ ha)
        (Q'.mul_eqv_congr_left _ _ _ hb)
  | neg a ha => exact Q'.neg_eqv_congr _ _ ha
  | pow a m ha => exact RingNormaliser.qpow_eqv_congr ha m

private theorem lowerSixDiscreteHermiteFluxPoly_eqv_congr_mode_local
    (D : Q') {N M : Q'} (hNM : N ≈ M) :
    lowerSixDiscreteHermiteFluxPoly D N ≈
      lowerSixDiscreteHermiteFluxPoly D M := by
  have henv : ∀ i,
      envelopeSemanticRho D N i ≈ envelopeSemanticRho D M i := by
    intro i
    cases i with
    | zero => exact hNM
    | succ i =>
        cases i with
        | zero => exact Q'.eqv_refl _
        | succ _ => exact Q'.eqv_refl _
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (envelopeSemanticJ_N_eval D N))
    (Q'.eqv_trans _ _ _
      (envelopeSemanticEval_env_congr
        (envelopeSemanticJ envelopeSemanticN)
        (envelopeSemanticRho D N) (envelopeSemanticRho D M) henv)
      (envelopeSemanticJ_N_eval D M))

private theorem envelopeSemanticSwapDN_eval
    (D N : Q') (i : Nat) :
    RingNormaliser.eval (envelopeSemanticRho D N)
        (envelopeSemanticSwapDN i) ≈
      tailTaylor9Rho D N i := by
  cases i with
  | zero => exact Q'.eqv_refl _
  | succ i =>
      cases i with
      | zero => exact Q'.eqv_refl _
      | succ _ => exact Q'.eqv_refl _

/-- Evaluation after swapping the public eighth-order prefix into `(n,D)`
order is exactly evaluation in its native `(D,n)` order. -/
theorem envelopeSemanticPrefix8_eval (D N : Q') :
    RingNormaliser.eval (envelopeSemanticRho D N)
        envelopeSemanticPrefix8 ≈
      RingNormaliser.eval (tailTaylor9Rho D N)
        (tailTaylor9Prefix 8) := by
  exact Q'.eqv_trans _ _ _
    (eval_substitute (envelopeSemanticRho D N)
      envelopeSemanticSwapDN (tailTaylor9Prefix 8))
    (envelopeSemanticEval_env_congr (tailTaylor9Prefix 8)
      (fun i => RingNormaliser.eval (envelopeSemanticRho D N)
        (envelopeSemanticSwapDN i))
      (tailTaylor9Rho D N)
      (envelopeSemanticSwapDN_eval D N))

/-- Evaluation after swapping the public ninth-order certificate into
`(n,D)` order is its native cleared Taylor value. -/
theorem envelopeSemanticPrefix9_eval (D N : Q') :
    RingNormaliser.eval (envelopeSemanticRho D N)
        envelopeSemanticPrefix9 ≈
      tailTaylor9Cleared D N := by
  unfold tailTaylor9Cleared
  exact Q'.eqv_trans _ _ _
    (eval_substitute (envelopeSemanticRho D N)
      envelopeSemanticSwapDN tailTaylor9ClearedExpr)
    (envelopeSemanticEval_env_congr tailTaylor9ClearedExpr
      (fun i => RingNormaliser.eval (envelopeSemanticRho D N)
        (envelopeSemanticSwapDN i))
      (tailTaylor9Rho D N)
      (envelopeSemanticSwapDN_eval D N))

theorem envelopeSemanticPrefix8_physical {D u : Q'}
    (hDu : D * u ≈ (1 : Q')) (n : Nat) (hn : 4 ≤ n) :
    RingNormaliser.eval (envelopeSemanticRho D (Q'.ofNat n))
        envelopeSemanticPrefix8 ≈
      (Q'.ofNat 362880 * RingNormaliser.qpow D 9) *
        oneSubTaylor8 u (2 * n + 1) :=
  Q'.eqv_trans _ _ _
    (envelopeSemanticPrefix8_eval D (Q'.ofNat n))
    (tailTaylor8Prefix_physical_bridge hDu n hn)

theorem envelopeSemanticPrefix9_physical {D u : Q'}
    (hDu : D * u ≈ (1 : Q')) (n : Nat) (hn : 4 ≤ n) :
    RingNormaliser.eval (envelopeSemanticRho D (Q'.ofNat n))
        envelopeSemanticPrefix9 ≈
      (Q'.ofNat 362880 * RingNormaliser.qpow D 9) *
        oneSubTaylor9 u (2 * n + 1) :=
  Q'.eqv_trans _ _ _
    (envelopeSemanticPrefix9_eval D (Q'.ofNat n))
    (tailTaylor9Cleared_physical_bridge hDu n hn)

def envelopeSemanticCommon : PE :=
  .mul (.pow envelopeSemanticR 4)
    (.pow envelopeSemanticDsucc 15)

def envelopeSemanticCommonValue (D : Q') : Q' :=
  RingNormaliser.qpow
      (RingNormaliser.qpow D 2 + -(1 : Q')) 4 *
    RingNormaliser.qpow (D + (1 : Q')) 15

def envelopeSemanticDenominatorValue (D : Q') : Q' :=
  RingNormaliser.qpow D 18 * envelopeSemanticCommonValue D

private theorem envelopeSemanticMul_eqv_congr
    {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ (a' * b) _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

theorem envelopeSemanticCommon_eval (D N : Q') :
    RingNormaliser.eval (envelopeSemanticRho D N)
        envelopeSemanticCommon ≈
      envelopeSemanticCommonValue D := by
  have hneg : Q'.ofInt (-1) ≈ -(1 : Q') := by decide
  have hR :
      RingNormaliser.eval (envelopeSemanticRho D N)
          envelopeSemanticR ≈
        RingNormaliser.qpow D 2 + -(1 : Q') :=
    Q'.add_eqv_congr' (Q'.eqv_refl _) hneg
  have hDp :
      RingNormaliser.eval (envelopeSemanticRho D N)
          envelopeSemanticDsucc ≈
        D + (1 : Q') := Q'.eqv_refl _
  exact envelopeSemanticMul_eqv_congr
    (RingNormaliser.qpow_eqv_congr hR 4)
    (RingNormaliser.qpow_eqv_congr hDp 15)

theorem envelopeSemanticStep_eval_nat (k n : Nat) :
    RingNormaliser.eval
        (envelopeSemanticRho (Q'.ofNat (k + 2)) (Q'.ofNat n))
        envelopeSemanticStep ≈
      lowerSixTailStepCoefficient k n := by
  let D := Q'.ofNat (k + 2)
  let N := Q'.ofNat n + (1 : Q')
  let N' := Q'.ofNat (n + 1)
  have hsucc : N ≈ N' := by
    exact Q'.eqv_symm
      (Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv n 1)
        (Q'.add_eqv_congr_left (Q'.ofNat n) (Q'.ofNat 1) (1 : Q')
          (by decide)))
  have hP := lowerSixHermiteSecondFluxPoly_eqv_congr_mode D hsucc
  have hJ := lowerSixDiscreteHermiteFluxPoly_eqv_congr_mode_local D hsucc
  have hscaledJ :
      Q'.ofNat 60 * RingNormaliser.qpow D 2 *
          lowerSixDiscreteHermiteFluxPoly D N ≈
        Q'.ofNat 60 * RingNormaliser.qpow D 2 *
          lowerSixDiscreteHermiteFluxPoly D N' :=
    Q'.mul_eqv_congr_left
      (Q'.ofNat 60 * RingNormaliser.qpow D 2) _ _ hJ
  have hstep := envelopeSemanticStep_eval D (Q'.ofNat n)
  unfold lowerSixTailStepCoefficient
  dsimp only [D, N, N'] at hP hscaledJ hstep ⊢
  exact Q'.eqv_trans _ _ _ hstep
    (Q'.add_eqv_congr' hP (Q'.neg_eqv_congr _ _ hscaledJ))

private theorem envelopeSemantic_harmDen_mul_harmU (k : Nat) :
    Q'.ofNat (k + 2) * HarmonicCutoffBoundary.harmU k ≈ (1 : Q') := by
  unfold HarmonicCutoffBoundary.harmU SummableInverseSquare.unit
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast, Q'.mkPos_num, Q'.mkPos_den, Int.mul_one,
    Int.one_mul]
  have h1n : (1 : Q').num = 1 := rfl
  have h1d : ((1 : Q').den : Int) = 1 := rfl
  rw [h1n, h1d, Int.mul_one, Int.one_mul]

/-- The Taylor part of `4608 * E8Cleared`. -/
def envelopeSemanticTaylor8Scaled : PE :=
  .mul (.pow envelopeSemanticPrefix8 2)
    (.mul envelopeSemanticCommon envelopeSemanticStep)

/-- The Taylor part of `512 * E9Cleared`. -/
def envelopeSemanticTaylor9Scaled : PE :=
  .mul (.pow envelopeSemanticPrefix9 2)
    (.mul envelopeSemanticCommon envelopeSemanticStep)

/-- Compositional semantics of the scaled eighth-order Taylor contribution.
No dense coefficient expansion occurs in this proof. -/
theorem envelopeSemanticTaylor8Scaled_physical {k n : Nat}
    (hn : 4 ≤ n) :
    RingNormaliser.eval
        (envelopeSemanticRho (Q'.ofNat (k + 2)) (Q'.ofNat n))
        envelopeSemanticTaylor8Scaled ≈
      RingNormaliser.qpow
          ((Q'.ofNat 362880 *
              RingNormaliser.qpow (Q'.ofNat (k + 2)) 9) *
            oneSubTaylor8 (HarmonicCutoffBoundary.harmU k) (2 * n + 1)) 2 *
        (envelopeSemanticCommonValue (Q'.ofNat (k + 2)) *
          lowerSixTailStepCoefficient k n) := by
  have hprefix := envelopeSemanticPrefix8_physical
    (envelopeSemantic_harmDen_mul_harmU k) n hn
  have hcommon := envelopeSemanticCommon_eval
    (Q'.ofNat (k + 2)) (Q'.ofNat n)
  have hstep := envelopeSemanticStep_eval_nat k n
  exact envelopeSemanticMul_eqv_congr
    (RingNormaliser.qpow_eqv_congr hprefix 2)
    (envelopeSemanticMul_eqv_congr hcommon hstep)

/-- Compositional semantics of the scaled ninth-order Taylor contribution. -/
theorem envelopeSemanticTaylor9Scaled_physical {k n : Nat}
    (hn : 4 ≤ n) :
    RingNormaliser.eval
        (envelopeSemanticRho (Q'.ofNat (k + 2)) (Q'.ofNat n))
        envelopeSemanticTaylor9Scaled ≈
      RingNormaliser.qpow
          ((Q'.ofNat 362880 *
              RingNormaliser.qpow (Q'.ofNat (k + 2)) 9) *
            oneSubTaylor9 (HarmonicCutoffBoundary.harmU k) (2 * n + 1)) 2 *
        (envelopeSemanticCommonValue (Q'.ofNat (k + 2)) *
          lowerSixTailStepCoefficient k n) := by
  have hprefix := envelopeSemanticPrefix9_physical
    (envelopeSemantic_harmDen_mul_harmU k) n hn
  have hcommon := envelopeSemanticCommon_eval
    (Q'.ofNat (k + 2)) (Q'.ofNat n)
  have hstep := envelopeSemanticStep_eval_nat k n
  exact envelopeSemanticMul_eqv_congr
    (RingNormaliser.qpow_eqv_congr hprefix 2)
    (envelopeSemanticMul_eqv_congr hcommon hstep)

private theorem envelopeRNQpow_mul_base (a b : Q') : ∀ exponent,
    RingNormaliser.qpow (a * b) exponent ≈
      RingNormaliser.qpow a exponent * RingNormaliser.qpow b exponent
  | 0 => Q'.eqv_symm (Q'.one_mul_eqv 1)
  | exponent + 1 => by
      show RingNormaliser.qpow (a * b) exponent * (a * b) ≈
        (RingNormaliser.qpow a exponent * a) *
          (RingNormaliser.qpow b exponent * b)
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (a * b)
          (envelopeRNQpow_mul_base a b exponent))
        (FusionResidualBound.mul_four_regroup
          (RingNormaliser.qpow a exponent)
          (RingNormaliser.qpow b exponent) a b)

private theorem envelopeRNQpow_iterate (value : Q') (a : Nat) : ∀ b,
    RingNormaliser.qpow (RingNormaliser.qpow value a) b ≈
      RingNormaliser.qpow value (a * b)
  | 0 => by
      rw [Nat.mul_zero]
      exact Q'.eqv_refl _
  | b + 1 => by
      show RingNormaliser.qpow (RingNormaliser.qpow value a) b *
          RingNormaliser.qpow value a ≈
        RingNormaliser.qpow value (a * (b + 1))
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (RingNormaliser.qpow value a)
          (envelopeRNQpow_iterate value a b)) ?_
      rw [Nat.mul_succ]
      exact Q'.eqv_symm
        (RingNormaliser.qpow_add value (a * b) a)

private theorem envelopeMulFive_regroup (A B C D E : Q') :
    ((A * B) * C) * (D * E) ≈
      A * ((B * D) * (C * E)) := by
  exact Q'.eqv_trans _ _ _
    (FusionResidualBound.mul_four_regroup (A * B) C D E)
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (C * E)
        (Q'.mul_assoc_eqv A B D))
      (Q'.mul_assoc_eqv A (B * D) (C * E)))

/-- The factorial-square, denominator, Taylor square, and step coefficient
can be regrouped without changing their exact rational value. -/
theorem envelopeTaylorPhysical_algebra (D U K : Q') :
    RingNormaliser.qpow
          ((Q'.ofNat 362880 * RingNormaliser.qpow D 9) * U) 2 *
        (envelopeSemanticCommonValue D * K) ≈
      RingNormaliser.qpow (Q'.ofNat 362880) 2 *
        (envelopeSemanticDenominatorValue D *
          (RingNormaliser.qpow U 2 * K)) := by
  let C := Q'.ofNat 362880
  let D9 := RingNormaliser.qpow D 9
  let C2 := RingNormaliser.qpow C 2
  let D18 := RingNormaliser.qpow D 18
  let U2 := RingNormaliser.qpow U 2
  let common := envelopeSemanticCommonValue D
  have houter := envelopeRNQpow_mul_base (C * D9) U 2
  have hinner := envelopeRNQpow_mul_base C D9 2
  have hD : RingNormaliser.qpow D9 2 ≈ D18 := by
    exact envelopeRNQpow_iterate D 9 2
  have hinner' : RingNormaliser.qpow (C * D9) 2 ≈ C2 * D18 :=
    Q'.eqv_trans _ _ _ hinner
      (Q'.mul_eqv_congr_left C2 _ _ hD)
  have hprefix : RingNormaliser.qpow ((C * D9) * U) 2 ≈
      (C2 * D18) * U2 :=
    Q'.eqv_trans _ _ _ houter
      (Q'.mul_eqv_congr_right _ _ U2 hinner')
  dsimp only [C, D9, C2, D18, U2, common] at hprefix ⊢
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _
      (envelopeSemanticCommonValue D * K) hprefix)
    (envelopeMulFive_regroup
      (RingNormaliser.qpow (Q'.ofNat 362880) 2)
      (RingNormaliser.qpow D 18)
      (RingNormaliser.qpow U 2)
      (envelopeSemanticCommonValue D) K)

theorem envelopeSemanticTaylor8Scaled_production {k n : Nat}
    (hn : 4 ≤ n) :
    RingNormaliser.eval
        (envelopeSemanticRho (Q'.ofNat (k + 2)) (Q'.ofNat n))
        envelopeSemanticTaylor8Scaled ≈
      RingNormaliser.qpow (Q'.ofNat 362880) 2 *
        (envelopeSemanticDenominatorValue (Q'.ofNat (k + 2)) *
          (RingNormaliser.qpow
              (oneSubTaylor8 (HarmonicCutoffBoundary.harmU k)
                (2 * n + 1)) 2 *
            lowerSixTailStepCoefficient k n)) :=
  Q'.eqv_trans _ _ _
    (envelopeSemanticTaylor8Scaled_physical hn)
    (envelopeTaylorPhysical_algebra
      (Q'.ofNat (k + 2))
      (oneSubTaylor8 (HarmonicCutoffBoundary.harmU k) (2 * n + 1))
      (lowerSixTailStepCoefficient k n))

theorem envelopeSemanticTaylor9Scaled_production {k n : Nat}
    (hn : 4 ≤ n) :
    RingNormaliser.eval
        (envelopeSemanticRho (Q'.ofNat (k + 2)) (Q'.ofNat n))
        envelopeSemanticTaylor9Scaled ≈
      RingNormaliser.qpow (Q'.ofNat 362880) 2 *
        (envelopeSemanticDenominatorValue (Q'.ofNat (k + 2)) *
          (RingNormaliser.qpow
              (oneSubTaylor9 (HarmonicCutoffBoundary.harmU k)
                (2 * n + 1)) 2 *
            lowerSixTailStepCoefficient k n)) :=
  Q'.eqv_trans _ _ _
    (envelopeSemanticTaylor9Scaled_physical hn)
    (envelopeTaylorPhysical_algebra
      (Q'.ofNat (k + 2))
      (oneSubTaylor9 (HarmonicCutoffBoundary.harmU k) (2 * n + 1))
      (lowerSixTailStepCoefficient k n))

#print axioms envelopeSemanticStep_eval
#print axioms envelopeSemanticPrefix8_eval
#print axioms envelopeSemanticPrefix9_eval
#print axioms envelopeSemanticTaylor8Scaled_physical
#print axioms envelopeSemanticTaylor9Scaled_physical
#print axioms envelopeTaylorPhysical_algebra
#print axioms envelopeSemanticTaylor8Scaled_production
#print axioms envelopeSemanticTaylor9Scaled_production

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeTaylorSemantic
