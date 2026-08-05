/-
`FusionBoxFirstShellReserve` -- exact central-shell producer for the
all-cutoff physical prefix campaign.

This file classifies equality in the balanced SU(2) strand-energy bounds.
Those equality cases are the finite, symbolic replacement for evaluating a
large four-index coefficient bucket: the even channel has one central pair,
whereas the odd channel has its two reflected central pairs.

The resulting first-shell formulae are stated directly for
`rawPowerCoeff`, hence connect to the canonical cleared prefix through the
existing four-adic seam.  No detached polynomial compiler is introduced.
-/

import YMGap.Continuum.FusionBoxPrefixReserve
import YMGap.Continuum.FusionBoxStrandCeilings

namespace YMGap.Continuum.FusionBoxFirstShellReserve

open YMGap.Continuum
open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.CoreBBernsteinConsumer
open YMGap.Continuum.FusionCoreStepRoundA
open YMGap.Continuum.FusionCoreStepRoundB
open YMGap.Continuum.FusionCoreStepRoundD
open YMGap.Continuum.BernsteinMonomialReconstruction
open YMGap.Continuum.BernsteinSignedMonomialReconstruction
open YMGap.Continuum.HarmonicThetaPascalBridge
open YMGap.Continuum.HarmonicThetaPascalEvaluation
open YMGap.Continuum.FusionBoxBernsteinReconstruction
open YMGap.Continuum.FusionBoxPrefixReserve

/-! ## 1. Equality cases in the balanced strand bounds -/

/-- Equality in the even balanced Casimir bound forces the unique central
strand and no common content. -/
theorem fusionCasimir_even_eq_min
    {a b m : Nat} (hactive : fusionOK a b (2 * m) = true)
    (heq : c4 a + c4 b = 2 * c4 m) :
    a = m ∧ b = m := by
  obtain ⟨p, q, r, ha, hb, ht⟩ := (fusionOK_strand a b (2 * m)).mp hactive
  rw [ha, hb] at heq
  by_cases hpm : p ≤ m
  · let d := m - p
    have hd : d ≤ m := by unfold d; omega
    have hq : q = m + d := by unfold d; omega
    have hp' : p = m - d := by unfold d; omega
    rw [hp', hq] at heq
    have henergy := c4_even_strand m d r hd
    have hsum : 2 * d * d + 2 * r * (2 * m + r + 2) = 0 := by
      omega
    have hd0 : d = 0 := by
      have hx := (Nat.add_eq_zero_iff.mp hsum).1
      rcases Nat.mul_eq_zero.mp hx with h2d | hd
      · rcases Nat.mul_eq_zero.mp h2d with h2 | hd
        · omega
        · exact hd
      · exact hd
    have hr0 : r = 0 := by
      have hy := (Nat.add_eq_zero_iff.mp hsum).2
      rcases Nat.mul_eq_zero.mp hy with h2r | hfactor
      · rcases Nat.mul_eq_zero.mp h2r with h2 | hr
        · omega
        · exact hr
      · omega
    constructor <;> omega
  · have hmp : m ≤ p := by omega
    let d := p - m
    have hd : d ≤ m := by unfold d; omega
    have hp' : p = m + d := by unfold d; omega
    have hq : q = m - d := by unfold d; omega
    rw [hp', hq] at heq
    have henergy := c4_even_strand m d r hd
    have hsum : 2 * d * d + 2 * r * (2 * m + r + 2) = 0 := by
      omega
    have hd0 : d = 0 := by
      have hx := (Nat.add_eq_zero_iff.mp hsum).1
      rcases Nat.mul_eq_zero.mp hx with h2d | hd
      · rcases Nat.mul_eq_zero.mp h2d with h2 | hd
        · omega
        · exact hd
      · exact hd
    have hr0 : r = 0 := by
      have hy := (Nat.add_eq_zero_iff.mp hsum).2
      rcases Nat.mul_eq_zero.mp hy with h2r | hfactor
      · rcases Nat.mul_eq_zero.mp h2r with h2 | hr
        · omega
        · exact hr
      · omega
    constructor <;> omega

/-- Equality in the odd balanced Casimir bound leaves exactly the two
reflected central pairs and no common content. -/
theorem fusionCasimir_odd_eq_min
    {a b m : Nat} (hactive : fusionOK a b (2 * m + 1) = true)
    (heq : c4 a + c4 b = c4 m + c4 (m + 1)) :
    (a = m ∧ b = m + 1) ∨ (a = m + 1 ∧ b = m) := by
  obtain ⟨p, q, r, ha, hb, ht⟩ :=
    (fusionOK_strand a b (2 * m + 1)).mp hactive
  rw [ha, hb] at heq
  by_cases hpm : p ≤ m
  · let d := m - p
    have hd : d ≤ m := by unfold d; omega
    have hp' : p = m - d := by unfold d; omega
    have hq : q = m + 1 + d := by unfold d; omega
    rw [hp', hq] at heq
    have henergy := c4_odd_strand m d r hd
    have hsum : 2 * d * (d + 1) + 2 * r * (2 * m + r + 3) = 0 := by
      omega
    have hd0 : d = 0 := by
      have hx := (Nat.add_eq_zero_iff.mp hsum).1
      rcases Nat.mul_eq_zero.mp hx with h2d | hsucc
      · rcases Nat.mul_eq_zero.mp h2d with h2 | hd
        · omega
        · exact hd
      · omega
    have hr0 : r = 0 := by
      have hy := (Nat.add_eq_zero_iff.mp hsum).2
      rcases Nat.mul_eq_zero.mp hy with h2r | hfactor
      · rcases Nat.mul_eq_zero.mp h2r with h2 | hr
        · omega
        · exact hr
      · omega
    right
    constructor <;> omega
  · have hmp : m + 1 ≤ p := by omega
    let d := p - (m + 1)
    have hd : d ≤ m := by unfold d; omega
    have hp' : p = m + 1 + d := by unfold d; omega
    have hq : q = m - d := by unfold d; omega
    rw [hp', hq] at heq
    have henergy := c4_odd_strand m d r hd
    have hsum : 2 * d * (d + 1) + 2 * r * (2 * m + r + 3) = 0 := by
      omega
    have hd0 : d = 0 := by
      have hx := (Nat.add_eq_zero_iff.mp hsum).1
      rcases Nat.mul_eq_zero.mp hx with h2d | hsucc
      · rcases Nat.mul_eq_zero.mp h2d with h2 | hd
        · omega
        · exact hd
      · omega
    have hr0 : r = 0 := by
      have hy := (Nat.add_eq_zero_iff.mp hsum).2
      rcases Nat.mul_eq_zero.mp hy with h2r | hfactor
      · rcases Nat.mul_eq_zero.mp h2r with h2 | hr
        · omega
        · exact hr
      · omega
    left
    constructor <;> omega

/-! ## 2. A generic all-prefix domination compiler -/

/-- The nonnegative cleared contribution of the middle-square cell. -/
def boxPositiveClearedCell
    (N s a a' b b' : Nat) : Int :=
  Int.ofNat (boxCellClearedMultiplicity N
    (boxPositiveMultiplicity s a a' b b') a a' b b')

/-- The nonnegative cleared contribution of the outer-product cell. -/
def boxNegativeClearedCell
    (N s a a' b b' : Nat) : Int :=
  Int.ofNat (boxCellClearedMultiplicity N
    (boxNegativeMultiplicity s a a' b b') a a' b b')

/-- Positive part of the canonical term-filtered prefix. -/
def boxPositiveClearedPrefix (N s K : Nat) : Int :=
  boxCellIntSum N (fun a a' b b' =>
    if boxQuadHalfExponent a a' b b' < K then
      boxPositiveClearedCell N s a a' b b'
    else 0)

/-- Negative part of the canonical term-filtered prefix. -/
def boxNegativeClearedPrefix (N s K : Nat) : Int :=
  boxCellIntSum N (fun a a' b b' =>
    if boxQuadHalfExponent a a' b b' < K then
      boxNegativeClearedCell N s a a' b b'
    else 0)

/-- Total negative mass after the same global denominator clearing. -/
def boxNegativeClearedTotal (N s : Nat) : Int :=
  boxCellIntSum N (boxNegativeClearedCell N s)

private theorem intFsum_sub_local (f g : Nat → Int) : ∀ n,
    intFsum (fun i => f i - g i) n = intFsum f n - intFsum g n
  | 0 => rfl
  | n + 1 => by
      rw [intFsum, intFsum, intFsum, intFsum_sub_local f g n]
      omega

private theorem intFsum_le_local {f g : Nat → Int}
    (h : ∀ i, f i ≤ g i) : ∀ n, intFsum f n ≤ intFsum g n
  | 0 => Int.le_refl 0
  | n + 1 => by
      rw [intFsum, intFsum]
      exact Int.add_le_add (intFsum_le_local h n) (h n)

private theorem boxCellIntSum_sub_local
    (N : Nat) (f g : Nat → Nat → Nat → Nat → Int) :
    boxCellIntSum N (fun a a' b b' => f a a' b b' - g a a' b b') =
      boxCellIntSum N f - boxCellIntSum N g := by
  unfold boxCellIntSum
  have h3 (a a' b : Nat) :
      intFsum (fun b' => f a a' b b' - g a a' b b') (N + 1) =
        intFsum (fun b' => f a a' b b') (N + 1) -
          intFsum (fun b' => g a a' b b') (N + 1) :=
    intFsum_sub_local _ _ (N + 1)
  have h2 (a a' : Nat) :
      intFsum (fun b => intFsum (fun b' =>
          f a a' b b' - g a a' b b') (N + 1)) (N + 1) =
        intFsum (fun b => intFsum (fun b' => f a a' b b') (N + 1)) (N + 1) -
          intFsum (fun b => intFsum (fun b' => g a a' b b') (N + 1))
            (N + 1) := by
    calc
      _ = intFsum (fun b =>
          intFsum (fun b' => f a a' b b') (N + 1) -
            intFsum (fun b' => g a a' b b') (N + 1)) (N + 1) := by
            exact congrArg (fun h : Nat → Int => intFsum h (N + 1))
              (funext (fun b => h3 a a' b))
      _ = _ := intFsum_sub_local _ _ (N + 1)
  have h1 (a : Nat) :
      intFsum (fun a' => intFsum (fun b => intFsum (fun b' =>
          f a a' b b' - g a a' b b') (N + 1)) (N + 1)) (N + 1) =
        intFsum (fun a' => intFsum (fun b => intFsum (fun b' =>
          f a a' b b') (N + 1)) (N + 1)) (N + 1) -
        intFsum (fun a' => intFsum (fun b => intFsum (fun b' =>
          g a a' b b') (N + 1)) (N + 1)) (N + 1) := by
    calc
      _ = intFsum (fun a' =>
          intFsum (fun b => intFsum (fun b' => f a a' b b') (N + 1))
              (N + 1) -
            intFsum (fun b => intFsum (fun b' => g a a' b b') (N + 1))
              (N + 1)) (N + 1) := by
            exact congrArg (fun h : Nat → Int => intFsum h (N + 1))
              (funext (fun a' => h2 a a'))
      _ = _ := intFsum_sub_local _ _ (N + 1)
  calc
    _ = intFsum (fun a =>
        intFsum (fun a' => intFsum (fun b => intFsum (fun b' =>
          f a a' b b') (N + 1)) (N + 1)) (N + 1) -
        intFsum (fun a' => intFsum (fun b => intFsum (fun b' =>
          g a a' b b') (N + 1)) (N + 1)) (N + 1)) (N + 1) := by
          exact congrArg (fun h : Nat → Int => intFsum h (N + 1))
            (funext h1)
    _ = _ := intFsum_sub_local _ _ (N + 1)

private theorem boxCellIntSum_le_local
    {N : Nat} {f g : Nat → Nat → Nat → Nat → Int}
    (h : ∀ a a' b b', f a a' b b' ≤ g a a' b b') :
    boxCellIntSum N f ≤ boxCellIntSum N g := by
  unfold boxCellIntSum
  apply intFsum_le_local
  intro a
  apply intFsum_le_local
  intro a'
  apply intFsum_le_local
  intro b
  apply intFsum_le_local
  intro b'
  exact h a a' b b'

/-- Exact positive-minus-negative split of Track A's term-filtered carrier. -/
theorem boxClearedPowerPrefix_eq_positive_sub_negative
    (N s K : Nat) :
    boxClearedPowerPrefix N s K =
      boxPositiveClearedPrefix N s K - boxNegativeClearedPrefix N s K := by
  unfold boxPositiveClearedPrefix boxNegativeClearedPrefix
    boxPositiveClearedCell boxNegativeClearedCell
  change boxCellIntSum N (fun a a' b b' =>
      if boxQuadHalfExponent a a' b b' < K then
        boxCellClearedCoefficient N s a a' b b'
      else 0) = _
  unfold boxCellClearedCoefficient
  have hfun :
      (fun a a' b b' =>
        if boxQuadHalfExponent a a' b b' < K then
          Int.ofNat (boxCellClearedMultiplicity N
            (boxPositiveMultiplicity s a a' b b') a a' b b') -
          Int.ofNat (boxCellClearedMultiplicity N
            (boxNegativeMultiplicity s a a' b b') a a' b b')
        else 0) =
      (fun a a' b b' =>
        (if boxQuadHalfExponent a a' b b' < K then
          Int.ofNat (boxCellClearedMultiplicity N
            (boxPositiveMultiplicity s a a' b b') a a' b b') else 0) -
        (if boxQuadHalfExponent a a' b b' < K then
          Int.ofNat (boxCellClearedMultiplicity N
            (boxNegativeMultiplicity s a a' b b') a a' b b') else 0)) := by
    funext a a' b b'
    by_cases h : boxQuadHalfExponent a a' b b' < K
    · simp [h]
    · simp [h]
  rw [hfun, boxCellIntSum_sub_local]

/-- Filtering by an arbitrary physical shell cutoff can only remove negative
mass.  This is the all-`K` monotonicity step: no shell classification appears
in its statement or proof. -/
theorem boxNegativeClearedPrefix_le_total (N s K : Nat) :
    boxNegativeClearedPrefix N s K ≤ boxNegativeClearedTotal N s := by
  unfold boxNegativeClearedPrefix boxNegativeClearedTotal
  apply boxCellIntSum_le_local
  intro a a' b b'
  by_cases h : boxQuadHalfExponent a a' b b' < K
  · simp [h]
  · simp [h, boxNegativeClearedCell]

/-- Generic reserve compiler.  Once a fixed positive central reserve lies in
the prefix and dominates the *total* negative mass, every later prefix is
nonnegative at once. -/
theorem boxClearedPowerPrefix_nonnegative_of_total_domination
    (N s K : Nat) (reserve : Int)
    (hnegative : boxNegativeClearedTotal N s ≤ reserve)
    (hpositive : reserve ≤ boxPositiveClearedPrefix N s K) :
    0 ≤ boxClearedPowerPrefix N s K := by
  rw [boxClearedPowerPrefix_eq_positive_sub_negative]
  have hfilter := boxNegativeClearedPrefix_le_total N s K
  omega

/-! ## 3. Exact endpoint scale bridge -/

private abbrev halfW : Q' := wH

private theorem pow_eqv_congr_local {a b : Q'} (h : a.eqv b) :
    ∀ n : Nat, (a ^ n).eqv (b ^ n)
  | 0 => Q'.eqv_refl 1
  | n + 1 => by
      show (a * a ^ n).eqv (b * b ^ n)
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right a b (a ^ n) h)
        (Q'.mul_eqv_congr_left b (a ^ n) (b ^ n)
          (pow_eqv_congr_local h n))

private theorem one_pow_eqv_local : ∀ n : Nat,
    ((1 : Q') ^ n).eqv (1 : Q')
  | 0 => Q'.eqv_refl 1
  | n + 1 => by
      show ((1 : Q') * (1 : Q') ^ n).eqv (1 : Q')
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (1 : Q') _ _ (one_pow_eqv_local n))
        (Q'.one_mul_eqv (1 : Q'))

private theorem ofInt_intFsum_eqv (f : Nat → Int) : ∀ n,
    (Q'.ofInt (intFsum f n)).eqv
      (fsum (fun i => Q'.ofInt (f i)) n)
  | 0 => Q'.eqv_refl 0
  | n + 1 => by
      change (Q'.ofInt (intFsum f n + f n)).eqv
        (fsum (fun i => Q'.ofInt (f i)) n + Q'.ofInt (f n))
      exact Q'.eqv_trans _ _ _
        (YMGap.Continuum.RingNormaliser.ofInt_add (intFsum f n) (f n))
        (Q'.add_eqv_congr_right _ _ _ (ofInt_intFsum_eqv f n))

private theorem ofInt_boxCellIntSum_eqv
    (N : Nat) (f : Nat → Nat → Nat → Nat → Int) :
    (Q'.ofInt (boxCellIntSum N f)).eqv
      (fsum (fun a => fsum (fun a' => fsum (fun b => fsum (fun b' =>
        Q'.ofInt (f a a' b b')) (N + 1)) (N + 1)) (N + 1)) (N + 1)) := by
  unfold boxCellIntSum
  refine Q'.eqv_trans _ _ _ (ofInt_intFsum_eqv _ (N + 1)) ?_
  refine fsum_eqv_congr _ _ (fun a => ?_) (N + 1)
  refine Q'.eqv_trans _ _ _ (ofInt_intFsum_eqv _ (N + 1)) ?_
  refine fsum_eqv_congr _ _ (fun a' => ?_) (N + 1)
  refine Q'.eqv_trans _ _ _ (ofInt_intFsum_eqv _ (N + 1)) ?_
  refine fsum_eqv_congr _ _ (fun b => ?_) (N + 1)
  exact ofInt_intFsum_eqv _ (N + 1)

/-- One denominator-cleared unsigned product cell is exactly `4^D` times
the corresponding endpoint kernel product. -/
theorem boxProductClearedCell_endpoint
    (N leftChannel rightChannel a a' b b' : Nat)
    (hparity : leftChannel % 2 = rightChannel % 2)
    (ha : a ≤ N) (ha' : a' ≤ N) (hb : b ≤ N) (hb' : b' ≤ N) :
    (Q'.ofInt (Int.ofNat (boxCellClearedMultiplicity N
      (boxProductMultiplicity leftChannel rightChannel a a' b b')
      a a' b b'))).eqv
      (Q'.ofNat (4 ^ boxBernsteinDegree N) *
        (boxKer halfW leftChannel a b *
          boxKer halfW rightChannel a' b')) := by
  let D := boxBernsteinDegree N
  let e := boxQuadHalfExponent a a' b b'
  let z : Int := Int.ofNat (boxCellClearedMultiplicity N
    (boxProductMultiplicity leftChannel rightChannel a a' b b')
    a a' b b')
  let u := physicalSquareCoordinate halfW
  have heD : e ≤ D := boxQuadHalfExponent_le_degree ha ha' hb hb'
  have hu : u.eqv (1 : Q') := by
    unfold u halfW physicalSquareCoordinate wH qpow
    decide
  have hupow : (u ^ e).eqv (1 : Q') :=
    Q'.eqv_trans _ _ _ (pow_eqv_congr_local hu e) (one_pow_eqv_local e)
  have hleft :
      (signedBernsteinEval D
        (boxProductBernsteinRow N leftChannel rightChannel a a' b b') u).eqv
        (Q'.ofInt z) := by
    unfold boxProductBernsteinRow
    refine Q'.eqv_trans _ _ _
      (signedBernsteinEval_scale D z (thetaMonoBernCoeff D e) u) ?_
    refine Q'.eqv_trans _ (Q'.ofInt z * u ^ e) _
      (Q'.mul_eqv_congr_left (Q'.ofInt z) _ _
        (thetaMonoBernCoeff_eval D e u heD)) ?_
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofInt z) _ _ hupow)
      (Q'.mul_one_eqv (Q'.ofInt z))
  have hright := boxProductBernsteinRow_eval halfW N
    leftChannel rightChannel a a' b b' hparity ha ha' hb hb'
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hleft) hright

/-- The total denominator-cleared unsigned product ledger. -/
def boxProductClearedTotal
    (N leftChannel rightChannel : Nat) : Int :=
  boxCellIntSum N (fun a a' b b' =>
    Int.ofNat (boxCellClearedMultiplicity N
      (boxProductMultiplicity leftChannel rightChannel a a' b b')
      a a' b b'))

private theorem const_mul_fsum4_local
    (c : Q') (F : Nat → Nat → Nat → Nat → Q') (n : Nat) :
    (c * fsum (fun a => fsum (fun a' =>
      fsum (fun b => fsum (fun b' => F a a' b b') n) n) n) n).eqv
      (fsum (fun a => fsum (fun a' =>
        fsum (fun b => fsum (fun b' => c * F a a' b b') n) n) n) n) := by
  refine Q'.eqv_trans _ _ _
    (fsum_const_mul c (fun a => fsum (fun a' =>
      fsum (fun b => fsum (fun b' => F a a' b b') n) n) n) n) ?_
  refine fsum_eqv_congr _ _ (fun a => ?_) n
  refine Q'.eqv_trans _ _ _
    (fsum_const_mul c (fun a' =>
      fsum (fun b => fsum (fun b' => F a a' b b') n) n) n) ?_
  refine fsum_eqv_congr _ _ (fun a' => ?_) n
  refine Q'.eqv_trans _ _ _
    (fsum_const_mul c (fun b => fsum (fun b' => F a a' b b') n) n) ?_
  refine fsum_eqv_congr _ _ (fun b => ?_) n
  exact fsum_const_mul c (fun b' => F a a' b b') n

/-- Summed scale bridge: the total cleared product ledger is exactly `4^D`
times the endpoint product of the two actual finite boxes. -/
theorem boxProductClearedTotal_endpoint
    (N leftChannel rightChannel : Nat)
    (hparity : leftChannel % 2 = rightChannel % 2) :
    (Q'.ofInt (boxProductClearedTotal N leftChannel rightChannel)).eqv
      (Q'.ofNat (4 ^ boxBernsteinDegree N) *
        (boxSum halfW N leftChannel * boxSum halfW N rightChannel)) := by
  let c := Q'.ofNat (4 ^ boxBernsteinDegree N)
  unfold boxProductClearedTotal
  refine Q'.eqv_trans _ _ _ (ofInt_boxCellIntSum_eqv N _) ?_
  refine Q'.eqv_trans _
    (fsum (fun a => fsum (fun a' => fsum (fun b => fsum (fun b' =>
      c * (boxKer halfW leftChannel a b *
        boxKer halfW rightChannel a' b')) (N + 1)) (N + 1)) (N + 1))
          (N + 1)) _ ?_ ?_
  · refine fsum_eqv_congr_lt _ _ (N + 1) (fun a ha => ?_)
    refine fsum_eqv_congr_lt _ _ (N + 1) (fun a' ha' => ?_)
    refine fsum_eqv_congr_lt _ _ (N + 1) (fun b hb => ?_)
    refine fsum_eqv_congr_lt _ _ (N + 1) (fun b' hb' => ?_)
    exact boxProductClearedCell_endpoint N leftChannel rightChannel
      a a' b b' hparity (by omega) (by omega) (by omega) (by omega)
  · refine Q'.eqv_trans _
      (c * quadProd halfW N leftChannel rightChannel) _
      (Q'.eqv_symm (const_mul_fsum4_local c
        (fun a a' b b' => boxKer halfW leftChannel a b *
          boxKer halfW rightChannel a' b') (N + 1))) ?_
    exact Q'.mul_eqv_congr_left c _ _
      (Q'.eqv_symm
        (boxSum_mul_eq_quad halfW N leftChannel rightChannel))

/-- The negative ledger is the outer product ledger, definitionally. -/
theorem boxNegativeClearedTotal_eq_product (N s : Nat) :
    boxNegativeClearedTotal N s = boxProductClearedTotal N s (s + 2) := rfl

private theorem ofInt_le_iff_local (x y : Int) :
    Q'.ofInt x ≤ Q'.ofInt y ↔ x ≤ y := by
  change x * 1 ≤ y * 1 ↔ x ≤ y
  simp

/-- Abstract endpoint-domination compiler.  A bound for the actual product
of the two outer boxes may be transported through the common `4^D` scale to
an integer reserve.  This is the only place where the rational endpoint
comparison is converted back to the cleared integer ledger. -/
theorem boxProductClearedTotal_le_reserve_of_endpoint
    (N leftChannel rightChannel : Nat)
    (hparity : leftChannel % 2 = rightChannel % 2)
    (endpointBound : Q') (reserve : Int)
    (hbound : boxSum halfW N leftChannel * boxSum halfW N rightChannel ≤
      endpointBound)
    (hreserve :
      (Q'.ofNat (4 ^ boxBernsteinDegree N) * endpointBound).eqv
        (Q'.ofInt reserve)) :
    boxProductClearedTotal N leftChannel rightChannel ≤ reserve := by
  let scale := Q'.ofNat (4 ^ boxBernsteinDegree N)
  have hscale0 : (0 : Q') ≤ scale := by
    unfold scale
    rw [Q'.zero_le_iff_num_nonneg]
    exact Int.natCast_nonneg _
  have hscaled :
      scale * (boxSum halfW N leftChannel * boxSum halfW N rightChannel) ≤
        scale * endpointBound :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hbound hscale0
  have htotal :
      Q'.ofInt (boxProductClearedTotal N leftChannel rightChannel) ≤
        Q'.ofInt reserve :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (boxProductClearedTotal_endpoint N leftChannel rightChannel hparity))
      (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hreserve))
  exact (ofInt_le_iff_local _ _).mp htotal

#print axioms YMGap.Continuum.FusionBoxFirstShellReserve.fusionCasimir_even_eq_min
#print axioms YMGap.Continuum.FusionBoxFirstShellReserve.fusionCasimir_odd_eq_min
#print axioms YMGap.Continuum.FusionBoxFirstShellReserve.boxClearedPowerPrefix_eq_positive_sub_negative
#print axioms YMGap.Continuum.FusionBoxFirstShellReserve.boxNegativeClearedPrefix_le_total
#print axioms YMGap.Continuum.FusionBoxFirstShellReserve.boxClearedPowerPrefix_nonnegative_of_total_domination
#print axioms YMGap.Continuum.FusionBoxFirstShellReserve.boxProductClearedCell_endpoint
#print axioms YMGap.Continuum.FusionBoxFirstShellReserve.boxProductClearedTotal_endpoint
#print axioms YMGap.Continuum.FusionBoxFirstShellReserve.boxProductClearedTotal_le_reserve_of_endpoint

end YMGap.Continuum.FusionBoxFirstShellReserve
