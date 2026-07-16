/-
# Finite-product transport for the growing Z4 character cutoff

The local character tail in `Z4GrowingCutoffVolumeTail` retains one dyadic
power per plaquette.  This file supplies the abstract finite-product estimate
that consumes that reserve.  It is deliberately independent of the concrete
graph enumeration: once the finite-box weight has been rewritten as a product
of nonnegative local factors bounded by two, a one-sided local truncation error
is amplified by at most one factor two per plaquette.
-/

import YMGap.Constructive.CornerBound
import YMGap.Continuum.Z4GrowingCutoffVolumeTail

namespace YMGap.Continuum.Z4FiniteProductTailTransport

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4GrowingCutoffVolumeTail

local infix:50 " ≈ " => Q'.eqv

/-- Bare finite product of the first `n` local weights. -/
def finiteWeightProduct (f : Nat → Q') : Nat → Q'
  | 0 => 1
  | n + 1 => finiteWeightProduct f n * f n

@[simp] theorem finiteWeightProduct_zero (f : Nat → Q') :
    finiteWeightProduct f 0 = 1 := rfl

@[simp] theorem finiteWeightProduct_succ (f : Nat → Q') (n : Nat) :
    finiteWeightProduct f (n + 1) = finiteWeightProduct f n * f n := rfl

theorem finiteWeightProduct_nonneg {f : Nat → Q'}
    (hf0 : ∀ i, (0 : Q') ≤ f i) :
    ∀ n, (0 : Q') ≤ finiteWeightProduct f n := by
  intro n
  induction n with
  | zero =>
      rw [finiteWeightProduct_zero]
      decide
  | succ n ih =>
      rw [finiteWeightProduct_succ]
      exact Q'.mul_nonneg _ _ ih (hf0 n)

/-- A product of `n` nonnegative factors, each at most two, is at most `2^n`. -/
theorem finiteWeightProduct_le_twoPow {f : Nat → Q'}
    (hf0 : ∀ i, (0 : Q') ≤ f i) (hf2 : ∀ i, f i ≤ Q'.ofNat 2) :
    ∀ n, finiteWeightProduct f n ≤ Q'.ofNat (2 ^ n) := by
  intro n
  induction n with
  | zero =>
      rw [finiteWeightProduct_zero]
      exact Q'.le_of_eqv (by decide)
  | succ n ih =>
      rw [finiteWeightProduct_succ]
      have hmul : finiteWeightProduct f n * f n ≤
          Q'.ofNat (2 ^ n) * Q'.ofNat 2 :=
        Q'.mul_le_mul_of_nonneg ih (hf2 n) (ExpNeg.ofNat_nonneg' _) (hf0 n)
      refine Q'.le_trans' _ _ _ hmul ?_
      have hpow : 2 ^ (n + 1) = 2 ^ n * 2 := by rw [Nat.pow_succ]
      rw [hpow]
      exact Q'.le_of_eqv (HeatKernelRGStep.ofNat_mul_eqv (2 ^ n) 2)

theorem finiteWeightProduct_mono {f g : Nat → Q'}
    (hf0 : ∀ i, (0 : Q') ≤ f i)
    (hg0 : ∀ i, (0 : Q') ≤ g i)
    (hfg : ∀ i, f i ≤ g i) :
    ∀ n, finiteWeightProduct f n ≤ finiteWeightProduct g n := by
  intro n
  induction n with
  | zero => exact Q'.le_refl' 1
  | succ n ih =>
      rw [finiteWeightProduct_succ, finiteWeightProduct_succ]
      exact Q'.mul_le_mul_of_nonneg ih (hfg n)
        (finiteWeightProduct_nonneg hg0 n) (hf0 n)

private theorem finSum_nonnegative (f : Nat → Q')
    (hf : ∀ i, (0 : Q') ≤ f i) :
    ∀ n, (0 : Q') ≤ finSum f n
  | 0 => by
      rw [finSum_zero]
      decide
  | n + 1 => Q'.zero_le_add _ _ (finSum_nonnegative f hf n) (hf n)

/-! ## The concrete local heat-kernel envelope -/

/-- Vacuum plus a finite window of all excited character-supremum charges. -/
def localCharacterSupEnvelope (depth : Nat) : Q' :=
  (1 : Q') + omittedCharacterSupWindow 0 depth

theorem localCharacterSupEnvelope_nonneg (depth : Nat) :
    (0 : Q') ≤ localCharacterSupEnvelope depth := by
  unfold localCharacterSupEnvelope omittedCharacterSupWindow tailWindow
  exact Q'.zero_le_add _ _ (by decide)
    (finSum_nonnegative (fun offset => tailTerm coupling 2 (1 + offset))
      (fun offset => tailTerm_nonneg (by decide) 2 (1 + offset)) depth)

/-- The complete finite SU(2) heat-kernel character envelope is uniformly at
most two.  In fact the proof obtains the sharper `3/2`; the integral dyadic
bound is retained because it is exactly what product transport consumes. -/
theorem localCharacterSupEnvelope_le_two (depth : Nat) :
    localCharacterSupEnvelope depth ≤ Q'.ofNat 2 := by
  have htail := omittedCharacterSupWindow_le_two_head 0 depth
  have hhead : Q'.ofNat 2 * tailTerm coupling 2 1 ≤ (1 : Q') := by
    decide
  have hexcited : omittedCharacterSupWindow 0 depth ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ htail hhead
  unfold localCharacterSupEnvelope
  refine Q'.le_trans' _ ((1 : Q') + 1) _
    (Q'.add_le_add_left 1 _ _ hexcited) ?_
  exact Q'.le_of_eqv (by decide)

/-- A product of concrete local heat-kernel character envelopes over `P`
plaquettes is bounded by the dyadic factor used in the cutoff budget. -/
theorem localCharacterSupEnvelope_product_le_twoPow (P depth : Nat) :
    finiteWeightProduct (fun _ => localCharacterSupEnvelope depth) P ≤
      Q'.ofNat (2 ^ P) :=
  finiteWeightProduct_le_twoPow
    (fun _ => localCharacterSupEnvelope_nonneg depth)
    (fun _ => localCharacterSupEnvelope_le_two depth) P

/-- Splitting a longer local character window at cutoff `K` gives the retained
window plus exactly the omitted character-supremum window. -/
theorem localCharacterSupEnvelope_split (K depth : Nat) :
    localCharacterSupEnvelope (K + depth) ≈
      localCharacterSupEnvelope K + omittedCharacterSupWindow K depth := by
  let f : Nat → Q' := fun offset => tailTerm coupling 2 (1 + offset)
  have hsplit := YMGap.Constructive.finSum_split f K depth
  have hsplit' : finSum f (K + depth) ≈
      finSum f K + omittedCharacterSupWindow K depth := by
    unfold omittedCharacterSupWindow tailWindow
    simpa only [f, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsplit
  unfold localCharacterSupEnvelope omittedCharacterSupWindow tailWindow
  dsimp only [f] at hsplit'
  refine Q'.eqv_trans _
    ((1 : Q') +
      (finSum (fun offset => tailTerm coupling 2 (1 + offset)) K +
        finSum (fun offset => tailTerm coupling 2 (K + 1 + offset)) depth)) _
    (Q'.add_eqv_congr_left _ _ _ hsplit') ?_
  exact Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)

theorem localCharacterSupEnvelope_le_extension (K depth : Nat) :
    localCharacterSupEnvelope K ≤
      localCharacterSupEnvelope (K + depth) := by
  have htail0 : (0 : Q') ≤ omittedCharacterSupWindow K depth := by
    unfold omittedCharacterSupWindow tailWindow
    exact finSum_nonnegative _ (fun offset =>
      tailTerm_nonneg (by decide) 2 (K + 1 + offset)) depth
  have hadd : localCharacterSupEnvelope K ≤
      localCharacterSupEnvelope K + omittedCharacterSupWindow K depth :=
    Q'.add_le_self_of_nonneg _ _ htail0
  exact Q'.le_trans' _ _ _ hadd
    (Q'.ge_of_eqv (localCharacterSupEnvelope_split K depth))

private theorem finSum_const_eqv (a : Q') : ∀ N : Nat,
    finSum (fun _ => a) N ≈ Q'.ofNat N * a
  | 0 => by
      refine Q'.eqv_trans _ ((0 : Q') * a) _ ?_ ?_
      · exact Q'.eqv_symm (Q'.zero_mul_eqv a)
      · exact Q'.mul_eqv_congr_right _ _ _ Q'.ofNat_zero_eqv
  | N + 1 => by
      have ih := finSum_const_eqv a N
      refine Q'.eqv_trans _ (Q'.ofNat N * a + a) _
        (Q'.add_eqv_congr_right _ _ a ih) ?_
      refine Q'.eqv_trans _ (Q'.ofNat N * a + 1 * a) _
        (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.one_mul_eqv a))) ?_
      refine Q'.eqv_trans _ ((Q'.ofNat N + 1) * a) _
        (Q'.eqv_symm (Q'.add_mul_eqv _ _ _)) ?_
      exact Q'.mul_eqv_congr_right _ _ a
        (Q'.eqv_symm (Q'.ofNat_add_eqv N 1))

private theorem mul_last_swap (a b c : Q') :
    (a * b) * c ≈ (a * c) * b := by
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  ac_rfl

private theorem add_three_rearrange (a b c : Q') :
    (a + b) + c ≈ a + (c + b) := by
  refine Q'.eqv_trans _ (a + (b + c)) _
    (Q'.add_assoc_eqv a b c) ?_
  exact Q'.add_eqv_congr_left a _ _ (Q'.add_comm_eqv b c)

/-- One-sided finite-product perturbation.  If `a i ≤ b i + err i`, all
quantities are nonnegative, and both local weight families are bounded by two,
then the accumulated error is at most `2^n` times the sum of local errors.
The coefficient is intentionally one factor two looser than the sharp
telescoping constant; it matches the reserve already proved for the growing
cutoff and avoids division or predecessor case splits. -/
theorem finiteWeightProduct_le_add_dyadic_error
    {a b err : Nat → Q'}
    (ha0 : ∀ i, (0 : Q') ≤ a i)
    (hb0 : ∀ i, (0 : Q') ≤ b i)
    (he0 : ∀ i, (0 : Q') ≤ err i)
    (ha2 : ∀ i, a i ≤ Q'.ofNat 2)
    (hb2 : ∀ i, b i ≤ Q'.ofNat 2)
    (hab : ∀ i, a i ≤ b i + err i) :
    ∀ n, finiteWeightProduct a n ≤
      finiteWeightProduct b n +
        Q'.ofNat (2 ^ n) * finSum err n := by
  intro n
  induction n with
  | zero =>
      rw [finiteWeightProduct_zero, finiteWeightProduct_zero]
      rw [finSum_zero]
      exact Q'.le_of_eqv (by decide)
  | succ n ih =>
      let A := finiteWeightProduct a n
      let B := finiteWeightProduct b n
      let E := finSum err n
      let C := Q'.ofNat (2 ^ n)
      let C' := Q'.ofNat (2 ^ (n + 1))
      have hA0 : (0 : Q') ≤ A := finiteWeightProduct_nonneg ha0 n
      have hB0 : (0 : Q') ≤ B := finiteWeightProduct_nonneg hb0 n
      have hE0 : (0 : Q') ≤ E := finSum_nonnegative err he0 n
      have hC0 : (0 : Q') ≤ C := ExpNeg.ofNat_nonneg' _
      have hCE0 : (0 : Q') ≤ C * E := Q'.mul_nonneg _ _ hC0 hE0
      have hBpow : B ≤ C := finiteWeightProduct_le_twoPow hb0 hb2 n
      have hstep0 : A * a n ≤ (B + C * E) * a n :=
        Q'.mul_le_mul_of_nonneg_right _ _ _ ih (ha0 n)
      have hexpand : (B + C * E) * a n ≈
          B * a n + (C * E) * a n :=
        QPoly.q_add_mul B (C * E) (a n)
      have hBa : B * a n ≤ B * b n + C * err n := by
        have hlocal : B * a n ≤ B * (b n + err n) :=
          Q'.mul_le_mul_of_nonneg_left _ _ _ (hab n) hB0
        have hdist : B * (b n + err n) ≈ B * b n + B * err n :=
          Q'.mul_add_eqv B (b n) (err n)
        have herror : B * err n ≤ C * err n :=
          Q'.mul_le_mul_of_nonneg_right _ _ _ hBpow (he0 n)
        refine Q'.le_trans' _ _ _ hlocal ?_
        refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hdist) ?_
        exact Q'.add_le_add_left (B * b n) _ _ herror
      have hCE : (C * E) * a n ≤ C' * E := by
        have htwo : (C * E) * a n ≤ (C * E) * Q'.ofNat 2 :=
          Q'.mul_le_mul_of_nonneg_left _ _ _ (ha2 n) hCE0
        have hrearr : (C * E) * Q'.ofNat 2 ≈
            (C * Q'.ofNat 2) * E := mul_last_swap _ _ _
        have hpow : 2 ^ (n + 1) = 2 ^ n * 2 := by rw [Nat.pow_succ]
        have hcoeff : C * Q'.ofNat 2 ≈ C' := by
          dsimp only [C, C']
          rw [hpow]
          exact HeatKernelRGStep.ofNat_mul_eqv (2 ^ n) 2
        refine Q'.le_trans' _ _ _ htwo ?_
        refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hrearr) ?_
        exact Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _ hcoeff)
      have hsum : B * a n + (C * E) * a n ≤
          (B * b n + C * err n) + C' * E :=
        Q'.add_le_add hBa hCE
      have hCC' : C ≤ C' := by
        dsimp only [C, C']
        exact Q'.ofNat_le_ofNat (by
          rw [Nat.pow_succ]
          omega)
      have hsmall : C * err n ≤ C' * err n :=
        Q'.mul_le_mul_of_nonneg_right _ _ _ hCC' (he0 n)
      have hgroup : (B * b n + C * err n) + C' * E ≤
          B * b n + C' * (E + err n) := by
        refine Q'.le_trans' _
          (B * b n + (C' * E + C * err n)) _ ?_ ?_
        · exact Q'.le_of_eqv (add_three_rearrange _ _ _)
        have hi : C' * E + C * err n ≤ C' * E + C' * err n :=
          Q'.add_le_add_left (C' * E) _ _ hsmall
        refine Q'.le_trans' _ _ _
          (Q'.add_le_add_left (B * b n) _ _ hi) ?_
        exact Q'.le_of_eqv
          (Q'.add_eqv_congr_left _ _ _
            (Q'.eqv_symm (Q'.mul_add_eqv C' E (err n))))
      rw [finiteWeightProduct_succ]
      change A * a n ≤ B * b n + C' * (E + err n)
      refine Q'.le_trans' _ _ _ hstep0 ?_
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hexpand) ?_
      exact Q'.le_trans' _ _ _ hsum hgroup

/-- The abstract product amplification has exactly the size already absorbed
by the growing dimension-weighted character tail. -/
theorem growingProductErrorBudget (stage depth : Nat) :
    Q'.ofNat (2 ^ plaquetteEdgeCount (stage + 2)) *
        growingCharacterSupVolumeTail stage depth ≤
      Q'.ofNat 2 * (HalfPow.half ^ stage) :=
  dyadicAmplifiedGrowingCharacterSupVolumeTail_le_two_halfPow stage depth

/-- Explicit depth-uniform convergence modulus after whole-product dyadic
amplification. -/
theorem growingProductErrorBudget_modulus (ε : Q') (hε : (0 : Q') < ε) :
    ∀ stage, ε.den + 1 ≤ stage → ∀ depth,
      Q'.ofNat (2 ^ plaquetteEdgeCount (stage + 2)) *
          growingCharacterSupVolumeTail stage depth ≤ ε := by
  intro stage hstage depth
  have hbudget := growingProductErrorBudget stage depth
  have hpow : HalfPow.half ^ stage ≤
      HalfPow.half ^ (ε.den + 1) := halfPow_antitone hstage
  have htwo : Q'.ofNat 2 * (HalfPow.half ^ stage) ≤
      Q'.ofNat 2 * (HalfPow.half ^ (ε.den + 1)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hpow (ExpNeg.ofNat_nonneg' _)
  refine Q'.le_trans' _ _ _ hbudget ?_
  refine Q'.le_trans' _ _ _ htwo ?_
  refine Q'.le_trans' _ (HalfPow.half ^ ε.den) _ ?_ ?_
  · exact Q'.le_of_eqv (two_halfPow_succ_eqv ε.den)
  · exact HalfPow.pow_half_le ε hε

/-- Concrete finite-plaquette cutoff transport for the character-supremum
envelope.  Extending every plaquette window by an arbitrary finite `depth`
changes the whole product by at most `2*(1/2)^stage`, uniformly in `depth`. -/
theorem growingFinitePlaquetteEnvelope_extension_le
    (stage depth : Nat) :
    let P := plaquetteEdgeCount (stage + 2)
    let K := volumeAbsorbingCutoff stage
    finiteWeightProduct
        (fun _ => localCharacterSupEnvelope (K + depth)) P ≤
      finiteWeightProduct (fun _ => localCharacterSupEnvelope K) P +
        Q'.ofNat 2 * (HalfPow.half ^ stage) := by
  let P := plaquetteEdgeCount (stage + 2)
  let K := volumeAbsorbingCutoff stage
  let tail := omittedCharacterSupWindow K depth
  have htail0 : (0 : Q') ≤ tail := by
    dsimp only [tail, omittedCharacterSupWindow, tailWindow]
    exact finSum_nonnegative _ (fun offset =>
      tailTerm_nonneg (by decide) 2 (K + 1 + offset)) depth
  have hpert := finiteWeightProduct_le_add_dyadic_error
    (a := fun _ => localCharacterSupEnvelope (K + depth))
    (b := fun _ => localCharacterSupEnvelope K)
    (err := fun _ => tail)
    (fun _ => localCharacterSupEnvelope_nonneg (K + depth))
    (fun _ => localCharacterSupEnvelope_nonneg K)
    (fun _ => htail0)
    (fun _ => localCharacterSupEnvelope_le_two (K + depth))
    (fun _ => localCharacterSupEnvelope_le_two K)
    (fun _ => Q'.le_of_eqv (localCharacterSupEnvelope_split K depth)) P
  have hsum : finSum (fun _ => tail) P ≈
      growingCharacterSupVolumeTail stage depth := by
    refine Q'.eqv_trans _ (Q'.ofNat P * tail) _
      (finSum_const_eqv tail P) ?_
    dsimp only [P, K, tail, growingCharacterSupVolumeTail]
    exact Q'.eqv_refl _
  have herr : Q'.ofNat (2 ^ P) * finSum (fun _ => tail) P ≤
      Q'.ofNat 2 * (HalfPow.half ^ stage) := by
    refine Q'.le_trans' _
      (Q'.ofNat (2 ^ P) * growingCharacterSupVolumeTail stage depth) _ ?_ ?_
    · exact Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ hsum)
    · dsimp only [P]
      exact growingProductErrorBudget stage depth
  dsimp only at hpert ⊢
  exact Q'.le_trans' _ _ _ hpert
    (Q'.add_le_add_left
      (finiteWeightProduct (fun _ => localCharacterSupEnvelope K) P) _ _ herr)

/-- Explicit modulus for the concrete whole-plaquette envelope extension,
uniform in the number of added character modes. -/
theorem growingFinitePlaquetteEnvelope_extension_modulus
    (ε : Q') (hε : (0 : Q') < ε) :
    ∀ stage, ε.den + 1 ≤ stage → ∀ depth,
      let P := plaquetteEdgeCount (stage + 2)
      let K := volumeAbsorbingCutoff stage
      finiteWeightProduct
          (fun _ => localCharacterSupEnvelope (K + depth)) P ≤
        finiteWeightProduct (fun _ => localCharacterSupEnvelope K) P + ε := by
  intro stage hstage depth
  let P := plaquetteEdgeCount (stage + 2)
  let K := volumeAbsorbingCutoff stage
  have hext := growingFinitePlaquetteEnvelope_extension_le stage depth
  have hpow : HalfPow.half ^ stage ≤
      HalfPow.half ^ (ε.den + 1) := halfPow_antitone hstage
  have htwo : Q'.ofNat 2 * (HalfPow.half ^ stage) ≤ ε := by
    refine Q'.le_trans' _
      (Q'.ofNat 2 * (HalfPow.half ^ (ε.den + 1))) _ ?_ ?_
    · exact Q'.mul_le_mul_of_nonneg_left _ _ _ hpow (ExpNeg.ofNat_nonneg' _)
    refine Q'.le_trans' _ (HalfPow.half ^ ε.den) _ ?_ ?_
    · exact Q'.le_of_eqv (two_halfPow_succ_eqv ε.den)
    · exact HalfPow.pow_half_le ε hε
  dsimp only [P, K] at hext ⊢
  exact Q'.le_trans' _ _ _ hext
    (Q'.add_le_add_left _ _ _ htwo)

/-- Two-sided constructive bracket for the whole plaquette character
envelope: the growing-cutoff product is monotone below every finite extension,
while the extension lies within `ε` above it. -/
theorem growingFinitePlaquetteEnvelope_extension_bracket
    (ε : Q') (hε : (0 : Q') < ε)
    (stage : Nat) (hstage : ε.den + 1 ≤ stage) (depth : Nat) :
    let P := plaquetteEdgeCount (stage + 2)
    let K := volumeAbsorbingCutoff stage
    finiteWeightProduct (fun _ => localCharacterSupEnvelope K) P ≤
        finiteWeightProduct
          (fun _ => localCharacterSupEnvelope (K + depth)) P ∧
      finiteWeightProduct
          (fun _ => localCharacterSupEnvelope (K + depth)) P ≤
        finiteWeightProduct (fun _ => localCharacterSupEnvelope K) P + ε := by
  let P := plaquetteEdgeCount (stage + 2)
  let K := volumeAbsorbingCutoff stage
  constructor
  · exact finiteWeightProduct_mono
      (fun _ => localCharacterSupEnvelope_nonneg K)
      (fun _ => localCharacterSupEnvelope_nonneg (K + depth))
      (fun _ => localCharacterSupEnvelope_le_extension K depth) P
  · exact growingFinitePlaquetteEnvelope_extension_modulus
      ε hε stage hstage depth

#print axioms finiteWeightProduct_nonneg
#print axioms finiteWeightProduct_le_twoPow
#print axioms finiteWeightProduct_mono
#print axioms localCharacterSupEnvelope_nonneg
#print axioms localCharacterSupEnvelope_le_two
#print axioms localCharacterSupEnvelope_product_le_twoPow
#print axioms localCharacterSupEnvelope_split
#print axioms localCharacterSupEnvelope_le_extension
#print axioms finiteWeightProduct_le_add_dyadic_error
#print axioms growingProductErrorBudget
#print axioms growingProductErrorBudget_modulus
#print axioms growingFinitePlaquetteEnvelope_extension_le
#print axioms growingFinitePlaquetteEnvelope_extension_modulus
#print axioms growingFinitePlaquetteEnvelope_extension_bracket

end YMGap.Continuum.Z4FiniteProductTailTransport
