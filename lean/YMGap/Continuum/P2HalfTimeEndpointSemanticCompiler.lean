/-
Track 11.7-fusion / R4za -- semantic endpoint-expansion compiler.

The reflected endpoint certificates through depth ten normalize one closed
polynomial at a time.  This module is the proof-producing replacement: it
expands an endpoint parity triangle at arbitrary depth into successive
increment monomials, performs finite Fubini independently of the depth,
proves the exact threshold multiplicity formula, and lifts its Nat inequality
to the table-free adjacent endpoint ratio at every positive depth.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2HalfTimeEndpointSupportCompiler
import YMGap.Continuum.KernelCB2

namespace YMGap.Continuum.P2HalfTimeEndpointSemanticCompiler

set_option maxRecDepth 100000
set_option maxHeartbeats 360000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.FusionCoreStepRoundB
open YMGap.Continuum.KernelCB2
open YMGap.Continuum.P2HalfTimeEndpointRatioCompiler
open YMGap.Continuum.P2HalfTimeEndpointRatioCertificateCompiler
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Public semantics for the reflected prefix language -/

/-- Evaluation commutes with the reflected right-nested finite sum. -/
theorem eval_polyFsum_eq_fsum
    (rho : Nat -> Q') (f : Nat -> PolyExpr) : forall n,
    eval rho (polyFsum f n) = fsum (fun i => eval rho (f i)) n
  | 0 => rfl
  | n + 1 => by
      change eval rho (polyFsum f n) + eval rho (f n) =
        fsum (fun i => eval rho (f i)) n + eval rho (f n)
      rw [eval_polyFsum_eq_fsum rho f n]

/-- A reflected endpoint prefix is the ordinary finite sum of increments. -/
theorem eval_endpointPrefixExpr_eq_fsum (rho : Nat -> Q') (i : Nat) :
    eval rho (endpointPrefixExpr i) = fsum rho (i + 1) := by
  unfold endpointPrefixExpr
  rw [eval_polyFsum_eq_fsum]
  rfl

/-! ## 2. Variable-bound increment expansion -/

/-- The raw four-index expansion before all increment bounds are enlarged to
the common endpoint box. -/
def endpointVariableExpansion (rho : Nat -> Q') (m : Nat) : Q' :=
  fsum (fun i =>
    fsum (fun j =>
      if endpointPairActive m i j then
        fsum (fun a => fsum (fun b => rho a * rho b) (j + 1)) (i + 1)
      else 0) (m + 1)) (m + 1)

/-- Every reflected endpoint triangle expands into increment monomials at
arbitrary depth.  This is pure finite distributivity; no normalization
certificate and no fixed value of `m` occurs. -/
theorem endpointTriangleExpr_eq_variableExpansion
    (rho : Nat -> Q') (m : Nat) :
    eval rho (endpointTriangleExpr m) ≈ endpointVariableExpansion rho m := by
  unfold endpointTriangleExpr endpointVariableExpansion
  rw [eval_polyFsum_eq_fsum]
  apply fsum_eqv_congr
  intro i
  rw [eval_polyFsum_eq_fsum]
  apply fsum_eqv_congr
  intro j
  by_cases hactive : endpointPairActive m i j = true
  · simp only [hactive, if_true, eval]
    rw [eval_endpointPrefixExpr_eq_fsum,
      eval_endpointPrefixExpr_eq_fsum]
    exact fsum_mul_fsum rho rho (i + 1) (j + 1)
  · have hfalse : endpointPairActive m i j = false :=
      Bool.eq_false_iff.mpr hactive
    simp only [hfalse, Bool.false_eq_true, if_false, eval]
    exact Q'.eqv_refl 0

/-! ## 3. Common-bound threshold expansion -/

/-- A monomial survives precisely when the endpoint cell is active and both
increment indices lie below its two prefix coordinates. -/
def endpointThresholdMonomial
    (rho : Nat -> Q') (m i j a b : Nat) : Q' :=
  if endpointPairActive m i j && decide (a <= i) && decide (b <= j) then
    rho a * rho b
  else 0

/-- The common-bound four-index expansion.  Its order is still
`cell i,j` then `increment a,b`; the next section swaps those pairs. -/
def endpointIndexedExpansion (rho : Nat -> Q') (m : Nat) : Q' :=
  fsum (fun i =>
    fsum (fun j =>
      fsum (fun a =>
        fsum (fun b => endpointThresholdMonomial rho m i j a b) (m + 1))
        (m + 1)) (m + 1)) (m + 1)

private theorem fsum_zero_extension {f : Nat -> Q'} {n M : Nat}
    (hnM : n <= M) (hz : forall i, n <= i -> f i ≈ 0) :
    fsum f M ≈ fsum f n := by
  induction hnM with
  | refl => exact Q'.eqv_refl _
  | @step M hnM ih =>
      rw [fsum_succ]
      exact Q'.eqv_trans _ (fsum f n + 0) _
        (Q'.add_eqv_congr' ih (hz M hnM))
        (Q'.eqv_of_eq (Q'.add_zero' _))

private theorem active_prefix_product_to_common_bound
    (rho : Nat -> Q') (m i j : Nat) (hi : i <= m) (hj : j <= m) :
    (if endpointPairActive m i j then
        fsum (fun a => fsum (fun b => rho a * rho b) (j + 1)) (i + 1)
      else 0) ≈
      fsum (fun a =>
        fsum (fun b => endpointThresholdMonomial rho m i j a b) (m + 1))
        (m + 1) := by
  by_cases hactive : endpointPairActive m i j = true
  · simp only [hactive, if_true]
    have houter :
        fsum (fun a =>
          fsum (fun b => endpointThresholdMonomial rho m i j a b) (m + 1))
          (m + 1) ≈
        fsum (fun a =>
          fsum (fun b => endpointThresholdMonomial rho m i j a b) (m + 1))
          (i + 1) := by
      apply fsum_zero_extension (by omega)
      intro a ha
      have hai : decide (a <= i) = false := by
        simp only [decide_eq_false_iff_not]
        omega
      have hterm : forall b,
          endpointThresholdMonomial rho m i j a b = 0 := by
        intro b
        simp only [endpointThresholdMonomial, hactive, Bool.true_and, hai,
          Bool.false_and, Bool.false_eq_true, if_false]
      rw [show (fun b => endpointThresholdMonomial rho m i j a b) =
          (fun _ => (0 : Q')) from funext hterm, fsum_zero_seq]
      exact Q'.eqv_refl 0
    have hinner :
        fsum (fun a =>
          fsum (fun b => endpointThresholdMonomial rho m i j a b) (m + 1))
          (i + 1) ≈
        fsum (fun a => fsum (fun b => rho a * rho b) (j + 1))
          (i + 1) := by
      apply fsum_eqv_congr_lt
      intro a ha
      have hai : decide (a <= i) = true := by
        simp only [decide_eq_true_eq]
        omega
      have htruncate :
          fsum (fun b => endpointThresholdMonomial rho m i j a b) (m + 1) ≈
          fsum (fun b => endpointThresholdMonomial rho m i j a b) (j + 1) := by
        apply fsum_zero_extension (by omega)
        intro b hb
        have hbj : decide (b <= j) = false := by
          simp only [decide_eq_false_iff_not]
          omega
        simp only [endpointThresholdMonomial, hactive, Bool.true_and, hai, hbj]
        exact Q'.eqv_refl 0
      refine Q'.eqv_trans _ _ _ htruncate ?_
      apply fsum_eqv_congr_lt
      intro b hb
      have hbj : decide (b <= j) = true := by
        simp only [decide_eq_true_eq]
        omega
      simp only [endpointThresholdMonomial, hactive, Bool.true_and, hai,
        hbj, if_true]
      exact Q'.eqv_refl _
    exact Q'.eqv_symm (Q'.eqv_trans _ _ _ houter hinner)
  · have hfalse : endpointPairActive m i j = false :=
      Bool.eq_false_iff.mpr hactive
    simp only [hfalse, Bool.false_eq_true, if_false]
    have hterm : forall a b,
        endpointThresholdMonomial rho m i j a b = 0 := by
      intro a b
      simp only [endpointThresholdMonomial, hfalse, Bool.false_and,
        Bool.false_eq_true, if_false]
    have hinner : forall a,
        fsum (fun b => endpointThresholdMonomial rho m i j a b) (m + 1) = 0 := by
      intro a
      rw [show (fun b => endpointThresholdMonomial rho m i j a b) =
        (fun _ => (0 : Q')) from funext (hterm a), fsum_zero_seq]
    rw [show (fun a =>
        fsum (fun b => endpointThresholdMonomial rho m i j a b) (m + 1)) =
          (fun _ => (0 : Q')) from funext hinner, fsum_zero_seq]
    exact Q'.eqv_refl 0

/-- The variable prefix bounds can be enlarged uniformly to `m+1`, with
threshold masks recording exactly which increment monomials survive. -/
theorem endpointVariableExpansion_eq_indexedExpansion
    (rho : Nat -> Q') (m : Nat) :
    endpointVariableExpansion rho m ≈ endpointIndexedExpansion rho m := by
  unfold endpointVariableExpansion endpointIndexedExpansion
  apply fsum_eqv_congr_lt
  intro i hi
  apply fsum_eqv_congr_lt
  intro j hj
  exact active_prefix_product_to_common_bound rho m i j (by omega) (by omega)

/-! ## 4. Finite Fubini: cells first equals increments first -/

/-- Generic fourfold finite Fubini permutation
`sum_i sum_j sum_a sum_b = sum_a sum_b sum_i sum_j`. -/
theorem fsum4_swap_pairs (F : Nat -> Nat -> Nat -> Nat -> Q') (n : Nat) :
    fsum (fun i => fsum (fun j => fsum (fun a =>
      fsum (fun b => F i j a b) n) n) n) n ≈
    fsum (fun a => fsum (fun b => fsum (fun i =>
      fsum (fun j => F i j a b) n) n) n) n := by
  have hja :
      fsum (fun i => fsum (fun j => fsum (fun a =>
        fsum (fun b => F i j a b) n) n) n) n ≈
      fsum (fun i => fsum (fun a => fsum (fun j =>
        fsum (fun b => F i j a b) n) n) n) n := by
    apply fsum_eqv_congr
    intro i
    exact fsum_swap (fun j a => fsum (fun b => F i j a b) n) n n
  have hia :
      fsum (fun i => fsum (fun a => fsum (fun j =>
        fsum (fun b => F i j a b) n) n) n) n ≈
      fsum (fun a => fsum (fun i => fsum (fun j =>
        fsum (fun b => F i j a b) n) n) n) n :=
    fsum_swap (fun i a => fsum (fun j =>
      fsum (fun b => F i j a b) n) n) n n
  have hjb :
      fsum (fun a => fsum (fun i => fsum (fun j =>
        fsum (fun b => F i j a b) n) n) n) n ≈
      fsum (fun a => fsum (fun i => fsum (fun b =>
        fsum (fun j => F i j a b) n) n) n) n := by
    apply fsum_eqv_congr
    intro a
    apply fsum_eqv_congr
    intro i
    exact fsum_swap (fun j b => F i j a b) n n
  have hib :
      fsum (fun a => fsum (fun i => fsum (fun b =>
        fsum (fun j => F i j a b) n) n) n) n ≈
      fsum (fun a => fsum (fun b => fsum (fun i =>
        fsum (fun j => F i j a b) n) n) n) n := by
    apply fsum_eqv_congr
    intro a
    exact fsum_swap (fun i b => fsum (fun j => F i j a b) n) n n
  exact Q'.eqv_trans _ _ _ hja
    (Q'.eqv_trans _ _ _ hia (Q'.eqv_trans _ _ _ hjb hib))

/-- Increment-first form of the arbitrary-depth endpoint expansion. -/
def endpointThresholdExpansion (rho : Nat -> Q') (m : Nat) : Q' :=
  fsum (fun a =>
    fsum (fun b =>
      fsum (fun i =>
        fsum (fun j => endpointThresholdMonomial rho m i j a b) (m + 1))
        (m + 1)) (m + 1)) (m + 1)

/-- Full semantic endpoint expansion at arbitrary depth, with increment
indices outermost and active threshold cells innermost. -/
theorem endpointTriangleExpr_eq_thresholdExpansion
    (rho : Nat -> Q') (m : Nat) :
    eval rho (endpointTriangleExpr m) ≈ endpointThresholdExpansion rho m := by
  refine Q'.eqv_trans _ _ _
    (endpointTriangleExpr_eq_variableExpansion rho m) ?_
  refine Q'.eqv_trans _ _ _
    (endpointVariableExpansion_eq_indexedExpansion rho m) ?_
  unfold endpointIndexedExpansion endpointThresholdExpansion
  exact fsum4_swap_pairs (endpointThresholdMonomial rho m) (m + 1)

/-! ## 5. Collecting equal increment monomials -/

/-- Rational `0/1` indicator for an active cell above thresholds `(a,b)`. -/
def endpointThresholdIndicator (m a b i j : Nat) : Q' :=
  if endpointPairActive m i j && decide (a <= i) && decide (b <= j) then
    1
  else 0

/-- Rational multiplicity of active endpoint cells above `(a,b)`. -/
def endpointThresholdMultiplicity (m a b : Nat) : Q' :=
  fsum (fun i =>
    fsum (fun j => endpointThresholdIndicator m a b i j) (m + 1))
    (m + 1)

/-- The collected coefficient expansion.  The next arithmetic compiler lemma
will identify `endpointThresholdMultiplicity m a b` with
`Q'.ofNat (thresholdTriangleCount m a b)`. -/
def endpointCoefficientExpansion (rho : Nat -> Q') (m : Nat) : Q' :=
  fsum (fun a =>
    fsum (fun b =>
      endpointThresholdMultiplicity m a b * (rho a * rho b)) (m + 1))
    (m + 1)

private theorem endpointThresholdMonomial_factor
    (rho : Nat -> Q') (m i j a b : Nat) :
    endpointThresholdMonomial rho m i j a b ≈
      endpointThresholdIndicator m a b i j * (rho a * rho b) := by
  by_cases hactive :
      (endpointPairActive m i j && decide (a <= i) && decide (b <= j)) = true
  · simp only [endpointThresholdMonomial, endpointThresholdIndicator,
      hactive, if_true]
    exact Q'.eqv_symm (Q'.one_mul_eqv _)
  · have hfalse :
        (endpointPairActive m i j && decide (a <= i) && decide (b <= j)) = false :=
      Bool.eq_false_iff.mpr hactive
    simp only [endpointThresholdMonomial, endpointThresholdIndicator,
      hfalse, Bool.false_eq_true, if_false]
    exact Q'.eqv_symm (Q'.zero_mul_eqv _)

private theorem thresholdMonomial_box_factor
    (rho : Nat -> Q') (m a b : Nat) :
    fsum (fun i =>
      fsum (fun j => endpointThresholdMonomial rho m i j a b) (m + 1))
      (m + 1) ≈
    endpointThresholdMultiplicity m a b * (rho a * rho b) := by
  let p := rho a * rho b
  have hterms :
      fsum (fun i =>
        fsum (fun j => endpointThresholdMonomial rho m i j a b) (m + 1))
        (m + 1) ≈
      fsum (fun i =>
        fsum (fun j => endpointThresholdIndicator m a b i j * p) (m + 1))
        (m + 1) := by
    apply fsum_eqv_congr
    intro i
    apply fsum_eqv_congr
    intro j
    exact endpointThresholdMonomial_factor rho m i j a b
  have hinner :
      fsum (fun i =>
        fsum (fun j => endpointThresholdIndicator m a b i j * p) (m + 1))
        (m + 1) ≈
      fsum (fun i =>
        fsum (fun j => endpointThresholdIndicator m a b i j) (m + 1) * p)
        (m + 1) := by
    apply fsum_eqv_congr
    intro i
    exact Q'.eqv_symm
      (fsum_mul_const (fun j => endpointThresholdIndicator m a b i j)
        p (m + 1))
  have houter :
      fsum (fun i =>
        fsum (fun j => endpointThresholdIndicator m a b i j) (m + 1) * p)
        (m + 1) ≈
      endpointThresholdMultiplicity m a b * p := by
    exact Q'.eqv_symm
      (fsum_mul_const
        (fun i => fsum (fun j => endpointThresholdIndicator m a b i j)
          (m + 1)) p (m + 1))
  exact Q'.eqv_trans _ _ _ hterms (Q'.eqv_trans _ _ _ hinner houter)

/-- Arbitrary-depth semantic coefficient expansion.  All finite Fubini and
distributivity are now proved once; only the closed multiplicity formula
remains between this theorem and the all-depth adjacent-ratio theorem. -/
theorem endpointTriangleExpr_eq_coefficientExpansion
    (rho : Nat -> Q') (m : Nat) :
    eval rho (endpointTriangleExpr m) ≈ endpointCoefficientExpansion rho m := by
  refine Q'.eqv_trans _ _ _
    (endpointTriangleExpr_eq_thresholdExpansion rho m) ?_
  unfold endpointThresholdExpansion endpointCoefficientExpansion
  apply fsum_eqv_congr
  intro a
  apply fsum_eqv_congr
  intro b
  exact thresholdMonomial_box_factor rho m a b

/-! ## 6. Proof-producing parity-row counter -/

/-- Front/tail splitting for the computational Nat sum. -/
theorem nsum_split_at (f : Nat -> Nat) (a b : Nat) :
    nsum f (a + b) = nsum f a + nsum (fun r => f (a + r)) b := by
  induction b with
  | zero => simp only [Nat.add_zero, nsum_zero, Nat.add_zero]
  | succ b ih =>
      rw [show a + (b + 1) = (a + b) + 1 by omega,
        nsum_succ, ih, nsum_succ]
      omega

/-- Range-restricted congruence for `nsum`. -/
theorem nsum_congr_lt {f g : Nat -> Nat} : forall R,
    (forall i, i < R -> f i = g i) -> nsum f R = nsum g R
  | 0, _ => rfl
  | R + 1, h => by
      rw [nsum_succ, nsum_succ,
        nsum_congr_lt R (fun i hi => h i (Nat.lt_succ_of_lt hi)),
        h R (Nat.lt_succ_self R)]

/-- Summing the constant one program returns the range length. -/
theorem nsum_one : forall R, nsum (fun _ => 1) R = R
  | 0 => rfl
  | R + 1 => by rw [nsum_succ, nsum_one R]

/-- `Q'.ofNat` transports a computational Nat sum to the rational `fsum`. -/
theorem fsum_ofNat_eqv_nsum (f : Nat -> Nat) : forall R,
    fsum (fun i => Q'.ofNat (f i)) R ≈ Q'.ofNat (nsum f R)
  | 0 => Q'.eqv_refl 0
  | R + 1 => by
      refine Q'.eqv_trans _
        (Q'.ofNat (nsum f R) + Q'.ofNat (f R)) _
        (Q'.add_eqv_congr_right _ _ _ (fsum_ofNat_eqv_nsum f R)) ?_
      exact Q'.eqv_symm (Q'.ofNat_add_eqv (nsum f R) (f R))

/-- Boolean Nat indicator selecting the parity row
`0 <= v <= n`, `v+n` even. -/
def parityRowNatIndicator (n v : Nat) : Nat :=
  if decide (v <= n /\ (v + n) % 2 = 0) then 1 else 0

/-- Executable count of the active entries in one parity row. -/
def parityRowNatCount (n : Nat) : Nat :=
  nsum (parityRowNatIndicator n) (n + 1)

/-- Adding two to the row depth leaves every old parity indicator unchanged. -/
theorem parityRowNatIndicator_add_two_prefix (n v : Nat) (hv : v < n + 1) :
    parityRowNatIndicator (n + 2) v = parityRowNatIndicator n v := by
  unfold parityRowNatIndicator
  have hmod : (v + (n + 2)) % 2 = (v + n) % 2 := by
    have hadd : v + (n + 2) = (v + n) + 2 := by omega
    rw [hadd, Nat.add_mod]
    simp only [Nat.mod_self, Nat.add_zero, Nat.mod_mod]
  have hiff :
      (v <= n + 2 /\ (v + (n + 2)) % 2 = 0) <->
        (v <= n /\ (v + n) % 2 = 0) := by
    constructor
    · rintro ⟨_, hparity⟩
      rw [hmod] at hparity
      exact ⟨by omega, hparity⟩
    · rintro ⟨_, hparity⟩
      rw [hmod]
      exact ⟨by omega, hparity⟩
  have hdec :
      decide (v <= n + 2 /\ (v + (n + 2)) % 2 = 0) =
        decide (v <= n /\ (v + n) % 2 = 0) := by
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using hiff
  rw [hdec]

/-- The two new slots in row `n+2` contribute exactly one active cell. -/
theorem parityRowNatIndicator_add_two_tail (n : Nat) :
    nsum (fun r => parityRowNatIndicator (n + 2) (n + 1 + r)) 2 = 1 := by
  simp only [nsum_succ, nsum_zero, parityRowNatIndicator]
  have h0 : decide
      (n + 1 <= n + 2 /\ (n + 1 + (n + 2)) % 2 = 0) = false := by
    apply decide_eq_false_iff_not.mpr
    rintro ⟨_, hparity⟩
    have hmod : (n + 1 + (n + 2)) % 2 = 1 := by
      have hadd : n + 1 + (n + 2) = 2 * n + 3 := by omega
      rw [hadd, Nat.add_mod, Nat.mul_mod]
      simp
    exact Nat.one_ne_zero (hmod.symm.trans hparity)
  have h1 : decide
      (n + 1 + 1 <= n + 2 /\ (n + 1 + 1 + (n + 2)) % 2 = 0) = true := by
    apply decide_eq_true_eq.mpr
    constructor
    · omega
    · have hadd : n + 1 + 1 + (n + 2) = 2 * (n + 2) := by omega
      rw [hadd, Nat.mul_mod]
      simp
  simp only [h0, h1, Bool.false_eq_true, if_false, if_true]

/-- Proof-about-computation recurrence: every two-row extension adds one. -/
theorem parityRowNatCount_add_two (n : Nat) :
    parityRowNatCount (n + 2) = parityRowNatCount n + 1 := by
  have hprefix :
      nsum (parityRowNatIndicator (n + 2)) (n + 1) =
        nsum (parityRowNatIndicator n) (n + 1) := by
    apply nsum_congr_lt
    intro v hv
    exact parityRowNatIndicator_add_two_prefix n v hv
  unfold parityRowNatCount
  rw [show n + 2 + 1 = (n + 1) + 2 by omega,
    nsum_split_at, hprefix, parityRowNatIndicator_add_two_tail]

theorem parityRowNatCount_even (q : Nat) :
    parityRowNatCount (2 * q) = q + 1 := by
  induction q with
  | zero => decide
  | succ q ih =>
      rw [show 2 * (q + 1) = 2 * q + 2 by omega,
        parityRowNatCount_add_two, ih]

theorem parityRowNatCount_odd (q : Nat) :
    parityRowNatCount (2 * q + 1) = q + 1 := by
  induction q with
  | zero => decide
  | succ q ih =>
      rw [show 2 * (q + 1) + 1 = (2 * q + 1) + 2 by omega,
        parityRowNatCount_add_two, ih]

/-- Closed proof-about-computation formula for every parity row. -/
theorem parityRowNatCount_eq (n : Nat) :
    parityRowNatCount n = n / 2 + 1 := by
  have hpar : n % 2 = 0 \/ n % 2 = 1 := by omega
  cases hpar with
  | inl heven =>
      let q := n / 2
      have hn : n = 2 * q := by unfold q; omega
      rw [hn, parityRowNatCount_even]
      omega
  | inr hodd =>
      let q := n / 2
      have hn : n = 2 * q + 1 := by unfold q; omega
      rw [hn, parityRowNatCount_odd]
      omega

/-! ## 7. Proof-producing parity-triangle counter -/

/-- Zero extension for a computational Nat sum. -/
theorem nsum_zero_extension {f : Nat -> Nat} {n M : Nat}
    (hnM : n <= M) (hz : forall i, n <= i -> f i = 0) :
    nsum f M = nsum f n := by
  induction hnM with
  | refl => rfl
  | @step M hnM ih =>
      rw [nsum_succ, hz M hnM, Nat.add_zero, ih]

/-- Pointwise addition commutes with the computational Nat sum. -/
theorem nsum_add (f g : Nat -> Nat) : forall R,
    nsum (fun i => f i + g i) R = nsum f R + nsum g R
  | 0 => rfl
  | R + 1 => by
      rw [nsum_succ, nsum_succ, nsum_succ, nsum_add f g R]
      omega

/-- Boolean Nat indicator for the full parity triangle of depth `n`. -/
def parityTriangleNatIndicator (n u v : Nat) : Nat :=
  if decide (u + v <= n /\ (u + v + n) % 2 = 0) then 1 else 0

/-- Executable count of all ordered cells in the parity triangle. -/
def parityTriangleNatCount (n : Nat) : Nat :=
  nsum (fun u =>
    nsum (fun v => parityTriangleNatIndicator n u v) (n + 1)) (n + 1)

/-- After fixing the first coordinate, a parity-triangle indicator is the
one-dimensional parity-row indicator at the remaining depth. -/
theorem parityTriangleNatIndicator_eq_row
    (n u v : Nat) (hu : u <= n) :
    parityTriangleNatIndicator n u v =
      parityRowNatIndicator (n - u) v := by
  unfold parityTriangleNatIndicator parityRowNatIndicator
  have hmod : (u + v + n) % 2 = (v + (n - u)) % 2 := by
    have hadd : u + v + n = (v + (n - u)) + 2 * u := by omega
    rw [hadd, Nat.add_mod, Nat.mul_mod]
    simp
  have hiff :
      (u + v <= n /\ (u + v + n) % 2 = 0) <->
        (v <= n - u /\ (v + (n - u)) % 2 = 0) := by
    constructor
    · rintro ⟨hbound, hparity⟩
      rw [hmod] at hparity
      exact ⟨by omega, hparity⟩
    · rintro ⟨hbound, hparity⟩
      rw [hmod]
      exact ⟨by omega, hparity⟩
  have hdec :
      decide (u + v <= n /\ (u + v + n) % 2 = 0) =
        decide (v <= n - u /\ (v + (n - u)) % 2 = 0) := by
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using hiff
  rw [hdec]

/-- Each horizontal slice of the triangle is exactly one parity row. -/
theorem parityTriangleNatRowCount (n u : Nat) (hu : u <= n) :
    nsum (fun v => parityTriangleNatIndicator n u v) (n + 1) =
      parityRowNatCount (n - u) := by
  have hshort : n - u + 1 <= n + 1 := by omega
  have htruncate :
      nsum (fun v => parityTriangleNatIndicator n u v) (n + 1) =
        nsum (fun v => parityTriangleNatIndicator n u v) (n - u + 1) := by
    apply nsum_zero_extension hshort
    intro v hv
    unfold parityTriangleNatIndicator
    have hfalse : decide (u + v <= n /\ (u + v + n) % 2 = 0) = false := by
      apply decide_eq_false_iff_not.mpr
      rintro ⟨hbound, _⟩
      omega
    simp only [hfalse, Bool.false_eq_true, if_false]
  rw [htruncate]
  unfold parityRowNatCount
  apply nsum_congr_lt
  intro v _
  exact parityTriangleNatIndicator_eq_row n u v hu

/-- The full two-dimensional count is the sum of its closed row counts. -/
theorem parityTriangleNatCount_eq_rowSum (n : Nat) :
    parityTriangleNatCount n =
      nsum (fun u => parityRowNatCount (n - u)) (n + 1) := by
  unfold parityTriangleNatCount
  apply nsum_congr_lt
  intro u hu
  exact parityTriangleNatRowCount n u (by omega)

/-- Adding two to the triangle depth preserves the old triangle and adds the
`n+3` cells on the new active diagonal. -/
theorem parityTriangleNatCount_add_two (n : Nat) :
    parityTriangleNatCount (n + 2) = parityTriangleNatCount n + (n + 3) := by
  rw [parityTriangleNatCount_eq_rowSum,
    parityTriangleNatCount_eq_rowSum]
  have hprefix :
      nsum (fun u => parityRowNatCount (n + 2 - u)) (n + 1) =
        nsum (fun u => parityRowNatCount (n - u) + 1) (n + 1) := by
    apply nsum_congr_lt
    intro u hu
    have hsub : n + 2 - u = (n - u) + 2 := by omega
    rw [hsub, parityRowNatCount_add_two]
  have htail :
      nsum (fun r => parityRowNatCount (n + 2 - (n + 1 + r))) 2 = 2 := by
    simp only [nsum_succ, nsum_zero]
    rw [show n + 2 - (n + 1 + 0) = 1 by omega,
      show n + 2 - (n + 1 + 1) = 0 by omega,
      parityRowNatCount_eq, parityRowNatCount_eq]
  rw [show n + 2 + 1 = (n + 1) + 2 by omega,
    nsum_split_at, hprefix, nsum_add, nsum_one, htail]
  omega

theorem parityTriangleNatCount_even (q : Nat) :
    parityTriangleNatCount (2 * q) = parityTriangleCount (2 * q) := by
  induction q with
  | zero => decide
  | succ q ih =>
      rw [show 2 * (q + 1) = 2 * q + 2 by omega,
        parityTriangleNatCount_add_two, ih,
        parityTriangleCount_even,
        show 2 * q + 2 = 2 * (q + 1) by omega,
        parityTriangleCount_even]
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
      omega

theorem parityTriangleNatCount_odd (q : Nat) :
    parityTriangleNatCount (2 * q + 1) =
      parityTriangleCount (2 * q + 1) := by
  induction q with
  | zero => decide
  | succ q ih =>
      rw [show 2 * (q + 1) + 1 = (2 * q + 1) + 2 by omega,
        parityTriangleNatCount_add_two, ih,
        parityTriangleCount_odd,
        show 2 * q + 1 + 2 = 2 * (q + 1) + 1 by omega,
        parityTriangleCount_odd]
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
      omega

/-- Closed proof-about-computation formula for every parity triangle. -/
theorem parityTriangleNatCount_eq (n : Nat) :
    parityTriangleNatCount n = parityTriangleCount n := by
  have hpar : n % 2 = 0 \/ n % 2 = 1 := by omega
  cases hpar with
  | inl heven =>
      let q := n / 2
      have hn : n = 2 * q := by unfold q; omega
      rw [hn, parityTriangleNatCount_even]
  | inr hodd =>
      let q := n / 2
      have hn : n = 2 * q + 1 := by unfold q; omega
      rw [hn, parityTriangleNatCount_odd]

/-! ## 8. Threshold translation and exact multiplicities -/

/-- Nat-valued copy of the rational threshold indicator. -/
def endpointThresholdNatIndicator (m a b i j : Nat) : Nat :=
  if endpointPairActive m i j && decide (a <= i) && decide (b <= j) then
    1
  else 0

/-- Executable threshold multiplicity before translation to the origin. -/
def endpointThresholdNatMultiplicity (m a b : Nat) : Nat :=
  nsum (fun i =>
    nsum (fun j => endpointThresholdNatIndicator m a b i j) (m + 1))
    (m + 1)

/-- A computational Nat sum of pointwise zero terms is zero. -/
theorem nsum_eq_zero {f : Nat -> Nat} : forall R,
    (forall i, i < R -> f i = 0) -> nsum f R = 0
  | 0, _ => rfl
  | R + 1, hz => by
      rw [nsum_succ, nsum_eq_zero R
        (fun i hi => hz i (Nat.lt_succ_of_lt hi)),
        hz R (Nat.lt_succ_self R), Nat.zero_add]

/-- A sum whose summand vanishes below `a` can be shifted down by `a`. -/
theorem nsum_shift_of_zero_before {f : Nat -> Nat} (a M : Nat)
    (haM : a <= M) (hz : forall i, i < a -> f i = 0) :
    nsum f M = nsum (fun u => f (a + u)) (M - a) := by
  have hfront : nsum f a = 0 := nsum_eq_zero a hz
  rw [show M = a + (M - a) by omega, nsum_split_at, hfront, Nat.zero_add]
  rw [show a + (M - a) - a = M - a by omega]

/-- Translating a surviving threshold cell by `(a,b)` gives the origin-based
parity triangle of residual depth `m-a-b`. -/
theorem endpointThresholdNatIndicator_shift
    (m a b u v : Nat) (hab : a + b <= m) :
    endpointThresholdNatIndicator m a b (a + u) (b + v) =
      parityTriangleNatIndicator (m - (a + b)) u v := by
  unfold endpointThresholdNatIndicator parityTriangleNatIndicator
  have hmod :
      (a + u + (b + v) + m) % 2 =
        (u + v + (m - (a + b))) % 2 := by
    have hadd :
        a + u + (b + v) + m =
          (u + v + (m - (a + b))) + 2 * (a + b) := by omega
    rw [hadd, Nat.add_mod, Nat.mul_mod]
    simp
  have hiff :
      (a + u + (b + v) <= m /\
          (a + u + (b + v) + m) % 2 = 0) <->
        (u + v <= m - (a + b) /\
          (u + v + (m - (a + b))) % 2 = 0) := by
    constructor
    · rintro ⟨hbound, hparity⟩
      rw [hmod] at hparity
      exact ⟨by omega, hparity⟩
    · rintro ⟨hbound, hparity⟩
      rw [hmod]
      exact ⟨by omega, hparity⟩
  have hactive :
      endpointPairActive m (a + u) (b + v) =
        decide (u + v <= m - (a + b) /\
          (u + v + (m - (a + b))) % 2 = 0) := by
    unfold endpointPairActive
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using hiff
  have ha : decide (a <= a + u) = true := by
    apply decide_eq_true_eq.mpr
    omega
  have hb : decide (b <= b + v) = true := by
    apply decide_eq_true_eq.mpr
    omega
  rw [hactive, ha, hb, Bool.and_true]
  simp only [Bool.and_true]

/-- Any rectangle extending beyond `n+1` in both directions has the same
parity-triangle count as the canonical `(n+1)^2` box. -/
theorem parityTriangleNatRectCount (n U V : Nat)
    (hU : n + 1 <= U) (hV : n + 1 <= V) :
    nsum (fun u =>
      nsum (fun v => parityTriangleNatIndicator n u v) V) U =
      parityTriangleNatCount n := by
  have hinner : forall u,
      nsum (fun v => parityTriangleNatIndicator n u v) V =
        nsum (fun v => parityTriangleNatIndicator n u v) (n + 1) := by
    intro u
    apply nsum_zero_extension hV
    intro v hv
    unfold parityTriangleNatIndicator
    have hfalse : decide (u + v <= n /\ (u + v + n) % 2 = 0) = false := by
      apply decide_eq_false_iff_not.mpr
      rintro ⟨hbound, _⟩
      omega
    simp only [hfalse, Bool.false_eq_true, if_false]
  rw [show (fun u =>
      nsum (fun v => parityTriangleNatIndicator n u v) V) =
        (fun u => nsum (fun v => parityTriangleNatIndicator n u v) (n + 1))
      from funext hinner]
  apply nsum_zero_extension hU
  intro u hu
  have hzero : forall v, parityTriangleNatIndicator n u v = 0 := by
    intro v
    unfold parityTriangleNatIndicator
    have hfalse : decide (u + v <= n /\ (u + v + n) % 2 = 0) = false := by
      apply decide_eq_false_iff_not.mpr
      rintro ⟨hbound, _⟩
      omega
    simp only [hfalse, Bool.false_eq_true, if_false]
  rw [show (fun v => parityTriangleNatIndicator n u v) = (fun _ => 0)
    from funext hzero]
  induction n + 1 with
  | zero => rfl
  | succ R ih => rw [nsum_succ, ih, Nat.zero_add]

/-- Exact computational threshold count.  The proof shifts away the lower
coordinate thresholds and invokes the arbitrary-depth parity-triangle
compiler; it contains no fixed shell depth. -/
theorem endpointThresholdNatMultiplicity_eq (m a b : Nat) :
    endpointThresholdNatMultiplicity m a b = thresholdTriangleCount m a b := by
  by_cases hab : a + b <= m
  · let n := m - (a + b)
    have haM : a <= m + 1 := by omega
    have hbM : b <= m + 1 := by omega
    have houter :
        endpointThresholdNatMultiplicity m a b =
          nsum (fun u =>
            nsum (fun j => endpointThresholdNatIndicator m a b (a + u) j)
              (m + 1)) (m + 1 - a) := by
      unfold endpointThresholdNatMultiplicity
      apply nsum_shift_of_zero_before a (m + 1) haM
      intro i hi
      have hzero : forall j, endpointThresholdNatIndicator m a b i j = 0 := by
        intro j
        unfold endpointThresholdNatIndicator
        have hai : decide (a <= i) = false := by
          apply decide_eq_false_iff_not.mpr
          omega
        simp only [hai, Bool.and_false, Bool.false_and,
          Bool.false_eq_true, if_false]
      rw [show (fun j => endpointThresholdNatIndicator m a b i j) =
          (fun _ => 0) from funext hzero]
      induction m + 1 with
      | zero => rfl
      | succ R ih => rw [nsum_succ, ih, Nat.zero_add]
    rw [houter]
    have hinner : forall u,
        nsum (fun j => endpointThresholdNatIndicator m a b (a + u) j)
            (m + 1) =
          nsum (fun v => endpointThresholdNatIndicator m a b
            (a + u) (b + v)) (m + 1 - b) := by
      intro u
      apply nsum_shift_of_zero_before b (m + 1) hbM
      intro j hj
      unfold endpointThresholdNatIndicator
      have hbj : decide (b <= j) = false := by
        apply decide_eq_false_iff_not.mpr
        omega
      simp only [hbj, Bool.and_false,
        Bool.false_eq_true, if_false]
    rw [show (fun u =>
        nsum (fun j => endpointThresholdNatIndicator m a b (a + u) j)
          (m + 1)) =
        (fun u => nsum (fun v => endpointThresholdNatIndicator m a b
          (a + u) (b + v)) (m + 1 - b)) from funext hinner]
    have hshift : forall u v,
        endpointThresholdNatIndicator m a b (a + u) (b + v) =
          parityTriangleNatIndicator n u v := by
      intro u v
      exact endpointThresholdNatIndicator_shift m a b u v hab
    rw [show (fun u => nsum (fun v => endpointThresholdNatIndicator m a b
        (a + u) (b + v)) (m + 1 - b)) =
        (fun u => nsum (fun v => parityTriangleNatIndicator n u v)
          (m + 1 - b)) from by
          funext u
          apply nsum_congr_lt
          intro v _
          exact hshift u v]
    have hU : n + 1 <= m + 1 - a := by unfold n; omega
    have hV : n + 1 <= m + 1 - b := by unfold n; omega
    rw [parityTriangleNatRectCount n (m + 1 - a) (m + 1 - b) hU hV,
      parityTriangleNatCount_eq]
    unfold thresholdTriangleCount
    rw [if_pos hab]
  · have hzero : endpointThresholdNatMultiplicity m a b = 0 := by
      unfold endpointThresholdNatMultiplicity
      have hterm : forall i j,
          endpointThresholdNatIndicator m a b i j = 0 := by
        intro i j
        unfold endpointThresholdNatIndicator
        have hfalse :
            (endpointPairActive m i j && decide (a <= i) && decide (b <= j)) =
              false := by
          apply Bool.eq_false_iff.mpr
          intro htrue
          simp only [Bool.and_eq_true, endpointPairActive,
            decide_eq_true_eq] at htrue
          omega
        simp only [hfalse, Bool.false_eq_true, if_false]
      rw [show (fun i => nsum
          (fun j => endpointThresholdNatIndicator m a b i j) (m + 1)) =
          (fun _ => 0) from by
            funext i
            rw [show (fun j => endpointThresholdNatIndicator m a b i j) =
              (fun _ => 0) from funext (hterm i)]
            induction m + 1 with
            | zero => rfl
            | succ R ih => rw [nsum_succ, ih, Nat.zero_add]]
      induction m + 1 with
      | zero => rfl
      | succ R ih => rw [nsum_succ, ih, Nat.zero_add]
    rw [hzero]
    unfold thresholdTriangleCount
    rw [if_neg hab]

/-! ## 9. Rational coefficient identity -/

/-- The rational and Nat threshold indicators agree under `Q'.ofNat`. -/
theorem endpointThresholdIndicator_eqv_ofNat (m a b i j : Nat) :
    endpointThresholdIndicator m a b i j ≈
      Q'.ofNat (endpointThresholdNatIndicator m a b i j) := by
  unfold endpointThresholdIndicator endpointThresholdNatIndicator
  by_cases hactive :
      (endpointPairActive m i j && decide (a <= i) && decide (b <= j)) = true
  · simp only [hactive, if_true]
    decide
  · have hfalse :
        (endpointPairActive m i j && decide (a <= i) && decide (b <= j)) =
          false := Bool.eq_false_iff.mpr hactive
    simp only [hfalse, Bool.false_eq_true, if_false]
    decide

/-- The rational multiplicity is the `Q'` image of the executable Nat count. -/
theorem endpointThresholdMultiplicity_eqv_ofNatCount (m a b : Nat) :
    endpointThresholdMultiplicity m a b ≈
      Q'.ofNat (endpointThresholdNatMultiplicity m a b) := by
  unfold endpointThresholdMultiplicity endpointThresholdNatMultiplicity
  have hterms :
      fsum (fun i =>
        fsum (fun j => endpointThresholdIndicator m a b i j) (m + 1))
        (m + 1) ≈
      fsum (fun i =>
        fsum (fun j => Q'.ofNat (endpointThresholdNatIndicator m a b i j))
          (m + 1)) (m + 1) := by
    apply fsum_eqv_congr
    intro i
    apply fsum_eqv_congr
    intro j
    exact endpointThresholdIndicator_eqv_ofNat m a b i j
  refine Q'.eqv_trans _ _ _ hterms ?_
  have hinner :
      fsum (fun i =>
        fsum (fun j => Q'.ofNat (endpointThresholdNatIndicator m a b i j))
          (m + 1)) (m + 1) ≈
      fsum (fun i => Q'.ofNat
        (nsum (fun j => endpointThresholdNatIndicator m a b i j) (m + 1)))
        (m + 1) := by
    apply fsum_eqv_congr
    intro i
    exact fsum_ofNat_eqv_nsum
      (fun j => endpointThresholdNatIndicator m a b i j) (m + 1)
  refine Q'.eqv_trans _ _ _ hinner ?_
  exact fsum_ofNat_eqv_nsum
    (fun i => nsum (fun j => endpointThresholdNatIndicator m a b i j)
      (m + 1)) (m + 1)

/-- Closed rational coefficient formula for every threshold and depth. -/
theorem endpointThresholdMultiplicity_eqv_closed (m a b : Nat) :
    endpointThresholdMultiplicity m a b ≈
      Q'.ofNat (thresholdTriangleCount m a b) := by
  rw [← endpointThresholdNatMultiplicity_eq m a b]
  exact endpointThresholdMultiplicity_eqv_ofNatCount m a b

/-- Closed coefficient expansion with an explicit summation bound. -/
def endpointClosedCoefficientExpansionAt
    (rho : Nat -> Q') (depth bound : Nat) : Q' :=
  fsum (fun a =>
    fsum (fun b =>
      Q'.ofNat (thresholdTriangleCount depth a b) * (rho a * rho b)) bound)
    bound

/-- Arbitrary-depth endpoint semantics with closed parity-triangle
coefficients. -/
theorem endpointTriangleExpr_eq_closedCoefficientExpansion
    (rho : Nat -> Q') (m : Nat) :
    eval rho (endpointTriangleExpr m) ≈
      endpointClosedCoefficientExpansionAt rho m (m + 1) := by
  refine Q'.eqv_trans _ _ _
    (endpointTriangleExpr_eq_coefficientExpansion rho m) ?_
  unfold endpointCoefficientExpansion endpointClosedCoefficientExpansionAt
  apply fsum_eqv_congr
  intro a
  apply fsum_eqv_congr
  intro b
  exact Q'.mul_eqv_congr_right _ _ (rho a * rho b)
    (endpointThresholdMultiplicity_eqv_closed m a b)

/-! ## 10. All-depth adjacent endpoint ratio -/

private theorem closedCoefficientTerm_eqv_zero_of_lt
    (rho : Nat -> Q') (depth a b : Nat) (hdepth : depth < a + b) :
    Q'.ofNat (thresholdTriangleCount depth a b) * (rho a * rho b) ≈ 0 := by
  have hcount : thresholdTriangleCount depth a b = 0 := by
    unfold thresholdTriangleCount
    rw [if_neg (by omega)]
  rw [hcount]
  refine Q'.eqv_trans _ (0 * (rho a * rho b)) _
    (Q'.mul_eqv_congr_right _ _ _ Q'.ofNat_zero_eqv) ?_
  exact Q'.zero_mul_eqv _

/-- Once the summation bound exceeds `depth`, all newly exposed rows and
columns have zero threshold coefficient. -/
theorem endpointClosedCoefficientExpansionAt_stabilizes
    (rho : Nat -> Q') (depth bound : Nat) (hbound : depth + 1 <= bound) :
    endpointClosedCoefficientExpansionAt rho depth bound ≈
      endpointClosedCoefficientExpansionAt rho depth (depth + 1) := by
  unfold endpointClosedCoefficientExpansionAt
  have hinner :
      fsum (fun a => fsum (fun b =>
        Q'.ofNat (thresholdTriangleCount depth a b) * (rho a * rho b)) bound)
        bound ≈
      fsum (fun a => fsum (fun b =>
        Q'.ofNat (thresholdTriangleCount depth a b) * (rho a * rho b))
        (depth + 1)) bound := by
    apply fsum_eqv_congr
    intro a
    apply fsum_zero_extension hbound
    intro b hb
    exact closedCoefficientTerm_eqv_zero_of_lt rho depth a b (by omega)
  refine Q'.eqv_trans _ _ _ hinner ?_
  apply fsum_zero_extension hbound
  intro a ha
  have hterm : forall b,
      Q'.ofNat (thresholdTriangleCount depth a b) * (rho a * rho b) ≈ 0 := by
    intro b
    exact closedCoefficientTerm_eqv_zero_of_lt rho depth a b (by omega)
  have hzero :
      fsum (fun b =>
        Q'.ofNat (thresholdTriangleCount depth a b) * (rho a * rho b))
        (depth + 1) ≈
      fsum (fun _ => (0 : Q')) (depth + 1) := by
    apply fsum_eqv_congr
    exact hterm
  rw [fsum_zero_seq] at hzero
  exact hzero

/-- Coefficient expansion after pulling a scalar through both finite sums. -/
def endpointScaledClosedExpansionAt
    (c : Q') (rho : Nat -> Q') (depth bound : Nat) : Q' :=
  fsum (fun a => fsum (fun b =>
    c * (Q'.ofNat (thresholdTriangleCount depth a b) * (rho a * rho b)))
    bound) bound

theorem scale_endpointClosedCoefficientExpansionAt
    (c : Q') (rho : Nat -> Q') (depth bound : Nat) :
    c * endpointClosedCoefficientExpansionAt rho depth bound ≈
      endpointScaledClosedExpansionAt c rho depth bound := by
  unfold endpointClosedCoefficientExpansionAt endpointScaledClosedExpansionAt
  refine Q'.eqv_trans _ _ _
    (fsum_const_mul c (fun a => fsum (fun b =>
      Q'.ofNat (thresholdTriangleCount depth a b) * (rho a * rho b)) bound)
      bound) ?_
  apply fsum_eqv_congr
  intro a
  exact fsum_const_mul c (fun b =>
    Q'.ofNat (thresholdTriangleCount depth a b) * (rho a * rho b)) bound

/-- Local finite-sum monotonicity, kept in this compiler to avoid importing a
larger positivity layer. -/
theorem fsum_le_of_termwise {f g : Nat -> Q'}
    (h : forall i, f i <= g i) : forall R, fsum f R <= fsum g R
  | 0 => Q'.le_refl' 0
  | R + 1 => Q'.add_le_add (fsum_le_of_termwise h R) (h R)

/-- Range-restricted finite-sum monotonicity. -/
theorem fsum_le_of_termwise_lt {f g : Nat -> Q'} : forall R,
    (forall i, i < R -> f i <= g i) -> fsum f R <= fsum g R
  | 0, _ => Q'.le_refl' 0
  | R + 1, h => Q'.add_le_add
      (fsum_le_of_termwise_lt R
        (fun i hi => h i (Nat.lt_succ_of_lt hi)))
      (h R (Nat.lt_succ_self R))

private theorem ofNat_le_ofNat_semantic {a b : Nat} (h : a <= b) :
    Q'.ofNat a <= Q'.ofNat b := by
  show Int.ofNat a * (1 : Int) <= Int.ofNat b * (1 : Int)
  rw [Int.mul_one, Int.mul_one]
  exact Int.ofNat_le.mpr h

private theorem ofNat_mul_eqv_semantic (a b : Nat) :
    Q'.ofNat (a * b) ≈ Q'.ofNat a * Q'.ofNat b := by
  have hd1 : ((Q'.ofNat a * Q'.ofNat b).den : Int) = 1 := rfl
  have hd2 : ((Q'.ofNat (a * b)).den : Int) = 1 := rfl
  show Int.ofNat (a * b) * ((Q'.ofNat a * Q'.ofNat b).den : Int) =
    (Int.ofNat a * Int.ofNat b) * ((Q'.ofNat (a * b)).den : Int)
  rw [hd1, hd2, Int.mul_one, Int.mul_one]
  exact (Int.ofNat_mul_ofNat a b).symm

private theorem scaledClosedCoefficientTerm_le
    (R m a b : Nat) (hm : 0 < m) (hmR : m <= 2 * R)
    (rho : Nat -> Q') (ha : (0 : Q') <= rho a)
    (hb : (0 : Q') <= rho b) :
    Q'.ofNat (R + 1) *
        (Q'.ofNat (thresholdTriangleCount (m - 1) a b) * (rho a * rho b)) <=
      Q'.ofNat R *
        (Q'.ofNat (thresholdTriangleCount m a b) * (rho a * rho b)) := by
  let leftCount := thresholdTriangleCount (m - 1) a b
  let rightCount := thresholdTriangleCount m a b
  let p := rho a * rho b
  have hNat : (R + 1) * leftCount <= R * rightCount := by
    unfold leftCount rightCount
    exact scaled_thresholdTriangleCount_pred R m a b hm hmR
  have hQ : Q'.ofNat ((R + 1) * leftCount) <=
      Q'.ofNat (R * rightCount) := ofNat_le_ofNat_semantic hNat
  have hp : (0 : Q') <= p := by
    unfold p
    exact Q'.mul_nonneg _ _ ha hb
  have hscaled :
      Q'.ofNat ((R + 1) * leftCount) * p <=
        Q'.ofNat (R * rightCount) * p :=
    Q'.mul_le_mul_of_nonneg_right _ _ p hQ hp
  have hleft :
      Q'.ofNat (R + 1) * (Q'.ofNat leftCount * p) ≈
        Q'.ofNat ((R + 1) * leftCount) * p := by
    refine Q'.eqv_trans _
      ((Q'.ofNat (R + 1) * Q'.ofNat leftCount) * p) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    exact Q'.mul_eqv_congr_right _ _ p
      (Q'.eqv_symm (ofNat_mul_eqv_semantic (R + 1) leftCount))
  have hright :
      Q'.ofNat R * (Q'.ofNat rightCount * p) ≈
        Q'.ofNat (R * rightCount) * p := by
    refine Q'.eqv_trans _
      ((Q'.ofNat R * Q'.ofNat rightCount) * p) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    exact Q'.mul_eqv_congr_right _ _ p
      (Q'.eqv_symm (ofNat_mul_eqv_semantic R rightCount))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hscaled (Q'.ge_of_eqv hright))

/-- Table-free adjacent endpoint ratio at every positive depth.  This is the
semantic replacement for the fixed reflected certificates through depth ten. -/
theorem endpointRatio_allDepth_prefix
    (R m : Nat) (hm : 0 < m) (hmR : m <= 2 * R)
    (rho : Nat -> Q') (hrho : forall i, i <= m -> (0 : Q') <= rho i) :
    Q'.ofNat (R + 1) * eval rho (endpointTriangleExpr (m - 1)) <=
      Q'.ofNat R * eval rho (endpointTriangleExpr m) := by
  let leftSum := endpointScaledClosedExpansionAt
    (Q'.ofNat (R + 1)) rho (m - 1) (m + 1)
  let rightSum := endpointScaledClosedExpansionAt
    (Q'.ofNat R) rho m (m + 1)
  have hsum : leftSum <= rightSum := by
    unfold leftSum rightSum endpointScaledClosedExpansionAt
    apply fsum_le_of_termwise_lt
    intro a haBound
    apply fsum_le_of_termwise_lt
    intro b hbBound
    exact scaledClosedCoefficientTerm_le R m a b hm hmR rho
      (hrho a (by omega)) (hrho b (by omega))
  have hpredBound : m - 1 + 1 <= m + 1 := by omega
  have hleft :
      Q'.ofNat (R + 1) * eval rho (endpointTriangleExpr (m - 1)) ≈
        leftSum := by
    have hsemantic := endpointTriangleExpr_eq_closedCoefficientExpansion
      rho (m - 1)
    have hstable := endpointClosedCoefficientExpansionAt_stabilizes
      rho (m - 1) (m + 1) hpredBound
    refine Q'.eqv_trans _
      (Q'.ofNat (R + 1) *
        endpointClosedCoefficientExpansionAt rho (m - 1) (m - 1 + 1)) _
      (Q'.mul_eqv_congr_left _ _ _ hsemantic) ?_
    refine Q'.eqv_trans _
      (Q'.ofNat (R + 1) *
        endpointClosedCoefficientExpansionAt rho (m - 1) (m + 1)) _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hstable)) ?_
    exact scale_endpointClosedCoefficientExpansionAt
      (Q'.ofNat (R + 1)) rho (m - 1) (m + 1)
  have hright :
      Q'.ofNat R * eval rho (endpointTriangleExpr m) ≈ rightSum := by
    refine Q'.eqv_trans _
      (Q'.ofNat R * endpointClosedCoefficientExpansionAt rho m (m + 1)) _
      (Q'.mul_eqv_congr_left _ _ _
        (endpointTriangleExpr_eq_closedCoefficientExpansion rho m)) ?_
    exact scale_endpointClosedCoefficientExpansionAt
      (Q'.ofNat R) rho m (m + 1)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv hright))

theorem endpointRatio_allDepth
    (R m : Nat) (hm : 0 < m) (hmR : m <= 2 * R)
    (rho : Nat -> Q') (hrho : forall i, (0 : Q') <= rho i) :
    Q'.ofNat (R + 1) * eval rho (endpointTriangleExpr (m - 1)) <=
      Q'.ofNat R * eval rho (endpointTriangleExpr m) :=
  endpointRatio_allDepth_prefix R m hm hmR rho (fun i _ => hrho i)

end YMGap.Continuum.P2HalfTimeEndpointSemanticCompiler

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2HalfTimeEndpointSemanticCompiler.eval_polyFsum_eq_fsum
#print axioms YMGap.Continuum.P2HalfTimeEndpointSemanticCompiler.endpointTriangleExpr_eq_variableExpansion
#print axioms YMGap.Continuum.P2HalfTimeEndpointSemanticCompiler.endpointVariableExpansion_eq_indexedExpansion
#print axioms YMGap.Continuum.P2HalfTimeEndpointSemanticCompiler.fsum4_swap_pairs
#print axioms YMGap.Continuum.P2HalfTimeEndpointSemanticCompiler.endpointTriangleExpr_eq_thresholdExpansion
#print axioms YMGap.Continuum.P2HalfTimeEndpointSemanticCompiler.endpointTriangleExpr_eq_coefficientExpansion
#print axioms YMGap.Continuum.P2HalfTimeEndpointSemanticCompiler.nsum_split_at
#print axioms YMGap.Continuum.P2HalfTimeEndpointSemanticCompiler.nsum_congr_lt
#print axioms YMGap.Continuum.P2HalfTimeEndpointSemanticCompiler.nsum_one
#print axioms YMGap.Continuum.P2HalfTimeEndpointSemanticCompiler.fsum_ofNat_eqv_nsum
#print axioms YMGap.Continuum.P2HalfTimeEndpointSemanticCompiler.parityRowNatIndicator
#print axioms YMGap.Continuum.P2HalfTimeEndpointSemanticCompiler.parityRowNatCount
#print axioms YMGap.Continuum.P2HalfTimeEndpointSemanticCompiler.parityRowNatIndicator_add_two_prefix
#print axioms YMGap.Continuum.P2HalfTimeEndpointSemanticCompiler.parityRowNatIndicator_add_two_tail
#print axioms YMGap.Continuum.P2HalfTimeEndpointSemanticCompiler.parityRowNatCount_add_two
#print axioms YMGap.Continuum.P2HalfTimeEndpointSemanticCompiler.parityRowNatCount_even
#print axioms YMGap.Continuum.P2HalfTimeEndpointSemanticCompiler.parityRowNatCount_odd
#print axioms YMGap.Continuum.P2HalfTimeEndpointSemanticCompiler.parityRowNatCount_eq
#print axioms YMGap.Continuum.P2HalfTimeEndpointSemanticCompiler.nsum_zero_extension
#print axioms YMGap.Continuum.P2HalfTimeEndpointSemanticCompiler.nsum_add
#print axioms YMGap.Continuum.P2HalfTimeEndpointSemanticCompiler.parityTriangleNatIndicator
#print axioms YMGap.Continuum.P2HalfTimeEndpointSemanticCompiler.parityTriangleNatCount
#print axioms YMGap.Continuum.P2HalfTimeEndpointSemanticCompiler.parityTriangleNatIndicator_eq_row
#print axioms YMGap.Continuum.P2HalfTimeEndpointSemanticCompiler.parityTriangleNatRowCount
#print axioms YMGap.Continuum.P2HalfTimeEndpointSemanticCompiler.parityTriangleNatCount_add_two
#print axioms YMGap.Continuum.P2HalfTimeEndpointSemanticCompiler.parityTriangleNatCount_eq
#print axioms YMGap.Continuum.P2HalfTimeEndpointSemanticCompiler.endpointThresholdNatIndicator
#print axioms YMGap.Continuum.P2HalfTimeEndpointSemanticCompiler.endpointThresholdNatMultiplicity
#print axioms YMGap.Continuum.P2HalfTimeEndpointSemanticCompiler.nsum_eq_zero
#print axioms YMGap.Continuum.P2HalfTimeEndpointSemanticCompiler.nsum_shift_of_zero_before
#print axioms YMGap.Continuum.P2HalfTimeEndpointSemanticCompiler.endpointThresholdNatIndicator_shift
#print axioms YMGap.Continuum.P2HalfTimeEndpointSemanticCompiler.parityTriangleNatRectCount
#print axioms YMGap.Continuum.P2HalfTimeEndpointSemanticCompiler.endpointThresholdNatMultiplicity_eq
#print axioms YMGap.Continuum.P2HalfTimeEndpointSemanticCompiler.endpointThresholdIndicator_eqv_ofNat
#print axioms YMGap.Continuum.P2HalfTimeEndpointSemanticCompiler.endpointThresholdMultiplicity_eqv_ofNatCount
#print axioms YMGap.Continuum.P2HalfTimeEndpointSemanticCompiler.endpointThresholdMultiplicity_eqv_closed
#print axioms YMGap.Continuum.P2HalfTimeEndpointSemanticCompiler.endpointTriangleExpr_eq_closedCoefficientExpansion
#print axioms YMGap.Continuum.P2HalfTimeEndpointSemanticCompiler.endpointClosedCoefficientExpansionAt_stabilizes
#print axioms YMGap.Continuum.P2HalfTimeEndpointSemanticCompiler.scale_endpointClosedCoefficientExpansionAt
#print axioms YMGap.Continuum.P2HalfTimeEndpointSemanticCompiler.fsum_le_of_termwise
#print axioms YMGap.Continuum.P2HalfTimeEndpointSemanticCompiler.fsum_le_of_termwise_lt
#print axioms YMGap.Continuum.P2HalfTimeEndpointSemanticCompiler.endpointRatio_allDepth_prefix
#print axioms YMGap.Continuum.P2HalfTimeEndpointSemanticCompiler.endpointRatio_allDepth
