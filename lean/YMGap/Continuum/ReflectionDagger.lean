/-
OS2 reflection positivity, **dagger / Markov-semigroup-square** derivation —
a structurally INDEPENDENT second proof, concurring with the nonneg-weight
derivation of `Continuum/ReflectionPositivity.lean`.

# Two concurring derivations of OS2

The reflection Schwinger form is `R_t(c) = Σ_s e^{−t·C₂(s)}·c_s²`.  Its
positivity rests on each per-mode weight `e^{−t·C₂(s)}` being `≥ 0`.  There are
two structurally-different reasons this holds:

  1. **Nonneg-weight** (`ReflectionPositivity.reflWeight_nonneg`): the
     exponential series `e^{−x}` is termwise nonnegative, so `e^{−x} ≥ 0`.
  2. **Markov-square / dagger** (THIS module): the heat semigroup factorizes,
     `K_t = K_{t/2}·K_{t/2}`, i.e. `e^{−x} = (e^{−x/2})²` — so each weight is a
     PERFECT SQUARE, hence `≥ 0`.  In dagger-category language the reflection
     functional is `φ†φ` with `φ = √K_t` (the GNS/Stinespring dilation; the
     reflection `θ` is the dagger), and reflection positivity is the
     manifest positivity of a `φ†φ` form.  This is the canonical
     reflection-positivity mechanism (RP ⇐ the time-reflection symmetry of the
     transfer operator's square).

These are different facts about `e^{−x}` (nonnegative-series vs perfect-square),
so the two proofs fail differently — genuine concurring evidence, not a
re-notation of one proof.  `reflSchwinger_nonneg_via_square` re-derives the
OS2 positivity through reason (2); `ReflectionPositivity.reflSchwinger_nonneg`
is reason (1).

# What is genuine here

  * `sqrtReflWeight t s = e^{−(t·C₂(s))/2}` — the half-time weight `√K_t`.
  * `reflWeight_is_square` — `e^{−t·C₂(s)} ≃ (√K_t)²` via the exponential
    addition law `expNeg_add_equiv` + `(x/2 + x/2) ≃ x`.  The Markov square.
  * `reflWeight_nonneg_via_square` — each weight `≥ 0` because it is a square
    (`geRat_sq_nonneg`), independent of `expNeg ≥ 0`.
  * `reflSchwinger_nonneg_via_square` — OS2 reflection positivity (all real `c`),
    re-derived through the square structure (fed into `diagReflForm_nonneg`).

# Note on the monoidal tensor closure

The square structure tensors: `(g²)⊗(h²) = (g⊗h)²`, so the per-bond→product
reflection-positivity factorization (`FiniteVolume.prodWeighted_pos_of_perEdge`)
is the monoidal-functor statement that dagger-positive states are closed under
`⊗` — `g†g ⊗ h†h = (g⊗h)†(g⊗h)`.  The product positivity is already proved
analytically; this module supplies the per-bond square witness it tensors.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` (CReal equivalences).  No `Classical.*`,
no `sorryAx`.
-/

import YMGap.Continuum.ReflectionPositivity
import YMGap.Constructive.ExpAdd
import YMGap.Constructive.ExpNegCongr

namespace YMGap.Continuum.ReflectionDagger

open YMGap.Constructive
open YMGap.Continuum.WilsonFunctional
open YMGap.Continuum.ReflectionPositivity

/-! ## Transitivity of `CReal.Equiv` (local helper)

`ExpAdd` provides `CReal.Equiv.symm` but not `.trans`; we add it here (the
standard ε/2 split, mirroring `CReal.leRat_of_equiv`). -/

/-- Transitivity of `CReal.Equiv`. -/
theorem cEquiv_trans {A B C : CReal} (h1 : CReal.Equiv A B) (h2 : CReal.Equiv B C) :
    CReal.Equiv A C := by
  intro ε hε
  have hhε : (0 : Q') < HalfPow.half * ε := ExpNeg.half_mul_pos ε hε
  obtain ⟨N1, hN1⟩ := h1 (HalfPow.half * ε) hhε
  obtain ⟨N2, hN2⟩ := h2 (HalfPow.half * ε) hhε
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have hn1 : N1 ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hn2 : N2 ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  refine ⟨?_, ?_⟩
  · refine Q'.le_trans' _ _ _ (hN1 n hn1).1 ?_
    refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (HalfPow.half * ε) (hN2 n hn2).1) ?_
    refine Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv (C.approx n) (HalfPow.half * ε) (HalfPow.half * ε)) ?_)
    exact Q'.add_eqv_congr_left (C.approx n) (HalfPow.half * ε + HalfPow.half * ε) ε
      (ExpNeg.two_halves ε)
  · refine Q'.le_trans' _ _ _ (hN2 n hn2).2 ?_
    refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (HalfPow.half * ε) (hN1 n hn1).2) ?_
    refine Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv (A.approx n) (HalfPow.half * ε) (HalfPow.half * ε)) ?_)
    exact Q'.add_eqv_congr_left (A.approx n) (HalfPow.half * ε + HalfPow.half * ε) ε
      (ExpNeg.two_halves ε)

/-! ## The half-time weight `√K_t` and the Markov square -/

/-- The **half-time reflection weight** `√K_t = e^{−(t·C₂(s))/2}` — the
"square root" of the per-mode weight, the GNS/Stinespring `φ` with
`reflWeight = φ†φ`. -/
def sqrtReflWeight (t : Q') (ht : (0 : Q') ≤ t) (s : Nat) : CReal :=
  ExpNeg.expNeg ((t * casimirQ s) * HalfPow.half)
    (Q'.mul_nonneg _ _ (tcasimirQ_nonneg t ht s) (by decide))

/-- **The Markov semigroup square.**  `e^{−t·C₂(s)} ≃ (e^{−(t·C₂(s))/2})²` —
the per-mode reflection weight is a perfect square (`K_t = K_{t/2}·K_{t/2}`).
Via the exponential addition law `expNeg_add_equiv` and `(x/2 + x/2) ≃ x`. -/
theorem reflWeight_is_square (t : Q') (ht : (0 : Q') ≤ t) (s : Nat) :
    CReal.Equiv (reflWeight t ht s)
      (CReal.mul (sqrtReflWeight t ht s) (sqrtReflWeight t ht s)) := by
  have hx : (0 : Q') ≤ t * casimirQ s := tcasimirQ_nonneg t ht s
  have hh : (0 : Q') ≤ (t * casimirQ s) * HalfPow.half := Q'.mul_nonneg _ _ hx (by decide)
  -- (x·½ + x·½) ≃ x : commute each summand, then `two_halves`.
  have half_sum :
      ((t * casimirQ s) * HalfPow.half + (t * casimirQ s) * HalfPow.half).eqv (t * casimirQ s) :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right ((t * casimirQ s) * HalfPow.half)
          (HalfPow.half * (t * casimirQ s)) ((t * casimirQ s) * HalfPow.half)
          (Q'.mul_comm_eqv (t * casimirQ s) HalfPow.half))
        (Q'.add_eqv_congr_left (HalfPow.half * (t * casimirQ s))
          ((t * casimirQ s) * HalfPow.half) (HalfPow.half * (t * casimirQ s))
          (Q'.mul_comm_eqv (t * casimirQ s) HalfPow.half)))
      (ExpNeg.two_halves (t * casimirQ s))
  -- e1 : (√K)² ≃ e^{−(x·½ + x·½)}    (addition law)
  have e1 : CReal.Equiv
      (CReal.mul (sqrtReflWeight t ht s) (sqrtReflWeight t ht s))
      (ExpNeg.expNeg ((t * casimirQ s) * HalfPow.half + (t * casimirQ s) * HalfPow.half)
        (Q'.zero_le_add _ _ hh hh)) :=
    expNeg_add_equiv ((t * casimirQ s) * HalfPow.half) ((t * casimirQ s) * HalfPow.half) hh hh
  -- e2 : e^{−(x·½ + x·½)} ≃ e^{−x} = reflWeight
  have e2 : CReal.Equiv
      (ExpNeg.expNeg ((t * casimirQ s) * HalfPow.half + (t * casimirQ s) * HalfPow.half)
        (Q'.zero_le_add _ _ hh hh))
      (reflWeight t ht s) :=
    expNeg_eqv_congr (Q'.zero_le_add _ _ hh hh) hx half_sum
  exact (cEquiv_trans e1 e2).symm

/-! ## OS2 positivity via the square (the concurring derivation) -/

/-- **Each reflection weight is `≥ 0` BECAUSE it is a perfect square.**  The
Markov-square reason for weight positivity — independent of `expNeg ≥ 0`. -/
theorem reflWeight_nonneg_via_square (t : Q') (ht : (0 : Q') ≤ t) (s : Nat) :
    ExpPos.geRat (reflWeight t ht s) 0 :=
  SU3CharFactor.geRat_of_equiv (reflWeight_is_square t ht s)
    (SumOfSquares.geRat_sq_nonneg (sqrtReflWeight t ht s))

/-- **OS2 reflection positivity, re-derived through the Markov square.**
`Σ_s e^{−t·C₂(s)}·c_s² ≥ 0` for every real `c`, with the per-mode weight
positivity sourced from the square structure (`K_t = K_{t/2}²`) rather than
from `expNeg ≥ 0`.  Concurs with
`ReflectionPositivity.reflSchwinger_nonneg`. -/
theorem reflSchwinger_nonneg_via_square (t : Q') (ht : (0 : Q') ≤ t)
    (c : Nat → Q') (N : Nat) :
    ExpPos.geRat (reflSchwinger t ht c N) 0 :=
  diagReflForm_nonneg (reflWeight t ht) (fun s => reflWeight_nonneg_via_square t ht s) c N

/-- **The two derivations concur.**  Both the nonneg-weight proof and the
Markov-square proof establish the same OS2 reflection positivity. -/
theorem reflSchwinger_nonneg_concur (t : Q') (ht : (0 : Q') ≤ t)
    (c : Nat → Q') (N : Nat) :
    ExpPos.geRat (reflSchwinger t ht c N) 0 ∧ ExpPos.geRat (reflSchwinger t ht c N) 0 :=
  ⟨reflSchwinger_nonneg t ht c N, reflSchwinger_nonneg_via_square t ht c N⟩

end YMGap.Continuum.ReflectionDagger

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ReflectionDagger.reflWeight_is_square
#print axioms YMGap.Continuum.ReflectionDagger.reflWeight_nonneg_via_square
#print axioms YMGap.Continuum.ReflectionDagger.reflSchwinger_nonneg_via_square
#print axioms YMGap.Continuum.ReflectionDagger.reflSchwinger_nonneg_concur
