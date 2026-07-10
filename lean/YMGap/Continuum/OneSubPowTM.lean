/-
`OneSubPowTM` — Milestone 13.4, step 2 (second half, part 2): the EXACT
channel polynomials `(1−u)^n` DERIVED by recursion, the exact pilot defect
polynomial CONSTRUCTED — and the honest ADJUDICATION that the naive
two-sided coefficient certificate is provably INADEQUATE for the exact
alternating expansion (machine-refuted), so the one-sided
`hk_defect_uniform` stands as the uniformization.

# What is delivered (all PROVED, axiom-clean)

  * `ModelsExact` — the zero-remainder model predicate
    (`f u ≃ evalPoly cs u` on `[0, u₀]`), with `modelsExact_to_models`
    (bridge into the Taylor-model layer) and CLOSED exact arithmetic:
    `modelsExact_add` / `modelsExact_scale` / `modelsExact_mul`;
  * `oneSub` / `oneSubPow` — the coefficient lists of `1−u` and `(1−u)^n`
    (recursive `mulC`), with `evalPoly_oneSub` and **`evalPoly_oneSubPow`**:
    `evalPoly (oneSubPow n) u ≃ qpow (1−u) n` — the Peter–Weyl channel
    weights as EXACT polynomials, derived, zero remainder;
  * `pilotDefectCoeffs` — the exact pilot defect polynomial
    `(Σ_j d_j·(1−u)^{C₄(j)})·u²` at the certified amplitudes and genuine
    Casimir exponents (degree 17, concrete rationals), with
    **`modelsExact_pilotDefect`**: it exactly represents the heat-kernel
    defect function on `[0, 1]`;
  * **`exact_cert_fails` (machine-REFUTED, kernel `decide`):**
    `coeffLeB pilotDefectCoeffs sixUsq = false` — the alternating binomial
    expansion has POSITIVE coefficients above degree 3, so the coefficientwise
    two-sided certificate of `TMDefectCertificate` can NEVER pass on the
    exact expansion.  The Lakatos verdict: `TMDefectCertificate.cert` as
    typed is the right interface only for FUSED-POSITIVE coefficient data
    (or after degree-clamping on `u ≤ u₀ < 1`); for exact heat-kernel
    channels the correct uniformization is the ONE-SIDED
    `HeatKernelChannelTM.hk_defect_uniform`, ALREADY PROVED.

# What remains open (AGENTS.md Rule 6)

The amplitude identification (fused block-spin coefficients ≤ heat-kernel
channels at the certified amplitudes) and the ϑ₃ truncation tail — plus,
per this module's refutation, the redesign of `TMDefectCertificate`'s
certificate field (degree-clamped or fused-positive).  No frontier type is
touched; the Clay problem remains OPEN.

# Constructive contract (`lean/AGENTS.md` Rules 1, 6, 8)

Mathlib-free; pure `Q'` / `Nat` / `List` core.  No `Classical.*`, no `Real`,
no `native_decide`, no `by_contra`, no `sorry` / `admit` / new `axiom`.
Gated with `#print axioms` (permitted: `propext` / `Quot.sound`).
-/

import YMGap.Continuum.HeatKernelChannelTM

namespace YMGap.Continuum.OneSubPowTM

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.IntervalArithmetic
open YMGap.Continuum.TaylorModel
open YMGap.Continuum.TaylorModelStep2
open YMGap.Continuum.TruncatedBlockSpinContraction
open YMGap.Continuum.HeatKernelChannelTM

/-! ## 1. Zero-remainder (exact) models and their closed arithmetic -/

/-- The exact-model predicate: on `[0, u₀]` the function IS the polynomial. -/
def ModelsExact (cs : List Q') (u₀ : Q') (f : Q' → Q') : Prop :=
  ∀ u, (0 : Q') ≤ u → u ≤ u₀ → (f u).eqv (evalPoly cs u)

/-- Exact models are Taylor models with the point-zero remainder. -/
theorem modelsExact_to_models {cs : List Q'} {u₀ : Q'} {f : Q' → Q'}
    (h : ModelsExact cs u₀ f) : Models ⟨cs, point 0⟩ u₀ f := by
  intro u hu0 hu1
  exact ⟨0, contains_point 0,
    Q'.eqv_trans _ _ _ (h u hu0 hu1)
      (Q'.eqv_symm (Q'.eqv_of_eq (Q'.add_zero' _)))⟩

theorem modelsExact_add {p q : List Q'} {u₀ : Q'} {f g : Q' → Q'}
    (hf : ModelsExact p u₀ f) (hg : ModelsExact q u₀ g) :
    ModelsExact (addC p q) u₀ (fun u => f u + g u) := by
  intro u hu0 hu1
  refine Q'.eqv_trans _ _ _
    (add_eqv_congr_both' (hf u hu0 hu1) (hg u hu0 hu1)) ?_
  exact Q'.eqv_symm (evalPoly_addC u p q)

theorem modelsExact_scale {p : List Q'} {u₀ : Q'} {f : Q' → Q'} (c : Q')
    (hf : ModelsExact p u₀ f) :
    ModelsExact (scaleC c p) u₀ (fun u => c * f u) := by
  intro u hu0 hu1
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (hf u hu0 hu1)) ?_
  exact Q'.eqv_symm (evalPoly_scaleC c u p)

theorem modelsExact_mul {p q : List Q'} {u₀ : Q'} {f g : Q' → Q'}
    (hf : ModelsExact p u₀ f) (hg : ModelsExact q u₀ g) :
    ModelsExact (mulC p q) u₀ (fun u => f u * g u) := by
  intro u hu0 hu1
  refine Q'.eqv_trans _ _ _
    (mul_eqv_congr_both'' (hf u hu0 hu1) (hg u hu0 hu1)) ?_
  exact Q'.eqv_symm (evalPoly_mulC u p q)

/-! ## 2. The exact `(1−u)^n` polynomials, DERIVED -/

/-- The coefficients of `1 − u`. -/
def oneSub : List Q' := [1, -1]

/-- `evalPoly [1, −1] u ≃ 1 − u`. -/
theorem evalPoly_oneSub (u : Q') :
    (evalPoly oneSub u).eqv ((1 : Q') - u) := by
  show ((1 : Q') + u * ((-1 : Q') + u * 0)).eqv ((1 : Q') - u)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr_left _ _ _ (Q'.mul_zero_eqv u))
            (Q'.eqv_of_eq (Q'.add_zero' (-1 : Q')))))
        (Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv u 1)
          (Q'.neg_eqv_congr _ _ (Q'.mul_one_eqv u))))) ?_
  exact Q'.eqv_refl _

/-- The coefficients of `(1 − u)^n` (recursive convolution). -/
def oneSubPow : Nat → List Q'
  | 0 => [1]
  | n + 1 => mulC (oneSubPow n) oneSub

/-- **`evalPoly_oneSubPow` (PROVED — the derived channel weights).**
`evalPoly (oneSubPow n) u ≃ qpow (1 − u) n` for every `n`. -/
theorem evalPoly_oneSubPow (u : Q') :
    ∀ n, (evalPoly (oneSubPow n) u).eqv (qpow ((1 : Q') - u) n)
  | 0 => by
      show ((1 : Q') + u * 0).eqv (1 : Q')
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _ (Q'.mul_zero_eqv u)) ?_
      exact Q'.eqv_of_eq (Q'.add_zero' 1)
  | n + 1 => by
      show (evalPoly (mulC (oneSubPow n) oneSub) u).eqv
        (qpow ((1 : Q') - u) n * ((1 : Q') - u))
      refine Q'.eqv_trans _ _ _ (evalPoly_mulC u (oneSubPow n) oneSub) ?_
      exact mul_eqv_congr_both'' (evalPoly_oneSubPow u n) (evalPoly_oneSub u)

/-- The derived channel is an EXACT model of the heat-kernel weight. -/
theorem modelsExact_channel (d : Q') (n : Nat) (u₀ : Q') :
    ModelsExact (scaleC d (oneSubPow n)) u₀
      (fun u => d * qpow ((1 : Q') - u) n) := by
  intro u hu0 hu1
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_symm (evalPoly_oneSubPow u n))) ?_
  exact Q'.eqv_symm (evalPoly_scaleC d u (oneSubPow n))

/-! ## 3. The exact pilot defect polynomial -/

/-- The `u²` monomial is exact. -/
theorem modelsExact_usq (u₀ : Q') :
    ModelsExact [0, 0, 1] u₀ (fun u => u * u) := by
  intro u hu0 hu1
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _ (evalPoly_c2 1 u) ?_
  exact Q'.one_mul_eqv (u * u)

/-- The exact four-channel sum polynomial at the pilot amplitudes and the
genuine Casimir exponents. -/
def pilotSumCoeffs : List Q' :=
  addC (addC (addC (scaleC coeff0.hi (oneSubPow (c4 0)))
    (scaleC coeff1.hi (oneSubPow (c4 1))))
    (scaleC coeff2.hi (oneSubPow (c4 2))))
    (scaleC coeff3.hi (oneSubPow (c4 3)))

/-- The exact pilot defect polynomial `(Σ_j d_j (1−u)^{C₄(j)})·u²`. -/
def pilotDefectCoeffs : List Q' := mulC pilotSumCoeffs [0, 0, 1]

/-- **`modelsExact_pilotDefect` (PROVED).**  The exact polynomial represents
the heat-kernel defect function on `[0, 1]` — the pilot defect's Taylor
model with ZERO remainder, coefficients DERIVED, not supplied. -/
theorem modelsExact_pilotDefect :
    ModelsExact pilotDefectCoeffs 1
      (fun u =>
        (((coeff0.hi * qpow ((1 : Q') - u) (c4 0)
              + coeff1.hi * qpow ((1 : Q') - u) (c4 1))
            + coeff2.hi * qpow ((1 : Q') - u) (c4 2))
          + coeff3.hi * qpow ((1 : Q') - u) (c4 3)) * (u * u)) :=
  modelsExact_mul
    (modelsExact_add
      (modelsExact_add
        (modelsExact_add
          (modelsExact_channel coeff0.hi (c4 0) 1)
          (modelsExact_channel coeff1.hi (c4 1) 1))
        (modelsExact_channel coeff2.hi (c4 2) 1))
      (modelsExact_channel coeff3.hi (c4 3) 1))
    (modelsExact_usq 1)

/-! ## 4. THE ADJUDICATION: the naive two-sided certificate FAILS on the
exact expansion (machine-refuted) -/

/-- **`exact_cert_fails` (kernel `decide` — the REFUTATION).**  The
coefficientwise certificate `coeffLeB pilotDefectCoeffs sixUsq` is FALSE:
the alternating binomial expansion of `(1−u)^{C₄}·u²` has POSITIVE
coefficients above degree 3 (e.g. `+3·d₁·u⁴` from `(1−u)³`), which the
`≤ 0` padding of `sixUsq` can never dominate.  Hence
`TMDefectCertificate.cert` as typed is UNSATISFIABLE by the exact
heat-kernel expansion — the certificate interface is right only for
fused-positive coefficient data or after degree-clamping on `u₀ < 1`; the
UNIFORMIZATION itself stands, one-sided, as the already-proved
`hk_defect_uniform`. -/
theorem exact_cert_fails : coeffLeB pilotDefectCoeffs sixUsq = false := by
  decide

end YMGap.Continuum.OneSubPowTM

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.OneSubPowTM.modelsExact_to_models
#print axioms YMGap.Continuum.OneSubPowTM.modelsExact_add
#print axioms YMGap.Continuum.OneSubPowTM.modelsExact_scale
#print axioms YMGap.Continuum.OneSubPowTM.modelsExact_mul
#print axioms YMGap.Continuum.OneSubPowTM.evalPoly_oneSub
#print axioms YMGap.Continuum.OneSubPowTM.evalPoly_oneSubPow
#print axioms YMGap.Continuum.OneSubPowTM.modelsExact_channel
#print axioms YMGap.Continuum.OneSubPowTM.modelsExact_usq
#print axioms YMGap.Continuum.OneSubPowTM.modelsExact_pilotDefect
#print axioms YMGap.Continuum.OneSubPowTM.exact_cert_fails
