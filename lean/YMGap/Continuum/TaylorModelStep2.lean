/-
`TaylorModelStep2` — Milestone 13.4, step 2 (first half): Taylor-model
MULTIPLICATION (the nonneg-coefficient case, sufficient for heat-kernel
expansions) and the PILOT DEFECT UNIFORMIZED — `defect(u) ≤ 6u²` for EVERY
`u ∈ [0, u₀]` from ONE kernel `decide`, conditional only on the uniform
channel enclosures.

# What is delivered (all PROVED, axiom-clean)

  * `mulC` / `evalPoly_mulC` — polynomial (convolution) multiplication with
    `eqv`-soundness, in Horner form throughout;
  * `evalPoly_mono_u` / `rangeNonneg` / `contains_rangeNonneg` — for
    nonneg-coefficient polynomials, the value on `[0, u₀]` is enclosed by
    `[0, p(u₀)]` (monotone Horner induction);
  * `tmMulN` / `models_mulN` — SOUND Taylor-model multiplication for
    nonneg-coefficient models: `(P + r)(Q + r') = PQ + [P·r' + Q·r + r·r']`
    with the cross terms enclosed through the range intervals — the
    arithmetic the derived Peter–Weyl channel polynomials will compose with;
  * `evalPoly_c2` — `evalPoly [0,0,c] u ≃ c·u²` (the quadratic normal form);
  * **`pilot_defect_uniform`** — THE UNIFORMIZED PILOT: for ANY four channel
    coefficient functions that are nonnegative and lie under the pilot's
    upper enclosures UNIFORMLY on `[0, u₀]`, the truncated defect
    `(Σ_j c_j(u))·u²` satisfies `≤ 6u²` for EVERY `u ∈ [0, u₀]` — the
    certificate is ONE kernel `decide`
    (`pilot_hi_sum_cert : Σ_j hi_j ≤ 6`, actual value `39/10`).  This
    replaces the single-coupling certification of
    `TruncatedBlockSpinContraction` (`w = 4/5` only) by the whole interval
    `w ∈ [1 − u₀, 1]`, i.e. the entire trajectory tail at once.

# What remains open (step 2, second half — AGENTS.md Rule 6)

The SOLE remaining input is the hypothesis this theorem carries: the
UNIFORM channel enclosures — that the true fused channel coefficients, as
functions of `u`, stay within the pilot bounds on `[0, u₀]`.  Deriving them
is the Peter–Weyl construction (channel weights `w^{C₄(r)} = (1−u)^{C₄(r)}`
as exact signed polynomials — `tmAdd`/`tmMulN` compose them; the ϑ₃ tail
into the remainder), which then inhabits `TMDefectCertificate`.  Until that
lands, the enclosures are a NAMED hypothesis, not data — nothing here is
a discharge of `singleStep`; the Clay problem remains OPEN.

# Constructive contract (`lean/AGENTS.md` Rules 1, 6, 8)

Mathlib-free; pure `Q'` / `Nat` / `List` core.  No `Classical.*`, no `Real`,
no `native_decide`, no `by_contra`, no `sorry` / `admit` / new `axiom`.
Gated with `#print axioms` (permitted: `propext` / `Quot.sound`).
-/

import YMGap.Continuum.TaylorModel

namespace YMGap.Continuum.TaylorModelStep2

open YMGap.Constructive
open YMGap.Continuum.IntervalArithmetic
open YMGap.Continuum.TaylorModel
open YMGap.Continuum.TruncatedBlockSpinContraction

/-! ## 1. Polynomial multiplication and its soundness -/

/-- Convolution (Horner) product of coefficient lists. -/
def mulC : List Q' → List Q' → List Q'
  | [], _ => []
  | c :: p, q => addC (scaleC c q) ((0 : Q') :: mulC p q)

/-- **Soundness of `mulC`:**
`evalPoly (mulC p q) u ≃ evalPoly p u · evalPoly q u`. -/
theorem evalPoly_mulC (u : Q') :
    ∀ (p q : List Q'),
      (evalPoly (mulC p q) u).eqv (evalPoly p u * evalPoly q u)
  | [], q => by
      show (0 : Q').eqv ((0 : Q') * evalPoly q u)
      exact Q'.eqv_symm (Q'.zero_mul_eqv _)
  | c :: p, q => by
      have h2 : (evalPoly ((0 : Q') :: mulC p q) u).eqv
          ((u * evalPoly p u) * evalPoly q u) := by
        show ((0 : Q') + u * evalPoly (mulC p q) u).eqv
          ((u * evalPoly p u) * evalPoly q u)
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_of_eq (Q'.zero_add' _)) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left _ _ _ (evalPoly_mulC u p q)) ?_
        exact Q'.eqv_symm (Q'.mul_assoc_eqv u (evalPoly p u) (evalPoly q u))
      show (evalPoly (addC (scaleC c q) ((0 : Q') :: mulC p q)) u).eqv
        ((c + u * evalPoly p u) * evalPoly q u)
      refine Q'.eqv_trans _ _ _
        (evalPoly_addC u (scaleC c q) ((0 : Q') :: mulC p q)) ?_
      refine Q'.eqv_trans _ _ _
        (add_eqv_congr_both' (evalPoly_scaleC c u q) h2) ?_
      exact Q'.eqv_symm
        (Q'.add_mul_eqv c (u * evalPoly p u) (evalPoly q u))

/-! ## 2. Range enclosure for nonneg-coefficient polynomials -/

/-- Monotonicity in the point for nonneg coefficients. -/
theorem evalPoly_mono_u {u u' : Q'} (hu : (0 : Q') ≤ u) (huu' : u ≤ u') :
    ∀ (cs : List Q'), allNonnegB cs = true →
      evalPoly cs u ≤ evalPoly cs u'
  | [], _ => Q'.le_refl' 0
  | c :: t, h => by
      have h' : (decide ((0 : Q') ≤ c) && allNonnegB t) = true := h
      obtain ⟨_, ht⟩ := (Bool.and_eq_true _ _).mp h'
      show c + u * evalPoly t u ≤ c + u' * evalPoly t u'
      refine Q'.add_le_add (Q'.le_refl' c) ?_
      exact Q'.mul_le_mul_of_nonneg huu'
        (evalPoly_mono_u hu huu' t ht)
        (Q'.le_trans' _ _ _ hu huu')
        (evalPoly_nonneg_of_allNonnegB hu t ht)

/-- The `[0, p(u₀)]` range enclosure of a nonneg-coefficient polynomial. -/
def rangeNonneg (cs : List Q') (u₀ : Q') (h : allNonnegB cs = true)
    (hu₀ : (0 : Q') ≤ u₀) : QI :=
  ⟨0, evalPoly cs u₀, evalPoly_nonneg_of_allNonnegB hu₀ cs h⟩

/-- **Soundness of `rangeNonneg`.** -/
theorem contains_rangeNonneg {cs : List Q'} {u₀ : Q'}
    (h : allNonnegB cs = true) (hu₀ : (0 : Q') ≤ u₀)
    {u : Q'} (hu : (0 : Q') ≤ u) (hu1 : u ≤ u₀) :
    contains (rangeNonneg cs u₀ h hu₀) (evalPoly cs u) :=
  ⟨evalPoly_nonneg_of_allNonnegB hu cs h, evalPoly_mono_u hu hu1 cs h⟩

/-! ## 3. Taylor-model multiplication (nonneg-coefficient case) -/

/-- Sound Taylor-model product for nonneg-coefficient models. -/
def tmMulN (t s : TM) (u₀ : Q') (ht : allNonnegB t.coeffs = true)
    (hs : allNonnegB s.coeffs = true) (hu₀ : (0 : Q') ≤ u₀) : TM :=
  ⟨mulC t.coeffs s.coeffs,
    add
      (add (mul (rangeNonneg t.coeffs u₀ ht hu₀) s.rem)
        (mul (rangeNonneg s.coeffs u₀ hs hu₀) t.rem))
      (mul t.rem s.rem)⟩

/-- Componentwise `eqv` congruence for `*`. -/
theorem mul_eqv_congr_both'' {x x' y y' : Q'} (hx : x.eqv x') (hy : y.eqv y') :
    (x * y).eqv (x' * y') :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hx)
    (Q'.mul_eqv_congr_left _ _ _ hy)

/-- **Soundness of `tmMulN`.** -/
theorem models_mulN {t s : TM} {u₀ : Q'} {f g : Q' → Q'}
    (ht : allNonnegB t.coeffs = true) (hs : allNonnegB s.coeffs = true)
    (hu₀ : (0 : Q') ≤ u₀)
    (hf : Models t u₀ f) (hg : Models s u₀ g) :
    Models (tmMulN t s u₀ ht hs hu₀) u₀ (fun u => f u * g u) := by
  intro u hu0 hu1
  obtain ⟨r, hr, hfe⟩ := hf u hu0 hu1
  obtain ⟨r', hr', hge⟩ := hg u hu0 hu1
  refine ⟨(evalPoly t.coeffs u * r' + evalPoly s.coeffs u * r) + r * r',
    contains_add
      (contains_add
        (contains_mul (contains_rangeNonneg ht hu₀ hu0 hu1) hr')
        (contains_mul (contains_rangeNonneg hs hu₀ hu0 hu1) hr))
      (contains_mul hr hr'), ?_⟩
  -- f·g ≃ (P+r)(Q+r') ≃ PQ + (P·r' + Q·r + r·r')
  refine Q'.eqv_trans _ _ _
    (mul_eqv_congr_both'' hfe hge) ?_
  -- (P+r)(Q+r') ≃ (PQ + rQ) + (P r' + r r')
  refine Q'.eqv_trans _ _ _
    (Q'.mul_add_eqv (evalPoly t.coeffs u + r) (evalPoly s.coeffs u) r') ?_
  refine Q'.eqv_trans _ _ _
    (add_eqv_congr_both'
      (Q'.add_mul_eqv (evalPoly t.coeffs u) r (evalPoly s.coeffs u))
      (Q'.add_mul_eqv (evalPoly t.coeffs u) r r')) ?_
  -- (PQ + rQ) + (P r' + r r') ≃ (PQ + P r') + (rQ + r r')
  refine Q'.eqv_trans _ _ _
    (add2_pair (evalPoly t.coeffs u * evalPoly s.coeffs u)
      (r * evalPoly s.coeffs u)
      (evalPoly t.coeffs u * r') (r * r')) ?_
  -- ≃ PQ + (P r' + (Q r + r r')) with rQ ≃ Q r, then reassociate
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.add_eqv_congr_left _ _ _
        (Q'.add_eqv_congr_right _ _ _
          (Q'.mul_comm_eqv r (evalPoly s.coeffs u))))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))) ?_
  exact Q'.add_eqv_congr_right _ _ _
    (Q'.eqv_symm (evalPoly_mulC u t.coeffs s.coeffs))

/-! ## 4. THE PILOT UNIFORMIZED (one-sided assembly + one `decide`) -/

/-- `evalPoly [0,0,c] u ≃ c·(u·u)` — the quadratic normal form. -/
theorem evalPoly_c2 (c u : Q') :
    (evalPoly [0, 0, c] u).eqv (c * (u * u)) := by
  show ((0 : Q') + u * ((0 : Q') + u * (c + u * 0))).eqv (c * (u * u))
  refine Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.zero_add' _)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_of_eq (Q'.zero_add' _))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left _ _ _ (Q'.mul_zero_eqv u))
          (Q'.eqv_of_eq (Q'.add_zero' c))))) ?_
  -- u·(u·c) ≃ c·(u·u)
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv u u c)) ?_
  exact Q'.mul_comm_eqv (u * u) c

/-- The pilot upper-enclosure sum `Σ_j hi_j = 39/10`. -/
def pilotHiSum : Q' := coeff0.hi + coeff1.hi + coeff2.hi + coeff3.hi

/-- **The ONE kernel certificate:** `Σ_j hi_j ≤ 6`. -/
theorem pilot_hi_sum_cert : coeffLeB [0, 0, pilotHiSum] sixUsq = true := by
  decide

/-- **`pilot_defect_uniform` (PROVED — the pilot certification UNIFORMIZED
over the whole interval).**  For ANY channel coefficient functions that are
nonnegative and lie under the pilot upper enclosures UNIFORMLY on
`[0, u₀]`, the truncated defect obeys the `singleStep`-shaped quadratic
bound at EVERY `u ∈ [0, u₀]` at once:

    (c₀(u) + c₁(u) + c₂(u) + c₃(u)) · u²  ≤  6u².

The certificate is the single kernel `decide` `pilot_hi_sum_cert`
(`39/10 ≤ 6`) — the entire trajectory tail `w ∈ [1 − u₀, 1]` in one check,
replacing the pointwise `w = 4/5` pilot.  The UNIFORM ENCLOSURE hypothesis
is the named residual (the Peter–Weyl derivation). -/
theorem pilot_defect_uniform (u₀ : Q')
    (c0f c1f c2f c3f : Q' → Q')
    (hnn : ∀ u, (0 : Q') ≤ u → u ≤ u₀ →
      (0 : Q') ≤ c0f u ∧ (0 : Q') ≤ c1f u ∧ (0 : Q') ≤ c2f u
        ∧ (0 : Q') ≤ c3f u)
    (hub : ∀ u, (0 : Q') ≤ u → u ≤ u₀ →
      c0f u ≤ coeff0.hi ∧ c1f u ≤ coeff1.hi ∧ c2f u ≤ coeff2.hi
        ∧ c3f u ≤ coeff3.hi) :
    ∀ u, (0 : Q') ≤ u → u ≤ u₀ →
      (((c0f u + c1f u) + c2f u) + c3f u) * (u * u)
        ≤ evalPoly sixUsq u := by
  intro u hu0 hu1
  obtain ⟨h0, h1, h2, h3⟩ := hub u hu0 hu1
  have husq : (0 : Q') ≤ u * u := Q'.mul_nonneg _ _ hu0 hu0
  -- Σ c_j(u) ≤ Σ hi_j
  have hsum : ((c0f u + c1f u) + c2f u) + c3f u ≤ pilotHiSum :=
    Q'.add_le_add (Q'.add_le_add (Q'.add_le_add h0 h1) h2) h3
  -- (Σ c)·u² ≤ (Σ hi)·u² ≃ evalPoly [0,0,Σhi] ≤ evalPoly sixUsq
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hsum husq) ?_
  refine Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (evalPoly_c2 pilotHiSum u)) ?_
  exact evalPoly_le_of_coeffLeB hu0 [0, 0, pilotHiSum] sixUsq
    pilot_hi_sum_cert

end YMGap.Continuum.TaylorModelStep2

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.TaylorModelStep2.evalPoly_mulC
#print axioms YMGap.Continuum.TaylorModelStep2.evalPoly_mono_u
#print axioms YMGap.Continuum.TaylorModelStep2.contains_rangeNonneg
#print axioms YMGap.Continuum.TaylorModelStep2.models_mulN
#print axioms YMGap.Continuum.TaylorModelStep2.evalPoly_c2
#print axioms YMGap.Continuum.TaylorModelStep2.pilot_hi_sum_cert
#print axioms YMGap.Continuum.TaylorModelStep2.pilot_defect_uniform
