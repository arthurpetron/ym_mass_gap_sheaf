/-
`TaylorModel` — Milestone 13.4, step 1: the TAYLOR-MODEL layer over the
certified `Q'` interval kernel (`IntervalArithmetic`), in the continuum
variable `u = 1 − w`.

# Why (the Koch–Wittwer uniformization)

The item-12 pilot (`TruncatedBlockSpinContraction`) certifies the truncated
block-spin defect at ONE coupling (`w = 4/5`) by interval arithmetic.  The
`singleStep` obligation is uniform along `w_k → 1` — infinitely many scales.
A TAYLOR MODEL — a polynomial with exact rational coefficients plus an
interval remainder, in `u = 1 − w` — converts the whole trajectory tail into
ONE `decide`-checked COEFFICIENT certificate: on `u ∈ [0, u₀]`, a
coefficientwise inequality between polynomials implies the pointwise
inequality for EVERY `u` at once (`evalPoly_le_of_coeffLeB`), because all
powers of `u ≥ 0` are nonnegative.  This is the completed Koch–Wittwer proof
shape (finite window + one parameterized certificate), realized in-substrate.

# What is delivered (all PROVED, axiom-clean)

  * `evalPoly` — Horner evaluation of a rational-coefficient polynomial
    (no `pow` anywhere), with `evalPoly_nonneg`;
  * `addC` / `evalPoly_addC`, `scaleC` / `evalPoly_scaleC` — coefficient
    operations with `eqv`-soundness;
  * `coeffLeB` / `evalPoly_le_of_coeffLeB` — **THE BRIDGE**: a `Bool`
    (hence `decide`-checkable on concrete rationals) coefficientwise
    comparison implies `evalPoly p u ≤ evalPoly q u` for ALL `u ≥ 0`;
  * `TM` (polynomial + `QI` remainder), `Models` (the enclosure semantics on
    `[0, u₀]`), `models_add` / `models_scale` (sound arithmetic), and
    `models_le_of_cert` — the END-TO-END certificate: one coefficient
    `decide` + one endpoint `decide` bound `f u ≤ g u` on the WHOLE domain;
  * `demo_quadratic_cert` — a kernel-checked sample certificate of the
    target shape (`5u² ≤ 6u²`-class, one `decide`).

# What remains open (step 2 — AGENTS.md Rule 6)

The pilot's Taylor model itself: DERIVE the truncated block-spin map's
coefficients as polynomials in `u` from the Peter–Weyl layer (`w^{C₄(r)}`
expanded at `w = 1 − u`), enclose the truncation tail into the remainder
(the ϑ₃ engine), and discharge the `defect(u) ≤ 6u²`-shaped certificate on
an explicit `[0, u₀]` — eliminating both the per-scale certification AND the
FREE-coefficient under-constraint.  `TMDefectCertificate` names that target
(deliberately uninhabited).  No frontier type is touched; the Clay problem
remains OPEN.

# Constructive contract (`lean/AGENTS.md` Rules 1, 6, 8)

Mathlib-free; pure `Q'` / `Nat` / `List` core.  No `Classical.*`, no `Real`,
no `native_decide`, no `by_contra`, no `sorry` / `admit` / new `axiom`.
Gated with `#print axioms` (permitted: `propext` / `Quot.sound`).
-/

import YMGap.Continuum.IntervalArithmetic
import YMGap.Continuum.TruncatedBlockSpinContraction

namespace YMGap.Continuum.TaylorModel

open YMGap.Constructive
open YMGap.Continuum.IntervalArithmetic

/-! ## 0. Small local `Q'` AC helpers -/

/-- Componentwise `eqv` congruence for `+`. -/
theorem add_eqv_congr_both' {a a' b b' : Q'} (ha : a.eqv a') (hb : b.eqv b') :
    (a + b).eqv (a' + b') :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right a a' b ha)
    (Q'.add_eqv_congr_left a' b b' hb)

/-- `(a + b) + (x + y) ≃ (a + x) + (b + y)`. -/
theorem add2_pair (a b x y : Q') :
    ((a + b) + (x + y)).eqv ((a + x) + (b + y)) := by
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a b (x + y)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv b x y))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv b x))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _ (Q'.add_assoc_eqv x b y)) ?_
  exact Q'.eqv_symm (Q'.add_assoc_eqv a x (b + y))

/-- `u·(c·P) ≃ c·(u·P)`. -/
theorem mul_swap' (u c P : Q') : (u * (c * P)).eqv (c * (u * P)) := by
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv u c P)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv u c)) ?_
  exact Q'.mul_assoc_eqv c u P

/-! ## 1. Horner evaluation and its algebra -/

/-- Horner evaluation: `evalPoly [c₀, c₁, …] u = c₀ + u·(c₁ + u·(…))`. -/
def evalPoly (cs : List Q') (u : Q') : Q' :=
  match cs with
  | [] => 0
  | c :: t => c + u * evalPoly t u

/-- Nonnegative coefficients + nonnegative point ⟹ nonnegative value. -/
theorem evalPoly_nonneg {cs : List Q'} (hc : ∀ c, c ∈ cs → (0 : Q') ≤ c)
    {u : Q'} (hu : (0 : Q') ≤ u) : (0 : Q') ≤ evalPoly cs u := by
  induction cs with
  | nil => exact Q'.le_refl' 0
  | cons c t ih =>
      exact Q'.zero_le_add _ _ (hc c List.mem_cons_self)
        (Q'.mul_nonneg _ _ hu
          (ih (fun d hd => hc d (List.mem_cons_of_mem _ hd))))

/-- Coefficientwise addition (with tail padding). -/
def addC : List Q' → List Q' → List Q'
  | [], q => q
  | p, [] => p
  | c :: p, d :: q => (c + d) :: addC p q

/-- **Soundness of `addC`:** `evalPoly (addC p q) u ≃ evalPoly p u + evalPoly q u`. -/
theorem evalPoly_addC (u : Q') :
    ∀ (p q : List Q'),
      (evalPoly (addC p q) u).eqv (evalPoly p u + evalPoly q u)
  | [], q => by
      show (evalPoly q u).eqv ((0 : Q') + evalPoly q u)
      exact Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' _))
  | c :: p, [] => by
      show (evalPoly (c :: p) u).eqv (evalPoly (c :: p) u + 0)
      exact Q'.eqv_symm (Q'.eqv_of_eq (Q'.add_zero' _))
  | c :: p, d :: q => by
      show ((c + d) + u * evalPoly (addC p q) u).eqv
        ((c + u * evalPoly p u) + (d + u * evalPoly q u))
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left _ _ _ (evalPoly_addC u p q))
            (Q'.mul_add_eqv u (evalPoly p u) (evalPoly q u)))) ?_
      exact add2_pair c d (u * evalPoly p u) (u * evalPoly q u)

/-- Coefficientwise scaling. -/
def scaleC (c : Q') (cs : List Q') : List Q' := cs.map (fun d => c * d)

/-- **Soundness of `scaleC`:** `evalPoly (scaleC c p) u ≃ c · evalPoly p u`. -/
theorem evalPoly_scaleC (c u : Q') :
    ∀ (p : List Q'), (evalPoly (scaleC c p) u).eqv (c * evalPoly p u)
  | [] => by
      show (0 : Q').eqv (c * 0)
      exact Q'.eqv_symm (Q'.mul_zero_eqv c)
  | d :: p => by
      show (c * d + u * evalPoly (scaleC c p) u).eqv
        (c * (d + u * evalPoly p u))
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left _ _ _ (evalPoly_scaleC c u p))
            (mul_swap' u c (evalPoly p u)))) ?_
      exact Q'.eqv_symm (Q'.mul_add_eqv c d (u * evalPoly p u))

/-! ## 2. THE BRIDGE: the coefficient certificate -/

/-- All coefficients nonnegative (`Bool`). -/
def allNonnegB : List Q' → Bool
  | [] => true
  | d :: q => decide ((0 : Q') ≤ d) && allNonnegB q

/-- All coefficients nonpositive (`Bool`). -/
def allNonposB : List Q' → Bool
  | [] => true
  | c :: p => decide (c ≤ (0 : Q')) && allNonposB p

/-- The `Bool` coefficientwise comparison (padding with `0`); structural on
the FIRST list so the kernel reduces it under `decide`. -/
def coeffLeB : List Q' → List Q' → Bool
  | [], q => allNonnegB q
  | c :: p, [] => decide (c ≤ (0 : Q')) && allNonposB p
  | c :: p, d :: q => decide (c ≤ d) && coeffLeB p q

/-- Nonneg coefficients ⟹ nonneg value (`Bool` form). -/
theorem evalPoly_nonneg_of_allNonnegB {u : Q'} (hu : (0 : Q') ≤ u) :
    ∀ (q : List Q'), allNonnegB q = true → (0 : Q') ≤ evalPoly q u
  | [], _ => Q'.le_refl' 0
  | d :: q, h => by
      have h' : (decide ((0 : Q') ≤ d) && allNonnegB q) = true := h
      obtain ⟨hd, hq⟩ := (Bool.and_eq_true _ _).mp h'
      show (0 : Q') ≤ d + u * evalPoly q u
      exact Q'.zero_le_add _ _ (of_decide_eq_true hd)
        (Q'.mul_nonneg _ _ hu (evalPoly_nonneg_of_allNonnegB hu q hq))

/-- Nonpos coefficients ⟹ nonpos value (`Bool` form). -/
theorem evalPoly_nonpos_of_allNonposB {u : Q'} (hu : (0 : Q') ≤ u) :
    ∀ (p : List Q'), allNonposB p = true → evalPoly p u ≤ (0 : Q')
  | [], _ => Q'.le_refl' 0
  | c :: p, h => by
      have h' : (decide (c ≤ (0 : Q')) && allNonposB p) = true := h
      obtain ⟨hc, hp⟩ := (Bool.and_eq_true _ _).mp h'
      show c + u * evalPoly p u ≤ (0 : Q')
      have h1 : u * evalPoly p u ≤ (0 : Q') := by
        refine Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_left _ _ _
            (evalPoly_nonpos_of_allNonposB hu p hp) hu) ?_
        exact Q'.le_of_eqv (Q'.mul_zero_eqv u)
      have h2 : c + u * evalPoly p u ≤ (0 : Q') + (0 : Q') :=
        Q'.add_le_add (of_decide_eq_true hc) h1
      refine Q'.le_trans' _ _ _ h2 ?_
      exact Q'.le_of_eqv (Q'.eqv_of_eq (Q'.zero_add' 0))

/-- **`evalPoly_le_of_coeffLeB` (PROVED — one `decide` covers the whole
domain).**  A coefficientwise certificate implies the pointwise polynomial
inequality for EVERY `u ≥ 0`. -/
theorem evalPoly_le_of_coeffLeB {u : Q'} (hu : (0 : Q') ≤ u) :
    ∀ (p q : List Q'), coeffLeB p q = true →
      evalPoly p u ≤ evalPoly q u
  | [], q, h => by
      show (0 : Q') ≤ evalPoly q u
      exact evalPoly_nonneg_of_allNonnegB hu q h
  | c :: p, [], h => by
      have h' : (decide (c ≤ (0 : Q')) && allNonposB p) = true := h
      obtain ⟨hc, hp⟩ := (Bool.and_eq_true _ _).mp h'
      show c + u * evalPoly p u ≤ (0 : Q')
      have h1 : u * evalPoly p u ≤ (0 : Q') := by
        refine Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_left _ _ _
            (evalPoly_nonpos_of_allNonposB hu p hp) hu) ?_
        exact Q'.le_of_eqv (Q'.mul_zero_eqv u)
      have h2 : c + u * evalPoly p u ≤ (0 : Q') + (0 : Q') :=
        Q'.add_le_add (of_decide_eq_true hc) h1
      refine Q'.le_trans' _ _ _ h2 ?_
      exact Q'.le_of_eqv (Q'.eqv_of_eq (Q'.zero_add' 0))
  | c :: p, d :: q, h => by
      have h' : (decide (c ≤ d) && coeffLeB p q) = true := h
      obtain ⟨hc, hpq⟩ := (Bool.and_eq_true _ _).mp h'
      show c + u * evalPoly p u ≤ d + u * evalPoly q u
      exact Q'.add_le_add (of_decide_eq_true hc)
        (Q'.mul_le_mul_of_nonneg_left _ _ _
          (evalPoly_le_of_coeffLeB hu p q hpq) hu)

/-! ## 3. Taylor models: polynomial + interval remainder -/

/-- A **Taylor model**: exact rational polynomial coefficients plus a `QI`
remainder enclosure. -/
structure TM where
  coeffs : List Q'
  rem : QI

/-- `Models t u₀ f` : on the domain `[0, u₀]`, the function `f` is enclosed by
the model — at every point it equals the polynomial plus some remainder value
inside the interval. -/
def Models (t : TM) (u₀ : Q') (f : Q' → Q') : Prop :=
  ∀ u, (0 : Q') ≤ u → u ≤ u₀ →
    ∃ r, contains t.rem r ∧ (f u).eqv (evalPoly t.coeffs u + r)

/-- Sound Taylor-model addition. -/
def tmAdd (t s : TM) : TM := ⟨addC t.coeffs s.coeffs, add t.rem s.rem⟩

/-- **Soundness of `tmAdd`.** -/
theorem models_add {t s : TM} {u₀ : Q'} {f g : Q' → Q'}
    (hf : Models t u₀ f) (hg : Models s u₀ g) :
    Models (tmAdd t s) u₀ (fun u => f u + g u) := by
  intro u hu0 hu1
  obtain ⟨r, hr, hfe⟩ := hf u hu0 hu1
  obtain ⟨r', hr', hge⟩ := hg u hu0 hu1
  refine ⟨r + r', contains_add hr hr', ?_⟩
  refine Q'.eqv_trans _ _ _ (add_eqv_congr_both' hfe hge) ?_
  refine Q'.eqv_trans _ _ _
    (add2_pair (evalPoly t.coeffs u) r (evalPoly s.coeffs u) r') ?_
  exact Q'.add_eqv_congr_right _ _ _
    (Q'.eqv_symm (evalPoly_addC u t.coeffs s.coeffs))

/-- Sound Taylor-model scaling (sign-unknown constant, via the 4-corner
`QI.scale`). -/
def tmScale (c : Q') (t : TM) : TM := ⟨scaleC c t.coeffs, scale c t.rem⟩

/-- **Soundness of `tmScale`.** -/
theorem models_scale {t : TM} {u₀ : Q'} {f : Q' → Q'} (c : Q')
    (hf : Models t u₀ f) :
    Models (tmScale c t) u₀ (fun u => c * f u) := by
  intro u hu0 hu1
  obtain ⟨r, hr, hfe⟩ := hf u hu0 hu1
  refine ⟨c * r, contains_scale hr, ?_⟩
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hfe) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_add_eqv c (evalPoly t.coeffs u) r) ?_
  exact Q'.add_eqv_congr_right _ _ _
    (Q'.eqv_symm (evalPoly_scaleC c u t.coeffs))

/-! ## 4. The END-TO-END certificate -/

/-- **`models_le_of_cert` (PROVED — THE uniformization).**  ONE coefficient
certificate (`decide`-checkable) plus ONE remainder-endpoint comparison
(`decide`-checkable) bound `f u ≤ g u` for EVERY `u ∈ [0, u₀]` at once —
replacing per-scale interval certification along the whole `w_k → 1`
trajectory tail. -/
theorem models_le_of_cert {t s : TM} {u₀ : Q'} {f g : Q' → Q'}
    (hf : Models t u₀ f) (hg : Models s u₀ g)
    (hcoef : coeffLeB t.coeffs s.coeffs = true)
    (hrem : t.rem.hi ≤ s.rem.lo) :
    ∀ u, (0 : Q') ≤ u → u ≤ u₀ → f u ≤ g u := by
  intro u hu0 hu1
  obtain ⟨r, hr, hfe⟩ := hf u hu0 hu1
  obtain ⟨r', hr', hge⟩ := hg u hu0 hu1
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hfe) ?_
  refine Q'.le_trans' _ _ _
    (Q'.add_le_add (evalPoly_le_of_coeffLeB hu0 t.coeffs s.coeffs hcoef)
      (Q'.le_trans' _ _ _ hr.2 (Q'.le_trans' _ _ _ hrem hr'.1))) ?_
  exact Q'.ge_of_eqv hge

/-! ## 5. A kernel-checked sample certificate + the step-2 target -/

/-- The `6u²` bound polynomial. -/
def sixUsq : List Q' := [0, 0, Q'.ofNat 6]

/-- A sample defect-shaped polynomial `5u² + (1/10)u³` dominated after a
degree-3 absorption into `[0, 0, 51/10, 0]` — the certificate is ONE
kernel `decide` on rational coefficients. -/
theorem demo_quadratic_cert :
    coeffLeB [0, 0, Q'.mkPos 51 10 (by decide), 0] sixUsq = true := by
  decide

/-- **`TMDefectCertificate` (NAMED-OPEN — the step-2 obligation).**  The
pilot's Taylor model: a `TM` whose polynomial coefficients are DERIVED from
the Peter–Weyl channel expansion at `w = 1 − u` (not supplied), modeling the
truncated block-spin defect on an explicit `[0, u₀]`, together with the
`≤ 6u²` coefficient certificate.  Deliberately uninhabited: inhabiting it
with derived coefficients is the step-2 construction that closes both the
per-scale gap and the FREE-coefficient under-constraint of the pilot. -/
structure TMDefectCertificate (u₀ : Q') (defect : Q' → Q') : Type where
  /-- The derived Taylor model of the truncated defect. -/
  tm : TM
  /-- It models the defect on `[0, u₀]`. -/
  models : Models tm u₀ defect
  /-- The `6u²`-domination certificate (kernel-checkable). -/
  cert : coeffLeB tm.coeffs sixUsq = true
  /-- The remainder is dominated by the zero remainder of the bound. -/
  rem_le : tm.rem.hi ≤ (0 : Q')

/-- **The producer (PROVED):** a `TMDefectCertificate` yields the UNIFORM
bound `defect u ≤ 6u²` on the whole domain — the `singleStep`-shaped
quadratic decay, uniformly in the scale. -/
theorem defect_le_sixUsq_of_cert {u₀ : Q'} {defect : Q' → Q'}
    (C : TMDefectCertificate u₀ defect) :
    ∀ u, (0 : Q') ≤ u → u ≤ u₀ → defect u ≤ evalPoly sixUsq u := by
  have hsix : Models ⟨sixUsq, point 0⟩ u₀ (fun u => evalPoly sixUsq u) := by
    intro u hu0 hu1
    exact ⟨0, contains_point 0, Q'.eqv_symm (Q'.eqv_of_eq (Q'.add_zero' _))⟩
  exact models_le_of_cert C.models hsix C.cert C.rem_le

end YMGap.Continuum.TaylorModel

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.TaylorModel.add2_pair
#print axioms YMGap.Continuum.TaylorModel.evalPoly_nonneg
#print axioms YMGap.Continuum.TaylorModel.evalPoly_addC
#print axioms YMGap.Continuum.TaylorModel.evalPoly_scaleC
#print axioms YMGap.Continuum.TaylorModel.evalPoly_le_of_coeffLeB
#print axioms YMGap.Continuum.TaylorModel.models_add
#print axioms YMGap.Continuum.TaylorModel.models_scale
#print axioms YMGap.Continuum.TaylorModel.models_le_of_cert
#print axioms YMGap.Continuum.TaylorModel.demo_quadratic_cert
#print axioms YMGap.Continuum.TaylorModel.defect_le_sixUsq_of_cert
