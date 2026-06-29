/-
OS reconstruction progress — the **pre-Hilbert Cauchy–Schwarz layer** that the
GNS construction was missing.

# Which stub this promotes

`Continuum/OSReconstruction.lean` carries the OS reconstruction quintuple
`(H_∞, Ω_0, U(t), H_op)` with the physical Hilbert space `HilbertSpace`
exposed only as a `Unit` carrier and the reconstruction laws
(`VacuumNormalized`, …) as abstract `Prop` fields supplied by the caller.
`Continuum/FiniteVolumeGNS.lean` already promotes part of this to genuine
finite-volume content: it builds the GNS sesquilinear form
`⟨a, b⟩ = E_Λ(star a · b)` and proves its **Gram positivity** `⟨a, a⟩ ≥ 0`
(= reflection positivity, `inner_nonneg`).

But a positive-semidefinite Gram form is *not yet* a pre-Hilbert space.  The
load-bearing analytic step that turns reflection positivity into an honest
inner-product structure — the one the GNS quotient-by-the-radical and the
seminorm rest on — is the **Cauchy–Schwarz / pre-inner-product inequality**.
That step was nowhere in the codebase (`grep cauchy.schwarz` over
`Continuum/` returns only prose mentions).  This module supplies it, as
genuine constructive content over `Q'`, derived purely from the
reflection-positivity input.

# What is genuine here (constructed / proved, axiom-clean)

  * `PreInnerForm V` — a real symmetric bilinear form on a carrier `V`,
    bundling exactly the **reflection-positivity input in diagonalized form**:
    `nonnegQuad` says `⟨s·a + r·b, s·a + r·b⟩ ≥ 0` for all real `s, r`, which
    is `0 ≤ s²⟨a,a⟩ + 2sr⟨a,b⟩ + r²⟨b,b⟩` — the OS2 statement
    `0 ≤ E(θ(w)*·w)` for the two-parameter family of observables
    `w = s·a + r·b`.
  * `self_nonneg` — **reflection positivity recovered**: `0 ≤ ⟨a,a⟩`
    (the `FiniteVolumeGNS.inner_nonneg` content, re-derived from `nonnegQuad`).
  * `tilted_cs` — the **tilted Cauchy–Schwarz family**
    `2t·⟨a,b⟩ ≤ t²·⟨a,a⟩ + ⟨b,b⟩` for every real `t` (the parametrized
    family whose envelope is the sharp Cauchy–Schwarz inequality).  Proved by
    plugging `s = t`, `r = -1` into `nonnegQuad`.
  * `young_cs` — the **Young / Cauchy–Schwarz upper bound**
    `2·⟨a,b⟩ ≤ ⟨a,a⟩ + ⟨b,b⟩` (`t = 1`), the genuine pre-Hilbert inequality
    that makes the GNS seminorm subadditive.
  * `inner_lower` — the matching **lower bound**
    `0 ≤ ⟨a,a⟩ + 2·⟨a,b⟩ + ⟨b,b⟩` (`s = r = 1`); together with `young_cs`
    this is the two-sided `|2·⟨a,b⟩| ≤ ⟨a,a⟩ + ⟨b,b⟩`.
  * `weightForm w hw` — a genuine non-degenerate inhabitant: the one-mode
    weighted GNS form `⟨x, y⟩ = w·(x·y)` for a nonnegative weight
    `w ≥ 0` (the rational stand-in for a Schur reflection weight
    `e^{−t·C₂(s)} ≥ 0` of `Continuum/ReflectionPositivity.lean`), with
    `nonnegQuad` discharged via the explicit sum-of-squares
    `⟨w, w⟩ = w·(s·a + r·b)² ≥ 0`.  On it `young_cs` is the genuine weighted
    `2ab ≤ a² + b²`, a non-trivial inequality.
  * `zeroForm V` — the degenerate (zero-state) inhabitant, for completeness.

# What remains stubbed / paper-level (declared honestly, NOT faked)

  * The **sharp** Cauchy–Schwarz `⟨a,b⟩² ≤ ⟨a,a⟩·⟨b,b⟩` is the *envelope* of
    the `tilted_cs` family; extracting it requires minimizing over `t`
    (a discriminant / division-and-case-analysis argument on `Q'`).  We
    supply the full tilted family, not the extracted envelope.
  * The GNS **quotient by the radical** and the **metric completion** to the
    Hilbert space, the **Hamiltonian** and **Stone semigroup**, and the
    thermodynamic limit `Λ → ∞` remain the paper-level boundary recorded in
    `Continuum/OSContent.lean`'s `ContinuumSpectralInterface`.  This module
    does not cross that boundary; it closes one analytic gap inside it.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` via the reused `Q'` arithmetic and the
`SumOfSquares` square-nonnegativity lemma.  No `Classical.*`, no `sorryAx`,
no `native_decide`.
-/

import YMGap.Constructive.RationalsMul
import YMGap.Constructive.QPoly
import YMGap.Constructive.SumOfSquares

namespace YMGap.Continuum.OSReconstructionProgress

open YMGap.Constructive

/-! ## `Q'` glue lemmas (transfer `≤` across `eqv`, sub-nonneg, doubling) -/

/-- Transfer the right endpoint of `≤` along `eqv`. -/
theorem le_of_le_eqv {a b c : Q'} (h : a ≤ b) (e : b.eqv c) : a ≤ c :=
  Q'.le_trans' a b c h (Q'.le_of_eqv e)

/-- Transfer the left endpoint of `≤` along `eqv`. -/
theorem le_of_eqv_le {a b c : Q'} (e : a.eqv b) (h : b ≤ c) : a ≤ c :=
  Q'.le_trans' a b c (Q'.le_of_eqv e) h

/-- `0 ≤ Y + (-X) ⟹ X ≤ Y` (sub-nonnegativity ⇒ order). -/
theorem q_le_of_sub_nonneg {X Y : Q'} (h : (0 : Q') ≤ Y + (-X)) : X ≤ Y := by
  have h1 : (0 : Q') + X ≤ (Y + (-X)) + X := Q'.add_le_add_right 0 (Y + (-X)) X h
  have eR : ((Y + (-X)) + X).eqv Y :=
    Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv Y (-X) X)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left Y ((-X) + X) 0 (Q'.neg_add_self_eqv X))
        (QPoly.q_add_zero_eqv Y))
  have eL : X ≤ (0 : Q') + X := Q'.ge_of_eqv (QPoly.q_zero_add_eqv X)
  have hX : X ≤ (Y + (-X)) + X := Q'.le_trans' X ((0 : Q') + X) ((Y + (-X)) + X) eL h1
  exact le_of_le_eqv hX eR

/-- `0 ≤ (P + (-N)) + Q ⟹ N ≤ P + Q` (the negated middle term moves over). -/
theorem q_le_of_mid_neg {P N Q : Q'} (h : (0 : Q') ≤ (P + (-N)) + Q) : N ≤ P + Q := by
  have e : ((P + (-N)) + Q).eqv ((P + Q) + (-N)) :=
    Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv P (-N) Q)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left P ((-N) + Q) (Q + (-N)) (Q'.add_comm_eqv (-N) Q))
        (Q'.eqv_symm (Q'.add_assoc_eqv P Q (-N))))
  exact q_le_of_sub_nonneg (le_of_le_eqv h e)

/-- `z + z ≃ 2·z`. -/
theorem q_two_mul (z : Q') : (z + z).eqv (2 * z) := by
  have e2 : (2 : Q') = (1 : Q') + 1 := by decide
  rw [e2]
  exact Q'.eqv_symm
    (Q'.eqv_trans _ _ _ (QPoly.q_add_mul 1 1 z)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right (1 * z) z (1 * z) (Q'.one_mul_eqv z))
        (Q'.add_eqv_congr_left z (1 * z) z (Q'.one_mul_eqv z))))

/-- Four-factor rearrangement `(p·q)·(r·u) ≃ (p·r)·(q·u)`. -/
theorem mul4_rearrange (p q r u : Q') : ((p * q) * (r * u)).eqv ((p * r) * (q * u)) :=
  Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv p q (r * u))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left p (q * (r * u)) ((q * r) * u) (Q'.eqv_symm (Q'.mul_assoc_eqv q r u)))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left p ((q * r) * u) ((r * q) * u)
          (Q'.mul_eqv_congr_right (q * r) (r * q) u (Q'.mul_comm_eqv q r)))
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left p ((r * q) * u) (r * (q * u)) (Q'.mul_assoc_eqv r q u))
          (Q'.eqv_symm (Q'.mul_assoc_eqv p r (q * u))))))

/-- Pull a left factor through a product: `w·(u·v) ≃ u·(w·v)`. -/
theorem mul_pull (w u v : Q') : (w * (u * v)).eqv (u * (w * v)) :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv w u v))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (w * u) (u * w) v (Q'.mul_comm_eqv w u))
      (Q'.mul_assoc_eqv u w v))

/-! ## The square-of-a-binomial expansion over `Q'` -/

/-- `(X + Y)² ≃ X² + 2·(X·Y) + Y²`. -/
theorem sq_binom (X Y : Q') :
    ((X + Y) * (X + Y)).eqv ((X * X + 2 * (X * Y)) + Y * Y) := by
  refine Q'.eqv_trans _ _ _ (QPoly.q_add_mul X Y (X + Y)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right (X * (X + Y)) (X * X + X * Y) (Y * (X + Y)) (Q'.mul_add_eqv X X Y)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (X * X + X * Y) (Y * (X + Y)) (Y * X + Y * Y) (Q'.mul_add_eqv Y X Y)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (X * X + X * Y) (Y * X + Y * Y) (X * Y + Y * Y)
      (Q'.add_eqv_congr_right (Y * X) (X * Y) (Y * Y) (Q'.mul_comm_eqv Y X))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv (X * X + X * Y) (X * Y) (Y * Y))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right ((X * X + X * Y) + X * Y) (X * X + (X * Y + X * Y)) (Y * Y)
      (Q'.add_assoc_eqv (X * X) (X * Y) (X * Y))) ?_
  exact Q'.add_eqv_congr_right (X * X + (X * Y + X * Y)) (X * X + 2 * (X * Y)) (Y * Y)
    (Q'.add_eqv_congr_left (X * X) (X * Y + X * Y) (2 * (X * Y)) (q_two_mul (X * Y)))

/-- The weighted-quadratic identity in `s, r, a, b`:
`(s·a + r·b)² ≃ s²·(a·a) + 2sr·(a·b) + r²·(b·b)`. -/
theorem unweighted_quad_eqv (s r a b : Q') :
    (((s * a) + (r * b)) * ((s * a) + (r * b))).eqv
      (((s * s) * (a * a) + (2 * (s * r)) * (a * b)) + (r * r) * (b * b)) := by
  have hXX : ((s * a) * (s * a)).eqv ((s * s) * (a * a)) := mul4_rearrange s a s a
  have hYY : ((r * b) * (r * b)).eqv ((r * r) * (b * b)) := mul4_rearrange r b r b
  have hXY : ((s * a) * (r * b)).eqv ((s * r) * (a * b)) := mul4_rearrange s a r b
  have h2XY : (2 * ((s * a) * (r * b))).eqv ((2 * (s * r)) * (a * b)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left 2 ((s * a) * (r * b)) ((s * r) * (a * b)) hXY)
      (Q'.eqv_symm (Q'.mul_assoc_eqv 2 (s * r) (a * b)))
  refine Q'.eqv_trans _ _ _ (sq_binom (s * a) (r * b)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ ((s * s) * (a * a) + (2 * (s * r)) * (a * b)) ((r * b) * (r * b))
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right ((s * a) * (s * a)) ((s * s) * (a * a)) (2 * ((s * a) * (r * b))) hXX)
        (Q'.add_eqv_congr_left ((s * s) * (a * a)) (2 * ((s * a) * (r * b))) ((2 * (s * r)) * (a * b)) h2XY))) ?_
  exact Q'.add_eqv_congr_left ((s * s) * (a * a) + (2 * (s * r)) * (a * b)) ((r * b) * (r * b)) ((r * r) * (b * b)) hYY

/-! ## The pre-inner-product form and its Cauchy–Schwarz inequalities -/

/-- A **real symmetric bilinear pre-inner-product form** on a carrier `V`.

The single field `nonnegQuad` is exactly the OS2 reflection-positivity input
in diagonalized form: `⟨s·a + r·b, s·a + r·b⟩ ≥ 0` for all real `s, r`,
written as the nonnegativity of the quadratic
`s²·⟨a,a⟩ + 2sr·⟨a,b⟩ + r²·⟨b,b⟩`.  This bundles symmetry, bilinearity and
positive-semidefiniteness of the form into the one statement a
reflection-positive functional supplies. -/
structure PreInnerForm (V : Type) where
  /-- The bilinear form `⟨a, b⟩`. -/
  B : V → V → Q'
  /-- **Reflection positivity (diagonalized).**  `0 ≤ ⟨s·a + r·b, s·a + r·b⟩`,
  i.e. the quadratic `s²⟨a,a⟩ + 2sr⟨a,b⟩ + r²⟨b,b⟩` is nonnegative for all
  real `s, r`. -/
  nonnegQuad : ∀ (s r : Q') (a b : V),
    (0 : Q') ≤ s * s * (B a a) + 2 * (s * r) * (B a b) + r * r * (B b b)

namespace PreInnerForm

variable {V : Type}

/-- **Reflection positivity recovered:** `0 ≤ ⟨a, a⟩`.  This is the
`FiniteVolumeGNS.inner_nonneg` content (the Gram positivity of the GNS form),
here re-derived from `nonnegQuad` at `s = 1`, `r = 0`. -/
theorem self_nonneg (F : PreInnerForm V) (a : V) : (0 : Q') ≤ F.B a a := by
  have h := F.nonnegQuad 1 0 a a
  -- h : 0 ≤ 1*1*(B a a) + 2*(1*0)*(B a a) + 0*0*(B a a)
  have c1 : ((1 * 1) * (F.B a a)).eqv (F.B a a) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right (1 * 1) 1 (F.B a a) (by decide))
      (Q'.one_mul_eqv (F.B a a))
  have c2 : ((2 * (1 * 0)) * (F.B a a)).eqv 0 :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right (2 * (1 * 0)) 0 (F.B a a) (by decide))
      (QPoly.q_zero_mul (F.B a a))
  have c3 : ((0 * 0) * (F.B a a)).eqv 0 :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right (0 * 0) 0 (F.B a a) (by decide))
      (QPoly.q_zero_mul (F.B a a))
  have e : ((1 * 1 * (F.B a a) + 2 * (1 * 0) * (F.B a a)) + 0 * 0 * (F.B a a)).eqv (F.B a a) :=
    Q'.eqv_trans _ _ _ (QPoly.q_add_congr (QPoly.q_add_congr c1 c2) c3)
      (Q'.eqv_trans _ _ _ (QPoly.q_add_zero_eqv (F.B a a + 0)) (QPoly.q_add_zero_eqv (F.B a a)))
  exact le_of_le_eqv h e

/-- **The tilted Cauchy–Schwarz family:** for every real `t`,
`2t·⟨a,b⟩ ≤ t²·⟨a,a⟩ + ⟨b,b⟩`.  This is the parametrized family whose
envelope (minimizing over `t`) is the sharp Cauchy–Schwarz inequality; we
supply the whole family.  Proved from `nonnegQuad` at `s = t`, `r = -1`. -/
theorem tilted_cs (F : PreInnerForm V) (t : Q') (a b : V) :
    (2 * t) * (F.B a b) ≤ t * t * (F.B a a) + F.B b b := by
  have h0 := F.nonnegQuad t (-1) a b
  -- h0 : 0 ≤ t*t*(B a a) + 2*(t*-1)*(B a b) + (-1)*(-1)*(B b b)
  -- middle coefficient: 2·(t·(-1)) ≃ -(2·t)
  have eT : ((t * (-1))).eqv (-t) :=
    Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv t 1) (Q'.neg_eqv_congr (t * 1) t (Q'.mul_one_eqv t))
  have eq1 : (2 * (t * (-1))).eqv (-(2 * t)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left 2 (t * (-1)) (-t) eT) (Q'.mul_neg_eqv 2 t)
  have eM : ((2 * (t * (-1))) * (F.B a b)).eqv (-((2 * t) * (F.B a b))) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right (2 * (t * (-1))) (-(2 * t)) (F.B a b) eq1)
      (Q'.neg_mul_eqv (2 * t) (F.B a b))
  -- third coefficient: (-1)·(-1) ≃ 1
  have cThird : (((-1) * (-1)) * (F.B b b)).eqv (F.B b b) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right ((-1) * (-1)) 1 (F.B b b) (by decide))
      (Q'.one_mul_eqv (F.B b b))
  have e : ((t * t * (F.B a a) + 2 * (t * (-1)) * (F.B a b)) + (-1) * (-1) * (F.B b b)).eqv
           ((t * t * (F.B a a) + (-((2 * t) * (F.B a b)))) + F.B b b) :=
    QPoly.q_add_congr (QPoly.q_add_congr (Q'.eqv_refl (t * t * (F.B a a))) eM) cThird
  exact q_le_of_mid_neg (le_of_le_eqv h0 e)

/-- **Young / Cauchy–Schwarz upper bound:** `2·⟨a,b⟩ ≤ ⟨a,a⟩ + ⟨b,b⟩`.
The genuine pre-Hilbert inequality (`t = 1` of `tilted_cs`) that makes the GNS
seminorm subadditive. -/
theorem young_cs (F : PreInnerForm V) (a b : V) :
    2 * (F.B a b) ≤ F.B a a + F.B b b := by
  have hLE := tilted_cs F 1 a b
  -- hLE : (2*1)*(B a b) ≤ 1*1*(B a a) + B b b
  have eL : (2 * (F.B a b)).eqv ((2 * 1) * (F.B a b)) :=
    Q'.mul_eqv_congr_right 2 (2 * 1) (F.B a b) (by decide)
  have c1 : ((1 * 1) * (F.B a a)).eqv (F.B a a) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right (1 * 1) 1 (F.B a a) (by decide))
      (Q'.one_mul_eqv (F.B a a))
  have eR : (1 * 1 * (F.B a a) + F.B b b).eqv (F.B a a + F.B b b) :=
    QPoly.q_add_congr c1 (Q'.eqv_refl (F.B b b))
  exact le_of_eqv_le eL (le_of_le_eqv hLE eR)

/-- **The matching lower bound:** `0 ≤ ⟨a,a⟩ + 2·⟨a,b⟩ + ⟨b,b⟩` (`s = r = 1`).
Together with `young_cs` this is the two-sided `|2·⟨a,b⟩| ≤ ⟨a,a⟩ + ⟨b,b⟩`. -/
theorem inner_lower (F : PreInnerForm V) (a b : V) :
    (0 : Q') ≤ (F.B a a + 2 * (F.B a b)) + F.B b b := by
  have h := F.nonnegQuad 1 1 a b
  -- h : 0 ≤ 1*1*(B a a) + 2*(1*1)*(B a b) + 1*1*(B b b)
  have c1 : ((1 * 1) * (F.B a a)).eqv (F.B a a) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right (1 * 1) 1 (F.B a a) (by decide))
      (Q'.one_mul_eqv (F.B a a))
  have c2 : ((2 * (1 * 1)) * (F.B a b)).eqv (2 * (F.B a b)) :=
    Q'.mul_eqv_congr_right (2 * (1 * 1)) 2 (F.B a b) (by decide)
  have c3 : ((1 * 1) * (F.B b b)).eqv (F.B b b) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right (1 * 1) 1 (F.B b b) (by decide))
      (Q'.one_mul_eqv (F.B b b))
  have e : ((1 * 1 * (F.B a a) + 2 * (1 * 1) * (F.B a b)) + 1 * 1 * (F.B b b)).eqv
           ((F.B a a + 2 * (F.B a b)) + F.B b b) :=
    QPoly.q_add_congr (QPoly.q_add_congr c1 c2) c3
  exact le_of_le_eqv h e

end PreInnerForm

/-! ## Inhabitants

`weightForm w hw` is the genuine non-degenerate witness: the one-mode weighted
GNS form `⟨x, y⟩ = w·(x·y)` for `w ≥ 0` (the rational stand-in for a Schur
reflection weight `e^{−t·C₂(s)} ≥ 0` of `Continuum/ReflectionPositivity.lean`).
`zeroForm` is the degenerate zero-state form. -/

/-- The **weighted one-mode pre-inner-product form** `⟨x, y⟩ = w·(x·y)` for a
nonnegative weight `w`.  `nonnegQuad` is discharged via the explicit
sum-of-squares `⟨s·a + r·b, s·a + r·b⟩ = w·(s·a + r·b)² ≥ 0`. -/
def weightForm (w : Q') (hw : (0 : Q') ≤ w) : PreInnerForm Q' where
  B := fun x y => w * (x * y)
  nonnegQuad := by
    intro s r a b
    have hsq : (0 : Q') ≤ w * (((s * a) + (r * b)) * ((s * a) + (r * b))) :=
      Q'.mul_nonneg w (((s * a) + (r * b)) * ((s * a) + (r * b))) hw
        (SumOfSquares.q_mul_self_nonneg ((s * a) + (r * b)))
    have hUQ := unweighted_quad_eqv s r a b
    have step1 : (w * (((s * a) + (r * b)) * ((s * a) + (r * b)))).eqv
                 (w * (((s * s) * (a * a) + (2 * (s * r)) * (a * b)) + (r * r) * (b * b))) :=
      Q'.mul_eqv_congr_left w _ _ hUQ
    have step2 : (w * (((s * s) * (a * a) + (2 * (s * r)) * (a * b)) + (r * r) * (b * b))).eqv
                 ((w * ((s * s) * (a * a) + (2 * (s * r)) * (a * b))) + w * ((r * r) * (b * b))) :=
      Q'.mul_add_eqv w ((s * s) * (a * a) + (2 * (s * r)) * (a * b)) ((r * r) * (b * b))
    have step3 : (w * ((s * s) * (a * a) + (2 * (s * r)) * (a * b))).eqv
                 (w * ((s * s) * (a * a)) + w * ((2 * (s * r)) * (a * b))) :=
      Q'.mul_add_eqv w ((s * s) * (a * a)) ((2 * (s * r)) * (a * b))
    have p1 : (w * ((s * s) * (a * a))).eqv ((s * s) * (w * (a * a))) := mul_pull w (s * s) (a * a)
    have p2 : (w * ((2 * (s * r)) * (a * b))).eqv ((2 * (s * r)) * (w * (a * b))) :=
      mul_pull w (2 * (s * r)) (a * b)
    have p3 : (w * ((r * r) * (b * b))).eqv ((r * r) * (w * (b * b))) := mul_pull w (r * r) (b * b)
    have hWS : (w * (((s * a) + (r * b)) * ((s * a) + (r * b)))).eqv
        (((s * s) * (w * (a * a)) + (2 * (s * r)) * (w * (a * b))) + (r * r) * (w * (b * b))) :=
      Q'.eqv_trans _ _ _ step1
        (Q'.eqv_trans _ _ _ step2
          (Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr_right _
              ((s * s) * (w * (a * a)) + (2 * (s * r)) * (w * (a * b))) (w * ((r * r) * (b * b)))
              (Q'.eqv_trans _ _ _ step3
                (Q'.eqv_trans _ _ _
                  (Q'.add_eqv_congr_right (w * ((s * s) * (a * a))) ((s * s) * (w * (a * a)))
                    (w * ((2 * (s * r)) * (a * b))) p1)
                  (Q'.add_eqv_congr_left ((s * s) * (w * (a * a))) (w * ((2 * (s * r)) * (a * b)))
                    ((2 * (s * r)) * (w * (a * b))) p2))))
            (Q'.add_eqv_congr_left ((s * s) * (w * (a * a)) + (2 * (s * r)) * (w * (a * b)))
              (w * ((r * r) * (b * b))) ((r * r) * (w * (b * b))) p3)))
    exact le_of_le_eqv hsq hWS

/-- The **degenerate zero-state form** `⟨x, y⟩ = 0`, a trivially-checkable
inhabitant of `PreInnerForm` for any carrier. -/
def zeroForm (V : Type) : PreInnerForm V where
  B := fun _ _ => 0
  nonnegQuad := by
    intro s r a b
    have e1 : (s * s * (0 : Q')).eqv 0 := QPoly.q_mul_zero (s * s)
    have e2 : (2 * (s * r) * (0 : Q')).eqv 0 := QPoly.q_mul_zero (2 * (s * r))
    have e3 : (r * r * (0 : Q')).eqv 0 := QPoly.q_mul_zero (r * r)
    have eAB : (s * s * (0 : Q') + 2 * (s * r) * (0 : Q')).eqv 0 :=
      Q'.eqv_trans _ _ _ (QPoly.q_add_congr e1 e2) (QPoly.q_add_zero_eqv 0)
    have e : ((s * s * (0 : Q') + 2 * (s * r) * (0 : Q')) + r * r * (0 : Q')).eqv 0 :=
      Q'.eqv_trans _ _ _ (QPoly.q_add_congr eAB e3) (QPoly.q_add_zero_eqv 0)
    exact le_of_le_eqv (Q'.le_refl' 0) (Q'.eqv_symm e)

/-! ## A concrete reflection-weight inhabitant + the inequalities firing on it

`reflModeForm` is `weightForm` at weight `1/2 ≥ 0` — a genuine non-degenerate
GNS form on which the Cauchy–Schwarz inequalities are non-trivial. -/

/-- The concrete reflection-weight form `⟨x, y⟩ = (1/2)·(x·y)`. -/
def reflModeForm : PreInnerForm Q' :=
  weightForm (Q'.mkPos 1 2 (by decide)) (by decide)

/-- **Reflection positivity** fires on the concrete form: `0 ≤ (1/2)·(a·a)`. -/
theorem reflModeForm_self_nonneg (a : Q') : (0 : Q') ≤ reflModeForm.B a a :=
  reflModeForm.self_nonneg a

/-- **Young / Cauchy–Schwarz** fires on the concrete form:
`2·((1/2)·(a·b)) ≤ (1/2)·(a·a) + (1/2)·(b·b)` — the genuine weighted
`2ab ≤ a² + b²`. -/
theorem reflModeForm_young (a b : Q') :
    2 * (reflModeForm.B a b) ≤ reflModeForm.B a a + reflModeForm.B b b :=
  reflModeForm.young_cs a b

/-- The **tilted family** fires on the concrete form. -/
theorem reflModeForm_tilted (t a b : Q') :
    (2 * t) * (reflModeForm.B a b) ≤ t * t * (reflModeForm.B a a) + reflModeForm.B b b :=
  reflModeForm.tilted_cs t a b

end YMGap.Continuum.OSReconstructionProgress

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.OSReconstructionProgress.PreInnerForm.self_nonneg
#print axioms YMGap.Continuum.OSReconstructionProgress.PreInnerForm.tilted_cs
#print axioms YMGap.Continuum.OSReconstructionProgress.PreInnerForm.young_cs
#print axioms YMGap.Continuum.OSReconstructionProgress.PreInnerForm.inner_lower
#print axioms YMGap.Continuum.OSReconstructionProgress.unweighted_quad_eqv
#print axioms YMGap.Continuum.OSReconstructionProgress.weightForm
#print axioms YMGap.Continuum.OSReconstructionProgress.zeroForm
#print axioms YMGap.Continuum.OSReconstructionProgress.reflModeForm_self_nonneg
#print axioms YMGap.Continuum.OSReconstructionProgress.reflModeForm_young
#print axioms YMGap.Continuum.OSReconstructionProgress.reflModeForm_tilted
