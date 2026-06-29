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

/-! ## `Q'` glue for the sharp Cauchy–Schwarz extraction

The tilted family `tilted_cs` is the *parametrized* inequality whose envelope
is the sharp `⟨a,b⟩² ≤ ⟨a,a⟩·⟨b,b⟩`.  Extracting the envelope constructively
is a discriminant argument; we route it through the two reflection-positivity
plugs `(s,r) = (−M, A)` and `(s,r) = (C, −M)` (which factor as `A·(AC−M²)` and
`C·(AC−M²)`), sum them, and cancel the positive weight `A+C` — falling back to
the tilted family only on the doubly-degenerate `A = C = 0`.  The lemmas below
are the reusable `Q'` pieces. -/

/-- Sign criterion for strict positivity: `0 < p ↔ 0 < p.num` (mirror of
`Q'.zero_le_iff_num_nonneg`). -/
theorem zero_lt_iff_num_pos (p : Q') : (0 : Q') < p ↔ (0 : Int) < p.num := by
  show (0 : Int) * (p.den : Int) < p.num * (((0 : Q').den) : Int) ↔ (0 : Int) < p.num
  show (0 : Int) * (p.den : Int) < p.num * (1 : Int) ↔ (0 : Int) < p.num
  simp

/-- **Left cancellation by a positive factor**: `0 < c → c·x ≤ c·y → x ≤ y`.
The `Q'` analog of `Int.le_of_mul_le_mul_left`; discharged at the numerator
level after clearing the common positive factor `c.num·c.den`. -/
theorem q_cancel_left {c x y : Q'} (hc : (0 : Q') < c) (h : c * x ≤ c * y) : x ≤ y := by
  have hcn : (0 : Int) < c.num := by
    have h2 : (0 : Int) * (c.den : Int) < c.num * (1 : Int) := hc
    rw [Int.zero_mul, Int.mul_one] at h2; exact h2
  have hh : (c * x).num * (((c * y).den) : Int) ≤ (c * y).num * (((c * x).den) : Int) := h
  show x.num * (y.den : Int) ≤ y.num * (x.den : Int)
  rw [show (c * x).num = c.num * x.num from rfl, show (c * y).num = c.num * y.num from rfl,
      Q'.mul_den_cast c y, Q'.mul_den_cast c x] at hh
  have e1 : (c.num * x.num) * ((c.den : Int) * (y.den : Int))
          = (c.num * (c.den : Int)) * (x.num * (y.den : Int)) := by ac_rfl
  have e2 : (c.num * y.num) * ((c.den : Int) * (x.den : Int))
          = (c.num * (c.den : Int)) * (y.num * (x.den : Int)) := by ac_rfl
  rw [e1, e2] at hh
  have hcc : (0 : Int) < c.num * (c.den : Int) :=
    Int.mul_pos hcn (by exact_mod_cast Q'.den_pos c)
  exact Int.le_of_mul_le_mul_left hh hcc

/-- `w + (-w) ≃ 0`. -/
theorem q_add_neg_self (w : Q') : (w + (-w)).eqv 0 :=
  Q'.eqv_trans _ _ _ (Q'.add_comm_eqv w (-w)) (Q'.neg_add_self_eqv w)

/-- `z + (-(2·z)) ≃ -z` (the `z − 2z = −z` cancellation behind the
discriminant). -/
theorem q_self_sub_two (z : Q') : (z + (-(2 * z))).eqv (-z) := by
  apply QPoly.q_eqv_of_sub_zero
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (z + (-(2 * z))) (-(-z)) z (Q'.neg_neg_eqv z)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv z (-(2 * z)) z) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left z ((-(2 * z)) + z) (z + (-(2 * z))) (Q'.add_comm_eqv (-(2 * z)) z)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv z z (-(2 * z)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right (z + z) (2 * z) (-(2 * z)) (q_two_mul z)) ?_
  exact q_add_neg_self (2 * z)

/-- `(-(2·z)) + z ≃ -z`. -/
theorem q_neg_two_add (z : Q') : ((-(2 * z)) + z).eqv (-z) :=
  Q'.eqv_trans _ _ _ (Q'.add_comm_eqv (-(2 * z)) z) (q_self_sub_two z)

/-- `(-Y)·(-Y) ≃ Y·Y`. -/
theorem q_neg_sq (Y : Q') : ((-Y) * (-Y)).eqv (Y * Y) :=
  Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv (-Y) Y)
    (Q'.eqv_trans _ _ _
      (Q'.neg_eqv_congr ((-Y) * Y) (-(Y * Y)) (Q'.neg_mul_eqv Y Y))
      (Q'.neg_neg_eqv (Y * Y)))

/-- **The `(s,r) = (−Y, X)` discriminant factoring.**  The reflection-positive
quadratic at this plug equals `X·(X·Z) − X·(Y·Y) = X·(XZ − Y²)`.  Combined with
`nonnegQuad` this gives `X·(Y·Y) ≤ X·(X·Z)` — the `A`-weighted Cauchy–Schwarz. -/
theorem quad_factor_left (X Y Z : Q') :
    ((-Y) * (-Y) * X + 2 * ((-Y) * X) * Y + X * X * Z).eqv
      (X * (X * Z) + (-(X * (Y * Y)))) := by
  have hu1 : ((-Y) * (-Y) * X).eqv (X * (Y * Y)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right ((-Y) * (-Y)) (Y * Y) X (q_neg_sq Y))
      (Q'.mul_comm_eqv (Y * Y) X)
  have hu3 : (X * X * Z).eqv (X * (X * Z)) := Q'.mul_assoc_eqv X X Z
  have e_a : ((-Y) * X).eqv (-(Y * X)) := Q'.neg_mul_eqv Y X
  have e_b : (2 * ((-Y) * X)).eqv (-(2 * (Y * X))) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left 2 ((-Y) * X) (-(Y * X)) e_a)
      (Q'.mul_neg_eqv 2 (Y * X))
  have e_c : ((2 * ((-Y) * X)) * Y).eqv (-((2 * (Y * X)) * Y)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right (2 * ((-Y) * X)) (-(2 * (Y * X))) Y e_b)
      (Q'.neg_mul_eqv (2 * (Y * X)) Y)
  have e_d : ((2 * (Y * X)) * Y).eqv (2 * (X * (Y * Y))) :=
    Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv 2 (Y * X) Y)
      (Q'.mul_eqv_congr_left 2 ((Y * X) * Y) (X * (Y * Y))
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right (Y * X) (X * Y) Y (Q'.mul_comm_eqv Y X))
          (Q'.mul_assoc_eqv X Y Y)))
  have hu2 : (2 * ((-Y) * X) * Y).eqv (-(2 * (X * (Y * Y)))) :=
    Q'.eqv_trans _ _ _ e_c (Q'.neg_eqv_congr ((2 * (Y * X)) * Y) (2 * (X * (Y * Y))) e_d)
  have h12 : (((-Y) * (-Y) * X) + (2 * ((-Y) * X) * Y)).eqv (-(X * (Y * Y))) :=
    Q'.eqv_trans _ _ _ (QPoly.q_add_congr hu1 hu2) (q_self_sub_two (X * (Y * Y)))
  exact Q'.eqv_trans _ _ _ (QPoly.q_add_congr h12 hu3)
    (Q'.add_comm_eqv (-(X * (Y * Y))) (X * (X * Z)))

/-- **The `(s,r) = (Z, −Y)` discriminant factoring.**  The reflection-positive
quadratic at this plug equals `Z·(X·Z) − Z·(Y·Y) = Z·(XZ − Y²)`.  Combined with
`nonnegQuad` this gives `Z·(Y·Y) ≤ Z·(X·Z)` — the `C`-weighted Cauchy–Schwarz. -/
theorem quad_factor_right (X Y Z : Q') :
    (Z * Z * X + 2 * (Z * (-Y)) * Y + (-Y) * (-Y) * Z).eqv
      (Z * (X * Z) + (-(Z * (Y * Y)))) := by
  have hv1 : (Z * Z * X).eqv (Z * (X * Z)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv Z Z X)
      (Q'.mul_eqv_congr_left Z (Z * X) (X * Z) (Q'.mul_comm_eqv Z X))
  have hv3 : ((-Y) * (-Y) * Z).eqv (Z * (Y * Y)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right ((-Y) * (-Y)) (Y * Y) Z (q_neg_sq Y))
      (Q'.mul_comm_eqv (Y * Y) Z)
  have f_a : (Z * (-Y)).eqv (-(Z * Y)) := Q'.mul_neg_eqv Z Y
  have f_b : (2 * (Z * (-Y))).eqv (-(2 * (Z * Y))) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left 2 (Z * (-Y)) (-(Z * Y)) f_a)
      (Q'.mul_neg_eqv 2 (Z * Y))
  have f_c : ((2 * (Z * (-Y))) * Y).eqv (-((2 * (Z * Y)) * Y)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right (2 * (Z * (-Y))) (-(2 * (Z * Y))) Y f_b)
      (Q'.neg_mul_eqv (2 * (Z * Y)) Y)
  have f_d : ((2 * (Z * Y)) * Y).eqv (2 * (Z * (Y * Y))) :=
    Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv 2 (Z * Y) Y)
      (Q'.mul_eqv_congr_left 2 ((Z * Y) * Y) (Z * (Y * Y)) (Q'.mul_assoc_eqv Z Y Y))
  have hv2 : (2 * (Z * (-Y)) * Y).eqv (-(2 * (Z * (Y * Y)))) :=
    Q'.eqv_trans _ _ _ f_c (Q'.neg_eqv_congr ((2 * (Z * Y)) * Y) (2 * (Z * (Y * Y))) f_d)
  have h23 : ((2 * (Z * (-Y)) * Y) + ((-Y) * (-Y) * Z)).eqv (-(Z * (Y * Y))) :=
    Q'.eqv_trans _ _ _ (QPoly.q_add_congr hv2 hv3) (q_neg_two_add (Z * (Y * Y)))
  exact Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv (Z * Z * X) (2 * (Z * (-Y)) * Y) ((-Y) * (-Y) * Z))
    (QPoly.q_add_congr hv1 h23)

/-- **The Cauchy–Schwarz core (pure `Q'` algebra).**  From the two weighted
inequalities `A·(M·M) ≤ A·(A·C)` and `C·(M·M) ≤ C·(A·C)` (the discriminant
plugs), the positive-weight sum gives `(A+C)·(M·M) ≤ (A+C)·(A·C)`; cancelling
the positive `A+C` yields the sharp `M·M ≤ A·C`.  When `A+C` is *not* positive,
reflection positivity (`hA`, `hC`) forces `A ≃ C ≃ 0`, and the supplied
degeneracy hypothesis `hdeg` (the tilted-family argument) forces `M ≃ 0`. -/
theorem cs_core (A M C : Q') (hA : (0 : Q') ≤ A) (hC : (0 : Q') ≤ C)
    (ineqA : A * (M * M) ≤ A * (A * C))
    (ineqC : C * (M * M) ≤ C * (A * C))
    (hdeg : A.eqv 0 → C.eqv 0 → M.eqv 0) :
    M * M ≤ A * C := by
  have hadd : A * (M * M) + C * (M * M) ≤ A * (A * C) + C * (A * C) :=
    Q'.le_trans' _ _ _
      (Q'.add_le_add_right (A * (M * M)) (A * (A * C)) (C * (M * M)) ineqA)
      (Q'.add_le_add_left (A * (A * C)) (C * (M * M)) (C * (A * C)) ineqC)
  have hsum : (A + C) * (M * M) ≤ (A + C) * (A * C) :=
    le_of_eqv_le (QPoly.q_add_mul A C (M * M))
      (le_of_le_eqv hadd (Q'.eqv_symm (QPoly.q_add_mul A C (A * C))))
  cases (inferInstance : Decidable ((0 : Q') < A + C)) with
  | isTrue hpos => exact q_cancel_left hpos hsum
  | isFalse hneg =>
    have hna_nonneg : (0 : Int) ≤ A.num := (Q'.zero_le_iff_num_nonneg A).mp hA
    have hnc_nonneg : (0 : Int) ≤ C.num := (Q'.zero_le_iff_num_nonneg C).mp hC
    have hsum_num : (A + C).num = A.num * (C.den : Int) + C.num * (A.den : Int) := rfl
    have hnum_le : (A + C).num ≤ 0 :=
      Int.not_lt.mp (fun hh => hneg ((zero_lt_iff_num_pos (A + C)).mpr hh))
    have hda : (1 : Int) ≤ (A.den : Int) := by have := Q'.den_pos A; omega
    have hdc : (1 : Int) ≤ (C.den : Int) := by have := Q'.den_pos C; omega
    have hp1 : (0 : Int) ≤ A.num * (C.den : Int) := Int.mul_nonneg hna_nonneg (by omega)
    have hp2 : (0 : Int) ≤ C.num * (A.den : Int) := Int.mul_nonneg hnc_nonneg (by omega)
    rw [hsum_num] at hnum_le
    have hp1z : A.num * (C.den : Int) = 0 := by omega
    have hp2z : C.num * (A.den : Int) = 0 := by omega
    have hna : A.num = 0 := by
      rcases Int.mul_eq_zero.mp hp1z with h | h
      · exact h
      · omega
    have hnc : C.num = 0 := by
      rcases Int.mul_eq_zero.mp hp2z with h | h
      · exact h
      · omega
    have hA0 : A.eqv 0 := by
      show A.num * (1 : Int) = (0 : Int) * (A.den : Int)
      simp only [hna, Int.zero_mul]
    have hC0 : C.eqv 0 := by
      show C.num * (1 : Int) = (0 : Int) * (C.den : Int)
      simp only [hnc, Int.zero_mul]
    have hMM0 : (M * M).eqv 0 :=
      Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right M 0 M (hdeg hA0 hC0)) (QPoly.q_zero_mul M)
    exact le_of_eqv_le hMM0 (Q'.mul_nonneg A C hA hC)

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

/-! ### Sharp Cauchy–Schwarz, the radical, and the seminorm -/

/-- **Degeneracy via the tilted family.**  When *both* diagonal entries vanish
(`⟨a,a⟩ ≃ 0` and `⟨b,b⟩ ≃ 0`), the tilted family `tilted_cs` at the integer
points `t = k` reads `(2k)·⟨a,b⟩ ≤ k²·⟨a,a⟩ + ⟨b,b⟩ ≃ 0`.  Plugging
`k = ⟨a,b⟩.num` yields `2·⟨a,b⟩.num² ≤ 0`, which forces `⟨a,b⟩.num = 0`, i.e.
`⟨a,b⟩ ≃ 0`.  This is the irreducibly-tilted boundary case of Cauchy–Schwarz. -/
theorem radical_tilted_zero (F : PreInnerForm V) (a b : V)
    (hA0 : (F.B a a).eqv 0) (hC0 : (F.B b b).eqv 0) : (F.B a b).eqv 0 := by
  have ht := F.tilted_cs (Q'.ofInt (F.B a b).num) a b
  have hTTA :
      (Q'.ofInt (F.B a b).num * Q'.ofInt (F.B a b).num * (F.B a a)).eqv 0 :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofInt (F.B a b).num * Q'.ofInt (F.B a b).num)
        (F.B a a) 0 hA0)
      (QPoly.q_mul_zero (Q'.ofInt (F.B a b).num * Q'.ofInt (F.B a b).num))
  have hRHS :
      (Q'.ofInt (F.B a b).num * Q'.ofInt (F.B a b).num * (F.B a a) + F.B b b).eqv 0 :=
    Q'.eqv_trans _ _ _ (QPoly.q_add_congr hTTA hC0) (QPoly.q_add_zero_eqv 0)
  have hle0 : (2 * Q'.ofInt (F.B a b).num) * (F.B a b) ≤ 0 := le_of_le_eqv ht hRHS
  have hnum_le : ((2 * Q'.ofInt (F.B a b).num) * (F.B a b)).num ≤ 0 := by
    have h2 : ((2 * Q'.ofInt (F.B a b).num) * (F.B a b)).num * (1 : Int)
            ≤ (0 : Int) * (((2 * Q'.ofInt (F.B a b).num) * (F.B a b)).den : Int) := hle0
    rw [Int.mul_one, Int.zero_mul] at h2; exact h2
  have hnum_eq : ((2 * Q'.ofInt (F.B a b).num) * (F.B a b)).num
                  = (2 * (F.B a b).num) * (F.B a b).num := rfl
  rw [hnum_eq, Int.mul_assoc 2 (F.B a b).num (F.B a b).num] at hnum_le
  have hsq_nn : (0 : Int) ≤ (F.B a b).num * (F.B a b).num :=
    (Q'.zero_le_iff_num_nonneg ((F.B a b) * (F.B a b))).mp
      (SumOfSquares.q_mul_self_nonneg (F.B a b))
  have hu0 : (F.B a b).num * (F.B a b).num = 0 := by omega
  have hm0 : (F.B a b).num = 0 := by
    rcases Int.mul_eq_zero.mp hu0 with h | h <;> exact h
  show (F.B a b).num * (1 : Int) = (0 : Int) * ((F.B a b).den : Int)
  simp only [hm0, Int.zero_mul]

/-- **THE SHARP CAUCHY–SCHWARZ INEQUALITY** `⟨a,b⟩² ≤ ⟨a,a⟩·⟨b,b⟩`, the
envelope of the tilted family.  Proved constructively over `Q'` from the
reflection-positivity input alone: the two discriminant plugs `(−M,A)` and
`(C,−M)` (`quad_factor_left`/`quad_factor_right`) give the weighted bounds, and
`cs_core` sums and cancels the positive weight `A+C`, falling back to
`radical_tilted_zero` only on the doubly-degenerate diagonal.  This is the
load-bearing analytic step the GNS quotient-by-the-radical rests on. -/
theorem cauchy_schwarz (F : PreInnerForm V) (a b : V) :
    F.B a b * F.B a b ≤ F.B a a * F.B b b := by
  have ineqA : (F.B a a) * (F.B a b * F.B a b) ≤ (F.B a a) * (F.B a a * F.B b b) :=
    q_le_of_sub_nonneg
      (le_of_le_eqv (F.nonnegQuad (-(F.B a b)) (F.B a a) a b)
        (quad_factor_left (F.B a a) (F.B a b) (F.B b b)))
  have ineqC : (F.B b b) * (F.B a b * F.B a b) ≤ (F.B b b) * (F.B a a * F.B b b) :=
    q_le_of_sub_nonneg
      (le_of_le_eqv (F.nonnegQuad (F.B b b) (-(F.B a b)) a b)
        (quad_factor_right (F.B a a) (F.B a b) (F.B b b)))
  exact cs_core (F.B a a) (F.B a b) (F.B b b) (F.self_nonneg a) (F.self_nonneg b)
    ineqA ineqC (radical_tilted_zero F a b)

/-- **The GNS seminorm-squared** `‖a‖² = ⟨a,a⟩`. -/
def seminormSq (F : PreInnerForm V) (a : V) : Q' := F.B a a

theorem seminormSq_nonneg (F : PreInnerForm V) (a : V) :
    (0 : Q') ≤ F.seminormSq a := F.self_nonneg a

/-- **The radical (null space)** of the form: vectors of zero seminorm.  The
GNS quotient is by this predicate. -/
def Radical (F : PreInnerForm V) (a : V) : Prop := (F.B a a).eqv 0

/-- **The radical is absorbed by the form** — `⟨a,a⟩ = 0 ⇒ ⟨a,b⟩ = 0` for every
`b`.  This is exactly the statement that the form *descends to the quotient by
the radical*: a null vector pairs trivially with everything, so the bilinear
form factors through `V / Radical`.  Proved from the sharp Cauchy–Schwarz:
`⟨a,b⟩² ≤ ⟨a,a⟩·⟨b,b⟩ ≃ 0` and `⟨a,b⟩² ≥ 0` force `⟨a,b⟩ ≃ 0`. -/
theorem radical_form_zero (F : PreInnerForm V) (a b : V)
    (h : F.Radical a) : (F.B a b).eqv 0 := by
  have hcs := F.cauchy_schwarz a b
  have hAC0 : (F.B a a * F.B b b).eqv 0 :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right (F.B a a) 0 (F.B b b) h)
      (QPoly.q_zero_mul (F.B b b))
  have hle0 : (F.B a b * F.B a b) ≤ 0 := le_of_le_eqv hcs hAC0
  have hge0 : (0 : Q') ≤ F.B a b * F.B a b := SumOfSquares.q_mul_self_nonneg (F.B a b)
  have hnum_le : (F.B a b * F.B a b).num ≤ 0 := by
    have h2 : (F.B a b * F.B a b).num * (1 : Int)
            ≤ (0 : Int) * ((F.B a b * F.B a b).den : Int) := hle0
    rw [Int.mul_one, Int.zero_mul] at h2; exact h2
  have hnum_ge : (0 : Int) ≤ (F.B a b * F.B a b).num :=
    (Q'.zero_le_iff_num_nonneg _).mp hge0
  have hnum_eq : (F.B a b * F.B a b).num = (F.B a b).num * (F.B a b).num := rfl
  rw [hnum_eq] at hnum_le hnum_ge
  have hu0 : (F.B a b).num * (F.B a b).num = 0 := by omega
  have hm0 : (F.B a b).num = 0 := by
    rcases Int.mul_eq_zero.mp hu0 with h' | h' <;> exact h'
  show (F.B a b).num * (1 : Int) = (0 : Int) * ((F.B a b).den : Int)
  simp only [hm0, Int.zero_mul]

end PreInnerForm

/-- **A pre-Hilbert datum**: a reflection-positive form bundled with its now-
*proved* sharp Cauchy–Schwarz inequality and the radical-descent law.  Every
`PreInnerForm` yields one (`PreInnerForm.toPreHilbert`), since both fields are
theorems.  Constructing the quotient Hilbert space `V / Radical` and its metric
completion additionally needs the *module* structure on `V` (subtraction, to
form the radical equivalence `a ≈ b ↔ ⟨a−b,a−b⟩ ≃ 0`), which lives at the
observable-algebra level and is the honest remaining boundary. -/
structure PreHilbert (V : Type) where
  /-- The underlying reflection-positive form. -/
  form : PreInnerForm V
  /-- Sharp Cauchy–Schwarz on the form (the pre-Hilbert inequality). -/
  cauchy_schwarz : ∀ a b, form.B a b * form.B a b ≤ form.B a a * form.B b b
  /-- The form descends to the quotient by its radical. -/
  radical_descends : ∀ a b, form.Radical a → (form.B a b).eqv 0

/-- Every reflection-positive form is a pre-Hilbert datum: the two laws are the
proved `cauchy_schwarz` and `radical_form_zero`. -/
def PreInnerForm.toPreHilbert {V : Type} (F : PreInnerForm V) : PreHilbert V where
  form := F
  cauchy_schwarz := F.cauchy_schwarz
  radical_descends := fun a b h => F.radical_form_zero a b h

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

/-- **THE SHARP CAUCHY–SCHWARZ fires on the concrete reflection-weight form**:
`((1/2)·(a·b))² ≤ ((1/2)·(a·a))·((1/2)·(b·b))` — the genuine weighted
`(ab)² ≤ a²·b²`, the envelope of the tilted family, on a non-degenerate
inhabitant. -/
theorem reflModeForm_cauchy_schwarz (a b : Q') :
    reflModeForm.B a b * reflModeForm.B a b ≤ reflModeForm.B a a * reflModeForm.B b b :=
  reflModeForm.cauchy_schwarz a b

/-- **Sharp Cauchy–Schwarz on the general weighted form** `⟨x,y⟩ = w·(x·y)`,
`w ≥ 0`: `(w·(a·b))² ≤ (w·(a·a))·(w·(b·b))`. -/
theorem weightForm_cauchy_schwarz (w : Q') (hw : (0 : Q') ≤ w) (a b : Q') :
    (weightForm w hw).B a b * (weightForm w hw).B a b
      ≤ (weightForm w hw).B a a * (weightForm w hw).B b b :=
  (weightForm w hw).cauchy_schwarz a b

/-- **Radical descent fires on the concrete form**: a vector of zero seminorm
pairs trivially with everything. -/
theorem reflModeForm_radical_form_zero (a b : Q')
    (h : reflModeForm.Radical a) : (reflModeForm.B a b).eqv 0 :=
  reflModeForm.radical_form_zero a b h

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
#print axioms YMGap.Continuum.OSReconstructionProgress.q_cancel_left
#print axioms YMGap.Continuum.OSReconstructionProgress.quad_factor_left
#print axioms YMGap.Continuum.OSReconstructionProgress.quad_factor_right
#print axioms YMGap.Continuum.OSReconstructionProgress.cs_core
#print axioms YMGap.Continuum.OSReconstructionProgress.PreInnerForm.radical_tilted_zero
#print axioms YMGap.Continuum.OSReconstructionProgress.PreInnerForm.cauchy_schwarz
#print axioms YMGap.Continuum.OSReconstructionProgress.PreInnerForm.radical_form_zero
#print axioms YMGap.Continuum.OSReconstructionProgress.PreInnerForm.toPreHilbert
#print axioms YMGap.Continuum.OSReconstructionProgress.reflModeForm_cauchy_schwarz
#print axioms YMGap.Continuum.OSReconstructionProgress.weightForm_cauchy_schwarz
#print axioms YMGap.Continuum.OSReconstructionProgress.reflModeForm_radical_form_zero
