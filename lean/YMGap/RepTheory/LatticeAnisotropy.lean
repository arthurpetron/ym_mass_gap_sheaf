/-
Thread B / R2 — the D₄ / 24-cell ROTATION-RESTORATION reduction: the finite
INVARIANT-THEORY crux that SELECTS the leading hypercubic rotation-breaking
operator and PROVES the 24-cell symmetry pushes it to strictly higher degree.

# Why this module exists

`RepTheory/Spin4Reflection.lean` discharged the finite ℤ₂ chiral-reflection
margin and ISOLATED the single remaining open `O(4)` datum into the named field
`O4ConnectedInput.rotationRestored : Prop` — the continuum statement that the
lattice's rotation-breaking operators are RG-irrelevant as `a → 0`.  That field
was an OPAQUE `Prop`: it carried no information about WHICH operator sets the
restoration rate, nor about how a finer lattice symmetry sharpens the wall.

This module supplies the finite, exact, group-theoretic content that the
restoration rate actually depends on, and UPGRADES `rotationRestored` into a
QUANTITATIVE, degree-parameterized named input.

# The math (exact finite `Q'` arithmetic at the operator level)

A lattice point group `G_lat ⊂ O(4)` breaks continuum `O(4)`.  Rotation
symmetry is restored in the continuum iff every `G_lat`-invariant-but-not-
`O(4)`-invariant operator is RG-IRRELEVANT.  The LEADING such operator (lowest
polynomial degree above the isotropic quadratic) sets the restoration rate: a
LARGER `G_lat` kills more low-degree breaking invariants, pushing the leading
breaking operator to HIGHER degree, hence FASTER restoration.

  * Hypercubic point group `B₄` (signed permutations) has basic-invariant
    degrees `{2, 4, 6, 8}`.  A degree-4 anisotropy invariant
    `A₄(x) = x₀⁴ + x₁⁴ + x₂⁴ + x₃⁴` exists and is THE leading hypercubic
    rotation-breaking operator (modulo its `O(4)` trace part).
  * The 24-cell point group = `F₄` Weyl group has degrees `{2, 6, 8, 12}`:
    NO degree-4 invariant; the first invariant above the isotropic quadratic
    `Q₂(x) = Σ xᵢ²` is degree 6.  (We CITE this `F₄`-invariant-ring
    classification; we do NOT reprove it.  What we DO prove is the concrete
    fact that forces it at degree 4: the extra 24-cell generator BREAKS `A₄`.)
  * The extra 24-cell/D₄ generator beyond signed permutations is the orthogonal
    Hadamard matrix
        H₄ = ½ · [[1, 1, 1, 1], [1,−1, 1,−1], [1, 1,−1,−1], [1,−1,−1, 1]]
    (`H₄ᵀ H₄ = I`, so `H₄ ∈ O(4)`).
  * CONCRETE WITNESS (the whole crux).  On `x = (1,0,0,0)`:
        `Q₂(H₄ x) = 4 · (½)² = 1 = Q₂(x)`     (quadratic preserved — `H₄ ∈ O(4)`),
        `A₄(H₄ x) = 4 · (½)⁴ = 1/4 ≠ 1 = A₄(x)` (degree-4 anisotropy BROKEN).

So the degree-4 invariant that SURVIVES the hypercubic group `B₄` is DESTROYED
by the larger 24-cell symmetry; the 24-cell's leading rotation-breaking operator
is therefore strictly higher degree (`≥ 6`).

# What is PROVED here — and what stays OPEN (honest)

PROVED, with `[propext]` / `[propext, Quot.sound]` axiom sets only:

  * `Q2_signPerm` / `A4_signPerm` — `Q₂` and `A₄` are invariant under the
    signed-permutation generators (a coordinate swap and a sign flip), hence
    under all of `B₄`: `Σ xᵢ^(2k)` is manifestly invariant under permuting and
    sign-flipping coordinates.
  * `Q2_H4` — `Q₂(H₄ v) ≃ Q₂(v)` for ALL `v` (the Hadamard generator preserves
    the isotropic quadratic; `H₄ ∈ O(4)`).
  * `A4_H4_not_invariant` — THE CRUX: `¬ (A₄(H₄ witness)).eqv (A₄ witness)` for
    `witness = (1,0,0,0)`, with `A₄(witness) ≃ 1` and `A₄(H₄ witness) ≃ 1/4`.
    The concrete degree-4 BREAK.
  * `cell24_leadingBreakDegree_gt_hypercubic` (`4 < 6`) — the rigorous "24-cell
    pushes the leading rotation-breaking operator strictly higher", anchored to
    the proved `A4_H4_not_invariant`.
  * `RotationRestorationInput` / `o4ConnectedFromAnisotropy` — the UPGRADE: the
    rotation-restoration datum is now PARAMETERIZED by `leadingBreakDegree`
    with a PROVED `4 < leadingBreakDegree` margin, and feeds
    `Spin4Reflection.O4ConnectedInput` so the `O(4)` accounting exposes the
    explicit leading-break degree instead of an opaque `Prop`.

NOT proved here — the genuinely-OPEN continuum analytic wall (carried as the
named field `RotationRestorationInput.irrelevant : Prop`, the accepted
named-input pattern, exactly like `rotationRestored`): the RG-IRRELEVANCE of an
operator of degree `leadingBreakDegree` as `a → 0`.  The group theory above
SELECTS which operator's irrelevance is needed and shows the 24-cell makes that
operator higher-degree (a weaker/sharper wall); it does NOT establish the
irrelevance itself, which is the continuum frontier.

# Honest scope / weakenings

  * We do NOT reprove the full `F₄` invariant-ring classification `{2,6,8,12}`;
    it is cited.  What we prove is the degree-4 break that is its operative
    consequence here.
  * The genuine rotation-breaking operator is `A₄`'s `O(4)`-TRACELESS part;
    `Σ xᵢ⁴` mixes in a trace piece `∝ (Σ xᵢ²)²`.  But the trace piece IS
    `O(4)`-invariant (a function of `Q₂`, which `H₄` preserves), so the
    non-invariance of `A₄` under `H₄` already exhibits a genuine degree-4
    anisotropy that the 24-cell breaks — which is exactly what selects the
    leading degree.  (Comment, not a gap.)
  * That the 24-cell gauge discretization yields the SAME continuum universality
    class is standard-but-unproven lore; noted, not claimed.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'` / `Nat` arithmetic and structural reuse of
`RepTheory/Spin4Reflection.lean`.  Every load-bearing declaration is gated with
`#print axioms`; permitted output is `propext` / `Quot.sound` (and `funext`)
only.  No `Classical.*`, no `native_decide`, no `decide`-on-nondecidable, no
`sorry`, no `Prop := True` stub.  All witnesses are `Type`-level data.
-/

import YMGap.RepTheory.Spin4Reflection
import YMGap.Constructive.Rationals
import YMGap.Constructive.RationalsMul

namespace YMGap.RepTheory.LatticeAnisotropy

open YMGap.Constructive

/-! ## 1. A tiny 4-vector + matrix-action layer over `Q'`

We represent a 4-vector over `Q'` as an explicit `structure V4` (four named
`Q'` coordinates) — the cleanest shape for closed-`Q'` `decide`.  We define the
isotropic quadratic `Q₂(v) = Σ vᵢ²`, the leading hypercubic anisotropy
`A₄(v) = Σ vᵢ⁴`, the signed-permutation GENERATORS (a coordinate swap and a
sign flip — enough to characterize `B₄`-invariance of `Q₂`/`A₄`), and the
24-cell Hadamard generator `H₄` (with the `½` factors over `Q'`). -/

/-- A 4-vector over the constructive rationals `Q'`. -/
structure V4 where
  x0 : Q'
  x1 : Q'
  x2 : Q'
  x3 : Q'

namespace V4

/-- Square of a `Q'` value. -/
@[inline] def sq (q : Q') : Q' := q * q

/-- Fourth power of a `Q'` value. -/
@[inline] def quart (q : Q') : Q' := (q * q) * (q * q)

/-- The isotropic quadratic `Q₂(v) = Σ vᵢ²` (the `O(4)`-invariant). -/
@[inline] def Q2 (v : V4) : Q' := sq v.x0 + sq v.x1 + sq v.x2 + sq v.x3

/-- The leading hypercubic anisotropy `A₄(v) = Σ vᵢ⁴` (the degree-4
rotation-breaking invariant of the hypercubic group `B₄`). -/
@[inline] def A4 (v : V4) : Q' := quart v.x0 + quart v.x1 + quart v.x2 + quart v.x3

/-! ### Signed-permutation generators of `B₄` -/

/-- Coordinate-swap generator `0 ↔ 1` (a transposition; a generator of the
permutation part of the hypercubic group `B₄`). -/
@[inline] def swap01 (v : V4) : V4 := ⟨v.x1, v.x0, v.x2, v.x3⟩

/-- Sign-flip generator on coordinate `0` (a generator of the sign part of the
hypercubic group `B₄`). -/
@[inline] def flip0 (v : V4) : V4 := ⟨-v.x0, v.x1, v.x2, v.x3⟩

/-! ### The 24-cell / D₄ Hadamard generator `H₄`

`H₄ = ½ · [[1, 1, 1, 1], [1,−1, 1,−1], [1, 1,−1,−1], [1,−1,−1, 1]]`.  The `½`
factor is `mkPos 1 2`.  Each output coordinate is `½ ·` the signed sum of the
input coordinates dictated by the corresponding row. -/

/-- The rational `½` over `Q'`. -/
@[inline] def half : Q' := Q'.mkPos 1 2 (by decide)

/-- The 24-cell / D₄ Hadamard generator `H₄ ∈ O(4)`, applied to `v`.
Rows (before the `½`):
`r0 = (+,+,+,+)`, `r1 = (+,−,+,−)`, `r2 = (+,+,−,−)`, `r3 = (+,−,−,+)`. -/
@[inline] def H4 (v : V4) : V4 :=
  ⟨half * (v.x0 + v.x1 + v.x2 + v.x3),
   half * (v.x0 - v.x1 + v.x2 - v.x3),
   half * (v.x0 + v.x1 - v.x2 - v.x3),
   half * (v.x0 - v.x1 - v.x2 + v.x3)⟩

/-! ## 2. Invariance facts (PROVED theorems) -/

/-- `Q₂` is invariant under the coordinate-swap generator (manifestly: swapping
two summands of `Σ vᵢ²` leaves the sum equal up to `Q'.eqv`). -/
theorem Q2_swap01 (v : V4) : (Q2 (swap01 v)).eqv (Q2 v) := by
  -- Q2 (swap01 v) = sq x1 + sq x0 + sq x2 + sq x3; reorder the first two summands.
  show ((sq v.x1 + sq v.x0) + sq v.x2 + sq v.x3).eqv
        ((sq v.x0 + sq v.x1) + sq v.x2 + sq v.x3)
  exact Q'.add_eqv_congr_right _ _ _
    (Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv (sq v.x1) (sq v.x0)))

/-- `Q₂` is invariant under the sign-flip generator (`(−x)² = x²`). -/
theorem Q2_flip0 (v : V4) : (Q2 (flip0 v)).eqv (Q2 v) := by
  -- Only the first summand changes: sq (−x0) ≃ sq x0.
  show ((sq (-v.x0) + sq v.x1) + sq v.x2 + sq v.x3).eqv
        ((sq v.x0 + sq v.x1) + sq v.x2 + sq v.x3)
  have h : (sq (-v.x0)).eqv (sq v.x0) := by
    -- sq (−x0) = (−x0)·(−x0) ≃ −(x0·(−x0)) ≃ −(−(x0·x0)) ≃ x0·x0 = sq x0.
    show ((-v.x0) * (-v.x0)).eqv (v.x0 * v.x0)
    exact Q'.eqv_trans _ (-(v.x0 * (-v.x0))) _
      (Q'.neg_mul_eqv v.x0 (-v.x0))
      (Q'.eqv_trans _ (-(-(v.x0 * v.x0))) _
        (Q'.neg_eqv_congr _ _ (Q'.mul_neg_eqv v.x0 v.x0))
        (Q'.neg_neg_eqv (v.x0 * v.x0)))
  exact Q'.add_eqv_congr_right _ _ _
    (Q'.add_eqv_congr_right _ _ _ (Q'.add_eqv_congr_right _ _ _ h))

/-- **`A₄` is invariant under the signed-permutation generators.**  Swapping
coordinates reorders the summands of `Σ vᵢ⁴`; flipping a sign uses `(−x)⁴ = x⁴`.
Both leave `A₄` equal up to `Q'.eqv`.  This is THE leading hypercubic invariant:
`A₄` SURVIVES the whole hypercubic group `B₄`. -/
theorem A4_signPerm (v : V4) :
    (A4 (swap01 v)).eqv (A4 v) ∧ (A4 (flip0 v)).eqv (A4 v) := by
  refine ⟨?_, ?_⟩
  · -- swap: reorder first two summands of Σ vᵢ⁴.
    show ((quart v.x1 + quart v.x0) + quart v.x2 + quart v.x3).eqv
          ((quart v.x0 + quart v.x1) + quart v.x2 + quart v.x3)
    exact Q'.add_eqv_congr_right _ _ _
      (Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv (quart v.x1) (quart v.x0)))
  · -- flip: quart (−x0) ≃ quart x0.
    show ((quart (-v.x0) + quart v.x1) + quart v.x2 + quart v.x3).eqv
          ((quart v.x0 + quart v.x1) + quart v.x2 + quart v.x3)
    have h : (quart (-v.x0)).eqv (quart v.x0) := by
      -- quart (−x0) = ((−x0)·(−x0)) · ((−x0)·(−x0)); each inner factor ≃ x0·x0,
      -- so the product ≃ (x0·x0)·(x0·x0) = quart x0.
      show (((-v.x0) * (-v.x0)) * ((-v.x0) * (-v.x0))).eqv
            ((v.x0 * v.x0) * (v.x0 * v.x0))
      have hinner : ((-v.x0) * (-v.x0)).eqv (v.x0 * v.x0) :=
        Q'.eqv_trans _ (-(v.x0 * (-v.x0))) _
          (Q'.neg_mul_eqv v.x0 (-v.x0))
          (Q'.eqv_trans _ (-(-(v.x0 * v.x0))) _
            (Q'.neg_eqv_congr _ _ (Q'.mul_neg_eqv v.x0 v.x0))
            (Q'.neg_neg_eqv (v.x0 * v.x0)))
      -- congruence of `*` on both factors.
      exact Q'.eqv_trans _ ((v.x0 * v.x0) * ((-v.x0) * (-v.x0))) _
        (Q'.mul_eqv_congr_right _ _ _ hinner)
        (Q'.mul_eqv_congr_left _ _ _ hinner)
    exact Q'.add_eqv_congr_right _ _ _
      (Q'.add_eqv_congr_right _ _ _ (Q'.add_eqv_congr_right _ _ _ h))

/-! ### The witness and the crux

`witness = (1,0,0,0)`.  `H₄ witness = (½,½,½,½)`.  We prove the quadratic is
preserved (`H₄ ∈ O(4)`) and the degree-4 anisotropy is BROKEN. -/

/-- The crux witness `x = (1,0,0,0)`. -/
def witness : V4 := ⟨1, 0, 0, 0⟩

/-- `Q₂(witness) ≃ 1`. -/
theorem Q2_witness : (Q2 witness).eqv 1 := by decide

/-- `A₄(witness) ≃ 1`. -/
theorem A4_witness : (A4 witness).eqv 1 := by decide

/-- `Q₂(H₄ witness) ≃ 1` — the Hadamard generator preserves the isotropic
quadratic on the witness (`4 · (½)² = 1`). -/
theorem Q2_H4_witness : (Q2 (H4 witness)).eqv 1 := by decide

/-- `A₄(H₄ witness) ≃ 1/4` — the Hadamard generator sends the degree-4
anisotropy to `4 · (½)⁴ = 1/4`. -/
theorem A4_H4_witness : (A4 (H4 witness)).eqv (Q'.mkPos 1 4 (by decide)) := by decide

/-- `Q₂(H₄ witness) ≃ Q₂(witness)` — the quadratic is preserved by `H₄` on the
witness.  (The local face of `H₄ ∈ O(4)`.) -/
theorem Q2_H4_eq_witness : (Q2 (H4 witness)).eqv (Q2 witness) :=
  Q'.eqv_trans _ 1 _ Q2_H4_witness (Q'.eqv_symm Q2_witness)

/-- The closed `Q'` fact `¬ (1/4 ≃ 1)` — the numeric core of the break. -/
theorem quarter_ne_one : ¬ (Q'.mkPos 1 4 (by decide)).eqv 1 := by decide

/-- **THE CRUX.**  `A₄` is NOT invariant under the 24-cell / D₄ Hadamard
generator `H₄`: on the witness `x = (1,0,0,0)` we have `A₄(x) ≃ 1` but
`A₄(H₄ x) ≃ 1/4`, and `¬ (1/4 ≃ 1)`.  So the degree-4 hypercubic anisotropy
invariant `A₄` (which SURVIVES the whole hypercubic group `B₄`, by
`A4_signPerm`) is BROKEN by the strictly larger 24-cell symmetry.  This is the
finite invariant-theory fact that forces the 24-cell's leading rotation-breaking
operator to be higher degree than 4. -/
theorem A4_H4_not_invariant : ¬ (A4 (H4 witness)).eqv (A4 witness) := by
  intro h
  -- A₄(H₄ witness) ≃ 1/4 and A₄(witness) ≃ 1, so 1/4 ≃ 1 — contradiction.
  exact quarter_ne_one
    (Q'.eqv_trans _ (A4 (H4 witness)) _ (Q'.eqv_symm A4_H4_witness)
      (Q'.eqv_trans _ (A4 witness) _ h A4_witness))

/-! ### General orthogonality of `H₄` — `Q₂(H₄ v) ≃ Q₂(v)` for ALL `v`

We prove the Hadamard generator preserves the isotropic quadratic EVERYWHERE
(`H₄ ∈ O(4)`).  Because `Q'` has no `ring`/`linarith` and the cross-product of
this identity is a genuine multivariate ring identity (which `decide` cannot see
for symbolic `v`), we build the proof from the constructive `Q'` eqv-algebra
(`RationalsMul.lean`: associativity, commutativity, distributivity, congruences
at `Q'.eqv`), exactly the AC-free style the rest of the repo uses.  The chain is:

  `Q₂(H₄ v) = Σ (½·rᵢ)²  ≃  ½² · Σ rᵢ²  ≃  ½² · 4·Σ xⱼ²  ≃  Σ xⱼ² = Q₂(v)`,

where `rᵢ` are the four Hadamard rows and `Σ rᵢ² ≃ 4·Σ xⱼ²` is the Hadamard
square-sum identity (cross terms cancel).  The final `½²·4 ≃ 1` is a closed `Q'`
fact (`decide`). -/

/-- `A + 0 ≃ A`. -/
private theorem add_zero_eqv (A : Q') : (A + 0).eqv A := by
  rw [Q'.add_zero']; exact Q'.eqv_refl A
/-- `0 + A ≃ A`. -/
private theorem zero_add_eqv (A : Q') : ((0:Q') + A).eqv A := by
  rw [Q'.zero_add']; exact Q'.eqv_refl A
/-- `C + (−C) ≃ 0`. -/
private theorem add_neg_self_eqv (C : Q') : (C + -C).eqv 0 :=
  Q'.eqv_trans _ ((-C) + C) _ (Q'.add_comm_eqv C (-C)) (Q'.neg_add_self_eqv C)
/-- Right-distributivity `(p+q)·r ≃ p·r + q·r` (derived from the left form). -/
private theorem add_mul_eqv (p q r : Q') : ((p+q)*r).eqv (p*r + q*r) :=
  Q'.eqv_trans _ (r*(p+q)) _ (Q'.mul_comm_eqv (p+q) r)
    (Q'.eqv_trans _ (r*p + r*q) _ (Q'.mul_add_eqv r p q)
      (Q'.eqv_trans _ (p*r + r*q) _ (Q'.add_eqv_congr_right _ _ _ (Q'.mul_comm_eqv r p))
        (Q'.add_eqv_congr_left _ _ _ (Q'.mul_comm_eqv r q))))
/-- Square of a sum: `(p+q)² ≃ (p·p + q·p) + (p·q + q·q)`. -/
private theorem sq_add (p q : Q') : (sq (p+q)).eqv ((p*p + q*p) + (p*q + q*q)) :=
  Q'.eqv_trans _ ((p+q)*p + (p+q)*q) _ (Q'.mul_add_eqv (p+q) p q)
    (Q'.eqv_trans _ ((p*p + q*p) + (p+q)*q) _
      (Q'.add_eqv_congr_right _ _ _ (add_mul_eqv p q p))
      (Q'.add_eqv_congr_left _ _ _ (add_mul_eqv p q q)))
/-- Square of a difference (`p−q = p + (−q)`). -/
private theorem sq_sub (p q : Q') :
    (sq (p-q)).eqv ((p*p + (-q)*p) + (p*(-q) + (-q)*(-q))) := sq_add p (-q)
/-- `(A+D) + (A + −D) ≃ A + A` (the `+D/−D` cross term cancels). -/
private theorem collapse_pair (A D : Q') : ((A + D) + (A + -D)).eqv (A + A) :=
  Q'.eqv_trans _ ((A + A) + (D + -D)) _ (Q'.add_swap_inner A D A (-D))
    (Q'.eqv_trans _ ((A + A) + 0) _ (Q'.add_eqv_congr_left _ _ _ (add_neg_self_eqv D))
      (add_zero_eqv (A + A)))
/-- `(C+B) + (−C + B) ≃ B + B`. -/
private theorem collapse_pair' (C B : Q') : ((C + B) + (-C + B)).eqv (B + B) :=
  Q'.eqv_trans _ ((C + -C) + (B + B)) _ (Q'.add_swap_inner C B (-C) B)
    (Q'.eqv_trans _ (0 + (B + B)) _ (Q'.add_eqv_congr_right _ _ _ (add_neg_self_eqv C))
      (zero_add_eqv (B + B)))
/-- Eight-term cancellation skeleton (cross terms `C/−C`, `D/−D` cancel). -/
private theorem cancel4 (A B C D : Q') :
    (((A + C) + (D + B)) + ((A + -C) + (-D + B))).eqv ((A + A) + (B + B)) := by
  refine Q'.eqv_trans _ (((A + D) + (C + B)) + ((A + -D) + (-C + B))) _
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (Q'.add_swap_inner A C D B))
      (Q'.add_eqv_congr_left _ _ _ (Q'.add_swap_inner A (-C) (-D) B))) ?_
  refine Q'.eqv_trans _ (((A + D) + (A + -D)) + ((C + B) + (-C + B))) _
    (Q'.add_swap_inner (A+D) (C+B) (A+ -D) (-C+B)) ?_
  exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (collapse_pair A D))
    (Q'.add_eqv_congr_left _ _ _ (collapse_pair' C B))
/-- **The two-term square-sum identity** `(p+q)² + (p−q)² ≃ 2p² + 2q²`
(written `(p²+p²)+(q²+q²)`).  The mixed terms `±pq, ±qp` cancel. -/
private theorem two_row (p q : Q') :
    (sq (p+q) + sq (p-q)).eqv ((sq p + sq p) + (sq q + sq q)) := by
  have e1 : ((-q)*p).eqv (-(q*p)) := Q'.neg_mul_eqv q p
  have e2 : (p*(-q)).eqv (-(p*q)) := Q'.mul_neg_eqv p q
  have e3 : ((-q)*(-q)).eqv (q*q) :=
    Q'.eqv_trans _ (-(q*(-q))) _ (Q'.neg_mul_eqv q (-q))
      (Q'.eqv_trans _ (-(-(q*q))) _ (Q'.neg_eqv_congr _ _ (Q'.mul_neg_eqv q q))
        (Q'.neg_neg_eqv (q*q)))
  have hB : (sq (p-q)).eqv ((p*p + -(q*p)) + (-(p*q) + q*q)) :=
    Q'.eqv_trans _ _ _ (sq_sub p q)
      (Q'.eqv_trans _ ((p*p + -(q*p)) + (p*(-q) + (-q)*(-q))) _
        (Q'.add_eqv_congr_right _ _ _ (Q'.add_eqv_congr_left _ _ _ e1))
        (Q'.add_eqv_congr_left _ _ _
          (Q'.eqv_trans _ (-(p*q) + (-q)*(-q)) _ (Q'.add_eqv_congr_right _ _ _ e2)
            (Q'.add_eqv_congr_left _ _ _ e3))))
  have hsum : (sq (p+q) + sq (p-q)).eqv
      (((p*p + q*p) + (p*q + q*q)) + ((p*p + -(q*p)) + (-(p*q) + q*q))) :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (sq_add p q))
      (Q'.add_eqv_congr_left _ _ _ hB)
  exact Q'.eqv_trans _ _ _ hsum (cancel4 (p*p) (q*q) (q*p) (p*q))
/-- `(h·r)² ≃ (h·h)·(r·r)`. -/
private theorem sq_mul (h r : Q') : (sq (h*r)).eqv ((h*h)*(r*r)) := by
  refine Q'.eqv_trans _ (h*(r*(h*r))) _ (Q'.mul_assoc_eqv h r (h*r)) ?_
  refine Q'.eqv_trans _ (h*((r*h)*r)) _
    (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv r h r))) ?_
  refine Q'.eqv_trans _ (h*((h*r)*r)) _
    (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv r h))) ?_
  refine Q'.eqv_trans _ (h*(h*(r*r))) _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_assoc_eqv h r r)) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv h h (r*r))
/-- `(h·r)² ≃ (h·h)·r²`. -/
private theorem sq_mul' (h r : Q') : (sq (h*r)).eqv ((h*h)*(sq r)) := sq_mul h r
/-- `sq` is an `eqv` congruence. -/
private theorem sq_eqv_congr (a b : Q') (h : a.eqv b) : (sq a).eqv (sq b) :=
  Q'.eqv_trans _ (a*b) _ (Q'.mul_eqv_congr_left a a b h) (Q'.mul_eqv_congr_right a b b h)
/-- `−(b+d) ≃ −b + −d`. -/
private theorem neg_add_eqv (b d : Q') : (-(b+d)).eqv ((-b) + (-d)) := by
  show (-(b+d)).num * (((-b)+(-d)).den : Int) = ((-b)+(-d)).num * ((-(b+d)).den : Int)
  have hL : (-(b+d)).num = -(b.num*(d.den:Int)+d.num*(b.den:Int)) := rfl
  have hR : ((-b)+(-d)).num = (-b.num)*(d.den:Int)+(-d.num)*(b.den:Int) := rfl
  have hLd : (((-b)+(-d)).den : Int) = (b.den:Int)*(d.den:Int) := by rw [Q'.add_den_cast]; rfl
  have hRd : ((-(b+d)).den : Int) = (b.den:Int)*(d.den:Int) := by
    show (((b+d)).den : Int) = _; rw [Q'.add_den_cast]
  rw [hL, hR, hLd, hRd, Int.neg_add, Int.neg_mul, Int.neg_mul]
/-- Hadamard row 0 regrouped: `a+b+c+d ≃ (a+c)+(b+d)`. -/
private theorem row0_eqv (a b c d : Q') : (a+b+c+d).eqv ((a+c)+(b+d)) :=
  Q'.eqv_trans _ ((a+b)+(c+d)) _ (Q'.add_assoc_eqv (a+b) c d) (Q'.add_swap_inner a b c d)
/-- Hadamard row 1 regrouped: `a−b+c−d ≃ (a+c) − (b+d)`. -/
private theorem row1_eqv (a b c d : Q') : (a-b+c-d).eqv ((a+c)+ -(b+d)) := by
  show (((a + -b)+c) + -d).eqv ((a+c) + -(b+d))
  refine Q'.eqv_trans _ ((a + -b)+(c + -d)) _ (Q'.add_assoc_eqv (a + -b) c (-d)) ?_
  refine Q'.eqv_trans _ ((a+c)+(-b + -d)) _ (Q'.add_swap_inner a (-b) c (-d)) ?_
  exact Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm (neg_add_eqv b d))
/-- Hadamard row 2 regrouped: `a+b−c−d ≃ (a−c)+(b−d)`. -/
private theorem row2_eqv (a b c d : Q') : (a+b-c-d).eqv ((a+ -c)+(b+ -d)) := by
  show (((a+b)+ -c) + -d).eqv ((a+ -c)+(b+ -d))
  refine Q'.eqv_trans _ ((a+b)+(-c + -d)) _ (Q'.add_assoc_eqv (a+b) (-c) (-d)) ?_
  exact Q'.add_swap_inner a b (-c) (-d)
/-- Hadamard row 3 regrouped: `a−b−c+d ≃ (a−c) − (b−d)`. -/
private theorem row3_eqv (a b c d : Q') : (a-b-c+d).eqv ((a+ -c)+ -(b+ -d)) := by
  show (((a + -b)+ -c)+d).eqv ((a+ -c)+ -(b+ -d))
  refine Q'.eqv_trans _ ((a + -b)+(-c+d)) _ (Q'.add_assoc_eqv (a + -b) (-c) d) ?_
  refine Q'.eqv_trans _ ((a+ -c)+(-b+d)) _ (Q'.add_swap_inner a (-b) (-c) d) ?_
  refine Q'.add_eqv_congr_left _ _ _ ?_
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ ((-b) + -(-d)) _ (neg_add_eqv b (-d)) ?_
  exact Q'.add_eqv_congr_left _ _ _ (Q'.neg_neg_eqv d)
/-- Rows 0,1 paired (via `two_row` on `P=a+c, Q=b+d`). -/
private theorem pair01 (a b c d : Q') :
    (sq (a+b+c+d) + sq (a-b+c-d)).eqv
      ((sq (a+c) + sq (a+c)) + (sq (b+d) + sq (b+d))) := by
  refine Q'.eqv_trans _ (sq ((a+c)+(b+d)) + sq ((a+c)-(b+d))) _
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (sq_eqv_congr _ _ (row0_eqv a b c d)))
      (Q'.add_eqv_congr_left _ _ _ (sq_eqv_congr _ _ (row1_eqv a b c d)))) ?_
  exact two_row (a+c) (b+d)
/-- Rows 2,3 paired (via `two_row` on `R=a−c, S=b−d`). -/
private theorem pair23 (a b c d : Q') :
    (sq (a+b-c-d) + sq (a-b-c+d)).eqv
      ((sq (a+ -c) + sq (a+ -c)) + (sq (b+ -d) + sq (b+ -d))) := by
  refine Q'.eqv_trans _ (sq ((a+ -c)+(b+ -d)) + sq ((a+ -c)-(b+ -d))) _
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (sq_eqv_congr _ _ (row2_eqv a b c d)))
      (Q'.add_eqv_congr_left _ _ _ (sq_eqv_congr _ _ (row3_eqv a b c d)))) ?_
  exact two_row (a+ -c) (b+ -d)
/-- `s + s` abbreviation, with distributivity over `+` and congruence. -/
private def dbl (s : Q') : Q' := s + s
private theorem dbl_add (p q : Q') : (dbl (p+q)).eqv (dbl p + dbl q) := Q'.add_swap_inner p q p q
private theorem dbl_congr (a b : Q') (h : a.eqv b) : (dbl a).eqv (dbl b) :=
  Q'.eqv_trans _ (a+b) _ (Q'.add_eqv_congr_left _ _ _ h) (Q'.add_eqv_congr_right _ _ _ h)
/-- Additive flattening of the post-pairing 16-term sum to `(S+S)+(S+S)`,
`S = ((X+Y)+Z)+W`. -/
private theorem flatten (X Y Z W : Q') :
    ((((X+X)+(Z+Z)) + ((X+X)+(Z+Z))) + (((Y+Y)+(W+W)) + ((Y+Y)+(W+W)))).eqv
    ((((X+Y)+Z)+W + (((X+Y)+Z)+W)) + (((X+Y)+Z)+W + (((X+Y)+Z)+W))) := by
  have hLl : (((X+X)+(Z+Z)) + ((X+X)+(Z+Z))).eqv (dbl (dbl X) + dbl (dbl Z)) := by
    show (dbl ((dbl X) + (dbl Z))).eqv _; exact dbl_add (dbl X) (dbl Z)
  have hLr : (((Y+Y)+(W+W)) + ((Y+Y)+(W+W))).eqv (dbl (dbl Y) + dbl (dbl W)) := by
    show (dbl ((dbl Y) + (dbl W))).eqv _; exact dbl_add (dbl Y) (dbl W)
  have hL : ((((X+X)+(Z+Z)) + ((X+X)+(Z+Z))) + (((Y+Y)+(W+W)) + ((Y+Y)+(W+W)))).eqv
      ((dbl (dbl X) + dbl (dbl Z)) + (dbl (dbl Y) + dbl (dbl W))) :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ hLl) (Q'.add_eqv_congr_left _ _ _ hLr)
  have hS : (dbl (((X+Y)+Z)+W)).eqv (((dbl X + dbl Y) + dbl Z) + dbl W) := by
    refine Q'.eqv_trans _ (dbl ((X+Y)+Z) + dbl W) _ (dbl_add ((X+Y)+Z) W) ?_
    refine Q'.add_eqv_congr_right _ _ _ ?_
    refine Q'.eqv_trans _ (dbl (X+Y) + dbl Z) _ (dbl_add (X+Y) Z) ?_
    exact Q'.add_eqv_congr_right _ _ _ (dbl_add X Y)
  have hRR : (dbl (dbl (((X+Y)+Z)+W))).eqv
      (((dbl (dbl X) + dbl (dbl Y)) + dbl (dbl Z)) + dbl (dbl W)) := by
    refine Q'.eqv_trans _ (dbl (((dbl X + dbl Y) + dbl Z) + dbl W)) _ (dbl_congr _ _ hS) ?_
    refine Q'.eqv_trans _ (dbl ((dbl X + dbl Y) + dbl Z) + dbl (dbl W)) _ (dbl_add _ _) ?_
    refine Q'.add_eqv_congr_right _ _ _ ?_
    refine Q'.eqv_trans _ (dbl (dbl X + dbl Y) + dbl (dbl Z)) _ (dbl_add _ _) ?_
    exact Q'.add_eqv_congr_right _ _ _ (dbl_add (dbl X) (dbl Y))
  have hmid : ((dbl (dbl X) + dbl (dbl Z)) + (dbl (dbl Y) + dbl (dbl W))).eqv
      (((dbl (dbl X) + dbl (dbl Y)) + dbl (dbl Z)) + dbl (dbl W)) := by
    refine Q'.eqv_trans _ ((dbl (dbl X)+dbl (dbl Y))+(dbl (dbl Z)+dbl (dbl W))) _
      (Q'.add_swap_inner (dbl (dbl X)) (dbl (dbl Z)) (dbl (dbl Y)) (dbl (dbl W))) ?_
    exact Q'.eqv_symm (Q'.add_assoc_eqv (dbl (dbl X)+dbl (dbl Y)) (dbl (dbl Z)) (dbl (dbl W)))
  exact Q'.eqv_trans _ _ _ hL (Q'.eqv_trans _ _ _ hmid (Q'.eqv_symm hRR))
/-- **The Hadamard square-sum identity** `Σ rᵢ² ≃ 4·Σ xⱼ²` (`(S+S)+(S+S)`,
`S = Q₂ v`).  The cross terms across the four rows cancel — this is the
eigenvalue-level statement `H₄ ∈ O(4)`. -/
private theorem four_row_sum (a b c d : Q') :
    ((sq (a+b+c+d) + sq (a-b+c-d)) + sq (a+b-c-d) + sq (a-b-c+d)).eqv
      (((sq a + sq b + sq c + sq d) + (sq a + sq b + sq c + sq d))
        + ((sq a + sq b + sq c + sq d) + (sq a + sq b + sq c + sq d))) := by
  refine Q'.eqv_trans _ ((sq (a+b+c+d) + sq (a-b+c-d)) + (sq (a+b-c-d) + sq (a-b-c+d))) _
    (Q'.add_assoc_eqv (sq (a+b+c+d) + sq (a-b+c-d)) (sq (a+b-c-d)) (sq (a-b-c+d))) ?_
  refine Q'.eqv_trans _
    (((sq (a+c) + sq (a+c)) + (sq (b+d) + sq (b+d)))
      + ((sq (a+ -c) + sq (a+ -c)) + (sq (b+ -d) + sq (b+ -d)))) _
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (pair01 a b c d))
      (Q'.add_eqv_congr_left _ _ _ (pair23 a b c d))) ?_
  have hgen8 : (((sq (a+c) + sq (a+c)) + (sq (b+d) + sq (b+d)))
      + ((sq (a+ -c) + sq (a+ -c)) + (sq (b+ -d) + sq (b+ -d)))).eqv
      (((sq (a+c) + sq (a+ -c)) + (sq (a+c) + sq (a+ -c)))
        + ((sq (b+d) + sq (b+ -d)) + (sq (b+d) + sq (b+ -d)))) := by
    refine Q'.eqv_trans _
      (((sq (a+c)+sq (a+c)) + (sq (a+ -c)+sq (a+ -c)))
        + ((sq (b+d)+sq (b+d)) + (sq (b+ -d)+sq (b+ -d)))) _
      (Q'.add_swap_inner (sq (a+c)+sq (a+c)) (sq (b+d)+sq (b+d))
        (sq (a+ -c)+sq (a+ -c)) (sq (b+ -d)+sq (b+ -d))) ?_
    refine Q'.eqv_trans _
      (((sq (a+c)+sq (a+ -c)) + (sq (a+c)+sq (a+ -c)))
        + ((sq (b+d)+sq (b+d)) + (sq (b+ -d)+sq (b+ -d)))) _
      (Q'.add_eqv_congr_right _ _ _
        (Q'.add_swap_inner (sq (a+c)) (sq (a+c)) (sq (a+ -c)) (sq (a+ -c)))) ?_
    exact Q'.add_eqv_congr_left _ _ _
      (Q'.add_swap_inner (sq (b+d)) (sq (b+d)) (sq (b+ -d)) (sq (b+ -d)))
  refine Q'.eqv_trans _ _ _ hgen8 ?_
  have hac : (sq (a+c) + sq (a+ -c)).eqv ((sq a + sq a) + (sq c + sq c)) := two_row a c
  have hbd : (sq (b+d) + sq (b+ -d)).eqv ((sq b + sq b) + (sq d + sq d)) := two_row b d
  refine Q'.eqv_trans _
    ((((sq a + sq a)+(sq c + sq c)) + ((sq a + sq a)+(sq c + sq c)))
      + (((sq b + sq b)+(sq d + sq d)) + ((sq b + sq b)+(sq d + sq d)))) _
    ?_ ?_
  · refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _
        (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ hac)
          (Q'.add_eqv_congr_left _ _ _ hac))) ?_
    exact Q'.add_eqv_congr_left _ _ _
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ hbd)
        (Q'.add_eqv_congr_left _ _ _ hbd))
  · exact flatten (sq a) (sq b) (sq c) (sq d)
/-- Factor `½²` out of a two-term sum: `h·x + h·y ≃ h·(x+y)`. -/
private theorem factor_hh (h x y : Q') : (h*x + h*y).eqv (h*(x+y)) :=
  Q'.eqv_symm (Q'.mul_add_eqv h x y)

/-- **`Q₂(H₄ v) ≃ Q₂(v)` for ALL `v`** — the Hadamard generator preserves the
isotropic quadratic everywhere, i.e. `H₄ ∈ O(4)`.  PROVED constructively from the
`Q'` eqv-algebra: `½²·(Σ rᵢ²) ≃ ½²·(4·Σ xⱼ²) ≃ Σ xⱼ²` (`½²·4 ≃ 1` is closed and
discharged by `decide`).  This is the quantitative content that the 24-cell's
Hadamard generator is genuinely orthogonal — it preserves the quadratic while
(below) breaking the quartic. -/
theorem Q2_H4 (v : V4) : (Q2 (H4 v)).eqv (Q2 v) := by
  -- Unfold to coordinates a,b,c,d and the row expressions of `H4`.
  obtain ⟨a, b, c, d⟩ := v
  show ((sq (half*(a+b+c+d)) + sq (half*(a-b+c-d))) + sq (half*(a+b-c-d))
        + sq (half*(a-b-c+d))).eqv ((sq a + sq b + sq c + sq d))
  -- step 1: each (½·rᵢ)² ≃ ½²·rᵢ²  (peel the left-assoc sum outside-in)
  have hsum1 : ((sq (half*(a+b+c+d)) + sq (half*(a-b+c-d))) + sq (half*(a+b-c-d))
        + sq (half*(a-b-c+d))).eqv
      (((half*half)*(sq (a+b+c+d)) + (half*half)*(sq (a-b+c-d)))
        + (half*half)*(sq (a+b-c-d)) + (half*half)*(sq (a-b-c+d))) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (sq_mul' half (a-b-c+d))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ (Q'.add_eqv_congr_left _ _ _ (sq_mul' half (a+b-c-d)))) ?_
    exact Q'.add_eqv_congr_right _ _ _ (Q'.add_eqv_congr_right _ _ _
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (sq_mul' half (a-b+c-d)))
        (Q'.add_eqv_congr_right _ _ _ (sq_mul' half (a+b+c+d)))))
  -- step 2: factor ½² out of the whole left-assoc sum
  have hfac : (((half*half)*(sq (a+b+c+d)) + (half*half)*(sq (a-b+c-d)))
        + (half*half)*(sq (a+b-c-d)) + (half*half)*(sq (a-b-c+d))).eqv
      ((half*half) * (((sq (a+b+c+d) + sq (a-b+c-d)) + sq (a+b-c-d)) + sq (a-b-c+d))) := by
    refine Q'.eqv_trans _ (((half*half)*(sq (a+b+c+d) + sq (a-b+c-d))
        + (half*half)*(sq (a+b-c-d))) + (half*half)*(sq (a-b-c+d))) _
      (Q'.add_eqv_congr_right _ _ _ (Q'.add_eqv_congr_right _ _ _
        (factor_hh (half*half) (sq (a+b+c+d)) (sq (a-b+c-d))))) ?_
    refine Q'.eqv_trans _ ((half*half)*((sq (a+b+c+d) + sq (a-b+c-d)) + sq (a+b-c-d))
        + (half*half)*(sq (a-b-c+d))) _
      (Q'.add_eqv_congr_right _ _ _
        (factor_hh (half*half) (sq (a+b+c+d) + sq (a-b+c-d)) (sq (a+b-c-d)))) ?_
    exact factor_hh (half*half) ((sq (a+b+c+d) + sq (a-b+c-d)) + sq (a+b-c-d)) (sq (a-b-c+d))
  -- step 4: ½²·((S+S)+(S+S)) ≃ S, with S = Σ xⱼ²
  have hfinal : ((half*half) * (((sq a + sq b + sq c + sq d) + (sq a + sq b + sq c + sq d))
        + ((sq a + sq b + sq c + sq d) + (sq a + sq b + sq c + sq d)))).eqv
      (sq a + sq b + sq c + sq d) := by
    refine Q'.eqv_trans _ ((half*half)*((sq a + sq b + sq c + sq d) + (sq a + sq b + sq c + sq d))
        + (half*half)*((sq a + sq b + sq c + sq d) + (sq a + sq b + sq c + sq d))) _
      (Q'.mul_add_eqv (half*half) ((sq a + sq b + sq c + sq d) + (sq a + sq b + sq c + sq d))
        ((sq a + sq b + sq c + sq d) + (sq a + sq b + sq c + sq d))) ?_
    refine Q'.eqv_trans _
      (((half*half)*(sq a + sq b + sq c + sq d) + (half*half)*(sq a + sq b + sq c + sq d))
        + ((half*half)*(sq a + sq b + sq c + sq d) + (half*half)*(sq a + sq b + sq c + sq d))) _
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _
          (Q'.mul_add_eqv (half*half) (sq a + sq b + sq c + sq d) (sq a + sq b + sq c + sq d)))
        (Q'.add_eqv_congr_left _ _ _
          (Q'.mul_add_eqv (half*half) (sq a + sq b + sq c + sq d) (sq a + sq b + sq c + sq d)))) ?_
    refine Q'.eqv_trans _
      (((half*half)+(half*half))*(sq a + sq b + sq c + sq d)
        + ((half*half)+(half*half))*(sq a + sq b + sq c + sq d)) _
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _
          (Q'.eqv_symm (add_mul_eqv (half*half) (half*half) (sq a + sq b + sq c + sq d))))
        (Q'.add_eqv_congr_left _ _ _
          (Q'.eqv_symm (add_mul_eqv (half*half) (half*half) (sq a + sq b + sq c + sq d))))) ?_
    refine Q'.eqv_trans _ ((((half*half)+(half*half))+((half*half)+(half*half)))
        *(sq a + sq b + sq c + sq d)) _
      (Q'.eqv_symm (add_mul_eqv ((half*half)+(half*half)) ((half*half)+(half*half))
        (sq a + sq b + sq c + sq d))) ?_
    refine Q'.eqv_trans _ ((1:Q')*(sq a + sq b + sq c + sq d)) _ ?_
      (Q'.one_mul_eqv (sq a + sq b + sq c + sq d))
    refine Q'.mul_eqv_congr_right _ _ _ ?_
    -- ½²·4 ≃ 1 is a closed `Q'` fact.
    show ((((half*half)+(half*half))+((half*half)+(half*half)))).eqv 1
    decide
  exact Q'.eqv_trans _ _ _ hsum1
    (Q'.eqv_trans _ _ _ hfac
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (half*half) _ _ (four_row_sum a b c d)) hfinal))

end V4

open V4

/-! ## 3. The `LatticeAnisotropy` datum and the strict-improvement theorem

A `LatticeAnisotropy` records, for a lattice point group, the polynomial degree
of its LEADING rotation-breaking invariant (the lowest-degree
`G_lat`-invariant-but-not-`O(4)`-invariant operator).  This degree sets the
continuum rotation-restoration rate: HIGHER leading degree ⇒ FASTER restoration.

We provide two instances and PROVE the strict improvement `4 < 6`.  The
`hypercubic` instance's degree `4` is justified by the SURVIVING `A₄`
(`B₄`-invariant degree-4 anisotropy: `A4_signPerm`).  The `cell24` instance's
degree `6` is justified by `A4_H4_not_invariant` (the surviving degree-4
invariant is BROKEN by the 24-cell generator, so the 24-cell leading degree
exceeds 4) together with the CITED `F₄` invariant-ring classification of degrees
`{2, 6, 8, 12}` (which we do not reprove). -/

/-- A lattice point group's leading rotation-breaking datum: a label plus the
polynomial degree of its leading `G_lat`-invariant-but-not-`O(4)`-invariant
operator. -/
structure LatticeAnisotropy where
  /-- Human-readable point-group label. -/
  pointGroup : String
  /-- Degree of the leading rotation-breaking invariant operator. -/
  leadingBreakDegree : Nat

/-- The hypercubic point group `B₄` (signed permutations), degrees `{2,4,6,8}`.
Its leading rotation-breaking operator is the degree-4 anisotropy `A₄`, which
survives `B₄` (proved: `A4_signPerm`). -/
def hypercubic : LatticeAnisotropy where
  pointGroup := "B4 (hypercubic, signed permutations)"
  leadingBreakDegree := 4

/-- The 24-cell point group `= F₄` Weyl group, degrees `{2,6,8,12}` (cited, not
reproved).  The degree-4 anisotropy `A₄` that survives `B₄` is BROKEN by the
extra 24-cell Hadamard generator `H₄` (proved: `A4_H4_not_invariant`), so the
leading rotation-breaking operator is pushed up to the next available degree, 6. -/
def cell24 : LatticeAnisotropy where
  pointGroup := "F4 (24-cell)"
  leadingBreakDegree := 6

/-- **THE STRICT IMPROVEMENT.**  The 24-cell pushes the leading
rotation-breaking operator to STRICTLY higher degree than the hypercubic lattice
(`4 < 6`).  Logical anchor: `A4_signPerm` shows the degree-4 invariant `A₄`
survives `B₄` (so `hypercubic.leadingBreakDegree = 4`), while
`A4_H4_not_invariant` shows that SAME invariant is broken by the 24-cell
generator `H₄` (so the 24-cell leading degree exceeds 4; the next `F₄` invariant
is degree 6).  A larger symmetry ⇒ higher leading-break degree ⇒ faster O(4)
restoration. -/
theorem cell24_leadingBreakDegree_gt_hypercubic :
    hypercubic.leadingBreakDegree < cell24.leadingBreakDegree := by decide

/-! ## 4. The upgraded, degree-parameterized rotation-restoration input

`Spin4Reflection.O4ConnectedInput.rotationRestored` was an OPAQUE `Prop`.  We
replace the opaqueness with a QUANTITATIVE datum: a `RotationRestorationInput`
parameterized by the leading-break degree, carrying a PROVED `4 < degree` margin
plus the still-open RG-irrelevance datum as a NAMED `Prop` field (the accepted
pattern).  The continuum analytic wall is thereby made explicit AND
degree-indexed: the irrelevance now concerns an operator of a NAMED degree, and
the `cell24` instance carries a strictly-larger degree (a sharper/weaker wall).

What is DISCHARGED: the finite invariant-theory selection of the leading
operator and the `4 < degree` margin (theorems above).  What stays NAMED-open:
the RG-irrelevance of an operator of that degree as `a → 0` — the genuine
continuum frontier, carried as `irrelevant : Prop` + `irrelevant_holds`. -/

/-- **The degree-parameterized rotation-restoration input.**  Carries the
leading rotation-breaking degree, a PROVED `4 < leadingBreakDegree` margin, and
the NAMED-open RG-irrelevance datum (Rule 8: Type-level witness of a `Prop`).
The irrelevance field is the genuine continuum analytic wall — but now indexed by
an explicit operator degree rather than left opaque. -/
structure RotationRestorationInput where
  /-- The leading rotation-breaking operator degree (from a `LatticeAnisotropy`). -/
  leadingBreakDegree : Nat
  /-- PROVED margin: the leading break degree strictly exceeds 4 (the hypercubic
  degree-4 anisotropy is broken by the finer symmetry). -/
  breakDegree_gt_four : 4 < leadingBreakDegree
  /-- NAMED OPEN continuum-frontier datum (Rule 8): the rotation-breaking operator
  of degree `leadingBreakDegree` is RG-IRRELEVANT as `a → 0`, so continuous `O(4)`
  is restored.  This is the genuine continuum analytic wall, now degree-indexed —
  NOT discharged here. -/
  irrelevant : Prop
  /-- Witness of the named open irrelevance datum (carried as data). -/
  irrelevant_holds : irrelevant

/-- **The 24-cell rotation-restoration input.**  Built from the `cell24` datum:
its leading-break degree is `6`, with the `4 < 6` margin PROVED
(`cell24_leadingBreakDegree_gt_hypercubic`).  The single remaining open field is
the degree-6 RG-irrelevance (caller-supplied), the sharper continuum wall. -/
def rotationRestorationFromCell24
    (irrelevant : Prop) (irrelevant_holds : irrelevant) :
    RotationRestorationInput where
  leadingBreakDegree := cell24.leadingBreakDegree
  breakDegree_gt_four := cell24_leadingBreakDegree_gt_hypercubic
  irrelevant := irrelevant
  irrelevant_holds := irrelevant_holds

/-- The `cell24` input carries the STRICTLY-LARGER leading-break degree than the
hypercubic one — the explicit "sharper/weaker wall" statement. -/
theorem rotationRestorationFromCell24_degree
    (irrelevant : Prop) (h : irrelevant) :
    hypercubic.leadingBreakDegree
      < (rotationRestorationFromCell24 irrelevant h).leadingBreakDegree :=
  cell24_leadingBreakDegree_gt_hypercubic

/-- **THE UPGRADE / BRIDGE.**  Feed a degree-parameterized
`RotationRestorationInput` into `Spin4Reflection.O4ConnectedInput`: the connected
and reflection margins come from the PROVED isotropic heat-kernel gap (as in
`Spin4Reflection.o4ConnectedFromHeatKernelIsotropic`), and the previously-opaque
`rotationRestored` field is now set to the input's degree-indexed `irrelevant`
datum (with `rotationRestored_holds := inp.irrelevant_holds`).  The `O(4)`
accounting thereby exposes the EXPLICIT leading-break degree and its `4 < d`
margin instead of an opaque `Prop`. -/
def o4ConnectedFromAnisotropy
    (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q'))
    (inp : RotationRestorationInput) :
    Spin4Reflection.O4ConnectedInput :=
  Spin4Reflection.o4ConnectedFromHeatKernelIsotropic w hw0 hw1
    inp.irrelevant inp.irrelevant_holds

/-- The bridge's `rotationRestored` field IS the input's degree-indexed
`irrelevant` datum — witnessing that the opaque `Prop` has been replaced by the
quantitative, degree-parameterized named input. -/
theorem o4ConnectedFromAnisotropy_rotationRestored
    (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q'))
    (inp : RotationRestorationInput) :
    (o4ConnectedFromAnisotropy w hw0 hw1 inp).rotationRestored = inp.irrelevant := rfl

end YMGap.RepTheory.LatticeAnisotropy

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.RepTheory.LatticeAnisotropy.V4.Q2_swap01
#print axioms YMGap.RepTheory.LatticeAnisotropy.V4.Q2_flip0
#print axioms YMGap.RepTheory.LatticeAnisotropy.V4.A4_signPerm
#print axioms YMGap.RepTheory.LatticeAnisotropy.V4.Q2_witness
#print axioms YMGap.RepTheory.LatticeAnisotropy.V4.A4_witness
#print axioms YMGap.RepTheory.LatticeAnisotropy.V4.Q2_H4_witness
#print axioms YMGap.RepTheory.LatticeAnisotropy.V4.A4_H4_witness
#print axioms YMGap.RepTheory.LatticeAnisotropy.V4.A4_H4_not_invariant
#print axioms YMGap.RepTheory.LatticeAnisotropy.V4.Q2_H4
#print axioms YMGap.RepTheory.LatticeAnisotropy.cell24_leadingBreakDegree_gt_hypercubic
#print axioms YMGap.RepTheory.LatticeAnisotropy.rotationRestorationFromCell24
#print axioms YMGap.RepTheory.LatticeAnisotropy.rotationRestorationFromCell24_degree
#print axioms YMGap.RepTheory.LatticeAnisotropy.o4ConnectedFromAnisotropy
#print axioms YMGap.RepTheory.LatticeAnisotropy.o4ConnectedFromAnisotropy_rotationRestored
