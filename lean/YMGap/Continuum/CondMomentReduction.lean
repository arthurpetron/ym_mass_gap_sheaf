/-
Track B / local-CLT — the CLEAN EQUIVALENT relocation of R1 onto conditional-second-moment
convexity, and the fermion-determinant (perfect-square) form of the continuum floor's leading face.

# What this module adds (read first — load-bearing honesty)

R1 = `CircleFourierPowerModel.SaddleVarianceFloor w` is the `−2` curvature floor on the FULL-range
theta-tilted position variance `V(t) = ⟨D²⟩_t = dmomNfull w t / acNfull w t`, i.e. `Δ²_t V ≥ −2`
for every window `s` (per-window face `FullRangeFloor w s`).

Set `n = p + 1`, `m = (t − p) + 1`, so `n + m = N := t + 2` and the fusion measure is two identical
particles with weight `g(k) = k·w^{k²}` conditioned on the total `n + m = N`.  The CONDITIONAL SECOND
MOMENT is `⟨n²⟩_N = ⟨(p+1)²⟩` under `μ_t`.  By the exact ledger `4⟨x⟩ + ⟨D²⟩ = t²`
(`EnvelopeClosure.covBridge`, `x_p = p(t−p)`, `D²_p = (t−2p)²`) together with the constant
curvature `Δ²((t+2)²) = 2` (`MeanComplementCovariance.sqEqv`), the symmetry `⟨D⟩_t = 0` of the
p ↔ t−p measure gives the exact dictionary

    4·⟨n²⟩_N = ⟨D²⟩_t + (t+2)²        (documented; the `⟨D⟩ = 0` symmetry is the one non-algebraic step)

so, taking the discrete second difference in `N` (= in `t`) and using `Δ²((t+2)²) = 2`,

    Δ²_N ⟨n²⟩_N = ¼·( Δ²_t ⟨D²⟩_t + 2 ) .

Therefore `⟨n²⟩_N` is DISCRETELY CONVEX in `N` (`Δ²⟨n²⟩ ≥ 0`) **iff** `Δ²⟨D²⟩ ≥ −2` = R1.  The `+2`
constant-curvature term is spent EXACTLY, turning the `−2`-floor into a bare convexity — a
Pólya-frequency conditional-variance-convexity, strictly better documented than the raw theta floor.

# What this module PROVES (all axiom-clean, `Type`-level, NO `sorry`)

  * `condSecondMoment w t := dmomNfull w t + (t+2)²·acNfull w t` — the CLEARED numerator of
    `4·⟨n²⟩_N` (subtraction-free: a nonneg moment plus a nonneg-scaled mass), `= 4·⟨(p+1)²⟩·acNfull`
    under `⟨D⟩ = 0`.
  * `condConvex_iff_fullFloor_core` / `condConvex_iff_fullFloor` — THE EXACT RECAST: the cleared
    convexity `CondSecondMomentConvex w s` is a ring-level `↔` with `FullRangeFloor w s` (the per-window
    face of R1).  Both directions, NO nonnegativity; the ONLY input is the constant-curvature relation
    `(s+2)² + (s+4)² = 2·(s+3)² + 2` (`sqEqv (s+2)`).  This makes the equivalence EXACT, not a
    one-way sufficient condition.
  * `saddleVarianceFloor_of_condMomentConvex` — a `CondSecondMomentConvexFloor w` witness inhabits R1
    `SaddleVarianceFloor w`; and `condMomentConvexFloor_of_saddleVarianceFloor` — the CONVERSE.  So the
    relocation is a genuine `⟺` (both bridges PROVED), not a strengthening.
  * `fermionDet_perfectSquare` / `continuumFloor_negSquare` — the fermion-determinant form of the
    continuum floor's leading (two-particle) face: with `A = Σ_{k odd} k w^{k²}`,
    `B = Σ_{k even} k w^{k²}`, `G_even = A²+B²`, `G_odd = 2AB`, one has
    `G_even − G_odd = (A−B)²`, hence `G_odd − G_even = −(A−B)² ≤ 0 ≤ 1` — the elliptic-modulus
    face (a) of `ContinuumShadowFloor` holds MANIFESTLY at the leading determinant, with room to spare.

# HONEST VERDICT — a strictly-sharper EQUIVALENT relocation, NOT a closure

`CondSecondMomentConvexFloor w` is EXACTLY as strong as R1 (`↔` per window, both bridges proved), so it
is a lossless, better-documented relocation — not a stronger residual smuggling the conclusion.  It is
NAMED-OPEN and deliberately UNINHABITED: producing a witness is R1 (open).  The fermion-determinant
identity records the perfect-square structure of the leading face of the continuum floor but does NOT
close it (the physical `ContinuumFloor` concerns the finite surrogate and the full 4-fermion object; the
limit `V(t) → G_parity` is documented, not formalized).  The Clay Yang–Mills mass gap remains OPEN.

# Axiom gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'` arithmetic: the reused subtraction-free `ring_qeqv` closer, one cancellation identity closed
by `ring` on the `Int` cross-product (`ring_qeqv_cancel`, the perfect square), the proved
`sqEqv`, and the order plumbing `le_of_eqvL/R`, `le_of_add_le_add_right`.  Every load-bearing
declaration is gated with `#print axioms`; permitted output is `propext` / `Quot.sound` only.  No
`Classical.*`, no `native_decide`, no `sorry`.  All witnesses are `Type`-level data.
-/

import YMGap.Continuum.EnvelopeClosure

namespace YMGap.Continuum.CondMomentReduction

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AutoconvGershgorin
open YMGap.Continuum.MeanComplementCovariance
open YMGap.Continuum.MeanExpConvexProgress
open YMGap.Continuum.CircleFourierPowerModel

/-! ## 1. The conditional second moment `⟨n²⟩` (cleared numerator) and its convexity residual. -/

/-- **`condSecondMoment w t`** — the CLEARED numerator of `4·⟨n²⟩_N`, `N = t + 2`, `n = p + 1`:

    condSecondMoment w t := dmomNfull w t + (t+2)²·acNfull w t .

Subtraction-free (a nonnegative antidiagonal-square moment `dmomNfull` plus a nonnegative-scaled mass
`acNfull`).  Under the p ↔ t−p symmetry `⟨D⟩_t = 0`, the termwise identity
`4(p+1)² = D²_p + (t+2)² − 2(t+2)D_p` sums to `4·⟨(p+1)²⟩·acNfull = dmomNfull + (t+2)²·acNfull`, so
`condSecondMoment w t = 4·⟨n²⟩_N·acNfull w t`.  (The `⟨D⟩ = 0` step is documented, not a Lean field;
the exact recast below needs only the algebraic definition.) -/
def condSecondMoment (w : Q') (t : Nat) : Q' :=
  dmomNfull w t + Q'.ofNat ((t + 2) * (t + 2)) * acNfull w t

/-- **`CondSecondMomentConvex w s`** — the cleared discrete convexity `Δ²_N ⟨n²⟩_N ≥ 0` at window `s`
(`N = s + 2`), i.e. `2·⟨n²⟩_{s+1} ≤ ⟨n²⟩_s + ⟨n²⟩_{s+2}`, cleared over the positive mass product
`acNfull_s · acNfull_{s+1} · acNfull_{s+2}` (the global factor `4` cancels).  NOTE: NO `+2` on the
right — the constant curvature `Δ²((t+2)²) = 2` is already spent inside `condSecondMoment`, so the
`−2`-floor of R1 becomes a bare convexity. -/
def CondSecondMomentConvex (w : Q') (s : Nat) : Prop :=
  Q'.ofNat 2 * (condSecondMoment w (s + 1) * (acNfull w s * acNfull w (s + 2)))
    ≤ condSecondMoment w s * (acNfull w (s + 1) * acNfull w (s + 2))
      + condSecondMoment w (s + 2) * (acNfull w s * acNfull w (s + 1))

/-- **`CondSecondMomentConvexFloor w`** — the uniform-in-`s` conditional-second-moment convexity: for
every window `s`, `⟨n²⟩_N` is discretely convex in `N`.  This is the CLEAN EQUIVALENT of R1
(`SaddleVarianceFloor`), a Pólya-frequency conditional-variance-convexity.  NAMED-OPEN (never `sorry`;
a witness IS R1, which is open). -/
structure CondSecondMomentConvexFloor (w : Q') : Type where
  convex : ∀ s, CondSecondMomentConvex w s

/-! ## 2. THE EXACT RECAST — `CondSecondMomentConvex ⟺ FullRangeFloor` (pure-`Q'` core). -/

/-- **`condConvex_iff_fullFloor_core`** — the abstract ring-level equivalence between the cleared
conditional-second-moment convexity (LEFT) and the `−2` position-variance floor `FullRangeFloor`
(RIGHT), given ONLY the constant-curvature relation `k0 + k2 ≃ two·k1 + two` (`Δ²((t+2)²) = 2`).

Both directions are proved by rewriting LEFT and RIGHT through the SAME extra term
`E := two·(k1·(A0·(A1·A2)))` — `LHScond ≃ Lfloor + E` (pure ring) and `RHScond ≃ Rfloor + E` (ring +
one curvature congruence) — and cancelling `E`.  NO nonnegativity, NO analysis: the constant-curvature
`+2` is spent EXACTLY, so the convexity and the `−2`-floor are literally the same inequality. -/
theorem condConvex_iff_fullFloor_core
    (A0 A1 A2 D0 D1 D2 k0 k1 k2 two : Q')
    (hk : (k0 + k2).eqv (two * k1 + two)) :
    ( two * ((D1 + k1 * A1) * (A0 * A2))
        ≤ (D0 + k0 * A0) * (A1 * A2) + (D2 + k2 * A2) * (A0 * A1) )
    ↔
    ( two * (D1 * (A0 * A2))
        ≤ D0 * (A1 * A2) + D2 * (A0 * A1) + two * (A0 * (A1 * A2)) ) := by
  -- LEFT ≃ Lfloor + E
  have eqL :
      (two * ((D1 + k1 * A1) * (A0 * A2))).eqv
        (two * (D1 * (A0 * A2)) + two * (k1 * (A0 * (A1 * A2)))) := by ring_qeqv
  -- RIGHT ≃ Rfloor + E   (via the curvature relation `hk`)
  have eqR :
      ((D0 + k0 * A0) * (A1 * A2) + (D2 + k2 * A2) * (A0 * A1)).eqv
        ((D0 * (A1 * A2) + D2 * (A0 * A1) + two * (A0 * (A1 * A2)))
          + two * (k1 * (A0 * (A1 * A2)))) := by
    have r1 :
        ((D0 + k0 * A0) * (A1 * A2) + (D2 + k2 * A2) * (A0 * A1)).eqv
          ((D0 * (A1 * A2) + D2 * (A0 * A1)) + (k0 + k2) * (A0 * (A1 * A2))) := by ring_qeqv
    have r2 :
        ((D0 * (A1 * A2) + D2 * (A0 * A1)) + (k0 + k2) * (A0 * (A1 * A2))).eqv
          ((D0 * (A1 * A2) + D2 * (A0 * A1)) + (two * k1 + two) * (A0 * (A1 * A2))) :=
      Q'.add_eqv_congr_left (D0 * (A1 * A2) + D2 * (A0 * A1)) _ _
        (Q'.mul_eqv_congr_right (k0 + k2) (two * k1 + two) (A0 * (A1 * A2)) hk)
    have r3 :
        ((D0 * (A1 * A2) + D2 * (A0 * A1)) + (two * k1 + two) * (A0 * (A1 * A2))).eqv
          ((D0 * (A1 * A2) + D2 * (A0 * A1) + two * (A0 * (A1 * A2)))
            + two * (k1 * (A0 * (A1 * A2)))) := by ring_qeqv
    exact Q'.eqv_trans _ _ _ r1 (Q'.eqv_trans _ _ _ r2 r3)
  constructor
  · intro h
    -- h : LHScond ≤ RHScond ;  rewrite both sides, cancel E
    have h1 := le_of_eqvR (le_of_eqvL (Q'.eqv_symm eqL) h) eqR
    exact le_of_add_le_add_right h1
  · intro h
    -- h : Lfloor ≤ Rfloor ;  add E to both, rewrite back
    have h1 := Q'.add_le_add_right _ _ (two * (k1 * (A0 * (A1 * A2)))) h
    exact le_of_eqvR (le_of_eqvL eqL h1) (Q'.eqv_symm eqR)

/-- **`condConvex_iff_fullFloor` — THE EXACT RECAST (over the genuine objects).**  The cleared
conditional-second-moment convexity `CondSecondMomentConvex w s` is EXACTLY the per-window `−2` floor
`FullRangeFloor w s`.  A ring-level `↔`, both directions, over the genuine `acNfull`/`dmomNfull`; the
sole input is the constant curvature `(s+2)²+(s+4)² = 2·(s+3)²+2` (`sqEqv (s+2)`). -/
theorem condConvex_iff_fullFloor (w : Q') (s : Nat) :
    CondSecondMomentConvex w s ↔ FullRangeFloor w s :=
  condConvex_iff_fullFloor_core
    (acNfull w s) (acNfull w (s + 1)) (acNfull w (s + 2))
    (dmomNfull w s) (dmomNfull w (s + 1)) (dmomNfull w (s + 2))
    (Q'.ofNat ((s + 2) * (s + 2))) (Q'.ofNat ((s + 1 + 2) * (s + 1 + 2)))
    (Q'.ofNat ((s + 2 + 2) * (s + 2 + 2))) (Q'.ofNat 2)
    (sqEqv (s + 2))

/-! ## 3. THE RELOCATION (both bridges) — R1 ⟺ conditional-second-moment convexity. -/

/-- **`saddleVarianceFloor_of_condMomentConvex` — THE RELOCATION (⟸).**  A uniform
`CondSecondMomentConvexFloor w` witness inhabits R1 `SaddleVarianceFloor w`: apply
`condConvex_iff_fullFloor` forward per window.  This relocates R1 onto the clean, general,
literature-recognizable conditional-variance-convexity residual. -/
def saddleVarianceFloor_of_condMomentConvex {w : Q'}
    (C : CondSecondMomentConvexFloor w) : SaddleVarianceFloor w where
  floor := fun s => (condConvex_iff_fullFloor w s).mp (C.convex s)

/-- **`condMomentConvexFloor_of_saddleVarianceFloor` — THE CONVERSE (⟹).**  R1
`SaddleVarianceFloor w` inhabits `CondSecondMomentConvexFloor w`: apply `condConvex_iff_fullFloor`
backward per window.  Together with `saddleVarianceFloor_of_condMomentConvex` this proves the
relocation is a genuine `⟺` (Rule 6a.5 / Rule 9.8: an EQUIVALENT reformulation, not a strengthening). -/
def condMomentConvexFloor_of_saddleVarianceFloor {w : Q'}
    (R : SaddleVarianceFloor w) : CondSecondMomentConvexFloor w where
  convex := fun s => (condConvex_iff_fullFloor w s).mpr (R.floor s)

/-! ## 4. By-product — the fermion-determinant (perfect-square) form of the continuum floor. -/

/-- **`fermionDet_gap`** — the two-particle spin-structure identity, cleared over `Q'`:

    G_even − G_odd = (A − B)²,   i.e.   (A − B)² = (A² + B²) − 2·A·B ,

with `A = Σ_{k odd} k·w^{k²}`, `B = Σ_{k even} k·w^{k²}` the odd/even single-particle theta partial
sums, `G_even = A²+B²` (NS-like, `n,m` same parity), `G_odd = 2AB` (R-like, opposite parity).  So
`G_odd − G_even = −(A−B)²` is a NEGATIVE perfect square — a fermionic determinant / Pfaffian of the
two-particle problem.  (Two-copy shadow of the project's 4-fermion `G_odd − G_even = ϑ₄(w²)⁴`; the
`A, B` are theta half-period pieces.  The `w → limit` identification of `G_parity` with the
theta-lattice variance is documented, not formalized.)  Proof mirrors the `CRealAlg.amgm_two`
binomial expansion. -/
theorem fermionDet_gap (A B : Q') :
    ((A + -B) * (A + -B)).eqv ((A * A + B * B) + -(Q'.ofNat 2 * (A * B))) := by
  have e1 : ((A + -B) * (A + -B)).eqv (A * (A + -B) + (-B) * (A + -B)) :=
    Q'.add_mul_eqv A (-B) (A + -B)
  have e2 : (A * (A + -B)).eqv (A * A + A * (-B)) := Q'.mul_add_eqv A A (-B)
  have e3 : ((-B) * (A + -B)).eqv ((-B) * A + (-B) * (-B)) := Q'.mul_add_eqv (-B) A (-B)
  have hAnB : (A * (-B)).eqv (-(A * B)) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv A (-B)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv B A) ?_
    exact Q'.neg_eqv_congr _ _ (Q'.mul_comm_eqv B A)
  have hnBA : ((-B) * A).eqv (-(A * B)) := by
    refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv B A) ?_
    exact Q'.neg_eqv_congr _ _ (Q'.mul_comm_eqv B A)
  have hnBnB : ((-B) * (-B)).eqv (B * B) := by
    refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv B (-B)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.mul_comm_eqv B (-B))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.neg_mul_eqv B B)) ?_
    exact Q'.neg_neg_eqv (B * B)
  have hexp : ((A + -B) * (A + -B)).eqv
      ((A * A + -(A * B)) + (-(A * B) + B * B)) := by
    refine Q'.eqv_trans _ _ _ e1 ?_
    refine Q'.add_eqv_congr' ?_ ?_
    · exact Q'.eqv_trans _ _ _ e2 (Q'.add_eqv_congr_left (A * A) _ _ hAnB)
    · refine Q'.eqv_trans _ _ _ e3 ?_
      exact Q'.add_eqv_congr' hnBA hnBnB
  have hregroup : ((A * A + -(A * B)) + (-(A * B) + B * B)).eqv
      ((A * A + B * B) + (-(A * B) + -(A * B))) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv (-(A * B)) (B * B))) ?_
    exact Q'.eqv_symm (Q'.add_swap_inner (A * A) (B * B) (-(A * B)) (-(A * B)))
  have hneg : (-(A * B) + -(A * B)).eqv (-(Q'.ofNat 2 * (A * B))) := by
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.neg_add_eqv (A * B) (A * B))) ?_
    exact Q'.neg_eqv_congr _ _ (Q'.eqv_symm (XMeanSecondDiffProgress.two_mul_eqv (A * B)))
  refine Q'.eqv_trans _ _ _ hexp (Q'.eqv_trans _ _ _ hregroup ?_)
  exact Q'.add_eqv_congr_left _ _ _ hneg

/-- **`continuumFloor_negSquare`** — the leading continuum-floor face `G_odd − G_even = −(A − B)²`
is a NEGATIVE perfect square, hence `≤ 0`.  This TIGHTENS face (a) of `ContinuumShadowFloor`
(`G_odd − G_even ≤ 1`): at the leading two-particle determinant the elliptic-modulus bound holds
MANIFESTLY (`−(A−B)² ≤ 0 ≤ 1`), with room to spare.  Rendered as `G_odd = 2AB ≤ A²+B² = G_even`
(the two-term AM-GM `CRealAlg.amgm_two`, whose sum-of-squares gap is exactly `fermionDet_gap`). -/
theorem continuumFloor_negSquare (A B : Q') :
    Q'.ofNat 2 * (A * B) ≤ A * A + B * B :=
  le_of_eqvL (XMeanSecondDiffProgress.two_mul_eqv (A * B)) (CRealAlg.amgm_two A B)

/-! ## 5. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean):
  * `condConvex_iff_fullFloor_core`, `condConvex_iff_fullFloor` — THE EXACT RECAST
    `CondSecondMomentConvex w s ⟺ FullRangeFloor w s` (per window; ring-level, both directions).
  * `saddleVarianceFloor_of_condMomentConvex` (⟸) and
    `condMomentConvexFloor_of_saddleVarianceFloor` (⟹) — R1 `⟺` conditional-second-moment convexity,
    BOTH bridges, so the relocation is EQUIVALENT (not a strengthening).
  * `fermionDet_gap`, `continuumFloor_negSquare` — the perfect-square fermion-determinant
    form of the continuum floor's leading face (`G_odd − G_even = −(A−B)² ≤ 0 ≤ 1`).

NAMED OPEN (Type-level structure, never `sorry`):
  * `CondSecondMomentConvexFloor w` — the uniform-in-`s` discrete convexity of the conditional second
    moment `⟨n²⟩_N` in `N`; EXACTLY equivalent to R1 `SaddleVarianceFloor w`.  A Pólya-frequency
    conditional-variance-convexity — the cleanest, most literature-recognizable home of R1.  The
    windows `s = 0,…,6` are inhabited via `condConvex_iff_fullFloor` from the proved
    `CircleFourierPowerModel.fullRangeFloor_zero..six`; the residual is the uniform-in-`s` convexity.

DOCUMENTED (not a Lean field):
  * `4·⟨(p+1)²⟩·acNfull = dmomNfull + (t+2)²·acNfull` (the `⟨D⟩_t = 0` symmetry) — the interpretation
    of `condSecondMoment` as `4·⟨n²⟩·mass`; the exact recast needs only the algebraic definition.
  * `V(t) → G_parity(w)` and `G_even = A²+B²`, `G_odd = 2AB` — the `w → theta` limit; the finite
    perfect-square identity is `fermionDet_gap`.

HONEST VERDICT.  A strictly-sharper EQUIVALENT relocation of R1 onto conditional-second-moment
convexity (both bridges proved), plus the fermion-determinant record of the continuum floor's leading
face.  NOT a closure.  The Clay Yang–Mills mass gap remains OPEN. -/

end YMGap.Continuum.CondMomentReduction

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.CondMomentReduction.condConvex_iff_fullFloor_core
#print axioms YMGap.Continuum.CondMomentReduction.condConvex_iff_fullFloor
#print axioms YMGap.Continuum.CondMomentReduction.saddleVarianceFloor_of_condMomentConvex
#print axioms YMGap.Continuum.CondMomentReduction.condMomentConvexFloor_of_saddleVarianceFloor
#print axioms YMGap.Continuum.CondMomentReduction.fermionDet_gap
#print axioms YMGap.Continuum.CondMomentReduction.continuumFloor_negSquare
