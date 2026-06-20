/-
Track B / R2 — PILLAR 3 of the `w`-uniform Casimir-square moment: the
generalized exp-beats-poly KERNEL (proved unconditionally) and the dyadic
partition-UPPER bound (named), assembling the TAIL moment and inhabiting the
`TailMomentCert` of the moving-cutoff module.

# What this settles (and what it honestly does NOT)

The fully-`w`-uniform Casimir-square moment splits at the moving cutoff `S` into
a HEAD (`s < S`, Pillar 2, `≤ 2^q`, proved unconditionally elsewhere) and a TAIL
(`s ≥ S`).  The TAIL summand is

    (1−w)²·casimirSqTerm w N hZ q (S+k)  =  μ(S+k)·(1+y)^q·y²,    y = (1−w)·C₄(S+k).

Bounding the tail by a `w`-INDEPENDENT constant rests on two ingredients:

  (A) the **generalized exp-beats-poly kernel** `ofNat(k^j)·sᵏ ≤ 1` for
      `ofNat(2^j)·s ≤ 1` — the polynomial monomial `kʲ` beaten by the geometric
      `sᵏ` (the `Q'` seed of `yʲ·e^{−y/2} ≤ C`).  This GENERALIZES the degree-2
      kernel `geom_beats_sq` of `CasimirMoment` to ARBITRARY degree `j`, with an
      explicit `Nat` constant.  PROVED UNCONDITIONALLY here.

  (B) the **dyadic partition-UPPER bound** — `∑_{s} (s+1)²·w^{C₄(s)/2} ≤ K·τ^{−3/2}`
      matching the Pillar-1 LOWER bound `Zsum ≥ c·τ^{−3/2}` so the `τ^{−3/2}`'s
      CANCEL.  This is the genuinely hard, scale-resolving piece.  It is NOT proved
      here; it is REDUCED to ONE explicitly-named hypothesis `PartitionUpperDyadic`
      (a `Type`-level certificate carrying the `w`-independent tail constant and the
      windowed inequality) and the `TailMomentCert` is inhabited CONDITIONAL on it.

# Honest verdict (AGENTS.md Rule 6)

Ingredient (A) closes UNCONDITIONALLY (`geom_beats_pow`, the reusable kernel).
Ingredient (B) is carried as the named certificate `PartitionUpperDyadic`; the
`TailMomentCert` builder `mkTailMomentCert` and the conditional canonical assembly
`fullMode_gap_canonical_of_partition` consume it explicitly.  We do NOT claim the
canonical chain is unconditional: it rests on the named structural input
`PartitionUpperDyadic` (the dyadic partition-upper bound) plus the moving-cutoff
head-floor data.  This is NOT a 4D Yang–Mills gap proof.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, structural inductions, decidable facts; every
load-bearing declaration is `#print axioms`-gated (permitted: `propext` /
`Quot.sound`).  No `Classical.*`, no `native_decide`, no `sorry`.  All witnesses
are `Type`-level data.
-/

import YMGap.Continuum.MovingCutoff

namespace YMGap.Continuum.PartitionUpperBound

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.BondMovingMoment
open YMGap.Continuum.FullModeAssembly
open YMGap.Continuum.CasimirMoment
open YMGap.Continuum.MovingCutoff

/-! ## 1. The generalized exp-beats-poly KERNEL (ingredient A, UNCONDITIONAL)

`geom_beats_sq` (in `CasimirMoment`) proves `ofNat(k·k)·sᵏ ≤ 1` for `4s ≤ 1`,
i.e. the degree-2 monomial beaten by the geometric.  Here we GENERALIZE to an
arbitrary degree `j`: `ofNat(kʲ)·sᵏ ≤ 1` for `ofNat(2ʲ)·s ≤ 1`.  This is the
`Q'` seed of the half-exponential domination `yʲ·e^{−y/2} ≤ C_j`. -/

/-- `kʲ ≤ (2ʲ)ᵏ` (Nat).  PROOF: `k ≤ 2ᵏ` (`nat_le_two_pow`), so `kʲ ≤ (2ᵏ)ʲ =
2^{k·j} = (2ʲ)ᵏ`. -/
theorem nat_pow_le_two_pow_pow (j k : Nat) : k ^ j ≤ (2 ^ j) ^ k := by
  have hk : k ≤ 2 ^ k := nat_le_two_pow k
  calc k ^ j ≤ (2 ^ k) ^ j := Nat.pow_le_pow_left hk j
    _ = 2 ^ (k * j) := by rw [← Nat.pow_mul]
    _ = 2 ^ (j * k) := by rw [Nat.mul_comm]
    _ = (2 ^ j) ^ k := by rw [Nat.pow_mul]

/-- A four-factor middle-regroup `(A·B)·(C·D) ≃ (A·C)·(B·D)` (pure assoc/comm at
the num/den cross-product level).  Local copy (the `CasimirMoment` one is in a
different namespace path; we reprove the elementary identity to stay self-contained). -/
theorem mul_four_mid' (A B C D : Q') :
    ((A * B) * (C * D)).eqv ((A * C) * (B * D)) := by
  show ((A * B) * (C * D)).num * (((A * C) * (B * D)).den : Int)
      = ((A * C) * (B * D)).num * (((A * B) * (C * D)).den : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  push_cast
  ac_rfl

/-- **`ofNat(dᵏ)·sᵏ ≃ (ofNat d · s)ᵏ`** (distribute the power over the product),
for an arbitrary base `d : Nat`.  Generalizes `ofNat_four_pow_mul`. -/
theorem ofNat_pow_mul (d : Nat) (s : Q') :
    ∀ k, (Q'.ofNat (d ^ k) * s ^ k).eqv ((Q'.ofNat d * s) ^ k)
  | 0 => by
      rw [Q'.pow_zero, Q'.pow_zero]
      show (Q'.ofNat (d ^ 0) * (1 : Q')).eqv (1 : Q')
      have : d ^ 0 = 1 := rfl
      rw [this]
      exact Q'.eqv_trans _ _ _ (Q'.mul_one_eqv (Q'.ofNat 1)) (by decide)
  | k + 1 => by
      rw [Q'.pow_succ, Q'.pow_succ]
      -- LHS = ofNat(d^{k+1})·(s·s^k) ; RHS = (ofNat d·s)·(ofNat d·s)^k
      have hd : (Q'.ofNat (d ^ (k + 1))).eqv (Q'.ofNat d * Q'.ofNat (d ^ k)) := by
        have : d ^ (k + 1) = d * d ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
        rw [this]
        exact ofNat_mul_eqv d (d ^ k)
      -- LHS ≃ (ofNat d·ofNat(d^k))·(s·s^k) ≃ (ofNat d·s)·(ofNat(d^k)·s^k) ≃ (ofNatd·s)·(ofNatd·s)^k
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (s * s ^ k) hd) ?_
      refine Q'.eqv_trans _ _ _
        (mul_four_mid' (Q'.ofNat d) (Q'.ofNat (d ^ k)) s (s ^ k)) ?_
      exact Q'.mul_eqv_congr_left _ _ _ (ofNat_pow_mul d s k)

/-- **THE GENERALIZED EXP-BEATS-POLY KERNEL.**  For `0 ≤ s` with `ofNat(2ʲ)·s ≤ 1`
(`s ≤ 1/2ʲ`), the degree-`j`-weighted geometric term is bounded:

    ofNat(kʲ)·sᵏ  ≤  1   for every `k`.

PROOF.  `kʲ ≤ (2ʲ)ᵏ` (`nat_pow_le_two_pow_pow`), so `ofNat(kʲ)·sᵏ ≤
ofNat((2ʲ)ᵏ)·sᵏ ≃ (2ʲ·s)ᵏ ≤ 1ᵏ = 1`.  This is the arbitrary-degree
generalization of `CasimirMoment.geom_beats_sq` (`j = 2`, `2ʲ = 4`). -/
theorem geom_beats_pow {s : Q'} (j : Nat) (hs0 : (0 : Q') ≤ s)
    (h2js : Q'.ofNat (2 ^ j) * s ≤ 1) :
    ∀ k, Q'.ofNat (k ^ j) * s ^ k ≤ 1 := by
  intro k
  have hspow_nn : (0 : Q') ≤ s ^ k := Q'.pow_nonneg s hs0 k
  have hpoly : Q'.ofNat (k ^ j) ≤ Q'.ofNat ((2 ^ j) ^ k) :=
    ofNat_le_ofNat (nat_pow_le_two_pow_pow j k)
  have h1 : Q'.ofNat (k ^ j) * s ^ k ≤ Q'.ofNat ((2 ^ j) ^ k) * s ^ k :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hpoly hspow_nn
  refine Q'.le_trans' _ _ _ h1 ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (ofNat_pow_mul (2 ^ j) s k)) ?_
  have h2jsnn : (0 : Q') ≤ Q'.ofNat (2 ^ j) * s :=
    Q'.mul_nonneg _ _ (zero_le_ofNat _) hs0
  have hpow : (Q'.ofNat (2 ^ j) * s) ^ k ≤ (1 : Q') ^ k :=
    pow_le_pow_of_le h2jsnn h2js k
  exact Q'.le_trans' _ _ _ hpow (Q'.le_of_eqv (one_pow_eqv k))

/-! ## 2. PILLAR 3 (ingredient B) — the dyadic partition-UPPER residual (NAMED)

The `w`-uniform tail bound rests on the dyadic partition-UPPER estimate

    ∑_{S ≤ s < S+M} (s+1)²·w^{C₄(s)/2}  ≤  K·τ^{−3/2}

whose `τ^{−3/2}` CANCELS the Pillar-1 lower bound `Zsum ≥ c·τ^{−3/2}`, yielding a
`w`-INDEPENDENT tail constant.  This scale-resolving estimate is NOT proved here;
it is carried as the explicit `Type`-level certificate below.  We carry it in the
exact form the tail assembly consumes: the renormalized TAIL MOMENT past `S` is
bounded by a `w`-independent `Nat` constant, for every window. -/

/-- **The named dyadic partition-UPPER certificate (Pillar 3, ingredient B).**
For a fixed weight `w`, cutoff `S`, fusion degree `N`, and test power `q`, the
renormalized tail moment past `S` is bounded by a `w`-INDEPENDENT `Nat` constant
`Cwin`, uniformly over every window `M`.

This is EXACTLY the content the dyadic block partition-upper bound delivers (the
`(s+1)²·w^{C₄/2}` block sum `≍ τ^{−3/2}` cancelling `Zsum ≥ c·τ^{−3/2}`, with the
`(1+y)^q·y²·w^{C₄/2} ≤ C_q` damping supplied by `geom_beats_pow`).  It is the
single honest open piece, carried as data — NOT proved here. -/
structure PartitionUpperDyadic (w : Q') (N : Nat) (hZ : (0 : Q') < Zsum w N)
    (q S : Nat) : Type where
  /-- The `w`-independent tail constant. -/
  Cwin : Nat
  /-- The renormalized tail moment bound, for every window `M`. -/
  windowed : ∀ M,
    ((1 : Q') - w) * ((1 : Q') - w)
        * RationalTail.finSum (fun k => casimirSqTerm w N hZ q (S + k)) M
      ≤ Q'.ofNat Cwin

/-- **The tail-moment certificate from the named dyadic input.**  Repackages a
`PartitionUpperDyadic` certificate as the `TailMomentCert` consumed by the
moving-cutoff assembly `casimir_moment_uniform_of_named`.  CONDITIONAL on the
named input — no unconditional claim. -/
def mkTailMomentCert {w : Q'} {N : Nat} {hZ : (0 : Q') < Zsum w N} {q S : Nat}
    (pud : PartitionUpperDyadic w N hZ q S) : TailMomentCert w N hZ q S where
  Ctail := pud.Cwin
  tail_bound := pud.windowed

/-! ## 3. The fully-`w`-uniform moment, conditional on the named residual

We re-export the moving-cutoff assembly with the tail certificate produced from
the named dyadic input.  The constant `2^q + Cwin` is genuinely independent of
`w`; the only `w`-dependence remaining is in the head-floor hypotheses
`hy : ∀ s, s < S → yArg w s ≤ 1` (Pillar 2, the moving-cutoff calibration) and in
the named `pud`. -/

/-- **THE FULLY-`w`-UNIFORM CASIMIR-SQUARE MOMENT (conditional on `PartitionUpperDyadic`).**
Given the head floors (Pillar 2) and the named dyadic certificate `pud` (Pillar 3),
the renormalized Casimir-square moment is bounded by the `w`-independent constant
`2^q + Cwin`, for every window `M`.  This is the moving-cutoff analogue of
`CasimirMoment.casimir_moment_bound` with the cutoff now MOVING (`S = S(w)`) and the
constant genuinely `w`-uniform — modulo the single named residual `pud`. -/
theorem casimir_moment_uniform_of_partition {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (N : Nat) (hZ : (0 : Q') < Zsum w N) (q S : Nat)
    (hSN : S ≤ N) (hy : ∀ s, s < S → yArg w s ≤ (1 : Q'))
    (pud : PartitionUpperDyadic w N hZ q S) :
    ∀ M, ((1 : Q') - w) * ((1 : Q') - w) * casimirSqSum w N hZ q (S + M)
      ≤ Q'.ofNat (2 ^ q) + Q'.ofNat pud.Cwin :=
  casimir_moment_uniform_of_named hw0 hw1 N hZ q S hSN hy (mkTailMomentCert pud)

/-! ## 4. Honest wiring note — the renormalized vs. bare moment

The full-mode summability chain (`FullModeDefect.d_quad`) consumes the BARE moment
bound `casimirSqSum w N hZ q n ≤ M` with `M` `w`-independent (so the defect
`d = (1−w)²·casimirSqSum ≤ M·(1−w)²` DECAYS like `(1−w)² ≍ 1/k²`, giving the
convergent product).  At a FIXED cutoff `S` that bare bound is `casimir_moment_bound`
(`CasimirMoment`), with `M = casimirSqM q r S` — but it consumes the fixed-cutoff
inequalities that FAIL as `w → 1`.

The result proved here, `casimir_moment_uniform_of_partition`, is the RENORMALIZED
bound `(1−w)²·casimirSqSum ≤ 2^q + Cwin`.  At the MOVING cutoff `S = S(w) ≍ τ^{−1/2}`
the bare moment `casimirSqSum ≍ τ^{−2}` is genuinely UNBOUNDED in `w`, so only the
renormalized form is `w`-uniform.  Feeding it to the chain as a *bare* `casimirSqSum
≤ M` would be FALSE (it would assert `τ^{−2} ≤ const`).  We therefore do NOT wire a
`fullModeDefect_uniform` from this renormalized bound: doing so would silently force
a false `d_quad`.  The honest gap is the wiring lemma

    bare moment at moving cutoff  ⟹  the chain's `d_quad`,

which is NOT a one-line rewrite — it requires the moving cutoff `S = S(w_k)` to be
chosen so that the chain's per-step margin already carries the right power.  That
re-wiring (Pillar-3 ↦ chain) is left as the explicit next step; `geom_beats_pow`
(ingredient A) and `PartitionUpperDyadic` (ingredient B, named) are the inputs it
will consume. -/

end YMGap.Continuum.PartitionUpperBound

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.PartitionUpperBound.nat_pow_le_two_pow_pow
#print axioms YMGap.Continuum.PartitionUpperBound.ofNat_pow_mul
#print axioms YMGap.Continuum.PartitionUpperBound.geom_beats_pow
#print axioms YMGap.Continuum.PartitionUpperBound.mkTailMomentCert
#print axioms YMGap.Continuum.PartitionUpperBound.casimir_moment_uniform_of_partition
