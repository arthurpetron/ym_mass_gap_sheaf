/-
Track B / R2 — **From the conserved CReal margin BUDGET to a SPACING-UNIFORM
physical-gap FLOOR via a single sharp scalar RATE-MATCH; the reduction PROVED and
a concrete TUNED inhabitant exhibited.**

# Why this module exists (read first)

`CodynamicPhysFloor` supplied the conserved-margin half of the emergent physical
gap: for a `SelfSimilarTower b` with a strictly-positive UV exponent seed
`PosEv (T.w 0)` and any strictly-positive spacing schedule `A`, the genuine
physical gap

    physGapC N = (1 − sep N) · (1 / a_N)

is `PosEv` at EVERY scale (`physGapC_pos_tower`).  The OPEN content was the
SPACING-UNIFORM floor `UniformPhysGapFloor` — a single positive rational below
`physGapC N` for ALL `N` at once.

This module isolates exactly what makes that uniform floor exist, as the sharpest
possible scalar condition.

# The exact recursion

Write `m N = 1 − sep N` (margin), `r N = 1/a_N` (reciprocal spacing),
`G N = geomSumC (sep (N+1)) (b+1)`.  Under the self-similar flow law the margin
telescopes one step (`margin_stepC`):

    m N ≃ m (N+1) · G N,

so the physical gap obeys the EXACT per-step recursion

    physGapC N  =  m N · r N  ≃  m (N+1) · (G N · r N),
    physGapC (N+1)  =  m (N+1) · r (N+1).

Hence `physGapC` is monotone NON-DECREASING in `N` **iff** at every step

    G N · r N  ≤  r (N+1)          (equivalently  G N ≤ a_N / a_{N+1}),

the margin-vs-spacing RATE MATCH.  The geometric-sum factor `G N` is the rate at
which the dimensionless margin shrinks per block step; `a_N / a_{N+1}` is the rate
at which the spacing shrinks.  The gap survives the continuum limit precisely when
the former does not outrun the latter.

# What is PROVED here (honest)

  * `RateMatch` — the sharp per-step scalar: `(1/a_N)·G N ≤ 1/a_{N+1}`.
  * `physGapC_step` / `physGapC_ge_base` — from `RateMatch`, `physGapC` is
    `leEv`-monotone non-decreasing, so `physGapC 0 ≤ physGapC N` at every scale.
  * `crealFloor_of_rateMatch` — `RateMatch`, plus an explicit Type-level UV-gap
    floor at the coarsest scale (a positive rational below `physGapC 0`), inhabits
    the canonical spacing-uniform `CRealFloor`; the tower wrappers give the named
    `UniformPhysGapFloor` and the full `CRealContinuumGapResidual`.  (The UV floor
    is supplied as DATA, never extracted from a `Prop`-∃ — Rule 8.)
  * `rateMatch_of_scalar` — the genuinely-RATIONAL sufficient criterion
    `G N ≤ a_N / a_{N+1}` (i.e. `ρ_N ≥ 1`) implies `RateMatch`.
  * `tunedRateMatch` (rational `1/2` seed) and `tunedRateMatch_E` (irrational
    `e^{−1}` seed) — NON-VACUOUS green inhabitants of `RateMatch` for the
    GENUINELY VANISHING geometric spacing `a_N = (1/2)^N` (`r = 1/(b+1)`), where the
    rates match exactly (`G N = 1 + sep ≤ 2 = a_N/a_{N+1}`).
  * `tunedCRealFloor` / `tunedResidual` — the floored inhabitant for the `1/2`-seed
    model with the explicit UV floor `1 − 2/3 = 1/3`: a strictly-positive rational
    below `physGapC N` at EVERY scale of a real `a → 0` schedule.

# HONEST residual — the open dimensional-transmutation content

`RateMatch` for the PHYSICAL Yang–Mills flow (the true RG separators `sep N` and
the true asymptotic-freedom spacing schedule `a_N`) is the open content: it is the
assertion that the genuine margin-decay rate is matched by the genuine spacing
schedule.  The tuned inhabitants above are MODEL self-similar flows with a
hand-tuned spacing; they certify the reduced scalar condition is satisfiable and
non-vacuous, but they do not inhabit `RateMatch` for the physical theory.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure composition over the `CodynamicPhysFloor` / `CodynamicCRealFlow` backbones;
every carrier is `Type`-level data (the floor's `bound` field is a `Pi` of `leEv`,
never a `Prop`-∃ witness; the UV floor is supplied as explicit data).  Each
load-bearing declaration is gated with `#print axioms` (permitted: `propext` /
`Quot.sound`).  No `Classical.*`, no `native_decide`, no `sorry`.
-/

import YMGap.Continuum.CodynamicPhysFloor
import YMGap.Continuum.UnifiedContinuumFloor

namespace YMGap.Continuum.RateMatchFloor

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.TuranPositivity
open YMGap.Continuum.CodynamicCRealFlow
open YMGap.Continuum.CodynamicPhysFloor
open YMGap.Continuum.UnifiedContinuumFloor

/-! ## 1. Generic `CReal` order glue -/

/-- **`Equiv ⇒ leEv`** (local copy; the eventual one-directional order). -/
theorem leEv_of_equiv {A B : CReal} (h : CReal.Equiv A B) : CReal.leEv A B := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  exact ⟨N, fun n hn => (hN n hn).1⟩

/-- **`geRat` transfers through `Equiv`** (local copy; mirror of `leRat_of_equiv`). -/
theorem geRat_equiv_transfer {A B : CReal} {d : Q'} (h : CReal.Equiv A B)
    (hB : ExpPos.geRat B d) : ExpPos.geRat A d := by
  intro ε hε
  have hhε : (0 : Q') < HalfPow.half * ε := ExpNeg.half_mul_pos ε hε
  obtain ⟨N1, h1⟩ := h (HalfPow.half * ε) hhε
  obtain ⟨N2, h2⟩ := hB (HalfPow.half * ε) hhε
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have hn1 : N1 ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hn2 : N2 ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  refine Q'.le_trans' _ _ _ (h2 n hn2) ?_
  refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (HalfPow.half * ε) (h1 n hn1).2) ?_
  refine Q'.le_of_eqv (Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv (A.approx n) (HalfPow.half * ε) (HalfPow.half * ε)) ?_)
  exact Q'.add_eqv_congr_left (A.approx n) (HalfPow.half * ε + HalfPow.half * ε) ε
    (ExpNeg.two_halves ε)

/-- **`leEv X Y ⇒ Y − X ≥ 0`.** -/
theorem geRat_sub_of_leEv {X Y : CReal} (h : CReal.leEv X Y) :
    ExpPos.geRat (CReal.sub Y X) 0 := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  show (0 : Q') ≤ (Y.approx n + -(X.approx n)) + ε
  have hxy : X.approx n ≤ Y.approx n + ε := hN n hn
  have h0 : (0 : Q') ≤ (Y.approx n + ε) + -(X.approx n) := Q'.sub_nonneg_of_le hxy
  refine Q'.le_trans' _ _ _ h0 (Q'.le_of_eqv ?_)
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (Y.approx n) ε (-(X.approx n))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (Y.approx n) (ε + -(X.approx n))
    (-(X.approx n) + ε) (Q'.add_comm_eqv ε (-(X.approx n)))) ?_
  exact Q'.eqv_symm (Q'.add_assoc_eqv (Y.approx n) (-(X.approx n)) ε)

/-- **`Y − X ≥ 0 ⇒ leEv X Y`.** -/
theorem leEv_of_geRat_sub {X Y : CReal} (h : ExpPos.geRat (CReal.sub Y X) 0) :
    CReal.leEv X Y := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  have h0 : (0 : Q') ≤ (Y.approx n + -(X.approx n)) + ε := hN n hn
  have h0' : (0 : Q') ≤ (Y.approx n + ε) + -(X.approx n) := by
    refine Q'.le_trans' _ _ _ h0 (Q'.le_of_eqv ?_)
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (Y.approx n) (-(X.approx n)) ε) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (Y.approx n) (-(X.approx n) + ε)
      (ε + -(X.approx n)) (Q'.add_comm_eqv (-(X.approx n)) ε)) ?_
    exact Q'.eqv_symm (Q'.add_assoc_eqv (Y.approx n) ε (-(X.approx n)))
  exact Q'.le_of_sub_nonneg h0'

/-- **Multiply an eventual order by a nonnegative `CReal` on the left.** -/
theorem leEv_mul_left_nonneg {c X Y : CReal} (hc : ExpPos.geRat c 0)
    (h : CReal.leEv X Y) : CReal.leEv (CReal.mul c X) (CReal.mul c Y) := by
  apply leEv_of_geRat_sub
  have hsub : ExpPos.geRat (CReal.sub Y X) 0 := geRat_sub_of_leEv h
  have hmul : ExpPos.geRat (CReal.mul c (CReal.sub Y X)) 0 := CReal.mul_nonneg hc hsub
  have hd : CReal.Equiv (CReal.mul c (CReal.sub Y X))
      (CReal.sub (CReal.mul c Y) (CReal.mul c X)) := CReal.mul_sub c Y X
  exact geRat_equiv_transfer (CReal.Equiv.symm hd) hmul

/-- **`c ≤ c + D` (eventually) when `D ≥ 0`.**  `leEv (ofQ' c) (c + D)` from
`geRat D 0`. -/
theorem leEv_ofQ'_add_right {c : Q'} {D : CReal} (hD : ExpPos.geRat D 0) :
    CReal.leEv (CReal.ofQ' c) (CReal.add (CReal.ofQ' c) D) := by
  intro ε hε
  obtain ⟨N, hN⟩ := hD ε hε
  refine ⟨N, fun n hn => ?_⟩
  show c ≤ (c + D.approx n) + ε
  have h0 : (0 : Q') ≤ D.approx n + ε := hN n hn
  refine Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg c (D.approx n + ε) h0) (Q'.le_of_eqv ?_)
  exact Q'.eqv_symm (Q'.add_assoc_eqv c (D.approx n) ε)

/-- **The UV margin floor from a sound separator bound.**  If `sep ≤ r` then
`1 − r ≤ 1 − sep`: the rational margin `1 − r` is an eventual lower bound for the
real margin.  (`1 − sep ≃ (1 − r) + (r − sep)`, with `r − sep ≥ 0`.) -/
theorem leEv_oneSub_of_leRat {x : CReal} {r : Q'} (hle : CReal.leRat x r) :
    CReal.leEv (CReal.ofQ' (1 + -r)) (CReal.sub CReal.cone x) :=
  CReal.leEv_trans (leEv_ofQ'_add_right (geRat_sub_ofQ'_of_leRat hle))
    (leEv_of_equiv (CReal.Equiv.symm (sub_cone_split x r)))

/-! ## 2. The sharp scalar RATE-MATCH and the monotonicity reduction -/

/-- **THE SHARP PER-STEP RATE MATCH.**  At every scale the rescaled geometric-sum
factor does not exceed the next reciprocal spacing:

    (1 / a_N) · geomSumC (sep (N+1)) (b+1)  ≤  1 / a_{N+1}.

Equivalently `geomSumC (sep (N+1)) (b+1) ≤ a_N / a_{N+1}` — the margin-decay rate
is matched by the spacing-shrink rate.  This single scalar condition is the
cleanest form of dimensional transmutation; it is the sole open input to the
spacing-uniform physical-gap floor (§3). -/
def RateMatch (b : Nat) (s : Nat → CReal) (A : SpacingSchedule) : Prop :=
  ∀ N, CReal.leEv
    (CReal.mul (recipSpacingC A N) (geomSumC (s (N + 1)) (b + 1)))
    (recipSpacingC A (N + 1))

/-- **THE PER-STEP MONOTONICITY OF THE PHYSICAL GAP.**  Under the self-similar
flow law, a nonnegative margin `1 − sep (N+1) ≥ 0` and the per-step `RateMatch`
inequality, `physGapC N ≤ physGapC (N+1)` in the eventual order.  This is the exact
recursion `physGapC N ≃ m(N+1)·(G N·r N) ≤ m(N+1)·r(N+1) = physGapC (N+1)`. -/
theorem physGapC_step {b : Nat} {s : Nat → CReal} (hss : selfSimilarC b s)
    (A : SpacingSchedule) (N : Nat)
    (hm : ExpPos.geRat (CReal.sub CReal.cone (s (N + 1))) 0)
    (hrm : CReal.leEv (CReal.mul (recipSpacingC A N) (geomSumC (s (N + 1)) (b + 1)))
      (recipSpacingC A (N + 1))) :
    CReal.leEv (physGapC b s A N) (physGapC b s A (N + 1)) := by
  show CReal.leEv (CReal.mul (CReal.sub CReal.cone (s N)) (recipSpacingC A N))
      (CReal.mul (CReal.sub CReal.cone (s (N + 1))) (recipSpacingC A (N + 1)))
  have hms : CReal.Equiv (CReal.sub CReal.cone (s N))
      (CReal.mul (CReal.sub CReal.cone (s (N + 1))) (geomSumC (s (N + 1)) (b + 1))) :=
    margin_stepC hss N
  have hLHS : CReal.Equiv (CReal.mul (CReal.sub CReal.cone (s N)) (recipSpacingC A N))
      (CReal.mul (CReal.mul (CReal.sub CReal.cone (s (N + 1))) (geomSumC (s (N + 1)) (b + 1)))
        (recipSpacingC A N)) := CReal.mul_congr_left hms
  refine CReal.leEv_trans (leEv_of_equiv hLHS) ?_
  have hassoc : CReal.Equiv
      (CReal.mul (CReal.mul (CReal.sub CReal.cone (s (N + 1))) (geomSumC (s (N + 1)) (b + 1)))
        (recipSpacingC A N))
      (CReal.mul (CReal.sub CReal.cone (s (N + 1)))
        (CReal.mul (geomSumC (s (N + 1)) (b + 1)) (recipSpacingC A N))) :=
    CRealAlg.cmul_assoc _ _ _
  refine CReal.leEv_trans (leEv_of_equiv hassoc) ?_
  refine leEv_mul_left_nonneg hm ?_
  have hcomm : CReal.Equiv (CReal.mul (geomSumC (s (N + 1)) (b + 1)) (recipSpacingC A N))
      (CReal.mul (recipSpacingC A N) (geomSumC (s (N + 1)) (b + 1))) := CRealAlg.cmul_comm _ _
  exact CReal.leEv_trans (leEv_of_equiv hcomm) hrm

/-- **The physical gap dominates its UV value at every scale (under `RateMatch`).**
`physGapC 0 ≤ physGapC N` for all `N`, by iterating the per-step monotonicity
through `leEv`-transitivity. -/
theorem physGapC_ge_base {b : Nat} {s : Nat → CReal} (hss : selfSimilarC b s)
    (A : SpacingSchedule)
    (hmpos : ∀ N, ExpPos.geRat (CReal.sub CReal.cone (s (N + 1))) 0)
    (hrm : RateMatch b s A) :
    ∀ N, CReal.leEv (physGapC b s A 0) (physGapC b s A N)
  | 0 => CReal.leEv_refl _
  | N + 1 => CReal.leEv_trans (physGapC_ge_base hss A hmpos hrm N)
      (physGapC_step hss A N (hmpos N) (hrm N))

/-! ## 3. RATE-MATCH (+ a Type-level UV floor) ⇒ the spacing-uniform floor -/

/-- **THE REDUCTION — `RateMatch` propagates a UV floor to all scales.**  Given the
self-similar flow law, the per-scale margin nonnegativity, the per-step
`RateMatch`, and an EXPLICIT UV-gap floor `floor0 > 0` with
`ofQ' floor0 ≤ physGapC 0` at the coarsest scale, the canonical spacing-uniform
`CRealFloor` on `physGapC` is inhabited: monotonicity (`physGapC_ge_base`)
propagates the UV floor below `physGapC N` at EVERY scale.  The UV floor is
supplied as Type-level data (Rule 8); the genuine open content is the per-step
`RateMatch`. -/
def crealFloor_of_rateMatch {b : Nat} {s : Nat → CReal} (hss : selfSimilarC b s)
    (A : SpacingSchedule)
    (hmpos : ∀ N, ExpPos.geRat (CReal.sub CReal.cone (s (N + 1))) 0)
    (hrm : RateMatch b s A)
    (floor0 : Q') (hpos0 : (0 : Q') < floor0)
    (hbase0 : CReal.leEv (CReal.ofQ' floor0) (physGapC b s A 0)) :
    CRealFloor (physGapC b s A) where
  floor := floor0
  floor_pos := hpos0
  bound := fun N => CReal.leEv_trans hbase0 (physGapC_ge_base hss A hmpos hrm N)

/-- **Tower form — the named open wall `UniformPhysGapFloor` from `RateMatch`.** -/
def uniformPhysGapFloor_of_rateMatch {b : Nat} (T : SelfSimilarTower b)
    (hx : PosEv (T.w 0)) (A : SpacingSchedule) (hrm : RateMatch b (sep T) A)
    (floor0 : Q') (hpos0 : (0 : Q') < floor0)
    (hbase0 : CReal.leEv (CReal.ofQ' floor0) (physGapC b (sep T) A 0)) :
    UniformPhysGapFloor T A :=
  toUniformPhysGapFloor T A
    (crealFloor_of_rateMatch (fun k => selfSimilarCReal T k) A
      (fun N => geRat_zero_of_posEv (margin_pos_tower T hx (N + 1))) hrm floor0 hpos0 hbase0)

/-- **Tower form — the full `CRealContinuumGapResidual` from `RateMatch`.** -/
def residual_of_rateMatch {b : Nat} (T : SelfSimilarTower b)
    (hx : PosEv (T.w 0)) (A : SpacingSchedule) (hrm : RateMatch b (sep T) A)
    (floor0 : Q') (hpos0 : (0 : Q') < floor0)
    (hbase0 : CReal.leEv (CReal.ofQ' floor0) (physGapC b (sep T) A 0)) :
    CRealContinuumGapResidual b :=
  toCRealContinuumGapResidual T hx A
    (crealFloor_of_rateMatch (fun k => selfSimilarCReal T k) A
      (fun N => geRat_zero_of_posEv (margin_pos_tower T hx (N + 1))) hrm floor0 hpos0 hbase0)

/-! ## 4. The genuinely-RATIONAL sufficient criterion `ρ_N ≥ 1` -/

/-- **`G N ≤ a_N / a_{N+1}` ⇒ `RateMatch`.**  The fully scalar criterion: a rational
upper bound `geomSumC (sep (N+1)) (b+1) ≤ a_N / a_{N+1}` on the geometric-sum factor
(the per-step ratio `ρ_N := (a_N/a_{N+1}) / G N ≥ 1`) implies the per-step
`RateMatch` inequality.  Proof: scale the rational bound by `1/a_N ≥ 0`
(`leRat_smul_nonneg`) and collapse `(1/a_N)·(a_N/a_{N+1}) = 1/a_{N+1}` via the
`divPos` identities. -/
theorem rateMatch_of_scalar {b : Nat} {s : Nat → CReal} {A : SpacingSchedule}
    (h : ∀ N, CReal.leRat (geomSumC (s (N + 1)) (b + 1))
      (Q'.divPos (A.a N) (A.a (N + 1)) (A.a_pos (N + 1)))) :
    RateMatch b s A := by
  intro N
  have hcNnn : (0 : Q') ≤ Q'.divPos 1 (A.a N) (A.a_pos N) :=
    Q'.le_of_lt (Q'.divPos_pos 1 (A.a N) (A.a_pos N) (by decide))
  have hsm := CReal.leRat_smul_nonneg hcNnn (h N)
  have hbound : Q'.divPos 1 (A.a N) (A.a_pos N)
        * Q'.divPos (A.a N) (A.a (N + 1)) (A.a_pos (N + 1))
      ≤ Q'.divPos 1 (A.a (N + 1)) (A.a_pos (N + 1)) := by
    apply Q'.le_divPos_of_mul_le 1 (A.a (N + 1)) (A.a_pos (N + 1))
    have e1 : (Q'.divPos (A.a N) (A.a (N + 1)) (A.a_pos (N + 1)) * A.a (N + 1)).eqv (A.a N) :=
      Q'.divPos_mul_eqv (A.a N) (A.a (N + 1)) (A.a_pos (N + 1))
    have e2 : (Q'.divPos 1 (A.a N) (A.a_pos N) * A.a N).eqv 1 :=
      Q'.divPos_mul_eqv 1 (A.a N) (A.a_pos N)
    have echain : ((Q'.divPos 1 (A.a N) (A.a_pos N)
          * Q'.divPos (A.a N) (A.a (N + 1)) (A.a_pos (N + 1))) * A.a (N + 1)).eqv 1 := by
      refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv (Q'.divPos 1 (A.a N) (A.a_pos N))
        (Q'.divPos (A.a N) (A.a (N + 1)) (A.a_pos (N + 1))) (A.a (N + 1))) ?_
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (Q'.divPos 1 (A.a N) (A.a_pos N)) _ _ e1) e2
    exact Q'.le_of_eqv echain
  exact CReal.leRat_mono hsm hbound

/-! ## 5. The sep / geomSum bounds the tuned criterion needs -/

/-- **A `CReal` lower bound passes to a convergent limit.**  Mirror of
`CodynamicCRealFlow.leRat_limit_of_eventually` for `geRat`. -/
theorem geRat_limit_of_eventually {s : Nat → CReal} {L : CReal} {r : Q'}
    (hconv : ConvergesTo s L)
    (hev : ∃ M : Nat, ∀ K : Nat, M ≤ K → ExpPos.geRat (s K) r) :
    ExpPos.geRat L r := by
  intro ε hε
  obtain ⟨M, hM⟩ := hev
  have hhε : (0 : Q') < HalfPow.half * ε := ExpNeg.half_mul_pos ε hε
  obtain ⟨Nstage, hstage⟩ := hconv (HalfPow.half * ε) hhε
  have hKstage : Nstage ≤ max Nstage M := Nat.le_max_left _ _
  have hKM : M ≤ max Nstage M := Nat.le_max_right _ _
  obtain ⟨Napx, hNapx⟩ := hstage (max Nstage M) hKstage
  obtain ⟨N', hN'⟩ := hM (max Nstage M) hKM (HalfPow.half * ε) hhε
  refine ⟨max Napx N', fun n hn => ?_⟩
  have hn1 : Napx ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hn2 : N' ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  have hsL : (s (max Nstage M)).approx n ≤ L.approx n + HalfPow.half * ε := (hNapx n hn1).1
  have hrs : r ≤ (s (max Nstage M)).approx n + HalfPow.half * ε := hN' n hn2
  have hcomb : r ≤ (L.approx n + HalfPow.half * ε) + HalfPow.half * ε :=
    Q'.le_trans' _ _ _ hrs (Q'.add_le_add_right _ _ (HalfPow.half * ε) hsL)
  refine Q'.le_trans' _ _ _ hcomb (Q'.le_of_eqv ?_)
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv (L.approx n) (HalfPow.half * ε) (HalfPow.half * ε)) ?_
  exact Q'.add_eqv_congr_left (L.approx n) _ _ (ExpNeg.two_halves ε)

/-- The separators are nonnegative: `sep T k ≥ 0`. -/
theorem sep_geRat_zero {b : Nat} (T : SelfSimilarTower b) (k : Nat) :
    ExpPos.geRat (sep T k) 0 :=
  geRat_limit_of_eventually (expNegCD_converges (T.w k) (T.dw k))
    ⟨0, fun K _ => expNeg_geRat_zero ((T.w k).approx K) ((T.dw k).hpos K)⟩

/-- The separators are `≤ 1`: `sep T k ≤ 1`. -/
theorem sep_leRat_one {b : Nat} (T : SelfSimilarTower b) (k : Nat) :
    CReal.leRat (sep T k) 1 :=
  leRat_limit_of_eventually (expNegCD_converges (T.w k) (T.dw k))
    ⟨0, fun K _ => expNeg_le_one ((T.w k).approx K) ((T.dw k).hpos K)⟩

/-- Powers of a `[0,1]` separator stay `≥ 0`. -/
theorem cpow_geRat_zero {x : CReal} (hx0 : ExpPos.geRat x 0) :
    ∀ m, ExpPos.geRat (CReal.cpow x m) 0
  | 0 => by
      refine ExpPos.geRat_of_eventually ⟨0, fun n _ => ?_⟩
      show (0 : Q') ≤ (CReal.cpow x 0).approx n
      show (0 : Q') ≤ (1 : Q')
      decide
  | m + 1 => by
      show ExpPos.geRat (CReal.mul (CReal.cpow x m) x) 0
      exact CReal.mul_nonneg (cpow_geRat_zero hx0 m) hx0

/-- Powers of a `[0,1]` separator stay `≤ 1`. -/
theorem cpow_leRat_one {x : CReal} (hx0 : ExpPos.geRat x 0) (hx1 : CReal.leRat x 1) :
    ∀ m, CReal.leRat (CReal.cpow x m) 1
  | 0 => by
      refine CReal.leRat_of_eventually ⟨0, fun n _ => ?_⟩
      show (CReal.cpow x 0).approx n ≤ (1 : Q')
      show (1 : Q') ≤ (1 : Q')
      exact Q'.le_refl' 1
  | m + 1 => by
      show CReal.leRat (CReal.mul (CReal.cpow x m) x) 1
      have hmul := CReal.leRat_mul (cpow_leRat_one hx0 hx1 m) hx1
        (cpow_geRat_zero hx0 m) hx0 (by decide) (by decide)
      exact CReal.leRat_mono hmul (Q'.le_of_eqv (Q'.mul_one_eqv 1))

/-- **`geomSumC x m ≤ m` for a `[0,1]` separator.**  Each of the `m` terms `xⁱ`
is `≤ 1`, so the finite geometric sum is `≤ m`. -/
theorem geomSumC_leRat_card {x : CReal} (hx0 : ExpPos.geRat x 0) (hx1 : CReal.leRat x 1) :
    ∀ m, CReal.leRat (geomSumC x m) (Q'.ofNat m)
  | 0 => by
      refine CReal.leRat_of_eventually ⟨0, fun n _ => ?_⟩
      show (geomSumC x 0).approx n ≤ Q'.ofNat 0
      show (0 : Q') ≤ Q'.ofNat 0
      exact Q'.le_of_eqv (Q'.eqv_symm Q'.ofNat_zero_eqv)
  | m + 1 => by
      show CReal.leRat (CReal.add (geomSumC x m) (CReal.cpow x m)) (Q'.ofNat (m + 1))
      have hadd := CReal.leRat_add (geomSumC_leRat_card hx0 hx1 m) (cpow_leRat_one hx0 hx1 m)
      refine CReal.leRat_mono hadd ?_
      have e1 : (Q'.ofNat 1).eqv (1 : Q') := by decide
      have e2 : (Q'.ofNat (m + 1)).eqv (Q'.ofNat m + (1 : Q')) :=
        Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv m 1)
          (Q'.add_eqv_congr_left (Q'.ofNat m) (Q'.ofNat 1) (1 : Q') e1)
      exact Q'.le_of_eqv (Q'.eqv_symm e2)

/-! ## 6. The concrete TUNED inhabitant: geometric spacing `a_N = (1/(b+1))^N` -/

/-- The geometric spacing schedule `a_0 = 1`, `a_{N+1} = a_N · (1/(b+1))` — a
GENUINELY VANISHING `a → 0` schedule with ratio `a_N / a_{N+1} = b+1`. -/
def geomA (b : Nat) : Nat → Q'
  | 0 => 1
  | N + 1 => geomA b N * Q'.invSucc b

theorem geomA_pos (b : Nat) : ∀ N, (0 : Q') < geomA b N
  | 0 => by show (0 : Q') < (1 : Q'); decide
  | N + 1 => Q'.mul_pos (geomA_pos b N) (Q'.invSucc_pos b)

/-- The tuned geometric spacing schedule as a `SpacingSchedule`. -/
def geomSpacing (b : Nat) : SpacingSchedule where
  a := geomA b
  a_pos := geomA_pos b

/-- **The tuned scalar bound `G N ≤ a_N / a_{N+1} = b+1`.**  For the geometric
spacing the ratio is exactly `b+1`, and `geomSumC (sep (N+1)) (b+1) ≤ b+1` because
every term of the `(b+1)`-fold sum of a `[0,1]` separator is `≤ 1`. -/
theorem geomSpacing_scalar {b : Nat} (T : SelfSimilarTower b) (N : Nat) :
    CReal.leRat (geomSumC (sep T (N + 1)) (b + 1))
      (Q'.divPos ((geomSpacing b).a N) ((geomSpacing b).a (N + 1))
        ((geomSpacing b).a_pos (N + 1))) := by
  have hcard : CReal.leRat (geomSumC (sep T (N + 1)) (b + 1)) (Q'.ofNat (b + 1)) :=
    geomSumC_leRat_card (sep_geRat_zero T (N + 1)) (sep_leRat_one T (N + 1)) (b + 1)
  refine CReal.leRat_mono hcard ?_
  apply Q'.le_divPos_of_mul_le ((geomSpacing b).a N) ((geomSpacing b).a (N + 1))
    ((geomSpacing b).a_pos (N + 1))
  have heq : (Q'.ofNat (b + 1) * (geomA b N * Q'.invSucc b)).eqv (geomA b N) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (Q'.ofNat (b + 1))
      (geomA b N * Q'.invSucc b) (Q'.invSucc b * geomA b N)
      (Q'.mul_comm_eqv (geomA b N) (Q'.invSucc b))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat (b + 1)) (Q'.invSucc b) (geomA b N))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (geomA b N) (Q'.ofNat_succ_mul_invSucc b)) ?_
    exact Q'.one_mul_eqv (geomA b N)
  exact Q'.le_of_eqv heq

/-- **THE TUNED RATE-MATCH (rational `1/2` seed).**  The self-similar flow
`concreteTower 1` with the genuinely-vanishing geometric spacing `a_N = (1/2)^N`
satisfies `RateMatch`. -/
theorem tunedRateMatch : RateMatch 1 (sep (concreteTower 1)) (geomSpacing 1) :=
  rateMatch_of_scalar (fun N => geomSpacing_scalar (concreteTower 1) N)

/-- **THE TUNED RATE-MATCH (irrational `e^{−1}` seed).**  `RateMatch` is
seed-agnostic: the irrational-exponent flow `concreteTowerE 1` with the same
geometric spacing also satisfies it. -/
theorem tunedRateMatch_E : RateMatch 1 (sep (concreteTowerE 1)) (geomSpacing 1) :=
  rateMatch_of_scalar (fun N => geomSpacing_scalar (concreteTowerE 1) N)

/-- The UV exponent seed of `concreteTower 1` is strictly positive (`w 0 = 1/2`). -/
theorem concreteTower1_seed : PosEv ((concreteTower 1).w 0) :=
  posEv_of_eventually (ε := Q'.invSucc 1) (Q'.invSucc_pos 1)
    ⟨0, fun _ _ => Q'.le_refl' (Q'.invSucc 1)⟩

/-- The explicit UV-gap floor for the tuned `1/2`-seed model: `1 − 1/(1+1/2) = 1/3`. -/
def tunedUVFloor : Q' := 1 + -(ExpUBInstance.oneOver1p (Q'.invSucc 1))

theorem tunedUVFloor_pos : (0 : Q') < tunedUVFloor := by decide

/-- **The tuned UV-gap floor lies below `physGapC 0`.**  `physGapC 0 = (1 − sep 0)·1`
with `sep 0 = e^{−(1/2)} ≤ 2/3`, so `physGapC 0 ≥ 1 − 2/3 = 1/3`. -/
theorem tuned_hbase :
    CReal.leEv (CReal.ofQ' tunedUVFloor)
      (physGapC 1 (sep (concreteTower 1)) (geomSpacing 1) 0) := by
  have h0nn : (0 : Q') ≤ Q'.invSucc 1 := Q'.invSucc_nonneg 1
  have hbridge : CReal.Equiv (sep (concreteTower 1) 0)
      (ExpNeg.expNeg (Q'.invSucc 1) h0nn) :=
    expNegCD_ofQ'_equiv (Q'.invSucc 1) h0nn _
  have hsep0 : CReal.leRat (sep (concreteTower 1) 0)
      (ExpUBInstance.oneOver1p (Q'.invSucc 1)) :=
    CReal.leRat_of_equiv hbridge (expNeg_le_oneOver1p (Q'.invSucc 1) h0nn)
  have hmargin : CReal.leEv (CReal.ofQ' tunedUVFloor)
      (CReal.sub CReal.cone (sep (concreteTower 1) 0)) :=
    leEv_oneSub_of_leRat hsep0
  have hgap0 : CReal.Equiv (physGapC 1 (sep (concreteTower 1)) (geomSpacing 1) 0)
      (CReal.sub CReal.cone (sep (concreteTower 1) 0)) := by
    show CReal.Equiv
      (CReal.mul (CReal.sub CReal.cone (sep (concreteTower 1) 0))
        (recipSpacingC (geomSpacing 1) 0))
      (CReal.sub CReal.cone (sep (concreteTower 1) 0))
    refine CReal.Equiv.trans (CRealContinuumAlg.cmul_congr_right ?_) (CRealAlg.cmul_cone _)
    refine SumOfSquares.Equiv_of_approx_eqv (fun _ => ?_)
    show (Q'.divPos 1 ((geomSpacing 1).a 0) ((geomSpacing 1).a_pos 0)).eqv (1 : Q')
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_one_eqv (Q'.divPos 1 ((geomSpacing 1).a 0) ((geomSpacing 1).a_pos 0))))
      (Q'.divPos_mul_eqv 1 ((geomSpacing 1).a 0) ((geomSpacing 1).a_pos 0))
  exact CReal.leEv_trans hmargin (leEv_of_equiv (CReal.Equiv.symm hgap0))

/-- **THE TUNED SPACING-UNIFORM FLOOR (non-vacuous green inhabitant).**  Feeding
`tunedRateMatch` and the explicit UV floor through the reduction yields an
INHABITED `CRealFloor` on the physical gap of a self-similar flow with a real
`a → 0` schedule — a strictly-positive rational below `physGapC N` at EVERY scale
simultaneously. -/
def tunedCRealFloor : CRealFloor (physGapC 1 (sep (concreteTower 1)) (geomSpacing 1)) :=
  crealFloor_of_rateMatch (fun k => selfSimilarCReal (concreteTower 1) k) (geomSpacing 1)
    (fun N => geRat_zero_of_posEv (margin_pos_tower (concreteTower 1) concreteTower1_seed (N + 1)))
    tunedRateMatch tunedUVFloor tunedUVFloor_pos tuned_hbase

/-- **THE TUNED CONTINUUM RESIDUAL.**  The full `CRealContinuumGapResidual` for the
tuned model — conserved-margin half supplied by the flow, uniform half discharged
by `tunedRateMatch` and the explicit UV floor. -/
def tunedResidual : CRealContinuumGapResidual 1 :=
  residual_of_rateMatch (concreteTower 1) concreteTower1_seed (geomSpacing 1)
    tunedRateMatch tunedUVFloor tunedUVFloor_pos tuned_hbase

/-- The tuned floor is strictly positive (non-vacuity witness). -/
theorem tunedCRealFloor_pos : (0 : Q') < tunedCRealFloor.floor :=
  tunedCRealFloor.floor_pos

end YMGap.Continuum.RateMatchFloor

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.RateMatchFloor.geRat_equiv_transfer
#print axioms YMGap.Continuum.RateMatchFloor.geRat_sub_of_leEv
#print axioms YMGap.Continuum.RateMatchFloor.leEv_of_geRat_sub
#print axioms YMGap.Continuum.RateMatchFloor.leEv_mul_left_nonneg
#print axioms YMGap.Continuum.RateMatchFloor.leEv_oneSub_of_leRat
#print axioms YMGap.Continuum.RateMatchFloor.physGapC_step
#print axioms YMGap.Continuum.RateMatchFloor.physGapC_ge_base
#print axioms YMGap.Continuum.RateMatchFloor.crealFloor_of_rateMatch
#print axioms YMGap.Continuum.RateMatchFloor.uniformPhysGapFloor_of_rateMatch
#print axioms YMGap.Continuum.RateMatchFloor.residual_of_rateMatch
#print axioms YMGap.Continuum.RateMatchFloor.rateMatch_of_scalar
#print axioms YMGap.Continuum.RateMatchFloor.geRat_limit_of_eventually
#print axioms YMGap.Continuum.RateMatchFloor.sep_geRat_zero
#print axioms YMGap.Continuum.RateMatchFloor.sep_leRat_one
#print axioms YMGap.Continuum.RateMatchFloor.geomSumC_leRat_card
#print axioms YMGap.Continuum.RateMatchFloor.geomSpacing_scalar
#print axioms YMGap.Continuum.RateMatchFloor.tunedRateMatch
#print axioms YMGap.Continuum.RateMatchFloor.tunedRateMatch_E
#print axioms YMGap.Continuum.RateMatchFloor.tuned_hbase
#print axioms YMGap.Continuum.RateMatchFloor.tunedCRealFloor
#print axioms YMGap.Continuum.RateMatchFloor.tunedResidual
#print axioms YMGap.Continuum.RateMatchFloor.tunedCRealFloor_pos
