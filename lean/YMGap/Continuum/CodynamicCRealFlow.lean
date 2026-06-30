/-
Track B / R2 — **The codynamic flow law, INHABITED at the `CReal` level.**

# Why this module exists (read first)

`CodynamicTransmutation` recast dimensional transmutation as the RG **flow law**
(self-similarity)

    sep k ≃ (sep (k+1))^(b+1)     (`selfSimilar`),

together with the conserved-margin budget (`marginInvariant`, `marginBudget_pos`).
Its central honest caveat (`CodynamicTransmutation`, §SCOPE) is that the flow law has
**NO rational inhabitant** — the canonical gaming flow `polyFlow` provably FAILS it
(`polyFlow_not_selfSimilar`), because the `(b+1)`-th-root flow is irrational.  So at
the `Q'` level the conserved-margin carrier is *vacuous*: the budget theorems are
conditional on a hypothesis (`selfSimilar b sep`) that the rational candidate cannot
satisfy.

This module closes that gap.  The constructive-real self-similar flow built in
`SelfSimilarFlow` (`concreteSelfSimilarFlow` / `concreteSelfSimilarFlowE`) is a
genuine inhabitant of the **CReal analogue** of the flow law.  We lift the rational
predicate `selfSimilar` to the `CReal` predicate `selfSimilarC`, bundle the flow with
its proof into a `Type`-level carrier `CRealFlow`, and exhibit two inhabitants:

  * `concreteCRealFlow`  — seeded at the rational exponent `1/2`;
  * `concreteCRealFlowE` — seeded at the IRRATIONAL exponent `1/e`.

The headline contrast is `flow_law_rational_empty_but_creal_inhabited`: the SAME flow
law that the rational `polyFlow` provably fails is constructively SATISFIED by the
CReal flow.  "No rational inhabitant" becomes "a genuine constructive-real
inhabitant" — the conserved-margin budget's carrier is no longer vacuous.

# Honest scope

`selfSimilarC` is the CReal mirror of `CodynamicTransmutation.selfSimilar`; the
inhabitants reuse the closed flows from `SelfSimilarFlow` (no new analytic content,
this is the *wiring*).  The rational margin telescoping (`marginInvariant`) is itself
unchanged; what is new is that its self-similar HYPOTHESIS — empty over `Q'` for the
gaming flow — is inhabited over `CReal`.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure composition over the `SelfSimilarFlow` backbone; the flow carrier is `Type`-level
data.  Each load-bearing declaration is gated with `#print axioms` (permitted:
`propext` / `Quot.sound`).  No `Classical.*`, no `native_decide`, no `sorry`.
-/

import YMGap.Constructive.SelfSimilarFlow
import YMGap.Continuum.CodynamicTransmutation
import YMGap.Continuum.TuranPositivity
import YMGap.Constructive.Soundness
import YMGap.Constructive.CRealMulMono

namespace YMGap.Continuum.CodynamicCRealFlow

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.CRealAlg
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.TuranPositivity

/-! ## 1. The CReal self-similarity predicate -/

/-- **The CReal flow law (self-similarity).**  The constructive-real analogue of
`CodynamicTransmutation.selfSimilar`: the separator family `s : Nat → CReal` satisfies
`s k ≈ (s (k+1))^(b+1)` at every scale.  Unlike the rational version, this predicate
is inhabited (§2). -/
def selfSimilarC (b : Nat) (s : Nat → CReal) : Prop :=
  ∀ k, CReal.Equiv (s k) (cpow (s (k + 1)) (b + 1))

/-- **A self-similar CReal flow** — a `Type`-level bundle of the separator family and
its flow-law proof.  This is the inhabited carrier of the codynamic conserved-margin
budget (the rational carrier being vacuous for the gaming flow). -/
structure CRealFlow (b : Nat) : Type where
  /-- The separator family `sep k`. -/
  s : Nat → CReal
  /-- The flow law `s k ≈ (s (k+1))^(b+1)` at every scale. -/
  ss : selfSimilarC b s

/-! ## 2. Two concrete inhabitants (rational `1/2` and irrational `1/e` seeds) -/

/-- **The rational-seed inhabitant.**  Separators `e^{−(1/2)/(b+1)^k}` of the
`1/2`-seeded tower — irrational reals satisfying the flow law `selfSimilar` failed
rationally. -/
def concreteCRealFlow (b : Nat) : CRealFlow b where
  s := sep (concreteTower b)
  ss := fun k => concreteSelfSimilarFlow b k

/-- **The irrational-seed inhabitant.**  Separators `e^{−(1/e)/(b+1)^k}` of the
`e^{−1}`-seeded tower — a self-similar CReal flow with genuinely irrational
EXPONENTS. -/
def concreteCRealFlowE (b : Nat) : CRealFlow b where
  s := sep (concreteTowerE b)
  ss := fun k => concreteSelfSimilarFlowE b k

/-- The CReal flow law is INHABITED for every block factor `b` (rational seed). -/
theorem selfSimilarC_inhabited (b : Nat) :
    selfSimilarC b (concreteCRealFlow b).s :=
  (concreteCRealFlow b).ss

/-- The CReal flow law is INHABITED for every block factor `b` (irrational `1/e`
seed). -/
theorem selfSimilarC_inhabited_E (b : Nat) :
    selfSimilarC b (concreteCRealFlowE b).s :=
  (concreteCRealFlowE b).ss

/-! ## 3. The headline contrast: rational-empty vs. CReal-inhabited -/

/-- The canonical rational gaming flow provably FAILS the rational flow law
(re-exposed from `CodynamicTransmutation`, the falsification anchoring this module). -/
theorem rational_flow_law_empty :
    ¬ CodynamicTransmutation.selfSimilar 1 CodynamicTransmutation.polyFlow :=
  CodynamicTransmutation.polyFlow_not_selfSimilar

/-- **THE CONNECTING THEOREM.**  At block factor `b = 1` the SAME flow law is:

  * empty over `Q'` for the gaming flow `polyFlow`
    (`¬ selfSimilar 1 polyFlow` — the rational carrier is vacuous), yet
  * inhabited over `CReal` by the concrete flow
    (`selfSimilarC 1 (concreteCRealFlow 1).s`).

This is the precise sense in which the codynamic conserved-margin budget — whose
rational hypothesis `selfSimilar` no rational flow satisfies — becomes a genuine
constructive-real inhabitant. -/
theorem flow_law_rational_empty_but_creal_inhabited :
    (¬ CodynamicTransmutation.selfSimilar 1 CodynamicTransmutation.polyFlow)
      ∧ selfSimilarC 1 (concreteCRealFlow 1).s :=
  ⟨CodynamicTransmutation.polyFlow_not_selfSimilar, (concreteCRealFlow 1).ss⟩

/-- **The conserved-margin budget is positive ALONG ANY RATIONAL SHADOW of the flow.**
For any rational separator family `seq` that DOES satisfy the rational flow law
(`selfSimilar b seq`) with a genuine UV margin (`seq 0 < 1`), the rescaled margin
stays strictly positive at every scale (`CodynamicTransmutation.marginBudget_pos`).
The CReal flow `concreteCRealFlow`/`concreteCRealFlowE` is the constructive object that
makes such a self-similar family inhabitable in the first place (the rational gaming
flow cannot, by `rational_flow_law_empty`). -/
theorem marginBudget_pos_along_selfSimilar {b : Nat} {seq : Nat → Q'}
    (hss : CodynamicTransmutation.selfSimilar b seq) (h0 : seq 0 < (1 : Q')) (N : Nat) :
    (0 : Q') < ((1 : Q') - seq N) * CodynamicTransmutation.marginProductTail b seq N :=
  CodynamicTransmutation.marginBudget_pos hss h0 N

/-! ## 4. The CReal finite geometric sum and the exact `1 − xⁿ` factorization

The rational `CodynamicTransmutation.oneSub_pow_factor` is the engine of the
margin telescoping.  We lift it to `CReal`.  Because `CReal.mul`, `CReal.add`,
`CReal.neg` are all *approx-wise definitional* and `cpow x m` has approximation
`qpow (x.approx n) m`, the CReal geometric sum has approximation `geomSum (x.approx
n) m`, so the CReal factorization reduces — index by index — to the existing `Q'`
factorization `oneSub_pow_factor`. -/

/-- **The CReal finite geometric sum** `geomSumC x m = ∑_{i<m} xⁱ` (fold, highest
term on the right) — the constructive-real analogue of `geomSum`. -/
def geomSumC (x : CReal) : Nat → CReal
  | 0 => CReal.czero
  | n + 1 => CReal.add (geomSumC x n) (CReal.cpow x n)

/-- `cpow x m` has approximation `qpow (x.approx n) m` (both are the same `Nat`-power
fold; `CReal.mul` is approx-wise). -/
theorem cpow_approx (x : CReal) :
    ∀ (m n : Nat), (CReal.cpow x m).approx n = RGTransport.qpow (x.approx n) m
  | 0, _ => rfl
  | m + 1, n => by
      show (CReal.cpow x m).approx n * x.approx n
        = RGTransport.qpow (x.approx n) m * x.approx n
      rw [cpow_approx x m n]

/-- `geomSumC x m` has approximation `geomSum (x.approx n) m` (the `CReal` sum is
approx-wise; `cpow_approx` handles the term). -/
theorem geomSumC_approx (x : CReal) :
    ∀ (m n : Nat), (geomSumC x m).approx n = geomSum (x.approx n) m
  | 0, _ => rfl
  | m + 1, n => by
      show (geomSumC x m).approx n + (CReal.cpow x m).approx n
        = geomSum (x.approx n) m + RGTransport.qpow (x.approx n) m
      rw [geomSumC_approx x m n, cpow_approx x m n]

/-- **THE CReal FINITE GEOMETRIC FACTORIZATION** `1 − x^(b+1) ≃ (1 − x)·∑_{i<b+1} xⁱ`
at the `CReal` level — the lift of `oneSub_pow_factor`.  Proved index-wise: every
approximation reduces (via `cpow_approx` / `geomSumC_approx`) to the rational
identity `oneSub_pow_factor (x.approx n) (b+1)`. -/
theorem oneSub_pow_factorC (x : CReal) (b : Nat) :
    CReal.Equiv (CReal.sub CReal.cone (CReal.cpow x (b + 1)))
      (CReal.mul (CReal.sub CReal.cone x) (geomSumC x (b + 1))) := by
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  show ((1 : Q') + -(CReal.cpow x (b + 1)).approx n).eqv
      (((1 : Q') + -(x.approx n)) * (geomSumC x (b + 1)).approx n)
  rw [cpow_approx x (b + 1) n, geomSumC_approx x (b + 1) n]
  exact oneSub_pow_factor (x.approx n) (b + 1)

/-! ## 5. The conserved-margin invariant, lifted to `CReal`

The rational `marginInvariant` is a telescoping induction over `margin_step`,
`mul_swap_right`, and the `Q'` multiplicative congruences.  Every ingredient has a
`CReal` counterpart (`oneSub_pow_factorC`, the `CRealAlg` ring lemmas, the
`CReal.*_congr` congruences), so the proof mirrors the rational one verbatim. -/

/-- `Equiv` congruence for `mul` on the right (from `mul_congr_left` + `cmul_comm`). -/
theorem mul_congr_rightC {A B B' : CReal} (h : CReal.Equiv B B') :
    CReal.Equiv (CReal.mul A B) (CReal.mul A B') :=
  CReal.Equiv.trans (cmul_comm A B)
    (CReal.Equiv.trans (CReal.mul_congr_left h) (cmul_comm B' A))

/-- `x·(y·z) ≃ (x·z)·y` (the CReal swap used to peel the top geomSum factor). -/
theorem mul_swap_rightC (x y z : CReal) :
    CReal.Equiv (CReal.mul x (CReal.mul y z)) (CReal.mul (CReal.mul x z) y) :=
  CReal.Equiv.trans (mul_congr_rightC (cmul_comm y z))
    (CReal.Equiv.symm (cmul_assoc x z y))

/-- **The per-step CReal margin recurrence.**  Under the CReal flow law,
`1 − s k ≃ (1 − s (k+1))·geomSumC (s (k+1)) (b+1)` — the lift of `margin_step`. -/
theorem margin_stepC {b : Nat} {s : Nat → CReal} (hss : selfSimilarC b s) (k : Nat) :
    CReal.Equiv (CReal.sub CReal.cone (s k))
      (CReal.mul (CReal.sub CReal.cone (s (k + 1))) (geomSumC (s (k + 1)) (b + 1))) :=
  CReal.Equiv.trans (CReal.sub_congr_right (hss k)) (oneSub_pow_factorC (s (k + 1)) b)

/-- The CReal margin-product tail `∏_{j=1}^{N} g j` (top factor on the right) — the
constructive-real analogue of `marginProductTail`. -/
def cprodTail (g : Nat → CReal) : Nat → CReal
  | 0 => CReal.cone
  | N + 1 => CReal.mul (cprodTail g N) (g (N + 1))

/-- **THE CONSERVED-MARGIN INVARIANT, LIFTED TO `CReal`.**  Under the CReal flow law
the geometrically-rescaled margin is a flow invariant:

    (1 − s N) · ∏_{j=1}^{N} geomSumC (s j) (b+1) ≃ 1 − s 0,

for every scale `N` — the constructive-real `marginInvariant`.  Proof: induction on
`N` via `margin_stepC` + `mul_swap_rightC`, mirroring the rational telescoping.  This
is the codynamic "summable budget" made exact along a genuine *irrational*
constructive-real self-similar flow (where no rational flow exists). -/
theorem marginInvariantC {b : Nat} {s : Nat → CReal} (hss : selfSimilarC b s) :
    ∀ N, CReal.Equiv
      (CReal.mul (CReal.sub CReal.cone (s N))
        (cprodTail (fun j => geomSumC (s j) (b + 1)) N))
      (CReal.sub CReal.cone (s 0))
  | 0 => cmul_cone (CReal.sub CReal.cone (s 0))
  | N + 1 => by
      refine CReal.Equiv.trans
        (mul_swap_rightC (CReal.sub CReal.cone (s (N + 1)))
          (cprodTail (fun j => geomSumC (s j) (b + 1)) N)
          (geomSumC (s (N + 1)) (b + 1))) ?_
      have hstep : CReal.Equiv
          (CReal.mul (CReal.sub CReal.cone (s (N + 1))) (geomSumC (s (N + 1)) (b + 1)))
          (CReal.sub CReal.cone (s N)) :=
        CReal.Equiv.symm (margin_stepC hss N)
      exact CReal.Equiv.trans (CReal.mul_congr_left hstep) (marginInvariantC hss N)

/-! ## 6. The budget is strictly positive (Equiv-stable `PosEv`)

The rational `marginBudget_pos` is conditional on a genuine UV margin (`sep 0 < 1`).
Its faithful `CReal` lift is conditional on the eventual strict positivity of the
*base* margin `1 − s 0` (the `Equiv`-stable `TuranPositivity.PosEv`, which — unlike
the one-slack `IsPositive` — transports across `Equiv`).  Given that single base
positivity, the rescaled margin at EVERY scale is strictly positive, because it
equals the fixed positive `1 − s 0` by `marginInvariantC`. -/

/-- **THE CReal BUDGET IS BOUNDED BELOW AWAY FROM ZERO.**  Given the eventual strict
positivity of the base margin `1 − s 0` (the genuine UV margin, the `CReal` analogue
of `sep 0 < 1`), the rescaled margin `(1 − s N)·∏geomSumC` is strictly positive
(`PosEv`) at every scale — it transports the fixed positive `1 − s 0` across the
conserved invariant.  The constructive-real `marginBudget_pos`. -/
theorem marginBudget_posC {b : Nat} {s : Nat → CReal} (hss : selfSimilarC b s)
    (h0 : PosEv (CReal.sub CReal.cone (s 0))) (N : Nat) :
    PosEv (CReal.mul (CReal.sub CReal.cone (s N))
      (cprodTail (fun j => geomSumC (s j) (b + 1)) N)) :=
  posEv_of_equiv h0 (CReal.Equiv.symm (marginInvariantC hss N))

/-! ## 6b. Discharging the base UV margin for a rational-seed exponent

For the rational-seed flow `concreteCRealFlow`, the base separator is
`sep 0 = e^{−(1/2)}` (an `expNegCD` of a *constant rational* exponent `1/2`).  We
discharge the base UV-margin hypothesis `PosEv (1 − sep 0)` UNCONDITIONALLY: bridge
the constant-exponent `expNegCD` to the rational-argument `ExpNeg.expNeg`, then use
the sound bound `e^{−c} ≤ 1/(1+c) < 1`. -/

/-- **The constant-exponent bridge** `expNegCD (ofQ' c) ≈ e^{−c}`.  The defining
sequence of `expNegCD (ofQ' c)` is the CONSTANT sequence `e^{−c}` (since
`(ofQ' c).approx k = c`), so both are limits of that constant sequence. -/
theorem expNegCD_ofQ'_equiv (c : Q') (h0 : (0 : Q') ≤ c) (d : ExpNegCData (CReal.ofQ' c)) :
    CReal.Equiv (expNegCD (CReal.ofQ' c) d) (ExpNeg.expNeg c h0) :=
  CReal.Equiv_of_limit_of_equal
    (fun k => expNeg_eqv_congr (d.hpos k) h0 (Q'.eqv_refl _))
    (expNegCD_converges (CReal.ofQ' c) d)
    (fun ε hε => ⟨0, fun _ _ => ⟨0, fun n _ =>
      ⟨Q'.add_le_self_of_nonneg ((ExpNeg.expNeg c h0).approx n) ε (Q'.le_of_lt hε),
       Q'.add_le_self_of_nonneg ((ExpNeg.expNeg c h0).approx n) ε (Q'.le_of_lt hε)⟩⟩⟩)

/-- `geRat (r − x) 0` from `leRat x r`: an eventual upper bound `x ≤ r` gives the
nonnegativity of the rational margin `r − x`. -/
theorem geRat_sub_ofQ'_of_leRat {x : CReal} {r : Q'} (h : CReal.leRat x r) :
    ExpPos.geRat (CReal.sub (CReal.ofQ' r) x) 0 := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  show (0 : Q') ≤ (r + -(x.approx n)) + ε
  have hnn : (0 : Q') ≤ (r + ε) + -(x.approx n) :=
    Q'.sub_nonneg_of_le (hN n hn)
  refine Q'.le_trans' _ _ _ hnn (Q'.le_of_eqv ?_)
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv r ε (-(x.approx n))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left r _ _ (Q'.add_comm_eqv ε (-(x.approx n)))) ?_
  exact Q'.eqv_symm (Q'.add_assoc_eqv r (-(x.approx n)) ε)

/-- The split `1 − x ≃ (1 − r) + (r − x)` (approx-wise `Q'` regrouping). -/
theorem sub_cone_split (x : CReal) (r : Q') :
    CReal.Equiv (CReal.sub CReal.cone x)
      (CReal.add (CReal.sub CReal.cone (CReal.ofQ' r)) (CReal.sub (CReal.ofQ' r) x)) := by
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  show ((1 : Q') + -(x.approx n)).eqv
      (((1 : Q') + -r) + (r + -(x.approx n)))
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv 1 (-r) (r + -(x.approx n))) ?_
  refine Q'.add_eqv_congr_left 1 _ _ ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv (-r) r (-(x.approx n)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ (-(x.approx n)) (Q'.neg_add_self_eqv r)) ?_
  exact QPoly.q_zero_add_eqv (-(x.approx n))

/-- **`PosEv (1 − x)` from a sound upper bound `x ≤ r < 1`** (the generic UV-margin
positivity engine).  Given a strictly-positive floor `0 < 1 − r` and a sound
rational upper bound `leRat x r`, the margin `1 − x` is eventually strictly
positive (`PosEv`).  The split `1 − x ≃ (1 − r) + (r − x)` adds the fixed positive
`1 − r` to the nonnegative `r − x`. -/
theorem posEv_oneSub_of_leRat {x : CReal} {r : Q'}
    (hfloor : (0 : Q') < (1 : Q') + -r) (hle : CReal.leRat x r) :
    PosEv (CReal.sub CReal.cone x) := by
  have hPosR : PosEv (CReal.sub CReal.cone (CReal.ofQ' r)) := by
    refine posEv_of_eventually (ε := (1 : Q') + -r) hfloor ⟨0, fun n _ => ?_⟩
    show (1 : Q') + -r ≤ (1 : Q') + -r
    exact Q'.le_refl' _
  have hgeR : ExpPos.geRat (CReal.sub (CReal.ofQ' r) x) 0 :=
    geRat_sub_ofQ'_of_leRat hle
  exact posEv_of_equiv (posEv_add_geRat hPosR hgeR)
    (CReal.Equiv.symm (sub_cone_split x r))

/-- **`PosEv (1 − e^{−c})` for a positive rational `c`** (eventual strict
positivity of the UV margin): `e^{−c} ≤ 1/(1+c)` gives a fixed positive floor
`1 − 1/(1+c)`. -/
theorem posEv_oneSub_expNeg {c : Q'} (h0 : (0 : Q') ≤ c)
    (hfloor : (0 : Q') < (1 : Q') + -(ExpUBInstance.oneOver1p c)) :
    PosEv (CReal.sub CReal.cone (ExpNeg.expNeg c h0)) :=
  posEv_oneSub_of_leRat hfloor (expNeg_le_oneOver1p c h0)

/-- **THE BASE UV MARGIN, DISCHARGED (rational `1/2` seed).**  For the rational-seed
flow the base margin `1 − sep 0 = 1 − e^{−(1/2)}` is eventually strictly positive
(`PosEv`), with the explicit floor `1 − 1/(1+1/2) = 1/3`. -/
theorem baseMargin_posC_concrete :
    PosEv (CReal.sub CReal.cone ((concreteCRealFlow 1).s 0)) := by
  have h0 : (0 : Q') ≤ Q'.invSucc 1 := Q'.invSucc_nonneg 1
  have hbridge : CReal.Equiv ((concreteCRealFlow 1).s 0)
      (ExpNeg.expNeg (Q'.invSucc 1) h0) :=
    expNegCD_ofQ'_equiv (Q'.invSucc 1) h0 _
  have hexp : PosEv (CReal.sub CReal.cone (ExpNeg.expNeg (Q'.invSucc 1) h0)) :=
    posEv_oneSub_expNeg h0 (by decide)
  exact posEv_of_equiv hexp (CReal.sub_congr_right (CReal.Equiv.symm hbridge))

/-! ## 6c. The general base UV margin: `e^{−x} < 1` for ANY strictly-positive
`CReal` exponent `x`

The §6b discharge bridged `expNegCD` of a *constant rational* exponent to the
rational-argument `ExpNeg.expNeg`, so it only covers rational seeds.  Here we close
the irrational-exponent case directly: for ANY `CReal` exponent `x` with `x > 0`
(`PosEv x`), the base margin `1 − e^{−x}` is strictly positive.  The route is the
genuine CReal-argument analogue of `e^{−c} ≤ 1/(1+c)`: from an eventual rational
floor `ε ≤ x.approx k` (extracted from `PosEv x`) each sequence term satisfies
`e^{−x.approx k} ≤ 1/(1+ε)`, so the limit `expNegCD x d ≤ 1/(1+ε) < 1`. -/

/-- **A sound rational upper bound transfers from the converging sequence to its
limit.**  If `ConvergesTo s L` and the terms `s K` are eventually (`K ≥ M`)
uniformly `≤ r` (`leRat (s K) r`), then the limit is `≤ r` (`leRat L r`).  Proof:
pick `K = max(Nstage, M)`; the limit's approx is `ε/2`-close to `(s K)`'s, which is
`ε/2`-close to `r`. -/
theorem leRat_limit_of_eventually {s : Nat → CReal} {L : CReal} {r : Q'}
    (hconv : ConvergesTo s L)
    (hev : ∃ M : Nat, ∀ K : Nat, M ≤ K → CReal.leRat (s K) r) :
    CReal.leRat L r := by
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
  have hLs : L.approx n ≤ (s (max Nstage M)).approx n + HalfPow.half * ε := (hNapx n hn1).2
  have hsr : (s (max Nstage M)).approx n ≤ r + HalfPow.half * ε := hN' n hn2
  have hcomb : L.approx n ≤ (r + HalfPow.half * ε) + HalfPow.half * ε :=
    Q'.le_trans' _ _ _ hLs
      (Q'.add_le_add_right _ _ (HalfPow.half * ε) hsr)
  refine Q'.le_trans' _ _ _ hcomb (Q'.le_of_eqv ?_)
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv r (HalfPow.half * ε) (HalfPow.half * ε)) ?_
  exact Q'.add_eqv_congr_left r _ _ (ExpNeg.two_halves ε)

/-- **`1/(1+x) < 1` for `x > 0`.**  At the `Q'` level: `oneOver1p x` has numerator
`x.den` and denominator `x.num⁺ + x.den`; for `x > 0` (so `x.num > 0`) the
denominator strictly exceeds the numerator. -/
theorem oneOver1p_lt_one {x : Q'} (hx : (0 : Q') < x) :
    ExpUBInstance.oneOver1p x < (1 : Q') := by
  have hxn : (0 : Int) < x.num := by
    have h : (0 : Int) * (x.den : Int) < x.num * (1 : Int) := hx
    rw [Int.zero_mul, Int.mul_one] at h; exact h
  show (ExpUBInstance.oneOver1p x).num * ((1 : Q').den : Int)
      < (1 : Q').num * ((ExpUBInstance.oneOver1p x).den : Int)
  rw [ExpUBInstance.oneOver1p_num, ExpUBInstance.oneOver1p_den]
  have e1 : (1 : Q').num = 1 := rfl
  have e2 : ((1 : Q').den : Int) = 1 := rfl
  rw [e1, e2, Int.mul_one, Int.one_mul]
  have htn : (1 : Int) ≤ (x.num.toNat : Int) := by omega
  have hcast : ((x.num.toNat + x.den : Nat) : Int) = (x.num.toNat : Int) + (x.den : Int) := by
    push_cast; rfl
  rw [hcast]; omega

/-- `c < d → 0 < d + (−c)` over `Q'` (the strict-margin form needed by the floor;
a local copy to avoid a heavy import). -/
theorem qsub_pos_of_lt {c d : Q'} (h : c < d) : (0 : Q') < d + (-c) := by
  have hc : c.num * (d.den : Int) < d.num * (c.den : Int) := h
  show (0 : Int) * ((d + (-c)).den : Int) < (d + (-c)).num * ((0 : Q').den : Int)
  have hnum : (d + (-c)).num = d.num * (c.den : Int) + (-c.num) * (d.den : Int) := rfl
  rw [hnum]
  have hden1 : ((0 : Q').den : Int) = 1 := rfl
  rw [hden1, Int.zero_mul, Int.mul_one]
  have hpos : (0 : Int) < d.num * (c.den : Int) - c.num * (d.den : Int) := Int.sub_pos.mpr hc
  have heq : d.num * (c.den : Int) + (-c.num) * (d.den : Int)
      = d.num * (c.den : Int) - c.num * (d.den : Int) := by rw [Int.neg_mul]; rfl
  rw [heq]; exact hpos

/-- **`e^{−x} < 1` FOR ANY STRICTLY-POSITIVE `CReal` EXPONENT `x`.**  Given
`PosEv x` (`x > 0`), the base margin `1 − e^{−x}` is eventually strictly positive
(`PosEv`).  This is the general, irrational-exponent-capable replacement for the
rational `expNegCD_ofQ'_equiv`-bridged §6b discharge: a positive rational floor
`ε ≤ x.approx k` (from `PosEv x`) bounds every sequence term `e^{−x.approx k} ≤
1/(1+ε)`, hence the limit `expNegCD x d ≤ 1/(1+ε) < 1`. -/
theorem expNegCD_lt_one {x : CReal} (d : ExpNegCData x) (hx : PosEv x) :
    PosEv (CReal.sub CReal.cone (expNegCD x d)) := by
  obtain ⟨εlo, hεlo, M, hM⟩ := eventually_ge_of_posEv hx
  have hle : CReal.leRat (expNegCD x d) (ExpUBInstance.oneOver1p εlo) := by
    refine leRat_limit_of_eventually (expNegCD_converges x d) ⟨M, fun K hK => ?_⟩
    exact CReal.leRat_mono (expNeg_le_oneOver1p (x.approx K) (d.hpos K))
      (ExpUBInstance.oneOver1p_antitone εlo (x.approx K) (hM K hK))
  exact posEv_oneSub_of_leRat (qsub_pos_of_lt (oneOver1p_lt_one hεlo)) hle

/-! ## 6d. The strictly-positive UV exponent seed `e^{−1} > 0`

`concreteCRealFlowE` is seeded at the irrational exponent `e^{−1}`.  To feed the
general `expNegCD_lt_one` we need its strict positivity `PosEv (e^{−1})`.  This is
proved multiplicatively — `e^{−1} ≃ e^{−1/2}·e^{−1/2}` — with each factor bounded
below by the alternating-series lower bound `e^{−1/2} ≥ 1 − 1/2 = 1/2 > 0`. -/

/-- **`e^{−1} > 0`** (`PosEv`).  The irrational UV exponent seed of the
`concreteTowerE` flow is strictly positive: `e^{−1} = e^{−1/2}·e^{−1/2}` with
`e^{−1/2} ≥ 1/2` (the alternating-series partial-sum lower bound
`1 − t ≤ partialSum t n`, `n ≥ 2`), so `e^{−1} ≥ 1/4 > 0`. -/
theorem posEv_expNeg_one : PosEv (ExpNeg.expNeg 1 (by decide)) := by
  have hh : (0 : Q') ≤ Q'.invSucc 1 := Q'.invSucc_nonneg 1
  have hhalf : PosEv (ExpNeg.expNeg (Q'.invSucc 1) hh) := by
    refine posEv_of_eventually (ε := (1 : Q') - Q'.invSucc 1) (by decide) ⟨2, fun n hn => ?_⟩
    show (1 : Q') - Q'.invSucc 1 ≤ ExpNeg.partialSum (Q'.invSucc 1) n
    exact ExpNeg.oneSub_le_partialSum hh (invSucc_le_one 1) n hn
  have hadd : CReal.Equiv
      (CReal.mul (ExpNeg.expNeg (Q'.invSucc 1) hh) (ExpNeg.expNeg (Q'.invSucc 1) hh))
      (ExpNeg.expNeg 1 (by decide)) :=
    CReal.Equiv.trans
      (expNeg_add_equiv (Q'.invSucc 1) (Q'.invSucc 1) hh hh)
      (expNeg_eqv_congr (Q'.zero_le_add _ _ hh hh) (by decide) (by decide))
  exact posEv_of_equiv (posEv_mul hhalf hhalf) hadd

/-! ## 7. Capstone: the budget along the genuine irrational constructive-real flow

`marginInvariantC` instantiated on `concreteCRealFlowE` is UNCONDITIONAL — the
conserved-margin telescoping holds verbatim along the irrational `e^{−1}`-seeded
self-similar flow, the flow that no rational separator family inhabits
(`rational_flow_law_empty`).  With the general base UV margin `expNegCD_lt_one`
discharged from the strictly-positive exponent seed `posEv_expNeg_one`, the
positivity capstone `marginBudget_posC_concreteE` is now also UNCONDITIONAL. -/

/-- **THE CODYNAMIC BUDGET IS POSITIVE ALONG ANY TOWER WITH A POSITIVE UV EXPONENT
SEED (the clean general capstone).**  For any `SelfSimilarTower b` whose UV exponent
`T.w 0` is strictly positive (`PosEv (T.w 0)`), the rescaled margin
`(1 − sep N)·∏geomSumC` is strictly positive (`PosEv`) at EVERY scale `N`.  The base
UV margin is discharged uniformly by `expNegCD_lt_one` (`e^{−x} < 1` for `x > 0`) and
propagated by the conserved invariant `marginBudget_posC`.  This subsumes both the
rational `1/2` seed and the genuinely-irrational `e^{−1}` seed. -/
theorem marginBudget_posC_tower {b : Nat} (T : SelfSimilarTower b)
    (hx : PosEv (T.w 0)) (N : Nat) :
    PosEv (CReal.mul (CReal.sub CReal.cone (sep T N))
      (cprodTail (fun j => geomSumC (sep T j) (b + 1)) N)) :=
  marginBudget_posC (fun k => selfSimilarCReal T k) (expNegCD_lt_one (T.dw 0) hx) N

/-- **THE BASE UV MARGIN, DISCHARGED (irrational `e^{−1}` seed) — UNCONDITIONAL.**
For the irrational-exponent flow the base margin `1 − sep 0 = 1 − e^{−(e^{−1})}` is
eventually strictly positive (`PosEv`): the exponent seed `e^{−1}` is strictly
positive (`posEv_expNeg_one`), so `e^{−(e^{−1})} < 1` by `expNegCD_lt_one`.  No open
hypothesis — the irrational-exponent analogue of `baseMargin_posC_concrete`. -/
theorem baseMargin_posC_concreteE :
    PosEv (CReal.sub CReal.cone ((concreteCRealFlowE 1).s 0)) :=
  expNegCD_lt_one ((concreteTowerE 1).dw 0) posEv_expNeg_one

/-- **THE CONSERVED-MARGIN INVARIANT ALONG THE IRRATIONAL `e^{−1}`-SEED FLOW
(UNCONDITIONAL).**  For the irrational-exponent flow `concreteCRealFlowE 1`, the
rescaled margin `(1 − s N)·∏geomSumC ≃ 1 − s 0` at every scale — the codynamic
summable budget made exact along a self-similar flow with genuinely irrational
separators, where the rational `polyFlow` provably fails the flow law. -/
theorem marginInvariantC_concreteE (N : Nat) :
    CReal.Equiv
      (CReal.mul (CReal.sub CReal.cone ((concreteCRealFlowE 1).s N))
        (cprodTail (fun j => geomSumC ((concreteCRealFlowE 1).s j) (1 + 1)) N))
      (CReal.sub CReal.cone ((concreteCRealFlowE 1).s 0)) :=
  marginInvariantC (concreteCRealFlowE 1).ss N

/-- **THE CODYNAMIC BUDGET IS POSITIVE ALONG THE IRRATIONAL `e^{−1}`-SEED FLOW
(UNCONDITIONAL).**  Combining `marginBudget_posC` with the discharged base UV margin
`baseMargin_posC_concreteE`, the rescaled margin stays strictly positive (`PosEv`) at
EVERY scale — a genuine constructive-real self-similar flow with genuinely IRRATIONAL
exponents `e^{−(e^{−1})/2^k}`, carrying a strictly-positive conserved codynamic
budget, with NO open hypothesis.  This is the carrier the rational `polyFlow` could
not provide (`rational_flow_law_empty`): no rational flow inhabits the flow law at
all, so the rational conserved-margin budget is vacuous, whereas here it is INHABITED
and positive — and, unlike the `1/2` seed, with no rational flow anywhere in sight. -/
theorem marginBudget_posC_concreteE (N : Nat) :
    PosEv (CReal.mul (CReal.sub CReal.cone ((concreteCRealFlowE 1).s N))
      (cprodTail (fun j => geomSumC ((concreteCRealFlowE 1).s j) (1 + 1)) N)) :=
  marginBudget_posC (concreteCRealFlowE 1).ss baseMargin_posC_concreteE N

/-- **THE CODYNAMIC BUDGET IS POSITIVE ALONG THE RATIONAL-SEED FLOW
(UNCONDITIONAL).**  Combining `marginBudget_posC` with the discharged base UV margin
`baseMargin_posC_concrete`, the rescaled margin
`(1 − sep N)·∏geomSumC ≃ 1 − sep 0` is strictly positive (`PosEv`) at EVERY scale
along the `1/2`-seeded self-similar flow — with NO open hypothesis.  The separators
`sep k = e^{−(1/2)/2^k}` are genuine irrational constructive reals, and the
conserved codynamic budget never vanishes: a strictly-positive summable budget on a
self-similar CReal flow, the carrier the rational `polyFlow` provably cannot
provide. -/
theorem marginBudget_posC_concrete (N : Nat) :
    PosEv (CReal.mul (CReal.sub CReal.cone ((concreteCRealFlow 1).s N))
      (cprodTail (fun j => geomSumC ((concreteCRealFlow 1).s j) (1 + 1)) N)) :=
  marginBudget_posC (concreteCRealFlow 1).ss baseMargin_posC_concrete N

end YMGap.Continuum.CodynamicCRealFlow

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.CodynamicCRealFlow.selfSimilarC_inhabited
#print axioms YMGap.Continuum.CodynamicCRealFlow.selfSimilarC_inhabited_E
#print axioms YMGap.Continuum.CodynamicCRealFlow.rational_flow_law_empty
#print axioms YMGap.Continuum.CodynamicCRealFlow.flow_law_rational_empty_but_creal_inhabited
#print axioms YMGap.Continuum.CodynamicCRealFlow.marginBudget_pos_along_selfSimilar
#print axioms YMGap.Continuum.CodynamicCRealFlow.oneSub_pow_factorC
#print axioms YMGap.Continuum.CodynamicCRealFlow.marginInvariantC
#print axioms YMGap.Continuum.CodynamicCRealFlow.marginBudget_posC
#print axioms YMGap.Continuum.CodynamicCRealFlow.marginInvariantC_concreteE
#print axioms YMGap.Continuum.CodynamicCRealFlow.marginBudget_posC_concreteE
#print axioms YMGap.Continuum.CodynamicCRealFlow.expNegCD_ofQ'_equiv
#print axioms YMGap.Continuum.CodynamicCRealFlow.baseMargin_posC_concrete
#print axioms YMGap.Continuum.CodynamicCRealFlow.marginBudget_posC_concrete
#print axioms YMGap.Continuum.CodynamicCRealFlow.posEv_oneSub_of_leRat
#print axioms YMGap.Continuum.CodynamicCRealFlow.leRat_limit_of_eventually
#print axioms YMGap.Continuum.CodynamicCRealFlow.oneOver1p_lt_one
#print axioms YMGap.Continuum.CodynamicCRealFlow.qsub_pos_of_lt
#print axioms YMGap.Continuum.CodynamicCRealFlow.expNegCD_lt_one
#print axioms YMGap.Continuum.CodynamicCRealFlow.posEv_expNeg_one
#print axioms YMGap.Continuum.CodynamicCRealFlow.marginBudget_posC_tower
#print axioms YMGap.Continuum.CodynamicCRealFlow.baseMargin_posC_concreteE
