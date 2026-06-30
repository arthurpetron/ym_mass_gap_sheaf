/-
Track B / R2 — SPECTRAL LOCALIZATION of the mass gap: is the gap a LOW-MODE
(eigenvalue) quantity, so the bulk `Θ(1)` bond-moving defect — sitting on HEAVIER
excitations — cannot close it?  VERDICT: **(a) LOCALIZATION HOLDS** in the
gap-relevant (eigenvalue) sense, with the bulk eigenvalues a `Θ(1)` margin BELOW
the gap edge.  The apparent `Θ(1)` obstruction of `BulkModeCrux` lives in the
WEIGHT/MULTIPLICITY (the spectral DENSITY), NOT in the eigenvalue LOCATION.

# The two objects that must NOT be conflated

The reconstructed mass gap is `Δ = 1 − sep`, where `sep` is the LOCATED second
eigenvalue of the compact (finite) transfer operator
(`Continuum/LocatedSpectralGap.lean`, `Continuum/GNSDynamics.lean`): the
largest EXCITED transfer EIGENVALUE, strictly below the vacuum eigenvalue `1`.
The vacuum-normalized transfer eigenvalue of the SU(2) spin-`s` mode is the bare
heat kernel

    eigA w s  =  w^{C₄(s)}        (no multiplicity factor),

with the vacuum `s = 0` at `eigA w 0 = w^0 = 1` and the first excited `s = 1` at
`eigA w 1 = w^{C₄(1)} = w³` — THE gap edge.

This must be sharply distinguished from the heat-kernel-SCALED coefficient

    Kτ(s)  =  (s+1)·w^{C₄(s)}  =  dimQ s · eigA w s     (`= coeffW w s`),

which is the mode's WEIGHT (eigenvalue × degeneracy) — the contribution of the
spin-`s` sector to the character/correlator, and the topology in which the
bond-moving defect's SUMMABILITY is measured.  Multiplicity `(s+1) = dimQ s`
moves the WEIGHT but does NOT move the EIGENVALUE; the gap (a second-eigenvalue
separation) is multiplicity-BLIND.

# The computation the crux turns on (`Kτ(s)/Kτ(1)` vs the eigenvalue ratio)

Factoring through the gap edge (`eig_factor`, `Ktau_factor`):

    eigA w s / eigA w 1  =  w^{C₄(s) − 3}                 (= `sepFactor w s`)
    Kτ(s)   / Kτ(1)      =  (dimQ s / dimQ 1)·w^{C₄(s)−3}
                         =  ((s+1)/2)·w^{C₄(s)−3}.

At the BULK scale `s ∼ 1/√(1−w)` (`C₄(s)·(1−w) = Θ(1)`):

  * EIGENVALUE ratio `w^{C₄(s)−3} → e^{−1}` — BOUNDED below `1`.  Concretely
    (`bulk_eigA_le`), on the bulk window `C₄(s)·(1−w) ≥ 1/2` the bulk eigenvalue
    obeys `eigA w s ≤ 2/3`, a constant `Θ(1)` below the gap edge `eigA w 1 = w³`,
    which `→ 1`.  ⇒ the bulk sits STRICTLY below the gap edge.
  * Kτ ratio `((s+1)/2)·e^{−1} → ∞` — UNBOUNDED, purely because the multiplicity
    `(s+1) ∼ 1/√(1−w) → ∞`.

So the SAME data gives OPPOSITE answers: the gap (eigenvalue) LOCALIZES; the
weight (Kτ) does not.  The Kτ blow-up is exactly the "fake-divergence trap"
documented in `BondMovingScaledNorm` (the count of active modes diverges though
each eigenvalue stays `O(1)`); it is the spectral DENSITY, not the gap location.

# What is PROVED here (genuine `Q'`/`Nat`, axiom-clean)

  * `eigA` / `eigA_le_one` / `gapEdge_dominates` — the vacuum-normalized transfer
    eigenvalue, `≤ 1`, and the `s = 1` DOMINANCE: among excited modes (`s ≥ 1`)
    the eigenvalue is MAXIMIZED at `s = 1` (the gap edge), all higher modes below.
  * `sepFactor` / `eig_factor` / `sepFactor_le_one` — the eigenvalue ratio
    `eigA w s = eigA w 1 · w^{C₄(s)−3}`, the separation factor `≤ 1`.
  * `Ktau_factor` — `coeffW w s = (dimQ s · w^{C₄(s)−3})·eigA w 1`: the SAME
    bounded eigenvalue factor, times the unbounded MULTIPLICITY `dimQ s = s+1`.
    This is WHY the Kτ ratio blows up while the eigenvalue ratio stays bounded.
  * **`bulk_eigA_le`** (THE SHARP BOUND).  On the bulk window
    `1/2 ≤ C₄(s)·(1−w)`, `eigA w s ≤ 2/3` — the bulk eigenvalue is bounded BELOW
    `1` by an absolute constant (the constructive `e^{−1/2}`-surrogate; PROOF
    reuses `BulkModeCrux.subA`: `(1−w)·(m·w^m) ≤ 1 − w^m`, so on `m(1−w) ≥ 1/2`,
    `(3/2)·w^m ≤ 1`).
  * `gapEdge_ge` — on the near-continuum regime `1 − w ≤ 1/12`, the gap edge
    `eigA w 1 = w³ ≥ 3/4` (Bernoulli).
  * **`bulk_below_gapEdge`** (THE LOCALIZATION VERDICT).  On
    `(1 − w ≤ 1/12) ∧ (C₄(s)·(1−w) ≥ 1/2)`,
        `eigA w 1 − eigA w s  ≥  1/12`  —  a POSITIVE CONSTANT margin.
    The bulk eigenvalues sit `≥ 1/12` BELOW the gap edge.  Localization HOLDS.
  * **`SpectralLocalization` / `localization_holds`** — the WEAKEST sufficient
    statement, as `Type`-level data: a bond-moved (perturbed) transfer spectrum
    `eig'` whose per-mode EIGENVALUE shift is `≤ 1/12` on the bulk has every bulk
    mode's perturbed eigenvalue STILL `≤` the gap edge `eigA w 1` (the bulk does
    not rise to the edge).  Non-vacuously inhabited (`trivialLocalization`, the
    unperturbed spectrum).

# THE HONEST DIAGNOSIS (for the next iteration)

"Gap = low-mode quantity" is TRUE in the EIGENVALUE sense: the gap edge is the
`s = 1` eigenvalue and the bulk eigenvalues are a `Θ(1)` (≥ 1/12) margin below
it.  The `BulkModeCrux` `Θ(1)` defect (`deltaRen ≥ 1/128` on the bulk) is a
WEIGHT defect — it perturbs `Kτ` (mass/density), where the multiplicity makes
the bulk dominant; it is NOT, a priori, an EIGENVALUE shift.  For the bulk to
CLOSE the gap it would have to LIFT a bulk eigenvalue from `≤ 2/3` up past the
edge `w³ ≥ 3/4` — an eigenvalue shift `≥ 1/12`, a `Θ(1)` move that a per-mode
weight defect does not directly produce.

So the bulk obstruction and the gap are DECOUPLED.  The sole remaining residual
is the BRIDGE `weight defect ⟹ eigenvalue shift`: the named hypothesis
`bulk_shift` of `SpectralLocalization` (`shift s ≤ 1/12`).  This is a genuinely
DIFFERENT — and far more plausible — obligation than the scaled-norm summability
that `BulkModeCrux` showed FAILS, because eigenvalue perturbation theory is
multiplicity-blind.  The graded (low-mode) budget is therefore LEGITIMATE FOR
THE GAP, even though it is NOT legitimate for the scaled-norm defect.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, reusing `BulkModeCrux.subA` / `qpow_ge_bernoulli`,
`qpow_add`, `qpow_antitone`, `qpow_le_one`, decidable `Q'` numeric facts.  Every
load-bearing declaration is gated with `#print axioms`; permitted output is
`propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide` (only
`decide` on decidable facts), no `sorry`.  All witnesses are `Type`-level data.
-/

import YMGap.Continuum.GNSDynamics
import YMGap.Continuum.BondMovingScaledNorm
import YMGap.Continuum.BondMovingQuadratic
import YMGap.Continuum.BulkModeCrux

namespace YMGap.Continuum.SpectralLocalizationCrux

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BulkModeCrux

/-! ## 0. Local rational constants (decidable) -/

/-- `2/3` — the bulk-eigenvalue ceiling. -/ def q23 : Q' := Q'.mkPos 2 3 (by decide)
/-- `3/2`. -/ def q32 : Q' := Q'.mkPos 3 2 (by decide)
/-- `1/12` — the localization margin. -/ def q112 : Q' := Q'.mkPos 1 12 (by decide)

/-- `c4` is monotone (`c4 s = s·(s+2)`); local copy to avoid an extra import. -/
theorem c4_le_c4 {s t : Nat} (h : s ≤ t) : c4 s ≤ c4 t := by
  show s * (s + 2) ≤ t * (t + 2)
  exact Nat.mul_le_mul h (by omega)

/-! ## 1. The vacuum-normalized transfer eigenvalue and `s = 1` dominance -/

/-- **The vacuum-normalized transfer eigenvalue of the spin-`s` mode**:
`eigA w s = w^{C₄(s)}` (the bare heat kernel, NO multiplicity).  Vacuum
`eigA w 0 = 1`; gap edge `eigA w 1 = w³`. -/
def eigA (w : Q') (s : Nat) : Q' := qpow w (c4 s)

/-- `eigA w 0 = 1` (the vacuum eigenvalue). -/
theorem eigA_zero (w : Q') : eigA w 0 = 1 := by
  show qpow w (c4 0) = 1
  rw [c4_zero]; rfl

theorem eigA_nonneg {w : Q'} (hw : (0 : Q') ≤ w) (s : Nat) : (0 : Q') ≤ eigA w s :=
  qpow_nonneg w hw (c4 s)

/-- Every transfer eigenvalue is `≤ 1` (the vacuum eigenvalue). -/
theorem eigA_le_one {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (s : Nat) :
    eigA w s ≤ (1 : Q') :=
  qpow_le_one hw0 hw1 (c4 s)

/-- **`s = 1` DOMINANCE (the gap edge).**  Among the EXCITED modes (`s ≥ 1`) the
transfer eigenvalue is MAXIMIZED at `s = 1`: `eigA w s ≤ eigA w 1`.  So the
located separator `sep` is the `s = 1` eigenvalue and every higher mode lies at or
below it (the eigenvalue `w^{C₄(s)}` is antitone in `C₄(s)`, which increases with
`s`). -/
theorem gapEdge_dominates {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    {s : Nat} (hs : 1 ≤ s) : eigA w s ≤ eigA w 1 := by
  show qpow w (c4 s) ≤ qpow w (c4 1)
  exact qpow_antitone hw0 hw1 (c4 1) (c4 s) (c4_le_c4 hs)

/-! ## 2. The eigenvalue ratio (the separation factor `w^{C₄(s)−3}`) -/

/-- **The separation factor** `sepFactor w s = w^{C₄(s) − C₄(1)} = w^{C₄(s)−3}` —
the vacuum-normalized eigenvalue RATIO `eigA w s / eigA w 1`. -/
def sepFactor (w : Q') (s : Nat) : Q' := qpow w (c4 s - c4 1)

/-- **The eigenvalue-ratio factorization**: for an excited mode `s ≥ 1`,
`eigA w s = eigA w 1 · w^{C₄(s)−3}` — the gap-edge eigenvalue times the
separation factor. -/
theorem eig_factor {w : Q'} (s : Nat) (hs : 1 ≤ s) :
    (eigA w s).eqv (eigA w 1 * sepFactor w s) := by
  have hsplit : c4 s = c4 1 + (c4 s - c4 1) := by
    have hc : c4 1 ≤ c4 s := c4_le_c4 hs
    omega
  show (qpow w (c4 s)).eqv (qpow w (c4 1) * qpow w (c4 s - c4 1))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (congrArg (qpow w) hsplit))
    (qpow_add w (c4 1) (c4 s - c4 1))

/-- The separation factor is `≤ 1` (the eigenvalue ratio is bounded by `1`: the
bulk lies at or below the gap edge). -/
theorem sepFactor_le_one {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (s : Nat) : sepFactor w s ≤ (1 : Q') :=
  qpow_le_one hw0 hw1 (c4 s - c4 1)

/-- **The `Kτ` factorization — WHERE the blow-up comes from.**  For `s ≥ 1`,

    coeffW w s  =  Kτ(s)  =  (dimQ s · w^{C₄(s)−3}) · eigA w 1,

i.e. the SAME bounded eigenvalue factor `eigA w 1` and separation factor
`w^{C₄(s)−3} ≤ 1` as the eigenvalue ratio, MULTIPLIED by the degeneracy
`dimQ s = (s+1)`.  So `Kτ(s)/Kτ(1) = ((s+1)/2)·w^{C₄(s)−3}`: the eigenvalue part
is bounded, and the UNBOUNDED growth is entirely the multiplicity `dimQ s → ∞` —
the spectral density, not the gap location. -/
theorem Ktau_factor {w : Q'} (s : Nat) (hs : 1 ≤ s) :
    (coeffW w s).eqv ((dimQ s * sepFactor w s) * eigA w 1) := by
  show (dimQ s * qpow w (c4 s)).eqv ((dimQ s * sepFactor w s) * eigA w 1)
  have hf : (qpow w (c4 s)).eqv (eigA w 1 * sepFactor w s) := eig_factor s hs
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (dimQ s) _ _ hf) ?_
  -- dimQ s · (eigA1 · sep) ≃ (dimQ s · sep) · eigA1
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (dimQ s) _ _ (Q'.mul_comm_eqv (eigA w 1) (sepFactor w s))) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv (dimQ s) (sepFactor w s) (eigA w 1))

/-! ## 3. THE SHARP BOUND — the bulk eigenvalue is `≤ 2/3` (a `Θ(1)` ceiling)

The bulk eigenvalue is bounded BELOW `1` by an absolute constant on the bulk
window `C₄(s)·(1−w) ≥ 1/2`.  This is the constructive `e^{−1/2}`-surrogate; the
PROOF reuses `BulkModeCrux.subA` (`(1−w)·(m·w^m) ≤ 1 − w^m`): on `m(1−w) ≥ 1/2`,
`(1/2)·w^m ≤ (1−w)·(m·w^m) ≤ 1 − w^m`, hence `(3/2)·w^m ≤ 1`, i.e. `w^m ≤ 2/3`. -/

/-- **THE BULK EIGENVALUE CEILING.**  For `0 ≤ w ≤ 1` and a mode `s` on the bulk
window `1/2 ≤ C₄(s)·(1−w)`, the transfer eigenvalue is `≤ 2/3`:

    eigA w s  ≤  2/3,

a constant `Θ(1)` below the vacuum eigenvalue `1` — the bulk does NOT crowd the
top of the spectrum (unlike the gap edge `eigA w 1 = w³ → 1`). -/
theorem bulk_eigA_le {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (s : Nat)
    (hlo : q12 ≤ Q'.ofNat (c4 s) * ((1 : Q') - w)) :
    eigA w s ≤ q23 := by
  have hxnn : (0 : Q') ≤ qpow w (c4 s) := qpow_nonneg w hw0 (c4 s)
  -- subA at i = C₄(s):  (1−w)·(C₄(s)·w^{C₄ s}) ≤ 1 − w^{C₄ s}
  have hsub : ((1 : Q') - w) * (Q'.ofNat (c4 s) * qpow w (c4 s))
      ≤ (1 : Q') - qpow w (c4 s) := subA hw0 hw1 (c4 s)
  -- reassociate (1−w)·(m·x) ≃ (m·(1−w))·x
  have hre : (((1 : Q') - w) * (Q'.ofNat (c4 s) * qpow w (c4 s))).eqv
      ((Q'.ofNat (c4 s) * ((1 : Q') - w)) * qpow w (c4 s)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv ((1 : Q') - w) (Q'.ofNat (c4 s)) (qpow w (c4 s)))) ?_
    exact Q'.mul_eqv_congr_right _ _ (qpow w (c4 s))
      (Q'.mul_comm_eqv ((1 : Q') - w) (Q'.ofNat (c4 s)))
  -- q12·x ≤ (m·(1−w))·x  (window hypothesis, x ≥ 0)
  have hhalf1 : q12 * qpow w (c4 s) ≤ (Q'.ofNat (c4 s) * ((1 : Q') - w)) * qpow w (c4 s) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hlo hxnn
  -- chain to the deficit:  q12·x ≤ 1 − x
  have hhalf : q12 * qpow w (c4 s) ≤ (1 : Q') - qpow w (c4 s) :=
    Q'.le_trans' _ _ _ hhalf1 (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hre) hsub)
  -- x + q12·x ≤ 1
  have hadd : qpow w (c4 s) + q12 * qpow w (c4 s) ≤ (1 : Q') := by
    have hstep : qpow w (c4 s) + q12 * qpow w (c4 s)
        ≤ qpow w (c4 s) + ((1 : Q') - qpow w (c4 s)) :=
      Q'.add_le_add_left (qpow w (c4 s)) _ _ hhalf
    refine Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv ?_)
    -- x + (1 + −x) ≃ 1
    show (qpow w (c4 s) + ((1 : Q') + -(qpow w (c4 s)))).eqv (1 : Q')
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (qpow w (c4 s)) _ _ (Q'.add_comm_eqv (1 : Q') (-(qpow w (c4 s))))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv (qpow w (c4 s)) (-(qpow w (c4 s))) (1 : Q'))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (1 : Q') (Q'.add_neg_self_eqv (qpow w (c4 s)))) ?_
    exact Q'.eqv_of_eq (Q'.zero_add' (1 : Q'))
  -- x + q12·x ≃ q32·x, so q32·x ≤ 1
  have hq32 : q32 * qpow w (c4 s) ≤ (1 : Q') := by
    have he : (q32 * qpow w (c4 s)).eqv (qpow w (c4 s) + q12 * qpow w (c4 s)) := by
      -- q32·x ≃ (1 + q12)·x ≃ 1·x + q12·x ≃ x + q12·x
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (qpow w (c4 s)) (by decide : (q32).eqv ((1 : Q') + q12))) ?_
      refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv (1 : Q') q12 (qpow w (c4 s))) ?_
      exact Q'.add_eqv_congr_right _ _ (q12 * qpow w (c4 s)) (Q'.one_mul_eqv (qpow w (c4 s)))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he) hadd
  -- x ≤ 2/3 :  q23·(q32·x) ≤ q23·1, collapse q23·q32 ≃ 1
  have hmul : q23 * (q32 * qpow w (c4 s)) ≤ q23 * (1 : Q') :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hq32 (by decide : (0 : Q') ≤ q23)
  have hcollapse : (q23 * (q32 * qpow w (c4 s))).eqv (qpow w (c4 s)) := by
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv q23 q32 (qpow w (c4 s)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (qpow w (c4 s)) (by decide : (q23 * q32).eqv (1 : Q'))) ?_
    exact Q'.one_mul_eqv (qpow w (c4 s))
  show qpow w (c4 s) ≤ q23
  refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv hcollapse) ?_
  exact Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv (Q'.mul_one_eqv q23))

/-! ## 4. The gap edge stays near `1`, and the LOCALIZATION VERDICT -/

/-- **The gap edge near `1`.**  On the near-continuum regime `1 − w ≤ 1/12`, the
gap-edge eigenvalue `eigA w 1 = w³ ≥ 3/4` (Bernoulli `w³ ≥ 1 − 3(1−w)`).  So the
gap edge approaches the vacuum eigenvalue `1` — the lightest excitation. -/
theorem gapEdge_ge {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hnc : (1 : Q') - w ≤ q112) : q34 ≤ eigA w 1 := by
  have hb : (1 : Q') - Q'.ofNat (c4 1) * ((1 : Q') - w) ≤ qpow w (c4 1) :=
    qpow_ge_bernoulli hw0 hw1 (c4 1)
  -- C₄(1)·(1−w) ≤ C₄(1)·(1/12) = 1/4
  have hm : Q'.ofNat (c4 1) * ((1 : Q') - w) ≤ q14 := by
    have h1 : Q'.ofNat (c4 1) * ((1 : Q') - w) ≤ Q'.ofNat (c4 1) * q112 :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ hnc (zero_le_ofNat (c4 1))
    exact Q'.le_trans' _ _ _ h1 (by decide : Q'.ofNat (c4 1) * q112 ≤ q14)
  -- 3/4 ≤ 1 − C₄(1)·(1−w)
  have h34 : q34 ≤ (1 : Q') - Q'.ofNat (c4 1) * ((1 : Q') - w) := by
    have hneg : -q14 ≤ -(Q'.ofNat (c4 1) * ((1 : Q') - w)) := Q'.neg_le_neg hm
    have hstep : (1 : Q') + -q14 ≤ (1 : Q') + -(Q'.ofNat (c4 1) * ((1 : Q') - w)) :=
      Q'.add_le_add_left (1 : Q') _ _ hneg
    exact Q'.le_trans' _ _ _ (by decide : q34 ≤ (1 : Q') + -q14) hstep
  exact Q'.le_trans' _ _ _ h34 hb

/-- **THE LOCALIZATION VERDICT (case a).**  On the near-continuum regime
`1 − w ≤ 1/12` with a bulk mode `C₄(s)·(1−w) ≥ 1/2`,

    eigA w 1  −  eigA w s   ≥   1/12,

a POSITIVE CONSTANT margin: the bulk transfer eigenvalues sit `≥ 1/12` BELOW the
gap edge `eigA w 1`.  The gap is a LOW-MODE (`s = 1`) quantity; the bulk modes are
genuinely heavier (their eigenvalues bounded away from the edge), so a bulk
perturbation must produce a `Θ(1)` EIGENVALUE shift to reach the edge.  PROOF:
`eigA w 1 ≥ 3/4` (`gapEdge_ge`), `eigA w s ≤ 2/3` (`bulk_eigA_le`), and
`3/4 − 2/3 = 1/12`. -/
theorem bulk_below_gapEdge {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (s : Nat)
    (hnc : (1 : Q') - w ≤ q112)
    (hlo : q12 ≤ Q'.ofNat (c4 s) * ((1 : Q') - w)) :
    q112 ≤ eigA w 1 - eigA w s := by
  have hge : q34 ≤ eigA w 1 := gapEdge_ge hw0 hw1 hnc
  have hle : eigA w s ≤ q23 := bulk_eigA_le hw0 hw1 s hlo
  have hneg : -q23 ≤ -(eigA w s) := Q'.neg_le_neg hle
  have hsum : q34 + -q23 ≤ eigA w 1 + -(eigA w s) := qadd_le_add hge hneg
  exact Q'.le_trans' _ _ _ (by decide : q112 ≤ q34 + -q23) hsum

/-! ## 5. `SpectralLocalization` — the WEAKEST sufficient statement, and the gap

The weakest sufficient statement for "the bulk `Θ(1)` defect does not close the
gap": a bond-moved (perturbed) transfer spectrum `eig'` whose per-mode EIGENVALUE
shift on the bulk is below the localization margin `1/12` leaves every bulk mode's
perturbed eigenvalue at or below the gap edge — so the gap edge remains the
`s = 1` mode.  The load-bearing field is `bulk_shift` (`shift s ≤ 1/12`): a
EIGENVALUE-shift bound, the honest residual (the `weight defect ⟹ eigenvalue
shift` bridge), DIFFERENT from — and more plausible than — the scaled-norm
summability that `BulkModeCrux` showed FAILS. -/

/-- **The spectral-localization certificate** for the bond-moved transfer
operator at weight `w`.  `eig'` is the perturbed (bond-moved) vacuum-normalized
spectrum; `shift` the per-mode eigenvalue-shift budget; the perturbation raises
each eigenvalue by at most its shift; and on the bulk the shift is below the
localization margin `1/12` (the named honest input — NOT faked). -/
structure SpectralLocalization (w : Q') : Type where
  /-- The perturbed (bond-moved) vacuum-normalized transfer spectrum. -/
  eig' : Nat → Q'
  /-- The per-mode eigenvalue-shift budget induced by bond-moving. -/
  shift : Nat → Q'
  /-- Near-continuum regime. -/
  hnc : (1 : Q') - w ≤ q112
  /-- The perturbation raises each eigenvalue by at most its shift budget. -/
  pert : ∀ s, eig' s ≤ eigA w s + shift s
  /-- **THE named honest hypothesis**: the bulk eigenvalue-shift is below the
  localization margin `1/12` (the `weight defect ⟹ eigenvalue shift` bridge). -/
  bulk_shift : ∀ s, shift s ≤ q112

/-- **`localization_holds` — the gap survives the bulk perturbation.**  Under a
`SpectralLocalization`, every bulk mode (`C₄(s)·(1−w) ≥ 1/2`) has perturbed
eigenvalue STILL at or below the gap edge:

    eig' s  ≤  eigA w 1,

so the bond-moved bulk does NOT rise to the `s = 1` gap edge; the gap remains a
low-mode quantity.  PROOF: `eig' s ≤ eigA w s + shift s ≤ 2/3 + 1/12 = 3/4 ≤
eigA w 1`. -/
theorem localization_holds {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (L : SpectralLocalization w) (s : Nat)
    (hlo : q12 ≤ Q'.ofNat (c4 s) * ((1 : Q') - w)) :
    L.eig' s ≤ eigA w 1 := by
  have h1 : L.eig' s ≤ eigA w s + L.shift s := L.pert s
  have hb : eigA w s ≤ q23 := bulk_eigA_le hw0 hw1 s hlo
  have hsh : L.shift s ≤ q112 := L.bulk_shift s
  have hsum : eigA w s + L.shift s ≤ q23 + q112 := qadd_le_add hb hsh
  have h34 : q23 + q112 ≤ eigA w 1 :=
    Q'.le_trans' _ _ _ (by decide : q23 + q112 ≤ q34) (gapEdge_ge hw0 hw1 L.hnc)
  exact Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ hsum h34)

/-- **Non-vacuity** of `SpectralLocalization`: the UNPERTURBED spectrum (`eig' =
eigA`, `shift = 0`) is a localization certificate on any near-continuum weight.
This is NOT the bond-moved spectrum; it certifies the interface is non-vacuous and
that the conclusion `localization_holds` is genuinely inhabited. -/
def trivialLocalization (w : Q') (hnc : (1 : Q') - w ≤ q112) :
    SpectralLocalization w where
  eig' := eigA w
  shift := fun _ => 0
  hnc := hnc
  pert := fun s => Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.add_zero' (eigA w s)))
  bulk_shift := fun _ => (by decide : (0 : Q') ≤ q112)

/-! ## 6. Demo — the localization margin FIRES at a concrete bulk mode

Reusing `BulkModeCrux`'s demo regime: at `w = 29/32` (`1 − w = 3/32`) the mode
`s = 2` has `C₄(2)·(1−w) = 8·(3/32) = 3/4 ≥ 1/2` (bulk window) — but `3/32` is NOT
`≤ 1/12`, so we move slightly closer to the continuum. -/

/-- The demo weight `w = 95/96` (`1 − w = 1/96 ≤ 1/12`). -/
def demoW : Q' := Q'.mkPos 95 96 (by decide)

theorem demoW_pos : (0 : Q') ≤ demoW := by decide
theorem demoW_le_one : demoW ≤ (1 : Q') := by decide
theorem demoW_nc : (1 : Q') - demoW ≤ q112 := by decide

/-- A bulk mode at `w = 95/96`: `C₄(s) = 48` gives `48·(1/96) = 1/2 ≥ 1/2`.
`C₄(s) = s(s+2) = 48` at `s = 6` (`6·8 = 48`).  So `s = 6` is on the bulk window. -/
theorem demo_bulk_window : q12 ≤ Q'.ofNat (c4 6) * ((1 : Q') - demoW) := by decide

/-- **The localization margin fires at `w = 95/96`, `s = 6`.**  The bulk mode
`s = 6` sits `≥ 1/12` below the gap edge: `eigA (95/96) 1 − eigA (95/96) 6 ≥
1/12`.  A concrete, non-vanishing eigenvalue separation between a genuine bulk
mode and the gap edge — localization is REAL, not posited. -/
theorem demo_localization : q112 ≤ eigA demoW 1 - eigA demoW 6 :=
  bulk_below_gapEdge demoW_pos demoW_le_one 6 demoW_nc demo_bulk_window

end YMGap.Continuum.SpectralLocalizationCrux

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.SpectralLocalizationCrux.c4_le_c4
#print axioms YMGap.Continuum.SpectralLocalizationCrux.eigA_zero
#print axioms YMGap.Continuum.SpectralLocalizationCrux.eigA_le_one
#print axioms YMGap.Continuum.SpectralLocalizationCrux.gapEdge_dominates
#print axioms YMGap.Continuum.SpectralLocalizationCrux.eig_factor
#print axioms YMGap.Continuum.SpectralLocalizationCrux.sepFactor_le_one
#print axioms YMGap.Continuum.SpectralLocalizationCrux.Ktau_factor
#print axioms YMGap.Continuum.SpectralLocalizationCrux.bulk_eigA_le
#print axioms YMGap.Continuum.SpectralLocalizationCrux.gapEdge_ge
#print axioms YMGap.Continuum.SpectralLocalizationCrux.bulk_below_gapEdge
#print axioms YMGap.Continuum.SpectralLocalizationCrux.localization_holds
#print axioms YMGap.Continuum.SpectralLocalizationCrux.trivialLocalization
#print axioms YMGap.Continuum.SpectralLocalizationCrux.demo_localization
