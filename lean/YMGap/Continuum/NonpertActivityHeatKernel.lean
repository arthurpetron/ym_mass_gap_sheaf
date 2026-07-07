/-
Track B / R1 — the NON-PERTURBATIVE (entire heat-kernel) test of the single-cluster
activity `z_1`, against the library's genuine Wilson functional
`coeffW(t,s) = dim(s)·e^{−t·C₂(s)}` (`WilsonFunctional.wilsonCharExp`).

# The obligation and the decisive question

`KPFieldAmplitude.SinglePolymerActivity` carries the sole open config-space scalar
`z1_le_g2 : z1 k ≤ fieldActivity (w_k) = (1 − w_k)`.  The perturbative (Isserlis)
series that would produce `z_1` is factorial / radius-0 (Dyson), so it needs a
Borel/non-perturbative prescription.  THIS file tests the natural non-perturbative
candidate: the library's single-plaquette Wilson weight

    coeffW(t,s) = dim(s)·e^{−t·C₂(s)}                      (`wilsonCharExp`)

is **ENTIRE in `t`** (`e^{−t·C₂}` is entire) — it is ALREADY the non-perturbatively
resummed single-plaquette (no factorial, no radius-0 problem).  The question the task
poses: does the REAL interacting single-cluster activity `z_1` connect to this entire
object, so that `z_1 ≤ g²` is CONSTRUCTED at fixed spacing (no Borel), closing R1?

# The genuine object: the fundamental heat-kernel factor `e^{−(3/4)t}`

For SU(2), `C₂(½) = 3/4`, `dim(½) = 2`, so the library's `coeffW` at the fundamental
rep is `wilsonCharExp t 1 = 2·e^{−(3/4)t}`, and the **average plaquette**
`⟨½χ_{1/2}⟩_t = e^{−(3/4)t}` is `avgPlaq` below — the actual, entire, non-perturbative
heat-kernel building block.  `t = g²`.  `w = e^{−t}`, `fieldActivity = 1 − w`.

# The DECISIVE dichotomy (this is the finding — verified `nonpert_activity.md`, mpmath dps 50)

The entire heat kernel supplies TWO distinct scalars, on OPPOSITE sides of the bound:

  1. the character single-plaquette **MOMENT** activity `1 − e^{−(3/4)t} = (3/4)g² + …`
     — this CLEARS `z_1 ≤ g²` with the fundamental-Casimir margin `3/4`
     (`charMoment_le_g2`).  BUT it is the one-point correlation function, NOT the
     connected Ursell activity: `⟨1−½χ_p⟩ = z_1 + Σ_{n≥2}(alternating clusters)`, equal
     to the connected `z_1` only at leading order; and it is TRANSCENDENTAL, so it is not
     the `Q'`-valued `z1` the structure demands.  It is a SURROGATE (Rule 9(6)).

  2. the strong-coupling **POLYMER** activity `a_{1/2} = e^{−(3/4)t}` — this IS a genuine
     polymer activity in the character basis, but at WEAK coupling it does NOT clear the
     bound: `strongPolymer_not_le_g2` proves `e^{−(3/4)t} ≥ 1 − (3/4)t ≫ g²` for
     `t = 1/10` (the activity is `≥ 37/40`, over 9× the required `g² = 1/10`).  It is
     small only at STRONG coupling `t ≳ 0.63`, exactly where KP does not need it.

Neither is the WEAK-coupling connected field-space activity that KP requires (that object
is the transcendental Gaussian fluctuation `~ (3/4)g²`, `ExactSinglePolymerActivity`,
proved `≤ g²` but NOT `≤ 1−w` for the real non-Gaussian su(2)/Wilson activity, and it
DIFFERS from the character moment at `O(g⁴)`).

# The Borel verdict (correct, and it matters)

At FIXED spacing every object here is ENTIRE in `t` (a finite combination of `e^{−t·C₂}`)
— there is NO factorial/Borel problem at fixed spacing (matches Osterwalder–Seiler /
convergent strong-coupling polymer expansion).  The Borel/Dyson factorial lives in the
WEAK-COUPLING PERTURBATIVE `g²`-expansion of these entire quantities (the `a→0` continuum),
NOT at fixed spacing.  So R1's obstruction is not "Borel at fixed spacing"; it is that the
entire heat-kernel (a strong-coupling object) does NOT deliver the weak-coupling connected
`z_1 ≤ 1−w` that `SinglePolymerActivity` demands.

# What is PROVED here (axiom-clean `Q'`/`CReal`)

  * `wilsonCharExp_fund` — the library `coeffW` at the fundamental IS `2·avgPlaq` (rfl):
    the object below is genuinely the library's entire Wilson functional.
  * `avgPlaq_geRat_zero`, `charMomentActivity_geRat_zero` — entire, well-defined,
    nonnegative (finite `CReal`; no Borel at fixed spacing).
  * `charMoment_le_g2` — the character MOMENT activity `1 − e^{−(3/4)t} ≤ g² = t`
    (Casimir margin `3/4`), via the transcendental `oneSub_le_expNeg`.
  * `avgPlaq_geRat_oneSub` — the alternating lower bound `e^{−(3/4)t} ≥ 1 − (3/4)t`.
  * `strongPolymer_not_le_g2` — **the refutation**: the strong-coupling polymer activity
    `e^{−(3/4)t}` does NOT satisfy `≤ g²` at weak coupling `t = 1/10`.

# HONEST VERDICT (adversarial — AGENTS.md Rule 6/9)

R1 does NOT close from the entire heat kernel.  `SinglePolymerActivity` is NOT inhabited
(the character moment is a transcendental surrogate agreeing with the connected `z_1` only
at leading order; the character polymer activity overshoots at weak coupling; the
`treeDom` field-Ursell substrate stays open).  Nothing is faked; no guarded frontier bundle
is inhabited; the 4D Yang–Mills mass gap remains OPEN.  The residual is sharpened: the
weak-coupling connected field-space activity `z_1 ≤ 1−w` for the real non-Gaussian su(2)
activity, and its `a→0` continuum (R2) — the Borel problem lives there, not at fixed spacing.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]`.  No `Classical.*`, no `sorryAx`, no `native_decide`.
-/
import YMGap.Continuum.WilsonFunctional
import YMGap.Continuum.FieldSpaceCluster

namespace YMGap.Continuum.NonpertActivityHeatKernel

open YMGap.Constructive
open YMGap.Continuum.WilsonFunctional
open YMGap.Continuum.FieldSpaceCluster

/-! ## 1. The entire heat-kernel fundamental factor `e^{−(3/4)t}` (the library's `coeffW`). -/

/-- **The average plaquette** `⟨½χ_{1/2}⟩_t = e^{−t·C₂(½)} = e^{−(3/4)t}` — the genuine,
ENTIRE, non-perturbatively-resummed single-plaquette factor of the library's Wilson
functional `coeffW`.  It is exactly the `expNeg` factor inside `wilsonCharExp t 1`. -/
def avgPlaq (t : Q') (ht : (0 : Q') ≤ t) : CReal :=
  ExpNeg.expNeg (t * casimirQ 1) (tcasimirQ_nonneg t ht 1)

/-- **Connection to the library's genuine Wilson functional.**  The heat-kernel character
expectation `coeffW(t, fund) = dim(½)·e^{−(3/4)t} = 2·avgPlaq` (definitional): `avgPlaq`
IS the entire building block of `WilsonFunctional.wilsonCharExp`, not a fresh model. -/
theorem wilsonCharExp_fund (t : Q') (ht : (0 : Q') ≤ t) :
    wilsonCharExp t ht 1 = CReal.mul (CReal.ofQ' (Q'.ofNat 2)) (avgPlaq t ht) := rfl

/-- The entire factor is well-defined and `≥ 0` (a finite `CReal`; no Borel at fixed
spacing). -/
theorem avgPlaq_geRat_zero (t : Q') (ht : (0 : Q') ≤ t) :
    ExpPos.geRat (avgPlaq t ht) 0 :=
  expNeg_geRat_zero _ _

/-! ## 2. The character single-plaquette MOMENT activity `1 − e^{−(3/4)t}`. -/

/-- **The character single-plaquette moment activity** `1 − ⟨½χ_{1/2}⟩_t = 1 − e^{−(3/4)t}`
— the deviation of the average plaquette from the identity, an entire object from the
library's `coeffW`. -/
def charMomentActivity (t : Q') (ht : (0 : Q') ≤ t) : CReal :=
  CReal.sub CReal.cone (avgPlaq t ht)

/-- The moment activity is `≥ 0` (from `e^{−(3/4)t} ≤ 1`). -/
theorem charMomentActivity_geRat_zero (t : Q') (ht : (0 : Q') ≤ t) :
    ExpPos.geRat (charMomentActivity t ht) 0 :=
  CReal.geRat_sub_cone_expNeg (tcasimirQ_nonneg t ht 1)

/-- **The character MOMENT activity clears `z_1 ≤ g²`** — `1 − e^{−(3/4)t} ≤ g² = t`, for
`t` in the weak-coupling regime `t·C₂(½) ≤ 1` (i.e. `t ≤ 4/3`, which contains all deep-UV
scales `t = g² → 0`).  The margin is the fundamental Casimir `C₂(½) = 3/4 < 1`:
`1 − e^{−(3/4)t} ≤ (3/4)t ≤ t`, via the transcendental convexity bound `oneSub_le_expNeg`.
This is the entire heat kernel's own witness that the LEADING-order activity clears the
bound — but on the WRONG object (the one-point moment, a surrogate; see verdict). -/
theorem charMoment_le_g2 (t : Q') (ht : (0 : Q') ≤ t)
    (h1 : t * casimirQ 1 ≤ (1 : Q')) :
    CReal.leRat (charMomentActivity t ht) t := by
  have hstep : CReal.leRat (charMomentActivity t ht) (t * casimirQ 1) :=
    CReal.oneSub_le_expNeg (tcasimirQ_nonneg t ht 1) h1
  have hle : t * casimirQ 1 ≤ t := by
    have hcas : t * casimirQ 1 ≤ t * (1 : Q') :=
      Q'.mul_le_mul_of_nonneg_left (casimirQ 1) 1 t (by decide) ht
    exact Q'.le_trans' _ _ _ hcas (Q'.le_of_eqv (Q'.mul_one_eqv t))
  exact CReal.leRat_mono hstep hle

/-! ## 3. The strong-coupling POLYMER activity `e^{−(3/4)t}` — the refutation. -/

/-- The rational `1/100` (a positive slack for the refutation). -/
def eps : Q' := Q'.mkPos 1 100 (by decide)

theorem eps_pos : (0 : Q') < eps := by decide

/-- The rational `1/10` — a concrete WEAK-coupling coupling `g² = 1/10`. -/
def oneTenth : Q' := Q'.mkPos 1 10 (by decide)

theorem oneTenth_nonneg : (0 : Q') ≤ oneTenth := by decide

theorem oneTenth_cas_le_one : oneTenth * casimirQ 1 ≤ (1 : Q') := by decide

/-- **The alternating-series lower bound** `e^{−(3/4)t} ≥ 1 − (3/4)t` on the entire
polymer activity, from `ExpNeg.oneSub_le_partialSum` (every partial sum `n ≥ 2` is
`≥ 1 − x`).  Requires `t·C₂(½) ≤ 1`. -/
theorem avgPlaq_geRat_oneSub (t : Q') (ht : (0 : Q') ≤ t)
    (h1 : t * casimirQ 1 ≤ (1 : Q')) :
    ExpPos.geRat (avgPlaq t ht) (1 - t * casimirQ 1) := by
  apply ExpPos.geRat_of_eventually
  refine ⟨2, fun n hn => ?_⟩
  exact ExpNeg.oneSub_le_partialSum (tcasimirQ_nonneg t ht 1) h1 n hn

/-- **THE REFUTATION.**  At weak coupling `g² = t = 1/10`, the strong-coupling POLYMER
activity `a_{1/2} = e^{−(3/4)t}` does NOT satisfy `z_1 ≤ g²`: its limit is
`≥ 1 − (3/4)(1/10) = 37/40`, over 9× the required bound `g² = 1/10`.  Formally
`¬ CReal.leRat (avgPlaq (1/10)) (1/10)`, derived from the alternating lower bound and the
`leRat` upper bound with slack `ε = 1/100`: they would force `37/40 ≤ 12/100`, false by
`decide`.  So the entire heat-kernel's own polymer activity overshoots exactly where KP
needs it (weak coupling). -/
theorem strongPolymer_not_le_g2 :
    ¬ CReal.leRat (avgPlaq oneTenth oneTenth_nonneg) oneTenth := by
  intro hle
  have hge : ExpPos.geRat (avgPlaq oneTenth oneTenth_nonneg) (1 - oneTenth * casimirQ 1) :=
    avgPlaq_geRat_oneSub oneTenth oneTenth_nonneg oneTenth_cas_le_one
  obtain ⟨N1, hN1⟩ := hle eps eps_pos
  obtain ⟨N2, hN2⟩ := hge eps eps_pos
  have hn1 : N1 ≤ max N1 N2 := Nat.le_max_left _ _
  have hn2 : N2 ≤ max N1 N2 := Nat.le_max_right _ _
  have h_up : (avgPlaq oneTenth oneTenth_nonneg).approx (max N1 N2) ≤ oneTenth + eps :=
    hN1 (max N1 N2) hn1
  have h_lo : (1 - oneTenth * casimirQ 1)
      ≤ (avgPlaq oneTenth oneTenth_nonneg).approx (max N1 N2) + eps :=
    hN2 (max N1 N2) hn2
  -- 37/40 ≤ approx n + eps ≤ (oneTenth + eps) + eps = 12/100
  have hchain : (1 - oneTenth * casimirQ 1) ≤ (oneTenth + eps) + eps :=
    Q'.le_trans' _ _ _ h_lo (Q'.add_le_add_right _ _ eps h_up)
  exact absurd hchain (by decide)

/-! ## 4. Honest verdict (AGENTS.md Rule 6 / Rule 9). -/

/-- **VERDICT.**  The library's single-plaquette Wilson functional `coeffW = dim·e^{−t·C₂}`
is genuinely ENTIRE in `t` (`avgPlaq`, `wilsonCharExp_fund`) — the non-perturbatively
resummed single-plaquette, with NO factorial/Borel problem AT FIXED SPACING.  But the
entire heat kernel does NOT close R1:

  * the character single-plaquette MOMENT activity `1 − e^{−(3/4)t}` clears `z_1 ≤ g²`
    (`charMoment_le_g2`, Casimir margin `3/4`) but is the one-point correlation function
    (a Rule 9(6) SURROGATE agreeing with the connected `z_1` only at leading order) and is
    transcendental (not the `Q'`-valued `z1` the structure needs);
  * the strong-coupling POLYMER activity `e^{−(3/4)t}` is a genuine polymer activity but
    OVERSHOOTS `g²` at weak coupling (`strongPolymer_not_le_g2`), where KP needs it.

Neither is the weak-coupling connected field-space activity `z_1 ≤ 1−w` that
`KPFieldAmplitude.SinglePolymerActivity` demands.  The Borel/Dyson factorial is a
WEAK-COUPLING PERTURBATIVE (`a→0`) artifact, not a fixed-spacing one.  `SinglePolymerActivity`
is NOT inhabited; the `treeDom` field-Ursell substrate stays open; nothing is faked; no
guarded frontier bundle is inhabited; the 4D Yang–Mills mass gap remains OPEN. -/
theorem nonpert_activity_honesty : True := trivial

end YMGap.Continuum.NonpertActivityHeatKernel

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.NonpertActivityHeatKernel.wilsonCharExp_fund
#print axioms YMGap.Continuum.NonpertActivityHeatKernel.avgPlaq_geRat_zero
#print axioms YMGap.Continuum.NonpertActivityHeatKernel.charMomentActivity_geRat_zero
#print axioms YMGap.Continuum.NonpertActivityHeatKernel.charMoment_le_g2
#print axioms YMGap.Continuum.NonpertActivityHeatKernel.avgPlaq_geRat_oneSub
#print axioms YMGap.Continuum.NonpertActivityHeatKernel.strongPolymer_not_le_g2
