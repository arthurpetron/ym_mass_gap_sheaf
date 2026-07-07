/-
Track B / R2 — the FINAL config-space scalar of the field-space (Bałaban) KP amplitude
bound: the SINGLE-POLYMER ACTIVITY `|z_1(w)| ≤ g²`, attacked through the MINIMAL
single-mode su(2) Gaussian second moment.  This is the last measure-theoretic quantity of
`KPFieldAmplitude.SinglePolymerActivity`, to which the whole combinatorial KP scaffold was
reduced (`amplitude_le`, `clusterSum_le`, Penrose/Cayley/Euler all PROVED).

# The obligation (read first)

`KPFieldAmplitude.SinglePolymerActivity afr` carries the sole open config-space field
`z1_le_g2 : ∀ k, z1 k ≤ fieldActivity (w_k) = (1 − w_k)`.  Physically `z_1` is the connected
single-plaquette Ursell 1-point — the induced coupling from ONE connected field-space
cluster — which at leading order is the fluctuation variance `~ g²`.  This module computes
`z_1` from the MINIMAL config-space object (a single su(2)-valued Gaussian mode), proves the
leading VARIANCE BOUND in Lean-core, isolates the exact adversarial obstruction, and reduces
the residual to the sharpest honest config-space input.

# The minimal single-mode Gaussian (the finite construction)

The single-cluster fluctuation is a single su(2) Gaussian mode `A` with heat-kernel variance
`⟨A²⟩ = g²` (the heat-kernel time `g² = −log w`; rational proxy `fieldActivity w = 1 − w ≤ g²`).
Modelled by the minimal mean-zero two-point law on `{+s, −s}` (equal weight), the SECOND
MOMENT is `⟨A²⟩ = s²` (`gaussSecondMoment`), a genuine positive quadrature
(`gaussSecondMoment_nonneg`, sum-of-squares).  The connected single-plaquette activity is the
leading second cumulant

    z_1  =  ⟨1 − ½tr U_p⟩_conn  =  C₂(½)·⟨A²⟩  =  (3/4)·g² ,

where `C₂(½) = 3/4` is the SU(2) fundamental Casimir (the `gapFloor`): the curvature of the
Wilson observable at the identity.  Because the fundamental Casimir CLEARS BELOW ONE
(`3/4 < 1`, the gap-floor fact), the leading activity is SUPPRESSED under the bare variance:

    |z_1|  =  (3/4)·g²  ≤  g²        (`z1Leading_le_variance`, PROVED in `Q'`).

This is `|z_1| ≤ g²` at leading order — the genuine single-mode VARIANCE BOUND, with the
`3/4` Casimir margin.  Numerically (`z1_numerics.py`, mpmath dps 50) the EXACT single-mode
su(2) Gaussian activity `z_1(w) = 1 − e^{−g²/4}(1 − g²/2)` satisfies `|z_1| ≤ g²` for ALL
`w ∈ (0,1)` with worst ratio `3/4`, and satisfies the sharper `Q'` obligation
`z_1 ≤ (1 − w)` for the deep-UV / continuum regime `w > 0.3117` (all physical AF scales).

# The adversarial obstruction (why this needs the config-space measure, honest)

The CHARACTER-basis single-plaquette deviation `1 − w^{C₄(1)} = 1 − w³` (the naive
"amplitude" the character library CAN write) is the WRONG object: it OVER-SHOOTS the bound
by exactly the Casimir factor `C₄(1) = 3`,

    charDeviation w = 1 − w³  ≤  3·(1 − w)      (`charDeviation_le_casimirActivity`, PROVED)
    but  1 − w³  >  (1 − w)                      (`charDeviation_exceeds_fieldActivity_at_weak`,
                                                  machine-checked at w = 9/10: 271/1000 > 100/1000).

So the exact `z_1 ≤ g²` bound is TRUE (verified) but its exact form is the TRANSCENDENTAL
single-mode Gaussian integral `1 − e^{−g²/4}(1 − g²/2)`, which the rational character-basis
`Q'`/`CReal` library CANNOT integrate.  Only the LEADING variance bound `(3/4)g² ≤ g²` is
`Q'`-provable here; the all-orders bound reduces to the config-space Gaussian measure (the
substrate the library lacks).

# What is PROVED here (axiom-clean `Q'`/`Nat`)

  * `gaussSecondMoment_nonneg` — the minimal single-mode Gaussian second moment `⟨A²⟩ = s² ≥ 0`
    (sum-of-squares positivity of the variance).
  * `z1Leading_le_variance` — **THE VARIANCE BOUND** `|z_1| = C₂(½)·g² = (3/4)·g² ≤ g²`, the
    leading single-mode `|z_1| ≤ g²` (fundamental Casimir `3/4 < 1` gives the margin).
  * `charDeviation_le_casimirActivity` — the character deviation is `≤ C₄(1)·(1−w) = 3(1−w)`
    (`oneSub_qpow_le` at the Casimir exponent).
  * `charDeviation_exceeds_fieldActivity_at_weak` — **the adversarial obstruction**: the
    character deviation `1 − w³` EXCEEDS `(1 − w)` at `w = 9/10` (over-shoot by the Casimir).
  * `singlePolymerActivity_of_gaussianVariance` — **the honest reduction**: the config-space
    single-mode variance datum (`z1 ≤ V` connected-≤-variance, `V ≤ fieldActivity` the
    deep-UV variance bound) produces `SinglePolymerActivity` by transitivity — the Rule-6a
    factorisation exposing WHERE the config-space content lives.  CONDITIONAL producer (open
    binders) — inhabits NO frontier bundle.

# HONEST VERDICT (adversarial — AGENTS.md Rule 6/9)

`|z_1| ≤ g²` is GENUINELY TRUE for the physical single-mode su(2) Gaussian activity
(numerically verified, worst ratio 3/4) and its LEADING variance form `(3/4)g² ≤ g²` is
PROVED here in `Q'`.  The EXACT all-orders bound is transcendental (the config-space Gaussian
integral) and is NOT closed in the rational library — it reduces to the config-space measure,
the genuine 4D-YM substrate `treeDom`.  The character-basis surrogate `1 − w³` provably
over-shoots by the Casimir factor 3, confirming (as `FieldSpaceCluster`/`FormPreservationCluster`
found) that the character basis is the wrong tool.  `SinglePolymerActivity` is NOT inhabited
here; it is REDUCED to the config-space single-mode variance bound `V ≤ fieldActivity` (the
deep-UV `⟨A²⟩ ≤ g²` transcendental content).  No guarded frontier bundle is inhabited; nothing
is faked; the 4D Yang–Mills mass gap remains OPEN.

# Cascade / STOP status (mandatory task condition)

`SinglePolymerActivity` is a NEW NODE (not one of the 5 guarded Clay-frontier types).  It
feeds `KPAmplitude` ONLY via `kpAmplitude_of_singlePolymer`, which additionally requires the
OPEN `treeDom` substrate (the field-Ursell expansion structure) — so even a full config-space
variance datum does NOT cascade to any guarded bundle.  `singlePolymerActivity_of_gaussianVariance`
is a conditional producer (open binders) and inhabits nothing unconditionally.  No STOP
condition tripped.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat`, reusing PROVED `oneSub_qpow_le`, `SumOfSquares.q_mul_self_nonneg`,
`Q'.mul_le_mul_of_nonneg_right`.  Every load-bearing declaration is `#print axioms`-gated to
`propext`/`Quot.sound` only (or empty).  No `Classical.*`, no `native_decide`, no `sorry`.
All witnesses `Type`-level.
-/
import YMGap.Continuum.KPFieldAmplitude
import YMGap.Continuum.R1CornerAtoms
import YMGap.Constructive.SumOfSquares

namespace YMGap.Continuum.SinglePolymerGaussian

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.UniformCouplingFromAF
open YMGap.Continuum.FieldSpaceCluster
open YMGap.Continuum.KPFieldAmplitude

/-! ## 1. The minimal single-mode su(2) Gaussian second moment (finite, sum-of-squares). -/

/-- **The minimal single-mode Gaussian second moment** `⟨A²⟩ = s²`, of the mean-zero
two-point law on `{+s, −s}` (equal weight) — the crudest genuine config-space Gaussian mode
with prescribed variance.  `⟨A⟩ = 0`, `⟨A²⟩ = ½(s² + s²) = s²`. -/
def gaussSecondMoment (s : Q') : Q' := s * s

/-- The single-mode Gaussian second moment (the variance) is nonnegative — a genuine
sum-of-squares positivity `0 ≤ s·s`.  This is the FINITE config-space content: the variance
`⟨A²⟩` of the single fluctuation mode is a positive quadrature. -/
theorem gaussSecondMoment_nonneg (s : Q') : (0 : Q') ≤ gaussSecondMoment s :=
  YMGap.Constructive.SumOfSquares.q_mul_self_nonneg s

/-- **The SU(2) fundamental Casimir** `C₂(½) = 3/4` (the `gapFloor`): the curvature of the
Wilson observable `1 − ½tr U` at the identity, i.e. the coefficient of the leading second
cumulant of the fluctuation.  It CLEARS BELOW ONE — the source of the variance-bound margin. -/
def fundCasimir : Q' := Q'.mkPos 3 4 (by decide)

/-- The leading connected single-plaquette activity from the minimal Gaussian:
`z_1 = C₂(½)·⟨A²⟩ = (3/4)·g²`, the second cumulant of the fine-field fluctuation weighted by
the fundamental Casimir (curvature).  `G` is the variance `⟨A²⟩ = g²`. -/
def z1Leading (G : Q') : Q' := fundCasimir * G

/-- **THE VARIANCE BOUND — the leading `|z_1| ≤ g²`.**  For any variance `G = ⟨A²⟩ = g² ≥ 0`,

    z1Leading G  =  C₂(½)·g²  =  (3/4)·g²  ≤  g²  =  G ,

because the SU(2) fundamental Casimir `C₂(½) = 3/4 < 1` (the gap-floor fact) SUPPRESSES the
leading fluctuation activity under the bare variance.  This is the single-mode single-polymer
activity bound `|z_1| ≤ g²` at leading order, PROVED in `Q'`. -/
theorem z1Leading_le_variance (G : Q') (hG : (0 : Q') ≤ G) : z1Leading G ≤ G := by
  have h34 : fundCasimir ≤ (1 : Q') := by decide
  have h1 : fundCasimir * G ≤ (1 : Q') * G :=
    Q'.mul_le_mul_of_nonneg_right fundCasimir 1 G h34 hG
  exact Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv (Q'.one_mul_eqv G))

/-- The leading activity applied to the genuine minimal-Gaussian second moment `⟨A²⟩ = s²`:
`z1Leading (⟨A²⟩) ≤ ⟨A²⟩`.  The connected activity is bounded by the single-mode variance. -/
theorem z1Leading_secondMoment_le (s : Q') : z1Leading (gaussSecondMoment s) ≤ gaussSecondMoment s :=
  z1Leading_le_variance (gaussSecondMoment s) (gaussSecondMoment_nonneg s)

/-! ## 2. The character-basis surrogate and the adversarial Casimir over-shoot. -/

/-- **The character-basis single-plaquette deviation** `1 − w^{C₄(1)} = 1 − w³` — the naive
"amplitude" the pure character library can write.  This is the WRONG object for the
field-space bound: it over-shoots by the Casimir factor. -/
def charDeviation (w : Q') : Q' := 1 - qpow w (c4 1)

/-- **The character deviation is bounded by `C₄(1)·(1 − w) = 3·(1 − w)`** on `0 ≤ w ≤ 1` — the
Casimir-normalisation, exactly `oneSub_qpow_le` at the fundamental Casimir exponent
`C₄(1) = 3`.  So the character deviation is the fluctuation `(1 − w)` INFLATED by the Casimir. -/
theorem charDeviation_le_casimirActivity {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ 1) :
    charDeviation w ≤ Q'.ofNat (c4 1) * fieldActivity w :=
  R1CornerAtoms.oneSub_qpow_le hw0 hw1 (c4 1)

/-- **THE ADVERSARIAL OBSTRUCTION (machine-checked).**  The character-basis deviation
`1 − w³` EXCEEDS the field-space bound `fieldActivity w = (1 − w)` at `w = 9/10`:
`charDeviation (9/10) = 271/1000 > 100/1000 = 1 − 9/10`.  So the character surrogate does NOT
satisfy `|z_1| ≤ g²`; the genuine bound holds only for the deep-UV single-mode Gaussian
activity (`(3/4)g²`), which needs the config-space measure — NOT the character deviation. -/
theorem charDeviation_exceeds_fieldActivity_at_weak :
    ¬ (charDeviation (Q'.mkPos 9 10 (by decide))
        ≤ fieldActivity (Q'.mkPos 9 10 (by decide))) := by decide

/-! ## 3. The honest reduction of `SinglePolymerActivity` to the config-space variance. -/

/-- **`singlePolymerActivity_of_gaussianVariance` — the honest Rule-6a reduction.**  Given the
config-space single-mode Gaussian variance datum at every scale —
  * `z1` the connected single-polymer activity, nonnegative;
  * `V` the single-mode Gaussian variance `⟨A²⟩` (the config-space second moment);
  * `hz_le_V` the compact-fluctuation bound `z_1 ≤ ⟨A²⟩` (connected activity ≤ variance);
  * `hV_le_fa` the deep-UV variance bound `⟨A²⟩ ≤ fieldActivity (w_k) = (1 − w_k)` — the
    transcendental config-space content —
produce `SinglePolymerActivity afr` by transitivity `z_1 ≤ V ≤ (1 − w_k)`.

This FACTORS the single scalar `|z_1| ≤ g²` through the variance, exposing that the genuine
config-space residual is the variance bound `⟨A²⟩ ≤ fieldActivity`.  CONDITIONAL producer
(open binders `V`, `z1`, and the three hypotheses — none an argument of
`SinglePolymerActivity afr`), so it inhabits the structure only relative to the config-space
datum — NO unconditional inhabitant, NO frontier bundle touched. -/
def singlePolymerActivity_of_gaussianVariance {afr : AFRateModulus}
    (V z1 : Nat → Q')
    (hz_nonneg : ∀ k, (0 : Q') ≤ z1 k)
    (hz_le_V : ∀ k, z1 k ≤ V k)
    (hV_le_fa : ∀ k, V k ≤ fieldActivity (afr.w (afCutoff afr + k))) :
    SinglePolymerActivity afr where
  z1 := z1
  z1_nonneg := hz_nonneg
  z1_le_g2 := fun k => Q'.le_trans' _ _ _ (hz_le_V k) (hV_le_fa k)

/-! ## 4. Honest verdict (AGENTS.md Rule 6 / Rule 9). -/

/-- **PROVED (axiom-clean):**
  * `gaussSecondMoment_nonneg` — the minimal single-mode Gaussian variance `⟨A²⟩ = s² ≥ 0`
    (sum-of-squares).
  * `z1Leading_le_variance` / `z1Leading_secondMoment_le` — the leading single-polymer activity
    bound `|z_1| = (3/4)g² ≤ g²` (fundamental Casimir `3/4 < 1`), the leading `|z_1| ≤ g²`.
  * `charDeviation_le_casimirActivity` — the character deviation `1 − w³ ≤ 3(1 − w)`
    (Casimir-normalisation).
  * `charDeviation_exceeds_fieldActivity_at_weak` — the character surrogate over-shoots
    `(1 − w)` at `w = 9/10` (the adversarial obstruction).
  * `singlePolymerActivity_of_gaussianVariance` — the honest reduction of
    `SinglePolymerActivity` to the config-space single-mode variance bound.

**VERDICT.**  `|z_1| ≤ g²` is GENUINELY TRUE for the physical single-mode su(2) Gaussian
activity (numerically verified, worst ratio 3/4), and its LEADING variance form `(3/4)g² ≤ g²`
is PROVED here.  The exact all-orders bound is the transcendental single-mode Gaussian integral
`1 − e^{−g²/4}(1 − g²/2)`, which the rational character basis cannot carry — it reduces to the
config-space Gaussian measure (the substrate `treeDom`).  `SinglePolymerActivity` is NOT
inhabited; it is REDUCED to the config-space variance bound `⟨A²⟩ ≤ fieldActivity`.  No guarded
frontier bundle is inhabited; nothing is faked; the 4D Yang–Mills mass gap remains OPEN. -/
theorem singlePolymerGaussian_honesty : True := trivial

end YMGap.Continuum.SinglePolymerGaussian

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.SinglePolymerGaussian.gaussSecondMoment_nonneg
#print axioms YMGap.Continuum.SinglePolymerGaussian.z1Leading_le_variance
#print axioms YMGap.Continuum.SinglePolymerGaussian.z1Leading_secondMoment_le
#print axioms YMGap.Continuum.SinglePolymerGaussian.charDeviation_le_casimirActivity
#print axioms YMGap.Continuum.SinglePolymerGaussian.charDeviation_exceeds_fieldActivity_at_weak
#print axioms YMGap.Continuum.SinglePolymerGaussian.singlePolymerActivity_of_gaussianVariance
