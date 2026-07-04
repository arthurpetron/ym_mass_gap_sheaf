/-
Milestone 11.17 (Track 11.17-localfields): the typed **local-operator content**
of the 4D Yang–Mills Schwinger functions, in two layers over ONE file:

  * a finite inductive **curvature-word grammar** (`CovWord`/`GaugeInv`) with
    total, computable physical charges (`numF`, `numD`, `massDim`, `idxCount`,
    `isScalar`, `fieldDegree`) and named canonical operators whose charges are
    PROVED (`ymDensity = tr F²` has `massDim 4`, `fieldDegree 2`, is a Lorentz
    scalar; the stress component `tr(F_{μα}F_{να})` is a rank-2 dim-4 tensor);
  * four **local-operator interfaces** pinned to a `ProbFunctional`
    (`LocalCurvatureFields`, `StressTensor`, `OPE`,
    `AsymptoticFreedomShortDistance`), each carrying real typed content, each
    proved NON-VACUOUS by a concrete witness (trivial one-point / SU(2)
    canonical), and two of them *discharging* the bare existence Props of the
    continuum-existence layer (`GaugeGeneratedContent`,
    `UVAsymptoticFreedomContent`);
  * a **capstone bundle** `LocalOperatorContent` gluing the four interfaces to
    ONE algebra/functional with the OPE running coupling PINNED to the AF rate.
    It is the capstone existence hypothesis; a term for it over the *actual*
    Wilson–Schwinger functional of `μ_∞` is the open Clay content — we
    deliberately provide NO such term here.  (Its individual fields are
    toy-satisfiable, as the witnesses above show; the open content is their
    SIMULTANEOUS realization on the real gauge-invariant functional.)

Identifications (docstrings only): a Wilson loop is a holonomy `tr P exp(∮A)`
whose small-loop expansion is `1 + area·tr F_{μν}² + …`, so the `GaugeInv`
grammar names the local-operator content that expansion generates; the
`AFRateModulus` margin `1 − w_k` is the running-coupling trajectory whose
one-loop law `invRunningCoupling`/`betaZero` supplies the AF sign.

Axiom gate (AGENTS.md Rule 1): structural definitions, `rfl`/`decide`/`omega`,
and reuse of proved `Q'` order lemmas.  No `Classical.*`, no `sorry`, no custom
axioms; Type-level witnesses (Rule 8).
-/

import YMGap.Continuum.FourDExistence
import YMGap.Continuum.AFRateCalibration
import YMGap.Continuum.SpectralGap

namespace YMGap.Continuum.LocalCurvatureFields

open YMGap.Constructive
open YMGap.RepTheory
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.ObservableMeasure
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.AFRateCalibration

/-! ## Part A — the finite curvature-word grammar -/

/-- The four Euclidean directions of ℝ⁴ (O(4) acts by permuting/reflecting). -/
inductive Dir | e0 | e1 | e2 | e3
  deriving DecidableEq

/-- **Covariant curvature words** (adjoint-valued, color-index-carrying).
`F μ ν` is the field strength `F_{μν}` (antisymmetric, mass dimension 2);
`covD μ w` the gauge-covariant derivative `D_μ w` (raises dimension by 1);
`mul w₁ w₂` the color(matrix) product.  NOT gauge-invariant on its own. -/
inductive CovWord
  | F    : Dir → Dir → CovWord
  | covD : Dir → CovWord → CovWord
  | mul  : CovWord → CovWord → CovWord
  deriving DecidableEq

/-- **Gauge-invariant curvature polynomials.**  The color trace `tr(w)` of a
covariant word is gauge-invariant; `one`, `add`, `mul`, `smul` close it into a
rational polynomial algebra of local observables. -/
inductive GaugeInv
  | one  : GaugeInv
  | tr   : CovWord → GaugeInv
  | add  : GaugeInv → GaugeInv → GaugeInv
  | mul  : GaugeInv → GaugeInv → GaugeInv
  | smul : Q' → GaugeInv → GaugeInv

/-! ### Faithful charge functions (total, computable) -/

/-- Number of `F` factors in a covariant word (the "field degree"). -/
def CovWord.numF : CovWord → Nat
  | .F _ _    => 1
  | .covD _ w => w.numF
  | .mul a b  => a.numF + b.numF

/-- Number of covariant derivatives in a covariant word. -/
def CovWord.numD : CovWord → Nat
  | .F _ _    => 0
  | .covD _ w => 1 + w.numD
  | .mul a b  => a.numD + b.numD

/-- Mass dimension of a covariant word: `[F] = 2`, `[D] = 1`. -/
def CovWord.massDim (w : CovWord) : Nat := 2 * w.numF + w.numD

/-- How many times direction `d` occurs as a Lorentz index in a covariant word
(the two indices of each `F`, plus each derivative index). -/
def CovWord.idxCount (d : Dir) : CovWord → Nat
  | .F μ ν    => (if μ = d then 1 else 0) + (if ν = d then 1 else 0)
  | .covD μ w => (if μ = d then 1 else 0) + CovWord.idxCount d w
  | .mul a b  => CovWord.idxCount d a + CovWord.idxCount d b

/-- A covariant word is a **Lorentz scalar** iff every direction occurs an even
number of times (all indices contracted in pairs). -/
def CovWord.isScalar (w : CovWord) : Prop := ∀ d : Dir, CovWord.idxCount d w % 2 = 0

/-- Field degree (count of `F`) of a gauge invariant. -/
def GaugeInv.fieldDegree : GaugeInv → Nat
  | .one      => 0
  | .tr w     => w.numF
  | .add a b  => max a.fieldDegree b.fieldDegree
  | .mul a b  => a.fieldDegree + b.fieldDegree
  | .smul _ a => a.fieldDegree

/-- Mass dimension of a gauge invariant. -/
def GaugeInv.massDim : GaugeInv → Nat
  | .one      => 0
  | .tr w     => w.massDim
  | .add a b  => max a.massDim b.massDim
  | .mul a b  => a.massDim + b.massDim
  | .smul _ a => a.massDim

/-- Any self-product `mul w w` is a Lorentz scalar (each index count doubles). -/
theorem CovWord.mul_self_isScalar (w : CovWord) : (CovWord.mul w w).isScalar := by
  intro d
  show (CovWord.idxCount d w + CovWord.idxCount d w) % 2 = 0
  omega

/-! ### Named canonical operators (charges PROVED) -/

/-- The **Yang–Mills Lagrangian density** `tr(F_{μν} F_{μν})`: the dimension-4,
degree-2 marginal gauge invariant whose O(4)-symmetrized sum is the YM action. -/
def ymDensity (μ ν : Dir) : GaugeInv :=
  .tr (.mul (.F μ ν) (.F μ ν))

/-- `ymDensity` is a marginal (mass-dimension-4) operator. -/
theorem ymDensity_massDim (μ ν : Dir) : (ymDensity μ ν).massDim = 4 := rfl

/-- `ymDensity` is quadratic in the field strength. -/
theorem ymDensity_fieldDegree (μ ν : Dir) : (ymDensity μ ν).fieldDegree = 2 := rfl

/-- `tr(F_{μν}F_{μν})` is a Lorentz scalar. -/
theorem ymDensity_isScalar (μ ν : Dir) :
    (CovWord.mul (.F μ ν) (.F μ ν)).isScalar :=
  CovWord.mul_self_isScalar (.F μ ν)

/-- The (un-summed) **stress-tensor component** `tr(F_{μα} F_{να})`: dimension-4,
degree-2, a rank-2 Lorentz tensor (free indices μ, ν), not a scalar. -/
def stressComp (μ ν α : Dir) : GaugeInv :=
  .tr (.mul (.F μ α) (.F ν α))

theorem stressComp_massDim (μ ν α : Dir) : (stressComp μ ν α).massDim = 4 := rfl
theorem stressComp_fieldDegree (μ ν α : Dir) : (stressComp μ ν α).fieldDegree = 2 := rfl

/-- The **covariant divergence word** entering the Ward/conservation identity
`∂^μ T_{μν} = 0` (a 2-of-4 representative of the physical divergence sum). -/
def stressDiv (ν α : Dir) : GaugeInv :=
  .add (.tr (.covD .e0 (.mul (.F .e0 α) (.F ν α))))
       (.tr (.covD .e1 (.mul (.F .e1 α) (.F ν α))))

/-! ## Part B — the four local-operator interfaces -/

/-! ### Interface 1 — `LocalCurvatureFields` (curvature ↔ observable map)

The Schwinger functional `E` is generated by gauge-invariant CURVATURE
polynomials: `realize : GaugeInv → A.carrier` is a homomorphism of the
polynomial algebra, landing in the gauge-invariant subalgebra `im P` of an
idempotent gauge projection `P` through which `E` factors. -/
structure LocalCurvatureFields {M : Nat → Type} (μ_inf : ContinuumMeasure M) : Type 1 where
  A     : ObsAlg
  E     : ProbFunctional A
  add   : A.carrier → A.carrier → A.carrier
  smul  : Q' → A.carrier → A.carrier
  zero  : A.carrier
  /-- The operator correspondence `⟦·⟧ : GaugeInv → A`. -/
  realize : GaugeInv → A.carrier
  realize_one  : realize .one = A.one
  realize_mul  : ∀ x y, realize (.mul x y) = A.mul (realize x) (realize y)
  realize_add  : ∀ x y, realize (.add x y) = add (realize x) (realize y)
  realize_smul : ∀ q x, realize (.smul q x) = smul q (realize x)
  /-- Idempotent gauge-averaging projection. -/
  P       : ObsHom A A
  P_idem  : ∀ a, P.map (P.map a) = P.map a
  /-- `E` factors through `P` (Schwinger functions live on `im P`). -/
  E_factors : ∀ a, E.E (P.map a) = E.E a
  /-- Every realized curvature invariant is gauge-invariant (`P`-fixed). -/
  realize_gauge_inv : ∀ x, P.map (realize x) = realize x

/-- **Non-vacuous:** the trivial one-point realization. -/
def localCurvatureFields_triv {M : Nat → Type} (μ_inf : ContinuumMeasure M) :
    LocalCurvatureFields μ_inf where
  A := trivAlg
  E := trivFunc
  add := fun _ _ => PUnit.unit
  smul := fun _ _ => PUnit.unit
  zero := PUnit.unit
  realize := fun _ => PUnit.unit
  realize_one := rfl
  realize_mul := fun _ _ => rfl
  realize_add := fun _ _ => rfl
  realize_smul := fun _ _ => rfl
  P := ObsHom.idHom _
  P_idem := fun _ => rfl
  E_factors := fun _ => rfl
  realize_gauge_inv := fun _ => rfl

/-- **Discharge:** a `LocalCurvatureFields` supplies the bare
`GaugeGeneratedContent` (hence `IsGaugeGenerated`) — replacing the structureless
`gauge_content` carrier by typed curvature content. -/
theorem gaugeGenerated_of_localCurvatureFields
    {M : Nat → Type} {μ_inf : ContinuumMeasure M}
    (L : LocalCurvatureFields μ_inf) :
    FourDExistence.GaugeGeneratedContent μ_inf :=
  ⟨L.A, L.E, L.P, L.P_idem, L.E_factors⟩

/-! ### Interface 2 — `StressTensor` (dimension-4 conserved local operator) -/
structure StressTensor {M : Nat → Type} {μ_inf : ContinuumMeasure M}
    (L : LocalCurvatureFields μ_inf) : Type where
  /-- The component operators `T_{μν}` (a rank-2 Lorentz tensor of dimension 4). -/
  T : Dir → Dir → GaugeInv
  dim4 : ∀ μ ν, (T μ ν).massDim = 4
  deg2 : ∀ μ ν, (T μ ν).fieldDegree = 2
  /-- Symmetry `⟨T_{μν}⟩ = ⟨T_{νμ}⟩`. -/
  symmetric : ∀ μ ν, L.E.E (L.realize (T μ ν)) = L.E.E (L.realize (T ν μ))
  /-- The conserved-current word `∂^μ T_{μν}`. -/
  div : Dir → GaugeInv
  /-- **Ward identity / conservation** `⟨∂^μ T_{μν}⟩ = ⟨0⟩`. -/
  conserved : ∀ ν, L.E.E (L.realize (div ν)) = L.E.E L.zero

/-- **Non-vacuous:** the canonical stress component `tr(F_{μα}F_{να})` over the
trivial realization. -/
def stressTensor_triv {M : Nat → Type} (μ_inf : ContinuumMeasure M) :
    StressTensor (localCurvatureFields_triv μ_inf) where
  T := fun μ ν => stressComp μ ν Dir.e0
  dim4 := fun _ _ => rfl
  deg2 := fun _ _ => rfl
  symmetric := fun _ _ => rfl
  div := fun ν => stressDiv ν Dir.e0
  conserved := fun _ => rfl

/-! ### Interface 3 — `OPE` (operator product expansion with AF remainder)

`O_a(x) O_b(0) = Σ_c C_{ab}^c(x) O_c(0) + remainder`, with the remainder
controlled at short distance by the AF running coupling: the remainder modulus
is dominated by the two-loop margin `1 − w_r` (`AFRateModulus`). -/
structure OPE {M : Nat → Type} {μ_inf : ContinuumMeasure M}
    (L : LocalCurvatureFields μ_inf) : Type where
  /-- The local-operator basis `O_c`. -/
  ops : Nat → GaugeInv
  /-- Wilson coefficients `C_{ab}^c(r)` (indices `a b c`, separation `r`). -/
  coeff : Nat → Nat → Nat → Nat → Q'
  /-- The **AF anomalous dimensions** `γ_c` (short-distance exponents). -/
  anomDim : Nat → Q'
  /-- The two-loop AF running that governs the coefficient decay. -/
  running : AFRateModulus
  /-- Explicit OPE **remainder modulus** `ε(N,r)` (truncate at `N`, separation `r`). -/
  remainderModulus : Nat → Nat → Q'
  remainderModulus_pos : ∀ N r, (0 : Q') ≤ remainderModulus N r
  /-- **AF short-distance control:** the remainder is dominated by the AF margin
  `1 − w_r`, i.e. it vanishes at the two-loop rate as `r → 0`. -/
  remainder_af : ∀ N r, remainderModulus N r ≤ (1 : Q') - running.w r

/-- **Non-vacuous:** the constant/zero OPE with the canonical AF running. -/
def ope_triv {M : Nat → Type} (μ_inf : ContinuumMeasure M) :
    OPE (localCurvatureFields_triv μ_inf) where
  ops := fun _ => ymDensity Dir.e0 Dir.e1
  coeff := fun _ _ _ _ => 0
  anomDim := fun _ => 0
  running := afRateModulus_canonical
  remainderModulus := fun _ _ => 0
  remainderModulus_pos := fun _ _ => Q'.le_refl' 0
  remainder_af := fun _ r =>
    Q'.sub_nonneg_of_le (Q'.le_of_lt (afRateModulus_canonical.w_lt_one r))

/-! ### Interface 4 — `AsymptoticFreedomShortDistance` (refines UV freedom)

Bundles the two-loop AF margin rate (`AFRateModulus` ≈ running coupling) with the
concrete one-loop law `invRunningCoupling`/`betaZero` and the short-distance
freedom `w_k < 1`.  Ties `AFRateCalibration` (rate side) to `FourDExistence`
(coefficient/sign side). -/
structure AsymptoticFreedomShortDistance {M : Nat → Type}
    (μ_inf : ContinuumMeasure M) : Type where
  /-- The two-loop AF margin rate (the running-coupling trajectory). -/
  rate : AFRateModulus
  /-- Inverse-coupling initial value. -/
  u0 : Q'
  /-- Adjoint Casimir. -/
  c2adj : Q'
  hvee : Casimir.hveeFloor ≤ c2adj
  /-- Correct one-loop AF sign `β₀ > 0`. -/
  betaPos : (0 : Q') < betaZero c2adj
  /-- Inverse coupling strictly increases (⇔ `g²` decays in the UV). -/
  runningMono : ∀ k, invRunningCoupling u0 c2adj k < invRunningCoupling u0 c2adj (k + 1)
  /-- Short-distance freedom: the margin stays in the weak-coupling window. -/
  freedom : ∀ k, rate.w k < 1

/-- **Non-vacuous** at SU(2) with NO open input: canonical AF rate + the
`u₀ = 0`, `c2adj = hveeFloor` one-loop data. -/
def afShortDistance_su2 {M : Nat → Type} (μ_inf : ContinuumMeasure M) :
    AsymptoticFreedomShortDistance μ_inf where
  rate := afRateModulus_canonical
  u0 := 0
  c2adj := Casimir.hveeFloor
  hvee := Q'.le_refl' _
  betaPos := betaZero_pos (Q'.le_refl' _)
  runningMono := fun k => invRunningCoupling_strictMono (betaZero_pos (Q'.le_refl' _)) k
  freedom := fun k => afRateModulus_canonical.w_lt_one k

/-- **Discharge:** an `AsymptoticFreedomShortDistance` supplies the bare
`UVAsymptoticFreedomContent` (hence `IsUVAsymptoticallyFree`). -/
theorem uvAF_of_afShortDistance
    {M : Nat → Type} {μ_inf : ContinuumMeasure M}
    (S : AsymptoticFreedomShortDistance μ_inf) :
    FourDExistence.UVAsymptoticFreedomContent μ_inf :=
  ⟨S.u0, S.c2adj, S.hvee, S.betaPos, S.runningMono⟩

/-! ## Part C — the capstone existence hypothesis (NOT inhabited here)

`LocalOperatorContent` glues the four interfaces to ONE algebra/functional
(`curvature`), with the stress tensor and OPE built over that same
correspondence, and the OPE running coupling PINNED to the AF short-distance
rate.  A term over the *actual* Wilson–Schwinger functional of `μ_∞` is the open
Clay content — we deliberately provide NO such term. -/
structure LocalOperatorContent {M : Nat → Type} (μ_inf : ContinuumMeasure M) : Type 1 where
  curvature : LocalCurvatureFields μ_inf
  stress    : StressTensor curvature
  ope       : OPE curvature
  af        : AsymptoticFreedomShortDistance μ_inf
  /-- **PIN:** the OPE's running coupling IS the AF short-distance rate. -/
  ratePinned : ope.running = af.rate

/-- The capstone discharges BOTH bare existence carriers at once (the intended
`FourDExistence` refinement target: `gauge_content` ← curvature content,
`uv_asymptotic_freedom` ← AF short-distance content). -/
theorem content_discharges
    {M : Nat → Type} {μ_inf : ContinuumMeasure M}
    (C : LocalOperatorContent μ_inf) :
    FourDExistence.GaugeGeneratedContent μ_inf ∧
    FourDExistence.UVAsymptoticFreedomContent μ_inf :=
  ⟨gaugeGenerated_of_localCurvatureFields C.curvature,
   uvAF_of_afShortDistance C.af⟩

end YMGap.Continuum.LocalCurvatureFields

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/
#print axioms YMGap.Continuum.LocalCurvatureFields.ymDensity_massDim
#print axioms YMGap.Continuum.LocalCurvatureFields.ymDensity_isScalar
#print axioms YMGap.Continuum.LocalCurvatureFields.stressComp_massDim
#print axioms YMGap.Continuum.LocalCurvatureFields.gaugeGenerated_of_localCurvatureFields
#print axioms YMGap.Continuum.LocalCurvatureFields.uvAF_of_afShortDistance
#print axioms YMGap.Continuum.LocalCurvatureFields.afShortDistance_su2
#print axioms YMGap.Continuum.LocalCurvatureFields.content_discharges
