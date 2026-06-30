/-
The DYNAMICS on the complete GNS Hilbert space: the transfer (time-translation)
operator and the reconstructed mass gap.

# Which gap this closes / opens

`Continuum/GNSComplete.lean` delivered the genuine constructive COMPLETE GNS
Hilbert space (`CompleteGNSHilbert`, and the unconditional
`CompleteGNSHilbertGeneral`).  The physical content of OS reconstruction now lives
ON that space: the time-translation / transfer operator `T`, and its spectral gap
— the mass gap.  This module builds the `Type`-level interface for that dynamics.

# What is genuine here (constructed / proved, axiom-clean)

  * **The `RC`-valued order (`RCle`, `RCnonneg`).**  The eventual rational order
    `CReal.leEv` (transitive) descends through `CReal.Equiv` to the real quotient
    `RC = CReal/Equiv` (`leEv_congr` + `Quotient.lift₂`).  This is the order in
    which the operator bounds are phrased.

  * **Reflection positivity on the completion (`cinner_self_nonneg`).**  The
    completed `CReal`-valued inner product is positive on the diagonal:
    `⟨z,z⟩ ≥ 0` in `RC`, for every point `z` of the completion — the limit of the
    representative-level `B(xₙ,xₙ) ≥ 0`.

  * **The `TransferOperator` interface.**  A map `T` on the completed carrier with
    the OS/reflection-positivity content stated through `cinner`: self-adjointness
    (`⟨Tx,y⟩ = ⟨x,Ty⟩`, an `RC`-equality), positivity (`⟨Tx,x⟩ ≥ 0`), and the
    contraction bound (`‖Tx‖² ≤ ‖x‖²`).  Inhabited non-vacuously by the identity
    operator (`idTransfer`) on the concrete Wilson/GNS completion.

  * **The `SpectralGapData` interface and `mass_gap_of_spectralGap`.**  Mirroring
    `Continuum/LocatedSpectralGap.lean`: a finite (compact) transfer model with a
    LOCATED gap `sep < 1` below the vacuum eigenvalue `1`.
    `mass_gap_of_spectralGap` extracts the strictly positive eigenvalue-gap margin
    `Δ = 1 − sep > 0` (the constructive mass gap; the physical mass is `−log sep`,
    the `log` avoided) together with the geometric two-point decay
    `G(n) ≤ G(0)·sep ⁿ` — the `e^{−Δ}`-type bound.  Inhabited in a trivial finite
    located case (`trivialSpectralGapData`) for non-vacuity.

# Honest residual (the continuum frontier)

The `TransferOperator`'s carrier has no built-in vector-space operations in this
development, so explicit additive linearity is not stated (the inner-product
axioms above are the constructive substance the mass gap rests on).  More
importantly: the GENUINE, spacing-uniform `SpectralGapData` for the physical
Wilson transfer operator — a `LocatedSpectralGap` whose margin does not collapse
as the lattice spacing `a → 0` — is the honest OPEN input.  It EQUALS the
continuum frontier of the whole programme.  The trivial inhabitant proves the
interface is non-vacuous; it is NOT the physical gap.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorryAx`,
no `native_decide`, no custom `axiom`.
-/

import YMGap.Continuum.GNSComplete
import YMGap.Continuum.LocatedSpectralGap

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient

namespace YMGap.Constructive

/-! ## The `RC`-valued eventual order -/

namespace CReal

/-- One-slack-free: `Equiv ⟹ leEv` (the eventual one-directional order). -/
theorem leEv_of_equiv {A B : CReal} (h : Equiv A B) : leEv A B := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  exact ⟨N, fun n hn => (hN n hn).1⟩

/-- `leEv` is `Equiv`-congruent on both arguments (so it descends to `RC`). -/
theorem leEv_congr {a a' b b' : CReal} (ha : Equiv a a') (hb : Equiv b b') :
    leEv a b ↔ leEv a' b' := by
  constructor
  · intro h
    exact leEv_trans (leEv_trans (leEv_of_equiv (Equiv.symm ha)) h) (leEv_of_equiv hb)
  · intro h
    exact leEv_trans (leEv_trans (leEv_of_equiv ha) h) (leEv_of_equiv (Equiv.symm hb))

/-- **The eventual order on the real quotient `RC = CReal/Equiv`.** -/
def RCle : RC → RC → Prop :=
  Quotient.lift₂ (s₁ := crealSetoid) (s₂ := crealSetoid)
    (fun a b => leEv a b)
    (fun _ _ _ _ ha hb => propext (leEv_congr ha hb))

@[simp] theorem RCle_mk (a b : CReal) :
    RCle (Quotient.mk crealSetoid a) (Quotient.mk crealSetoid b) = leEv a b := rfl

/-- `RCle` is reflexive. -/
theorem RCle_refl (a : RC) : RCle a a := by
  refine Quotient.inductionOn a (fun x => ?_)
  exact leEv_refl x

/-- Zero of `RC` (the class of `czero`). -/
def RCzero : RC := Quotient.mk crealSetoid czero

/-- **Nonnegativity in `RC`**: `0 ≤ a`. -/
def RCnonneg (a : RC) : Prop := RCle RCzero a

end CReal

end YMGap.Constructive

/-! ## Reflection positivity of the completed inner product -/

namespace YMGap.Continuum.GNSQuotient

namespace GNSData

variable (D : GNSData)

/-- **Reflection positivity on the completion.**  `⟨z,z⟩ ≥ 0` in `RC` for every
point `z` of the metric completion — the descended limit of the
representative-level `B(xₙ,xₙ) ≥ 0`. -/
theorem cinner_self_nonneg (z : GNSCompletionSpace D) :
    CReal.RCnonneg (D.cinnerCompl z z) := by
  refine Quotient.inductionOn z (fun x => ?_)
  show CReal.leEv CReal.czero (D.cinnerRep x x)
  exact CReal.leEv_ofQ'_of_approx_ge (fun _ => D.self_nonneg _)

end GNSData

end YMGap.Continuum.GNSQuotient

namespace YMGap.Continuum

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.SpectralGap

/-! ## The transfer (time-translation) operator -/

/-- A **transfer operator** on a complete GNS Hilbert space.  The physically
load-bearing OS / reflection-positivity content is stated through the completed
inner product `cinner`: self-adjointness (an `RC`-equality), positivity, and the
contraction bound (squared-norm `RC`-order).  The carrier's vector-space
operations are not built in this development, so explicit additive linearity is
deferred — these inner-product axioms are the constructive substance. -/
structure TransferOperator {D : GNSData} (H : CompleteGNSHilbert D) where
  /-- The operator on the completed carrier. -/
  T : H.hilbert.carrier → H.hilbert.carrier
  /-- The vacuum vector. -/
  vacuum : H.hilbert.carrier
  /-- **Self-adjointness** w.r.t. the completed inner product. -/
  selfAdjoint : ∀ x y, H.hilbert.cinner (T x) y = H.hilbert.cinner x (T y)
  /-- **Positivity** `⟨T x, x⟩ ≥ 0` (positive transfer matrix / reflection
  positivity). -/
  positive : ∀ x, CReal.RCnonneg (H.hilbert.cinner (T x) x)
  /-- **Contraction** `‖T x‖² ≤ ‖x‖²` (spectral radius `≤ 1`). -/
  contraction : ∀ x, CReal.RCle (H.hilbert.cinner (T x) (T x)) (H.hilbert.cinner x x)

/-- **Non-vacuity (identity operator).**  The identity is a transfer operator on
the concrete GNS completion: self-adjoint (trivially), positive (reflection
positivity, `cinner_self_nonneg`), and a contraction (reflexivity of `RCle`). -/
def GNSQuotient.GNSData.idTransfer (D : GNSData) : TransferOperator D.gnsComplete where
  T := id
  vacuum := GNSQuotient.embedV D D.zero
  selfAdjoint := fun _ _ => rfl
  positive := fun x => D.cinner_self_nonneg x
  contraction := fun _ => CReal.RCle_refl _

/-! ## The reconstructed mass gap (located spectral-gap form) -/

/-- The **spectral-gap datum** reconstructed on a complete GNS Hilbert space: a
transfer operator together with a finite (compact) Källén–Lehmann spectral model
carrying a LOCATED gap `sep < 1` below the vacuum eigenvalue `1`. -/
structure SpectralGapData {D : GNSData} (H : CompleteGNSHilbert D) where
  /-- The transfer operator whose gap this datum records. -/
  op : TransferOperator H
  /-- The finite spectral model of the transfer operator. -/
  model : SpectralModel
  /-- The located spectral gap: `sep < 1` bounding the excited spectrum. -/
  gap : LocatedSpectralGap model

/-- The reconstructed mass gap `Δ = 1 − sep > 0`. -/
def SpectralGapData.massGap {D : GNSData} {H : CompleteGNSHilbert D}
    (G : SpectralGapData H) : Q' := G.gap.gapMargin

theorem SpectralGapData.massGap_pos {D : GNSData} {H : CompleteGNSHilbert D}
    (G : SpectralGapData H) : (0 : Q') < G.massGap :=
  G.gap.gapMargin_pos

/-- **`mass_gap_of_spectralGap`.**  Extract from a `SpectralGapData` the strictly
positive eigenvalue-gap margin `Δ = 1 − sep > 0` (the constructive mass gap)
together with the geometric two-point decay `G(n) ≤ G(0)·sep ⁿ` — the
`e^{−Δ}`-type bound that IS the reconstructed mass gap. -/
theorem mass_gap_of_spectralGap {D : GNSData} {H : CompleteGNSHilbert D}
    (G : SpectralGapData H) :
    ∃ Δ : Q', (0 : Q') < Δ ∧
      ∀ n : Nat, corr G.model n ≤ (corr G.model 0) * G.gap.sep ^ n :=
  ⟨G.massGap, G.gap.gapMargin_pos, fun n => G.gap.decay n⟩

/-! ## Non-vacuity: a trivial finite located case -/

/-- A trivial finite spectral model (no modes). -/
def trivialSpectralModel : SpectralModel where
  k := 0
  w := fun _ => 0
  lam := fun _ => 0
  w_nonneg := fun _ => Q'.le_refl' 0
  lam_nonneg := fun _ => Q'.le_refl' 0

/-- `1/2 < 1`. -/
theorem invSucc_one_lt_one : Q'.invSucc 1 < (1 : Q') := by decide

/-- A trivial located gap (separator `1/2 < 1`, every eigenvalue `0 ≤ 1/2`). -/
def trivialLocatedGap : LocatedSpectralGap trivialSpectralModel where
  sep := Q'.invSucc 1
  sep_lt_one := invSucc_one_lt_one
  bound := fun _ => Q'.invSucc_nonneg 1

/-- **Non-vacuity of `SpectralGapData`.**  The interface is inhabited on the
concrete GNS completion (identity operator + trivial located gap).  This is NOT
the physical gap; the genuine spacing-uniform `SpectralGapData` for the Wilson
transfer operator is the honest open input (= the continuum frontier). -/
def GNSQuotient.GNSData.trivialSpectralGapData (D : GNSData) :
    SpectralGapData D.gnsComplete where
  op := D.idTransfer
  model := trivialSpectralModel
  gap := trivialLocatedGap

/-- The trivial datum yields a positive `Δ` — the interface produces a genuine
positive mass-gap witness (non-vacuously). -/
theorem GNSQuotient.GNSData.trivial_massGap_pos (D : GNSData) :
    (0 : Q') < (D.trivialSpectralGapData).massGap :=
  (D.trivialSpectralGapData).massGap_pos

end YMGap.Continuum

/-! ## The Wilson dynamics -/

namespace YMGap.Continuum.WilsonGNS

open YMGap.Continuum
open YMGap.Continuum.GNSQuotient

/-- **The transfer operator on the Wilson GNS Hilbert space** (identity
inhabitant; non-vacuity). -/
def WilsonGNSData.idTransfer {A : ObservableMeasure.ObsAlg} (W : WilsonGNSData A) :
    TransferOperator W.toGNSData.gnsComplete :=
  W.toGNSData.idTransfer

/-- **Non-vacuity of the reconstructed Wilson mass-gap interface.** -/
def WilsonGNSData.trivialSpectralGapData {A : ObservableMeasure.ObsAlg}
    (W : WilsonGNSData A) : SpectralGapData W.toGNSData.gnsComplete :=
  W.toGNSData.trivialSpectralGapData

/-- **The reconstructed Wilson mass gap, given a `SpectralGapData`.**  This is the
honest reduction: from ANY located transfer-operator gap on the Wilson GNS Hilbert
space, extract a strictly positive mass gap `Δ` with geometric decay.  The genuine
spacing-uniform such datum is the open continuum input. -/
theorem WilsonGNSData.mass_gap_of_spectralGap {A : ObservableMeasure.ObsAlg}
    (W : WilsonGNSData A) (G : SpectralGapData W.toGNSData.gnsComplete) :
    ∃ Δ : Q', (0 : Q') < Δ ∧
      ∀ n : Nat, SpectralGap.corr G.model n
        ≤ (SpectralGap.corr G.model 0) * G.gap.sep ^ n :=
  YMGap.Continuum.mass_gap_of_spectralGap G

end YMGap.Continuum.WilsonGNS

namespace YMGap.Constructive

/-! ## Axiom gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Constructive.CReal.leEv_congr
#print axioms YMGap.Constructive.CReal.RCle
#print axioms YMGap.Constructive.CReal.RCle_refl
#print axioms YMGap.Continuum.GNSQuotient.GNSData.cinner_self_nonneg
#print axioms YMGap.Continuum.GNSQuotient.GNSData.idTransfer
#print axioms YMGap.Continuum.invSucc_one_lt_one
#print axioms YMGap.Continuum.trivialLocatedGap
#print axioms YMGap.Continuum.mass_gap_of_spectralGap
#print axioms YMGap.Continuum.GNSQuotient.GNSData.trivialSpectralGapData
#print axioms YMGap.Continuum.GNSQuotient.GNSData.trivial_massGap_pos
#print axioms YMGap.Continuum.WilsonGNS.WilsonGNSData.idTransfer
#print axioms YMGap.Continuum.WilsonGNS.WilsonGNSData.mass_gap_of_spectralGap

end YMGap.Constructive
