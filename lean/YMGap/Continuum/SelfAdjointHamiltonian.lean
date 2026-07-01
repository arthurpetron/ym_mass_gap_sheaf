/-
Operator-level scaffolding for `H = −log T` on the completed GNS Hilbert space.

# The soundness constraint that shapes this module

`H = −log T` is NOT achievable as a bounded operator.  On `vac⊥` the located
transfer spectrum is `[0, sep]` with the top pinned `sep < 1` but the bottom only
`≥ 0`; `−log` is *unbounded at 0*, and the Bridges–Ishihara continuous functional
calculus produces bounded operators from bounded continuous functions only.  So
the achievable operator-level object is the BOUNDED quadratic-form gap for `T`,
from which the physical gap `Δ = −log sep` is delivered at the *scalar / form*
level by the already-proved `isPositive_neg_logRat`.  Building `H` itself as a
bounded operator is quarantined into a single named residual.

# What is genuine here (constructed / proved, axiom-clean)

  * **RC order algebra.**  `CReal.Equiv_add` (the sum respects `Equiv`),
    `CReal.RCadd` (the lifted real addition), `CReal.RCle_trans` /
    `CReal.RCle_antisymm` (the real order is a partial order), and the auxiliary
    `CReal.equiv_of_leEv_leEv`.  These upgrade the previously THIN `RC` order to a
    genuine ordered additive structure — enough to state operator bounds.

  * **Vector-space scaffold on the completion.**  `GNSData.cAdd`, `cNeg`, `cSub`
    on `GNSCompletionSpace` — the pointwise-on-representatives lifts, well-defined
    through `CauchyNull`.  The Cauchy modulus of the sum comes from the quadratic
    `distSqQ_add_le` (a parallelogram bound mirroring `distSqQ_triangle`); the sum
    respects `CauchyNull` for the same reason.  Computation rules `cAdd_embed`,
    `cNeg_embed` show these extend the pre-Hilbert operations on the dense image.
    This discharges the literal blocker "the carrier has no vector-space
    operations".

  * **Additive transfer scaffold.**  `AdditiveTransferOperator` (a
    `TransferOperator` that is additive w.r.t. `cAdd`), non-vacuously inhabited by
    the identity (`idAdditiveTransfer`).  Additivity is the achievable half of
    linearity; scalar-linearity is blocked (see the residual) because `GNSData`
    carries no module distributivity of `smul` over `add`.

  * **The form-level Hamiltonian gap.**  `SpectralGapData.vacPerp` (the excited
    subspace) and `SpectralGapData.hamiltonian_form_gap` = the positive `CReal`
    `Δ = −log sep`, reusing `hamiltonianGapReal_pos` verbatim.  NO operator
    `−log(T)` is formed.

# What stays open (honest, Type-level residuals; AGENTS.md Rule 8)

  * `VectorScalingResidual` — the completion scalar action `cSmul`.  `GNSData`
    lacks the module law `smul s (a − b) ≈ smul s a − smul s b`, so the Cauchy
    modulus of a scaled sequence cannot be established from the axioms; only the
    *form* homogeneity `B_smul_left` is available (which fixes the value, not the
    vector).  This is the precise obstruction to full linearity.

  * `RCScaleResidual` — the `RC`-by-`Q'` scaling `RCscale` with its monotonicity.
    Constructing it needs a genuine analytic (division) Cauchy modulus; recorded
    as data to be supplied.

  * `TransferFormGapResidual` — the operator-level `T`-gap `⟨T x, x⟩ ≤ sep·⟨x,x⟩`
    on `vac⊥`.  It is NOT derivable from the current `TransferOperator` fields
    (self-adjoint / positive / contraction): the separator `sep` lives in the
    finite `SpectralModel`, disconnected from `T`'s quadratic form.  A genuine
    spectral bridge is the missing input.

  * `BoundedFunctionalCalculusResidual` — the single irreducibly hard object: a
    genuine self-adjoint, ADDITIVE (Brick 3) bounded operator `H` with `e^{−H}=T`,
    obtained through a BOUNDED functional-calculus surrogate (e.g. a resolvent),
    NEVER through polynomial approximation of the unbounded `−log`.  Upgraded over
    the prior `SelfAdjointHamiltonianResidual` by carrying additivity (`op_add`,
    tied to `cAdd`) and the proved gap witness.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorryAx`,
no `native_decide`, no custom `axiom`.
-/

import YMGap.Continuum.GNSHamiltonian

open YMGap.Constructive
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.SpectralGap
open YMGap.Constructive.CRealLog

namespace YMGap.Constructive

namespace CReal

/-! ## RC order algebra — upgrading the thin `RC` order

The completed inner product is valued in `RC = CReal / Equiv` (`GNSDynamics`),
which so far carried only `RCle`, `RCzero`, `RCnonneg`.  We add the lifted real
addition and the missing order laws (transitivity, antisymmetry). -/

/-- **The sum respects `Equiv`.**  If `a ≈ a'` and `b ≈ b'` then
`a + b ≈ a' + b'` — the congruence that lets `add` descend to `RC`. -/
theorem Equiv_add {a a' b b' : CReal} (ha : Equiv a a') (hb : Equiv b b') :
    Equiv (add a b) (add a' b') := by
  intro ε hε
  have hhε : (0 : Q') < HalfPow.half * ε := ExpNeg.half_mul_pos ε hε
  obtain ⟨N1, hN1⟩ := ha (HalfPow.half * ε) hhε
  obtain ⟨N2, hN2⟩ := hb (HalfPow.half * ε) hhε
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have hn1 : N1 ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hn2 : N2 ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  obtain ⟨ha1, ha2⟩ := hN1 n hn1
  obtain ⟨hb1, hb2⟩ := hN2 n hn2
  have step : ∀ am an bm bn : Q',
      am ≤ an + HalfPow.half * ε → bm ≤ bn + HalfPow.half * ε →
      am + bm ≤ (an + bn) + ε := by
    intro am an bm bn haa hbb
    have hsum : am + bm ≤ (an + HalfPow.half * ε) + (bn + HalfPow.half * ε) :=
      Q'.add_le_add haa hbb
    have ereg : ((an + HalfPow.half * ε) + (bn + HalfPow.half * ε)).eqv
        ((an + bn) + (HalfPow.half * ε + HalfPow.half * ε)) :=
      Q'.regroup an bn (HalfPow.half * ε)
    have etwo : ((an + bn) + (HalfPow.half * ε + HalfPow.half * ε)).eqv ((an + bn) + ε) :=
      Q'.add_eqv_congr_left (an + bn) (HalfPow.half * ε + HalfPow.half * ε) ε
        (ExpNeg.two_halves ε)
    exact Q'.le_trans' _ _ _ hsum
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv ereg) (Q'.le_of_eqv etwo))
  refine ⟨?_, ?_⟩
  · show a.approx n + b.approx n ≤ (a'.approx n + b'.approx n) + ε
    exact step (a.approx n) (a'.approx n) (b.approx n) (b'.approx n) ha1 hb1
  · show a'.approx n + b'.approx n ≤ (a.approx n + b.approx n) + ε
    exact step (a'.approx n) (a.approx n) (b'.approx n) (b.approx n) ha2 hb2

/-- **The real addition on `RC = CReal/Equiv`.**  The lift of `CReal.add`. -/
def RCadd : RC → RC → RC :=
  Quotient.lift₂ (s₁ := crealSetoid) (s₂ := crealSetoid)
    (fun a b => Quotient.mk crealSetoid (add a b))
    (fun _ _ _ _ ha hb => Quotient.sound (Equiv_add ha hb))

@[simp] theorem RCadd_mk (a b : CReal) :
    RCadd (Quotient.mk crealSetoid a) (Quotient.mk crealSetoid b)
      = Quotient.mk crealSetoid (add a b) := rfl

/-- **Transitivity of the real order.**  Descends `leEv_trans`. -/
theorem RCle_trans {a b c : RC} : RCle a b → RCle b c → RCle a c := by
  refine Quotient.inductionOn₃ a b c ?_
  intro x y z h1 h2
  exact leEv_trans h1 h2

/-- Two-sided `leEv` gives `Equiv` (the antisymmetry witness). -/
theorem equiv_of_leEv_leEv {x y : CReal} (h1 : leEv x y) (h2 : leEv y x) :
    Equiv x y := by
  intro ε hε
  obtain ⟨N1, hN1⟩ := h1 ε hε
  obtain ⟨N2, hN2⟩ := h2 ε hε
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have hn1 : N1 ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hn2 : N2 ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  exact ⟨hN1 n hn1, hN2 n hn2⟩

/-- **Antisymmetry of the real order.**  `a ≤ b`, `b ≤ a` ⟹ `a = b` in `RC`. -/
theorem RCle_antisymm {a b : RC} : RCle a b → RCle b a → a = b := by
  refine Quotient.inductionOn₂ a b ?_
  intro x y h1 h2
  exact Quotient.sound (equiv_of_leEv_leEv h1 h2)

end CReal

end YMGap.Constructive

/-! ## Vector-space scaffold on the completion -/

namespace YMGap.Continuum.GNSQuotient

namespace GNSData

variable (D : GNSData)

/-- **The squared distance is negation-invariant** `d²(−a,−b) ≃ d²(a,b)`.
`(−a)−(−b) ≈ b−a`, then `B_diag_congr` + `distSqQ_comm`. -/
theorem distSqQ_neg (a b : D.V) :
    (D.distSqQ (D.neg a) (D.neg b)).eqv (D.distSqQ a b) := by
  have hv : D.veq (D.sub (D.neg a) (D.neg b)) (D.sub b a) :=
    D.veq_trans (D.add_congr (D.veq_refl (D.neg a)) (D.neg_neg b))
      (D.add_comm (D.neg a) b)
  exact Q'.eqv_trans _ _ _ (D.B_diag_congr hv) (D.distSqQ_comm b a)

/-- **The quadratic sum bound** `d²(a+b, a'+b') ≤ 2·d²(a,a') + 2·d²(b,b')`
(written `(P+P)+(Q+Q)`).  Same parallelogram argument as `distSqQ_triangle`,
with `u = a−a'`, `v = b−b'` and `sub_sub_distrib` supplying the vector identity
`(a+b)−(a'+b') ≈ (a−a')+(b−b')`. -/
theorem distSqQ_add_le (a b a' b' : D.V) :
    D.distSqQ (D.add a b) (D.add a' b') ≤
      (D.distSqQ a a' + D.distSqQ a a') + (D.distSqQ b b' + D.distSqQ b b') := by
  have hexp0 := D.B_add_diag_expand (D.sub a a') (D.sub b b')
  have hsym : (D.B (D.sub b b') (D.sub a a')).eqv (D.B (D.sub a a') (D.sub b b')) :=
    D.B_symm (D.sub b b') (D.sub a a')
  have hexp : (D.B (D.add (D.sub a a') (D.sub b b')) (D.add (D.sub a a') (D.sub b b'))).eqv
      ((D.B (D.sub a a') (D.sub a a') + D.B (D.sub a a') (D.sub b b'))
        + (D.B (D.sub a a') (D.sub b b') + D.B (D.sub b b') (D.sub b b'))) :=
    Q'.eqv_trans _ _ _ hexp0
      (QPoly.q_add_congr (Q'.eqv_refl _) (QPoly.q_add_congr hsym (Q'.eqv_refl _)))
  have hv : D.veq (D.sub (D.add a b) (D.add a' b')) (D.add (D.sub a a') (D.sub b b')) :=
    D.sub_sub_distrib a b a' b'
  have hdiag : (D.B (D.sub (D.add a b) (D.add a' b')) (D.sub (D.add a b) (D.add a' b'))).eqv
      (D.B (D.add (D.sub a a') (D.sub b b')) (D.add (D.sub a a') (D.sub b b'))) :=
    D.B_diag_congr hv
  have hfull : (D.distSqQ (D.add a b) (D.add a' b')).eqv
      ((D.distSqQ a a' + D.B (D.sub a a') (D.sub b b'))
        + (D.B (D.sub a a') (D.sub b b') + D.distSqQ b b')) :=
    Q'.eqv_trans _ _ _ hdiag hexp
  have hre1 := GNSAux.rearr1 (D.distSqQ a a') (D.B (D.sub a a') (D.sub b b')) (D.distSqQ b b')
  have hcross : (D.B (D.sub a a') (D.sub b b') + D.B (D.sub a a') (D.sub b b'))
        ≤ (D.distSqQ a a' + D.distSqQ b b') :=
    D.B_cross_le (D.sub a a') (D.sub b b')
  have h1 : D.distSqQ (D.add a b) (D.add a' b')
        ≤ ((D.distSqQ a a' + D.distSqQ b b')
            + (D.B (D.sub a a') (D.sub b b') + D.B (D.sub a a') (D.sub b b'))) :=
    Q'.le_of_eqv (Q'.eqv_trans _ _ _ hfull hre1)
  have h2 : ((D.distSqQ a a' + D.distSqQ b b')
            + (D.B (D.sub a a') (D.sub b b') + D.B (D.sub a a') (D.sub b b')))
        ≤ ((D.distSqQ a a' + D.distSqQ b b') + (D.distSqQ a a' + D.distSqQ b b')) :=
    Q'.add_le_add_left (D.distSqQ a a' + D.distSqQ b b') _ _ hcross
  have h3 : ((D.distSqQ a a' + D.distSqQ b b') + (D.distSqQ a a' + D.distSqQ b b')).eqv
        ((D.distSqQ a a' + D.distSqQ a a') + (D.distSqQ b b' + D.distSqQ b b')) :=
    GNSAux.add4_swap (D.distSqQ a a') (D.distSqQ b b')
  exact le_of_le_eqv (Q'.le_trans' _ _ _ h1 h2) h3

/-! ### The additive lifts on Cauchy representatives -/

/-- The pointwise sum of two Cauchy representatives; Cauchy via `distSqQ_add_le`
and the quartering `4·(ε/4) = ε`. -/
def cAddCauchy (x y : CauchyGNS D) : CauchyGNS D where
  seq := fun n => D.add (x.seq n) (y.seq n)
  modulus := fun ε =>
    max (x.modulus (HalfPow.half * (HalfPow.half * ε)))
        (y.modulus (HalfPow.half * (HalfPow.half * ε)))
  isCauchy := by
    intro ε hε p q hp hq
    have hq4 : (0 : Q') < HalfPow.half * (HalfPow.half * ε) :=
      ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos ε hε)
    have hpx : x.modulus (HalfPow.half * (HalfPow.half * ε)) ≤ p :=
      Nat.le_trans (Nat.le_max_left _ _) hp
    have hqx : x.modulus (HalfPow.half * (HalfPow.half * ε)) ≤ q :=
      Nat.le_trans (Nat.le_max_left _ _) hq
    have hpy : y.modulus (HalfPow.half * (HalfPow.half * ε)) ≤ p :=
      Nat.le_trans (Nat.le_max_right _ _) hp
    have hqy : y.modulus (HalfPow.half * (HalfPow.half * ε)) ≤ q :=
      Nat.le_trans (Nat.le_max_right _ _) hq
    have hax : D.distSqQ (x.seq p) (x.seq q) ≤ HalfPow.half * (HalfPow.half * ε) :=
      x.isCauchy _ hq4 p q hpx hqx
    have hay : D.distSqQ (y.seq p) (y.seq q) ≤ HalfPow.half * (HalfPow.half * ε) :=
      y.isCauchy _ hq4 p q hpy hqy
    have hbound := D.distSqQ_add_le (x.seq p) (y.seq p) (x.seq q) (y.seq q)
    have hr : (D.distSqQ (x.seq p) (x.seq q) + D.distSqQ (x.seq p) (x.seq q))
              + (D.distSqQ (y.seq p) (y.seq q) + D.distSqQ (y.seq p) (y.seq q))
            ≤ ((HalfPow.half * (HalfPow.half * ε) + HalfPow.half * (HalfPow.half * ε))
                + (HalfPow.half * (HalfPow.half * ε) + HalfPow.half * (HalfPow.half * ε))) :=
      Q'.add_le_add (Q'.add_le_add hax hax) (Q'.add_le_add hay hay)
    have heps : ((HalfPow.half * (HalfPow.half * ε) + HalfPow.half * (HalfPow.half * ε))
                + (HalfPow.half * (HalfPow.half * ε) + HalfPow.half * (HalfPow.half * ε))).eqv ε := by
      have hqq : (HalfPow.half * (HalfPow.half * ε) + HalfPow.half * (HalfPow.half * ε)).eqv
          (HalfPow.half * ε) := ExpNeg.two_halves (HalfPow.half * ε)
      exact Q'.eqv_trans _ _ _ (QPoly.q_add_congr hqq hqq) (ExpNeg.two_halves ε)
    exact le_of_le_eqv (Q'.le_trans' _ _ _ hbound hr) heps

/-- `cAddCauchy` respects `CauchyNull` on both arguments. -/
theorem cAddCauchy_null {x x' y y' : CauchyGNS D}
    (hx : CauchyNull D x x') (hy : CauchyNull D y y') :
    CauchyNull D (D.cAddCauchy x y) (D.cAddCauchy x' y') := by
  intro ε hε
  have hq4 : (0 : Q') < HalfPow.half * (HalfPow.half * ε) :=
    ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos ε hε)
  obtain ⟨N1, hN1⟩ := hx _ hq4
  obtain ⟨N2, hN2⟩ := hy _ hq4
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have hn1 : N1 ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hn2 : N2 ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  have hax : D.distSqQ (x.seq n) (x'.seq n) ≤ HalfPow.half * (HalfPow.half * ε) := hN1 n hn1
  have hay : D.distSqQ (y.seq n) (y'.seq n) ≤ HalfPow.half * (HalfPow.half * ε) := hN2 n hn2
  have hbound := D.distSqQ_add_le (x.seq n) (y.seq n) (x'.seq n) (y'.seq n)
  have hr : (D.distSqQ (x.seq n) (x'.seq n) + D.distSqQ (x.seq n) (x'.seq n))
            + (D.distSqQ (y.seq n) (y'.seq n) + D.distSqQ (y.seq n) (y'.seq n))
          ≤ ((HalfPow.half * (HalfPow.half * ε) + HalfPow.half * (HalfPow.half * ε))
              + (HalfPow.half * (HalfPow.half * ε) + HalfPow.half * (HalfPow.half * ε))) :=
    Q'.add_le_add (Q'.add_le_add hax hax) (Q'.add_le_add hay hay)
  have heps : ((HalfPow.half * (HalfPow.half * ε) + HalfPow.half * (HalfPow.half * ε))
              + (HalfPow.half * (HalfPow.half * ε) + HalfPow.half * (HalfPow.half * ε))).eqv ε := by
    have hqq : (HalfPow.half * (HalfPow.half * ε) + HalfPow.half * (HalfPow.half * ε)).eqv
        (HalfPow.half * ε) := ExpNeg.two_halves (HalfPow.half * ε)
    exact Q'.eqv_trans _ _ _ (QPoly.q_add_congr hqq hqq) (ExpNeg.two_halves ε)
  exact le_of_le_eqv (Q'.le_trans' _ _ _ hbound hr) heps

/-- The pointwise negation of a Cauchy representative; Cauchy via `distSqQ_neg`. -/
def cNegCauchy (x : CauchyGNS D) : CauchyGNS D where
  seq := fun n => D.neg (x.seq n)
  modulus := x.modulus
  isCauchy := by
    intro ε hε p q hp hq
    exact le_of_eqv_le (D.distSqQ_neg (x.seq p) (x.seq q)) (x.isCauchy ε hε p q hp hq)

/-- `cNegCauchy` respects `CauchyNull`. -/
theorem cNegCauchy_null {x x' : CauchyGNS D} (hx : CauchyNull D x x') :
    CauchyNull D (D.cNegCauchy x) (D.cNegCauchy x') := by
  intro ε hε
  obtain ⟨N, hN⟩ := hx ε hε
  exact ⟨N, fun n hn => le_of_eqv_le (D.distSqQ_neg (x.seq n) (x'.seq n)) (hN n hn)⟩

/-! ### The descended completion operations -/

/-- **Addition on the completion** `⟦x⟧ + ⟦y⟧ = ⟦x+y⟧`. -/
def cAdd : GNSCompletionSpace D → GNSCompletionSpace D → GNSCompletionSpace D :=
  Quotient.lift₂ (fun x y => Quotient.mk (cauchySetoid D) (D.cAddCauchy x y))
    (fun _ _ _ _ hx hy => Quotient.sound (D.cAddCauchy_null hx hy))

/-- **Negation on the completion** `−⟦x⟧ = ⟦−x⟧`. -/
def cNeg : GNSCompletionSpace D → GNSCompletionSpace D :=
  Quotient.lift (fun x => Quotient.mk (cauchySetoid D) (D.cNegCauchy x))
    (fun _ _ hx => Quotient.sound (D.cNegCauchy_null hx))

/-- **Subtraction on the completion** `x − y := x + (−y)`. -/
def cSub (x y : GNSCompletionSpace D) : GNSCompletionSpace D := D.cAdd x (D.cNeg y)

/-- `cAdd` extends `add` on the dense image: `⟦const a⟧ + ⟦const b⟧ = ⟦const (a+b)⟧`. -/
theorem cAdd_embed (a b : D.V) :
    D.cAdd (embedV D a) (embedV D b) = embedV D (D.add a b) := by
  apply Quotient.sound
  intro ε hε
  exact ⟨0, fun n _ => Q'.le_trans' _ 0 ε
    (Q'.le_of_eqv (D.rad_refl (D.add a b))) (Q'.le_of_lt hε)⟩

/-- `cNeg` extends `neg` on the dense image: `−⟦const a⟧ = ⟦const (−a)⟧`. -/
theorem cNeg_embed (a : D.V) :
    D.cNeg (embedV D a) = embedV D (D.neg a) := by
  apply Quotient.sound
  intro ε hε
  exact ⟨0, fun n _ => Q'.le_trans' _ 0 ε
    (Q'.le_of_eqv (D.rad_refl (D.neg a))) (Q'.le_of_lt hε)⟩

/-- `cSub` extends `sub` on the dense image. -/
theorem cSub_embed (a b : D.V) :
    D.cSub (embedV D a) (embedV D b) = embedV D (D.sub a b) := by
  show D.cAdd (embedV D a) (D.cNeg (embedV D b)) = embedV D (D.add a (D.neg b))
  rw [D.cNeg_embed b, D.cAdd_embed a (D.neg b)]

end GNSData

end YMGap.Continuum.GNSQuotient

/-! ## Operator-level scaffolds and the form-level gap -/

namespace YMGap.Continuum

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient

/-- An **additive transfer operator** on the concrete GNS completion: a
`TransferOperator` on `D.gnsComplete` that is additive with respect to the
completion addition `cAdd`.  Additivity is the achievable half of linearity
(scalar-linearity is blocked — see `VectorScalingResidual`).  Together with the
inherited `selfAdjoint` field this is the reflection-positive, additive-linear
operator scaffold.  (The concrete completion is required because `cAdd` acts on
`GNSCompletionSpace D`, whereas a general `CompleteGNSHilbert`'s carrier is an
abstract `Type`.) -/
structure AdditiveTransferOperator (D : GNSData)
    extends TransferOperator D.gnsComplete where
  /-- **Additivity** `T (x + y) = T x + T y`. -/
  T_add : ∀ x y, T (D.cAdd x y) = D.cAdd (T x) (T y)

/-- **Non-vacuity (identity is additive).**  The identity transfer operator is
additive: `id (x + y) = x + y = id x + id y`. -/
def GNSQuotient.GNSData.idAdditiveTransfer (D : GNSData) :
    AdditiveTransferOperator D where
  toTransferOperator := D.idTransfer
  T_add := fun _ _ => rfl

/-! ### The excited subspace and the form-level Hamiltonian gap -/

/-- The **excited subspace** `vac⊥`: vectors orthogonal to the vacuum. -/
def SpectralGapData.vacPerp {D : GNSData} {H : CompleteGNSHilbert D}
    (G : SpectralGapData H) (x : H.hilbert.carrier) : Prop :=
  H.hilbert.cinner x G.op.vacuum = CReal.RCzero

/-- **Form-level Hamiltonian gap.**  `Δ = −log sep` is a genuine positive `CReal`
— the located form-gap of `H` on `vac⊥`, delivered by the already-proved scalar
transport `isPositive_neg_logRat`.  The operator `H` itself is NOT built (that is
`BoundedFunctionalCalculusResidual`); this is the bounded, scalar deliverable. -/
theorem SpectralGapData.hamiltonian_form_gap {D : GNSData} {H : CompleteGNSHilbert D}
    (G : SpectralGapData H)
    (hwin : Q'.abs (yOf G.gap.sep (sepPlusOne_pos G.gap)) ≤ recipOdd 1) :
    CReal.IsPositive (G.hamiltonianGapReal hwin) :=
  G.hamiltonianGapReal_pos hwin

/-! ## Honest named residuals (Type-level, Rule 8) -/

/-- **Vector-scaling residual.**  The completion scalar action `cSmul`.  Building
it needs the Cauchy modulus of a scaled representative sequence, i.e. a bound on
`d²(smul s a, smul s b)`.  `GNSData` provides only the FORM homogeneity
`B_smul_left` (`⟨smul s a, b⟩ ≃ s·⟨a,b⟩`), which fixes the paired value but not
the vector: there is no module law `smul s (a − b) ≈ smul s a − smul s b`, so the
squared distance of the scaled sequence cannot be controlled from the axioms.
This is the precise obstruction to full linearity. -/
structure VectorScalingResidual (D : GNSData) : Type where
  /-- The would-be scalar action on the completion. -/
  cSmul : Q' → GNSCompletionSpace D → GNSCompletionSpace D
  /-- It extends `smul` on the dense image. -/
  cSmul_embed : ∀ (s : Q') (a : D.V),
    cSmul s (embedV D a) = embedV D (D.smul s a)

/-- **RC-scaling residual.**  The `RC`-by-`Q'` scaling `RCscale` and its
monotonicity for nonnegative scalars.  Constructing `RCscale` needs a genuine
analytic (division) Cauchy modulus; recorded here as the data to be supplied.
Needed to phrase the *scaled* form-gap `sep·⟨x,x⟩` at the operator level. -/
structure RCScaleResidual : Type where
  /-- The `Q'`-scaling of a real. -/
  RCscale : Q' → CReal.RC → CReal.RC
  /-- Monotone in the scaled argument for `0 ≤ s`. -/
  RCscale_mono : ∀ {s : Q'}, (0 : Q') ≤ s → ∀ {a b : CReal.RC},
    CReal.RCle a b → CReal.RCle (RCscale s a) (RCscale s b)

/-- **Transfer form-gap residual.**  The operator-level `T`-gap on `vac⊥`,
`⟨T x, x⟩ ≤ sep·⟨x,x⟩`.  This is NOT derivable from the current
`TransferOperator` fields (`selfAdjoint` / `positive` / `contraction`): the
separator `sep` lives in the finite `SpectralModel`, disconnected from `T`'s
quadratic form.  The bridge from the located compact spectral model to `T`'s form
is the missing spectral-theoretic input, isolated here.  The scaled bound
`scaledInner x` stands for `sep·⟨x,x⟩` (its construction awaits
`RCScaleResidual`). -/
structure TransferFormGapResidual {D : GNSData} {H : CompleteGNSHilbert D}
    (G : SpectralGapData H) : Type where
  /-- The scaled inner product `x ↦ sep·⟨x,x⟩`, as an `RC`-valued map. -/
  scaledInner : H.hilbert.carrier → CReal.RC
  /-- The operator-level `T`-gap on `vac⊥`. -/
  form_gap : ∀ {x : H.hilbert.carrier}, G.vacPerp x →
    CReal.RCle (H.hilbert.cinner (G.op.T x) x) (scaledInner x)

/-- **Bounded functional-calculus residual (the single irreducibly hard node).**
A genuine self-adjoint, ADDITIVE bounded operator `H` on the completed carrier
with `e^{−H} = T`, obtained through a BOUNDED functional-calculus surrogate (e.g.
a resolvent `(1+H)⁻¹ = φ(T)` with `φ` bounded) — NEVER through polynomial
approximation of the unbounded `−log`.  Upgraded over the prior
`SelfAdjointHamiltonianResidual` by carrying additivity (`op_add`, tied to the
completion addition `cAdd` of Brick 1) and by recording the proved located gap
`Δ = −log sep` as `gapWitness`.  The genuinely unconstructed content is
`op` / `op_add` / `selfAdjoint`. -/
structure BoundedFunctionalCalculusResidual {D : GNSData}
    (G : SpectralGapData D.gnsComplete) (L : AdditiveTransferOperator D) : Type where
  /-- The reconstructed Hamiltonian `H` on the completed carrier. -/
  op : GNSCompletionSpace D → GNSCompletionSpace D
  /-- **Additivity** of `H` (Brick 3), stated through `cAdd`. -/
  op_add : ∀ x y, op (D.cAdd x y) = D.cAdd (op x) (op y)
  /-- **Self-adjointness** of `H` w.r.t. the completed inner product. -/
  selfAdjoint : ∀ x y,
    (D.gnsComplete).hilbert.cinner (op x) y = (D.gnsComplete).hilbert.cinner x (op y)
  /-- The proved located gap `Δ = −log sep > 0` that `H` realizes on `vac⊥`. -/
  gapWitness : ∀ (hwin : Q'.abs (yOf G.gap.sep (sepPlusOne_pos G.gap)) ≤ recipOdd 1),
    CReal.IsPositive (G.hamiltonianGapReal hwin)

end YMGap.Continuum

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Constructive.CReal.Equiv_add
#print axioms YMGap.Constructive.CReal.RCadd
#print axioms YMGap.Constructive.CReal.RCle_trans
#print axioms YMGap.Constructive.CReal.RCle_antisymm
#print axioms YMGap.Continuum.GNSQuotient.GNSData.distSqQ_neg
#print axioms YMGap.Continuum.GNSQuotient.GNSData.distSqQ_add_le
#print axioms YMGap.Continuum.GNSQuotient.GNSData.cAdd
#print axioms YMGap.Continuum.GNSQuotient.GNSData.cNeg
#print axioms YMGap.Continuum.GNSQuotient.GNSData.cAdd_embed
#print axioms YMGap.Continuum.GNSQuotient.GNSData.cNeg_embed
#print axioms YMGap.Continuum.GNSQuotient.GNSData.cSub_embed
#print axioms YMGap.Continuum.GNSQuotient.GNSData.idAdditiveTransfer
#print axioms YMGap.Continuum.SpectralGapData.hamiltonian_form_gap
