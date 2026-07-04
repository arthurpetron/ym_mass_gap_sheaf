/-
Track 11.10-o4 / R2 — **O(4)-restoration statement-layer reduction: both OS1
conjuncts fired from ONE structured input.**

# What this module supplies

The OS1 axiom carries TWO pieces of content on the observable algebra:

  * **H₄ (hypercubic) invariance** — `IsOS1HypercubicH4 E ψ`, functional
    equivariance `E(ψ a) = E a` under a genuine hypercubic-rotation `*`-hom `ψ`;
  * the **open O(4)-restoration clause** `RubricO4Restoration` — the continuum
    statement that the rotational-anisotropy defect vanishes as `a → 0`.

This module bundles the honest hypotheses for both into a single
`O4RestorationInput` and fires `IsOS1Full` (their conjunction) from it, with:

  * the H₄ conjunct discharged as a genuine **theorem**
    (`prodCharFunc_isotropic_H4_equivariant`), NOT a posited field — the
    ISOTROPIC product heat-kernel functional is equivariant under the genuine
    invertible order-4 automorphism `rot4` (cyclic edge shift).  This is `Eq`
    (not `.eqv`), so it is NOT `rfl`; it reduces to exactly one elementary
    arithmetic leaf, `mul4_cyclic`, a 4-fold cyclic-product `Eq` on `Q'` built
    from `Int`/`Nat` multiplication commutativity+associativity.  Isotropy
    (`wx = wy = w`) is essential — the anisotropic case is exactly where
    equivariance FAILS (`H4RotationAuto.prodAniso_pos`);
  * the open O(4) clause discharged verbatim from the proved AF decay-to-zero
    pipeline `O4ClauseStrength.rubricO4Restoration_of_strong`, with the explicit
    geometric certificate `(C, ρ)` surfaced (`ρ = ½`, `C = breakCoeff D 0`,
    envelope `breakCoeff_le_geo`).

# Honest scope (frontier UNCHANGED — do not overclaim)

The reduction adds NO new analytic content: it fires the open clause from a
STRUCTURED hypothesis (a pinned geometric schedule + a proved H₄ equivariance),
exactly as `O4BetaSign.o4_restored_of_tauModel` fires from a proven trajectory.
The out-of-scope (11.8-class) discharge is that the TRUE interacting Wilson
`anisoDefect` obeys this geometric decay for the physical AF `ρ`
(`O4RestorationProgress.CouplingRunning.betaDrop_nonneg`, `β ≤ 0`) — untouched.

Distinct from `RepTheory.Spin4.O4RestorationInput` (the gap-margin object); this
one lives in `YMGap.Continuum`.

# Axiom-gate (AGENTS.md Rules 1, 8)

Pure `Q'`/`Nat`/`Int`/`Prod` arithmetic and the reused proved AF-decay pipeline;
every load-bearing law is `Eq` via `Int`/`Nat` AC or `rfl`/`decide`.  All
witnesses are `Type`-level data.  Every load-bearing declaration is gated with
`#print axioms`; permitted output is `propext` / `Quot.sound` only.
-/

import YMGap.Continuum.OSAxioms
import YMGap.Continuum.H4RotationAuto
import YMGap.Rubric.ClayScorecard

namespace YMGap.Continuum.O4RestorationReduction

open YMGap.Constructive
open YMGap.Continuum.ObservableMeasure (ProbFunctional ObsAlg ObsHom)
open YMGap.Continuum.OSAxioms
open YMGap.Continuum.O4ClauseStrength
  (StrongO4Restoration anisoDefect rubricO4Restoration_of_strong)
open YMGap.Continuum.H4RotationAuto
  (prodCharAlg4 prodCharFunc rot4 rot4_nontrivial wX hwX)

/-! ## 0. Elementary `Eq`-level arithmetic on `Q'`

`Q'` is a raw `⟨num : Int, denPred : Nat⟩` struct; the library provides only
`.eqv`-level commutativity/associativity (`RationalsMul`).  For an `Eq`-level
`FunctionalEquivariant` we need genuine `Eq` multiplication laws, which hold
because `Q'.mul` is componentwise `Int`-mul on the numerator and `Nat`-mul (on
`den`, then predecessor) on the denominator — both commutative and associative
as literal `Eq`. -/

/-- Field extensionality for `Q'` via `den` (equivalently `denPred`, since
`den = denPred + 1` is injective). -/
theorem q_ext_den : ∀ {p q : Q'}, p.num = q.num → p.den = q.den → p = q
  | ⟨_, _⟩, ⟨_, _⟩, hn, hd => by
      cases hn
      have : _ = _ := hd
      simp only [Q'.den, Nat.add_right_cancel_iff] at this
      cases this; rfl

/-- The numerator of a product is the product of numerators (`rfl`). -/
theorem mul_num (p q : Q') : (p * q).num = p.num * q.num := rfl

/-- The denominator of a product is the product of denominators.  NOT `rfl`
(the raw field stores `p.den * q.den - 1`; recovering `den` needs positivity). -/
theorem mul_den (p q : Q') : (p * q).den = p.den * q.den := by
  have h : 0 < p.den * q.den := Nat.mul_pos p.den_pos q.den_pos
  show (p.den * q.den - 1) + 1 = p.den * q.den
  omega

/-- **`Eq`-level commutativity** of `Q'` multiplication. -/
theorem qmul_comm (p q : Q') : p * q = q * p := by
  apply q_ext_den
  · exact Int.mul_comm p.num q.num
  · simp only [mul_den]; exact Nat.mul_comm p.den q.den

/-- **`Eq`-level associativity** of `Q'` multiplication. -/
theorem qmul_assoc (p q r : Q') : (p * q) * r = p * (q * r) := by
  apply q_ext_den
  · show (p.num * q.num) * r.num = p.num * (q.num * r.num)
    exact Int.mul_assoc p.num q.num r.num
  · simp only [mul_den]; exact Nat.mul_assoc p.den q.den r.den

/-- **The genuine arithmetic leaf**: the 4-fold product on `Q'` is invariant
under a CYCLIC reorder as literal `Eq` — the honest cost of an `Eq`-level
`FunctionalEquivariant` witness.  From `qmul_comm`/`qmul_assoc` only. -/
theorem mul4_cyclic (w x y z : Q') :
    ((z * w) * x) * y = ((w * x) * y) * z := by
  rw [qmul_comm z w, qmul_assoc w z x, qmul_comm z x, ← qmul_assoc w x z,
      qmul_assoc (w * x) z y, qmul_comm z y, ← qmul_assoc (w * x) y z]

/-! ## 1. H₄ invariance as a PROVED theorem (not a posited field) -/

/-- **H₄ invariance, PROVED.**  The ISOTROPIC product heat-kernel functional is
`FunctionalEquivariant` under the genuine order-4 automorphism `rot4`
(`rot4 (a,b,c,d) = (d,a,b,c)` cyclically reorders the four equal-weight factors).
This is `IsOS1HypercubicH4` for a non-trivial `ObsHom`, discharged as a theorem —
the anisotropic `wx ≠ wy` case is exactly where equivariance FAILS
(`H4RotationAuto.prodAniso_pos`). -/
theorem prodCharFunc_isotropic_H4_equivariant (w : Q') (hw : (0 : Q') ≤ w) :
    IsOS1HypercubicH4 (prodCharFunc w w hw hw) rot4 := by
  intro a
  obtain ⟨a, b, c, d⟩ := a
  -- E (rot4 (a,b,c,d)) = E (d,a,b,c) = ((t_d·t_a)·t_b)·t_c ;
  -- E (a,b,c,d) = ((t_a·t_b)·t_c)·t_d  with the SAME weight w in every slot.
  exact mul4_cyclic _ _ _ _

/-! ## 2. The pinned-anisotropy + geometric-decay input (Continuum namespace) -/

/-- **O(4)-restoration input.**  Bundles (a) the anisotropy PROVENANCE and its
pinned AF schedule (a `StrongO4Restoration`: non-trivial rotation, L=4 generator,
step-0 coeff pinned to the extractor `anisoDefect`, strict positivity), (b) the
EXPLICIT geometric-decay certificate `(C, ρ)` with `ρ < 1` and the closed
envelope `breakCoeff k ≤ C·ρ^k`, and (c) the H₄ rotation slot `ψ` on the
isotropic functional `H4E` together with its equivariance witness (discharged by
the theorem above in the smart constructor).  Distinct from
`RepTheory.Spin4.O4RestorationInput` (gap-margin object). -/
structure O4RestorationInput : Type 1 where
  /-- Anisotropy provenance + pinned AF decay schedule. -/
  strong       : StrongO4Restoration
  /-- Explicit geometric-envelope amplitude. -/
  C            : Q'
  /-- Explicit geometric-envelope ratio (the AF-proved `½`). -/
  ρ            : Q'
  ρ_nonneg     : (0 : Q') ≤ ρ
  ρ_lt_one     : ρ < 1
  /-- `C` is the step-0 anisotropy (pinned to the extractor via `strong`). -/
  C_pin        : C.eqv (O4RestorationAF.breakCoeff strong.D 0)
  /-- The closed geometric decay of the extracted anisotropy. -/
  decayBound   : ∀ k, O4RestorationAF.breakCoeff strong.D k ≤ C * ρ ^ k
  /-- The isotropic (equivariant) functional carrying the H₄ conjunct. -/
  A4           : ObsAlg
  H4E          : ProbFunctional A4
  ψ            : ObsHom A4 A4
  ψ_nontrivial : ∃ a, ψ.map a ≠ a
  /-- H₄ invariance of the isotropic functional (a THEOREM in the inhabitant). -/
  h4_inv       : IsOS1HypercubicH4 H4E ψ

/-- **Full OS1 predicate**: proved H₄ invariance ∧ the open O(4)-restoration
clause. -/
def IsOS1Full {A : ObsAlg} (E : ProbFunctional A) (ψ : ObsHom A A) : Prop :=
  IsOS1HypercubicH4 E ψ ∧ YMGap.Rubric.ClayScorecard.RubricO4Restoration

/-! ## 3. THE REDUCTION -/

/-- **Statement-layer reduction.**  From an `O4RestorationInput`, both OS1
conjuncts fire: the H₄ conjunct from the input's proved equivariance witness, the
open O(4)-restoration clause from `rubricO4Restoration_of_strong` (decay-to-zero
of the pinned anisotropy).  Fires from structured data (a pinned schedule +
geometric certificate), not a posited defect. -/
theorem o4_restoration_of_input (inp : O4RestorationInput) :
    IsOS1Full inp.H4E inp.ψ :=
  ⟨inp.h4_inv, rubricO4Restoration_of_strong inp.strong⟩

/-! ## 4. Smart constructor / non-vacuity — H₄ conjunct discharged by the theorem -/

/-- Build the input from a `StrongO4Restoration` whose `D` is the proved
geometric schedule (`ρ = ½`, `C = breakCoeff D 0`, envelope `breakCoeff_le_geo`),
and whose H₄ slot is the isotropic `prodCharFunc w w` under `rot4` with
equivariance supplied by `prodCharFunc_isotropic_H4_equivariant`. -/
def o4Input_isotropic (S : StrongO4Restoration) (w : Q') (hw : (0 : Q') ≤ w) :
    O4RestorationInput where
  strong       := S
  C            := O4RestorationAF.breakCoeff S.D 0
  ρ            := HalfPow.half
  ρ_nonneg     := HalfPow.half_nonneg
  ρ_lt_one     := by decide
  C_pin        := Q'.eqv_refl _
  decayBound   := O4RestorationAF.breakCoeff_le_geo S.D
  A4           := prodCharAlg4
  H4E          := prodCharFunc w w hw hw
  ψ            := rot4
  ψ_nontrivial := rot4_nontrivial
  h4_inv       := prodCharFunc_isotropic_H4_equivariant w hw

/-- **Non-vacuity capstone**: full OS1 fired from the concrete SU(2) heat-kernel
strong certificate + the isotropic H₄ functional — genuine non-trivial `ψ = rot4`,
genuine positive extracted anisotropy, genuine geometric decay. -/
theorem isOS1Full_concrete :
    IsOS1Full (prodCharFunc wX wX hwX hwX) rot4 :=
  o4_restoration_of_input
    (o4Input_isotropic O4ClauseStrength.strongO4_charAlg wX hwX)

/-! ## Axiom-dependency gates (AGENTS.md Rules 1, 8) -/

#print axioms mul4_cyclic
#print axioms prodCharFunc_isotropic_H4_equivariant
#print axioms o4_restoration_of_input
#print axioms o4Input_isotropic
#print axioms isOS1Full_concrete

end YMGap.Continuum.O4RestorationReduction
