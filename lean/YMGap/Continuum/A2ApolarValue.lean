/-
**Track A2 — the 6j VALUE from the rep category: the dim-weighted Racah kernel
as a RATIO OF APOLAR NORMS of the transvectant Clebsch–Gordan channels.**

`PentagonRelation.PentagonNumericCore` demands the fractional value
`P = dim(e)·dim(f)·{6j}² = 1/4` at the smallest SU(2) tetrahedron.  Until now it
was inhabited by the constant shape witness (`numericShapeWitness`, `P ≡ 1/4`)
and by the factorial kernel (`SixJKernel.racahKernelQ`, a ratio of factorials).
This module computes the SAME value `1/4` from the **binary-forms invariant
theory**: the SU(2)-invariant apolar pairing `apolarHalf` (the top transvectant,
Cayley's apolarity, `TransvectantCG`) is the `ε`-form on spin ½; the
dim-weighted 6j² is the square of the recoupling coefficient, and that square is
a ratio of the **apolar norms of the two coupling-tree intertwiners**:

    P  =  ⟨A,B⟩² / (⟨A,A⟩·⟨B,B⟩)

where `A`, `B` are the two three-leg coupling trees of the recoupling square
(couple `(12)→e→(·3)` vs `(23)→f→(1·)`), and `⟨·,·⟩` is the invariant apolar
net pairing (all legs closed by `ε`-caps).  We compute, entirely from
`apolarHalf`, `⟨A,A⟩ = ⟨B,B⟩ = 12`, `⟨A,B⟩ = −6`, so
`P = 36/144 = 1/4` — the genuine 6j value, NOT the constant witness, and it
matches the factorial kernel `SixJKernel.racahKernelQ` where checkable
(`sixj_value_is_apolar_norm_ratio`).

# Why this is `Q'`-legal (no √)

The signed Wigner `{6j}` is irrational.  But the recoupling coefficient here is
`⟨A,B⟩/√(⟨A,A⟩⟨B,B⟩)`, and its SQUARE — the dim-weighted Racah kernel — is a
ratio of integer apolar norms (`ε` has integer entries `0,±1`, so every net
pairing is an integer).  The whole computation is exact `Q'` arithmetic.  We
state the ratio in the division-free cross-multiplied form
`⟨A,B⟩² = P·⟨A,A⟩·⟨B,B⟩`, so no `Q'` reciprocal is needed.

# Constructive contract (AGENTS.md Rules 1/6/8)

Mathlib-free; `Q'`/`Nat` core only.  No `Real`, no `Classical.*`, no
`native_decide` (only `decide` on decidable `Q'` facts), no `sorry`.  `eps`,
`treeA/B`, `netPair` are `Type`-level computable data; the apolar norms are
kernel-checked `Q'` facts; the value `1/4` is the proved apolar ratio.
`#print axioms` gated to `propext`/`Quot.sound`.
-/

import YMGap.Continuum.TransvectantCG
import YMGap.Continuum.SixJKernel

namespace YMGap.Continuum.A2ApolarValue

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.PentagonRelation
open YMGap.Continuum.SixJKernel
open YMGap.Continuum.RacahInhabit

/-! ## 1. The apolar (ε) tensor, DEFINED from the transvectant apolar pairing. -/

/-- **The apolar (`ε`) tensor on spin ½**, defined as the top-transvectant
invariant pairing `apolarHalf` of the basis monomials.  This is the genuine
rep-category object — the `SU(2)`-invariant symplectic form on `V_½`. -/
def eps (i j : Nat) : Q' := apolarHalf (mono i) (mono j)

/-- The apolar tensor takes the `ε` values `⟨e₀,e₁⟩ = −1`, `⟨e₁,e₀⟩ = 1`, and
`⟨e₀,e₀⟩ = ⟨e₁,e₁⟩ = 0` — verbatim from `apolarHalf_basis`. -/
theorem eps_values :
    (eps 0 0).eqv 0 ∧ (eps 1 1).eqv 0 ∧
    (eps 0 1).eqv (Q'.ofInt (-1)) ∧ (eps 1 0).eqv 1 :=
  apolarHalf_basis

/-- **The Penrose binor loop value** `tr(ε·εᵀ) = Σ_{i,j} ε_{ij} ε_{ji} = −2`,
computed from the apolar tensor.  (The spin-½ loop is `−(dim) = −2`.) -/
def apolarLoop : Q' := finSum (fun i => finSum (fun j => eps i j * eps j i) 2) 2

theorem apolarLoop_eq : apolarLoop.eqv (Q'.ofInt (-2)) := by decide

/-! ## 2. The two coupling-tree intertwiners of the recoupling square. -/

/-- Kronecker delta on `Nat`. -/
def kron (a b : Nat) : Q' := if a = b then 1 else 0

/-- **Coupling tree `A`**: couple legs `(1,2)` to the internal spin-1 line `e`
via the symmetric intertwiner, then couple `e` with leg `3` to the total spin-½
output `t`.  Realized as the `ε`-contraction
`A_{ijk}^{t} = ε_{jk} δ_i^t + ε_{ik} δ_j^t` (the unique `1⊗½→½` intertwiner,
symmetrized over the two `e`-strands). -/
def treeA (i j k t : Nat) : Q' := eps j k * kron i t + eps i k * kron j t

/-- **Coupling tree `B`**: couple legs `(2,3)` to the internal spin-1 line `f`,
then couple leg `1` with `f` to the total `t`:
`B_{ijk}^{t} = ε_{ki} δ_j^t + ε_{ji} δ_k^t`. -/
def treeB (i j k t : Nat) : Q' := eps k i * kron j t + eps j i * kron k t

/-- The apolar cap (the co-form dual to `ε`): `capE_{ij} = ε_{ji}`. -/
def capE (i j : Nat) : Q' := eps j i

/-- **The invariant apolar net pairing** of two four-leg tensors: close every
one of the four legs (the three externals `i,j,k` and the total `t`) with an
`ε`-cap.  This is the closed spin-network evaluation. -/
def netPair (X Y : Nat → Nat → Nat → Nat → Q') : Q' :=
  finSum (fun i => finSum (fun j => finSum (fun k => finSum (fun t =>
    finSum (fun i' => finSum (fun j' => finSum (fun k' => finSum (fun t' =>
      X i j k t * Y i' j' k' t' * capE i i' * capE j j' * capE k k' * capE t t')
        2) 2) 2) 2) 2) 2) 2) 2

/-- The apolar norm `⟨A,A⟩` of coupling tree `A`. -/
def normAA : Q' := netPair treeA treeA

/-- The apolar norm `⟨B,B⟩` of coupling tree `B`. -/
def normBB : Q' := netPair treeB treeB

/-- The apolar overlap `⟨A,B⟩` (the tetrahedral net of the recoupling square). -/
def crossAB : Q' := netPair treeA treeB

/-! ## 3. The apolar norms (kernel-checked from `apolarHalf`). -/

theorem normAA_eq : normAA.eqv (Q'.ofNat 12) := by decide
theorem normBB_eq : normBB.eqv (Q'.ofNat 12) := by decide
theorem crossAB_eq : crossAB.eqv (Q'.ofInt (-6)) := by decide

/-- **The overlap is genuinely nonzero** (`⟨A,B⟩ = −6 ≠ 0`): the two coupling
trees are NOT orthogonal, so the recoupling coefficient — and hence the 6j value
— is nontrivial.  This is what rules out a degenerate/shape witness. -/
theorem crossAB_ne_zero : ¬ crossAB.eqv 0 := by decide

/-! ## 4. The dim-weighted 6j² as the apolar norm ratio: `P = ⟨A,B⟩²/(⟨A,A⟩⟨B,B⟩) = 1/4`.

Stated division-free (cross-multiplied): `⟨A,B⟩² = P·⟨A,A⟩·⟨B,B⟩` with
`P = 1/4`.  Since `⟨A,B⟩ = −6` and `⟨A,A⟩⟨B,B⟩ = 144`, this reads
`36 = (1/4)·144 = 36`. -/

/-- **THE 6j VALUE AS AN APOLAR NORM RATIO (`decide`).**  The square of the
recoupling coefficient — the dim-weighted Racah kernel `P = dim(e)dim(f){6j}²` —
is the ratio of apolar norms `⟨A,B⟩²/(⟨A,A⟩·⟨B,B⟩)`, and it equals `1/4`:

    ⟨A,B⟩²  ≃  (1/4) · ⟨A,A⟩ · ⟨B,B⟩.

Every quantity here is a `Q'` net pairing of the transvectant apolar form
`apolarHalf` — this is the genuine 6j value computed from binary-forms invariant
theory, NOT the constant `1/4` shape witness. -/
theorem apolar_dimweighted_6j_sq :
    (crossAB * crossAB).eqv (oneQuarter * (normAA * normBB)) := by decide

/-- The apolar norm ratio is nonnegative (`⟨A,B⟩² ≥ 0` — a square). -/
theorem apolar_ratio_nonneg : (0 : Q') ≤ crossAB * crossAB := qMulSelf_nonneg crossAB

/-! ## 5. The bridge: the physical factorial 6j² kernel value IS the apolar ratio.

`SixJKernel.racahKernelQ` computes `P = dim(e)dim(f){6j}²` from FACTORIALS (the
Racah `t`-sum).  Here we prove its value at the smallest tetrahedron coincides
with the APOLAR norm ratio just computed — two independent routes (Racah
factorials vs. binary-forms apolar contractions) to the same rational `1/4`. -/

/-- **`sixj_value_is_apolar_norm_ratio` (`decide`).**  The physical factorial
Racah kernel value at the smallest tetrahedron equals the apolar norm ratio:

    racahKernelQ(smallestTetra) · ⟨A,A⟩ · ⟨B,B⟩  ≃  ⟨A,B⟩².

i.e. `P_factorial = ⟨A,B⟩²/(⟨A,A⟩⟨B,B⟩)` — the factorial 6j² and the apolar-norm
6j² agree exactly.  This certifies the `PentagonNumericCore` value `1/4` is the
genuine rep-category apolar ratio, matching the physical kernel where checkable. -/
theorem sixj_value_is_apolar_norm_ratio :
    (racahKernelQ smallestTetra * (normAA * normBB)).eqv (crossAB * crossAB) := by decide

/-! ## 6. The `PentagonNumericCore` inhabitant, value FROM the apolar rep theory. -/

/-- **`racahApolarCore` — a `PentagonNumericCore` whose fractional value `1/4` is
the apolar norm ratio of the transvectant coupling trees.**  The kernel is the
faithful, label-varying physical Racah kernel `racahKernelQ` (so it is NOT the
constant shape witness and matches `racahKernel6` at every label); its pinned
value `1/4` at the smallest tetrahedron is certified — by
`sixj_value_is_apolar_norm_ratio` together with `apolar_dimweighted_6j_sq` — to
equal the binary-forms apolar norm ratio `⟨A,B⟩²/(⟨A,A⟩⟨B,B⟩)` built from
`apolarHalf`.  This is the 6j VALUE computed from the rep category. -/
def racahApolarCore : PentagonNumericCore where
  racahKernel := racahKernelQ
  nonneg := racahKernelQ_nonneg
  smallest_value := racahKernelQ_smallest

/-- **The apolar core's pinned value is genuinely fractional** (`1/4 ∉ {0,1}`):
the apolar norm ratio is neither the trivial `0` nor `1` channel, so it is real
Level-2 associator content, refuting every permutation surrogate. -/
theorem racahApolarCore_fractional :
    ¬ (racahApolarCore.racahKernel smallestTetra).eqv 0 ∧
    ¬ (racahApolarCore.racahKernel smallestTetra).eqv 1 :=
  racahKernelQ_smallest_fractional

/-- **The apolar core defeats every permutation surrogate.**  Being a genuine
`PentagonNumericCore` with the fractional apolar value, it disagrees with the
0/1 permutation kernel at the smallest tetrahedron. -/
theorem racahApolarCore_not_perm :
    ¬ (racahApolarCore.racahKernel smallestTetra).eqv (racahPerm smallestTetra) :=
  pentagonNumericCore_not_perm racahApolarCore

/-! ## 7. Documentation: PROVED (AGENTS.md Rule 6)

PROVED (genuine, axiom-clean):

  * `eps` (+ `eps_values`) — the apolar/`ε` tensor DEFINED from `apolarHalf`;
  * `apolarLoop_eq` — the Penrose binor loop `−2` from the apolar tensor;
  * `treeA`/`treeB`/`netPair`, `normAA_eq`/`normBB_eq`/`crossAB_eq` — the two
    coupling-tree intertwiners and their apolar norms `⟨A,A⟩ = ⟨B,B⟩ = 12`,
    `⟨A,B⟩ = −6`, all kernel-checked from `apolarHalf`;
  * `crossAB_ne_zero` — the overlap is genuinely nonzero (nondegenerate);
  * `apolar_dimweighted_6j_sq` — **the 6j value as the apolar norm ratio**
    `⟨A,B⟩² = (1/4)·⟨A,A⟩·⟨B,B⟩` (division-free), the genuine `1/4`;
  * `sixj_value_is_apolar_norm_ratio` — the physical factorial kernel value
    coincides with the apolar ratio (two independent routes agree);
  * `racahApolarCore` — a `PentagonNumericCore` inhabitant whose value is the
    rep-category apolar norm ratio (varies across labels; NOT the constant
    witness), with `racahApolarCore_fractional` / `racahApolarCore_not_perm`.

This module computes the smallest-tetrahedron 6j VALUE `1/4` from binary-forms
invariant theory (the apolar pairing `apolarHalf`).  It is NOT the signed
associator, NOT the general pentagon, and NOT a Yang–Mills mass gap. -/

end YMGap.Continuum.A2ApolarValue

#print axioms YMGap.Continuum.A2ApolarValue.apolarLoop_eq
#print axioms YMGap.Continuum.A2ApolarValue.normAA_eq
#print axioms YMGap.Continuum.A2ApolarValue.normBB_eq
#print axioms YMGap.Continuum.A2ApolarValue.crossAB_eq
#print axioms YMGap.Continuum.A2ApolarValue.crossAB_ne_zero
#print axioms YMGap.Continuum.A2ApolarValue.apolar_dimweighted_6j_sq
#print axioms YMGap.Continuum.A2ApolarValue.sixj_value_is_apolar_norm_ratio
#print axioms YMGap.Continuum.A2ApolarValue.racahApolarCore
#print axioms YMGap.Continuum.A2ApolarValue.racahApolarCore_fractional
#print axioms YMGap.Continuum.A2ApolarValue.racahApolarCore_not_perm
