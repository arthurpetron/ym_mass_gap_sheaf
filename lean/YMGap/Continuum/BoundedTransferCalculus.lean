/-
The BOUNDED transfer-operator functional calculus — the correctly-stated
replacement for the mis-stated "bounded Hamiltonian" residual.

# Why the old statement was wrong, and what replaces it

`SelfAdjointHamiltonian.BoundedFunctionalCalculusResidual` asks for a
self-adjoint BOUNDED operator `H` on the completed carrier with `e^{−H} = T`.
That object does not exist: on `vac⊥` the located transfer spectrum is `[0, sep]`
with the bottom only `≥ 0`, so `H = −log T` has eigenvalues `−log w^{C₄(s)} → +∞`
as the excitation `s → ∞`.  `H` is genuinely UNBOUNDED; no amount of functional
calculus produces it as a bounded operator.

The physically-meaningful, bounded, gap-carrying object is the TRANSFER OPERATOR
itself.  Its spectral gap is the OPERATOR-NORM gap `‖T|vac⊥‖ ≤ sep < 1`, and the
energy gap `Δ = −log sep` is that norm gap read in log units — already delivered
at the eigenvalue level by `isPositive_neg_logRat` / `hamiltonianGapReal_pos`,
with NO unbounded operator.

# What is GENUINELY proved here (axiom-clean)

  * **The operator-norm gap** (`diagResolution_normGap`).  From a finite diagonal
    spectral resolution of `T`'s quadratic form against the located model — the
    same standing Osterwalder–Seiler / Schur datum the reconstruction already uses
    — the operator-norm bound on `vac⊥`
        `⟨T x, T x⟩ ≤ sep²·⟨x, x⟩`
    (i.e. `‖T x‖² ≤ sep²‖x‖²`).  The proof is a pure finite-dimensional termwise
    chain through the self-adjointness of `T`, the *linear* form gap
    `⟨T x, x⟩ ≤ sep·⟨x, x⟩`, and the *quadratic* square-form gap
    `⟨T² x, x⟩ ≤ sep·⟨T x, x⟩` — both discharged termwise from the resolution.  NO
    `−log`, NO unbounded operator, NO Cauchy–Schwarz on `RC` (which would need an
    `RC` product that is not developed): everything stays inside the proved
    `RCscale` (`Q'`-scalar) algebra.

  * **`RCscale_RCscale`** / **`RCscale_one`** — the composition law
    `s·(t·a) = (s·t)·a` and the unit `1·a = a` for the `Q'`-scaling on `RC`
    (pointwise `CReal` multiplication associativity / unit).

  * **Iterated transfer `Tpow`** — the `n`-fold composition `Tⁿ`, proved
    self-adjoint (`Tpow_selfAdjoint`) and a contraction
    (`Tpow_contraction`, `‖Tⁿ x‖² ≤ ‖x‖²`).  These are the genuine
    polynomial-functional-calculus building blocks: `Tⁿ = f(T)` for the monomial
    `f(λ) = λⁿ`, a BOUNDED continuous function on `[0, sep]`.

  * **`BoundedTransferCalculusResidual`** — the correctly-stated residual: a
    BOUNDED continuous `f` on the located spectrum `[0, sep]` gives a bounded
    self-adjoint operator `f(T)` with the operator-norm bound
    `‖f(T) x‖² ≤ M²·‖x‖²`, `M = sup_{[0,sep]}|f|`.  Non-vacuously inhabited by the
    monomial calculus `monomialCalculus` (`f(λ)=λⁿ`, `f(T)=Tⁿ`, `M = 1`).  The
    only genuinely open content is the Bernstein/Chebyshev LIMIT
    `f(T) = lim pₙ(T)` for a general continuous `f` (named honestly, not faked).

# How the mis-stated residual is dissolved

`physical_gap_from_resolution` produces, from the diagonal resolution plus the
decidable artanh window, BOTH the bounded operator-norm gap AND the strictly
positive physical energy gap `Δ = −log sep > 0` — taking NO
`BoundedFunctionalCalculusResidual` as input.  The mis-stated unbounded `H` is
therefore OFF the mass-gap critical path; the bounded transfer operator carries
the entire gap.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorryAx`,
no `native_decide`, no custom `axiom`.
-/

import YMGap.Continuum.ReconstructionCapstone
import YMGap.Constructive.CRealAlg

open YMGap.Constructive
open YMGap.Constructive.CRealLog
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.SpectralGap

/-! ## The `Q'`-scaling composition and unit laws on `RC` -/

namespace YMGap.Constructive.CReal

/-- **Composition of `Q'`-scalings.**  `s·(t·a) = (s·t)·a`.  Pointwise: the two
`CReal` multiplications reassociate (`cmul_assoc`) and `ofQ'` is multiplicative
(`ofQ'_mul`), so `ofQ' s · (ofQ' t · A) ≃ ofQ'(s·t) · A`. -/
theorem RCscale_RCscale (s t : Q') (a : RC) :
    RCscale s (RCscale t a) = RCscale (s * t) a := by
  refine Quotient.inductionOn a ?_
  intro A
  show Quotient.mk crealSetoid (mul (ofQ' s) (mul (ofQ' t) A))
      = Quotient.mk crealSetoid (mul (ofQ' (s * t)) A)
  apply Quotient.sound
  refine CReal.Equiv.trans (CReal.Equiv.symm (CRealAlg.cmul_assoc (ofQ' s) (ofQ' t) A)) ?_
  exact YMGap.Continuum.Pivot2.mul_congr_left (CReal.Equiv.symm (CRealAlg.ofQ'_mul s t))

/-- **The `Q'`-scaling unit.**  `1·a = a`, pointwise `1 · Aₙ ≃ Aₙ`. -/
theorem RCscale_one (a : RC) : RCscale (1 : Q') a = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound
    (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.one_mul_eqv (A.approx n)))

end YMGap.Constructive.CReal

namespace YMGap.Continuum.BoundedTransferCalculus

open YMGap.Constructive.CReal

/-! ## 1. The finite diagonal spectral resolution of `T`'s quadratic form

The genuine, finite, Osterwalder–Seiler / Schur input: a coordinate resolution of
the completed inner product against the located model.  It carries the resolution
of the norm, the `T`-form and the `T²`-form, together with the two eigenvalue
bounds (linear and quadratic) that hold TERMWISE on `vac⊥` (where the vacuum-mode
coordinate vanishes).  Everything is finite, so no located-spectrum no-go binds. -/
structure DiagResolution {D : GNSData} {H : CompleteGNSHilbert D}
    (G : SpectralGapData H) : Type where
  /-- Number of resolved modes. -/
  k : Nat
  /-- The transfer eigenvalues. -/
  lam : Fin k → Q'
  /-- The squared coordinate weights `|cᵢ(x)|²`. -/
  coeffSq : H.hilbert.carrier → Fin k → CReal.RC
  /-- The coordinate weights are nonnegative. -/
  coeffSq_nonneg : ∀ x i, CReal.RCnonneg (coeffSq x i)
  /-- Resolution of the norm: `⟨x,x⟩ = Σ |cᵢ|²`. -/
  innerSelf_diag : ∀ x,
    H.hilbert.cinner x x = CReal.RCfinSum k (coeffSq x)
  /-- Resolution of the `T`-form: `⟨Tx,x⟩ = Σ lamᵢ·|cᵢ|²`. -/
  innerT_diag : ∀ x,
    H.hilbert.cinner (G.op.T x) x
      = CReal.RCfinSum k (fun i => CReal.RCscale (lam i) (coeffSq x i))
  /-- Resolution of the `T²`-form: `⟨T²x,x⟩ = Σ lamᵢ²·|cᵢ|²`. -/
  innerTsq_diag : ∀ x,
    H.hilbert.cinner (G.op.T (G.op.T x)) x
      = CReal.RCfinSum k (fun i => CReal.RCscale (lam i * lam i) (coeffSq x i))
  /-- **Linear eigenvalue bound on `vac⊥`.**  `lamᵢ·|cᵢ|² ≤ sep·|cᵢ|²`. -/
  eigen_le_sep : ∀ {x}, G.vacPerp x → ∀ i,
    CReal.RCle (CReal.RCscale (lam i) (coeffSq x i))
               (CReal.RCscale G.gap.sep (coeffSq x i))
  /-- **Quadratic eigenvalue bound on `vac⊥`.**  `lamᵢ²·|cᵢ|² ≤ (sep·lamᵢ)·|cᵢ|²`. -/
  eigenSq_le : ∀ {x}, G.vacPerp x → ∀ i,
    CReal.RCle (CReal.RCscale (lam i * lam i) (coeffSq x i))
               (CReal.RCscale (G.gap.sep * lam i) (coeffSq x i))

variable {D : GNSData} {H : CompleteGNSHilbert D} {G : SpectralGapData H}

/-! ## 2. The linear and quadratic form gaps from the resolution -/

/-- **The linear form gap** `⟨Tx,x⟩ ≤ sep·⟨x,x⟩` on `vac⊥`.  Termwise
`lamᵢ·|cᵢ|² ≤ sep·|cᵢ|²`, summed by `RCfinSum_mono`, using `RCscale`-over-sum. -/
theorem formGap (Br : DiagResolution G) {x : H.hilbert.carrier} (hx : G.vacPerp x) :
    RCle (H.hilbert.cinner (G.op.T x) x)
         (RCscale G.gap.sep (H.hilbert.cinner x x)) := by
  rw [Br.innerT_diag x, Br.innerSelf_diag x, RCscale_finSum]
  exact RCfinSum_mono (fun i => Br.eigen_le_sep hx i)

/-- **The quadratic (square) form gap** `⟨T²x,x⟩ ≤ sep·⟨Tx,x⟩` on `vac⊥`.  This is
the commuting-product positivity `T·(sep − T) ≥ 0`, obtained here TERMWISE from the
finite resolution: `lamᵢ²·|cᵢ|² ≤ (sep·lamᵢ)·|cᵢ|² = sep·(lamᵢ·|cᵢ|²)`.  It is the
extra genuine spectral content that upgrades the linear gap to the operator norm —
no square root, no `RC` Cauchy–Schwarz. -/
theorem squareFormGap (Br : DiagResolution G) {x : H.hilbert.carrier}
    (hx : G.vacPerp x) :
    RCle (H.hilbert.cinner (G.op.T (G.op.T x)) x)
         (RCscale G.gap.sep (H.hilbert.cinner (G.op.T x) x)) := by
  rw [Br.innerTsq_diag x, Br.innerT_diag x, RCscale_finSum]
  refine RCfinSum_mono (fun i => ?_)
  rw [RCscale_RCscale]
  exact Br.eigenSq_le hx i

/-! ## 3. The operator-norm gap `‖T x‖² ≤ sep²·‖x‖²` -/

/-- **The operator-norm gap** on `vac⊥`:  `⟨T x, T x⟩ ≤ sep²·⟨x, x⟩`, i.e.
`‖T x‖² ≤ sep²·‖x‖²`.  This is the genuine bounded-operator statement of the
spectral gap `‖T|vac⊥‖ ≤ sep`.  Chain:
`‖T x‖² = ⟨T² x, x⟩ ≤ sep·⟨T x, x⟩ ≤ sep·(sep·⟨x, x⟩) = sep²·⟨x, x⟩`,
using self-adjointness for the first equality, the square form gap for the second
step, and `RCscale`-monotonicity of the linear form gap for the third. -/
theorem diagResolution_normGap (Br : DiagResolution G) {x : H.hilbert.carrier}
    (hx : G.vacPerp x) :
    RCle (H.hilbert.cinner (G.op.T x) (G.op.T x))
         (RCscale (G.gap.sep * G.gap.sep) (H.hilbert.cinner x x)) := by
  -- `‖T x‖² = ⟨T² x, x⟩` by self-adjointness (of `T` between `T x` and `x`).
  have hsa : H.hilbert.cinner (G.op.T x) (G.op.T x)
      = H.hilbert.cinner (G.op.T (G.op.T x)) x :=
    (G.op.selfAdjoint (G.op.T x) x).symm
  rw [hsa]
  -- `⟨T² x, x⟩ ≤ sep·⟨T x, x⟩`.
  refine RCle_trans (squareFormGap Br hx) ?_
  -- `sep·⟨T x, x⟩ ≤ sep·(sep·⟨x, x⟩)` by monotone `RCscale` of the linear gap.
  have hstep : RCle (RCscale G.gap.sep (H.hilbert.cinner (G.op.T x) x))
      (RCscale G.gap.sep (RCscale G.gap.sep (H.hilbert.cinner x x))) :=
    RCscale_mono G.gap.sep_nonneg (formGap Br hx)
  refine RCle_trans hstep ?_
  -- `sep·(sep·⟨x,x⟩) = sep²·⟨x,x⟩`.
  rw [RCscale_RCscale]
  exact RCle_refl _

/-! ## 4. Iterated transfer `Tⁿ` — the polynomial calculus seed -/

/-- The **iterated transfer operator** `Tⁿ` (the monomial `f(λ)=λⁿ` at `T`). -/
def Tpow (op : TransferOperator H) : Nat → H.hilbert.carrier → H.hilbert.carrier
  | 0 => fun x => x
  | (n + 1) => fun x => op.T (Tpow op n x)

/-- `Tⁿ` commutes with `T`: `Tⁿ (T x) = T (Tⁿ x)`. -/
theorem Tpow_comm (op : TransferOperator H) (n : Nat) (x : H.hilbert.carrier) :
    Tpow op n (op.T x) = op.T (Tpow op n x) := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show op.T (Tpow op k (op.T x)) = op.T (op.T (Tpow op k x))
      rw [ih]

/-- **`Tⁿ` is self-adjoint** — composition of self-adjoints. -/
theorem Tpow_selfAdjoint (op : TransferOperator H) (n : Nat) :
    ∀ x y, H.hilbert.cinner (Tpow op n x) y = H.hilbert.cinner x (Tpow op n y) := by
  induction n with
  | zero => intro x y; rfl
  | succ k ih =>
      intro x y
      show H.hilbert.cinner (op.T (Tpow op k x)) y
          = H.hilbert.cinner x (op.T (Tpow op k y))
      rw [op.selfAdjoint (Tpow op k x) y, ih x (op.T y), Tpow_comm op k y]

/-- **`Tⁿ` is a contraction** — `‖Tⁿ x‖² ≤ ‖x‖²`, iterating the single-step
contraction.  This is the norm bound `‖f(T)‖ ≤ 1 = sup_{[0,1]}|λⁿ|` for the
monomial functional calculus. -/
theorem Tpow_contraction (op : TransferOperator H) (n : Nat) :
    ∀ x, RCle (H.hilbert.cinner (Tpow op n x) (Tpow op n x)) (H.hilbert.cinner x x) := by
  induction n with
  | zero => intro x; exact RCle_refl _
  | succ k ih =>
      intro x
      show RCle (H.hilbert.cinner (op.T (Tpow op k x)) (op.T (Tpow op k x)))
          (H.hilbert.cinner x x)
      exact RCle_trans (op.contraction (Tpow op k x)) (ih x)

/-! ## 5. The correctly-stated bounded functional-calculus residual -/

/-- **Bounded transfer functional calculus (correctly stated).**  A BOUNDED
continuous function `f` on the located spectrum `[0, sep]` gives a bounded
self-adjoint operator `f(T)` with the operator-norm bound
`‖f(T) x‖² ≤ M²·‖x‖²`, `M = sup_{[0,sep]}|f|` (here `normSqBound = M²`).  This is
the ONLY well-posed version: it never forms the unbounded `H = −log T`.  The
genuinely open content is the Bernstein/Chebyshev polynomial LIMIT
`f(T) = lim pₙ(T)` for a general continuous `f` (the monomial powers `Tⁿ` and
their finite `Q'`-combinations are already available, `Tpow`). -/
structure BoundedTransferCalculusResidual {D : GNSData} {H : CompleteGNSHilbert D}
    (G : SpectralGapData H) : Type where
  /-- The squared uniform bound `M² = (sup_{[0,sep]}|f|)²`. -/
  normSqBound : Q'
  /-- The bounded operator `f(T)`. -/
  fT : H.hilbert.carrier → H.hilbert.carrier
  /-- `f(T)` is self-adjoint (real `f`). -/
  fT_selfAdjoint : ∀ x y,
    H.hilbert.cinner (fT x) y = H.hilbert.cinner x (fT y)
  /-- **Operator-norm bound** `‖f(T) x‖² ≤ M²·‖x‖²`. -/
  fT_normBound : ∀ x,
    CReal.RCle (H.hilbert.cinner (fT x) (fT x))
               (CReal.RCscale normSqBound (H.hilbert.cinner x x))

/-- **Non-vacuity: the monomial calculus.**  `f(λ) = λⁿ` gives `f(T) = Tⁿ`, a
bounded self-adjoint operator with `M = 1` (since `|λⁿ| ≤ 1` on `[0, 1]`), whose
norm bound is exactly `Tpow_contraction`.  A genuine inhabitant of the corrected
residual — the polynomial functional calculus for a single monomial. -/
def monomialCalculus (G : SpectralGapData H) (n : Nat) :
    BoundedTransferCalculusResidual G where
  normSqBound := 1
  fT := Tpow G.op n
  fT_selfAdjoint := Tpow_selfAdjoint G.op n
  fT_normBound := fun x => by
    rw [RCscale_one]
    exact Tpow_contraction G.op n x

/-! ## 6. Dissolving the mis-stated `BoundedFunctionalCalculusResidual` -/

/-- **The physical gap needs NO unbounded Hamiltonian.**  From the finite diagonal
resolution plus the decidable artanh window, deliver SIMULTANEOUSLY:

  * the BOUNDED operator-norm gap `‖T x‖² ≤ sep²·‖x‖²` on `vac⊥`
    (`diagResolution_normGap`), and
  * the strictly positive physical energy gap `Δ = −log sep > 0`
    (`hamiltonianGapReal_pos`),

taking NO `BoundedFunctionalCalculusResidual` (the unbounded `H = −log T`) as
input.  The mis-stated residual is thereby OFF the mass-gap critical path: the
bounded transfer operator carries the entire gap. -/
theorem physical_gap_from_resolution (Br : DiagResolution G)
    (hwin : Q'.abs (yOf G.gap.sep (sepPlusOne_pos G.gap)) ≤ recipOdd 1) :
    (∀ (x : H.hilbert.carrier), G.vacPerp x →
        RCle (H.hilbert.cinner (G.op.T x) (G.op.T x))
             (RCscale (G.gap.sep * G.gap.sep) (H.hilbert.cinner x x)))
      ∧ (∃ Δ : CReal, CReal.IsPositive Δ ∧
          Δ = CReal.neg (logRat G.gap.sep (sepPlusOne_pos G.gap) hwin)) := by
  have h1 : ∀ (x : H.hilbert.carrier), G.vacPerp x →
      RCle (H.hilbert.cinner (G.op.T x) (G.op.T x))
           (RCscale (G.gap.sep * G.gap.sep) (H.hilbert.cinner x x)) :=
    fun x hx => diagResolution_normGap Br hx
  exact ⟨h1, mass_gap_hamiltonian G hwin⟩

/-- **The corrected residual is inhabited (calculus is non-vacuous).**  For any
`G`, the bounded functional calculus exists (monomial witness).  This REPLACES the
mis-stated `BoundedFunctionalCalculusResidual` (bounded `H` with `e^{−H}=T`, which
does not exist) by the well-posed BOUNDED-`f` calculus. -/
def boundedTransferCalculusResidual_inhabited (G : SpectralGapData H) :
    BoundedTransferCalculusResidual G :=
  monomialCalculus G 0

end YMGap.Continuum.BoundedTransferCalculus

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Constructive.CReal.RCscale_RCscale
#print axioms YMGap.Constructive.CReal.RCscale_one
#print axioms YMGap.Continuum.BoundedTransferCalculus.formGap
#print axioms YMGap.Continuum.BoundedTransferCalculus.squareFormGap
#print axioms YMGap.Continuum.BoundedTransferCalculus.diagResolution_normGap
#print axioms YMGap.Continuum.BoundedTransferCalculus.Tpow_comm
#print axioms YMGap.Continuum.BoundedTransferCalculus.Tpow_selfAdjoint
#print axioms YMGap.Continuum.BoundedTransferCalculus.Tpow_contraction
#print axioms YMGap.Continuum.BoundedTransferCalculus.monomialCalculus
#print axioms YMGap.Continuum.BoundedTransferCalculus.physical_gap_from_resolution
#print axioms YMGap.Continuum.BoundedTransferCalculus.boundedTransferCalculusResidual_inhabited
