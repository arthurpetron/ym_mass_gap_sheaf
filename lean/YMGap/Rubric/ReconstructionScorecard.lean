/-
The RECONSTRUCTION SCORECARD — a machine-checked, three-way honesty ledger for
the finite-volume Wilson GNS reconstruction of the Yang–Mills mass gap.

# What this module is

The continuum reconstruction program produced, over several rounds, a family of
genuinely-discharged deliverables about the CONCRETE excited-tower transfer
object.  This module is the single downstream CONSUMER that records, in one
place, exactly WHICH of those deliverables are:

  * PROVED-UNCONDITIONAL (at fixed lattice spacing) — bundled as
    `ReconstructionProvedLine`, whose every field is an ACTUAL discharge term
    (never `True`, never a vacuous predicate);
  * PROVED-MODULO named honest residuals — the operator-form gap (Residual A =
    the diagonal Schur / Peter–Weyl identities) and the full 5-field GNS
    reconstruction (Residual A + Residual B = the bounded functional-calculus
    Hamiltonian), recorded as REDUCTIONS (`operatorFormGap_of_schur`,
    `full_reconstruction_of_inputs`) whose hypotheses are the residuals;
  * OPEN (deliberately uninhabited) — the bounded self-adjoint `H` with
    `e^{−H}=T` (Residual B), the genuine dimensionless physical margin, the
    physical `O(4)` isotropization running, and the continuum Minlos measure.

# The key upgrade recorded here

`ReconstructionProvedLine.spectrumInfLowerBound` closes the two monotonicity
premises `Y`/`A` that the reconstruction capstone still exposes: the genuine
constructed witnesses for `YOfMonotone` and `ArtanhMonotoneWindow` are fed in,
so the located spectrum-infimum LOWER bound `Δ = −log sep ≤ E_i` is
UNCONDITIONAL here (not gated on `Y`/`A`).

# Three-way ledger and the two split-honesty caveats

  * The uniform-in-coupling deliverable carried by the proved line is the
    SURVIVAL-PRODUCT SURROGATE `∏(1−δ_ren)`; it is DISTINCT from the genuine
    dimensionless margin `Δ_k = m_lat(a_k)/a_k` (the `TrueMarginRecursion`
    token, left OPEN).  The two must never be collapsed.
  * The proved `O(4)` cell is the INVERTIBLE ORDER-4 automorphism `rot4` on the
    4-directed-edge product character algebra.  The PHYSICAL `O(4)`
    isotropization running (the `betaDrop`-sign / anisotropy-decay content of
    `CouplingRunning`) is a SEPARATE OPEN cell; only a MODEL anisotropy-decay
    fires the classical clause, not the physical running.

# Honesty ledger

  * PROVED-UNCONDITIONAL (fixed spacing): mass gap `Δ = −log sep > 0`; GNS
    vector-scaling; located spectrum-inf and its lower bound (both `Y`/`A`
    discharged); invertible order-4 `O(4)` rotation automorphism;
    uniform-in-coupling surrogate floor.
  * PROVED-MODULO: operator-form gap (Residual A); full 5-field GNS
    reconstruction (Residual A + Residual B).
  * OPEN (uninhabited): bounded self-adjoint `H` with `e^{−H}=T` (Residual B);
    genuine physical margin; physical `O(4)` isotropization running; continuum
    Minlos measure.  The Clay Yang–Mills mass-gap problem remains OPEN.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorryAx`,
no `native_decide`, no custom `axiom`.  This module wires already-proved terms;
its axiom footprint is exactly that of the sources it consumes.
-/

import YMGap.Continuum.ReconstructionCapstone
import YMGap.Continuum.HamiltonianSpectrumInf
import YMGap.Continuum.ArtanhMonotone
import YMGap.Continuum.UniformCouplingFromAF
import YMGap.Continuum.H4RotationAuto
import YMGap.Continuum.O4RestorationProgress
import YMGap.Rubric.ClayScorecard

namespace YMGap.Rubric.ReconstructionScorecard

open YMGap.Constructive
open YMGap.Constructive.CRealLog
open YMGap.Continuum
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.RGTransport
open YMGap.Continuum.ReflectionPositivity
open YMGap.Continuum.WilsonSpectralBridge
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.CharacterDiagResolutionProof
open YMGap.Continuum.HamiltonianSpectrumInf
open YMGap.Continuum.ReconstructionCapstone

/-! ## 0. The two diagonal Schur / Peter–Weyl identities (Residual A), named once

These are the finite-character-coordinate parseval identities that
`wilsonFormGap` consumes.  Naming them once (as `def`s definitionally equal to
the raw `∀`-forms the capstone expects) lets the reductions below reuse the
statements without re-transcription. -/

/-- **Residual A, part 1.**  The diagonal self-inner Schur identity in the finite
character coordinates `coord`: `⟨x,x⟩ = Σ_i reflWeight·|coord x i|²`. -/
def SchurSelfIdentity (D : SmulGNSData)
    (t : Q') (ht : (0 : Q') ≤ t) (N : Nat)
    (coord : (D.toGNSData.gnsComplete).hilbert.carrier → Fin N → Q') : Prop :=
  ∀ x, (D.toGNSData.gnsComplete).hilbert.cinner x x
      = CReal.RCfinSum N (fun i =>
          Quotient.mk CReal.crealSetoid
            (CReal.mul (reflWeight t ht (i.val + 1))
              (CReal.ofQ' (coord x i * coord x i))))

/-- **Residual A, part 2.**  The diagonal `T`-inner Schur identity: the transfer
operator acts by the diagonal heat-kernel eigenvalue `qpow w (c4 (i+1))`. -/
def SchurTIdentity (D : SmulGNSData)
    (op : TransferOperator D.toGNSData.gnsComplete)
    (w t : Q') (ht : (0 : Q') ≤ t) (N : Nat)
    (coord : (D.toGNSData.gnsComplete).hilbert.carrier → Fin N → Q') : Prop :=
  ∀ x, (D.toGNSData.gnsComplete).hilbert.cinner (op.T x) x
      = CReal.RCfinSum N (fun i =>
          Quotient.mk CReal.crealSetoid
            (CReal.mul (CReal.ofQ' (qpow w (c4 (i.val + 1))))
              (CReal.mul (reflWeight t ht (i.val + 1))
                (CReal.ofQ' (coord x i * coord x i)))))

/-! ## 1. `ReconstructionProvedLine` — the PROVED-UNCONDITIONAL bundle

CONCRETE about the named excited-tower transfer object `excG op w hw0 hw1 N`
(no free existential over abstract models).  Every field is an actual discharge
term of an already-proved theorem. -/

/-- **The proved-unconditional reconstruction line** over the concrete
excited-tower object `excG op w hw0 hw1 N`.  Each field is a genuine theorem. -/
structure ReconstructionProvedLine
    (D : SmulGNSData)
    (op : TransferOperator D.toGNSData.gnsComplete)
    (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (hwpos : (0 : Q') < w)
    (N : Nat) : Type where
  /-- (1) the strictly-positive mass gap `Δ`, pinned to `−log sep` through the
  genuine range reduction (UNCONDITIONAL in the separator). -/
  massGap :
    ∃ Δ : CReal, CReal.IsPositive Δ ∧
      ∃ red : CRealLogRangeReduction (CReal.ofQ' (excG op w hw0 hw1 N).gap.sep),
        CReal.Equiv Δ (CReal.neg (CReal.log
          (CReal.ofQ' (excG op w hw0 hw1 N).gap.sep) red))
  /-- (2) the completion vector-scaling structure (`cSmul` + dense-image law). -/
  gnsVectorSpace : VectorScalingResidual D.toGNSData
  /-- (3) the located spectrum-infimum residual `Δ = inf spec`, discharged. -/
  spectrumInf :
    ∀ (_hwin : Q'.abs (yOf (excG op w hw0 hw1 N).gap.sep
        (sepPlusOne_pos (excG op w hw0 hw1 N).gap)) ≤ recipOdd 1),
      SpectrumInfResidual (excG op w hw0 hw1 N)
  /-- (4) the located-inf LOWER bound `Δ ≤ E_i` for every in-window excited mode
  `i` — UNCONDITIONAL here (the `Y`/`A` monotonicity premises the capstone
  exposes are closed by the genuine `ArtanhMonotone` witnesses). -/
  spectrumInfLowerBound :
    ∀ (hwin : Q'.abs (yOf (excG op w hw0 hw1 N).gap.sep
        (sepPlusOne_pos (excG op w hw0 hw1 N).gap)) ≤ recipOdd 1)
      (i : Nat)
      (hm1i : (0 : Q') < (excitedCharModel w hw0 N).lam i + 1)
      (hwini : Q'.abs (yOf ((excitedCharModel w hw0 N).lam i) hm1i) ≤ recipOdd 1),
      CReal.leEv ((excG op w hw0 hw1 N).hamiltonianGapReal hwin)
        (CReal.neg (logRat ((excitedCharModel w hw0 N).lam i) hm1i hwini))
  /-- (5) the invertible order-4 `O(4)` rotation automorphism: two-sided
  inverse, order 4, and order EXACTLY 4. -/
  o4RotationAut :
    (∀ x, H4RotationAuto.rot4Inv.map (H4RotationAuto.rot4.map x) = x)
    ∧ (∀ x, H4RotationAuto.rot4.map (H4RotationAuto.rot4Inv.map x) = x)
    ∧ (∀ x, H4RotationAuto.rot4.map (H4RotationAuto.rot4.map
              (H4RotationAuto.rot4.map (H4RotationAuto.rot4.map x))) = x)
    ∧ (H4RotationAuto.rot4.map (1, 0, 0, 0) ≠ (1, 0, 0, 0)
       ∧ H4RotationAuto.rot4.map (H4RotationAuto.rot4.map (1, 0, 0, 0)) ≠ (1, 0, 0, 0)
       ∧ H4RotationAuto.rot4.map (H4RotationAuto.rot4.map
            (H4RotationAuto.rot4.map (1, 0, 0, 0))) ≠ (1, 0, 0, 0))
  /-- (6) the uniform-in-coupling SURROGATE floor (survival product
  `∏(1−δ_ren)`; NOT the genuine dimensionless margin — see the ledger). -/
  uniformInCouplingSurrogate : YMGap.Rubric.ClayScorecard.RubricUniformInCoupling

/-- **The proved-unconditional line, inhabited** for ANY excited-tower transfer
object.  All six fields are real theorems. -/
def reconstruction_proved_line
    (D : SmulGNSData)
    (op : TransferOperator D.toGNSData.gnsComplete)
    (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (hwpos : (0 : Q') < w)
    (N : Nat) :
    ReconstructionProvedLine D op w hw0 hw1 hwpos N where
  massGap :=
    HamiltonianAllSep.mass_gap_hamiltonian_all (excG op w hw0 hw1 N)
      (ReconstructionCapstone.heatKernelSep_num_pos w hwpos)
  gnsVectorSpace := D.vectorScalingResidual
  spectrumInf := fun hwin =>
    HamiltonianSpectrumInf.spectrumInfResidual op w hw0 hw1 N hwin
  spectrumInfLowerBound := fun hwin i hm1i hwini =>
    HamiltonianSpectrumInf.hamiltonianGap_le_energy op w hw0 hw1 N
      ArtanhMonotone.yOfMonotone ArtanhMonotone.artanhMonotoneWindow
      hwin i hm1i hwini
  o4RotationAut :=
    ⟨H4RotationAuto.rot4_leftInv, H4RotationAuto.rot4_rightInv,
     H4RotationAuto.rot4_order4, H4RotationAuto.rot4_order_exactly4⟩
  uniformInCouplingSurrogate := UniformCouplingFromAF.rubricUniformInCoupling_met

/-! ## 2. PROVED-MODULO reductions

These are NOT part of the proved line: `schur_self` / `schur_T` (Residual A) and
`H` (Residual B) are HYPOTHESES.  The REDUCTION — that they assemble the
operator-form gap / the full 5-field reconstruction — is what is proved. -/

/-- **Operator-form gap, MODULO Residual A.**  From the two diagonal Schur
identities, the operator-level `T`-gap `⟨Tx,x⟩ ≤ sep·⟨x,x⟩` on `vac⊥`.  The
scalar-order monotonicity is discharged internally by `CReal.RCscale_mono_scalar`
(not an exposed premise). -/
def operatorFormGap_of_schur
    (D : SmulGNSData)
    (op : TransferOperator D.toGNSData.gnsComplete)
    (w t : Q') (ht : (0 : Q') ≤ t)
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (N : Nat)
    (coord : (D.toGNSData.gnsComplete).hilbert.carrier → Fin N → Q')
    (schur_self : SchurSelfIdentity D t ht N coord)
    (schur_T : SchurTIdentity D op w t ht N coord) :
    TransferFormGapResidual (excitedCharSpectralGapData op w hw0 hw1 N) :=
  wilsonFormGap op w t ht hw0 hw1 N CReal.RCscale_mono_scalar coord schur_self schur_T

/-- **Full 5-field GNS reconstruction, MODULO Residual A + Residual B.**  Given
the two Schur identities (Residual A) and the bounded functional-calculus
Hamiltonian datum `H` (Residual B), assemble the whole finite-volume Wilson GNS
reconstruction bundle. -/
def full_reconstruction_of_inputs
    (D : SmulGNSData)
    (op : TransferOperator D.toGNSData.gnsComplete)
    (L : AdditiveTransferOperator D.toGNSData)
    (w t : Q') (ht : (0 : Q') ≤ t)
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (hwpos : (0 : Q') < w) (N : Nat)
    (hwin : Q'.abs (yOf (excitedCharSpectralGapData op w hw0 hw1 N).gap.sep
        (sepPlusOne_pos (excitedCharSpectralGapData op w hw0 hw1 N).gap)) ≤ recipOdd 1)
    (coord : (D.toGNSData.gnsComplete).hilbert.carrier → Fin N → Q')
    (schur_self : SchurSelfIdentity D t ht N coord)
    (schur_T : SchurTIdentity D op w t ht N coord)
    (H : BoundedFunctionalCalculusResidual
          (excitedCharSpectralGapData op w hw0 hw1 N) L) :
    WilsonGNSReconstruction D op L w hw0 hw1 hwpos N :=
  wilson_gns_reconstruction_gap D op L w t ht hw0 hw1 hwpos N hwin
    coord schur_self schur_T H

/-! ## 3. OPEN residual tokens (uninhabited here — NO inhabitant provided) -/

/-- **OPEN (Residual B).**  The bounded self-adjoint additive Hamiltonian `H`
with `e^{−H}=T` — the single irreducibly hard operator-theoretic node. -/
abbrev OpenBoundedHamiltonian {D : GNSData}
    (G : SpectralGapData D.gnsComplete) (L : AdditiveTransferOperator D) :=
  BoundedFunctionalCalculusResidual G L

/-- **OPEN.**  The genuine dimensionless physical margin recursion
`Δ_k = m_lat(a_k)/a_k` — DISTINCT from the survival-product surrogate. -/
abbrev OpenTrueMargin := UniformCouplingFromAF.TrueMarginRecursion

/-- **OPEN.**  The physical `O(4)` isotropization running (`betaDrop`-sign /
anisotropy decay) — DISTINCT from the invertible order-4 automorphism. -/
abbrev OpenO4PhysicalRunning := O4RestorationProgress.CouplingRunning

/-- **OPEN.**  The continuum Minlos measure (OS reconstruction with tightness). -/
abbrev OpenContinuumMeasure := YMGap.Rubric.ClayScorecard.ClayContinuumExistence

/-! ## 4. `FullReconstructionTarget` — DELIBERATELY UNINHABITED

Bundles the PROVED line with the PROVED-MODULO inputs (Residual A = the two
Schur identities; Residual B = `OpenBoundedHamiltonian`) and the remaining OPEN
tokens.  A `reconstruction_proved_line` term IS provided (above); NO
`FullReconstructionTarget` term is.  Inhabiting this structure WITHOUT `sorry`,
`axiom`, or a vacuous `Prop := True` field is EXACTLY the open
continuum-reconstruction problem: it requires genuine inhabitants of Residual B,
`OpenTrueMargin`, `OpenO4PhysicalRunning`, and `OpenContinuumMeasure`, none of
which this development possesses. -/
structure FullReconstructionTarget
    (D : SmulGNSData)
    (op : TransferOperator D.toGNSData.gnsComplete)
    (L : AdditiveTransferOperator D.toGNSData)
    (w t : Q') (ht : (0 : Q') ≤ t)
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (hwpos : (0 : Q') < w) (N : Nat)
    (coord : (D.toGNSData.gnsComplete).hilbert.carrier → Fin N → Q') : Type where
  /-- the PROVED-UNCONDITIONAL line. -/
  provedLine : ReconstructionProvedLine D op w hw0 hw1 hwpos N
  /-- Residual A, part 1 (a HYPOTHESIS). -/
  schur_self : SchurSelfIdentity D t ht N coord
  /-- Residual A, part 2 (a HYPOTHESIS). -/
  schur_T : SchurTIdentity D op w t ht N coord
  /-- Residual B — OPEN, no inhabitant in this development. -/
  boundedH : OpenBoundedHamiltonian (excG op w hw0 hw1 N) L
  /-- OPEN: the genuine dimensionless physical margin. -/
  openTrueMargin : OpenTrueMargin
  /-- OPEN: the physical `O(4)` isotropization running. -/
  openO4Running : OpenO4PhysicalRunning
  /-- OPEN: the continuum Minlos measure. -/
  openContinuum : OpenContinuumMeasure

/-! ## 5. The assembled full reconstruction, MODULO the whole target

IF a `FullReconstructionTarget` were inhabited, THEN the full 5-field Wilson GNS
reconstruction follows — by feeding its Residual-A/Residual-B fields to the
proved-modulo reduction.  This is the honest statement of what continuum
closure would need; NO `FullReconstructionTarget` term is provided. -/
def full_reconstruction_of_target
    (D : SmulGNSData)
    (op : TransferOperator D.toGNSData.gnsComplete)
    (L : AdditiveTransferOperator D.toGNSData)
    (w t : Q') (ht : (0 : Q') ≤ t)
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (hwpos : (0 : Q') < w) (N : Nat)
    (hwin : Q'.abs (yOf (excitedCharSpectralGapData op w hw0 hw1 N).gap.sep
        (sepPlusOne_pos (excitedCharSpectralGapData op w hw0 hw1 N).gap)) ≤ recipOdd 1)
    (coord : (D.toGNSData.gnsComplete).hilbert.carrier → Fin N → Q')
    (F : FullReconstructionTarget D op L w t ht hw0 hw1 hwpos N coord) :
    WilsonGNSReconstruction D op L w hw0 hw1 hwpos N :=
  full_reconstruction_of_inputs D op L w t ht hw0 hw1 hwpos N hwin
    coord F.schur_self F.schur_T F.boundedH

end YMGap.Rubric.ReconstructionScorecard

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Rubric.ReconstructionScorecard.reconstruction_proved_line
#print axioms YMGap.Rubric.ReconstructionScorecard.operatorFormGap_of_schur
#print axioms YMGap.Rubric.ReconstructionScorecard.full_reconstruction_of_inputs
#print axioms YMGap.Rubric.ReconstructionScorecard.full_reconstruction_of_target
