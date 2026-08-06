/-
Track 11.7-fusion / R2k -- reflective adjacent-scale fusion-power data.

The spectrum-pinned blocking dictionary has already discharged `finePin`
definitionally and `imagePin` from `BlockingStep.step`.  Its sole remaining
field is an equality between two rational fusion eigenvalues after embedding
them into `CReal`.  This module moves that equality back to its exact
computational substrate.

`QPowerCell` is a proof-about-computation certificate: it stores only the
cross-multiplied integer equality for `coarse = fine^n`.  A generic soundness
theorem lifts the cell through `Q'.eqv`, the rational embedding, and `CReal.cpow`.
The all-scale carrier therefore asks later physical work for decidable integer
certificates rather than opaque constructive-real equalities.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2RetunedBlockingDictionary

namespace YMGap.Continuum.P2RetunedFusionPowerCertificate

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.FusionKernelStatement
open YMGap.Continuum.FusionSpectrumBlockingIdentification
open YMGap.Continuum.P2RetunedBlockingDictionary
open YMGap.Continuum.BlockingStepFrontier
open YMGap.Continuum.CodynamicCRealFlow

local infix:50 " ≈ " => Q'.eqv

/-- The selected normalized p=2 fusion eigenvalue before embedding into
constructive reals. -/
def fusionModeQ (F : P2RetunedControlFamily) (mode : Nat -> Nat)
    (k : Nat) : Q' :=
  fusionEig (F.N k) (F.w k) 2 (mode k)
    ((F.control k).denomPos (mode k))

/-- `CReal.cpow` of a rational constant is the rational `qpow`, embedded.
This is approximation-wise definitional; no analytic limit argument enters. -/
theorem cpow_ofQ' (q : Q') : forall n : Nat,
    CReal.Equiv (CReal.cpow (CReal.ofQ' q) n)
      (CReal.ofQ' (RGTransport.qpow q n)) := by
  intro n
  apply SumOfSquares.Equiv_of_approx_eqv
  intro m
  rw [CodynamicCRealFlow.cpow_approx]
  exact Q'.eqv_refl _

/-- A reflection-friendly exact power cell.  The field is literally the
integer cross product computed by `Q'.eqv`; no division or `CReal` reasoning
appears in certificate data. -/
structure QPowerCell (coarse fine : Q') (n : Nat) : Type where
  crossMul :
    coarse.num * ((RGTransport.qpow fine n).den : Int) =
      (RGTransport.qpow fine n).num * (coarse.den : Int)

/-- Executable checker for a rational power cell.  Certificate generation may
emit only `(coarse, fine, n)`; the kernel recomputes the exact integer cross
product and `QPowerCell.ofCheck` reflects a successful result into the proof
interface. -/
def qPowerCellCheck (coarse fine : Q') (n : Nat) : Bool :=
  decide
    (coarse.num * ((RGTransport.qpow fine n).den : Int) =
      (RGTransport.qpow fine n).num * (coarse.den : Int))

/-- Reflection soundness for the executable power-cell checker. -/
def QPowerCell.ofCheck {coarse fine : Q'} {n : Nat}
    (h : qPowerCellCheck coarse fine n = true) :
    QPowerCell coarse fine n := by
  refine ⟨?_⟩
  exact of_decide_eq_true h

/-- Soundness of a cross-multiplied power cell. -/
theorem QPowerCell.eqv {coarse fine : Q'} {n : Nat}
    (C : QPowerCell coarse fine n) :
    coarse ≈ RGTransport.qpow fine n := by
  exact C.crossMul

/-- Existing rational equality proofs can be packaged as cells without loss. -/
def QPowerCell.ofEqv {coarse fine : Q'} {n : Nat}
    (h : coarse ≈ RGTransport.qpow fine n) :
    QPowerCell coarse fine n where
  crossMul := h

/-- A rational power cell lifts to the exact fusion-power field used by the
reviewed spectrum-pinned dictionary. -/
theorem fusionPower_of_cell
    {b : Nat} {F : P2RetunedControlFamily} {mode : Nat -> Nat} {k : Nat}
    (C : QPowerCell (fusionModeQ F mode k)
      (fusionModeQ F mode (k + 1)) (b + 1)) :
    CReal.Equiv (fusionModeCReal (F.control k) (mode k))
      (CReal.cpow
        (fusionModeCReal (F.control (k + 1)) (mode (k + 1))) (b + 1)) := by
  have hlift :
      CReal.Equiv (CReal.ofQ' (fusionModeQ F mode k))
        (CReal.ofQ'
          (RGTransport.qpow (fusionModeQ F mode (k + 1)) (b + 1))) :=
    CReal.ofQ'_equiv_of_eqv C.eqv
  exact CReal.Equiv.trans
    (by simpa only [fusionModeCReal, fusionModeQ] using hlift)
    (CReal.Equiv.symm (by
      simpa only [fusionModeCReal, fusionModeQ] using
        (cpow_ofQ' (fusionModeQ F mode (k + 1)) (b + 1))))

/-- The preferred all-scale physical interface after both map pins have been
eliminated.  `fusionPowerCell` is the only adjacent-scale spectral datum. -/
structure SpectrumPinnedP2CrossMulPowerData
    (b : Nat) (F : P2RetunedControlFamily) (mode : Nat -> Nat)
    (_blockingStep : BlockingStep (fusionSeparator F mode)) : Type where
  modeBulk : forall k,
    BulkModeCrux.q12 <= Q'.ofNat (c4 (mode k)) *
      ((1 : Q') - (F.control k).weff)
  fusionPowerCell : forall k,
    QPowerCell (fusionModeQ F mode k)
      (fusionModeQ F mode (k + 1)) (b + 1)

/-- Compile exact integer cells into the formerly CReal-valued fusion-power
field. -/
def SpectrumPinnedP2CrossMulPowerData.toFusionPowerData
    {b : Nat} {F : P2RetunedControlFamily} {mode : Nat -> Nat}
    {B : BlockingStep (fusionSeparator F mode)}
    (D : SpectrumPinnedP2CrossMulPowerData b F mode B) :
    SpectrumPinnedP2FusionPowerData b F mode B where
  modeBulk := D.modeBulk
  fusionPower := fun k => fusionPower_of_cell (D.fusionPowerCell k)

/-- Cross-multiplied cells now reach the genuine block-power law; `finePin`
and `imagePin` are still supplied only by the spectrum definition and the
physical `BlockingStep`. -/
theorem SpectrumPinnedP2CrossMulPowerData.blockPowerOnTrajectory
    {b : Nat} {F : P2RetunedControlFamily} {mode : Nat -> Nat}
    {B : BlockingStep (fusionSeparator F mode)}
    (D : SpectrumPinnedP2CrossMulPowerData b F mode B) :
    IsBlockPowerOnTrajectory b (fusionSeparator F mode) B.Φ :=
  D.toFusionPowerData.blockPowerOnTrajectory

/-- The same cells expose the exact self-similar spectrum trajectory. -/
theorem SpectrumPinnedP2CrossMulPowerData.selfSimilar
    {b : Nat} {F : P2RetunedControlFamily} {mode : Nat -> Nat}
    {B : BlockingStep (fusionSeparator F mode)}
    (D : SpectrumPinnedP2CrossMulPowerData b F mode B) :
    selfSimilarC b (fusionSeparator F mode) :=
  D.toFusionPowerData.selfSimilar

/-- End-to-end transport with the fusion power represented only by exact
cross-multiplied rational cells. -/
structure SpectrumPinnedP2CrossMulTransport (b : Nat) : Type where
  hb : 1 <= b
  family : P2RetunedControlFamily
  mode : Nat -> Nat
  blockingStep : BlockingStep (fusionSeparator family mode)
  cells : SpectrumPinnedP2CrossMulPowerData b family mode blockingStep
  sepNonneg : forall k, ExpPos.geRat (fusionSeparator family mode k) 0
  sepLeOne : forall k, CReal.leRat (fusionSeparator family mode k) 1
  floor0 : Q'
  floor0_pos : (0 : Q') < floor0
  hbase0 : CReal.leEv (CReal.ofQ' floor0)
    (CodynamicPhysFloor.physGapC b (fusionSeparator family mode)
      (RateMatchFloor.geomSpacing b) 0)

/-- Compile the integer-certificate transport into the reviewed one-pin
transport without adding a physical hypothesis. -/
def SpectrumPinnedP2CrossMulTransport.toBlockingTransport {b : Nat}
    (T : SpectrumPinnedP2CrossMulTransport b) :
    SpectrumPinnedP2BlockingTransport b where
  hb := T.hb
  family := T.family
  mode := T.mode
  blockingStep := T.blockingStep
  pins := T.cells.toFusionPowerData
  sepNonneg := T.sepNonneg
  sepLeOne := T.sepLeOne
  floor0 := T.floor0
  floor0_pos := T.floor0_pos
  hbase0 := T.hbase0

/-- Exact cross products reach the physical RG input. -/
def SpectrumPinnedP2CrossMulTransport.physicalRGInput {b : Nat}
    (T : SpectrumPinnedP2CrossMulTransport b) : PhysicalRGInput :=
  T.toBlockingTransport.physicalRGInput

/-- Exact cross products reach the spacing-uniform constructive-real floor. -/
def SpectrumPinnedP2CrossMulTransport.continuumGap {b : Nat}
    (T : SpectrumPinnedP2CrossMulTransport b) :
    UnifiedContinuumFloor.CRealFloor
      (CodynamicPhysFloor.physGapC b
        (fusionSeparator T.family T.mode) (RateMatchFloor.geomSpacing b)) :=
  T.toBlockingTransport.continuumGap

end YMGap.Continuum.P2RetunedFusionPowerCertificate

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2RetunedFusionPowerCertificate.cpow_ofQ'
#print axioms YMGap.Continuum.P2RetunedFusionPowerCertificate.QPowerCell.ofCheck
#print axioms YMGap.Continuum.P2RetunedFusionPowerCertificate.QPowerCell.eqv
#print axioms YMGap.Continuum.P2RetunedFusionPowerCertificate.fusionPower_of_cell
#print axioms YMGap.Continuum.P2RetunedFusionPowerCertificate.SpectrumPinnedP2CrossMulPowerData.toFusionPowerData
#print axioms YMGap.Continuum.P2RetunedFusionPowerCertificate.SpectrumPinnedP2CrossMulPowerData.blockPowerOnTrajectory
#print axioms YMGap.Continuum.P2RetunedFusionPowerCertificate.SpectrumPinnedP2CrossMulPowerData.selfSimilar
#print axioms YMGap.Continuum.P2RetunedFusionPowerCertificate.SpectrumPinnedP2CrossMulTransport.physicalRGInput
#print axioms YMGap.Continuum.P2RetunedFusionPowerCertificate.SpectrumPinnedP2CrossMulTransport.continuumGap
