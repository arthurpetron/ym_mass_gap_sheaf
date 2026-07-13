/-
Faithful two-mode SU(2) character integration from the constructive midpoint
Riemann-sum substrate.

`CosIntegralFamily` is underconstrained: it contains a value family and the
desired equations, but no integration operation or convergence provenance.
This file therefore does not use that record to claim Haar integration.
Instead it uses the actual rational midpoint sequences
`ChebOrthoMatrix.seqOrth2 c d`.  The proved Chebyshev fusion recurrence and the
constructive Riemann estimates give, unconditionally,

  seqOrth2 c d  -->  semiInt * delta(c,d).

Restricting to `c,d < 2` gives the requested faithful two-character integral
record.  Multiplication by the constructed `2/pi` normalizes every off-diagonal
entry to zero.  Normalizing the diagonal to one is exactly the still-open
`SemicircleValue.SemiConvergesToHalfPi` residual.

The final equivalence sharpens the semantic fence: adding even the base
Riemann-provenance field to any legacy `CosIntegralFamily` is logically
equivalent to that same open semicircle value residual.  Thus the trivial value
table cannot discharge it.
-/

import YMGap.Continuum.CosIntegralReduction
import YMGap.Continuum.ChebOrthoMatrixUncond
import YMGap.Continuum.SemicircleValue
import YMGap.Continuum.CRealContinuumAlg

namespace YMGap.Continuum.SU2FiniteHaarRiemannTwoMode

open YMGap.Constructive
open YMGap.Constructive.CRealAlg
open YMGap.Continuum
open YMGap.Continuum.ChebOrthoMatrix
open YMGap.Continuum.ChebOrthoMatrixUncond
open YMGap.Continuum.CosIntegralReduction
open YMGap.Continuum.HaarClassIntegral
open YMGap.Continuum.SemicircleValue

local infix:50 " ≈ " => Q'.eqv

def half : Q' := Q'.mkPos 1 2 (by decide)

/-! ## A faithful two-mode integral record -/

/-- A two-mode integral record whose values are certified as limits of the
actual midpoint Riemann sequences.  Unlike `CosIntegralFamily`, the provenance
is a field of the type. -/
structure FaithfulTwoModeIntegral : Type where
  rawMoment : Fin 2 → Fin 2 → CReal
  riemann_converges : ∀ i j,
    CReal.ConvergesTo (seqOrth2 i.val j.val) (rawMoment i j)

/-- The exact raw moment table delivered by the unconditional Chebyshev fusion
and midpoint-Riemann recurrence. -/
def faithfulTwoModeIntegral : FaithfulTwoModeIntegral where
  rawMoment := fun i j =>
    if i.val = j.val then SemicircleBoundClosed.semiInt else CReal.czero
  riemann_converges := fun i j => orthMatrix_unconditional i.val j.val

theorem faithful_raw_diagonal (i : Fin 2) :
    faithfulTwoModeIntegral.rawMoment i i =
      SemicircleBoundClosed.semiInt := by
  simp [faithfulTwoModeIntegral]

theorem faithful_raw_offdiagonal :
    faithfulTwoModeIntegral.rawMoment ⟨0, by decide⟩ ⟨1, by decide⟩ =
      CReal.czero := by
  rfl

/-- The headline faithful convergence theorem for the two character modes. -/
theorem faithful_two_mode_Riemann_converges (i j : Fin 2) :
    CReal.ConvergesTo (seqOrth2 i.val j.val)
      (if i.val = j.val then SemicircleBoundClosed.semiInt else CReal.czero) :=
  orthMatrix_unconditional i.val j.val

/-! ## Exact normalization arithmetic -/

/-- The normalized two-mode moment `(2/pi) * rawMoment`. -/
def normalizedMoment (i j : Fin 2) : CReal :=
  CReal.mul Constructive.Pi.twoOverPi
    (faithfulTwoModeIntegral.rawMoment i j)

/-- `(2/pi) * (pi/2) = 1`, derived from the repository's proved reciprocal
law `(2/pi) * pi = 2`. -/
theorem twoOverPi_mul_halfPi :
    CReal.Equiv
      (CReal.mul Constructive.Pi.twoOverPi Constructive.Pi.halfPi)
      (CReal.ofQ' (1 : Q')) := by
  unfold Constructive.Pi.halfPi
  refine CReal.Equiv.trans
    (CReal.Equiv.symm
      (cmul_assoc Constructive.Pi.twoOverPi (CReal.ofQ' half)
        Constructive.Pi.pi)) ?_
  refine CReal.Equiv.trans
    (CRealContinuumAlg.cmul_congr_left
      (cmul_comm Constructive.Pi.twoOverPi (CReal.ofQ' half))) ?_
  refine CReal.Equiv.trans
    (cmul_assoc (CReal.ofQ' half) Constructive.Pi.twoOverPi
      Constructive.Pi.pi) ?_
  refine CReal.Equiv.trans
    (CRealContinuumAlg.cmul_congr_right Constructive.Pi.twoOverPi_mul_pi) ?_
  refine CReal.Equiv.trans
    (CReal.Equiv.symm (ofQ'_mul half (2 : Q'))) ?_
  exact CReal.ofQ'_equiv_of_eqv (by decide)

/-- The off-diagonal normalized Haar moment is already closed, with no `pi`
value input. -/
theorem normalized_offdiagonal :
    CReal.Equiv (normalizedMoment ⟨0, by decide⟩ ⟨1, by decide⟩)
      CReal.czero := by
  unfold normalizedMoment
  rw [faithful_raw_offdiagonal]
  exact mul_czero Constructive.Pi.twoOverPi

/-- The diagonal normalizes to one once the sole semicircle value identity is
supplied. -/
theorem normalized_diagonal_of_semiValue
    (hvalue : CReal.Equiv SemicircleBoundClosed.semiInt
      Constructive.Pi.halfPi) (i : Fin 2) :
    CReal.Equiv (normalizedMoment i i) (CReal.ofQ' (1 : Q')) := by
  unfold normalizedMoment
  rw [faithful_raw_diagonal]
  exact CReal.Equiv.trans
    (CRealContinuumAlg.cmul_congr_right hvalue) twoOverPi_mul_halfPi

theorem normalized_diagonal_of_semiConverges
    (h : SemiConvergesToHalfPi) (i : Fin 2) :
    CReal.Equiv (normalizedMoment i i) (CReal.ofQ' (1 : Q')) :=
  normalized_diagonal_of_semiValue (semiVal_of_conv h) i

/-! ## Exact provenance fence for the legacy value-table type -/

/-- The base integral provenance absent from `CosIntegralFamily`: the genuine
`U_0^2 sqrt(1-x^2)` midpoint sums must converge to half of the record's claimed
raw constant-cosine value. -/
def BaseRiemannProvenance (F : CosIntegralFamily) : Prop :=
  CReal.ConvergesTo (seqOrth2 0 0)
    (CReal.mul (CReal.ofQ' half) (F.I 0))

theorem legacy_base_target_eq_halfPi (F : CosIntegralFamily) :
    CReal.Equiv (CReal.mul (CReal.ofQ' half) (F.I 0))
      Constructive.Pi.halfPi := by
  unfold Constructive.Pi.halfPi
  exact CRealContinuumAlg.cmul_congr_right F.I_zero

/-- Adding faithful base Riemann provenance to any legacy value table is
equivalent to the named open semicircle value residual.  In particular the
trivial inhabitant of `CosIntegralFamily` does not prove this field. -/
theorem baseRiemannProvenance_iff_semiConverges (F : CosIntegralFamily) :
    BaseRiemannProvenance F ↔ SemiConvergesToHalfPi := by
  constructor
  · intro hprov
    have hraw : CReal.Equiv SemicircleBoundClosed.semiInt
        (CReal.mul (CReal.ofQ' half) (F.I 0)) :=
      CReal.Equiv_of_limit_of_equal
        (fun N => Equiv_refl_self (seqOrth2 0 0 N))
        (orthMatrix_unconditional 0 0) hprov
    have hvalue : CReal.Equiv SemicircleBoundClosed.semiInt
        Constructive.Pi.halfPi :=
      CReal.Equiv.trans hraw (legacy_base_target_eq_halfPi F)
    exact convergesTo_retarget SemicircleBoundClosed.semiInt_converges hvalue
  · intro hsemi
    have hvalue : CReal.Equiv SemicircleBoundClosed.semiInt
        Constructive.Pi.halfPi := semiVal_of_conv hsemi
    have htarget : CReal.Equiv SemicircleBoundClosed.semiInt
        (CReal.mul (CReal.ofQ' half) (F.I 0)) :=
      CReal.Equiv.trans hvalue
        (CReal.Equiv.symm (legacy_base_target_eq_halfPi F))
    exact convergesTo_retarget (orthMatrix_unconditional 0 0) htarget

end YMGap.Continuum.SU2FiniteHaarRiemannTwoMode

#print axioms YMGap.Continuum.SU2FiniteHaarRiemannTwoMode.faithfulTwoModeIntegral
#print axioms YMGap.Continuum.SU2FiniteHaarRiemannTwoMode.faithful_two_mode_Riemann_converges
#print axioms YMGap.Continuum.SU2FiniteHaarRiemannTwoMode.normalized_offdiagonal
#print axioms YMGap.Continuum.SU2FiniteHaarRiemannTwoMode.normalized_diagonal_of_semiConverges
#print axioms YMGap.Continuum.SU2FiniteHaarRiemannTwoMode.baseRiemannProvenance_iff_semiConverges
