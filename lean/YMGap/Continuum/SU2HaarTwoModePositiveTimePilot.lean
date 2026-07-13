/-
The smallest exact two-character calculation exposed by the legacy
`physPairing` expression, together with two semantic obstruction fences.

The `physPairing` expression is diagonal on the first two character modes, and
the established character transfer has two distinct strict rational
eigenvalues.  This is algebraically exact, but it is not an actual Haar
construction: `CosIntegralFamily` stores only the desired output values and no
integral or Riemann-sum provenance.  A trivial inhabitant is exhibited below.

The construction cannot yet be made into an actual reconstructed Wilson GNS
transfer.  First, the underconstrained `CosIntegralFamily` is not a faithful
integration interface.  Independently, the character Hilbert space is
attached to the deliberately degenerate `charGNS`: its dense-map field sends
the unique quotient class to zero, so neither nonzero character basis vector
is in its image.  The final theorems make that connector failure kernel-visible.
-/

import YMGap.Continuum.CosIntegralReduction
import YMGap.Continuum.PhysicalWilsonBridge
import YMGap.Constructive.ExpNegCongr
import YMGap.Constructive.SU3CharFactor

namespace YMGap.Continuum.SU2HaarTwoModePositiveTimePilot

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HaarClassIntegral
open YMGap.Continuum.CosIntegralReduction
open YMGap.Continuum.PhysicalWilsonBridge
open YMGap.Continuum.ReflectionPositivity
open YMGap.Continuum.RGTransport
open YMGap.Continuum.WilsonCharBridge
open YMGap.Continuum.WilsonSchurIdentities
open YMGap.Continuum.WilsonFunctional

local infix:50 " ≈ " => Q'.eqv

def coupling : Q' := Q'.mkPos 1 2 (by decide)
def legacyTime : Q' := Q'.mkPos 4 3 (by decide)

theorem coupling_window :
    (0 : Q') < coupling ∧ coupling < (1 : Q') := by decide

theorem legacyTime_pos : (0 : Q') ≤ legacyTime := by decide

/-! ## Underconstrained legacy cosine-value model -/

/-- A completely formal value table satisfying `CosIntegralFamily` without
defining or evaluating any integral. -/
def formalCosineValues : Nat → CReal
  | 0 => Constructive.Pi.pi
  | _ + 1 => CReal.czero

/-- `CosIntegralFamily` is trivially inhabited: its fields encode only the
claimed values, not their provenance as definite integrals.  This declaration
is a semantic no-go fence and must not be used as physical Haar closure. -/
def trivialCosIntegralFamily : CosIntegralFamily where
  I := formalCosineValues
  I_zero := CReal.Equiv.refl _
  I_succ := fun _ => CReal.Equiv.refl _

theorem trivial_family_is_value_table_only :
    trivialCosIntegralFamily.I 0 = Constructive.Pi.pi ∧
      (∀ k, trivialCosIntegralFamily.I (k + 1) = CReal.czero) := by
  exact ⟨rfl, fun _ => rfl⟩

/-! ## The legacy two-character `physPairing` table -/

/-- The heat-kernel-weighted legacy pairing on the first two character modes,
parameterized by the underconstrained value-table record. -/
def legacyTwoModeGram (F : CosIntegralFamily) (i j : Fin 2) : CReal :=
  physPairing (toAngleCosineIntegral F) legacyTime legacyTime_pos i.val j.val

/-- Every legacy pairing entry equals the directly defined character-Hilbert
inner product.  This is an algebraic equality of the underconstrained model,
not an integral-provenance theorem. -/
theorem legacyTwoModeGram_eq_cinner
    (F : CosIntegralFamily) (i j : Fin 2) :
    Quotient.mk CReal.crealSetoid (legacyTwoModeGram F i j) =
      (charHilbert legacyTime legacyTime_pos 2).cinner
        (basisVec i.val) (basisVec j.val) :=
  physPairing_eq_cinner (toAngleCosineIntegral F) legacyTime legacyTime_pos
    2 i.val j.val
    i.isLt j.isLt

/-- The exact two-mode Gram table, derived rather than postulated. -/
theorem legacyTwoModeGram_diagonal
    (F : CosIntegralFamily) (i j : Fin 2) :
    Quotient.mk CReal.crealSetoid (legacyTwoModeGram F i j) =
      if i.val = j.val then
        Quotient.mk CReal.crealSetoid
          (reflWeight legacyTime legacyTime_pos (i.val + 1))
      else Quotient.mk CReal.crealSetoid CReal.czero :=
  physical_reflection_diagonal_of_family F legacyTime legacyTime_pos 2
    i.val j.val i.isLt j.isLt

theorem legacyTwoModeGram_offdiag
    (F : CosIntegralFamily) :
    CReal.Equiv (legacyTwoModeGram F ⟨0, by decide⟩ ⟨1, by decide⟩)
      CReal.czero :=
  physPairing_offdiag (toAngleCosineIntegral F) legacyTime legacyTime_pos
    (by decide)

theorem legacyTwoModeGram_diag_nonneg
    (F : CosIntegralFamily) (i : Fin 2) :
    ExpPos.geRat (legacyTwoModeGram F i i) 0 := by
  exact SU3CharFactor.geRat_of_equiv
    (physPairing_diag (toAngleCosineIntegral F) legacyTime legacyTime_pos i.val)
    (reflWeight_nonneg legacyTime legacyTime_pos (i.val + 1))

/-! ## The diagonal heat-kernel expression is non-unit -/

def fiveTwelfths : Q' := Q'.mkPos 5 12 (by decide)

/-- At the first character, the chosen legacy parameter makes the heat-kernel
exponent exactly one.  The established alternating-series estimate therefore
bounds the diagonal weight by `5/12`. -/
theorem firstReflectionWeight_le_fiveTwelfths :
    CReal.leRat (reflWeight legacyTime legacyTime_pos 1) fiveTwelfths := by
  unfold reflWeight legacyTime fiveTwelfths
  exact CReal.leRat_of_equiv
    (expNeg_eqv_congr
      (Q'.mul_nonneg _ _ (by decide) (by decide)) (by decide)
      (by decide :
        (Q'.mkPos 4 3 (by decide) * casimirQ 1) ≈ (1 : Q')))
    ExpNeg.expNeg_one_leRat

/-- Consequently the diagonal heat-kernel expression is not the unit weight. -/
theorem firstReflectionWeight_nonunit :
    ¬ CReal.Equiv (reflWeight legacyTime legacyTime_pos 1)
      (CReal.ofQ' (1 : Q')) := by
  intro hunit
  have hone_le : CReal.leRat (CReal.ofQ' (1 : Q')) fiveTwelfths :=
    CReal.leRat_of_equiv (CReal.Equiv.symm hunit)
      firstReflectionWeight_le_fiveTwelfths
  obtain ⟨N, hN⟩ := hone_le (Q'.mkPos 1 12 (by decide)) (by decide)
  have hfalse := hN N (Nat.le_refl N)
  exact (by decide : ¬ ((1 : Q') ≤
    fiveTwelfths + Q'.mkPos 1 12 (by decide))) hfalse

/-! ## Two exact strict modes of the standalone character transfer -/

def firstMode : Nat → Q' := basisVec 0
def secondMode : Nat → Q' := basisVec 1

theorem two_modes_distinct : firstMode ≠ secondMode := by
  intro h
  have h0 := congrFun h 0
  exact (by decide : ¬ ((1 : Q') = (0 : Q'))) h0

def firstEigenvalue : Q' := qpow coupling (c4 1)
def secondEigenvalue : Q' := qpow coupling (c4 2)

theorem firstEigenvalue_exact :
    firstEigenvalue ≈ Q'.mkPos 1 8 (by decide) := by decide

theorem secondEigenvalue_exact :
    secondEigenvalue ≈ Q'.mkPos 1 256 (by decide) := by decide

theorem two_strict_eigenvalue_windows :
    ((0 : Q') < firstEigenvalue ∧ firstEigenvalue < (1 : Q')) ∧
      ((0 : Q') < secondEigenvalue ∧ secondEigenvalue < (1 : Q')) := by
  decide

theorem eigenvalues_distinct : ¬ (firstEigenvalue ≈ secondEigenvalue) := by
  decide

def twoModeCharacterTransfer :=
  charTransfer coupling (by decide) (by decide)
    legacyTime legacyTime_pos 2

theorem firstMode_eigen (s : Nat) :
    (twoModeCharacterTransfer.T firstMode s) ≈
      firstEigenvalue * firstMode s := by
  by_cases h : s = 0
  · subst s
    decide
  · change qpow coupling (c4 (s + 1)) * (if s = 0 then 1 else 0) ≈
      firstEigenvalue * (if s = 0 then 1 else 0)
    rw [if_neg h]
    exact Q'.eqv_trans _ _ _ (Q'.mul_zero_eqv _)
      (Q'.eqv_symm (Q'.mul_zero_eqv _))

theorem secondMode_eigen (s : Nat) :
    (twoModeCharacterTransfer.T secondMode s) ≈
      secondEigenvalue * secondMode s := by
  by_cases h : s = 1
  · subst s
    decide
  · change qpow coupling (c4 (s + 1)) * (if s = 1 then 1 else 0) ≈
      secondEigenvalue * (if s = 1 then 1 else 0)
    rw [if_neg h]
    exact Q'.eqv_trans _ _ _ (Q'.mul_zero_eqv _)
      (Q'.eqv_symm (Q'.mul_zero_eqv _))

/-! ## Exact current-API obstruction -/

/-- The current character Hilbert carrier is not reconstructed from its GNS
scaffold on even the first character mode: its `ι` map is identically
zero. -/
theorem firstMode_not_in_scaffold_image :
    ¬ ∃ q : charGNS.QuotSpace,
      (charHilbert legacyTime legacyTime_pos 2).ι q = firstMode := by
  intro h
  obtain ⟨q, hq⟩ := h
  have h0 := congrFun hq 0
  change (0 : Q') = 1 at h0
  exact (by decide : ¬ ((0 : Q') = (1 : Q'))) h0

theorem secondMode_not_in_scaffold_image :
    ¬ ∃ q : charGNS.QuotSpace,
      (charHilbert legacyTime legacyTime_pos 2).ι q = secondMode := by
  intro h
  obtain ⟨q, hq⟩ := h
  have h1 := congrFun hq 1
  change (0 : Q') = 1 at h1
  exact (by decide : ¬ ((0 : Q') = (1 : Q'))) h1

/-- Minimal connector condition required to interpret the two established
character modes as reconstructed positive-time GNS states. -/
def CurrentTwoModeGNSConnector : Prop :=
  ∀ i : Fin 2, ∃ q : charGNS.QuotSpace,
    (charHilbert legacyTime legacyTime_pos 2).ι q = basisVec i.val

/-- The current degenerate scaffold cannot supply that connector.  Thus the
strict two-mode operator is exact but not yet an operator on an actual Wilson
GNS reconstruction. -/
theorem current_two_mode_GNS_connector_impossible :
    ¬ CurrentTwoModeGNSConnector := by
  intro h
  exact firstMode_not_in_scaffold_image (h ⟨0, by decide⟩)

end YMGap.Continuum.SU2HaarTwoModePositiveTimePilot

#print axioms YMGap.Continuum.SU2HaarTwoModePositiveTimePilot.trivialCosIntegralFamily
#print axioms YMGap.Continuum.SU2HaarTwoModePositiveTimePilot.legacyTwoModeGram_diagonal
#print axioms YMGap.Continuum.SU2HaarTwoModePositiveTimePilot.firstReflectionWeight_nonunit
#print axioms YMGap.Continuum.SU2HaarTwoModePositiveTimePilot.firstMode_eigen
#print axioms YMGap.Continuum.SU2HaarTwoModePositiveTimePilot.secondMode_eigen
#print axioms YMGap.Continuum.SU2HaarTwoModePositiveTimePilot.current_two_mode_GNS_connector_impossible
