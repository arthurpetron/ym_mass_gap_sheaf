/-
# Completed original signed slab carrier after representation cutoff removal

The proved common cutoff-limit form supplies the existing constructive
null quotient and Hilbert completion. Every finite anchor observable maps
into this ONE carrier, and its completed pairing is pinned to the original
anchored cutoff limit, or to any sufficiently late original finite pairing.

The vacuum-code vector has norm one and is non-null in this completion.
Stationarity is NOT asserted: physical time/transfer, a strict gap, volume
and spacing limits, and the canonical continuum positive-time root remain
separate obligations. Completion retains explicit Cauchy representatives
and moduli; it does not choose representatives of arbitrary quotient sequences.
-/

import YMGap.Continuum.BF4ExactSlabCutoffLimitForm

namespace YMGap.Continuum.BF4ExactSlabCutoffLimitGNS

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4ExactPhysicalPerronSameActionFence
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredMatrixCauchy
open YMGap.Continuum.BF4FiveHolonomyNormalizedKernel
open YMGap.Continuum.BF4ExactSlabAnchoredCutoffLimit
open YMGap.Continuum.BF4ExactSlabBoundaryCutoffRecoding
open YMGap.Continuum.BF4ExactSlabFiniteBoundaryObservable
open YMGap.Continuum.BF4ExactSlabCutoffLimitForm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem norm_one_not_rad (D : GNSData) (a : D.V) (hunit : D.B a a ≈ 1) :
    ¬ D.rad a D.zero := by
  intro h
  have hz := (D.rad_zero_iff a).mp h
  have hbad : (1 : Q') ≈ 0 := Q'.eqv_trans _ _ _ (Q'.eqv_symm hunit) hz
  exact (by decide : ¬ (1 : Q') ≈ 0) hbad

/-- No fixed representation cutoff parameter remains on this carrier. -/
def cutoffLimitCompletion (w : Q') (hw : (0 : Q') ≤ w) :
    CompleteGNSHilbertGeneral (cutoffLimitGNSData w hw) :=
  (cutoffLimitGNSData w hw).gnsComplete_general

abbrev CutoffLimitCarrier (w : Q') (hw : (0 : Q') ≤ w) :=
  (cutoffLimitCompletion w hw).hilbert.carrier

def cutoffLimitEmbed (w : Q') (hw : (0 : Q') ≤ w) (a : BoundaryObservable) : CutoffLimitCarrier w hw :=
  (cutoffLimitCompletion w hw).hilbert.ι ((cutoffLimitGNSData w hw).qmk a)

theorem cutoffLimitEmbed_pairing (w : Q') (hw : (0 : Q') ≤ w) (a b : BoundaryObservable) :
    (cutoffLimitCompletion w hw).hilbert.cinner (cutoffLimitEmbed w hw a) (cutoffLimitEmbed w hw b) =
      Quotient.mk CReal.crealSetoid (CReal.ofQ' (limitForm w a b)) :=
  (cutoffLimitCompletion w hw).hilbert.ι_inner a b

/-- SAME original finite form, after its explicit pair-dependent modulus. -/
theorem cutoffLimitEmbed_finite_pairing (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (a b : BoundaryObservable) (hK : formModulus w a b ≤ K) :
    (cutoffLimitCompletion w hw).hilbert.cinner (cutoffLimitEmbed w hw a) (cutoffLimitEmbed w hw b) =
      Quotient.mk CReal.crealSetoid (CReal.ofQ' (finiteForm w K a b)) :=
  (cutoffLimitEmbed_pairing w hw a b).trans
    (Quotient.sound (CReal.ofQ'_equiv_of_eqv (Q'.eqv_symm (finiteForm_stable w K a b hK))))

/-- Every old finite anchor embeds into the same completed original limit. -/
theorem cutoffLimitEmbed_anchored_pairing (w : Q') (hw : (0 : Q') ≤ w) (anchor : Nat)
    (a b : EdgeLabelling → Q') :
    (cutoffLimitCompletion w hw).hilbert.cinner
      (cutoffLimitEmbed w hw (BoundaryObservable.ofCoefficients anchor a))
      (cutoffLimitEmbed w hw (BoundaryObservable.ofCoefficients anchor b)) =
      Quotient.mk CReal.crealSetoid (exactCutoffPairingLimit w anchor a b) :=
  (cutoffLimitEmbed_pairing w hw _ _).trans
    (Quotient.sound (CReal.ofQ'_equiv_of_eqv (limitForm_ofCoefficients w anchor a b)))

/-- A specified limit representative, not a choice of quotient representatives. -/
def limitRepresentative (w : Q') (hw : (0 : Q') ≤ w)
    (X : GeneralCompletionCauchy (cutoffLimitGNSData w hw)) : CauchyGNS (cutoffLimitGNSData w hw) := X.lim

theorem limitRepresentative_converges (w : Q') (hw : (0 : Q') ≤ w)
    (X : GeneralCompletionCauchy (cutoffLimitGNSData w hw)) :
    ∀ ε : Q', (0 : Q') < ε → ∃ P : Nat, ∀ p : Nat, P ≤ p →
      ∃ N : Nat, ∀ n : Nat, N ≤ n →
        (cutoffLimitGNSData w hw).distSqQ ((X.pt p).seq n) ((limitRepresentative w hw X).seq n) ≤ ε :=
  X.converges

/-- The trivial-representation boundary code, with its literal zero-cutoff witness. -/
def vacuumCode : BoundaryObservable := BoundaryObservable.ofCoefficients 0 (fun _ => 1)

private theorem zero_within : labelWithinB 0 (centralLowerFaceIds 0) zeroEdgeLabelling = true :=
  (labelWithinB_true_iff _ _ _).mpr (fun _ _ => Nat.zero_lt_succ 0)

private theorem state_eq_zero_of_within_zero (K : Nat) (state : EdgeLabelling)
    (hs : state ∈ centralHalfStates K 0)
    (hzero : labelWithinB 0 (centralLowerFaceIds 0) state = true) : state = zeroEdgeLabelling := by
  have hb := (labelWithinB_true_iff _ _ _).mp hzero
  have hoff := (boundedEdgeLabellings_sound K _ state hs).2
  funext id
  change state id = 0
  by_cases hi : id ∈ centralLowerFaceIds 0
  · have ht := hb id hi
    omega
  · exact hoff id hi

/-- On every original finite carrier, this one vector is exactly the old
vacuum-code delta, not merely a vector with coincidentally equal norm. -/
theorem vacuumCode_coefficient (K : Nat) (state : EdgeLabelling)
    (hs : state ∈ centralHalfStates K 0) : vacuumCode.coefficient state = vacuumCodeDelta K state := by
  cases ht : labelWithinB 0 (centralLowerFaceIds 0) state with
  | true =>
    have he := state_eq_zero_of_within_zero K state hs ht
    subst state
    change boundaryExtension 0 0 (fun _ => 1) zeroEdgeLabelling = vacuumCodeDelta K zeroEdgeLabelling
    simp only [boundaryExtension, zero_within, ↓reduceIte, vacuumCodeDelta]
  | false =>
    have hcode : bf4StateCode K 0 state ≠ bf4StateCode K 0 zeroEdgeLabelling := by
      intro he
      have hz := bf4StateCode_injective_on_centralHalfStates hs (zeroEdgeLabelling_mem_centralHalfStates K 0) he
      rw [hz, zero_within] at ht
      exact Bool.noConfusion ht
    change boundaryExtension 0 0 (fun _ => 1) state = vacuumCodeDelta K state
    simp only [boundaryExtension, ht, Bool.false_eq_true, ↓reduceIte, vacuumCodeDelta, if_neg hcode]

theorem vacuumCode_finite_norm (w : Q') (K : Nat) : finiteForm w K vacuumCode vacuumCode ≈ 1 :=
  Q'.eqv_trans _ _ _
    (finiteJointBilinear_coefficient_eqv_on _ _ (vacuumCodeDelta K) _ (vacuumCodeDelta K) _
      (fun state hs => Q'.eqv_of_eq (vacuumCode_coefficient K state hs))
      (fun state hs => Q'.eqv_of_eq (vacuumCode_coefficient K state hs)))
    (exactSlabAllCutoffQuadratic_vacuumCodeDelta_eqv_one w K)

theorem vacuumCode_limit_norm (w : Q') : limitForm w vacuumCode vacuumCode ≈ 1 :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm
    (finiteForm_stable w (formModulus w vacuumCode vacuumCode) vacuumCode vacuumCode (Nat.le_refl _)))
    (vacuumCode_finite_norm w _)

theorem vacuumCode_not_null (w : Q') (hw : (0 : Q') ≤ w) :
    ¬ (cutoffLimitGNSData w hw).rad vacuumCode (cutoffLimitGNSData w hw).zero := by
  apply norm_one_not_rad
  rw [cutoffLimitGNSData_form]
  exact vacuumCode_limit_norm w

theorem vacuumCode_completed_norm (w : Q') (hw : (0 : Q') ≤ w) :
    (cutoffLimitCompletion w hw).hilbert.cinner
      (cutoffLimitEmbed w hw vacuumCode) (cutoffLimitEmbed w hw vacuumCode) =
      Quotient.mk CReal.crealSetoid (CReal.ofQ' 1) :=
  (cutoffLimitEmbed_pairing w hw _ _).trans
    (Quotient.sound (CReal.ofQ'_equiv_of_eqv (vacuumCode_limit_norm w)))

theorem vacuumCode_completed_ne_zero (w : Q') (hw : (0 : Q') ≤ w) :
    cutoffLimitEmbed w hw vacuumCode ≠ cutoffLimitEmbed w hw BoundaryObservable.zero := by
  intro h
  have he := (cutoffLimitCompletion w hw).hilbert.ι_injective h
  exact vacuumCode_not_null w hw (Quotient.exact he)

end YMGap.Continuum.BF4ExactSlabCutoffLimitGNS

#print axioms YMGap.Continuum.BF4ExactSlabCutoffLimitGNS.cutoffLimitCompletion
#print axioms YMGap.Continuum.BF4ExactSlabCutoffLimitGNS.CutoffLimitCarrier
#print axioms YMGap.Continuum.BF4ExactSlabCutoffLimitGNS.cutoffLimitEmbed
#print axioms YMGap.Continuum.BF4ExactSlabCutoffLimitGNS.cutoffLimitEmbed_pairing
#print axioms YMGap.Continuum.BF4ExactSlabCutoffLimitGNS.cutoffLimitEmbed_finite_pairing
#print axioms YMGap.Continuum.BF4ExactSlabCutoffLimitGNS.cutoffLimitEmbed_anchored_pairing
#print axioms YMGap.Continuum.BF4ExactSlabCutoffLimitGNS.limitRepresentative
#print axioms YMGap.Continuum.BF4ExactSlabCutoffLimitGNS.limitRepresentative_converges
#print axioms YMGap.Continuum.BF4ExactSlabCutoffLimitGNS.vacuumCode
#print axioms YMGap.Continuum.BF4ExactSlabCutoffLimitGNS.vacuumCode_coefficient
#print axioms YMGap.Continuum.BF4ExactSlabCutoffLimitGNS.vacuumCode_finite_norm
#print axioms YMGap.Continuum.BF4ExactSlabCutoffLimitGNS.vacuumCode_limit_norm
#print axioms YMGap.Continuum.BF4ExactSlabCutoffLimitGNS.vacuumCode_not_null
#print axioms YMGap.Continuum.BF4ExactSlabCutoffLimitGNS.vacuumCode_completed_norm
#print axioms YMGap.Continuum.BF4ExactSlabCutoffLimitGNS.vacuumCode_completed_ne_zero
