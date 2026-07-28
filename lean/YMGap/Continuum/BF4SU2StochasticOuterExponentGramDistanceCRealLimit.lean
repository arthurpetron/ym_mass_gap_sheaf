/-
# Nonlinear stochastic SU(2) exponent-Gram distance limit

For a supplied source-indexed SU(2) outer Markov contract, this module sums
the absolute blocked-minus-coarse residual over a fixed finite list of
exponent-Gram coordinates.  The reverse triangle inequality transports the
coordinate Cauchy theorem through the nonlinear absolute value.

The executable list modulus pays one common coordinate tolerance

    epsilon * invSucc coordinates.length.

Thus the complete finite sum costs at most
`coordinates.length / (coordinates.length + 1) * epsilon ≤ epsilon`.
The empty list is handled by a separate definitional branch with modulus
zero.

The resulting exact rational distance sequence defines a Bishop `CReal`,
with constructive convergence and uniqueness.

This remains conditional on `SU2OuterPhysicalMarkovContract`.  In
particular it does not construct the all-cutoff BF4 raw kernel or discharge
the positive-row and lossless-support inputs isolated by
`BF4SU2OuterPhysicalMarkovKernelFrontier`.

## Axiom gate

Finite `List`, `Nat`, and `Q'` algebra plus the project's Bishop `CReal`.
No classical principle, native decision shortcut, custom axiom, hidden proof
hole, functional extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4SU2CoarseOuterExponentGramTail
import YMGap.Continuum.Z4FiniteCylinderQuadraticStability
import YMGap.Constructive.CRealAbs

namespace
  YMGap.Continuum.BF4SU2StochasticOuterExponentGramDistanceCRealLimit

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4ExponentGramMatchedOneStep
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.BF4SU2CoarseOuterExponentGramTail
open YMGap.Continuum.BF4SU2OuterCutoffBlockGramContract
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The nonlinear finite-coordinate distance -/

/-- Finite nonlinear stochastic SU(2) exponent-Gram distance at outer
cutoff `K`. -/
def stochasticOuterExponentGramDistance
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (contract :
      SU2OuterPhysicalMarkovContract
        G g hg candidate hcandidate)
    (K : Nat)
    (coordinates : List ExponentGramCoordinate) : Q' :=
  listQSum
    (fun coordinate =>
      Q'.abs
        (stochasticBlockedMinusCoarseCoordinateDifference
          contract K coordinate))
    coordinates

/-- The exact rational score sequence embedded as constant constructive
reals. -/
def stochasticOuterExponentGramDistanceSeq
    {G : CutoffOneGeometry}
    {g : Q'} (hg0 : (0 : Q') < g)
    {candidate : Q'} (hcandidate0 : (0 : Q') < candidate)
    (contract :
      SU2OuterPhysicalMarkovContract
        G g (Q'.le_of_lt hg0)
        candidate hcandidate0)
    (coordinates : List ExponentGramCoordinate) :
    Nat → CReal :=
  fun K =>
    CReal.ofQ'
      (stochasticOuterExponentGramDistance
        contract K coordinates)

/-! ## 2. Absolute-value Lipschitz transport -/

/-- Reverse-triangle transport: two-sided closeness of signed coordinate
residuals gives the same tolerance after taking absolute values. -/
theorem stochasticCoordinateAbsoluteDistance_twoSided
    {firstValue secondValue ε : Q'}
    (h :
      firstValue ≤ secondValue + ε ∧
        secondValue ≤ firstValue + ε) :
    Q'.abs firstValue ≤ Q'.abs secondValue + ε ∧
      Q'.abs secondValue ≤ Q'.abs firstValue + ε := by
  have hsub :
      Q'.abs (firstValue + (-secondValue)) ≤ ε :=
    CReal.abs_sub_le_of_bounds h.1 h.2
  constructor
  · exact Q'.le_trans' _ _ _
      (Q'.abs_le_abs_add_abs_sub
        firstValue secondValue)
      (Q'.add_le_add_left
        (Q'.abs secondValue) _ _ hsub)
  · have hreverse :
        Q'.abs (secondValue + (-firstValue)) ≤ ε := by
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm
            secondValue firstValue))
        hsub
    exact Q'.le_trans' _ _ _
      (Q'.abs_le_abs_add_abs_sub
        secondValue firstValue)
      (Q'.add_le_add_left
        (Q'.abs firstValue) _ _ hreverse)

/-- One nonlinear absolute residual inherits the coordinate modulus without
loss. -/
theorem
    stochasticCoordinateAbsoluteDistance_twoSided_of_modulus
    {G : CutoffOneGeometry}
    {g : Q'} (hg0 : (0 : Q') < g)
    (hg1 : g < (1 : Q'))
    {candidate : Q'}
    (hcandidate0 : (0 : Q') < candidate)
    (hcandidate1 : candidate < (1 : Q'))
    (contract :
      SU2OuterPhysicalMarkovContract
        G g (Q'.le_of_lt hg0)
        candidate hcandidate0)
    {ε : Q'} (hε : (0 : Q') < ε)
    {first second : Nat}
    (hfirst :
      stochasticBlockedMinusCoarseCoordinateModulus
          G g candidate ε ≤ first)
    (hsecond :
      stochasticBlockedMinusCoarseCoordinateModulus
          G g candidate ε ≤ second)
    (coordinate : ExponentGramCoordinate) :
    Q'.abs
          (stochasticBlockedMinusCoarseCoordinateDifference
            contract first coordinate) ≤
        Q'.abs
            (stochasticBlockedMinusCoarseCoordinateDifference
              contract second coordinate) + ε ∧
      Q'.abs
          (stochasticBlockedMinusCoarseCoordinateDifference
            contract second coordinate) ≤
        Q'.abs
            (stochasticBlockedMinusCoarseCoordinateDifference
              contract first coordinate) + ε := by
  exact stochasticCoordinateAbsoluteDistance_twoSided
    (stochasticBlockedMinusCoarseCoordinateDifference_twoSided_of_modulus
      hg0 hg1 hcandidate0 hcandidate1 contract hε
      hfirst hsecond coordinate)

private theorem listQSum_le_length_mul
    {A : Type} (value : A → Q')
    {bound : Q'} (hbound0 : (0 : Q') ≤ bound) :
    ∀ items : List A,
      (∀ item, item ∈ items → value item ≤ bound) →
      listQSum value items ≤
        Q'.ofNat items.length * bound
  | [], _ =>
      Q'.le_of_eqv
        (Q'.eqv_symm (Q'.zero_mul_eqv bound))
  | head :: rest, hbound => by
      have hhead := hbound head List.mem_cons_self
      have hrest :=
        listQSum_le_length_mul value hbound0 rest
          (fun item hitem =>
            hbound item
              (List.mem_cons_of_mem head hitem))
      have hsum :
          value head + listQSum value rest ≤
            bound + Q'.ofNat rest.length * bound :=
        Q'.add_le_add hhead hrest
      have htarget :
          bound + Q'.ofNat rest.length * bound ≈
            Q'.ofNat (head :: rest).length * bound := by
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right
            bound ((1 : Q') * bound)
            (Q'.ofNat rest.length * bound)
            (Q'.eqv_symm
              (Q'.one_mul_eqv bound))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_symm
            (Q'.add_mul_eqv
              1 (Q'.ofNat rest.length) bound)) ?_
        apply Q'.mul_eqv_congr_right
        exact Q'.eqv_trans _ _ _
          (Q'.add_comm_eqv
            1 (Q'.ofNat rest.length))
          (Q'.eqv_symm
            (YMGap.Continuum.HKConvGen.ofNat_succ_eqv
              rest.length))
      exact Q'.le_trans' _ _ _
        hsum (Q'.le_of_eqv htarget)

private theorem length_mul_scaled_tolerance_le
    {A : Type} (items : List A)
    {ε : Q'} (hε0 : (0 : Q') ≤ ε) :
    Q'.ofNat items.length *
        (ε * Q'.invSucc items.length) ≤
      ε := by
  have hcount :
      Q'.ofNat items.length ≤
        Q'.ofNat (items.length + 1) :=
    Q'.ofNat_le_ofNat (by omega)
  have hratio :
      Q'.ofNat items.length *
          Q'.invSucc items.length ≤
        (1 : Q') := by
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right
        (Q'.ofNat items.length)
        (Q'.ofNat (items.length + 1))
        (Q'.invSucc items.length)
        hcount
        (Q'.invSucc_nonneg items.length))
      (Q'.le_of_eqv
        (Q'.ofNat_succ_mul_invSucc
          items.length))
  have hrearrange :
      Q'.ofNat items.length *
          (ε * Q'.invSucc items.length) ≈
        ε *
          (Q'.ofNat items.length *
            Q'.invSucc items.length) := by
    refine Q'.eqv_trans _
      ((Q'.ofNat items.length * ε) *
        Q'.invSucc items.length) _
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv
          (Q'.ofNat items.length) ε
          (Q'.invSucc items.length))) ?_
    refine Q'.eqv_trans _
      ((ε * Q'.ofNat items.length) *
        Q'.invSucc items.length) _
      (Q'.mul_eqv_congr_right _ _
        (Q'.invSucc items.length)
        (Q'.mul_comm_eqv
          (Q'.ofNat items.length) ε)) ?_
    exact Q'.mul_assoc_eqv
      ε (Q'.ofNat items.length)
      (Q'.invSucc items.length)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv hrearrange)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left
        (Q'.ofNat items.length *
          Q'.invSucc items.length)
        1 ε hratio hε0)
      (Q'.le_of_eqv (Q'.mul_one_eqv ε)))

/-! ## 3. Executable list-uniform modulus -/

/-- The empty nonlinear score is already constant.  A nonempty coordinate
list uses the coordinate modulus at the multiplicity-scaled tolerance. -/
def stochasticOuterExponentGramDistanceModulus
    (G : CutoffOneGeometry)
    (g candidate ε : Q')
    (coordinates : List ExponentGramCoordinate) : Nat :=
  match coordinates with
  | [] => 0
  | _ :: _ =>
      stochasticBlockedMinusCoarseCoordinateModulus
        G g candidate
        (ε * Q'.invSucc coordinates.length)

/-- Absolute difference of two full nonlinear scores, assuming the common
coordinate modulus at tolerance `delta`, is at most
`coordinates.length * delta`. -/
theorem stochasticOuterExponentGramDistance_abs_sub_le_length
    {G : CutoffOneGeometry}
    {g : Q'} (hg0 : (0 : Q') < g)
    (hg1 : g < (1 : Q'))
    {candidate : Q'}
    (hcandidate0 : (0 : Q') < candidate)
    (hcandidate1 : candidate < (1 : Q'))
    (contract :
      SU2OuterPhysicalMarkovContract
        G g (Q'.le_of_lt hg0)
        candidate hcandidate0)
    (coordinates : List ExponentGramCoordinate)
    {δ : Q'} (hδ : (0 : Q') < δ)
    {first second : Nat}
    (hfirst :
      stochasticBlockedMinusCoarseCoordinateModulus
          G g candidate δ ≤ first)
    (hsecond :
      stochasticBlockedMinusCoarseCoordinateModulus
          G g candidate δ ≤ second) :
    Q'.abs
        (stochasticOuterExponentGramDistance
            contract first coordinates +
          -stochasticOuterExponentGramDistance
            contract second coordinates) ≤
      Q'.ofNat coordinates.length * δ := by
  let firstValue : ExponentGramCoordinate → Q' :=
    fun coordinate =>
      Q'.abs
        (stochasticBlockedMinusCoarseCoordinateDifference
          contract first coordinate)
  let secondValue : ExponentGramCoordinate → Q' :=
    fun coordinate =>
      Q'.abs
        (stochasticBlockedMinusCoarseCoordinateDifference
          contract second coordinate)
  refine Q'.le_trans' _
    (listQSum
      (fun coordinate =>
        Q'.abs
          (firstValue coordinate +
            -secondValue coordinate))
      coordinates) _ ?_ ?_
  · unfold stochasticOuterExponentGramDistance
    exact abs_listQSum_sub_le
      firstValue secondValue coordinates
  · apply listQSum_le_length_mul
      (hbound0 := Q'.le_of_lt hδ)
    intro coordinate _
    have htwo :=
      stochasticCoordinateAbsoluteDistance_twoSided_of_modulus
        hg0 hg1 hcandidate0 hcandidate1 contract hδ
        hfirst hsecond coordinate
    exact CReal.abs_sub_le_of_bounds
      htwo.1 htwo.2

private theorem twoSided_of_abs_sub_le
    {a b ε : Q'}
    (h : Q'.abs (a + (-b)) ≤ ε) :
    a ≤ b + ε ∧ b ≤ a + ε := by
  constructor
  · exact
      YMGap.Constructive.ExpNeg.le_add_of_abs_sub_le h
  · apply
      YMGap.Constructive.ExpNeg.le_add_of_abs_sub_le
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm
          b a))
      h

/-- Every two full nonlinear score stages beyond the executable modulus are
two-sided `epsilon`-close. -/
theorem stochasticOuterExponentGramDistance_twoSided_of_modulus
    {G : CutoffOneGeometry}
    {g : Q'} (hg0 : (0 : Q') < g)
    (hg1 : g < (1 : Q'))
    {candidate : Q'}
    (hcandidate0 : (0 : Q') < candidate)
    (hcandidate1 : candidate < (1 : Q'))
    (contract :
      SU2OuterPhysicalMarkovContract
        G g (Q'.le_of_lt hg0)
        candidate hcandidate0)
    (coordinates : List ExponentGramCoordinate)
    {ε : Q'} (hε : (0 : Q') < ε)
    {first second : Nat}
    (hfirst :
      stochasticOuterExponentGramDistanceModulus
          G g candidate ε coordinates ≤ first)
    (hsecond :
      stochasticOuterExponentGramDistanceModulus
          G g candidate ε coordinates ≤ second) :
    stochasticOuterExponentGramDistance
          contract first coordinates ≤
        stochasticOuterExponentGramDistance
            contract second coordinates + ε ∧
      stochasticOuterExponentGramDistance
          contract second coordinates ≤
        stochasticOuterExponentGramDistance
            contract first coordinates + ε := by
  cases coordinates with
  | nil =>
      unfold stochasticOuterExponentGramDistance
      change
        (0 : Q') ≤ 0 + ε ∧
          (0 : Q') ≤ 0 + ε
      constructor <;>
        exact Q'.add_le_self_of_nonneg
          0 ε (Q'.le_of_lt hε)
  | cons head tail =>
      let coordinates :=
        head :: tail
      let δ :=
        ε * Q'.invSucc coordinates.length
      have hδ :
          (0 : Q') < δ :=
        Q'.mul_pos hε
          (Q'.invSucc_pos coordinates.length)
      have hcoordinateFirst :
          stochasticBlockedMinusCoarseCoordinateModulus
              G g candidate δ ≤ first := by
        exact hfirst
      have hcoordinateSecond :
          stochasticBlockedMinusCoarseCoordinateModulus
              G g candidate δ ≤ second := by
        exact hsecond
      have habsLength :=
        stochasticOuterExponentGramDistance_abs_sub_le_length
          hg0 hg1 hcandidate0 hcandidate1 contract
          coordinates hδ hcoordinateFirst
          hcoordinateSecond
      have habs :
          Q'.abs
              (stochasticOuterExponentGramDistance
                  contract first coordinates +
                -stochasticOuterExponentGramDistance
                  contract second coordinates) ≤
            ε :=
        Q'.le_trans' _ _ _ habsLength
          (length_mul_scaled_tolerance_le
            coordinates (Q'.le_of_lt hε))
      exact twoSided_of_abs_sub_le habs

/-! ## 4. Bishop real, convergence, and uniqueness -/

/-- Fixed-geometry, fixed-nome, finite-coordinate limit of the nonlinear
stochastic SU(2) exponent-Gram distance. -/
def stochasticOuterExponentGramDistanceLimit
    {G : CutoffOneGeometry}
    {g : Q'} (hg0 : (0 : Q') < g)
    (hg1 : g < (1 : Q'))
    {candidate : Q'}
    (hcandidate0 : (0 : Q') < candidate)
    (hcandidate1 : candidate < (1 : Q'))
    (contract :
      SU2OuterPhysicalMarkovContract
        G g (Q'.le_of_lt hg0)
        candidate hcandidate0)
    (coordinates : List ExponentGramCoordinate) : CReal where
  approx K :=
    stochasticOuterExponentGramDistance
      contract K coordinates
  cauchy := by
    intro ε hε
    refine
      ⟨stochasticOuterExponentGramDistanceModulus
          G g candidate ε coordinates,
        fun first second hfirst hsecond => ?_⟩
    exact
      stochasticOuterExponentGramDistance_twoSided_of_modulus
        hg0 hg1 hcandidate0 hcandidate1 contract
        coordinates hε hfirst hsecond

@[simp] theorem stochasticOuterExponentGramDistanceLimit_approx
    {G : CutoffOneGeometry}
    {g : Q'} (hg0 : (0 : Q') < g)
    (hg1 : g < (1 : Q'))
    {candidate : Q'}
    (hcandidate0 : (0 : Q') < candidate)
    (hcandidate1 : candidate < (1 : Q'))
    (contract :
      SU2OuterPhysicalMarkovContract
        G g (Q'.le_of_lt hg0)
        candidate hcandidate0)
    (coordinates : List ExponentGramCoordinate)
    (K : Nat) :
    (stochasticOuterExponentGramDistanceLimit
      hg0 hg1 hcandidate0 hcandidate1
      contract coordinates).approx K =
        stochasticOuterExponentGramDistance
          contract K coordinates :=
  rfl

theorem stochasticOuterExponentGramDistanceSeq_converges
    {G : CutoffOneGeometry}
    {g : Q'} (hg0 : (0 : Q') < g)
    (hg1 : g < (1 : Q'))
    {candidate : Q'}
    (hcandidate0 : (0 : Q') < candidate)
    (hcandidate1 : candidate < (1 : Q'))
    (contract :
      SU2OuterPhysicalMarkovContract
        G g (Q'.le_of_lt hg0)
        candidate hcandidate0)
    (coordinates : List ExponentGramCoordinate) :
    CReal.ConvergesTo
      (stochasticOuterExponentGramDistanceSeq
        hg0 hcandidate0 contract coordinates)
      (stochasticOuterExponentGramDistanceLimit
        hg0 hg1 hcandidate0 hcandidate1
        contract coordinates) := by
  intro ε hε
  let M :=
    stochasticOuterExponentGramDistanceModulus
      G g candidate ε coordinates
  refine ⟨M, fun K hK => ⟨M, fun n hn => ?_⟩⟩
  change
    stochasticOuterExponentGramDistance
          contract K coordinates ≤
        stochasticOuterExponentGramDistance
            contract n coordinates + ε ∧
      stochasticOuterExponentGramDistance
          contract n coordinates ≤
        stochasticOuterExponentGramDistance
            contract K coordinates + ε
  exact
    stochasticOuterExponentGramDistance_twoSided_of_modulus
      hg0 hg1 hcandidate0 hcandidate1 contract
      coordinates hε hK hn

private theorem crealEquiv_refl (x : CReal) :
    CReal.Equiv x x :=
  fun ε hε =>
    ⟨0, fun n _ =>
      ⟨Q'.add_le_self_of_nonneg
          (x.approx n) ε (Q'.le_of_lt hε),
        Q'.add_le_self_of_nonneg
          (x.approx n) ε (Q'.le_of_lt hε)⟩⟩

theorem
    stochasticOuterExponentGramDistanceLimit_equiv_of_converges
    {G : CutoffOneGeometry}
    {g : Q'} (hg0 : (0 : Q') < g)
    (hg1 : g < (1 : Q'))
    {candidate : Q'}
    (hcandidate0 : (0 : Q') < candidate)
    (hcandidate1 : candidate < (1 : Q'))
    (contract :
      SU2OuterPhysicalMarkovContract
        G g (Q'.le_of_lt hg0)
        candidate hcandidate0)
    (coordinates : List ExponentGramCoordinate)
    (L : CReal)
    (hL :
      CReal.ConvergesTo
        (stochasticOuterExponentGramDistanceSeq
          hg0 hcandidate0 contract coordinates) L) :
    CReal.Equiv
      (stochasticOuterExponentGramDistanceLimit
        hg0 hg1 hcandidate0 hcandidate1
        contract coordinates)
      L := by
  exact CReal.Equiv_of_limit_of_equal
    (fun K =>
      crealEquiv_refl
        (stochasticOuterExponentGramDistanceSeq
          hg0 hcandidate0 contract coordinates K))
    (stochasticOuterExponentGramDistanceSeq_converges
      hg0 hg1 hcandidate0 hcandidate1
      contract coordinates)
    hL

#print axioms stochasticOuterExponentGramDistance
#print axioms
  stochasticCoordinateAbsoluteDistance_twoSided
#print axioms
  stochasticCoordinateAbsoluteDistance_twoSided_of_modulus
#print axioms stochasticOuterExponentGramDistanceModulus
#print axioms
  stochasticOuterExponentGramDistance_abs_sub_le_length
#print axioms
  stochasticOuterExponentGramDistance_twoSided_of_modulus
#print axioms stochasticOuterExponentGramDistanceLimit
#print axioms stochasticOuterExponentGramDistanceSeq_converges
#print axioms
  stochasticOuterExponentGramDistanceLimit_equiv_of_converges

end
  YMGap.Continuum.BF4SU2StochasticOuterExponentGramDistanceCRealLimit
