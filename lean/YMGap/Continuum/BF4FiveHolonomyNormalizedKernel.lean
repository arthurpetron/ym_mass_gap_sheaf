/-
# Normalized five-holonomy character kernel and faithful BF4 state coding

This module constructs two concrete analytic ingredients for the
Peter--Weyl endpoint bridge.

1. `centralFiveHeatKernelPacket` is the finite all-spin character expansion
   of the product SU(2) heat kernel on the five retained holonomies.  Its
   coefficient at a five-spin mode is the product of the five literal
   heat-kernel coefficients.  The fivefold Haar functional is extraction of
   the all-vacuum coefficient, and the kernel is proved normalized exactly.

2. `bf4StateCode` is a mixed-radix code of a bounded BF4 face labelling.
   It is proved injective on the literal `centralHalfStates` carrier.  Hence
   every retained BF4 state has a canonical, distinct all-spin SU(2)
   character `chi_(bf4StateCode state)` available as an orthonormal
   Peter--Weyl coordinate.

The second construction is a faithful Hilbert-carrier realization, not yet
the geometric spin-network evaluation obtained by integrating the
non-transmitted BF4 chords.  That final identification must prove that the
canonical character coordinate agrees with the physical boundary
spin-network transform; it is not asserted here.

The fivefold kernel below is the genuine normalized product heat kernel.
It is not yet the coupled BF4 Mehler kernel associated with the generalized
pair `(kineticK24, spatialS24)`.  The final section records why the
non-symmetric matrix `generalizedA = K^{-1}S` cannot itself be called a
scalar Hessian.

## Axiom gate

Finite `Nat`, `List`, `Fin`, and exact `Q'` algebra only.  No
`Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4CentralPositivePeterWeylEndpoint
import YMGap.Continuum.SU2CharacterVacuumHaar
import YMGap.Continuum.ChebOrthoLegProof

namespace YMGap.Continuum.BF4FiveHolonomyNormalizedKernel

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BF4CanonicalClassCoordinateCarrier
open YMGap.Continuum.BF4CentralPositivePeterWeylEndpoint
open YMGap.Continuum.BF4FiveHolonomyGaussian
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ChebOrthoLegProof
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2ClassPolynomialAlgebra
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

local infix:50 " ≈ " => Q'.eqv

private theorem mul_eqv_congr
    {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-! ## 1. Fivefold character packets and their Haar functional -/

/-- A five-spin Peter--Weyl character mode.  Labels use the repository's
twice-spin convention, so the representation dimension is `spin + 1`. -/
abbrev FiveCharacterMode := Fin 5 → Nat

/-- Coefficients of the complete fivefold character box through cutoff `K`. -/
structure FiveCharacterPacket (K : Nat) : Type where
  coeff : FiveCharacterMode → Q'
  supported :
    ∀ mode,
      (∃ coordinate, K < mode coordinate) →
        coeff mode ≈ 0

/-- The all-vacuum five-spin mode. -/
def fiveVacuumMode : FiveCharacterMode :=
  fun _ => 0

/-- The normalized fivefold Haar functional: extract the coefficient of the
tensor product of five trivial characters. -/
def fiveCharacterHaar
    {K : Nat} (packet : FiveCharacterPacket K) : Q' :=
  packet.coeff fiveVacuumMode

/-- Point value of one fivefold central Peter--Weyl character. -/
def fiveCharacterValue
    (mode : FiveCharacterMode)
    (configuration : BF4FiveHolonomyConfiguration) : Q' :=
  indices.foldr
    (fun coordinate total =>
      Cheb.U
          (mode coordinate)
          (RationalQuaternion.coordinateNat
            (configuration coordinate).quaternion 0) *
        total)
    1

/-- One finite SU(2) heat-character value on a relative class coordinate. -/
def finiteHeatCharacterValue
    (w : Q') (K : Nat) (x : Q') : Q' :=
  finSum
    (fun spin =>
      coeffW w spin * Cheb.U spin x)
    (K + 1)

/-- The concrete finite product heat kernel on the five relative
holonomies. -/
def centralFiveHeatKernelValue
    (w : Q') (K : Nat)
    (source target : BF4FiveHolonomyConfiguration) : Q' :=
  indices.foldr
    (fun coordinate total =>
      finiteHeatCharacterValue w K
          (fiveRelativeClassCoordinate
            source target coordinate) *
        total)
    1

/-- Nested coefficient-bearing Peter--Weyl evaluation over an arbitrary
displayed list of retained holonomy coordinates. -/
def nestedFiveHeatPWExpansion
    (w : Q') (K : Nat)
    (source target : BF4FiveHolonomyConfiguration) :
    List BF4TemporalHolonomy → Q'
  | [] => 1
  | coordinate :: rest =>
      finSum
        (fun spin =>
          (coeffW w spin *
            Cheb.U spin
              (fiveRelativeClassCoordinate
                source target coordinate)) *
            nestedFiveHeatPWExpansion
              w K source target rest)
        (K + 1)

private theorem productHeatKernel_eq_nestedExpansion
    (w : Q') (K : Nat)
    (source target : BF4FiveHolonomyConfiguration) :
    ∀ coordinates : List BF4TemporalHolonomy,
      coordinates.foldr
          (fun coordinate total =>
            finiteHeatCharacterValue w K
                (fiveRelativeClassCoordinate
                  source target coordinate) *
              total)
          1 ≈
        nestedFiveHeatPWExpansion
          w K source target coordinates
  | [] => Q'.eqv_refl 1
  | coordinate :: rest => by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _
          (productHeatKernel_eq_nestedExpansion
            w K source target rest)) ?_
      unfold finiteHeatCharacterValue
      exact finSum_mul_const
        (fun spin =>
          coeffW w spin *
            Cheb.U spin
              (fiveRelativeClassCoordinate
                source target coordinate))
        (nestedFiveHeatPWExpansion
          w K source target rest)
        (K + 1)

/-- **Exact pointwise Peter--Weyl expansion.**  The normalized five-holonomy
kernel is the nested all-spin expansion with the displayed heat
coefficients; no informal product-of-sums step remains. -/
theorem centralFiveHeatKernelValue_eq_nestedPWExpansion
    (w : Q') (K : Nat)
    (source target : BF4FiveHolonomyConfiguration) :
    centralFiveHeatKernelValue w K source target ≈
      nestedFiveHeatPWExpansion
        w K source target indices := by
  exact productHeatKernel_eq_nestedExpansion
    w K source target indices

/-- Product of the five heat coefficients at one five-spin mode. -/
def fiveHeatModeCoefficient
    (w : Q') (mode : FiveCharacterMode) : Q' :=
  indices.foldr
    (fun coordinate total =>
      coeffW w (mode coordinate) * total)
    1

/-- The literal finite all-spin character packet of the fivefold product
heat kernel. -/
def centralFiveHeatKernelPacket
    (w : Q') (K : Nat) : FiveCharacterPacket K where
  coeff mode :=
    if ∀ coordinate, mode coordinate < K + 1
    then fiveHeatModeCoefficient w mode
    else 0
  supported := by
    intro mode hlarge
    rw [if_neg]
    · exact Q'.eqv_refl 0
    · intro hall
      rcases hlarge with ⟨coordinate, hcoordinate⟩
      exact (Nat.not_lt_of_ge hcoordinate) (hall coordinate)

/-- The vacuum heat coefficient is exactly one. -/
theorem coeffW_zero_exact (w : Q') :
    coeffW w 0 ≈ 1 := by
  unfold coeffW dimQ c4 qpow
  decide

private theorem foldr_coeffW_zero (w : Q') :
    ∀ coordinates : List (Fin 5),
      coordinates.foldr
          (fun _ total => coeffW w 0 * total) 1 ≈
        1
  | [] => Q'.eqv_refl 1
  | _ :: rest =>
      Q'.eqv_trans _ _ _
        (mul_eqv_congr
          (coeffW_zero_exact w)
          (foldr_coeffW_zero w rest))
        (by decide)

private theorem fiveHeatModeCoefficient_vacuum (w : Q') :
    fiveHeatModeCoefficient w fiveVacuumMode ≈ 1 := by
  unfold fiveHeatModeCoefficient fiveVacuumMode
  exact foldr_coeffW_zero w indices

/-- **Exact fivefold Haar normalization.**  Every cutoff of the genuine
five-holonomy product heat kernel has all-vacuum coefficient one. -/
theorem centralFiveHeatKernelPacket_normalized
    (w : Q') (K : Nat) :
    fiveCharacterHaar
        (centralFiveHeatKernelPacket w K) ≈
      1 := by
  unfold fiveCharacterHaar centralFiveHeatKernelPacket
  change
    (if ∀ coordinate : Fin 5, fiveVacuumMode coordinate < K + 1
      then fiveHeatModeCoefficient w fiveVacuumMode else 0) ≈ 1
  rw [if_pos]
  · exact fiveHeatModeCoefficient_vacuum w
  · intro coordinate
    change 0 < K + 1
    omega

/-- Relative quaternion class coordinates are symmetric in their endpoints. -/
theorem fiveRelativeClassCoordinate_symmetric
    (source target : BF4FiveHolonomyConfiguration)
    (coordinate : BF4TemporalHolonomy) :
    fiveRelativeClassCoordinate source target coordinate ≈
      fiveRelativeClassCoordinate target source coordinate := by
  unfold fiveRelativeClassCoordinate relativeClassCoordinate
    RationalQuaternion.dot
  exact finSum_eqv_congr _ _
    (fun index =>
      Q'.mul_comm_eqv
        ((source coordinate).quaternion.coordinateNat index)
        ((target coordinate).quaternion.coordinateNat index))
    4

private theorem finiteHeatCharacterValue_congr
    (w : Q') (K : Nat) {x y : Q'} (hxy : x ≈ y) :
    finiteHeatCharacterValue w K x ≈
      finiteHeatCharacterValue w K y := by
  unfold finiteHeatCharacterValue
  exact finSum_eqv_congr _ _
    (fun spin =>
      Q'.mul_eqv_congr_left
        (coeffW w spin) _ _
        (U_arg_eqv spin hxy))
    (K + 1)

/-- The normalized finite five-holonomy heat kernel is symmetric. -/
theorem centralFiveHeatKernelValue_symmetric
    (w : Q') (K : Nat)
    (source target : BF4FiveHolonomyConfiguration) :
    centralFiveHeatKernelValue w K source target ≈
      centralFiveHeatKernelValue w K target source := by
  unfold centralFiveHeatKernelValue indices
  exact mul_eqv_congr
    (finiteHeatCharacterValue_congr w K
      (fiveRelativeClassCoordinate_symmetric
        source target ⟨0, by decide⟩))
    (mul_eqv_congr
      (finiteHeatCharacterValue_congr w K
        (fiveRelativeClassCoordinate_symmetric
          source target ⟨1, by decide⟩))
      (mul_eqv_congr
        (finiteHeatCharacterValue_congr w K
          (fiveRelativeClassCoordinate_symmetric
            source target ⟨2, by decide⟩))
        (mul_eqv_congr
          (finiteHeatCharacterValue_congr w K
            (fiveRelativeClassCoordinate_symmetric
              source target ⟨3, by decide⟩))
          (mul_eqv_congr
            (finiteHeatCharacterValue_congr w K
              (fiveRelativeClassCoordinate_symmetric
                source target ⟨4, by decide⟩))
            (Q'.eqv_refl 1)))))

/-! ## 2. A faithful mixed-radix code for bounded BF4 states -/

/-- Mixed-radix code of the labels displayed on `ids`, with the first
displayed face as the least significant digit. -/
def edgeLabellingCode
    (base : Nat) : List Nat → EdgeLabelling → Nat
  | [], _ => 0
  | id :: rest, state =>
      state id + base * edgeLabellingCode base rest state

private theorem edgeLabellingCode_eq_implies_agree
    {base : Nat} (hbase : 0 < base) :
    ∀ {ids : List Nat} {left right : EdgeLabelling},
      (∀ id, id ∈ ids → left id < base) →
      (∀ id, id ∈ ids → right id < base) →
      edgeLabellingCode base ids left =
        edgeLabellingCode base ids right →
      ∀ id, id ∈ ids → left id = right id
  | [], left, right, _, _, _, id, hmem =>
      False.elim (List.not_mem_nil hmem)
  | head :: rest, left, right, hleft, hright, hcode, id, hmem => by
      have hleftHead : left head < base :=
        hleft head List.mem_cons_self
      have hrightHead : right head < base :=
        hright head List.mem_cons_self
      have hmod :=
        congrArg (fun value => value % base) hcode
      have hhead : left head = right head := by
        simpa [edgeLabellingCode,
          Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt hleftHead,
          Nat.mod_eq_of_lt hrightHead] using hmod
      rcases List.mem_cons.mp hmem with hid | hrest
      · subst id
        exact hhead
      · have hdiv :=
          congrArg (fun value => value / base) hcode
        have htailCode :
            edgeLabellingCode base rest left =
              edgeLabellingCode base rest right := by
          simpa [edgeLabellingCode,
            Nat.add_mul_div_left,
            Nat.div_eq_of_lt hleftHead,
            Nat.div_eq_of_lt hrightHead,
            hbase] using hdiv
        exact edgeLabellingCode_eq_implies_agree hbase
          (fun position hposition =>
            hleft position
              (List.mem_cons_of_mem head hposition))
          (fun position hposition =>
            hright position
              (List.mem_cons_of_mem head hposition))
          htailCode id hrest

/-- On labellings bounded on `ids` and zero off `ids`, the mixed-radix code
is injective as a function-valued labelling. -/
theorem edgeLabellingCode_injective_on_bounded
    {base : Nat} (hbase : 0 < base)
    {ids : List Nat} {left right : EdgeLabelling}
    (hleftBound : ∀ id, id ∈ ids → left id < base)
    (hrightBound : ∀ id, id ∈ ids → right id < base)
    (hleftZero : ∀ id, id ∉ ids → left id = 0)
    (hrightZero : ∀ id, id ∉ ids → right id = 0)
    (hcode :
      edgeLabellingCode base ids left =
        edgeLabellingCode base ids right) :
    left = right := by
  funext id
  by_cases hid : id ∈ ids
  · exact edgeLabellingCode_eq_implies_agree hbase
      hleftBound hrightBound hcode id hid
  · rw [hleftZero id hid, hrightZero id hid]

/-- Canonical all-spin character code of a literal BF4 lower-half state. -/
def bf4StateCode
    (K half : Nat) (state : EdgeLabelling) : Nat :=
  edgeLabellingCode
    (K + 1) (centralLowerFaceIds half) state

/-- **Faithfulness on the exact BF4 carrier.**  Distinct bounded lower-half
face labellings receive distinct all-spin character labels. -/
theorem bf4StateCode_injective_on_centralHalfStates
    {K half : Nat} {left right : EdgeLabelling}
    (hleft : left ∈ centralHalfStates K half)
    (hright : right ∈ centralHalfStates K half)
    (hcode :
      bf4StateCode K half left =
        bf4StateCode K half right) :
    left = right := by
  have hleftSound :=
    boundedEdgeLabellings_sound
      K (centralLowerFaceIds half) left hleft
  have hrightSound :=
    boundedEdgeLabellings_sound
      K (centralLowerFaceIds half) right hright
  exact edgeLabellingCode_injective_on_bounded
    (by omega : 0 < K + 1)
    hleftSound.1 hrightSound.1
    hleftSound.2 hrightSound.2 hcode

/-- The same faithful code theorem on the positive-row physical carrier. -/
theorem bf4StateCode_injective_on_positive
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {left right : EdgeLabelling}
    (hleft :
      left ∈ centralPositiveHalfStates w hw K half)
    (hright :
      right ∈ centralPositiveHalfStates w hw K half)
    (hcode :
      bf4StateCode K half left =
        bf4StateCode K half right) :
    left = right := by
  exact bf4StateCode_injective_on_centralHalfStates
    (mem_centralPositiveHalfStates_iff.mp hleft).1
    (mem_centralPositiveHalfStates_iff.mp hright).1
    hcode

/-! ## 3. Exact all-spin BF4 character wavefunctions -/

/-- The genuine single-copy SU(2) Haar pairing of two arbitrary character
labels.  The cutoff is chosen dynamically to contain both labels, so this is
an all-spin rather than fixed-cutoff definition. -/
def allSpinCharacterHaarPair (left right : Nat) : Q' :=
  let cutoff := max left right
  let leftMode : Fin (cutoff + 1) := ⟨left, by omega⟩
  let rightMode : Fin (cutoff + 1) := ⟨right, by omega⟩
  fusionHaar
    (basisPacket leftMode)
    (basisPacket rightMode)

/-- The all-spin Haar pairing is the exact Peter--Weyl Kronecker table. -/
theorem allSpinCharacterHaarPair_eq_delta
    (left right : Nat) :
    allSpinCharacterHaarPair left right ≈
      (if left = right then 1 else 0) := by
  exact all_mode_character_orthogonality left right

/-- Exact product Haar pairing of two fivefold character modes. -/
def fiveCharacterHaarPair
    (left right : FiveCharacterMode) : Q' :=
  indices.foldr
    (fun coordinate total =>
      allSpinCharacterHaarPair
          (left coordinate) (right coordinate) *
        total)
    1

/-- A faithful BF4 state is placed in the same nontrivial all-spin character
on each of the five transmitted holonomies.  The successor excludes the
vacuum and makes every wavefunction depend on every retained holonomy.

This is the canonical faithful character-coordinate realization.  It is not
yet the geometric BF4 spin-network produced by integrating the other
eighteen tree-gauge chords. -/
def bf4AllSpinMode
    (K half : Nat) (state : EdgeLabelling) :
    FiveCharacterMode :=
  fun _ => bf4StateCode K half state + 1

/-- Rational-complex point value of an arbitrary fivefold character mode. -/
def fiveCharacterWavefunction
    (mode : FiveCharacterMode)
    (configuration : BF4FiveHolonomyConfiguration) :
    RationalComplex :=
  { re := fiveCharacterValue mode configuration
    im := 0 }

/-- The explicit all-spin BF4 boundary wavefunction. -/
def bf4AllSpinWavefunction
    (K half : Nat) (state : EdgeLabelling) :
    BF4FiveHolonomyConfiguration → RationalComplex :=
  fiveCharacterWavefunction (bf4AllSpinMode K half state)

/-- The displayed finite Peter--Weyl character expansion.  Each canonical
BF4 wavefunction is one tensor-product character mode with coefficient one. -/
def bf4AllSpinExpansion
    (K half : Nat) (state : EdgeLabelling) :
    List FiveCharacterMode :=
  [bf4AllSpinMode K half state]

/-- Exact synthesis of the displayed one-term all-spin expansion. -/
theorem bf4AllSpinExpansion_synthesizes
    (K half : Nat) (state : EdgeLabelling) :
    ∀ configuration,
      RationalComplex.Eqv
        (bf4AllSpinWavefunction K half state configuration)
        ((bf4AllSpinExpansion K half state).foldr
          (fun mode total =>
            let value :=
              fiveCharacterWavefunction mode configuration
            { re := value.re + total.re
              im := value.im + total.im })
          RationalComplex.zero) := by
  intro configuration
  unfold bf4AllSpinWavefunction bf4AllSpinExpansion
  change RationalComplex.Eqv
    (fiveCharacterWavefunction
      (bf4AllSpinMode K half state) configuration)
    { re :=
        (fiveCharacterWavefunction
          (bf4AllSpinMode K half state) configuration).re + 0
      im :=
        (fiveCharacterWavefunction
          (bf4AllSpinMode K half state) configuration).im + 0 }
  exact
    ⟨Q'.eqv_symm
        (QPoly.q_add_zero_eqv
          (fiveCharacterWavefunction
            (bf4AllSpinMode K half state) configuration).re),
      Q'.eqv_symm
        (QPoly.q_add_zero_eqv
          (fiveCharacterWavefunction
            (bf4AllSpinMode K half state) configuration).im)⟩

/-- The canonical five-spin label is faithful on the positive physical
carrier. -/
theorem bf4AllSpinMode_injective_on_positive
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {left right : EdgeLabelling}
    (hleft :
      left ∈ centralPositiveHalfStates w hw K half)
    (hright :
      right ∈ centralPositiveHalfStates w hw K half)
    (hmode :
      bf4AllSpinMode K half left =
        bf4AllSpinMode K half right) :
    left = right := by
  have hcoordinate :=
    congrArg
      (fun mode : FiveCharacterMode =>
        mode ⟨0, by decide⟩)
      hmode
  apply bf4StateCode_injective_on_positive
    hleft hright
  change
    bf4StateCode K half left + 1 =
      bf4StateCode K half right + 1 at hcoordinate
  omega

private theorem foldr_character_self_normalized
    (label : Nat) :
    ∀ coordinates : List (Fin 5),
      coordinates.foldr
          (fun _ total =>
            allSpinCharacterHaarPair label label * total)
          1 ≈
        1
  | [] => Q'.eqv_refl 1
  | _ :: rest => by
      have hpair :
          allSpinCharacterHaarPair label label ≈ 1 :=
        Q'.eqv_trans _ _ _
          (allSpinCharacterHaarPair_eq_delta label label)
          (by rw [if_pos rfl]; exact Q'.eqv_refl 1)
      have hrest :=
        foldr_character_self_normalized label rest
      exact Q'.eqv_trans _ _ _
        (mul_eqv_congr hpair hrest)
        (Q'.one_mul_eqv 1)

/-- Every canonical BF4 all-spin wavefunction has unit fivefold Haar norm. -/
theorem bf4AllSpinWavefunction_normalized
    (K half : Nat) (state : EdgeLabelling) :
    fiveCharacterHaarPair
        (bf4AllSpinMode K half state)
        (bf4AllSpinMode K half state) ≈
      1 := by
  unfold fiveCharacterHaarPair bf4AllSpinMode
  exact foldr_character_self_normalized
    (bf4StateCode K half state + 1) indices

/-- Distinct retained BF4 states give orthogonal fivefold all-spin
Peter--Weyl wavefunctions. -/
theorem bf4AllSpinWavefunction_orthogonal
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {left right : EdgeLabelling}
    (hleft :
      left ∈ centralPositiveHalfStates w hw K half)
    (hright :
      right ∈ centralPositiveHalfStates w hw K half)
    (hne : left ≠ right) :
    fiveCharacterHaarPair
        (bf4AllSpinMode K half left)
        (bf4AllSpinMode K half right) ≈
      0 := by
  have hcode :
      bf4StateCode K half left + 1 ≠
        bf4StateCode K half right + 1 := by
    intro heq
    apply hne
    apply bf4StateCode_injective_on_positive
      hleft hright
    omega
  unfold fiveCharacterHaarPair bf4AllSpinMode indices
  refine Q'.eqv_trans _ _ _
    (mul_eqv_congr
      (Q'.eqv_trans _ _ _
        (allSpinCharacterHaarPair_eq_delta
          (bf4StateCode K half left + 1)
          (bf4StateCode K half right + 1))
        (by rw [if_neg hcode]; exact Q'.eqv_refl 0))
      (Q'.eqv_refl _)) ?_
  exact Q'.zero_mul_eqv _

/-- An expansion-level Peter--Weyl transform on the literal positive BF4
carrier.  Unlike the former raw-function Haar interface, every analytic
operation here is attached to coefficient-bearing character modes, on which
the normalized Haar functional has already been constructed exactly. -/
structure CentralPositiveBoundaryAllSpinCharacterTransform
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) : Type where
  stateMode : EdgeLabelling → FiveCharacterMode
  expansion : EdgeLabelling → List FiveCharacterMode
  boundaryWavefunction :
    EdgeLabelling →
      BF4FiveHolonomyConfiguration → RationalComplex
  haarInner : EdgeLabelling → EdgeLabelling → Q'
  mode_faithful :
    ∀ {left right},
      left ∈ centralPositiveHalfStates w hw K half →
      right ∈ centralPositiveHalfStates w hw K half →
      stateMode left = stateMode right →
        left = right
  synthesis :
    ∀ state,
      state ∈ centralPositiveHalfStates w hw K half →
      ∀ configuration,
        RationalComplex.Eqv
          (boundaryWavefunction state configuration)
          ((expansion state).foldr
            (fun mode total =>
              let value :=
                fiveCharacterWavefunction mode configuration
              { re := value.re + total.re
                im := value.im + total.im })
            RationalComplex.zero)
  haar_eq_mode :
    ∀ left right,
      left ∈ centralPositiveHalfStates w hw K half →
      right ∈ centralPositiveHalfStates w hw K half →
        haarInner left right ≈
          fiveCharacterHaarPair
            (stateMode left) (stateMode right)
  boundary_normalized :
    ∀ state,
      state ∈ centralPositiveHalfStates w hw K half →
        haarInner state state ≈ 1
  boundary_orthogonal :
    ∀ left,
      left ∈ centralPositiveHalfStates w hw K half →
      ∀ right,
        right ∈ centralPositiveHalfStates w hw K half →
        left ≠ right →
          haarInner left right ≈ 0

/-- **Constructed witness.**  The exact positive BF4 carrier now has a
normalized, faithful, all-spin five-holonomy character transform. -/
def canonicalBF4AllSpinCharacterTransform
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) :
    CentralPositiveBoundaryAllSpinCharacterTransform
      w hw K half where
  stateMode := bf4AllSpinMode K half
  expansion := bf4AllSpinExpansion K half
  boundaryWavefunction := bf4AllSpinWavefunction K half
  haarInner := fun left right =>
    fiveCharacterHaarPair
      (bf4AllSpinMode K half left)
      (bf4AllSpinMode K half right)
  mode_faithful := by
    intro left right hleft hright hmode
    exact bf4AllSpinMode_injective_on_positive
      hleft hright hmode
  synthesis := by
    intro state _ configuration
    exact bf4AllSpinExpansion_synthesizes
      K half state configuration
  haar_eq_mode := by
    intro left right _ _
    exact Q'.eqv_refl _
  boundary_normalized := by
    intro state _
    exact bf4AllSpinWavefunction_normalized
      K half state
  boundary_orthogonal := by
    intro left hleft right hright hne
    exact bf4AllSpinWavefunction_orthogonal
      hleft hright hne

/-! ## 4. The generalized operator is not a scalar Hessian -/

private def coordinateZero : Fin 5 := ⟨0, by decide⟩
private def coordinateOne : Fin 5 := ⟨1, by decide⟩

/-- The generalized operator `K^{-1}S` is not symmetric in the displayed
coordinate basis.  It is therefore not itself the Hessian of a scalar
Gaussian density; the genuine endpoint must retain the symmetric pair
`(K,S)` or perform a constructive square-root conjugation. -/
theorem generalizedA_not_symmetric :
    ¬ (∀ row column,
      generalizedA row column ≈
        generalizedA column row) := by
  intro hsymmetric
  have hbad := hsymmetric coordinateZero coordinateOne
  exact (by decide :
    ¬ (generalizedA coordinateZero coordinateOne ≈
      generalizedA coordinateOne coordinateZero)) hbad

end YMGap.Continuum.BF4FiveHolonomyNormalizedKernel

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4FiveHolonomyNormalizedKernel.centralFiveHeatKernelPacket_normalized
#print axioms YMGap.Continuum.BF4FiveHolonomyNormalizedKernel.centralFiveHeatKernelValue_eq_nestedPWExpansion
#print axioms YMGap.Continuum.BF4FiveHolonomyNormalizedKernel.centralFiveHeatKernelValue_symmetric
#print axioms YMGap.Continuum.BF4FiveHolonomyNormalizedKernel.edgeLabellingCode_injective_on_bounded
#print axioms YMGap.Continuum.BF4FiveHolonomyNormalizedKernel.bf4StateCode_injective_on_positive
#print axioms YMGap.Continuum.BF4FiveHolonomyNormalizedKernel.allSpinCharacterHaarPair_eq_delta
#print axioms YMGap.Continuum.BF4FiveHolonomyNormalizedKernel.bf4AllSpinExpansion_synthesizes
#print axioms YMGap.Continuum.BF4FiveHolonomyNormalizedKernel.bf4AllSpinMode_injective_on_positive
#print axioms YMGap.Continuum.BF4FiveHolonomyNormalizedKernel.bf4AllSpinWavefunction_normalized
#print axioms YMGap.Continuum.BF4FiveHolonomyNormalizedKernel.bf4AllSpinWavefunction_orthogonal
#print axioms YMGap.Continuum.BF4FiveHolonomyNormalizedKernel.canonicalBF4AllSpinCharacterTransform
#print axioms YMGap.Continuum.BF4FiveHolonomyNormalizedKernel.generalizedA_not_symmetric
