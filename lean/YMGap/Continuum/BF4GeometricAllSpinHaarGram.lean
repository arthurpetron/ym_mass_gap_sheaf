/-
# Exact geometric all-spin Haar--L2 Gram

The eighteen-chord BF4 contraction produces, for every (unbounded) face
labelling, a finite rational polynomial on the five transmitted
holonomies.  Distinct face labellings are not assumed orthogonal and the
internal recoupling expansion may contain signs.

This file forms arbitrary finite signed packets of those exact geometric
wavefunctions and proves positivity of their normalized fivefold-Haar
square.  Positivity is therefore obtained before any entrywise recoupling
claim: it is the product-Haar integral of one literal square.

The compact coupled-action endpoint has the analogous located
constructive-real positivity theorem in
`BF4CompactActionPhysicalLimit.compactPhysicalNegativeTaylorQuadraticLimit_nonnegative`.
Neither result by itself identifies the exact Wilson slab with the compact
Mehler reference; that common-action bridge remains separate.

## Axiom gate

Finite lists, exact `Q'` polynomial algebra, and the constructive
arbitrary-degree quaternion-Haar square theorem only.  No `Classical.*`,
`native_decide`, `sorry`, custom axiom, choice, or noncomputable
declaration.
-/

import YMGap.Continuum.BF4ReflectedAllSpinPeterWeylBridge
import YMGap.Continuum.SU2QuaternionArbitraryHaarPolynomialPositivity

namespace YMGap.Continuum.BF4GeometricAllSpinHaarGram

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ReflectedAllSpinPeterWeylBridge
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionArbitraryHaarPolynomialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Arbitrary finite all-spin packets -/

/-- A finite signed all-spin packet.  The spin labels themselves are
unbounded; finiteness belongs only to the chosen test packet. -/
abbrev GeometricAllSpinPacket :=
  List (Q' × EdgeLabelling)

/-- Literal linear combination of the geometric BF4 wavefunctions obtained
after exact integration of the eighteen non-transmitted chords. -/
def geometricAllSpinPacketWavefunction :
    GeometricAllSpinPacket → RatPoly
  | [] => polyZero
  | weightedState :: rest =>
      polyAdd
        (polySmul weightedState.1
          (geometricBF4WavefunctionOfState
            weightedState.2))
        (geometricAllSpinPacketWavefunction rest)

/-- Every exact geometric boundary wavefunction lives on precisely the five
transmitted quaternion blocks. -/
theorem geometricBF4WavefunctionOfState_supported_five
    (state : EdgeLabelling) :
    SupportedQuaternionBlocks 5
      (geometricBF4WavefunctionOfState state) := by
  intro term hterm
  rw [geometricBF4WavefunctionOfState_term_length
    state term hterm]
  omega

private theorem supported_polyAdd_five
    {left right : RatPoly}
    (hleft : SupportedQuaternionBlocks 5 left)
    (hright : SupportedQuaternionBlocks 5 right) :
    SupportedQuaternionBlocks 5
      (polyAdd left right) := by
  intro term hterm
  simp only [polyAdd, List.mem_append] at hterm
  rcases hterm with hterm | hterm
  · exact hleft term hterm
  · exact hright term hterm

private theorem supported_polySmul_five
    (coefficient : Q') {polynomial : RatPoly}
    (hsupport :
      SupportedQuaternionBlocks 5 polynomial) :
    SupportedQuaternionBlocks 5
      (polySmul coefficient polynomial) := by
  intro term hterm
  simp only [polySmul, List.mem_map] at hterm
  rcases hterm with ⟨source, hsource, rfl⟩
  exact hsupport source hsource

/-- Every finite signed all-spin packet remains on the same five-holonomy
carrier. -/
theorem geometricAllSpinPacketWavefunction_supported :
    ∀ packet : GeometricAllSpinPacket,
      SupportedQuaternionBlocks 5
        (geometricAllSpinPacketWavefunction packet)
  | [] => by
      intro term hterm
      exact False.elim (List.not_mem_nil hterm)
  | weightedState :: rest =>
      supported_polyAdd_five
        (supported_polySmul_five weightedState.1
          (geometricBF4WavefunctionOfState_supported_five
            weightedState.2))
        (geometricAllSpinPacketWavefunction_supported rest)

/-! ## 2. Certificate-free Haar--L2 positivity -/

private theorem bool_false_of_not_true
    {value : Bool} (hvalue : ¬ value = true) :
    value = false := by
  cases hcase : value with
  | false => rfl
  | true => exact (hvalue hcase).elim

private theorem exponentAt_drop_local
    (monomial : List Nat) :
    ∀ (offset index : Nat),
      exponentAt (monomial.drop offset) index =
        exponentAt monomial (offset + index)
  | 0, index => by
      simp [exponentAt]
  | offset + 1, index => by
      cases monomial with
      | nil => simp [exponentAt]
      | cons exponent rest =>
          have hindex :
              offset + 1 + index =
                (offset + index) + 1 := by
            omega
          rw [hindex]
          simp only [List.drop_succ_cons]
          unfold exponentAt
          simp only [List.getD_cons_succ]
          exact exponentAt_drop_local rest offset index

/-- The older explicit fivefold moment and the arbitrary-product Haar
moment are the same normalized functional. -/
theorem fivefoldHaarMono_equiv_quaternionHaarMono_five
    (monomial : List Nat) :
    fivefoldHaarMono monomial ≈
      quaternionHaarMono 5 monomial := by
  by_cases htail :
      allZero (monomial.drop 20) = true
  · simp only [fivefoldHaarMono, quaternionHaarMono,
      show 4 * 5 = 20 by decide, htail, if_true]
    simp only [quaternionHaarPrefix,
      exponentAt_drop_local, Nat.reduceAdd]
    exact Q'.mul_eqv_congr_left
      (sphereMoment4
        (exponentAt monomial 0)
        (exponentAt monomial 1)
        (exponentAt monomial 2)
        (exponentAt monomial 3))
      _ _
      (Q'.mul_eqv_congr_left
        (sphereMoment4
          (exponentAt monomial 4)
          (exponentAt monomial 5)
          (exponentAt monomial 6)
          (exponentAt monomial 7))
        _ _
        (Q'.mul_eqv_congr_left
          (sphereMoment4
            (exponentAt monomial 8)
            (exponentAt monomial 9)
            (exponentAt monomial 10)
            (exponentAt monomial 11))
          _ _
          (Q'.mul_eqv_congr_left
            (sphereMoment4
              (exponentAt monomial 12)
              (exponentAt monomial 13)
              (exponentAt monomial 14)
              (exponentAt monomial 15))
            _ _
            (Q'.eqv_symm
              (Q'.mul_one_eqv
                (sphereMoment4
                  (exponentAt monomial 16)
                  (exponentAt monomial 17)
                  (exponentAt monomial 18)
                  (exponentAt monomial 19)))))))
  · have hfalse :=
      bool_false_of_not_true htail
    simp [fivefoldHaarMono, quaternionHaarMono,
      show 4 * 5 = 20 by decide, hfalse]
    exact Q'.eqv_refl 0

/-- Equality of the explicit fivefold Haar functional with the uniform
arbitrary-block implementation, for every finite rational polynomial. -/
theorem fivefoldHaar_equiv_quaternionHaar_five :
    ∀ polynomial : RatPoly,
      fivefoldHaar polynomial ≈
        quaternionHaar 5 polynomial
  | [] => Q'.eqv_refl 0
  | term :: rest => by
      exact Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left term.2 _ _
          (fivefoldHaarMono_equiv_quaternionHaarMono_five
            term.1))
        (fivefoldHaar_equiv_quaternionHaar_five rest)

/-- Entry kernel of the exact geometric all-spin Haar Gram. -/
def geometricAllSpinHaarKernel
    (left right : EdgeLabelling) : Q' :=
  geometricFivefoldHaarPairing left right

/-- The exact geometric all-spin Haar entry kernel is symmetric without any
claim that distinct face labellings are orthogonal. -/
theorem geometricAllSpinHaarKernel_symmetric
    (left right : EdgeLabelling) :
    geometricAllSpinHaarKernel left right ≈
      geometricAllSpinHaarKernel right left := by
  unfold geometricAllSpinHaarKernel
    geometricFivefoldHaarPairing fivefoldHaarInner
  refine Q'.eqv_trans _
    (quaternionHaar 5
      (polyMul
        (geometricBF4WavefunctionOfState left)
        (geometricBF4WavefunctionOfState right))) _
    (fivefoldHaar_equiv_quaternionHaar_five
      (polyMul
        (geometricBF4WavefunctionOfState left)
        (geometricBF4WavefunctionOfState right))) ?_
  refine Q'.eqv_trans _
    (quaternionHaar 5
      (polyMul
        (geometricBF4WavefunctionOfState right)
        (geometricBF4WavefunctionOfState left))) _
    (quaternionHaar_polyMul_comm
      5
      (geometricBF4WavefunctionOfState left)
      (geometricBF4WavefunctionOfState right)) ?_
  exact Q'.eqv_symm
    (fivefoldHaar_equiv_quaternionHaar_five
      (polyMul
        (geometricBF4WavefunctionOfState right)
        (geometricBF4WavefunctionOfState left)))

/-- Every exact geometric all-spin state has nonnegative Haar norm. -/
theorem geometricAllSpinHaarKernel_diagonal_nonnegative
    (state : EdgeLabelling) :
    (0 : Q') ≤
      geometricAllSpinHaarKernel state state := by
  have hpositive :=
    quaternionHaar_square_nonnegative
      5
      (geometricBF4WavefunctionOfState state)
      (geometricBF4WavefunctionOfState_supported_five state)
  exact Q'.le_trans' _ _ _ hpositive
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (fivefoldHaar_equiv_quaternionHaar_five
          (polyMul
            (geometricBF4WavefunctionOfState state)
            (geometricBF4WavefunctionOfState state)))))

/-- Exact normalized five-holonomy Haar square of an arbitrary finite
all-spin packet. -/
def geometricAllSpinHaarQuadratic
    (packet : GeometricAllSpinPacket) : Q' :=
  quaternionHaar 5
    (polyMul
      (geometricAllSpinPacketWavefunction packet)
      (geometricAllSpinPacketWavefunction packet))

/-- **Geometric all-spin Haar Gram positivity.**

For every finite signed coefficient packet, including packets with arbitrary
high spin labels, the exact five-holonomy quadratic is nonnegative.  The
proof is the literal normalized-Haar integral of the packet square; no
orthogonality, entrywise sign, or positivity-certificate field is used. -/
theorem geometricAllSpinHaarQuadratic_nonnegative
    (packet : GeometricAllSpinPacket) :
    (0 : Q') ≤
      geometricAllSpinHaarQuadratic packet := by
  exact quaternionHaar_square_nonnegative
    5
    (geometricAllSpinPacketWavefunction packet)
    (geometricAllSpinPacketWavefunction_supported packet)

/-- The new arbitrary-packet quadratic is exactly the pre-existing
fivefold-Haar inner product of the packet with itself. -/
theorem geometricAllSpinHaarQuadratic_equiv_fivefoldInner
    (packet : GeometricAllSpinPacket) :
    geometricAllSpinHaarQuadratic packet ≈
      fivefoldHaarInner
        (geometricAllSpinPacketWavefunction packet)
        (geometricAllSpinPacketWavefunction packet) := by
  exact Q'.eqv_symm
    (fivefoldHaar_equiv_quaternionHaar_five
      (polyMul
        (geometricAllSpinPacketWavefunction packet)
        (geometricAllSpinPacketWavefunction packet)))

end YMGap.Continuum.BF4GeometricAllSpinHaarGram

#print axioms YMGap.Continuum.BF4GeometricAllSpinHaarGram.geometricBF4WavefunctionOfState_supported_five
#print axioms YMGap.Continuum.BF4GeometricAllSpinHaarGram.geometricAllSpinPacketWavefunction_supported
#print axioms YMGap.Continuum.BF4GeometricAllSpinHaarGram.fivefoldHaar_equiv_quaternionHaar_five
#print axioms YMGap.Continuum.BF4GeometricAllSpinHaarGram.geometricAllSpinHaarKernel_symmetric
#print axioms YMGap.Continuum.BF4GeometricAllSpinHaarGram.geometricAllSpinHaarKernel_diagonal_nonnegative
#print axioms YMGap.Continuum.BF4GeometricAllSpinHaarGram.geometricAllSpinHaarQuadratic_nonnegative
#print axioms YMGap.Continuum.BF4GeometricAllSpinHaarGram.geometricAllSpinHaarQuadratic_equiv_fivefoldInner
