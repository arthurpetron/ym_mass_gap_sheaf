/-
# Faraut windows on the full BF4 joint carrier and the exact AF depth budget

The fixed strong-coupling corridor used elsewhere in the BF4 development is
not uniform on an asymptotically-free trajectory.  Faraut's image formula
suggests the correct replacement: at each spacing retain a positive rational
one-factor floor and ceiling, and measure their projective cost by an integer
`bits` satisfying

    localCeiling ≤ 4^bits * localFloor.

This module proves the complete algebra downstream of that estimate.

* A literal product of the 23 retained BF4 factors has projective spread
  `4^(23*bits)`.
* The two-sided Perron comparison therefore has square cost bounded by
  `4^(46*bits)`.
* If the nonlinear spectral ratio is at most `1/4`, the explicit depth
  `46*bits+3` gives

      C_s^2 q_s^(m-2) ≤ 1/4 < 1.

The retained paths used by the physical specialization are built from
`WholeSlabJointCarrierCode`.  Hence a retained state contains the complete
coarse face-channel field and the shared-link fusion-witness assignment.
This is the enlarged carrier required by the binary-sheet counterexample;
no binary decomposition is assumed.

The genuinely analytic input has now been reduced to a quantitative Faraut
bit window at every AF scale, plus identification of the local completed
kernels with the physical joint-carrier factors.  Neither is manufactured
here.

## Constructivity

Finite lists, exact `Q'` powers, and approximation-wise `CReal` order only.
No `Classical.*`, `Real`, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.SU2FarautInteriorImageHarnack
import YMGap.Continuum.BF4CompletedRetainedConditionalOrder
import YMGap.Continuum.FiveHolonomyPerronCutoff
import YMGap.Continuum.BF4SU2OuterJointCarrierEnumeration
import YMGap.Continuum.BF4AFHeatSpacing

namespace YMGap.Continuum.BF4FarautJointCarrierAFBudget

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4CompletedHeatRetainedConsumer
open YMGap.Continuum.BF4CompletedRetainedConditionalOrder
open YMGap.Continuum.BF4GroupedFeynmanKacHarnack
open YMGap.Continuum.BF4RetainedKineticWindow
open YMGap.Continuum.BareAFDiagnostic
open YMGap.Continuum.BF4SU2OuterJointCarrierEnumeration
open YMGap.Continuum.BF4SU2OuterPositiveRowClosureReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiveHolonomyPerronCutoff
open YMGap.Continuum.SU2FarautInteriorImageHarnack

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Dynamic Faraut windows -/

/-- The rational floor produced by one Faraut image certificate. -/
def farautLocalFloor
    (prefactorFloor imageFloor : Q') : Q' :=
  prefactorFloor * imageFloor

/-- The rational ceiling produced by one Faraut image certificate. -/
def farautLocalCeiling
    (prefactorCeiling imageCeiling : Q') : Q' :=
  prefactorCeiling * imageCeiling

/-- A quantitative, spacing-dependent Faraut window.

The field is strictly weaker than assuming the desired BF4 contraction: it
only compares one local completed heat factor with its own positive floor.
All tensorization, conditional integration, and Perron powers are derived
below. -/
structure FarautBitWindow
    (prefactorFloor prefactorCeiling
      imageFloor imageCeiling : Q') : Type where
  bits : Nat
  prefactor_floor_pos : (0 : Q') < prefactorFloor
  image_floor_pos : (0 : Q') < imageFloor
  prefactor_ceiling_nonnegative :
    (0 : Q') ≤ prefactorCeiling
  image_ceiling_nonnegative :
    (0 : Q') ≤ imageCeiling
  local_ceiling_le_bit_cap :
    farautLocalCeiling prefactorCeiling imageCeiling ≤
      four ^ bits *
        farautLocalFloor prefactorFloor imageFloor

/-- The retained 23-factor projective spread associated with a local bit
cost. -/
def farautRetainedSpread (bits : Nat) : Q' :=
  four ^ (bits * bf4SpatialCycleCount)

/-- The square of the two-sided retained projective spread. -/
def farautPerronSquare (bits : Nat) : Q' :=
  farautRetainedSpread bits * farautRetainedSpread bits

/-- The exact lattice depth which pays the 46-bit Perron cost and leaves one
extra quarter power after subtracting the two endpoint buffers. -/
def farautRequiredDepth (bits : Nat) : Nat :=
  46 * bits + 3

private theorem pow_pos_local {value : Q'}
    (value_pos : (0 : Q') < value) :
    ∀ exponent : Nat, (0 : Q') < value ^ exponent
  | 0 => by
      show (0 : Q') < (1 : Q')
      decide
  | exponent + 1 =>
      Q'.mul_pos value_pos
        (pow_pos_local value_pos exponent)

private theorem one_le_pow_local {value : Q'}
    (one_le_value : (1 : Q') ≤ value) :
    ∀ exponent : Nat, (1 : Q') ≤ value ^ exponent
  | 0 => Q'.le_refl' 1
  | exponent + 1 => by
      have hvalue_nonnegative : (0 : Q') ≤ value :=
        Q'.le_trans' _ _ _ Q'.zero_le_one one_le_value
      have hscaled :
          (1 : Q') * 1 ≤ value * value ^ exponent :=
        Q'.mul_le_mul_of_nonneg
          one_le_value
          (one_le_pow_local one_le_value exponent)
          hvalue_nonnegative
          Q'.zero_le_one
      exact Q'.le_trans' _ _ _
        (Q'.ge_of_eqv (Q'.one_mul_eqv 1))
        hscaled

private theorem mul_pow_eqv_local (left right : Q') :
    ∀ exponent : Nat,
      (left * right) ^ exponent ≈
        left ^ exponent * right ^ exponent
  | 0 => Q'.eqv_symm (Q'.mul_one_eqv 1)
  | exponent + 1 => by
      have hinductive := mul_pow_eqv_local left right exponent
      show
        (left * right) * (left * right) ^ exponent ≈
          (left * left ^ exponent) *
            (right * right ^ exponent)
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left
          (left * right) _ _ hinductive) ?_
      calc
        (left * right) *
              (left ^ exponent * right ^ exponent) ≈
            left *
              (right *
                (left ^ exponent * right ^ exponent)) :=
          Q'.mul_assoc_eqv _ _ _
        _ ≈ left *
              ((right * left ^ exponent) *
                right ^ exponent) :=
          Q'.mul_eqv_congr_left _ _ _
            (Q'.eqv_symm
              (Q'.mul_assoc_eqv
                right (left ^ exponent)
                (right ^ exponent)))
        _ ≈ left *
              ((left ^ exponent * right) *
                right ^ exponent) :=
          Q'.mul_eqv_congr_left _ _ _
            (Q'.mul_eqv_congr_right _ _
              (right ^ exponent)
              (Q'.mul_comm_eqv
                right (left ^ exponent)))
        _ ≈ left *
              (left ^ exponent *
                (right * right ^ exponent)) :=
          Q'.mul_eqv_congr_left _ _ _
            (Q'.mul_assoc_eqv
              (left ^ exponent) right
              (right ^ exponent))
        _ ≈ (left * left ^ exponent) *
              (right * right ^ exponent) :=
          Q'.eqv_symm
            (Q'.mul_assoc_eqv _ _ _)

/-- A one-factor bit cap tensorizes to the exact 23-factor retained spread. -/
theorem faraut_product_window_cap
    {prefactorFloor prefactorCeiling
      imageFloor imageCeiling : Q'}
    (window :
      FarautBitWindow
        prefactorFloor prefactorCeiling
        imageFloor imageCeiling)
    (localCeiling_nonnegative :
      (0 : Q') ≤
        farautLocalCeiling prefactorCeiling imageCeiling) :
    farautLocalCeiling prefactorCeiling imageCeiling ^
        bf4SpatialCycleCount ≤
      farautRetainedSpread window.bits *
        (farautLocalFloor prefactorFloor imageFloor ^
          bf4SpatialCycleCount) := by
  have hpowered :=
    FiveHolonomyPerronCutoff.pow_base_mono
      (farautLocalCeiling prefactorCeiling imageCeiling)
      (four ^ window.bits *
        farautLocalFloor prefactorFloor imageFloor)
      localCeiling_nonnegative
      window.local_ceiling_le_bit_cap
      bf4SpatialCycleCount
  have hfactor :
      (four ^ window.bits *
          farautLocalFloor prefactorFloor imageFloor) ^
          bf4SpatialCycleCount ≈
        farautRetainedSpread window.bits *
          (farautLocalFloor prefactorFloor imageFloor ^
            bf4SpatialCycleCount) := by
    refine Q'.eqv_trans _ _ _
      (mul_pow_eqv_local
        (four ^ window.bits)
        (farautLocalFloor prefactorFloor imageFloor)
        bf4SpatialCycleCount) ?_
    unfold farautRetainedSpread
    exact Q'.mul_eqv_congr_right _ _
      (farautLocalFloor prefactorFloor imageFloor ^
        bf4SpatialCycleCount)
      (FiveHolonomyPerronCutoff.pow_mul_eqv
        four window.bits bf4SpatialCycleCount)
  exact Q'.le_trans' _ _ _ hpowered
    (Q'.le_of_eqv hfactor)

/-! ## 2. Completed retained products and conditional integration -/

/-- Dynamic completed retained Harnack data.  Unlike the older fixed-corridor
carrier, its rational floor, ceiling, and spread may vary with spacing. -/
structure DynamicCompletedRetainedHarnackData
    {Source Target State : Type}
    (paths : List (List State))
    (kineticWeight : Source → Target → List State → CReal)
    (sources : List Source) (targets : List Target) : Type where
  lower : Q'
  upper : Q'
  spread : Q'
  lower_pos : (0 : Q') < lower
  one_le_spread : (1 : Q') ≤ spread
  kinetic_nonnegative :
    ∀ source, source ∈ sources →
      ∀ target, target ∈ targets →
        ∀ path, path ∈ paths →
          ExpPos.geRat (kineticWeight source target path) 0
  lower_bound :
    ∀ source, source ∈ sources →
      ∀ target, target ∈ targets →
        ∀ path, path ∈ paths →
          ExpPos.geRat (kineticWeight source target path) lower
  upper_bound :
    ∀ source, source ∈ sources →
      ∀ target, target ∈ targets →
        ∀ path, path ∈ paths →
          CReal.leRat (kineticWeight source target path) upper
  pathwiseDomination :
    ∀ first, first ∈ sources →
      ∀ second, second ∈ sources →
        ∀ target, target ∈ targets →
          ∀ path, path ∈ paths →
            CReal.leEv
              (kineticWeight first target path)
              (CReal.mul
                (CReal.ofQ' spread)
                (kineticWeight second target path))

private theorem leEv_of_leRat_local
    {value : CReal} {upper : Q'}
    (h : CReal.leRat value upper) :
    CReal.leEv value (CReal.ofQ' upper) := by
  intro ε hε
  exact h ε hε

private theorem leEv_of_geRat_local
    {value : CReal} {lower : Q'}
    (h : ExpPos.geRat value lower) :
    CReal.leEv (CReal.ofQ' lower) value := by
  intro ε hε
  exact h ε hε

private theorem rationalWindow_leEv
    {lower upper spread : Q'}
    {first second : CReal}
    (spread_nonnegative : (0 : Q') ≤ spread)
    (window_order : upper ≤ spread * lower)
    (first_upper : CReal.leRat first upper)
    (second_lower : ExpPos.geRat second lower) :
    CReal.leEv first
      (CReal.mul (CReal.ofQ' spread) second) := by
  have hconstant :
      CReal.leEv
        (CReal.ofQ' upper)
        (CReal.ofQ' (spread * lower)) := by
    intro ε hε
    refine ⟨0, fun _ _ => ?_⟩
    exact Q'.le_trans' _ _ _ window_order
      (Q'.add_le_self_of_nonneg
        (spread * lower) ε (Q'.le_of_lt hε))
  have hscaled :
      ExpPos.geRat
        (CReal.mul (CReal.ofQ' spread) second)
        (spread * lower) :=
    YMGap.Constructive.SU3CharFactor.geRat_smul_nonneg
      spread_nonnegative second_lower
  exact CReal.leEv_trans
    (CReal.leEv_trans
      (leEv_of_leRat_local first_upper)
      hconstant)
    (leEv_of_geRat_local hscaled)

/-- Faraut image certificates on all literal local factors construct the
dynamic 23-factor retained Harnack datum. -/
def farautCompletedRetainedHarnack
    {Source Target State Factor : Type}
    (paths : List (List State))
    (factors : List Factor)
    (factor_count :
      factors.length = bf4SpatialCycleCount)
    (kernel :
      Source → Target → List State → Factor → CReal)
    (sources : List Source) (targets : List Target)
    (prefactorFloor prefactorCeiling
      imageFloor imageCeiling : Q')
    (certificates :
      ∀ source, source ∈ sources →
        ∀ target, target ∈ targets →
          ∀ path, path ∈ paths →
            ∀ factor, factor ∈ factors →
              FarautInteriorImageCertificate
                (kernel source target path factor)
                prefactorFloor prefactorCeiling
                imageFloor imageCeiling)
    (window :
      FarautBitWindow
        prefactorFloor prefactorCeiling
        imageFloor imageCeiling) :
    DynamicCompletedRetainedHarnackData
      paths
      (fun source target path =>
        completedFactorProduct
          (kernel source target path) factors)
      sources targets := by
  let lower :=
    farautLocalFloor prefactorFloor imageFloor
  let upper :=
    farautLocalCeiling prefactorCeiling imageCeiling
  let spread :=
    farautRetainedSpread window.bits
  have hfloor_pos :
      (0 : Q') < lower := by
    exact Q'.mul_pos
      window.prefactor_floor_pos
      window.image_floor_pos
  have hceiling_nonnegative :
      (0 : Q') ≤ upper := by
    exact Q'.mul_nonneg _ _
      window.prefactor_ceiling_nonnegative
      window.image_ceiling_nonnegative
  exact {
    lower := lower ^ bf4SpatialCycleCount
    upper := upper ^ bf4SpatialCycleCount
    spread := spread
    lower_pos := by
      unfold lower
      exact pow_pos_local hfloor_pos bf4SpatialCycleCount
    one_le_spread := by
      unfold spread farautRetainedSpread
      exact one_le_pow_local
        (by decide)
        (window.bits * bf4SpatialCycleCount)
    kinetic_nonnegative := by
      intro source hsource target htarget path hpath
      have hlower :=
        completedFactorProduct_lower_on
          (kernel source target path)
          lower
          (Q'.le_of_lt hfloor_pos)
          factors
          (fun factor hfactor =>
            (certificates source hsource
              target htarget path hpath
              factor hfactor).kernel_ge_floor)
      exact ExpPos.geRat_mono hlower
        (Q'.pow_nonneg lower
          (Q'.le_of_lt hfloor_pos) factors.length)
    lower_bound := by
      intro source hsource target htarget path hpath
      have hlower :=
        completedFactorProduct_lower_on
          (kernel source target path)
          lower
          (Q'.le_of_lt hfloor_pos)
          factors
          (fun factor hfactor =>
            (certificates source hsource
              target htarget path hpath
              factor hfactor).kernel_ge_floor)
      rw [factor_count] at hlower
      exact hlower
    upper_bound := by
      intro source hsource target htarget path hpath
      have hcert := certificates source hsource
        target htarget path hpath
      have hlocal_nonnegative :
          ∀ factor, factor ∈ factors →
            ExpPos.geRat
              (kernel source target path factor) lower :=
        fun factor hfactor =>
          (hcert factor hfactor).kernel_ge_floor
      have hupper :=
        completedFactorProduct_upper_on
          (kernel source target path)
          lower upper
          (Q'.le_of_lt hfloor_pos)
          hceiling_nonnegative
          factors
          hlocal_nonnegative
          (fun factor hfactor =>
            (hcert factor hfactor).kernel_le_ceiling)
      rw [factor_count] at hupper
      exact hupper
    pathwiseDomination := by
      intro first hfirst second hsecond target htarget path hpath
      have hfirstUpper :=
        completedFactorProduct_upper_on
          (kernel first target path)
          lower upper
          (Q'.le_of_lt hfloor_pos)
          hceiling_nonnegative
          factors
          (fun factor hfactor =>
            (certificates first hfirst target htarget
              path hpath factor hfactor).kernel_ge_floor)
          (fun factor hfactor =>
            (certificates first hfirst target htarget
              path hpath factor hfactor).kernel_le_ceiling)
      have hsecondLower :=
        completedFactorProduct_lower_on
          (kernel second target path)
          lower
          (Q'.le_of_lt hfloor_pos)
          factors
          (fun factor hfactor =>
            (certificates second hsecond target htarget
              path hpath factor hfactor).kernel_ge_floor)
      rw [factor_count] at hfirstUpper hsecondLower
      exact rationalWindow_leEv
        (Q'.pow_nonneg four (by decide)
          (window.bits * bf4SpatialCycleCount))
        (faraut_product_window_cap window
          hceiling_nonnegative)
        hfirstUpper hsecondLower
  }

private theorem dynamicPotentialSpreadSwap
    (potentialWeight spread : Q') (value : CReal) :
    CReal.Equiv
      (CReal.mul
        (CReal.ofQ' potentialWeight)
        (CReal.mul
          (CReal.ofQ' spread) value))
      (CReal.mul
        (CReal.ofQ' spread)
        (CReal.mul
          (CReal.ofQ' potentialWeight) value)) :=
  SumOfSquares.Equiv_of_approx_eqv
    (fun n =>
      Q'.eqv_trans _ _ _
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv
            potentialWeight spread
            (value.approx n)))
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right
            (potentialWeight * spread)
            (spread * potentialWeight)
            (value.approx n)
            (Q'.mul_comm_eqv
              potentialWeight spread))
          (Q'.mul_assoc_eqv
            spread potentialWeight
            (value.approx n))))

/-- A common nonnegative interior spatial weight preserves a dynamic Faraut
pathwise comparison with no path-length loss. -/
theorem dynamicCompletedFeynmanKac_pathwiseDomination
    {Source Target State : Type}
    (paths : List (List State))
    (kineticWeight :
      Source → Target → List State → CReal)
    (potential : State → Q')
    (potential_nonnegative :
      ∀ state, (0 : Q') ≤ potential state)
    (sources : List Source) (targets : List Target)
    (harnack :
      DynamicCompletedRetainedHarnackData
        paths kineticWeight sources targets)
    (first : Source) (hfirst : first ∈ sources)
    (second : Source) (hsecond : second ∈ sources)
    (target : Target) (htarget : target ∈ targets)
    (path : List State) (hpath : path ∈ paths) :
    CReal.leEv
      (completedRetainedFeynmanKacWeight
        kineticWeight potential first target path)
      (CReal.mul
        (CReal.ofQ' harnack.spread)
        (completedRetainedFeynmanKacWeight
          kineticWeight potential second target path)) := by
  let potentialWeight :=
    pathPotentialProduct potential path
  have hpotential :
      (0 : Q') ≤ potentialWeight :=
    pathPotentialProduct_nonnegative
      potential_nonnegative path
  have hkinetic :=
    harnack.pathwiseDomination
      first hfirst second hsecond
      target htarget path hpath
  have hscaled :=
    CReal.leEv_smul_nonneg
      hpotential hkinetic
  exact
    (CReal.leEv_congr
      (CReal.Equiv.refl _)
      (dynamicPotentialSpreadSwap
        potentialWeight harnack.spread
        (kineticWeight second target path))).mp
      hscaled

/-- Finite conditional integration over the complete retained carrier
preserves the dynamic Faraut spread exactly. -/
theorem dynamicCompletedConditionalPushforward_domination
    {Source Target State : Type}
    (paths : List (List State))
    (kineticWeight :
      Source → Target → List State → CReal)
    (potential : State → Q')
    (potential_nonnegative :
      ∀ state, (0 : Q') ≤ potential state)
    (sources : List Source) (targets : List Target)
    (harnack :
      DynamicCompletedRetainedHarnackData
        paths kineticWeight sources targets)
    (first : Source) (hfirst : first ∈ sources)
    (second : Source) (hsecond : second ∈ sources)
    (target : Target) (htarget : target ∈ targets) :
    CReal.leEv
      (completedConditionalPathPushforward
        paths kineticWeight potential first target)
      (CReal.mul
        (CReal.ofQ' harnack.spread)
        (completedConditionalPathPushforward
          paths kineticWeight potential second target)) := by
  have hsum :
      CReal.leEv
        (completedConditionalPathPushforward
          paths kineticWeight potential first target)
        (completedPathSum
          (fun path =>
            CReal.mul
              (CReal.ofQ' harnack.spread)
              (completedRetainedFeynmanKacWeight
                kineticWeight potential second target path))
          paths) :=
    completedPathSum_mono_on
      (completedRetainedFeynmanKacWeight
        kineticWeight potential first target)
      (fun path =>
        CReal.mul
          (CReal.ofQ' harnack.spread)
          (completedRetainedFeynmanKacWeight
            kineticWeight potential second target path))
      paths
      (fun path hpath =>
        dynamicCompletedFeynmanKac_pathwiseDomination
          paths kineticWeight potential
          potential_nonnegative sources targets harnack
          first hfirst second hsecond
          target htarget path hpath)
  exact
    (CReal.leEv_congr
      (CReal.Equiv.refl _)
      (completedPathSum_const_mul
        (CReal.ofQ' harnack.spread)
        (completedRetainedFeynmanKacWeight
          kineticWeight potential second target)
        paths)).mp
      hsum

/-! ## 3. The full joint face-channel/shared-intertwiner retained carrier -/

/-- The complete finite joint carrier, retained as singleton paths so that
conditional integration can forget it only after the pathwise comparison.
Every state still contains its face-channel field and shared-link fusion
witness. -/
def wholeSlabJointCarrierPaths
    (S : CompactDualFiniteBlockRemainder.SlabScalePair)
    (fineState :
      SU2FundamentalPentagonFiniteGraph.EdgeLabelling) :
    List (List (WholeSlabJointCarrierCode S fineState)) :=
  (wholeSlabJointCarrierCodes S fineState).map
    (fun code => [code])

/-- Every enumerated joint code occurs as its own retained path. -/
theorem singleton_mem_wholeSlabJointCarrierPaths
    {S : CompactDualFiniteBlockRemainder.SlabScalePair}
    {fineState :
      SU2FundamentalPentagonFiniteGraph.EdgeLabelling}
    {code : WholeSlabJointCarrierCode S fineState}
    (hcode :
      code ∈ wholeSlabJointCarrierCodes S fineState) :
    [code] ∈ wholeSlabJointCarrierPaths S fineState :=
  List.mem_map.mpr ⟨code, hcode, rfl⟩

/-- The retained joint state exposes the shared-link fusion assignment; it
is not a binary-sheet quotient. -/
def retainedJointFusionWitness
    {S : CompactDualFiniteBlockRemainder.SlabScalePair}
    {fineState :
      SU2FundamentalPentagonFiniteGraph.EdgeLabelling}
    (code : WholeSlabJointCarrierCode S fineState) :=
  code.coarseFusionWitness

/-- Faraut certificates on the literal full joint carrier construct the
dynamic retained Harnack datum without any binary-sheet projection. -/
def wholeSlabFarautCompletedRetainedHarnack
    {Source Target Factor : Type}
    {S : CompactDualFiniteBlockRemainder.SlabScalePair}
    {fineState :
      SU2FundamentalPentagonFiniteGraph.EdgeLabelling}
    (factors : List Factor)
    (factor_count :
      factors.length = bf4SpatialCycleCount)
    (kernel :
      Source → Target →
        List (WholeSlabJointCarrierCode S fineState) →
          Factor → CReal)
    (sources : List Source) (targets : List Target)
    (prefactorFloor prefactorCeiling
      imageFloor imageCeiling : Q')
    (certificates :
      ∀ source, source ∈ sources →
        ∀ target, target ∈ targets →
          ∀ path,
            path ∈ wholeSlabJointCarrierPaths S fineState →
            ∀ factor, factor ∈ factors →
              FarautInteriorImageCertificate
                (kernel source target path factor)
                prefactorFloor prefactorCeiling
                imageFloor imageCeiling)
    (window :
      FarautBitWindow
        prefactorFloor prefactorCeiling
        imageFloor imageCeiling) :
    DynamicCompletedRetainedHarnackData
      (wholeSlabJointCarrierPaths S fineState)
      (fun source target path =>
        completedFactorProduct
          (kernel source target path) factors)
      sources targets :=
  farautCompletedRetainedHarnack
    (wholeSlabJointCarrierPaths S fineState)
    factors factor_count kernel sources targets
    prefactorFloor prefactorCeiling
    imageFloor imageCeiling
    certificates window

/-- Conditional integration over the literal joint face-channel and
shared-intertwiner carrier preserves the Faraut projective spread exactly. -/
theorem wholeSlabFarautConditionalPushforward_domination
    {Source Target Factor : Type}
    {S : CompactDualFiniteBlockRemainder.SlabScalePair}
    {fineState :
      SU2FundamentalPentagonFiniteGraph.EdgeLabelling}
    (factors : List Factor)
    (factor_count :
      factors.length = bf4SpatialCycleCount)
    (kernel :
      Source → Target →
        List (WholeSlabJointCarrierCode S fineState) →
          Factor → CReal)
    (potential :
      WholeSlabJointCarrierCode S fineState → Q')
    (potential_nonnegative :
      ∀ state, (0 : Q') ≤ potential state)
    (sources : List Source) (targets : List Target)
    (prefactorFloor prefactorCeiling
      imageFloor imageCeiling : Q')
    (certificates :
      ∀ source, source ∈ sources →
        ∀ target, target ∈ targets →
          ∀ path,
            path ∈ wholeSlabJointCarrierPaths S fineState →
            ∀ factor, factor ∈ factors →
              FarautInteriorImageCertificate
                (kernel source target path factor)
                prefactorFloor prefactorCeiling
                imageFloor imageCeiling)
    (window :
      FarautBitWindow
        prefactorFloor prefactorCeiling
        imageFloor imageCeiling)
    (first : Source) (hfirst : first ∈ sources)
    (second : Source) (hsecond : second ∈ sources)
    (target : Target) (htarget : target ∈ targets) :
    CReal.leEv
      (completedConditionalPathPushforward
        (wholeSlabJointCarrierPaths S fineState)
        (fun source target path =>
          completedFactorProduct
            (kernel source target path) factors)
        potential first target)
      (CReal.mul
        (CReal.ofQ'
          (farautRetainedSpread window.bits))
        (completedConditionalPathPushforward
          (wholeSlabJointCarrierPaths S fineState)
          (fun source target path =>
            completedFactorProduct
              (kernel source target path) factors)
          potential second target)) := by
  let harnack :=
    wholeSlabFarautCompletedRetainedHarnack
      factors factor_count kernel sources targets
      prefactorFloor prefactorCeiling
      imageFloor imageCeiling certificates window
  exact dynamicCompletedConditionalPushforward_domination
    (wholeSlabJointCarrierPaths S fineState)
    (fun source target path =>
      completedFactorProduct
        (kernel source target path) factors)
    potential potential_nonnegative
    sources targets harnack
    first hfirst second hsecond target htarget

/-- Positive weighting and conditional summation preserve every already
formed nonnegative Gram quadratic on the full joint carrier.  This is the
safe CP/Loewner-order conclusion: positivity is asserted after the complete
shared-intertwiner channel has been retained, never inferred from scalar
entrywise order alone. -/
theorem wholeSlabJointCarrierQuadratic_nonnegative
    {S : CompactDualFiniteBlockRemainder.SlabScalePair}
    {fineState :
      SU2FundamentalPentagonFiniteGraph.EdgeLabelling}
    (pathWeight :
      List (WholeSlabJointCarrierCode S fineState) → Q')
    (pathWeight_nonnegative :
      ∀ path,
        path ∈ wholeSlabJointCarrierPaths S fineState →
          (0 : Q') ≤ pathWeight path)
    (pathQuadratic :
      List (WholeSlabJointCarrierCode S fineState) → CReal)
    (pathQuadratic_nonnegative :
      ∀ path,
        path ∈ wholeSlabJointCarrierPaths S fineState →
          ExpPos.geRat (pathQuadratic path) 0) :
    ExpPos.geRat
      (completedPathSum
        (fun path =>
          CReal.mul
            (CReal.ofQ' (pathWeight path))
            (pathQuadratic path))
        (wholeSlabJointCarrierPaths S fineState))
      0 :=
  completedConditionalQuadratic_nonnegative
    (wholeSlabJointCarrierPaths S fineState)
    pathWeight pathWeight_nonnegative
    pathQuadratic pathQuadratic_nonnegative

/-! ## 4. Exact spacing-uniform Perron budget -/

/-- The square of the retained Faraut spread is exactly bounded by the
`46*bits` fourth-power cap. -/
theorem farautPerronSquare_le_cap (bits : Nat) :
    farautPerronSquare bits ≤ four ^ (46 * bits) := by
  apply Q'.le_of_eqv
  unfold farautPerronSquare farautRetainedSpread
  have hmul :
      bits * bf4SpatialCycleCount +
        bits * bf4SpatialCycleCount = 46 * bits := by
    unfold bf4SpatialCycleCount
    omega
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (Q'.pow_add_eqv four
        (bits * bf4SpatialCycleCount)
        (bits * bf4SpatialCycleCount)))
    (by rw [hmul]; exact Q'.eqv_refl _)

/-- The required depth leaves exactly `46*bits+1` kinetic powers after the
two endpoint buffers. -/
theorem farautRequiredDepth_sub_two (bits : Nat) :
    farautRequiredDepth bits - 2 = 46 * bits + 1 := by
  unfold farautRequiredDepth
  omega

/-- **Spacing-uniform Faraut/Perron contraction.**  Once the nonlinear
five-holonomy ratio is at most `1/4`, the depth selected from the local
Faraut bit cost proves the desired strict inequality. -/
theorem faraut_perron_requiredDepth_strict
    (bits : Nat) (qS : Q')
    (qS_nonnegative : (0 : Q') ≤ qS)
    (qS_le_quarter : qS ≤ quarter) :
    farautPerronSquare bits *
      qS ^ (farautRequiredDepth bits - 2) < 1 := by
  have hcap := farautPerronSquare_le_cap bits
  have hqpow :
      (0 : Q') ≤
        qS ^ (farautRequiredDepth bits - 2) :=
    Q'.pow_nonneg qS qS_nonnegative _
  have hproduct :
      farautPerronSquare bits *
          qS ^ (farautRequiredDepth bits - 2) ≤
        four ^ (46 * bits) *
          qS ^ (farautRequiredDepth bits - 2) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      hcap hqpow
  have hquarter :
      four ^ (46 * bits) *
          qS ^ (farautRequiredDepth bits - 2) ≤
        quarter := by
    apply fourPow_mul_qPow_le_quarter
      qS_nonnegative qS_le_quarter
      (46 * bits)
      (farautRequiredDepth bits - 2)
    rw [farautRequiredDepth_sub_two]
    exact Nat.le_refl _
  exact Q'.lt_of_le_of_lt
    (Q'.le_trans' _ _ _ hproduct hquarter)
    (by decide)

/-- Any physical source-target depth above the explicit Faraut requirement
inherits the same strict contraction.  This is the direct form of
`C_{s(a)}^2 q_{s(a)}^(m(a,L)-2) < 1`. -/
theorem faraut_perron_of_available_depth
    (bits : Nat) (qS : Q') (m : Nat)
    (qS_nonnegative : (0 : Q') ≤ qS)
    (qS_le_quarter : qS ≤ quarter)
    (depth_available :
      farautRequiredDepth bits ≤ m) :
    farautPerronSquare bits *
      qS ^ (m - 2) < 1 := by
  have hcap := farautPerronSquare_le_cap bits
  have hqpow :
      (0 : Q') ≤ qS ^ (m - 2) :=
    Q'.pow_nonneg qS qS_nonnegative _
  have hproduct :
      farautPerronSquare bits * qS ^ (m - 2) ≤
        four ^ (46 * bits) * qS ^ (m - 2) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      hcap hqpow
  have hdepth :
      46 * bits + 1 ≤ m - 2 := by
    unfold farautRequiredDepth at depth_available
    omega
  have hquarter :
      four ^ (46 * bits) * qS ^ (m - 2) ≤
        quarter :=
    fourPow_mul_qPow_le_quarter
      qS_nonnegative qS_le_quarter
      (46 * bits) (m - 2) hdepth
  exact Q'.lt_of_le_of_lt
    (Q'.le_trans' _ _ _ hproduct hquarter)
    (by decide)

/-- A family of spacing-dependent Faraut bit costs therefore gives the
strict Perron inequality at every scale, with no uniform bound on `bits`
itself.  Only the physical depth must track the explicit required depth. -/
theorem faraut_perron_family_strict
    (bits : Nat → Nat) (qS : Nat → Q')
    (qS_nonnegative :
      ∀ scale, (0 : Q') ≤ qS scale)
    (qS_le_quarter :
      ∀ scale, qS scale ≤ quarter) :
    ∀ scale,
      farautPerronSquare (bits scale) *
        qS scale ^
          (farautRequiredDepth (bits scale) - 2) < 1 :=
  fun scale =>
    faraut_perron_requiredDepth_strict
      (bits scale) (qS scale)
      (qS_nonnegative scale)
      (qS_le_quarter scale)

/-! ## 5. AF spacing pays a growing Faraut bit cost in fixed physical length -/

/-- A scale family of Faraut bit costs whose product with the physical heat
argument remains bounded.  This is the exact constructive form of the
analytic growth estimate `bits(t) = O(1/t)` suggested by Faraut's Gaussian
images. -/
structure FarautAFBitGrowth
    (E : AFEnvelope)
    (coupling : Nat → Q')
    (bits : Nat → Nat) : Type where
  costCeiling : Q'
  costCeiling_nonnegative : (0 : Q') ≤ costCeiling
  coupling_pos :
    ∀ scale, (0 : Q') < coupling scale
  coupling_le :
    ∀ scale, coupling scale ≤ E.g₁
  bit_heat_cost :
    ∀ scale,
      Q'.ofNat (bits scale) *
          (BF4AFHeatSpacing.quarter *
            E.t (coupling scale)) ≤
        costCeiling

/-- The per-scale Faraut windows and their AF heat-cost control are tied to
the same bit function.  This prevents using a cheap unrelated bit schedule
to pay for a more expensive analytic window. -/
structure FarautAFWindowFamily
    (E : AFEnvelope)
    (coupling : Nat → Q')
    (prefactorFloor prefactorCeiling
      imageFloor imageCeiling : Nat → Q') : Type where
  window :
    ∀ scale,
      FarautBitWindow
        (prefactorFloor scale)
        (prefactorCeiling scale)
        (imageFloor scale)
        (imageCeiling scale)
  growth :
    FarautAFBitGrowth E coupling
      (fun scale => (window scale).bits)

/-- **AF/Faraut physical-length cancellation.**  If the Faraut Harnack bit
cost grows at most like `1/t`, then the `46*bits` lattice steps required by
the Perron comparison occupy uniformly bounded physical length:

`κ · (46 bits · a) ≤ 46 · costCeiling`,

where `κ = αΛ/(4C)` is the positive BF4 heat/spacing rate derived from the
`AFEnvelope`.  Thus a diverging label/Harnack cutoff is compatible with one
fixed physical cylinder; no spacing-independent bound on `bits` is needed. -/
theorem af_faraut_core_physical_length
    (E : AFEnvelope)
    (g : Q') (hg : (0 : Q') < g) (hgle : g ≤ E.g₁)
    (bits : Nat) (costCeiling : Q')
    (bit_heat_cost :
      Q'.ofNat bits *
          (BF4AFHeatSpacing.quarter * E.t g) ≤
        costCeiling) :
    BF4AFHeatSpacing.heatSpacingRate E *
        (Q'.ofNat (46 * bits) * E.a g) ≤
      Q'.ofNat 46 * costCeiling := by
  have hheat :=
    BF4AFHeatSpacing.heat_time_ge_rate_mul_spacing
      E g hg hgle
  have hnat_nonnegative :
      (0 : Q') ≤ Q'.ofNat (46 * bits) := by
    exact HeatKernelRGStep.zero_le_ofNat _
  have hscaled :
      Q'.ofNat (46 * bits) *
          (BF4AFHeatSpacing.heatSpacingRate E * E.a g) ≤
        Q'.ofNat (46 * bits) *
          (BF4AFHeatSpacing.quarter * E.t g) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      hheat hnat_nonnegative
  have hleft :
      (BF4AFHeatSpacing.heatSpacingRate E *
          (Q'.ofNat (46 * bits) * E.a g)) ≈
        Q'.ofNat (46 * bits) *
          (BF4AFHeatSpacing.heatSpacingRate E * E.a g) := by
    calc
      BF4AFHeatSpacing.heatSpacingRate E *
            (Q'.ofNat (46 * bits) * E.a g) ≈
          (BF4AFHeatSpacing.heatSpacingRate E *
            Q'.ofNat (46 * bits)) * E.a g :=
        Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
      _ ≈
          (Q'.ofNat (46 * bits) *
            BF4AFHeatSpacing.heatSpacingRate E) * E.a g :=
        Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_comm_eqv
            (BF4AFHeatSpacing.heatSpacingRate E)
            (Q'.ofNat (46 * bits)))
      _ ≈
          Q'.ofNat (46 * bits) *
            (BF4AFHeatSpacing.heatSpacingRate E * E.a g) :=
        Q'.mul_assoc_eqv _ _ _
  have hright :
      (Q'.ofNat (46 * bits) *
          (BF4AFHeatSpacing.quarter * E.t g)) ≈
        Q'.ofNat 46 *
          (Q'.ofNat bits *
            (BF4AFHeatSpacing.quarter * E.t g)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right
        (Q'.ofNat (46 * bits))
        (Q'.ofNat 46 * Q'.ofNat bits)
        (BF4AFHeatSpacing.quarter * E.t g)
        (YMGap.Constructive.SU3CharFactor.ofNat_mul_eqv
          46 bits)) ?_
    exact Q'.mul_assoc_eqv _ _ _
  have hcost :
      Q'.ofNat 46 *
          (Q'.ofNat bits *
            (BF4AFHeatSpacing.quarter * E.t g)) ≤
        Q'.ofNat 46 * costCeiling :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      bit_heat_cost (HeatKernelRGStep.zero_le_ofNat 46)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hscaled
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv hright) hcost))

/-- The preceding physical-length estimate holds uniformly along every
coupling family carrying a `FarautAFBitGrowth` witness. -/
theorem faraut_af_family_core_length_uniform
    {E : AFEnvelope}
    {coupling : Nat → Q'} {bits : Nat → Nat}
    (growth : FarautAFBitGrowth E coupling bits) :
    ∀ scale,
      BF4AFHeatSpacing.heatSpacingRate E *
          (Q'.ofNat (46 * bits scale) *
            E.a (coupling scale)) ≤
        Q'.ofNat 46 * growth.costCeiling :=
  fun scale =>
    af_faraut_core_physical_length
      E (coupling scale)
      (growth.coupling_pos scale)
      (growth.coupling_le scale)
      (bits scale) growth.costCeiling
      (growth.bit_heat_cost scale)

/-- The tied AF/Faraut window family pays the strict Perron inequality at
every scale once the physical depth contains its own explicit bit cost. -/
theorem faraut_af_window_family_perron_strict
    {E : AFEnvelope}
    {coupling : Nat → Q'}
    {prefactorFloor prefactorCeiling
      imageFloor imageCeiling : Nat → Q'}
    (family :
      FarautAFWindowFamily E coupling
        prefactorFloor prefactorCeiling
        imageFloor imageCeiling)
    (qS : Nat → Q') (m : Nat → Nat)
    (qS_nonnegative :
      ∀ scale, (0 : Q') ≤ qS scale)
    (qS_le_quarter :
      ∀ scale, qS scale ≤ quarter)
    (depth_available :
      ∀ scale,
        farautRequiredDepth
            ((family.window scale).bits) ≤
          m scale) :
    ∀ scale,
      farautPerronSquare
          ((family.window scale).bits) *
        qS scale ^ (m scale - 2) < 1 :=
  fun scale =>
    faraut_perron_of_available_depth
      ((family.window scale).bits)
      (qS scale) (m scale)
      (qS_nonnegative scale)
      (qS_le_quarter scale)
      (depth_available scale)

/-- The same tied family has one uniform AF-scaled physical core-length
ceiling. -/
theorem faraut_af_window_family_core_length_uniform
    {E : AFEnvelope}
    {coupling : Nat → Q'}
    {prefactorFloor prefactorCeiling
      imageFloor imageCeiling : Nat → Q'}
    (family :
      FarautAFWindowFamily E coupling
        prefactorFloor prefactorCeiling
        imageFloor imageCeiling) :
    ∀ scale,
      BF4AFHeatSpacing.heatSpacingRate E *
          (Q'.ofNat
              (46 * (family.window scale).bits) *
            E.a (coupling scale)) ≤
        Q'.ofNat 46 *
          family.growth.costCeiling :=
  faraut_af_family_core_length_uniform family.growth

end YMGap.Continuum.BF4FarautJointCarrierAFBudget

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4FarautJointCarrierAFBudget.faraut_product_window_cap
#print axioms YMGap.Continuum.BF4FarautJointCarrierAFBudget.farautCompletedRetainedHarnack
#print axioms YMGap.Continuum.BF4FarautJointCarrierAFBudget.dynamicCompletedFeynmanKac_pathwiseDomination
#print axioms YMGap.Continuum.BF4FarautJointCarrierAFBudget.dynamicCompletedConditionalPushforward_domination
#print axioms YMGap.Continuum.BF4FarautJointCarrierAFBudget.singleton_mem_wholeSlabJointCarrierPaths
#print axioms YMGap.Continuum.BF4FarautJointCarrierAFBudget.wholeSlabFarautCompletedRetainedHarnack
#print axioms YMGap.Continuum.BF4FarautJointCarrierAFBudget.wholeSlabFarautConditionalPushforward_domination
#print axioms YMGap.Continuum.BF4FarautJointCarrierAFBudget.wholeSlabJointCarrierQuadratic_nonnegative
#print axioms YMGap.Continuum.BF4FarautJointCarrierAFBudget.farautPerronSquare_le_cap
#print axioms YMGap.Continuum.BF4FarautJointCarrierAFBudget.farautRequiredDepth_sub_two
#print axioms YMGap.Continuum.BF4FarautJointCarrierAFBudget.faraut_perron_requiredDepth_strict
#print axioms YMGap.Continuum.BF4FarautJointCarrierAFBudget.faraut_perron_of_available_depth
#print axioms YMGap.Continuum.BF4FarautJointCarrierAFBudget.faraut_perron_family_strict
#print axioms YMGap.Continuum.BF4FarautJointCarrierAFBudget.af_faraut_core_physical_length
#print axioms YMGap.Continuum.BF4FarautJointCarrierAFBudget.faraut_af_family_core_length_uniform
#print axioms YMGap.Continuum.BF4FarautJointCarrierAFBudget.faraut_af_window_family_perron_strict
#print axioms YMGap.Continuum.BF4FarautJointCarrierAFBudget.faraut_af_window_family_core_length_uniform
