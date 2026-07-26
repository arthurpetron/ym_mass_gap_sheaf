/-
# Quantitative grouped Feynman--Kac Harnack/order certificate

This module supplies the positive counterpart to
`BF4InterleavedPotentialShortcutFence`.  It treats genuinely nonconstant
interior spatial weights.  For a finite path expansion

  K_V(x,z) = sum_path kinetic(x,z,path) * product_{y in path} V(y),

pointwise kinetic positivity and the checkable oscillation window

  vLo <= V(y) <= vHi <= vSpread * vLo

give the exact sandwich

  vLo^p K_0(x,z) <= K_V(x,z) <= vHi^p K_0(x,z)

when every recorded path has `p` interior vertices.  Combining this with a
kinetic window

  kLo <= K_0(x,z) <= kHi <= kSpread * kLo

produces the terminal-independent cross-ratio spread

  kSpread * vSpread^p.

Thus the potential is not discarded or absorbed into the heat semigroup:
its full oscillation cost is retained, once per interior insertion.

For the BF4 all-label census the kinetic constants are instantiated as

  kLo     = (1055/2272)^23,
  kHi     = (3489/2272)^23,
  kSpread = (3489/1055)^23.

The remaining Yang--Mills-specific input is exactly a spacing-uniform
oscillation estimate for the spatial Feynman--Kac weights.  The final
two-state spike theorem proves that strict positivity alone cannot supply
any finite uniform oscillation constant.

## Axiom gate

Exact `Q'` arithmetic and finite list induction only.  No `Classical.*`,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration.
-/

import YMGap.Continuum.BF4InterleavedPotentialShortcutFence
import YMGap.Continuum.RationalCrossRatioDiameter

namespace YMGap.Continuum.BF4GroupedFeynmanKacHarnack

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.GroupedAllLabelHaarRefresh
open YMGap.Continuum.RationalCrossRatioDiameter
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## Exact finite-path Feynman--Kac expansion -/

/-- Product of a possibly nonconstant potential along the interior vertices
of one finite path. -/
def pathPotentialProduct {State : Type}
    (potential : State → Q') : List State → Q'
  | [] => 1
  | state :: tail =>
      potential state * pathPotentialProduct potential tail

/-- Bare grouped kinetic path sum. -/
def groupedPathKernel
    {Source Target State : Type}
    (paths : List (List State))
    (kineticWeight : Source → Target → List State → Q')
    (source : Source) (target : Target) : Q' :=
  listQSum (kineticWeight source target) paths

/-- Grouped Feynman--Kac path sum with every interior spatial weight retained. -/
def feynmanKacPathKernel
    {Source Target State : Type}
    (paths : List (List State))
    (kineticWeight : Source → Target → List State → Q')
    (potential : State → Q')
    (source : Source) (target : Target) : Q' :=
  listQSum
    (fun path =>
      kineticWeight source target path *
        pathPotentialProduct potential path)
    paths

/-- Pointwise nonnegativity of the potential passes to every finite path
product. -/
theorem pathPotentialProduct_nonnegative
    {State : Type} {potential : State → Q'}
    (potential_nonnegative :
      ∀ state, (0 : Q') ≤ potential state) :
    ∀ path : List State,
      (0 : Q') ≤ pathPotentialProduct potential path
  | [] => Q'.zero_le_one
  | state :: tail =>
      Q'.mul_nonneg _ _
        (potential_nonnegative state)
        (pathPotentialProduct_nonnegative potential_nonnegative tail)

/-- A pointwise lower potential bound multiplies once per interior vertex. -/
theorem potentialProduct_lower
    {State : Type} (potential : State → Q') (vLo : Q')
    (vLo_nonnegative : (0 : Q') ≤ vLo)
    (lower_bound : ∀ state, vLo ≤ potential state) :
    ∀ path : List State,
      vLo ^ path.length ≤ pathPotentialProduct potential path
  | [] => Q'.le_refl' 1
  | state :: tail => by
      change
        vLo * vLo ^ tail.length ≤
          potential state * pathPotentialProduct potential tail
      have hpotential : (0 : Q') ≤ potential state :=
        Q'.le_trans' _ _ _
          vLo_nonnegative (lower_bound state)
      exact Q'.mul_le_mul_of_nonneg
        (lower_bound state)
        (potentialProduct_lower
          potential vLo vLo_nonnegative lower_bound tail)
        hpotential
        (Q'.pow_nonneg vLo vLo_nonnegative tail.length)

/-- A pointwise upper potential bound multiplies once per interior vertex. -/
theorem potentialProduct_upper
    {State : Type} (potential : State → Q') (vHi : Q')
    (potential_nonnegative :
      ∀ state, (0 : Q') ≤ potential state)
    (vHi_nonnegative : (0 : Q') ≤ vHi)
    (upper_bound : ∀ state, potential state ≤ vHi) :
    ∀ path : List State,
      pathPotentialProduct potential path ≤ vHi ^ path.length
  | [] => Q'.le_refl' 1
  | state :: tail => by
      change
        potential state * pathPotentialProduct potential tail ≤
          vHi * vHi ^ tail.length
      exact Q'.mul_le_mul_of_nonneg
        (upper_bound state)
        (potentialProduct_upper
          potential vHi potential_nonnegative
          vHi_nonnegative upper_bound tail)
        vHi_nonnegative
        (pathPotentialProduct_nonnegative
          potential_nonnegative tail)

private theorem listQSum_mono_on
    {A : Type} (lower upper : A → Q') :
    ∀ xs : List A,
      (∀ x, x ∈ xs → lower x ≤ upper x) →
        listQSum lower xs ≤ listQSum upper xs
  | [], _ => Q'.le_refl' 0
  | head :: tail, hbound =>
      Q'.add_le_add
        (hbound head List.mem_cons_self)
        (listQSum_mono_on lower upper tail
          (fun x hx =>
            hbound x (List.mem_cons_of_mem head hx)))

/-- Exact lower Feynman--Kac sandwich.  No semigroup identity is used: the
potential product is bounded path by path and only then summed. -/
theorem feynmanKac_ge_scaled_grouped
    {Source Target State : Type}
    (paths : List (List State))
    (kineticWeight : Source → Target → List State → Q')
    (potential : State → Q') (interiorCount : Nat)
    (kinetic_nonnegative :
      ∀ source target path,
        path ∈ paths →
          (0 : Q') ≤ kineticWeight source target path)
    (fixed_length :
      ∀ path, path ∈ paths → path.length = interiorCount)
    (vLo : Q') (vLo_nonnegative : (0 : Q') ≤ vLo)
    (lower_bound : ∀ state, vLo ≤ potential state)
    (source : Source) (target : Target) :
    vLo ^ interiorCount *
        groupedPathKernel paths kineticWeight source target ≤
      feynmanKacPathKernel
        paths kineticWeight potential source target := by
  have hsum :
      listQSum
          (fun path =>
            vLo ^ interiorCount *
              kineticWeight source target path)
          paths ≤
        feynmanKacPathKernel
          paths kineticWeight potential source target := by
    unfold feynmanKacPathKernel
    apply listQSum_mono_on
    intro path hpath
    have hproduct :
        vLo ^ interiorCount ≤
          pathPotentialProduct potential path := by
      have hraw :=
        potentialProduct_lower
          potential vLo vLo_nonnegative lower_bound path
      rwa [fixed_length path hpath] at hraw
    have hscaled :
        kineticWeight source target path *
            vLo ^ interiorCount ≤
          kineticWeight source target path *
            pathPotentialProduct potential path :=
      Q'.mul_le_mul_of_nonneg_left _ _ _
        hproduct (kinetic_nonnegative source target path hpath)
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.mul_comm_eqv
          (vLo ^ interiorCount)
          (kineticWeight source target path)))
      hscaled
  have hfactor :
      listQSum
          (fun path =>
            vLo ^ interiorCount *
              kineticWeight source target path)
          paths ≈
        vLo ^ interiorCount *
          groupedPathKernel paths kineticWeight source target := by
    unfold groupedPathKernel
    exact listQSum_mul_left
      (vLo ^ interiorCount)
      (kineticWeight source target) paths
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv hfactor) hsum

/-- Exact upper Feynman--Kac sandwich, retaining the full potential
oscillation cost once per interior vertex. -/
theorem feynmanKac_le_scaled_grouped
    {Source Target State : Type}
    (paths : List (List State))
    (kineticWeight : Source → Target → List State → Q')
    (potential : State → Q') (interiorCount : Nat)
    (kinetic_nonnegative :
      ∀ source target path,
        path ∈ paths →
          (0 : Q') ≤ kineticWeight source target path)
    (fixed_length :
      ∀ path, path ∈ paths → path.length = interiorCount)
    (potential_nonnegative :
      ∀ state, (0 : Q') ≤ potential state)
    (vHi : Q') (vHi_nonnegative : (0 : Q') ≤ vHi)
    (upper_bound : ∀ state, potential state ≤ vHi)
    (source : Source) (target : Target) :
    feynmanKacPathKernel
        paths kineticWeight potential source target ≤
      vHi ^ interiorCount *
        groupedPathKernel paths kineticWeight source target := by
  have hsum :
      feynmanKacPathKernel
          paths kineticWeight potential source target ≤
        listQSum
          (fun path =>
            vHi ^ interiorCount *
              kineticWeight source target path)
          paths := by
    unfold feynmanKacPathKernel
    apply listQSum_mono_on
    intro path hpath
    have hproduct :
        pathPotentialProduct potential path ≤
          vHi ^ interiorCount := by
      have hraw :=
        potentialProduct_upper
          potential vHi potential_nonnegative
          vHi_nonnegative upper_bound path
      rwa [fixed_length path hpath] at hraw
    have hscaled :
        kineticWeight source target path *
            pathPotentialProduct potential path ≤
          kineticWeight source target path *
            vHi ^ interiorCount :=
      Q'.mul_le_mul_of_nonneg_left _ _ _
        hproduct (kinetic_nonnegative source target path hpath)
    exact Q'.le_trans' _ _ _
      hscaled
      (Q'.le_of_eqv
        (Q'.mul_comm_eqv
          (kineticWeight source target path)
          (vHi ^ interiorCount)))
  have hfactor :
      listQSum
          (fun path =>
            vHi ^ interiorCount *
              kineticWeight source target path)
          paths ≈
        vHi ^ interiorCount *
          groupedPathKernel paths kineticWeight source target := by
    unfold groupedPathKernel
    exact listQSum_mul_left
      (vHi ^ interiorCount)
      (kineticWeight source target) paths
  exact Q'.le_trans' _ _ _
    hsum (Q'.le_of_eqv hfactor)

/-! ## Window data and the terminal-independent cross-ratio theorem -/

/-- Checkable oscillation data for a nonconstant interior potential. -/
structure PotentialOscillationData
    {State : Type} (potential : State → Q') : Type where
  lower : Q'
  upper : Q'
  spread : Q'
  lower_pos : (0 : Q') < lower
  upper_nonnegative : (0 : Q') ≤ upper
  one_le_spread : (1 : Q') ≤ spread
  lower_bound : ∀ state, lower ≤ potential state
  upper_bound : ∀ state, potential state ≤ upper
  upper_le_spread_lower : upper ≤ spread * lower

namespace PotentialOscillationData

theorem potential_nonnegative
    {State : Type} {potential : State → Q'}
    (data : PotentialOscillationData potential)
    (state : State) :
    (0 : Q') ≤ potential state :=
  Q'.le_trans' _ _ _
    (Q'.le_of_lt data.lower_pos)
    (data.lower_bound state)

end PotentialOscillationData

/-- Checkable lower/upper/oscillation data for a grouped kinetic kernel on
the selected finite source-target rectangle. -/
structure KineticWindowData
    {Source Target : Type}
    (kernel : Source → Target → Q')
    (sources : List Source) (targets : List Target) : Type where
  lower : Q'
  upper : Q'
  spread : Q'
  lower_pos : (0 : Q') < lower
  upper_nonnegative : (0 : Q') ≤ upper
  one_le_spread : (1 : Q') ≤ spread
  lower_bound :
    ∀ source, source ∈ sources →
      ∀ target, target ∈ targets →
        lower ≤ kernel source target
  upper_bound :
    ∀ source, source ∈ sources →
      ∀ target, target ∈ targets →
        kernel source target ≤ upper
  upper_le_spread_lower : upper ≤ spread * lower

private theorem pow_pos_local {value : Q'}
    (value_pos : (0 : Q') < value) :
    ∀ exponent : Nat, (0 : Q') < value ^ exponent
  | 0 => by
      show (0 : Q') < (1 : Q')
      decide
  | exponent + 1 =>
      Q'.mul_pos value_pos (pow_pos_local value_pos exponent)

private theorem pow_base_mono {lower upper : Q'}
    (lower_nonnegative : (0 : Q') ≤ lower)
    (upper_nonnegative : (0 : Q') ≤ upper)
    (lower_le_upper : lower ≤ upper) :
    ∀ exponent : Nat, lower ^ exponent ≤ upper ^ exponent
  | 0 => Q'.le_refl' 1
  | exponent + 1 =>
      Q'.mul_le_mul_of_nonneg
        lower_le_upper
        (pow_base_mono
          lower_nonnegative upper_nonnegative
          lower_le_upper exponent)
        upper_nonnegative
        (Q'.pow_nonneg lower lower_nonnegative exponent)

private theorem pow_eqv_congr {left right : Q'}
    (base_eqv : left ≈ right) :
    ∀ exponent : Nat, left ^ exponent ≈ right ^ exponent
  | 0 => Q'.eqv_refl 1
  | exponent + 1 =>
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right
          left right (left ^ exponent) base_eqv)
        (Q'.mul_eqv_congr_left
          right (left ^ exponent) (right ^ exponent)
          (pow_eqv_congr base_eqv exponent))

private theorem mul_pow_eqv (left right : Q') :
    ∀ exponent : Nat,
      (left * right) ^ exponent ≈
        left ^ exponent * right ^ exponent
  | 0 => Q'.eqv_symm (Q'.mul_one_eqv 1)
  | exponent + 1 => by
      have hinductive := mul_pow_eqv left right exponent
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

private theorem one_le_pow {value : Q'}
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
          (one_le_pow one_le_value exponent)
          hvalue_nonnegative
          Q'.zero_le_one
      exact Q'.le_trans' _ _ _
        (Q'.ge_of_eqv (Q'.one_mul_eqv 1))
        hscaled

private theorem mul_swap4_local (a b c d : Q') :
    ((a * b) * (c * d)) ≈
      ((a * c) * (b * d)) := by
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv a b (c * d)) ?_
  refine Q'.eqv_trans _ _ _
    ?_ (Q'.eqv_symm
      (Q'.mul_assoc_eqv a c (b * d)))
  apply Q'.mul_eqv_congr_left
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv b c d)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ d
      (Q'.mul_comm_eqv b c)) ?_
  exact Q'.mul_assoc_eqv c b d

/-- Any strictly positive pointwise window whose upper/lower ratio is at
most `spread` gives a division-free, terminal-independent cross-ratio
certificate with that spread. -/
def crossRatioCertificateOfWindow
    {Source Target : Type}
    (kernel : Source → Target → Q')
    (sources : List Source) (targets : List Target)
    (lower upper spread : Q')
    (lower_pos : (0 : Q') < lower)
    (upper_nonnegative : (0 : Q') ≤ upper)
    (one_le_spread : (1 : Q') ≤ spread)
    (lower_bound :
      ∀ source, source ∈ sources →
        ∀ target, target ∈ targets →
          lower ≤ kernel source target)
    (upper_bound :
      ∀ source, source ∈ sources →
        ∀ target, target ∈ targets →
          kernel source target ≤ upper)
    (upper_le_spread_lower :
      upper ≤ spread * lower) :
    FiniteCrossRatioDiameterCertificate
      kernel sources targets where
  spread := spread
  one_le_spread := one_le_spread
  strictlyPositive := by
    intro source hsource target htarget
    exact Q'.pos_of_lt_of_le
      lower_pos
      (lower_bound source hsource target htarget)
  crossRatioBound := by
    intro first hfirst second hsecond left hleft right hright
    have hfirstLeftNonnegative :
        (0 : Q') ≤ kernel first left :=
      Q'.le_trans' _ _ _
        (Q'.le_of_lt lower_pos)
        (lower_bound first hfirst left hleft)
    have hsecondRightNonnegative :
        (0 : Q') ≤ kernel second right :=
      Q'.le_trans' _ _ _
        (Q'.le_of_lt lower_pos)
        (lower_bound second hsecond right hright)
    have hfirstRightNonnegative :
        (0 : Q') ≤ kernel first right :=
      Q'.le_trans' _ _ _
        (Q'.le_of_lt lower_pos)
        (lower_bound first hfirst right hright)
    have hspreadNonnegative : (0 : Q') ≤ spread :=
      Q'.le_trans' _ _ _
        Q'.zero_le_one one_le_spread
    have hspreadLowerNonnegative :
        (0 : Q') ≤ spread * lower :=
      Q'.mul_nonneg _ _
        hspreadNonnegative (Q'.le_of_lt lower_pos)
    have hleftToUpper :
        kernel first left * kernel second right ≤
          upper * upper :=
      Q'.mul_le_mul_of_nonneg
        (upper_bound first hfirst left hleft)
        (upper_bound second hsecond right hright)
        upper_nonnegative hsecondRightNonnegative
    have hupperToScaled :
        upper * upper ≤
          (spread * lower) * (spread * lower) :=
      Q'.mul_le_mul_of_nonneg
        upper_le_spread_lower
        upper_le_spread_lower
        hspreadLowerNonnegative upper_nonnegative
    have hlowerToReverse :
        lower * lower ≤
          kernel first right * kernel second left :=
      Q'.mul_le_mul_of_nonneg
        (lower_bound first hfirst right hright)
        (lower_bound second hsecond left hleft)
        hfirstRightNonnegative (Q'.le_of_lt lower_pos)
    have hspreadSquareNonnegative :
        (0 : Q') ≤ spread * spread :=
      Q'.mul_nonneg _ _
        hspreadNonnegative hspreadNonnegative
    have hscaledLowerToReverse :
        (spread * spread) * (lower * lower) ≤
          (spread * spread) *
            (kernel first right * kernel second left) :=
      Q'.mul_le_mul_of_nonneg_left _ _ _
        hlowerToReverse hspreadSquareNonnegative
    exact Q'.le_trans' _ _ _
      hleftToUpper
      (Q'.le_trans' _ _ _
        hupperToScaled
        (Q'.le_trans' _ _ _
          (Q'.le_of_eqv
            (mul_swap4_local
              spread lower spread lower))
          hscaledLowerToReverse))

/-- Exact combined window cap.  The kinetic spread occurs once; the
potential spread occurs once for every interior insertion. -/
theorem combinedFeynmanKacWindowCap
    {Source Target State : Type}
    {kineticKernel : Source → Target → Q'}
    {sources : List Source} {targets : List Target}
    {potential : State → Q'}
    (kinetic :
      KineticWindowData kineticKernel sources targets)
    (potentialData :
      PotentialOscillationData potential)
    (interiorCount : Nat) :
    potentialData.upper ^ interiorCount * kinetic.upper ≤
      (kinetic.spread *
          potentialData.spread ^ interiorCount) *
        (potentialData.lower ^ interiorCount *
          kinetic.lower) := by
  have hspreadNonnegative :
      (0 : Q') ≤ potentialData.spread :=
    Q'.le_trans' _ _ _
      Q'.zero_le_one potentialData.one_le_spread
  have hlowerNonnegative :
      (0 : Q') ≤ potentialData.lower :=
    Q'.le_of_lt potentialData.lower_pos
  have hspreadLowerNonnegative :
      (0 : Q') ≤
        potentialData.spread * potentialData.lower :=
    Q'.mul_nonneg _ _
      hspreadNonnegative hlowerNonnegative
  have hpotentialPower :
      potentialData.upper ^ interiorCount ≤
        (potentialData.spread *
          potentialData.lower) ^ interiorCount :=
    pow_base_mono
      potentialData.upper_nonnegative
      hspreadLowerNonnegative
      potentialData.upper_le_spread_lower
      interiorCount
  have hkineticSpreadNonnegative :
      (0 : Q') ≤ kinetic.spread :=
    Q'.le_trans' _ _ _
      Q'.zero_le_one kinetic.one_le_spread
  have hkineticSpreadLowerNonnegative :
      (0 : Q') ≤ kinetic.spread * kinetic.lower :=
    Q'.mul_nonneg _ _
      hkineticSpreadNonnegative
      (Q'.le_of_lt kinetic.lower_pos)
  have hcombined :
      potentialData.upper ^ interiorCount * kinetic.upper ≤
        (potentialData.spread *
            potentialData.lower) ^ interiorCount *
          (kinetic.spread * kinetic.lower) :=
    Q'.mul_le_mul_of_nonneg
      hpotentialPower
      kinetic.upper_le_spread_lower
      (Q'.pow_nonneg
        (potentialData.spread *
          potentialData.lower)
        hspreadLowerNonnegative interiorCount)
      kinetic.upper_nonnegative
  have hreindex :
      (potentialData.spread *
          potentialData.lower) ^ interiorCount *
          (kinetic.spread * kinetic.lower) ≈
        (kinetic.spread *
            potentialData.spread ^ interiorCount) *
          (potentialData.lower ^ interiorCount *
            kinetic.lower) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right
        ((potentialData.spread *
            potentialData.lower) ^ interiorCount)
        (potentialData.spread ^ interiorCount *
          potentialData.lower ^ interiorCount)
        (kinetic.spread * kinetic.lower)
        (mul_pow_eqv
          potentialData.spread
          potentialData.lower
          interiorCount)) ?_
    refine Q'.eqv_trans _ _ _
      (mul_swap4_local
        (potentialData.spread ^ interiorCount)
        (potentialData.lower ^ interiorCount)
        kinetic.spread kinetic.lower) ?_
    exact Q'.mul_eqv_congr_right _ _
      (potentialData.lower ^ interiorCount *
        kinetic.lower)
      (Q'.mul_comm_eqv
        (potentialData.spread ^ interiorCount)
        kinetic.spread)
  exact Q'.le_trans' _ _ _
    hcombined (Q'.le_of_eqv hreindex)

/-- **Quantitative grouped Feynman--Kac Harnack/order theorem.**

From the finite path expansion, fixed path length, nonnegative kinetic path
weights, a grouped kinetic window, and pointwise potential oscillation data,
this constructs a terminal-independent cross-ratio certificate.  No bound on
the physical kernel is assumed: its lower and upper windows are derived from
the path sum. -/
def groupedFeynmanKacCrossRatioCertificate
    {Source Target State : Type}
    (paths : List (List State))
    (kineticWeight : Source → Target → List State → Q')
    (potential : State → Q')
    (sources : List Source) (targets : List Target)
    (interiorCount : Nat)
    (kinetic_nonnegative :
      ∀ source target path,
        path ∈ paths →
          (0 : Q') ≤ kineticWeight source target path)
    (fixed_length :
      ∀ path, path ∈ paths →
        path.length = interiorCount)
    (kinetic :
      KineticWindowData
        (groupedPathKernel paths kineticWeight)
        sources targets)
    (potentialData :
      PotentialOscillationData potential) :
    FiniteCrossRatioDiameterCertificate
      (feynmanKacPathKernel
        paths kineticWeight potential)
      sources targets := by
  let physicalLower :=
    potentialData.lower ^ interiorCount *
      kinetic.lower
  let physicalUpper :=
    potentialData.upper ^ interiorCount *
      kinetic.upper
  let physicalSpread :=
    kinetic.spread *
      potentialData.spread ^ interiorCount
  have hphysicalLowerPos :
      (0 : Q') < physicalLower := by
    unfold physicalLower
    exact Q'.mul_pos
      (pow_pos_local
        potentialData.lower_pos interiorCount)
      kinetic.lower_pos
  have hphysicalUpperNonnegative :
      (0 : Q') ≤ physicalUpper := by
    unfold physicalUpper
    exact Q'.mul_nonneg _ _
      (Q'.pow_nonneg
        potentialData.upper
        potentialData.upper_nonnegative
        interiorCount)
      kinetic.upper_nonnegative
  have hphysicalSpreadOne :
      (1 : Q') ≤ physicalSpread := by
    unfold physicalSpread
    have hproduct :
        (1 : Q') * 1 ≤
          kinetic.spread *
            potentialData.spread ^ interiorCount :=
      Q'.mul_le_mul_of_nonneg
        kinetic.one_le_spread
        (one_le_pow
          potentialData.one_le_spread interiorCount)
        (Q'.le_trans' _ _ _
          Q'.zero_le_one kinetic.one_le_spread)
        Q'.zero_le_one
    exact Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (Q'.one_mul_eqv 1))
      hproduct
  have hphysicalLower :
      ∀ source, source ∈ sources →
        ∀ target, target ∈ targets →
          physicalLower ≤
            feynmanKacPathKernel
              paths kineticWeight potential
              source target := by
    intro source hsource target htarget
    have hscaledKinetic :
        potentialData.lower ^ interiorCount *
            kinetic.lower ≤
          potentialData.lower ^ interiorCount *
            groupedPathKernel
              paths kineticWeight source target :=
      Q'.mul_le_mul_of_nonneg_left _ _ _
        (kinetic.lower_bound
          source hsource target htarget)
        (Q'.pow_nonneg
          potentialData.lower
          (Q'.le_of_lt potentialData.lower_pos)
          interiorCount)
    exact Q'.le_trans' _ _ _
      hscaledKinetic
      (feynmanKac_ge_scaled_grouped
        paths kineticWeight potential interiorCount
        kinetic_nonnegative fixed_length
        potentialData.lower
        (Q'.le_of_lt potentialData.lower_pos)
        potentialData.lower_bound
        source target)
  have hphysicalUpper :
      ∀ source, source ∈ sources →
        ∀ target, target ∈ targets →
          feynmanKacPathKernel
              paths kineticWeight potential
              source target ≤ physicalUpper := by
    intro source hsource target htarget
    have hsandwich :=
      feynmanKac_le_scaled_grouped
        paths kineticWeight potential interiorCount
        kinetic_nonnegative fixed_length
        potentialData.potential_nonnegative
        potentialData.upper
        potentialData.upper_nonnegative
        potentialData.upper_bound
        source target
    have hscaledKinetic :
        potentialData.upper ^ interiorCount *
            groupedPathKernel
              paths kineticWeight source target ≤
          potentialData.upper ^ interiorCount *
            kinetic.upper :=
      Q'.mul_le_mul_of_nonneg_left _ _ _
        (kinetic.upper_bound
          source hsource target htarget)
        (Q'.pow_nonneg
          potentialData.upper
          potentialData.upper_nonnegative
          interiorCount)
    exact Q'.le_trans' _ _ _
      hsandwich hscaledKinetic
  exact crossRatioCertificateOfWindow
    (feynmanKacPathKernel
      paths kineticWeight potential)
    sources targets
    physicalLower physicalUpper physicalSpread
    hphysicalLowerPos hphysicalUpperNonnegative
    hphysicalSpreadOne
    hphysicalLower hphysicalUpper
    (combinedFeynmanKacWindowCap
      kinetic potentialData interiorCount)

/-- The spread recorded by the constructed physical certificate is exactly
the kinetic spread times one potential-spread factor per insertion. -/
theorem groupedFeynmanKacCrossRatioCertificate_spread
    {Source Target State : Type}
    (paths : List (List State))
    (kineticWeight : Source → Target → List State → Q')
    (potential : State → Q')
    (sources : List Source) (targets : List Target)
    (interiorCount : Nat)
    (kinetic_nonnegative :
      ∀ source target path,
        path ∈ paths →
          (0 : Q') ≤ kineticWeight source target path)
    (fixed_length :
      ∀ path, path ∈ paths →
        path.length = interiorCount)
    (kinetic :
      KineticWindowData
        (groupedPathKernel paths kineticWeight)
        sources targets)
    (potentialData :
      PotentialOscillationData potential) :
    (groupedFeynmanKacCrossRatioCertificate
      paths kineticWeight potential
      sources targets interiorCount
      kinetic_nonnegative fixed_length
      kinetic potentialData).spread =
        kinetic.spread *
          potentialData.spread ^ interiorCount :=
  rfl

/-! ## Exact BF4 constants and physical consumer -/

/-- Exact all-label one-cycle ceiling from the BF4 heat-tail census. -/
def allLabelHaarCeiling : Q' :=
  Q'.mkPos 3489 2272 (by decide)

/-- Exact one-cycle upper/lower ratio. -/
def allLabelKineticSpread : Q' :=
  Q'.mkPos 3489 1055 (by decide)

/-- Cycle rank of the connected 48-edge, 26-vertex BF4 spatial boundary
graph: `48 - 26 + 1 = 23`. -/
def bf4SpatialCycleCount : Nat := 23

/-- Product-window lower bound on the 23-cycle BF4 kinetic carrier. -/
def bf4KineticFloor : Q' :=
  allLabelHaarFloor ^ bf4SpatialCycleCount

/-- Product-window upper bound on the 23-cycle BF4 kinetic carrier. -/
def bf4KineticCeiling : Q' :=
  allLabelHaarCeiling ^ bf4SpatialCycleCount

/-- Exact BF4 kinetic projective spread. -/
def bf4KineticSpread : Q' :=
  allLabelKineticSpread ^ bf4SpatialCycleCount

/-- Reciprocal one-cycle ratio used in the terminal-independent kinetic
common-mass ledger. -/
def inverseAllLabelKineticSpread : Q' :=
  Q'.mkPos 1055 3489 (by decide)

/-- Exact terminal-independent common mass of the 23-cycle kinetic reference:
two row comparisons cost `2 * 23 = 46` powers. -/
def bf4KineticCommonMass : Q' :=
  inverseAllLabelKineticSpread ^ 46

theorem allLabelHaarCeiling_pos :
    (0 : Q') < allLabelHaarCeiling := by
  decide

theorem allLabelKineticSpread_one_le :
    (1 : Q') ≤ allLabelKineticSpread := by
  decide

theorem allLabelHaarCeiling_eqv_spread_floor :
    allLabelHaarCeiling ≈
      allLabelKineticSpread * allLabelHaarFloor := by
  decide

theorem bf4KineticFloor_pos :
    (0 : Q') < bf4KineticFloor := by
  unfold bf4KineticFloor
  exact pow_pos_local
    allLabelHaarFloor_pos bf4SpatialCycleCount

theorem bf4KineticCeiling_nonnegative :
    (0 : Q') ≤ bf4KineticCeiling := by
  unfold bf4KineticCeiling
  exact Q'.pow_nonneg
    allLabelHaarCeiling
    (Q'.le_of_lt allLabelHaarCeiling_pos)
    bf4SpatialCycleCount

theorem bf4KineticSpread_one_le :
    (1 : Q') ≤ bf4KineticSpread := by
  unfold bf4KineticSpread
  exact one_le_pow
    allLabelKineticSpread_one_le
    bf4SpatialCycleCount

/-- The exact one-cycle ratio identity tensorizes to the BF4 23-cycle
kinetic window without a numerical approximation. -/
theorem bf4KineticCeiling_le_spread_floor :
    bf4KineticCeiling ≤
      bf4KineticSpread * bf4KineticFloor := by
  have hpowered :
      allLabelHaarCeiling ^ bf4SpatialCycleCount ≈
        (allLabelKineticSpread *
          allLabelHaarFloor) ^ bf4SpatialCycleCount :=
    pow_eqv_congr
      allLabelHaarCeiling_eqv_spread_floor
      bf4SpatialCycleCount
  have hfactorized :
      (allLabelKineticSpread *
          allLabelHaarFloor) ^ bf4SpatialCycleCount ≈
        allLabelKineticSpread ^ bf4SpatialCycleCount *
          allLabelHaarFloor ^ bf4SpatialCycleCount :=
    mul_pow_eqv
      allLabelKineticSpread allLabelHaarFloor
      bf4SpatialCycleCount
  unfold bf4KineticCeiling bf4KineticSpread bf4KineticFloor
  exact Q'.le_of_eqv
    (Q'.eqv_trans _ _ _ hpowered hfactorized)

theorem bf4KineticCommonMass_pos :
    (0 : Q') < bf4KineticCommonMass := by
  unfold bf4KineticCommonMass
  exact pow_pos_local (by decide) 46

theorem bf4KineticCommonMass_value :
    bf4KineticCommonMass ≈
      (Q'.mkPos 1055 3489 (by decide)) ^ 46 :=
  Q'.eqv_refl _

/-- Package any verified BF4 grouped kinetic entry bounds into the exact
23-cycle window.  Only the two pointwise inequalities remain to be supplied
by the kinetic constructor; every numerical constant and their ratio
relation is already discharged here. -/
def bf4KineticWindowOfBounds
    {Source Target : Type}
    (kernel : Source → Target → Q')
    (sources : List Source) (targets : List Target)
    (lower_bound :
      ∀ source, source ∈ sources →
        ∀ target, target ∈ targets →
          bf4KineticFloor ≤ kernel source target)
    (upper_bound :
      ∀ source, source ∈ sources →
        ∀ target, target ∈ targets →
          kernel source target ≤ bf4KineticCeiling) :
    KineticWindowData kernel sources targets where
  lower := bf4KineticFloor
  upper := bf4KineticCeiling
  spread := bf4KineticSpread
  lower_pos := bf4KineticFloor_pos
  upper_nonnegative := bf4KineticCeiling_nonnegative
  one_le_spread := bf4KineticSpread_one_le
  lower_bound := lower_bound
  upper_bound := upper_bound
  upper_le_spread_lower :=
    bf4KineticCeiling_le_spread_floor

/-- **BF4 physical consumer.**  Once the actual grouped kinetic path
expansion has the proved 23-cycle floor/ceiling and the nonconstant spatial
potential has an oscillation certificate, the physical Feynman--Kac kernel
has an explicit terminal-independent cross-ratio certificate. -/
def bf4GroupedFeynmanKacCrossRatioCertificate
    {Source Target State : Type}
    (paths : List (List State))
    (kineticWeight : Source → Target → List State → Q')
    (potential : State → Q')
    (sources : List Source) (targets : List Target)
    (interiorCount : Nat)
    (kinetic_nonnegative :
      ∀ source target path,
        path ∈ paths →
          (0 : Q') ≤ kineticWeight source target path)
    (fixed_length :
      ∀ path, path ∈ paths →
        path.length = interiorCount)
    (kinetic_lower :
      ∀ source, source ∈ sources →
        ∀ target, target ∈ targets →
          bf4KineticFloor ≤
            groupedPathKernel paths kineticWeight
              source target)
    (kinetic_upper :
      ∀ source, source ∈ sources →
        ∀ target, target ∈ targets →
          groupedPathKernel paths kineticWeight
              source target ≤ bf4KineticCeiling)
    (potentialData :
      PotentialOscillationData potential) :
    FiniteCrossRatioDiameterCertificate
      (feynmanKacPathKernel
        paths kineticWeight potential)
      sources targets :=
  groupedFeynmanKacCrossRatioCertificate
    paths kineticWeight potential
    sources targets interiorCount
    kinetic_nonnegative fixed_length
    (bf4KineticWindowOfBounds
      (groupedPathKernel paths kineticWeight)
      sources targets kinetic_lower kinetic_upper)
    potentialData

/-- The BF4 physical spread exposes the missing estimate with no hidden
constant:

`(3489/1055)^23 * potentialSpread^interiorCount`.
-/
theorem bf4GroupedFeynmanKacCrossRatioCertificate_spread
    {Source Target State : Type}
    (paths : List (List State))
    (kineticWeight : Source → Target → List State → Q')
    (potential : State → Q')
    (sources : List Source) (targets : List Target)
    (interiorCount : Nat)
    (kinetic_nonnegative :
      ∀ source target path,
        path ∈ paths →
          (0 : Q') ≤ kineticWeight source target path)
    (fixed_length :
      ∀ path, path ∈ paths →
        path.length = interiorCount)
    (kinetic_lower :
      ∀ source, source ∈ sources →
        ∀ target, target ∈ targets →
          bf4KineticFloor ≤
            groupedPathKernel paths kineticWeight
              source target)
    (kinetic_upper :
      ∀ source, source ∈ sources →
        ∀ target, target ∈ targets →
          groupedPathKernel paths kineticWeight
              source target ≤ bf4KineticCeiling)
    (potentialData :
      PotentialOscillationData potential) :
    (bf4GroupedFeynmanKacCrossRatioCertificate
      paths kineticWeight potential
      sources targets interiorCount
      kinetic_nonnegative fixed_length
      kinetic_lower kinetic_upper potentialData).spread =
        bf4KineticSpread *
          potentialData.spread ^ interiorCount :=
  rfl

/-! ## Sharp no-go: positivity does not control potential oscillation -/

/-- A strictly positive two-state potential with unit floor and an arbitrarily
high spike. -/
def spikePotential (height : Nat) (state : Bool) : Q' :=
  if state then Q'.ofNat (height + 1) else 1

theorem spikePotential_pos (height : Nat) (state : Bool) :
    (0 : Q') < spikePotential height state := by
  cases state
  · change (0 : Q') < (1 : Q')
    decide
  · change (0 : Q') < Q'.ofNat (height + 1)
    exact Q'.ofNat_succ_pos height

theorem spikePotential_unit_floor (height : Nat) (state : Bool) :
    (1 : Q') ≤ spikePotential height state := by
  cases state
  · exact Q'.le_refl' 1
  · exact CReal.ofNat_le_ofNat
      (Nat.succ_le_succ (Nat.zero_le height))

/-- Every finite spike has honest oscillation data.  Its exact spread is the
spike height, so the positive theorem above applies without pretending that
the resulting constant is uniform. -/
def spikePotentialOscillationData (height : Nat) :
    PotentialOscillationData (spikePotential height) where
  lower := 1
  upper := Q'.ofNat (height + 1)
  spread := Q'.ofNat (height + 1)
  lower_pos := by decide
  upper_nonnegative :=
    Q'.le_of_lt (Q'.ofNat_succ_pos height)
  one_le_spread :=
    CReal.ofNat_le_ofNat
      (Nat.succ_le_succ (Nat.zero_le height))
  lower_bound := spikePotential_unit_floor height
  upper_bound := by
    intro state
    cases state
    · exact CReal.ofNat_le_ofNat
        (Nat.succ_le_succ (Nat.zero_le height))
    · exact Q'.le_refl' _
  upper_le_spread_lower :=
    Q'.ge_of_eqv
      (Q'.mul_one_eqv (Q'.ofNat (height + 1)))

/-- Constructive Archimedean witness used by the no-uniformity theorem. -/
private theorem lt_ofNat_toNat_succ_local (bound : Q') :
    bound < Q'.ofNat (bound.num.toNat + 1) := by
  have hdenOne : (1 : Int) ≤ (bound.den : Int) := by
    exact_mod_cast bound.den_pos
  have hnumLe :
      bound.num ≤ (bound.num.toNat : Int) :=
    Int.self_le_toNat bound.num
  have hmultiplierNonnegative :
      (0 : Int) ≤ (bound.num.toNat : Int) + 1 := by
    have hcastNonnegative :
        (0 : Int) ≤ (bound.num.toNat : Int) :=
      Int.natCast_nonneg _
    omega
  have hmul :
      ((bound.num.toNat : Int) + 1) * (1 : Int) ≤
        ((bound.num.toNat : Int) + 1) *
          (bound.den : Int) :=
    Int.mul_le_mul_of_nonneg_left
      hdenOne hmultiplierNonnegative
  rw [Int.mul_one] at hmul
  show
    bound.num *
        ((Q'.ofNat (bound.num.toNat + 1)).den : Int) <
      (Q'.ofNat (bound.num.toNat + 1)).num *
        (bound.den : Int)
  have hden :
      (Q'.ofNat (bound.num.toNat + 1)).den = 1 :=
    rfl
  have hnum :
      (Q'.ofNat (bound.num.toNat + 1)).num =
        ((bound.num.toNat + 1 : Nat) : Int) :=
    rfl
  rw [hden, hnum]
  push_cast
  push_cast at hmul
  omega

private theorem exists_ofNat_gt_local (bound : Q') :
    ∃ index : Nat, bound < Q'.ofNat index :=
  ⟨bound.num.toNat + 1,
    lt_ofNat_toNat_succ_local bound⟩

private theorem not_reverse_le_of_lt {left right : Q'}
    (hlt : left < right) :
    ¬ right ≤ left := by
  intro hle
  exact (Int.not_lt_of_ge hle) hlt

/-- **No spacing-uniform oscillation follows from strict positivity and a
unit floor.**  For every proposed finite spread there is a strictly positive
two-state potential whose unit-relative ceiling exceeds it.

This is the sharp fail-closed location of the missing Yang--Mills estimate:
one must prove a physical, spacing-uniform control of the interior spatial
weights (or a finer projective cancellation theorem); positivity cannot
produce it. -/
theorem no_uniform_spike_oscillation (spread : Q') :
    ∃ height : Nat,
      ¬ ∀ state : Bool,
        spikePotential height state ≤ spread * (1 : Q') := by
  let height := spread.num.toNat
  refine ⟨height, ?_⟩
  intro hbound
  have hspikeBound := hbound true
  have hspikeLeSpread :
      Q'.ofNat (height + 1) ≤ spread := by
    exact Q'.le_trans' _ _ _
      hspikeBound
      (Q'.le_of_eqv (Q'.mul_one_eqv spread))
  have hspreadLtSpike :
      spread < Q'.ofNat (height + 1) := by
    unfold height
    exact lt_ofNat_toNat_succ_local spread
  exact
    (not_reverse_le_of_lt hspreadLtSpike)
      hspikeLeSpread

/-- There is no single finite ceiling ratio that covers the entire family of
strictly positive unit-floor potentials. -/
theorem no_finite_uniform_positive_potential_spread :
    ¬ ∃ spread : Q',
      ∀ height : Nat,
        ∀ state : Bool,
          spikePotential height state ≤
            spread * (1 : Q') := by
  intro hexists
  obtain ⟨spread, huniform⟩ := hexists
  obtain ⟨height, hfailure⟩ :=
    no_uniform_spike_oscillation spread
  exact hfailure (huniform height)

end YMGap.Continuum.BF4GroupedFeynmanKacHarnack

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4GroupedFeynmanKacHarnack.potentialProduct_lower
#print axioms YMGap.Continuum.BF4GroupedFeynmanKacHarnack.potentialProduct_upper
#print axioms YMGap.Continuum.BF4GroupedFeynmanKacHarnack.feynmanKac_ge_scaled_grouped
#print axioms YMGap.Continuum.BF4GroupedFeynmanKacHarnack.feynmanKac_le_scaled_grouped
#print axioms YMGap.Continuum.BF4GroupedFeynmanKacHarnack.combinedFeynmanKacWindowCap
#print axioms YMGap.Continuum.BF4GroupedFeynmanKacHarnack.groupedFeynmanKacCrossRatioCertificate
#print axioms YMGap.Continuum.BF4GroupedFeynmanKacHarnack.bf4KineticCeiling_le_spread_floor
#print axioms YMGap.Continuum.BF4GroupedFeynmanKacHarnack.bf4GroupedFeynmanKacCrossRatioCertificate
#print axioms YMGap.Continuum.BF4GroupedFeynmanKacHarnack.no_uniform_spike_oscillation
#print axioms YMGap.Continuum.BF4GroupedFeynmanKacHarnack.no_finite_uniform_positive_potential_spread
