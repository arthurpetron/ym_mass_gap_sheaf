/-
# Heat-kernel resummation of the adjacent-even fixed-face kernel

Site reflection fixes spatial faces on the integer reflection plane.  A
single prescribed nonzero face spin inserts a fusion matrix, which need not
be positive.  The physical local kernel therefore has to sum those matrices
with the heat-kernel character coefficients before positivity is tested.

This file first gives the exact finite-cutoff channel matrix for that
resummation and identifies it with the production fusion-path count.  It then
solves the complete cutoff-one channel problem: the matrix is

    [[1, a], [a, 1]],    a = coeffW w 1,

and its quadratic form is

    (1-a)(x0^2+x1^2) + a(x0+x1)^2.

Consequently it is constructively positive whenever `0 <= a <= 1`, in
particular at the exact strong-coupling anchor.  Higher cutoffs and gluing the
local channel matrices over the whole fixed interface remain separate.
-/

import YMGap.Continuum.Z4FusionChannelConvolution
import YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
import YMGap.Continuum.Z4StrongCouplingParametricAnchor
import YMGap.Continuum.Pivot2Schur
import YMGap.Continuum.FiniteWeightedGramSOS
import YMGap.Continuum.PlaquetteActivity
import YMGap.Continuum.SU2CharacterFusionSynthesis
import YMGap.Continuum.CubeRatioBounds
import YMGap.Continuum.FusedFreeSplit

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedFaceResummedKernel

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.SumOfSquares
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.BondMovingMoment
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.FusionPositivity
open YMGap.Continuum.FusedFreeSplit
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2CharacterFusionSynthesis
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FusionChannelConvolution
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact natural-valued insertion factorization -/

private theorem natListSumMapMulLeft {A : Type}
    (factor : Nat) (value : A → Nat) : ∀ xs : List A,
    factor * natListSum (xs.map value) =
      natListSum (xs.map fun x => factor * value x)
  | [] => by simp [natListSum]
  | head :: tail => by
      simp only [List.map_cons, natListSum]
      rw [Nat.mul_add, natListSumMapMulLeft factor value tail]

/-- Inserting a fixed face spin between the two reflected halves is exactly
the finite matrix element of its fusion transition between open channels. -/
theorem fusionPathMultiplicity_fixedFace_channel_factorization
    {cutoff fixed : Nat} {left right : List Nat}
    (hfixed : fixed ≤ cutoff)
    (hleft : SpinsBounded cutoff left)
    (hright : SpinsBounded cutoff right) :
    fusionPathMultiplicity cutoff
        (left ++ [fixed] ++ right.reverse) =
      natListSum ((List.range (cutoff + 1)).map fun source =>
        natListSum ((List.range (cutoff + 1)).map fun target =>
          (fusionChannelAmplitude cutoff left source *
            boolMultiplicity (fusionOK source fixed target)) *
            fusionChannelAmplitude cutoff right target)) := by
  have hbounded :
      SpinsBounded cutoff (left ++ [fixed] ++ right.reverse) := by
    intro spin hspin
    rcases List.mem_append.mp hspin with hleftFixed | hrightReverse
    · rcases List.mem_append.mp hleftFixed with hsource | hsingleton
      · exact hleft spin hsource
      · have heq : spin = fixed := List.mem_singleton.mp hsingleton
        rw [heq]
        exact hfixed
    · exact hright spin (List.mem_reverse.mp hrightReverse)
  calc
    fusionPathMultiplicity cutoff
        (left ++ [fixed] ++ right.reverse) =
        fusionWalkMultiplicity cutoff 0 0
          (left ++ ([fixed] ++ right.reverse)) := by
      rw [fusionPathMultiplicity_eq_walk hbounded]
      simp only [List.append_assoc]
    _ = natListSum ((List.range (cutoff + 1)).map fun source =>
          fusionWalkMultiplicity cutoff 0 source left *
            fusionWalkMultiplicity cutoff source 0
              ([fixed] ++ right.reverse)) :=
      fusionWalkMultiplicity_append left ([fixed] ++ right.reverse) 0
        (Nat.zero_le cutoff)
    _ = natListSum ((List.range (cutoff + 1)).map fun source =>
          fusionWalkMultiplicity cutoff 0 source left *
            natListSum ((List.range (cutoff + 1)).map fun target =>
              fusionWalkMultiplicity cutoff source target [fixed] *
                fusionWalkMultiplicity cutoff target 0 right.reverse)) := by
      apply natListSum_map_congr
      intro source hsource
      have hsourceBound : source ≤ cutoff := by
        have hlt := List.mem_range.mp hsource
        omega
      rw [fusionWalkMultiplicity_append [fixed] right.reverse 0
        hsourceBound]
    _ = natListSum ((List.range (cutoff + 1)).map fun source =>
          natListSum ((List.range (cutoff + 1)).map fun target =>
            (fusionWalkMultiplicity cutoff 0 source left *
              fusionWalkMultiplicity cutoff source target [fixed]) *
              fusionWalkMultiplicity cutoff target 0 right.reverse)) := by
      apply natListSum_map_congr
      intro source _
      rw [natListSumMapMulLeft]
      apply natListSum_map_congr
      intro target _
      simp only [Nat.mul_assoc]
    _ = natListSum ((List.range (cutoff + 1)).map fun source =>
          natListSum ((List.range (cutoff + 1)).map fun target =>
            (fusionChannelAmplitude cutoff left source *
              boolMultiplicity (fusionOK source fixed target)) *
              fusionChannelAmplitude cutoff right target)) := by
      apply natListSum_map_congr
      intro source hsource
      have hsourceBound : source ≤ cutoff := by
        have hlt := List.mem_range.mp hsource
        omega
      rw [fusionChannelAmplitude_eq_walk hsourceBound hleft]
      apply natListSum_map_congr
      intro target htarget
      have htargetBound : target ≤ cutoff := by
        have hlt := List.mem_range.mp htarget
        omega
      rw [fusionWalkMultiplicity_singleton fixed htargetBound]
      rw [fusionChannelAmplitude_eq_walk htargetBound hright]
      rw [fusionWalkMultiplicity_reverse right.reverse
        htargetBound (Nat.zero_le cutoff)]
      simp only [List.reverse_reverse]

/-! ## 2. Exact rational resummation and finite Fubini -/

private theorem ofNat_natListSum_map_eqv
    {A : Type} (value : A → Nat) : ∀ xs : List A,
    Q'.ofNat (natListSum (xs.map value)) ≈
      listQSum (fun item => Q'.ofNat (value item)) xs
  | [] => Q'.eqv_refl _
  | head :: tail => by
      simp only [List.map_cons, natListSum, listQSum]
      exact Q'.eqv_trans _ _ _
        (Q'.ofNat_add_eqv (value head)
          (natListSum (tail.map value)))
        (Q'.add_eqv_congr_left _ _ _
          (ofNat_natListSum_map_eqv value tail))

private theorem ofNat_three_mul_eqv (a b c : Nat) :
    Q'.ofNat ((a * b) * c) ≈
      (Q'.ofNat a * Q'.ofNat b) * Q'.ofNat c := by
  refine Q'.eqv_trans _ _ _ (ofNat_mul_eqv (a * b) c) ?_
  exact Q'.mul_eqv_congr_right _ _ (Q'.ofNat c)
    (ofNat_mul_eqv a b)

private theorem ofNat_nestedChannelSum_eqv
    (cutoff : Nat)
    (term : Nat → Nat → Nat) :
    Q'.ofNat
        (natListSum ((List.range (cutoff + 1)).map fun source =>
          natListSum ((List.range (cutoff + 1)).map fun target =>
            term source target))) ≈
      listQSum (fun source =>
        listQSum (fun target => Q'.ofNat (term source target))
          (List.range (cutoff + 1)))
        (List.range (cutoff + 1)) := by
  refine Q'.eqv_trans _ _ _
    (ofNat_natListSum_map_eqv
      (fun source =>
        natListSum ((List.range (cutoff + 1)).map fun target =>
          term source target))
      (List.range (cutoff + 1))) ?_
  apply listQSum_congr
  intro source
  exact ofNat_natListSum_map_eqv (term source)
    (List.range (cutoff + 1))

private theorem fixedFaceRationalChannelFactorization
    {cutoff fixed : Nat} {left right : List Nat}
    (hfixed : fixed ≤ cutoff)
    (hleft : SpinsBounded cutoff left)
    (hright : SpinsBounded cutoff right) :
    Q'.ofNat (fusionPathMultiplicity cutoff
        (left ++ [fixed] ++ right.reverse)) ≈
      listQSum (fun source =>
        listQSum (fun target =>
          (Q'.ofNat (fusionChannelAmplitude cutoff left source) *
            Q'.ofNat (boolMultiplicity
              (fusionOK source fixed target))) *
            Q'.ofNat (fusionChannelAmplitude cutoff right target))
          (List.range (cutoff + 1)))
        (List.range (cutoff + 1)) := by
  rw [fusionPathMultiplicity_fixedFace_channel_factorization
    hfixed hleft hright]
  refine Q'.eqv_trans _ _ _
    (ofNat_nestedChannelSum_eqv cutoff
      (fun source target =>
        (fusionChannelAmplitude cutoff left source *
          boolMultiplicity (fusionOK source fixed target)) *
          fusionChannelAmplitude cutoff right target)) ?_
  apply listQSum_congr
  intro source
  apply listQSum_congr
  intro target
  exact ofNat_three_mul_eqv
    (fusionChannelAmplitude cutoff left source)
    (boolMultiplicity (fusionOK source fixed target))
    (fusionChannelAmplitude cutoff right target)

/-! ## 3. Heat-kernel-resummed channel and physical link kernels -/

/-- The fixed-face heat-kernel multiplication matrix on the finite open
channel space. -/
def adjacentEvenResummedFaceChannelKernel
    (cutoff : Nat) (w : Q') (source target : Nat) : Q' :=
  listQSum (fun fixed =>
    coeffAt (heatKernelPacket cutoff w) fixed *
      Q'.ofNat (boolMultiplicity (fusionOK source fixed target)))
    (List.range (cutoff + 1))

/-- The same resummation before splitting the lower and reflected halves into
open channels. -/
def adjacentEvenResummedFixedFaceLinkKernel
    (cutoff : Nat) (w : Q') (left right : List Nat) : Q' :=
  listQSum (fun fixed =>
    coeffAt (heatKernelPacket cutoff w) fixed *
      Q'.ofNat (fusionPathMultiplicity cutoff
        (left ++ [fixed] ++ right.reverse)))
    (List.range (cutoff + 1))

def adjacentEvenResummedFaceChannelAmplitude
    (cutoff : Nat) (state : List Nat) (channel : Nat) : Q' :=
  Q'.ofNat (fusionChannelAmplitude cutoff state channel)

/-- Bilinear contraction of the two half-state channel vectors through the
resummed fixed-face multiplication matrix. -/
def adjacentEvenResummedFaceChannelBilinear
    (cutoff : Nat) (w : Q') (left right : List Nat) : Q' :=
  listQSum (fun source =>
    listQSum (fun target =>
      (adjacentEvenResummedFaceChannelAmplitude cutoff left source *
        adjacentEvenResummedFaceChannelKernel cutoff w source target) *
        adjacentEvenResummedFaceChannelAmplitude cutoff right target)
      (List.range (cutoff + 1)))
    (List.range (cutoff + 1))

private theorem resummedTerm_rearrange
    (a left indicator right : Q') :
    a * ((left * indicator) * right) ≈
      (left * (a * indicator)) * right := by
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv a (left * indicator) right)) ?_
  refine Q'.mul_eqv_congr_right _ _ right ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv a left indicator)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right (a * left) (left * a) indicator
      (Q'.mul_comm_eqv a left)) ?_
  exact Q'.mul_assoc_eqv left a indicator

/-- Exact finite-cutoff identification of the literal, heat-kernel-resummed
fixed-face link count with its arbitrary-channel bilinear matrix form. -/
theorem adjacentEvenResummedFixedFaceLinkKernel_eqv_channelBilinear
    {cutoff : Nat} {w : Q'} {left right : List Nat}
    (hleft : SpinsBounded cutoff left)
    (hright : SpinsBounded cutoff right) :
    adjacentEvenResummedFixedFaceLinkKernel cutoff w left right ≈
      adjacentEvenResummedFaceChannelBilinear cutoff w left right := by
  let faces := List.range (cutoff + 1)
  let channels := List.range (cutoff + 1)
  let faceWeight : Nat → Q' := fun fixed =>
    coeffAt (heatKernelPacket cutoff w) fixed
  let leftAmplitude : Nat → Q' := fun source =>
    adjacentEvenResummedFaceChannelAmplitude cutoff left source
  let rightAmplitude : Nat → Q' := fun target =>
    adjacentEvenResummedFaceChannelAmplitude cutoff right target
  let indicator : Nat → Nat → Nat → Q' :=
    fun fixed source target =>
      Q'.ofNat (boolMultiplicity (fusionOK source fixed target))
  let term : Nat → Nat → Nat → Q' :=
    fun fixed source target =>
      faceWeight fixed *
        ((leftAmplitude source * indicator fixed source target) *
          rightAmplitude target)
  have hfixed :
      adjacentEvenResummedFixedFaceLinkKernel cutoff w left right ≈
        listQSum (fun fixed =>
          faceWeight fixed *
            listQSum (fun source =>
              listQSum (fun target =>
                (leftAmplitude source * indicator fixed source target) *
                  rightAmplitude target) channels) channels) faces := by
    unfold adjacentEvenResummedFixedFaceLinkKernel faces channels
      faceWeight leftAmplitude rightAmplitude indicator
    apply listQSum_congr_on
    intro fixed hfixedMem
    have hfixedBound : fixed ≤ cutoff := by
      have hlt := List.mem_range.mp hfixedMem
      omega
    exact Q'.mul_eqv_congr_left _ _ _
      (fixedFaceRationalChannelFactorization
        hfixedBound hleft hright)
  have hdistributed :
      listQSum (fun fixed =>
          faceWeight fixed *
            listQSum (fun source =>
              listQSum (fun target =>
                (leftAmplitude source * indicator fixed source target) *
                  rightAmplitude target) channels) channels) faces ≈
        listQSum (fun fixed =>
          listQSum (fun source =>
            listQSum (fun target => term fixed source target)
              channels) channels) faces := by
    apply listQSum_congr
    intro fixed
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (listQSum_mul_left (faceWeight fixed)
        (fun source => listQSum (fun target =>
          (leftAmplitude source * indicator fixed source target) *
            rightAmplitude target) channels) channels)) ?_
    apply listQSum_congr
    intro source
    exact Q'.eqv_symm (listQSum_mul_left (faceWeight fixed)
      (fun target =>
        (leftAmplitude source * indicator fixed source target) *
          rightAmplitude target) channels)
  have hswapSource :
      listQSum (fun fixed =>
          listQSum (fun source =>
            listQSum (fun target => term fixed source target)
              channels) channels) faces ≈
        listQSum (fun source =>
          listQSum (fun fixed =>
            listQSum (fun target => term fixed source target)
              channels) faces) channels :=
    Q'.eqv_symm (listQSum_swap
      (fun fixed source =>
        listQSum (fun target => term fixed source target) channels)
      faces channels)
  have hswapTarget :
      listQSum (fun source =>
          listQSum (fun fixed =>
            listQSum (fun target => term fixed source target)
              channels) faces) channels ≈
        listQSum (fun source =>
          listQSum (fun target =>
            listQSum (fun fixed => term fixed source target) faces)
            channels) channels := by
    apply listQSum_congr
    intro source
    exact Q'.eqv_symm (listQSum_swap
      (fun fixed target => term fixed source target)
      faces channels)
  have hcollapse :
      listQSum (fun source =>
          listQSum (fun target =>
            listQSum (fun fixed => term fixed source target) faces)
            channels) channels ≈
        adjacentEvenResummedFaceChannelBilinear
          cutoff w left right := by
    unfold adjacentEvenResummedFaceChannelBilinear
    apply listQSum_congr
    intro source
    apply listQSum_congr
    intro target
    have hrearrange :
        listQSum (fun fixed => term fixed source target) faces ≈
          listQSum (fun fixed =>
            (leftAmplitude source *
              (faceWeight fixed * indicator fixed source target)) *
              rightAmplitude target) faces := by
      apply listQSum_congr
      intro fixed
      exact resummedTerm_rearrange
        (faceWeight fixed) (leftAmplitude source)
        (indicator fixed source target) (rightAmplitude target)
    refine Q'.eqv_trans _ _ _ hrearrange ?_
    refine Q'.eqv_trans _ _ _
      (listQSum_mul_right
        (fun fixed => leftAmplitude source *
          (faceWeight fixed * indicator fixed source target))
        (rightAmplitude target) faces) ?_
    refine Q'.mul_eqv_congr_right _ _ (rightAmplitude target) ?_
    refine Q'.eqv_trans _ _ _
      (listQSum_mul_left (leftAmplitude source)
        (fun fixed => faceWeight fixed * indicator fixed source target)
        faces) ?_
    exact Q'.mul_eqv_congr_left (leftAmplitude source) _ _
      (Q'.eqv_refl _)
  exact Q'.eqv_trans _ _ _ hfixed
    (Q'.eqv_trans _ _ _ hdistributed
      (Q'.eqv_trans _ _ _ hswapSource
        (Q'.eqv_trans _ _ _ hswapTarget hcollapse)))

/-! ## 4. Arbitrary-cutoff anchor row envelope -/

/-- Delta-ladder envelope for every output of tensoring `source` with the
fixed face representation.  It deliberately runs to `fixed`, so its length
is independent of the source channel and of the ambient cutoff. -/
def fusionOutputEnvelope (source fixed target : Nat) : Q' :=
  fsum (fun rung =>
    delta
      (YMGap.Continuum.ChebOrthogonality.fusionLow source fixed +
        2 * rung) target) (fixed + 1)

theorem fusionInd_le_outputEnvelope (source fixed target : Nat) :
    fusionInd source fixed target ≤
      fusionOutputEnvelope source fixed target := by
  unfold fusionInd
  by_cases hok : fusionOK source fixed target
  · rw [if_pos hok]
    obtain ⟨rung, hrung, htarget⟩ :=
      (fusionOK_iff_ascending source fixed target).1 hok
    have hrungLt : rung < fixed + 1 := by omega
    have hdelta :
        delta
          (YMGap.Continuum.ChebOrthogonality.fusionLow source fixed +
            2 * rung) target = 1 := by
      unfold delta
      rw [if_pos htarget]
    have hterm := fsum_term_le_of_nonneg
      (fun rung => delta_nonneg
        (YMGap.Continuum.ChebOrthogonality.fusionLow source fixed +
          2 * rung) target)
      rung (fixed + 1) hrungLt
    rw [hdelta] at hterm
    exact hterm
  · rw [if_neg hok]
    exact fsum_nonneg (fun rung => delta_nonneg
      (YMGap.Continuum.ChebOrthogonality.fusionLow source fixed +
        2 * rung) target) (fixed + 1)

private theorem fsum_le_of_each_le_one (value : Nat → Q')
    (hvalue : ∀ index, value index ≤ (1 : Q')) :
    ∀ count, fsum value count ≤ Q'.ofNat count
  | 0 => Q'.le_refl' 0
  | count + 1 => by
      have hsum : fsum value count + value count ≤
          Q'.ofNat count + (1 : Q') :=
        Q'.add_le_add (fsum_le_of_each_le_one value hvalue count)
          (hvalue count)
      exact Q'.le_trans' _ _ _ hsum
        (Q'.ge_of_eqv (ofNat_succ_eqv count))

/-- A complete or truncated output row of the fixed-spin SU(2) fusion matrix
has at most `fixed+1` nonzero entries. -/
theorem fusionOutputRowCount_le_dimension
    (cutoff source fixed : Nat) :
    fsum (fun target => fusionInd source fixed target) (cutoff + 1) ≤
      Q'.ofNat (fixed + 1) := by
  have hpoint := fsum_mono
    (fun target => fusionInd_le_outputEnvelope source fixed target)
    (cutoff + 1)
  have hswap :
      fsum (fun target => fusionOutputEnvelope source fixed target)
          (cutoff + 1) ≈
        fsum (fun rung =>
          fsum (fun target =>
            delta
              (YMGap.Continuum.ChebOrthogonality.fusionLow source fixed +
                2 * rung) target) (cutoff + 1))
          (fixed + 1) :=
    fsum_swap
      (fun target rung =>
        delta
          (YMGap.Continuum.ChebOrthogonality.fusionLow source fixed +
            2 * rung) target)
      (cutoff + 1) (fixed + 1)
  have hrows :
      fsum (fun rung =>
          fsum (fun target =>
            delta
              (YMGap.Continuum.ChebOrthogonality.fusionLow source fixed +
                2 * rung) target) (cutoff + 1))
          (fixed + 1) ≤ Q'.ofNat (fixed + 1) :=
    fsum_le_of_each_le_one _ (fun rung =>
      fsum_delta_le_one
        (YMGap.Continuum.ChebOrthogonality.fusionLow source fixed +
          2 * rung) (cutoff + 1)) (fixed + 1)
  exact Q'.le_trans' _ _ _ hpoint
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hswap) hrows)

/-- The excited fixed-face part of the resummed anchor channel matrix. -/
def anchorExcitedFaceChannelKernel
    (cutoff source target : Nat) : Q' :=
  fsum (fun index =>
    coeffW anchorCoupling (1 + index) *
      fusionInd source (1 + index) target) cutoff

def anchorExcitedFaceChannelRowSum
    (cutoff source : Nat) : Q' :=
  fsum (fun target =>
    anchorExcitedFaceChannelKernel cutoff source target) (cutoff + 1)

private theorem anchorWeightedCoeff_eq_tailTerm (fixed : Nat) :
    coeffW anchorCoupling fixed * Q'.ofNat (fixed + 1) ≈
      tailTerm anchorCoupling 2 fixed := by
  unfold coeffW dimQ tailTerm
  rw [Nat.pow_two]
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (Q'.ofNat (fixed + 1))
        (qpow anchorCoupling (c4 fixed)) (Q'.ofNat (fixed + 1)))
      (Q'.mul_eqv_congr_left (Q'.ofNat (fixed + 1)) _ _
        (Q'.mul_comm_eqv
          (qpow anchorCoupling (c4 fixed))
          (Q'.ofNat (fixed + 1))))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv
      (Q'.ofNat (fixed + 1)) (Q'.ofNat (fixed + 1))
      (qpow anchorCoupling (c4 fixed)))) ?_
  exact Q'.mul_eqv_congr_right _ _
    (qpow anchorCoupling (c4 fixed))
    (Q'.eqv_symm (ofNat_mul_eqv (fixed + 1) (fixed + 1)))

/-- Degree-two Gaussian tail: it pays simultaneously for the character
dimension in `coeffW` and for the number of fusion outputs. -/
theorem anchorWeightedExcitedFaceTail_le_half (cutoff : Nat) :
    tailWindow anchorCoupling 2 1 cutoff ≤ dyad 1 := by
  exact tail_modulus
    (w := anchorCoupling) (by decide) (by decide)
    2 1 1 (by decide) (by decide) cutoff

/-- Uniform row bound for every channel and every representation cutoff.  The
entire excited resummed face contribution has row mass at most `1/2`. -/
theorem anchorExcitedFaceChannelRowSum_le_half
    (cutoff source : Nat) :
    anchorExcitedFaceChannelRowSum cutoff source ≤ dyad 1 := by
  have hswap :
      anchorExcitedFaceChannelRowSum cutoff source ≈
        fsum (fun index =>
          fsum (fun target =>
            coeffW anchorCoupling (1 + index) *
              fusionInd source (1 + index) target) (cutoff + 1))
          cutoff := by
    unfold anchorExcitedFaceChannelRowSum
      anchorExcitedFaceChannelKernel
    exact fsum_swap
      (fun target index =>
        coeffW anchorCoupling (1 + index) *
          fusionInd source (1 + index) target)
      (cutoff + 1) cutoff
  have hterm : ∀ index,
      fsum (fun target =>
          coeffW anchorCoupling (1 + index) *
            fusionInd source (1 + index) target) (cutoff + 1) ≤
        tailTerm anchorCoupling 2 (1 + index) := by
    intro index
    have hfactor :
        fsum (fun target =>
            coeffW anchorCoupling (1 + index) *
              fusionInd source (1 + index) target) (cutoff + 1) ≈
          coeffW anchorCoupling (1 + index) *
            fsum (fun target =>
              fusionInd source (1 + index) target) (cutoff + 1) :=
      Q'.eqv_symm (fsum_const_mul
        (coeffW anchorCoupling (1 + index))
        (fun target => fusionInd source (1 + index) target)
        (cutoff + 1))
    have hcount := fusionOutputRowCount_le_dimension
      cutoff source (1 + index)
    have hscaled :
        coeffW anchorCoupling (1 + index) *
            fsum (fun target =>
              fusionInd source (1 + index) target) (cutoff + 1) ≤
          coeffW anchorCoupling (1 + index) *
            Q'.ofNat ((1 + index) + 1) :=
      Q'.mul_le_mul_of_nonneg_left _ _
        (coeffW anchorCoupling (1 + index)) hcount
        (coeffW_nonneg (by decide) (1 + index))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor)
      (Q'.le_trans' _ _ _ hscaled
        (Q'.le_of_eqv (anchorWeightedCoeff_eq_tailTerm (1 + index))))
  have hsum :
      fsum (fun index =>
        fsum (fun target =>
          coeffW anchorCoupling (1 + index) *
            fusionInd source (1 + index) target) (cutoff + 1))
        cutoff ≤
      fsum (fun index => tailTerm anchorCoupling 2 (1 + index))
        cutoff :=
    fsum_mono hterm cutoff
  have htail :
      fsum (fun index => tailTerm anchorCoupling 2 (1 + index))
          cutoff = tailWindow anchorCoupling 2 1 cutoff := by
    unfold tailWindow
    rw [← YMGap.Continuum.MovingCutoff.fsum_eq_finSum]
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hswap)
    (Q'.le_trans' _ _ _ hsum (by
      rw [htail]
      exact anchorWeightedExcitedFaceTail_le_half cutoff))

/-! ## 5. A constructive diagonal-dominance Gram/SOS -/

def finiteDoubleSum (term : Nat → Nat → Q') (count : Nat) : Q' :=
  fsum (fun first => fsum (term first) count) count

private theorem finiteDoubleSum_congr
    (left right : Nat → Nat → Q')
    (h : ∀ first second, left first second ≈ right first second)
    (count : Nat) :
    finiteDoubleSum left count ≈ finiteDoubleSum right count := by
  unfold finiteDoubleSum
  apply fsum_eqv_congr
  intro first
  apply fsum_eqv_congr
  intro second
  exact h first second

private theorem finiteDoubleSum_add
    (left right : Nat → Nat → Q') (count : Nat) :
    finiteDoubleSum (fun first second =>
      left first second + right first second) count ≈
      finiteDoubleSum left count + finiteDoubleSum right count := by
  unfold finiteDoubleSum
  refine Q'.eqv_trans _ _ _
    (fsum_eqv_congr _ _ (fun first =>
      fsum_add (left first) (right first) count) count) ?_
  exact fsum_add
    (fun first => fsum (left first) count)
    (fun first => fsum (right first) count) count

def finiteRowSum (matrix : Nat → Nat → Q')
    (count row : Nat) : Q' :=
  fsum (matrix row) count

def finiteDiagonalNorm (vector : Nat → Q') (count : Nat) : Q' :=
  fsum (fun row => vector row * vector row) count

def finiteRowWeightedNorm (matrix : Nat → Nat → Q')
    (vector : Nat → Q') (count : Nat) : Q' :=
  fsum (fun row =>
    finiteRowSum matrix count row * (vector row * vector row)) count

def finiteMatrixCross (matrix : Nat → Nat → Q')
    (vector : Nat → Q') (count : Nat) : Q' :=
  finiteDoubleSum (fun row column =>
    matrix row column * (vector row * vector column)) count

def finiteDominantResidual (matrix : Nat → Nat → Q')
    (vector : Nat → Q') (count : Nat) : Q' :=
  fsum (fun row =>
    ((1 : Q') + -finiteRowSum matrix count row) *
      (vector row * vector row)) count

def finiteSymmetricEdgeSOS (matrix : Nat → Nat → Q')
    (vector : Nat → Q') (count : Nat) : Q' :=
  YMGap.Constructive.HalfPow.half *
    finiteDoubleSum (fun row column =>
      matrix row column *
        ((vector row + vector column) *
          (vector row + vector column))) count

def finiteDominantGramSOS (matrix : Nat → Nat → Q')
    (vector : Nat → Q') (count : Nat) : Q' :=
  finiteDominantResidual matrix vector count +
    finiteSymmetricEdgeSOS matrix vector count

def finiteIdentityPlusQuadratic (matrix : Nat → Nat → Q')
    (vector : Nat → Q') (count : Nat) : Q' :=
  finiteDiagonalNorm vector count + finiteMatrixCross matrix vector count

private theorem square_add_expand (left right : Q') :
    (left + right) * (left + right) ≈
      (left * left + left * right) +
        (right * left + right * right) := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_mul_eqv left right (left + right)) ?_
  exact Q'.add_eqv_congr'
    (Q'.mul_add_eqv left left right)
    (Q'.mul_add_eqv right left right)

private theorem edgeTerm_expand
    (weight left right : Q') :
    weight * ((left + right) * (left + right)) ≈
      (weight * (left * left) + weight * (left * right)) +
        (weight * (right * left) + weight * (right * right)) := by
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left weight _ _
      (square_add_expand left right)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_add_eqv weight
      (left * left + left * right)
      (right * left + right * right)) ?_
  exact Q'.add_eqv_congr'
    (Q'.mul_add_eqv weight (left * left) (left * right))
    (Q'.mul_add_eqv weight (right * left) (right * right))

private theorem half_symmetric_four_collapse (row cross : Q') :
    YMGap.Constructive.HalfPow.half *
        ((row + cross) + (cross + row)) ≈
      row + cross := by
  have hinside : ((row + cross) + (cross + row)) ≈
      (row + row) + (cross + cross) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (row + cross) _ _
        (Q'.add_comm_eqv cross row)) ?_
    exact Q'.add_swap_inner row cross row cross
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left YMGap.Constructive.HalfPow.half _ _
      hinside) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_add_eqv YMGap.Constructive.HalfPow.half
      (row + row) (cross + cross)) ?_
  exact Q'.add_eqv_congr'
    (Q'.eqv_trans _ _ _
      (Q'.mul_add_eqv YMGap.Constructive.HalfPow.half row row)
      (YMGap.Constructive.ExpNeg.two_halves row))
    (Q'.eqv_trans _ _ _
      (Q'.mul_add_eqv YMGap.Constructive.HalfPow.half cross cross)
      (YMGap.Constructive.ExpNeg.two_halves cross))

private theorem finiteEdgeLeft_eqv_rowWeighted
    (matrix : Nat → Nat → Q') (vector : Nat → Q') (count : Nat) :
    finiteDoubleSum (fun row column =>
        matrix row column * (vector row * vector row)) count ≈
      finiteRowWeightedNorm matrix vector count := by
  unfold finiteDoubleSum finiteRowWeightedNorm finiteRowSum
  apply fsum_eqv_congr
  intro row
  exact Q'.eqv_symm (fsum_mul_const (matrix row)
    (vector row * vector row) count)

private theorem finiteEdgeRight_eqv_rowWeighted
    (matrix : Nat → Nat → Q') (vector : Nat → Q') (count : Nat)
    (hsymmetric : ∀ row column,
      matrix row column ≈ matrix column row) :
    finiteDoubleSum (fun row column =>
        matrix row column * (vector column * vector column)) count ≈
      finiteRowWeightedNorm matrix vector count := by
  refine Q'.eqv_trans _ _ _
    (fsum_swap (fun row column =>
      matrix row column * (vector column * vector column)) count count) ?_
  unfold finiteRowWeightedNorm finiteRowSum
  apply fsum_eqv_congr
  intro column
  refine Q'.eqv_trans _ _ _
    (fsum_eqv_congr _ _ (fun row =>
      Q'.mul_eqv_congr_right (matrix row column)
        (matrix column row) (vector column * vector column)
        (hsymmetric row column)) count) ?_
  exact Q'.eqv_symm (fsum_mul_const (matrix column)
    (vector column * vector column) count)

private theorem finiteReverseCross_eqv_cross
    (matrix : Nat → Nat → Q') (vector : Nat → Q') (count : Nat) :
    finiteDoubleSum (fun row column =>
        matrix row column * (vector column * vector row)) count ≈
      finiteMatrixCross matrix vector count := by
  unfold finiteMatrixCross
  apply finiteDoubleSum_congr
  intro row column
  exact Q'.mul_eqv_congr_left (matrix row column) _ _
    (Q'.mul_comm_eqv (vector column) (vector row))

theorem finiteSymmetricEdgeSOS_eqv_row_add_cross
    (matrix : Nat → Nat → Q') (vector : Nat → Q') (count : Nat)
    (hsymmetric : ∀ row column,
      matrix row column ≈ matrix column row) :
    finiteSymmetricEdgeSOS matrix vector count ≈
      finiteRowWeightedNorm matrix vector count +
        finiteMatrixCross matrix vector count := by
  let edgeLeft : Nat → Nat → Q' := fun row column =>
    matrix row column * (vector row * vector row)
  let edgeCross : Nat → Nat → Q' := fun row column =>
    matrix row column * (vector row * vector column)
  let edgeReverse : Nat → Nat → Q' := fun row column =>
    matrix row column * (vector column * vector row)
  let edgeRight : Nat → Nat → Q' := fun row column =>
    matrix row column * (vector column * vector column)
  have hexpand :
      finiteDoubleSum (fun row column =>
          matrix row column *
            ((vector row + vector column) *
              (vector row + vector column))) count ≈
        finiteDoubleSum (fun row column =>
          (edgeLeft row column + edgeCross row column) +
            (edgeReverse row column + edgeRight row column)) count := by
    apply finiteDoubleSum_congr
    intro row column
    exact edgeTerm_expand (matrix row column)
      (vector row) (vector column)
  have hsplit :
      finiteDoubleSum (fun row column =>
          (edgeLeft row column + edgeCross row column) +
            (edgeReverse row column + edgeRight row column)) count ≈
        (finiteDoubleSum edgeLeft count +
          finiteDoubleSum edgeCross count) +
          (finiteDoubleSum edgeReverse count +
            finiteDoubleSum edgeRight count) := by
    refine Q'.eqv_trans _ _ _
      (finiteDoubleSum_add
        (fun row column => edgeLeft row column + edgeCross row column)
        (fun row column => edgeReverse row column + edgeRight row column)
        count) ?_
    exact Q'.add_eqv_congr'
      (finiteDoubleSum_add edgeLeft edgeCross count)
      (finiteDoubleSum_add edgeReverse edgeRight count)
  have hcomponents :
      (finiteDoubleSum edgeLeft count +
          finiteDoubleSum edgeCross count) +
          (finiteDoubleSum edgeReverse count +
            finiteDoubleSum edgeRight count) ≈
        (finiteRowWeightedNorm matrix vector count +
          finiteMatrixCross matrix vector count) +
          (finiteMatrixCross matrix vector count +
            finiteRowWeightedNorm matrix vector count) :=
    Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (finiteEdgeLeft_eqv_rowWeighted matrix vector count)
        (Q'.eqv_refl _))
      (Q'.add_eqv_congr'
        (finiteReverseCross_eqv_cross matrix vector count)
        (finiteEdgeRight_eqv_rowWeighted
          matrix vector count hsymmetric))
  unfold finiteSymmetricEdgeSOS
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left YMGap.Constructive.HalfPow.half _ _
      (Q'.eqv_trans _ _ _ hexpand
        (Q'.eqv_trans _ _ _ hsplit hcomponents))) ?_
  exact half_symmetric_four_collapse
    (finiteRowWeightedNorm matrix vector count)
    (finiteMatrixCross matrix vector count)

theorem finiteDominantResidual_eqv_diag_sub_row
    (matrix : Nat → Nat → Q') (vector : Nat → Q') (count : Nat) :
    finiteDominantResidual matrix vector count ≈
      finiteDiagonalNorm vector count +
        -finiteRowWeightedNorm matrix vector count := by
  have hterm : ∀ row,
      (((1 : Q') + -finiteRowSum matrix count row) *
          (vector row * vector row)) ≈
        (vector row * vector row) +
          -(finiteRowSum matrix count row *
            (vector row * vector row)) := by
    intro row
    refine Q'.eqv_trans _ _ _
      (Q'.add_mul_eqv 1 (-finiteRowSum matrix count row)
        (vector row * vector row)) ?_
    exact Q'.add_eqv_congr'
      (Q'.one_mul_eqv (vector row * vector row))
      (Q'.neg_mul_eqv (finiteRowSum matrix count row)
        (vector row * vector row))
  unfold finiteDominantResidual finiteDiagonalNorm
  refine Q'.eqv_trans _ _ _
    (fsum_eqv_congr _ _ hterm count) ?_
  refine Q'.eqv_trans _ _ _
    (fsum_add
      (fun row => vector row * vector row)
      (fun row => -(finiteRowSum matrix count row *
        (vector row * vector row))) count) ?_
  exact Q'.add_eqv_congr_left _ _ _
    (fsum_neg
      (fun row => finiteRowSum matrix count row *
        (vector row * vector row)) count)

private theorem cancel_row_pair (diagonal row cross : Q') :
    (diagonal + -row) + (row + cross) ≈ diagonal + cross := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv diagonal (-row) (row + cross)) ?_
  refine Q'.add_eqv_congr_left diagonal _ _ ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv (-row) row cross)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right ((-row) + row) 0 cross
      (Q'.neg_add_self_eqv row)) ?_
  exact q_zero_add_eqv cross

theorem finiteDominantGramSOS_eqv_identityPlusQuadratic
    (matrix : Nat → Nat → Q') (vector : Nat → Q') (count : Nat)
    (hsymmetric : ∀ row column,
      matrix row column ≈ matrix column row) :
    finiteDominantGramSOS matrix vector count ≈
      finiteIdentityPlusQuadratic matrix vector count := by
  unfold finiteDominantGramSOS finiteIdentityPlusQuadratic
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (finiteDominantResidual_eqv_diag_sub_row matrix vector count)
      (finiteSymmetricEdgeSOS_eqv_row_add_cross
        matrix vector count hsymmetric)) ?_
  exact cancel_row_pair
    (finiteDiagonalNorm vector count)
    (finiteRowWeightedNorm matrix vector count)
    (finiteMatrixCross matrix vector count)

theorem finiteDominantGramSOS_nonnegative
    (matrix : Nat → Nat → Q') (vector : Nat → Q') (count : Nat)
    (hmatrix : ∀ row column, (0 : Q') ≤ matrix row column)
    (hrow : ∀ row, finiteRowSum matrix count row ≤ (1 : Q')) :
    (0 : Q') ≤ finiteDominantGramSOS matrix vector count := by
  have hresidual : (0 : Q') ≤
      finiteDominantResidual matrix vector count := by
    unfold finiteDominantResidual
    exact fsum_nonneg (fun row =>
      Q'.mul_nonneg _ _
        (Q'.sub_nonneg_of_le (hrow row))
        (q_mul_self_nonneg (vector row))) count
  have hedge : (0 : Q') ≤
      finiteSymmetricEdgeSOS matrix vector count := by
    unfold finiteSymmetricEdgeSOS finiteDoubleSum
    exact Q'.mul_nonneg _ _ (by decide)
      (fsum_nonneg (fun row =>
        fsum_nonneg (fun column =>
          Q'.mul_nonneg _ _ (hmatrix row column)
            (q_mul_self_nonneg (vector row + vector column))) count) count)
  exact Q'.zero_le_add _ _ hresidual hedge

theorem finiteIdentityPlusQuadratic_nonnegative_of_dominance
    (matrix : Nat → Nat → Q') (vector : Nat → Q') (count : Nat)
    (hmatrix : ∀ row column, (0 : Q') ≤ matrix row column)
    (hsymmetric : ∀ row column,
      matrix row column ≈ matrix column row)
    (hrow : ∀ row, finiteRowSum matrix count row ≤ (1 : Q')) :
    (0 : Q') ≤ finiteIdentityPlusQuadratic matrix vector count := by
  have hsos := finiteDominantGramSOS_nonnegative
    matrix vector count hmatrix hrow
  exact Q'.le_trans' _ _ _ hsos
    (Q'.le_of_eqv
      (finiteDominantGramSOS_eqv_identityPlusQuadratic
        matrix vector count hsymmetric))

/-! ## 6. Arbitrary-cutoff anchor channel PSD -/

theorem anchorExcitedFaceChannelKernel_nonnegative
    (cutoff source target : Nat) :
    (0 : Q') ≤ anchorExcitedFaceChannelKernel cutoff source target := by
  unfold anchorExcitedFaceChannelKernel
  exact fsum_nonneg (fun index =>
    Q'.mul_nonneg _ _
      (coeffW_nonneg (by decide) (1 + index))
      (fusionInd_nonneg source (1 + index) target)) cutoff

theorem anchorExcitedFaceChannelKernel_symmetric
    (cutoff source target : Nat) :
    anchorExcitedFaceChannelKernel cutoff source target ≈
      anchorExcitedFaceChannelKernel cutoff target source := by
  unfold anchorExcitedFaceChannelKernel
  apply fsum_eqv_congr
  intro index
  apply Q'.mul_eqv_congr_left
  unfold fusionInd
  rw [fusionOK_reverse_step source (1 + index) target]
  exact Q'.eqv_refl _

theorem anchorExcitedFaceChannelRowSum_le_one
    (cutoff source : Nat) :
    finiteRowSum (anchorExcitedFaceChannelKernel cutoff)
        (cutoff + 1) source ≤ (1 : Q') := by
  have hhalf := anchorExcitedFaceChannelRowSum_le_half cutoff source
  have hidentify :
      finiteRowSum (anchorExcitedFaceChannelKernel cutoff)
          (cutoff + 1) source =
        anchorExcitedFaceChannelRowSum cutoff source := rfl
  rw [hidentify]
  exact Q'.le_trans' _ _ _ hhalf (by
    unfold dyad YMGap.Constructive.HalfPow.half
    decide)

/-- Arbitrary-cutoff PSD of the complete resummed face channel matrix at the
anchor.  The vacuum face supplies the identity; all excited faces form the
uniformly row-dominated symmetric matrix proved above. -/
theorem anchorResummedFaceChannelQuadratic_nonnegative
    (cutoff : Nat) (vector : Nat → Q') :
    (0 : Q') ≤
      finiteIdentityPlusQuadratic
        (anchorExcitedFaceChannelKernel cutoff)
        vector (cutoff + 1) := by
  exact finiteIdentityPlusQuadratic_nonnegative_of_dominance
    (anchorExcitedFaceChannelKernel cutoff) vector (cutoff + 1)
    (anchorExcitedFaceChannelKernel_nonnegative cutoff)
    (anchorExcitedFaceChannelKernel_symmetric cutoff)
    (anchorExcitedFaceChannelRowSum_le_one cutoff)

/-! ## 7. Identification with the production resummed channel matrix -/

private theorem listQSum_append_local {A : Type}
    (value : A → Q') : ∀ left right : List A,
    listQSum value (left ++ right) ≈
      listQSum value left + listQSum value right
  | [], right => Q'.eqv_symm (q_zero_add_eqv _)
  | head :: tail, right => by
      simp only [List.cons_append, listQSum]
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (value head) _ _
          (listQSum_append_local value tail right)) ?_
      exact Q'.eqv_symm (Q'.add_assoc_eqv
        (value head) (listQSum value tail) (listQSum value right))

private theorem listQSum_range_eqv_fsum
    (value : Nat → Q') : ∀ count,
    listQSum value (List.range count) ≈ fsum value count
  | 0 => Q'.eqv_refl 0
  | count + 1 => by
      rw [List.range_succ]
      refine Q'.eqv_trans _ _ _
        (listQSum_append_local value (List.range count) [count]) ?_
      simp only [listQSum]
      change listQSum value (List.range count) + (value count + 0) ≈
        fsum value count + value count
      exact Q'.add_eqv_congr'
        (listQSum_range_eqv_fsum value count)
        (q_add_zero_eqv (value count))

private theorem ofNat_boolMultiplicity_eqv_fusionInd
    (source fixed target : Nat) :
    Q'.ofNat (boolMultiplicity (fusionOK source fixed target)) ≈
      fusionInd source fixed target := by
  unfold boolMultiplicity fusionInd
  cases fusionOK source fixed target <;> exact Q'.eqv_refl _

theorem adjacentEvenResummedFaceChannelKernel_anchor_eqv_identity_add_excited
    (cutoff source target : Nat) :
    adjacentEvenResummedFaceChannelKernel
        cutoff anchorCoupling source target ≈
      delta source target +
        anchorExcitedFaceChannelKernel cutoff source target := by
  let packetTerm : Nat → Q' := fun fixed =>
    coeffAt (heatKernelPacket cutoff anchorCoupling) fixed *
      Q'.ofNat (boolMultiplicity (fusionOK source fixed target))
  let fusionTerm : Nat → Q' := fun fixed =>
    coeffW anchorCoupling fixed * fusionInd source fixed target
  have htoFsum :
      adjacentEvenResummedFaceChannelKernel
          cutoff anchorCoupling source target ≈
        fsum packetTerm (cutoff + 1) := by
    unfold adjacentEvenResummedFaceChannelKernel
    exact listQSum_range_eqv_fsum packetTerm (cutoff + 1)
  have hpacket : fsum packetTerm (cutoff + 1) ≈
      fsum fusionTerm (cutoff + 1) := by
    apply fsum_eqv_congr_lt
    intro fixed hfixed
    unfold packetTerm fusionTerm
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (ofNat_boolMultiplicity_eqv_fusionInd source fixed target)) ?_
    exact Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_of_eq (coeffAt_heatKernelPacket hfixed))
  have hpeel : fsum fusionTerm (cutoff + 1) ≈
      fusionTerm 0 + fsum (fun index => fusionTerm (index + 1)) cutoff :=
    fsum_peel fusionTerm cutoff
  have hvacuum : fusionTerm 0 ≈ delta source target := by
    unfold fusionTerm
    rw [coeffW_zero]
    refine Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) ?_
    unfold fusionInd delta
    rw [fusionOK_zero_right_eq_decide]
    by_cases heq : target = source
    · rw [if_pos heq]
      simp [heq]
      exact Q'.eqv_refl _
    · rw [if_neg heq]
      simp [heq]
      exact Q'.eqv_refl _
  have hexcited :
      fsum (fun index => fusionTerm (index + 1)) cutoff ≈
        anchorExcitedFaceChannelKernel cutoff source target := by
    unfold fusionTerm anchorExcitedFaceChannelKernel
    apply fsum_eqv_congr
    intro index
    have hindex : index + 1 = 1 + index := by omega
    rw [hindex]
    exact Q'.eqv_refl _
  exact Q'.eqv_trans _ _ _ htoFsum
    (Q'.eqv_trans _ _ _ hpacket
      (Q'.eqv_trans _ _ _ hpeel
        (Q'.add_eqv_congr' hvacuum hexcited)))

def adjacentEvenAnchorResummedChannelQuadratic
    (cutoff : Nat) (vector : Nat → Q') : Q' :=
  finiteDoubleSum (fun source target =>
    (vector source * vector target) *
      adjacentEvenResummedFaceChannelKernel
        cutoff anchorCoupling source target) (cutoff + 1)

private theorem finiteDeltaQuadratic_eqv_diagonal
    (vector : Nat → Q') (count : Nat) :
    finiteDoubleSum (fun source target =>
        (vector source * vector target) * delta source target) count ≈
      finiteDiagonalNorm vector count := by
  unfold finiteDoubleSum finiteDiagonalNorm
  apply fsum_eqv_congr_lt
  intro source hsource
  refine Q'.eqv_trans _ _ _
    (fsum_eqv_congr_lt _ _ count (fun target _ =>
      Q'.eqv_trans _ _ _
        (Q'.mul_comm_eqv
          (vector source * vector target) (delta source target))
        (Q'.mul_eqv_congr_left (delta source target) _ _
          (Q'.eqv_refl _)))) ?_
  unfold delta
  exact Q'.eqv_trans _ _ _
    (delta_fsum (fun target => vector source * vector target)
      source count hsource)
    (Q'.eqv_refl _)

theorem adjacentEvenAnchorResummedChannelQuadratic_eqv_dominantForm
    (cutoff : Nat) (vector : Nat → Q') :
    adjacentEvenAnchorResummedChannelQuadratic cutoff vector ≈
      finiteIdentityPlusQuadratic
        (anchorExcitedFaceChannelKernel cutoff)
        vector (cutoff + 1) := by
  unfold adjacentEvenAnchorResummedChannelQuadratic
    finiteIdentityPlusQuadratic
  have hkernel :
      finiteDoubleSum (fun source target =>
          (vector source * vector target) *
            adjacentEvenResummedFaceChannelKernel
              cutoff anchorCoupling source target) (cutoff + 1) ≈
        finiteDoubleSum (fun source target =>
          (vector source * vector target) *
            (delta source target +
              anchorExcitedFaceChannelKernel cutoff source target))
          (cutoff + 1) := by
    apply finiteDoubleSum_congr
    intro source target
    exact Q'.mul_eqv_congr_left (vector source * vector target) _ _
      (adjacentEvenResummedFaceChannelKernel_anchor_eqv_identity_add_excited
        cutoff source target)
  have hdistribute :
      finiteDoubleSum (fun source target =>
          (vector source * vector target) *
            (delta source target +
              anchorExcitedFaceChannelKernel cutoff source target))
          (cutoff + 1) ≈
        finiteDoubleSum (fun source target =>
          (vector source * vector target) * delta source target)
            (cutoff + 1) +
          finiteDoubleSum (fun source target =>
            (vector source * vector target) *
              anchorExcitedFaceChannelKernel cutoff source target)
            (cutoff + 1) := by
    refine Q'.eqv_trans _ _ _
      (finiteDoubleSum_congr _ _ (fun source target =>
        Q'.mul_add_eqv (vector source * vector target)
          (delta source target)
          (anchorExcitedFaceChannelKernel cutoff source target))
        (cutoff + 1)) ?_
    exact finiteDoubleSum_add _ _ (cutoff + 1)
  have hcross :
      finiteDoubleSum (fun source target =>
          (vector source * vector target) *
            anchorExcitedFaceChannelKernel cutoff source target)
          (cutoff + 1) ≈
        finiteMatrixCross (anchorExcitedFaceChannelKernel cutoff)
          vector (cutoff + 1) := by
    unfold finiteMatrixCross
    apply finiteDoubleSum_congr
    intro source target
    exact Q'.mul_comm_eqv _ _
  exact Q'.eqv_trans _ _ _ hkernel
    (Q'.eqv_trans _ _ _ hdistribute
      (Q'.add_eqv_congr'
        (finiteDeltaQuadratic_eqv_diagonal vector (cutoff + 1))
        hcross))

/-- Arbitrary-cutoff PSD for the exact production resummed channel kernel,
not merely for the auxiliary identity-plus-excited presentation. -/
theorem adjacentEvenAnchorResummedChannelQuadratic_nonnegative
    (cutoff : Nat) (vector : Nat → Q') :
    (0 : Q') ≤
      adjacentEvenAnchorResummedChannelQuadratic cutoff vector := by
  have hdominant := anchorResummedFaceChannelQuadratic_nonnegative
    cutoff vector
  exact Q'.le_trans' _ _ _ hdominant
    (Q'.le_of_eqv (Q'.eqv_symm
      (adjacentEvenAnchorResummedChannelQuadratic_eqv_dominantForm
        cutoff vector)))

/-! ## 8. The complete cutoff-one channel matrix -/

theorem cutoffOne_resummedChannelKernel_00 (w : Q') :
    adjacentEvenResummedFaceChannelKernel 1 w 0 0 ≈ 1 := by
  change
    coeffAt (heatKernelPacket 1 w) 0 * Q'.ofNat 1 +
      (coeffAt (heatKernelPacket 1 w) 1 * Q'.ofNat 0 + 0) ≈ 1
  rw [coeffAt_heatKernelPacket (by decide), coeffW_zero,
    coeffAt_heatKernelPacket (by decide)]
  have hinner : coeffW w 1 * (0 : Q') + 0 ≈ 0 :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.mul_zero_eqv _) (Q'.eqv_refl 0))
      (q_zero_add_eqv 0)
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.one_mul_eqv 1) hinner)
    (q_add_zero_eqv 1)

theorem cutoffOne_resummedChannelKernel_01 (w : Q') :
    adjacentEvenResummedFaceChannelKernel 1 w 0 1 ≈ coeffW w 1 := by
  change
    coeffAt (heatKernelPacket 1 w) 0 * Q'.ofNat 0 +
      (coeffAt (heatKernelPacket 1 w) 1 * Q'.ofNat 1 + 0) ≈
        coeffW w 1
  rw [coeffAt_heatKernelPacket (by decide), coeffW_zero,
    coeffAt_heatKernelPacket (by decide)]
  have hinner : coeffW w 1 * (1 : Q') + 0 ≈ coeffW w 1 :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.mul_one_eqv _) (Q'.eqv_refl 0))
      (q_add_zero_eqv _)
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.mul_zero_eqv _) hinner)
    (q_zero_add_eqv _)

theorem cutoffOne_resummedChannelKernel_10 (w : Q') :
    adjacentEvenResummedFaceChannelKernel 1 w 1 0 ≈ coeffW w 1 := by
  change
    coeffAt (heatKernelPacket 1 w) 0 * Q'.ofNat 0 +
      (coeffAt (heatKernelPacket 1 w) 1 * Q'.ofNat 1 + 0) ≈
        coeffW w 1
  rw [coeffAt_heatKernelPacket (by decide), coeffW_zero,
    coeffAt_heatKernelPacket (by decide)]
  have hinner : coeffW w 1 * (1 : Q') + 0 ≈ coeffW w 1 :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.mul_one_eqv _) (Q'.eqv_refl 0))
      (q_add_zero_eqv _)
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.mul_zero_eqv _) hinner)
    (q_zero_add_eqv _)

theorem cutoffOne_resummedChannelKernel_11 (w : Q') :
    adjacentEvenResummedFaceChannelKernel 1 w 1 1 ≈ 1 := by
  change
    coeffAt (heatKernelPacket 1 w) 0 * Q'.ofNat 1 +
      (coeffAt (heatKernelPacket 1 w) 1 * Q'.ofNat 0 + 0) ≈ 1
  rw [coeffAt_heatKernelPacket (by decide), coeffW_zero,
    coeffAt_heatKernelPacket (by decide)]
  have hinner : coeffW w 1 * (0 : Q') + 0 ≈ 0 :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.mul_zero_eqv _) (Q'.eqv_refl 0))
      (q_zero_add_eqv 0)
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.one_mul_eqv 1) hinner)
    (q_add_zero_eqv 1)

/-- The literal quadratic form of the full cutoff-one resummed channel
matrix. -/
def cutoffOneResummedChannelQuadratic
    (w x0 x1 : Q') : Q' :=
  (x0 * x0) * adjacentEvenResummedFaceChannelKernel 1 w 0 0 +
    (x0 * x1) * adjacentEvenResummedFaceChannelKernel 1 w 0 1 +
    (x1 * x0) * adjacentEvenResummedFaceChannelKernel 1 w 1 0 +
    (x1 * x1) * adjacentEvenResummedFaceChannelKernel 1 w 1 1

/-- Manifest rational SOS for the cutoff-one channel matrix. -/
def cutoffOneResummedChannelSOS
    (w x0 x1 : Q') : Q' :=
  (x0 + x1 * coeffW w 1) * (x0 + x1 * coeffW w 1) +
    ((1 : Q') + -(coeffW w 1 * coeffW w 1)) * (x1 * x1)

theorem cutoffOneResummedChannelQuadratic_eqv_sos
    (w x0 x1 : Q') :
    cutoffOneResummedChannelQuadratic w x0 x1 ≈
      cutoffOneResummedChannelSOS w x0 x1 := by
  let a := coeffW w 1
  let p := (x0 * x1) * a
  let q0 := x0 * x0
  let q1 := x1 * x1
  have hentries : cutoffOneResummedChannelQuadratic w x0 x1 ≈
      ((((x0 * x0) * 1 + (x0 * x1) * a) +
          (x1 * x0) * a) + (x1 * x1) * 1) := by
    unfold cutoffOneResummedChannelQuadratic
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left (x0 * x0) _ _
            (cutoffOne_resummedChannelKernel_00 w))
          (Q'.mul_eqv_congr_left (x0 * x1) _ _
            (cutoffOne_resummedChannelKernel_01 w)))
        (Q'.mul_eqv_congr_left (x1 * x0) _ _
          (cutoffOne_resummedChannelKernel_10 w)))
      (Q'.mul_eqv_congr_left (x1 * x1) _ _
        (cutoffOne_resummedChannelKernel_11 w))
  have hreverse : (x1 * x0) * a ≈ p :=
    Q'.mul_eqv_congr_right (x1 * x0) (x0 * x1) a
      (Q'.mul_comm_eqv x1 x0)
  have hnormalized :
      ((((x0 * x0) * 1 + (x0 * x1) * a) +
          (x1 * x0) * a) + (x1 * x1) * 1) ≈
        ((q0 + p) + p) + q1 := by
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.mul_one_eqv (x0 * x0)) (Q'.eqv_refl p))
        hreverse)
      (Q'.mul_one_eqv (x1 * x1))
  have hcross : p + p ≈ ((2 : Q') * (x0 * x1)) * a := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (q_add_mul (x0 * x1) (x0 * x1) a)) ?_
    exact Q'.mul_eqv_congr_right
      ((x0 * x1) + (x0 * x1)) ((2 : Q') * (x0 * x1)) a
      (YMGap.Continuum.Pivot2.twoMul (x0 * x1))
  have hregroup : ((q0 + p) + p) + q1 ≈
      (q0 + ((2 : Q') * (x0 * x1)) * a) + q1 := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right ((q0 + p) + p) (q0 + (p + p)) q1
        (Q'.add_assoc_eqv q0 p p)) ?_
    exact Q'.add_eqv_congr_right _ _ q1
      (Q'.add_eqv_congr_left q0 _ _ hcross)
  have honePlusZero : ((1 : Q') + 0) ≈ 1 := q_add_zero_eqv 1
  have hq0Raw : q0 ≈ q0 * (1 : Q') :=
    Q'.eqv_symm (Q'.mul_one_eqv q0)
  have hq1Raw : q1 ≈ q1 * ((1 : Q') + 0) := by
    refine Q'.eqv_symm (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left q1 ((1 : Q') + 0) 1 honePlusZero) ?_)
    exact Q'.mul_one_eqv q1
  have htoPivot :
      (q0 + ((2 : Q') * (x0 * x1)) * a) + q1 ≈
        ((q0 * (1 : Q') + ((2 : Q') * (x0 * x1)) * a) +
          q1 * ((1 : Q') + 0)) :=
    Q'.add_eqv_congr'
      (Q'.add_eqv_congr_right q0 (q0 * (1 : Q'))
        (((2 : Q') * (x0 * x1)) * a) hq0Raw)
      hq1Raw
  have hpivot := YMGap.Continuum.Pivot2.schur_q
    (1 : Q') x0 x1 a 0 (Q'.eqv_refl 1)
  have hsquareHead :
      ((0 : Q') + (1 : Q') *
          ((x0 + x1 * a) * (x0 + x1 * a))) ≈
        (x0 + x1 * a) * (x0 + x1 * a) := by
    refine Q'.eqv_trans _ _ _ (q_zero_add_eqv _) ?_
    exact Q'.one_mul_eqv _
  have hpivotCoeff :
      (((1 : Q') + 0) + -(a * a)) ≈
        (1 : Q') + -(a * a) :=
    Q'.add_eqv_congr_right ((1 : Q') + 0) 1 (-(a * a))
      honePlusZero
  have hpivotTail :
      ((((1 : Q') + 0) + -(a * a)) * (x1 * x1)) ≈
        (((1 : Q') + -(a * a)) * (x1 * x1)) :=
    Q'.mul_eqv_congr_right _ _ (x1 * x1) hpivotCoeff
  have hfromPivot :
      (((0 : Q') + (1 : Q') *
          ((x0 + x1 * a) * (x0 + x1 * a))) +
          (((1 : Q') + 0) + -(a * a)) * (x1 * x1)) ≈
        cutoffOneResummedChannelSOS w x0 x1 := by
    unfold cutoffOneResummedChannelSOS
    exact Q'.add_eqv_congr' hsquareHead hpivotTail
  exact Q'.eqv_trans _ _ _ hentries
    (Q'.eqv_trans _ _ _ hnormalized
      (Q'.eqv_trans _ _ _ hregroup
        (Q'.eqv_trans _ _ _ htoPivot
          (Q'.eqv_trans _ _ _ hpivot hfromPivot))))

theorem cutoffOneResummedChannelQuadratic_nonnegative
    {w : Q'} (hcoeff0 : (0 : Q') ≤ coeffW w 1)
    (hcoeff1 : coeffW w 1 ≤ (1 : Q')) (x0 x1 : Q') :
    (0 : Q') ≤ cutoffOneResummedChannelQuadratic w x0 x1 := by
  have hsos : (0 : Q') ≤ cutoffOneResummedChannelSOS w x0 x1 := by
    unfold cutoffOneResummedChannelSOS
    have hsqCoeff : coeffW w 1 * coeffW w 1 ≤ (1 : Q') := by
      have hfirst := Q'.mul_le_mul_of_nonneg_right
        (coeffW w 1) 1 (coeffW w 1) hcoeff1 hcoeff0
      have hsecond := Q'.mul_le_mul_of_nonneg_left
        (coeffW w 1) 1 1 hcoeff1 (by decide)
      exact Q'.le_trans' _ _ _ hfirst
        (Q'.le_trans' _ _ _ hsecond
          (Q'.le_of_eqv (Q'.one_mul_eqv 1)))
    exact Q'.zero_le_add _ _
      (q_mul_self_nonneg (x0 + x1 * coeffW w 1))
      (Q'.mul_nonneg _ _ (Q'.sub_nonneg_of_le hsqCoeff)
        (q_mul_self_nonneg x1))
  exact Q'.le_trans' _ _ _ hsos
    (Q'.le_of_eqv (Q'.eqv_symm
      (cutoffOneResummedChannelQuadratic_eqv_sos w x0 x1)))

/-- Exact anchor coefficient used by the cutoff-one interface kernel. -/
theorem anchorFundamentalCoefficient_resummed :
    coeffW anchorCoupling 1 ≈ anchorFaceCoefficient :=
  anchorFundamentalCoefficient

/-- The resummed fixed-face channel matrix is positive semidefinite at the
derived strong-coupling anchor, with no measured input. -/
theorem cutoffOneResummedChannelQuadratic_anchor_nonnegative
    (x0 x1 : Q') :
    (0 : Q') ≤
      cutoffOneResummedChannelQuadratic anchorCoupling x0 x1 := by
  apply cutoffOneResummedChannelQuadratic_nonnegative
  · exact Q'.le_trans' _ _ _ (by decide)
      (Q'.ge_of_eqv anchorFundamentalCoefficient_resummed)
  · exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv anchorFundamentalCoefficient_resummed) (by decide)

#print axioms fusionPathMultiplicity_fixedFace_channel_factorization
#print axioms fixedFaceRationalChannelFactorization
#print axioms adjacentEvenResummedFixedFaceLinkKernel_eqv_channelBilinear
#print axioms fusionInd_le_outputEnvelope
#print axioms fusionOutputRowCount_le_dimension
#print axioms anchorWeightedExcitedFaceTail_le_half
#print axioms anchorExcitedFaceChannelRowSum_le_half
#print axioms finiteSymmetricEdgeSOS_eqv_row_add_cross
#print axioms finiteDominantResidual_eqv_diag_sub_row
#print axioms finiteDominantGramSOS_eqv_identityPlusQuadratic
#print axioms finiteDominantGramSOS_nonnegative
#print axioms finiteIdentityPlusQuadratic_nonnegative_of_dominance
#print axioms anchorExcitedFaceChannelKernel_nonnegative
#print axioms anchorExcitedFaceChannelKernel_symmetric
#print axioms anchorExcitedFaceChannelRowSum_le_one
#print axioms anchorResummedFaceChannelQuadratic_nonnegative
#print axioms adjacentEvenResummedFaceChannelKernel_anchor_eqv_identity_add_excited
#print axioms adjacentEvenAnchorResummedChannelQuadratic_eqv_dominantForm
#print axioms adjacentEvenAnchorResummedChannelQuadratic_nonnegative
#print axioms cutoffOne_resummedChannelKernel_00
#print axioms cutoffOne_resummedChannelKernel_01
#print axioms cutoffOne_resummedChannelKernel_10
#print axioms cutoffOne_resummedChannelKernel_11
#print axioms cutoffOneResummedChannelQuadratic_eqv_sos
#print axioms cutoffOneResummedChannelQuadratic_nonnegative
#print axioms anchorFundamentalCoefficient_resummed
#print axioms cutoffOneResummedChannelQuadratic_anchor_nonnegative

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedFaceResummedKernel
