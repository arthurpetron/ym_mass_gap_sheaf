/-
Track 11.7-fusion / R2i -- reflective certificates for the retuned p=2 tail.

# Result

`P2RetunedRatioCompiler` reduces a complete cutoff certificate to adjacent
ratios on `1 <= s < 2*N`.  This module supplies a verified Boolean evaluator
for exactly that residual.  The evaluator is untrusted computation; its
soundness theorem turns any kernel-checked `true` result into the mathematical
`P2RetunedTailRatio`, and hence into `CanonicalBulkControl N w 2`.

The first checked fence family uses the physical near-continuum weight
`w = 11/12` and its canonical two-fold retune `q = 23/24`.  Unlike the earlier
cell-specific `23/25` choice, this is the actual `renormWFix 2 w` and is the
right base for extension across cutoffs.

# Constructivity

Pure `Nat`/`Q'` kernel reflection through `List.all` and `decide`.  No
`Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2RetunedRatioCompiler

namespace YMGap.Continuum.P2RetunedRatioCertificate

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BulkModeCrux
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.SpectralLocalizationCrux
open YMGap.Continuum.FusionKernelStatement
open YMGap.Continuum.RebasedBulkShift
open YMGap.Continuum.RebasedBulkLocalizationBridge
open YMGap.Continuum.P2RetunedRatioCompiler

set_option maxHeartbeats 4000000
set_option maxRecDepth 30000

local infix:50 " ≈ " => Q'.eqv

/-- Exact finite evaluator for every genuinely open adjacent ratio.  Index
`i` represents mode `s=i+1`, so the range has exactly `2*N-1` atoms. -/
def p2TailRatioCheck (N : Nat) (w : Q')
    (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q')) : Bool :=
  (List.range (2 * N - 1)).all fun i =>
    let s := i + 1
    decide (p2VacNorm N hw0 hw1 (s + 1) <=
      qpow (p2RetunedWeight w) (2 * s + 3) * p2VacNorm N hw0 hw1 s)

/-- Soundness of the reflective tail scan.  The proof about the computation
is cutoff-independent; individual certificate files need only establish that
the Boolean evaluator reduces to `true`. -/
def p2TailRatio_of_check {N : Nat} {w : Q'}
    (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q'))
    (hcheck : p2TailRatioCheck N w hw0 hw1 = true) :
    P2RetunedTailRatio N w hw0 hw1 where
  tail := fun s hs1 hs2 => by
    have hi : s - 1 < 2 * N - 1 := by omega
    have hmem : s - 1 ∈ List.range (2 * N - 1) := List.mem_range.mpr hi
    have hrow := List.all_eq_true.mp hcheck (s - 1) hmem
    have hsEq : s - 1 + 1 = s := by omega
    simpa only [hsEq] using of_decide_eq_true hrow

/-- A successful reflected scan compiles directly into the reviewed physical
carrier; no mode-by-mode theorem script remains. -/
def canonicalBulkControl_p2_of_check {N : Nat} {w : Q'}
    (hN : 1 <= N) (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q'))
    (hnc : (1 : Q') - w <= SpectralLocalizationCrux.q112)
    (hcheck : p2TailRatioCheck N w hw0 hw1 = true) :
    CanonicalBulkControl N w 2 :=
  canonicalBulkControl_p2_of_tail hN hw0 hw1 hnc
    (p2TailRatio_of_check hw0 hw1 hcheck)

/-! ## Division-free reflective checker -/

/-- Exact evaluator for the cross-multiplied coefficient residual.  It checks
the same adjacent comparison as `p2TailRatioCheck`, but never constructs a
vacuum-normalized quotient. -/
def p2CoeffTailRatioCheck (N : Nat) (w : Q') : Bool :=
  (List.range (2 * N - 1)).all fun i =>
    let s := i + 1
    decide (dimQ s * bondMovedCoeff N w 2 (s + 1) <=
      qpow (p2RetunedWeight w) (2 * s + 3) *
        (dimQ (s + 1) * bondMovedCoeff N w 2 s))

/-- Soundness is a theorem about the computation: a successful Boolean scan
supplies the division-free mathematical residual at any cutoff. -/
def p2CoeffTailRatio_of_check {N : Nat} {w : Q'}
    (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q'))
    (hcheck : p2CoeffTailRatioCheck N w = true) :
    P2RetunedCoeffTailRatio N w hw0 hw1 where
  tail := fun s hs1 hs2 => by
    have hi : s - 1 < 2 * N - 1 := by omega
    have hmem : s - 1 ∈ List.range (2 * N - 1) := List.mem_range.mpr hi
    have hrow := List.all_eq_true.mp hcheck (s - 1) hmem
    have hsEq : s - 1 + 1 = s := by omega
    simpa only [hsEq] using of_decide_eq_true hrow

/-- Direct physical compiler using only raw coefficient arithmetic in the
closed certificate. -/
def canonicalBulkControl_p2_of_coeffCheck {N : Nat} {w : Q'}
    (hN : 1 <= N) (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q'))
    (hnc : (1 : Q') - w <= SpectralLocalizationCrux.q112)
    (hcheck : p2CoeffTailRatioCheck N w = true) :
    CanonicalBulkControl N w 2 :=
  canonicalBulkControl_p2_of_coeffTail hN hw0 hw1 hnc
    (p2CoeffTailRatio_of_check hw0 hw1 hcheck)

/-! ## Bounded certificate composition -/

/-- Check `length` consecutive tail atoms beginning at the actual mode
`start`.  Certificate generators can split a large cutoff into blocks without
changing the proposition that the kernel checks. -/
def p2TailRatioBlockCheck (N : Nat) (w : Q')
    (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q'))
    (start length : Nat) : Bool :=
  (List.range length).all fun i =>
    let s := start + i
    decide (p2VacNorm N hw0 hw1 (s + 1) <=
      qpow (p2RetunedWeight w) (2 * s + 3) * p2VacNorm N hw0 hw1 s)

/-- Soundness of one bounded block. -/
theorem p2TailRatioBlockCheck_sound {N : Nat} {w : Q'}
    (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q'))
    {start length : Nat}
    (hcheck : p2TailRatioBlockCheck N w hw0 hw1 start length = true)
    (s : Nat) (hlo : start <= s) (hhi : s < start + length) :
    p2VacNorm N hw0 hw1 (s + 1) <=
      qpow (p2RetunedWeight w) (2 * s + 3) * p2VacNorm N hw0 hw1 s := by
  have hi : s - start < length := by omega
  have hmem : s - start ∈ List.range length := List.mem_range.mpr hi
  have hrow := List.all_eq_true.mp hcheck (s - start) hmem
  have hsEq : start + (s - start) = s := by omega
  simpa only [hsEq] using of_decide_eq_true hrow

/-- Two independently checked blocks covering the exact interval
`[1,2*N)` assemble the mathematical tail-ratio datum.  This is a theorem
about the checker, so later certificates contain only small closed Boolean
proofs. -/
def p2TailRatio_of_split {N : Nat} {w : Q'}
    (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q')) (cut : Nat)
    (hleft : p2TailRatioBlockCheck N w hw0 hw1 1 cut = true)
    (hright : p2TailRatioBlockCheck N w hw0 hw1 (1 + cut)
      (2 * N - 1 - cut) = true) :
    P2RetunedTailRatio N w hw0 hw1 where
  tail := fun s hs1 hsN => by
    by_cases hsCut : s < 1 + cut
    · exact p2TailRatioBlockCheck_sound hw0 hw1 hleft s hs1 hsCut
    · exact p2TailRatioBlockCheck_sound hw0 hw1 hright s
        (by omega) (by omega)

/-- Bounded raw-coefficient scan.  Splitting the certificate controls kernel
reduction size without adding any mathematical assumption. -/
def p2CoeffTailRatioBlockCheck (N : Nat) (w : Q')
    (start length : Nat) : Bool :=
  (List.range length).all fun i =>
    let s := start + i
    decide (dimQ s * bondMovedCoeff N w 2 (s + 1) <=
      qpow (p2RetunedWeight w) (2 * s + 3) *
        (dimQ (s + 1) * bondMovedCoeff N w 2 s))

/-- Soundness of one bounded division-free block. -/
theorem p2CoeffTailRatioBlockCheck_sound {N : Nat} {w : Q'}
    {start length : Nat}
    (hcheck : p2CoeffTailRatioBlockCheck N w start length = true)
    (s : Nat) (hlo : start <= s) (hhi : s < start + length) :
    dimQ s * bondMovedCoeff N w 2 (s + 1) <=
      qpow (p2RetunedWeight w) (2 * s + 3) *
        (dimQ (s + 1) * bondMovedCoeff N w 2 s) := by
  have hi : s - start < length := by omega
  have hmem : s - start ∈ List.range length := List.mem_range.mpr hi
  have hrow := List.all_eq_true.mp hcheck (s - start) hmem
  have hsEq : start + (s - start) = s := by omega
  simpa only [hsEq] using of_decide_eq_true hrow

/-- Two raw blocks covering `[1,2*N)` assemble the division-free residual. -/
def p2CoeffTailRatio_of_split {N : Nat} {w : Q'}
    (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q')) (cut : Nat)
    (hleft : p2CoeffTailRatioBlockCheck N w 1 cut = true)
    (hright : p2CoeffTailRatioBlockCheck N w (1 + cut)
      (2 * N - 1 - cut) = true) :
    P2RetunedCoeffTailRatio N w hw0 hw1 where
  tail := fun s hs1 hsN => by
    by_cases hsCut : s < 1 + cut
    · exact p2CoeffTailRatioBlockCheck_sound hleft s hs1 hsCut
    · exact p2CoeffTailRatioBlockCheck_sound hright s
        (by omega) (by omega)

/-! ## Exact `w=11/12` cutoff cells -/

/-- First reflected adjacent-ratio cutoff. -/
theorem fenceTailRatioCheckN2 :
    p2TailRatioCheck 2 fenceW fenceW_nonneg fenceW_le_one = true := by decide

/-- The next four cutoffs are independent kernel certificates for the same
canonical retune.  Keeping them as separate declarations bounds reduction work
and makes each certificate individually auditable. -/
theorem fenceTailRatioCheckN3 :
    p2TailRatioCheck 3 fenceW fenceW_nonneg fenceW_le_one = true := by decide

theorem fenceTailRatioCheckN4 :
    p2TailRatioCheck 4 fenceW fenceW_nonneg fenceW_le_one = true := by decide

theorem fenceTailRatioCheckN5 :
    p2TailRatioCheck 5 fenceW fenceW_nonneg fenceW_le_one = true := by decide

theorem fenceTailRatioCheckN6 :
    p2TailRatioCheck 6 fenceW fenceW_nonneg fenceW_le_one = true := by decide

/-- A larger cutoff certified as two bounded reduction blocks. -/
theorem fenceTailRatioBlockN12Left :
    p2TailRatioBlockCheck 12 fenceW fenceW_nonneg fenceW_le_one 1 12 = true :=
  by decide

theorem fenceTailRatioBlockN12Right :
    p2TailRatioBlockCheck 12 fenceW fenceW_nonneg fenceW_le_one 13 11 = true :=
  by decide

def fenceTailRatioN12 :
    P2RetunedTailRatio 12 fenceW fenceW_nonneg fenceW_le_one :=
  p2TailRatio_of_split fenceW_nonneg fenceW_le_one 12
    fenceTailRatioBlockN12Left fenceTailRatioBlockN12Right

/-! The same cutoff is re-certified below with the division-free evaluator.
The side-by-side declarations make the computational improvement auditable. -/

theorem fenceCoeffTailRatioBlockN12Left :
    p2CoeffTailRatioBlockCheck 12 fenceW 1 12 = true := by decide

theorem fenceCoeffTailRatioBlockN12Right :
    p2CoeffTailRatioBlockCheck 12 fenceW 13 11 = true := by decide

def fenceCoeffTailRatioN12 :
    P2RetunedCoeffTailRatio 12 fenceW fenceW_nonneg fenceW_le_one :=
  p2CoeffTailRatio_of_split fenceW_nonneg fenceW_le_one 12
    fenceCoeffTailRatioBlockN12Left fenceCoeffTailRatioBlockN12Right

/-- The reflected cutoff-two physical carrier with canonical effective weight
`23/24`. -/
def fenceRetunedControlN2 : CanonicalBulkControl 2 fenceW 2 :=
  canonicalBulkControl_p2_of_check (by decide) fenceW_nonneg fenceW_le_one
    fenceW_near_continuum fenceTailRatioCheckN2

/-- The same compiler yields a physically uniform family through cutoff six;
only the reflected Boolean evidence changes with the cutoff. -/
def fenceRetunedControlN3 : CanonicalBulkControl 3 fenceW 2 :=
  canonicalBulkControl_p2_of_check (by decide) fenceW_nonneg fenceW_le_one
    fenceW_near_continuum fenceTailRatioCheckN3

def fenceRetunedControlN4 : CanonicalBulkControl 4 fenceW 2 :=
  canonicalBulkControl_p2_of_check (by decide) fenceW_nonneg fenceW_le_one
    fenceW_near_continuum fenceTailRatioCheckN4

def fenceRetunedControlN5 : CanonicalBulkControl 5 fenceW 2 :=
  canonicalBulkControl_p2_of_check (by decide) fenceW_nonneg fenceW_le_one
    fenceW_near_continuum fenceTailRatioCheckN5

def fenceRetunedControlN6 : CanonicalBulkControl 6 fenceW 2 :=
  canonicalBulkControl_p2_of_check (by decide) fenceW_nonneg fenceW_le_one
    fenceW_near_continuum fenceTailRatioCheckN6

def fenceRetunedControlN12 : CanonicalBulkControl 12 fenceW 2 :=
  canonicalBulkControl_p2_of_coeffTail (by decide) fenceW_nonneg fenceW_le_one
    fenceW_near_continuum fenceCoeffTailRatioN12

/-- The canonical retune is the exact rational `23/24`. -/
theorem fenceRetunedWeight_eqv_23_24 :
    p2RetunedWeight fenceW ≈ Q'.mkPos 23 24 (by decide) := by decide

/-- Mode three witnesses a nonempty effective bulk for the canonical retune. -/
theorem fenceRetunedModeThree_isBulk :
    q12 <= Q'.ofNat (c4 3) * ((1 : Q') - p2RetunedWeight fenceW) := by decide

/-- Concrete nonvacuous localization output at the first reflected cutoff. -/
theorem fenceRetunedN2FusionEig_three_below_gapEdge :
    fusionEig 2 fenceW 2 3 (fenceRetunedControlN2.denomPos 3) <=
      eigA fenceW 1 :=
  fenceRetunedControlN2.bulk_below_gapEdge 3 fenceRetunedModeThree_isBulk

end YMGap.Continuum.P2RetunedRatioCertificate

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2RetunedRatioCertificate.p2TailRatio_of_check
#print axioms YMGap.Continuum.P2RetunedRatioCertificate.canonicalBulkControl_p2_of_check
#print axioms YMGap.Continuum.P2RetunedRatioCertificate.p2CoeffTailRatio_of_check
#print axioms YMGap.Continuum.P2RetunedRatioCertificate.canonicalBulkControl_p2_of_coeffCheck
#print axioms YMGap.Continuum.P2RetunedRatioCertificate.p2TailRatioBlockCheck_sound
#print axioms YMGap.Continuum.P2RetunedRatioCertificate.p2TailRatio_of_split
#print axioms YMGap.Continuum.P2RetunedRatioCertificate.p2CoeffTailRatioBlockCheck_sound
#print axioms YMGap.Continuum.P2RetunedRatioCertificate.p2CoeffTailRatio_of_split
#print axioms YMGap.Continuum.P2RetunedRatioCertificate.fenceTailRatioCheckN2
#print axioms YMGap.Continuum.P2RetunedRatioCertificate.fenceTailRatioCheckN3
#print axioms YMGap.Continuum.P2RetunedRatioCertificate.fenceTailRatioCheckN4
#print axioms YMGap.Continuum.P2RetunedRatioCertificate.fenceTailRatioCheckN5
#print axioms YMGap.Continuum.P2RetunedRatioCertificate.fenceTailRatioCheckN6
#print axioms YMGap.Continuum.P2RetunedRatioCertificate.fenceTailRatioBlockN12Left
#print axioms YMGap.Continuum.P2RetunedRatioCertificate.fenceTailRatioBlockN12Right
#print axioms YMGap.Continuum.P2RetunedRatioCertificate.fenceRetunedControlN12
#print axioms YMGap.Continuum.P2RetunedRatioCertificate.fenceCoeffTailRatioBlockN12Left
#print axioms YMGap.Continuum.P2RetunedRatioCertificate.fenceCoeffTailRatioBlockN12Right
#print axioms YMGap.Continuum.P2RetunedRatioCertificate.fenceRetunedWeight_eqv_23_24
#print axioms YMGap.Continuum.P2RetunedRatioCertificate.fenceRetunedModeThree_isBulk
#print axioms YMGap.Continuum.P2RetunedRatioCertificate.fenceRetunedN2FusionEig_three_below_gapEdge
