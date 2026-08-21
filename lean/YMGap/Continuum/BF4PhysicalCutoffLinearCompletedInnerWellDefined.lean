/-
# Representative independence of the completed physical BF4 pairing

The preceding module constructs a Bishop-real pairing limit for each pair of
explicit-modulus completion representatives.  Here we prove that this limit is
unchanged when either representative is replaced by an asymptotically close
one.  The proof compares same-index dense pairings by the bilinear telescope,
the two `Close` moduli, uniform diagonal bounds, and quantitative
Cauchy--Schwarz.

This closes the well-definedness prerequisite for quotient descent.  It does
not yet define the `RC`-valued completed form or prove its laws, and it makes no
thermodynamic, continuum, or mass-gap claim.

## Axiom gate

All recoverable thresholds remain Type-level data.  No classical choice,
noncomputable declaration, custom axiom, or unproved placeholder is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerOuter

namespace YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerWellDefined

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerKernel
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerOuter
open YMGap.Continuum.CRealSeminormCompletion

/-! ## 1. A general constructive limit-comparison lemma -/

/-- Two convergent `CReal` sequences whose same-index differences tend to
zero in two-sided `leRat` order have equivalent limits. -/
theorem CReal.Equiv_of_convergesTo_leRat_close
    {s t : Nat -> CReal} {A B : CReal}
    (hA : CReal.ConvergesTo s A) (hB : CReal.ConvergesTo t B)
    (hclose : forall epsilon : Q', (0 : Q') < epsilon ->
      exists N : Nat, forall n : Nat, N <= n ->
        CReal.leRat (CReal.add (s n) (CReal.neg (t n))) epsilon /\
        CReal.leRat (CReal.add (t n) (CReal.neg (s n))) epsilon) :
    CReal.Equiv A B := by
  intro epsilon hepsilon
  let q := HalfPow.half * (HalfPow.half * epsilon)
  have hqpos : (0 : Q') < q :=
    ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos epsilon hepsilon)
  obtain ⟨NA, hNA⟩ := hA q hqpos
  obtain ⟨NB, hNB⟩ := hB q hqpos
  obtain ⟨NC, hNC⟩ := hclose q hqpos
  let N := max (max NA NB) NC
  have hN_A : NA <= N :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hN_B : NB <= N :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have hN_C : NC <= N := Nat.le_max_right _ _
  obtain ⟨KA, hKA⟩ := hNA N hN_A
  obtain ⟨KB, hKB⟩ := hNB N hN_B
  obtain ⟨hst, hts⟩ := hNC N hN_C
  obtain ⟨Kst, hKst⟩ := hst q hqpos
  obtain ⟨Kts, hKts⟩ := hts q hqpos
  refine ⟨max (max KA KB) (max Kst Kts), fun k hk => ?_⟩
  have hkA : KA <= k :=
    Nat.le_trans
      (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hk
  have hkB : KB <= k :=
    Nat.le_trans
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hk
  have hkst : Kst <= k :=
    Nat.le_trans (Nat.le_max_left _ _)
      (Nat.le_trans (Nat.le_max_right _ _) hk)
  have hkts : Kts <= k :=
    Nat.le_trans (Nat.le_max_right _ _)
      (Nat.le_trans (Nat.le_max_right _ _) hk)
  obtain ⟨hsA, hAs⟩ := hKA k hkA
  obtain ⟨htB, hBt⟩ := hKB k hkB
  have hstRaw := hKst k hkst
  have htsRaw := hKts k hkts
  have hst' : (s N).approx k <= (t N).approx k + (q + q) :=
    CReal.leAddOfSubLe hstRaw
  have hts' : (t N).approx k <= (s N).approx k + (q + q) :=
    CReal.leAddOfSubLe htsRaw
  have hcollapse : forall value : Q',
      ((((value + q) + q) + q) + q) <= value + epsilon :=
    fun value => CReal.collapse4 value q epsilon
      (CReal.fourQ_le epsilon hepsilon)
  refine ⟨?_, ?_⟩
  · have h1 : A.approx k <= ((t N).approx k + (q + q)) + q :=
      Q'.le_trans' _ _ _ hAs (Q'.add_le_add_right _ _ q hst')
    have h2 : A.approx k <= (((B.approx k + q) + q) + q) + q := by
      refine Q'.le_trans' _ _ _ h1 ?_
      have hpush : (t N).approx k + (q + q) <=
          (B.approx k + q) + (q + q) :=
        Q'.add_le_add_right _ _ (q + q) htB
      refine Q'.le_trans' _ _ _
        (Q'.add_le_add_right _ _ q hpush) ?_
      exact Q'.le_of_eqv (Q'.add_eqv_congr_right _ _ q
        (Q'.eqv_symm (Q'.add_assoc_eqv (B.approx k + q) q q)))
    exact Q'.le_trans' _ _ _ h2 (hcollapse (B.approx k))
  · have h1 : B.approx k <= ((s N).approx k + (q + q)) + q :=
      Q'.le_trans' _ _ _ hBt (Q'.add_le_add_right _ _ q hts')
    have h2 : B.approx k <= (((A.approx k + q) + q) + q) + q := by
      refine Q'.le_trans' _ _ _ h1 ?_
      have hpush : (s N).approx k + (q + q) <=
          (A.approx k + q) + (q + q) :=
        Q'.add_le_add_right _ _ (q + q) hsA
      refine Q'.le_trans' _ _ _
        (Q'.add_le_add_right _ _ q hpush) ?_
      exact Q'.le_of_eqv (Q'.add_eqv_congr_right _ _ q
        (Q'.eqv_symm (Q'.add_assoc_eqv (A.approx k + q) q q)))
    exact Q'.le_trans' _ _ _ h2 (hcollapse (A.approx k))

/-! ## 2. Same-index comparison for close physical representatives -/

/-- Raw same-index rate for comparing pairings of close representatives. -/
def physicalCauchyPairCloseRate
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    {X X' Y Y' : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy}
    (hX : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Close X X')
    (hY : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Close Y Y')
    (epsilon : Q') : Nat :=
  let u := physicalCauchyPairTolerance hw0 hw1 half Y X' epsilon
  max (max (physicalCauchyNormBase hw0 hw1 half Y)
      (physicalCauchyNormBase hw0 hw1 half X'))
    (max (hX.modulus u) (hY.modulus u))

/-- One directed same-index comparison of pairings of close representatives. -/
theorem physicalCauchyPairingSeq_close_diff_leRat
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    {X X' Y Y' : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy}
    (hX : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Close X X')
    (hY : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Close Y Y')
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (n : Nat)
    (hn : physicalCauchyPairCloseRate hw0 hw1 half hX hY epsilon <= n) :
    CReal.leRat
      (CReal.add (physicalCauchyPairingSeq hw0 hw1 half X Y n)
        (CReal.neg
          (physicalCauchyPairingSeq hw0 hw1 half X' Y' n))) epsilon := by
  let u := physicalCauchyPairTolerance hw0 hw1 half Y X' epsilon
  let ceiling := physicalCauchyPairNormCeil hw0 hw1 half Y X'
  have hu : (0 : Q') < u :=
    physicalCauchyPairTolerance_pos hw0 hw1 half Y X' epsilon hepsilon
  have hehalf : (0 : Q') < HalfPow.half * epsilon :=
    ExpNeg.half_mul_pos epsilon hepsilon
  have hbase : max (physicalCauchyNormBase hw0 hw1 half Y)
      (physicalCauchyNormBase hw0 hw1 half X') <= n :=
    Nat.le_trans (Nat.le_max_left _ _) hn
  have hmods : max (hX.modulus u) (hY.modulus u) <= n :=
    Nat.le_trans (Nat.le_max_right _ _) hn
  have hYn : physicalCauchyNormBase hw0 hw1 half Y <= n :=
    Nat.le_trans (Nat.le_max_left _ _) hbase
  have hX'n : physicalCauchyNormBase hw0 hw1 half X' <= n :=
    Nat.le_trans (Nat.le_max_right _ _) hbase
  have hXmod : hX.modulus u <= n :=
    Nat.le_trans (Nat.le_max_left _ _) hmods
  have hYmod : hY.modulus u <= n :=
    Nat.le_trans (Nat.le_max_right _ _) hmods
  have hdistX := hX.close u hu n hXmod
  have hdistY := hY.close u hu n hYmod
  have hsubX : CReal.leEv
      (innerLimit hw0 hw1 half
        (sub (X.seq n) (X'.seq n)) (sub (X.seq n) (X'.seq n)))
      (CReal.ofQ' u) := hdistX
  have hsubY : CReal.leEv
      (innerLimit hw0 hw1 half
        (sub (Y.seq n) (Y'.seq n)) (sub (Y.seq n) (Y'.seq n)))
      (CReal.ofQ' u) := hdistY
  have hnormY : CReal.leEv
      (innerLimit hw0 hw1 half (Y.seq n) (Y.seq n))
      (CReal.ofQ' (Q'.ofNat ceiling)) := by
    apply CReal.leEv_trans
      (physicalCauchyStageDiagonal_leEv_normCeil
        hw0 hw1 half Y n hYn)
    exact CReal.leEv_of_le (CReal.ofQ'_le_ofQ'
      (Q'.ofNat_le_ofNat (Nat.le_max_left _ _)))
  have hnormX' : CReal.leEv
      (innerLimit hw0 hw1 half (X'.seq n) (X'.seq n))
      (CReal.ofQ' (Q'.ofNat ceiling)) := by
    apply CReal.leEv_trans
      (physicalCauchyStageDiagonal_leEv_normCeil
        hw0 hw1 half X' n hX'n)
    exact CReal.leEv_of_le (CReal.ofQ'_le_ofQ'
      (Q'.ofNat_le_ofNat (Nat.le_max_right _ _)))
  have hbudget := physicalCauchyPairTolerance_budget
    hw0 hw1 half Y X' epsilon hepsilon
  have htermX := innerLimit_twoSided_leRat hw0 hw1 half
    (sub (X.seq n) (X'.seq n)) (Y.seq n)
    u (Q'.ofNat ceiling) (HalfPow.half * epsilon)
    hu hehalf hsubX hnormY hbudget
  have htermY := innerLimit_twoSided_leRat hw0 hw1 half
    (sub (Y.seq n) (Y'.seq n)) (X'.seq n)
    u (Q'.ofNat ceiling) (HalfPow.half * epsilon)
    hu hehalf hsubY hnormX' hbudget
  have hsum := CReal.leRat_add htermX.1 htermY.1
  have hsplit := innerLimit_diff_split hw0 hw1 half
    (X.seq n) (X'.seq n) (Y.seq n) (Y'.seq n)
  apply CReal.leRat_of_equiv hsplit
  exact CReal.leRat_mono hsum
    (Q'.le_of_eqv (ExpNeg.two_halves epsilon))

/-! ## 3. Pairing-limit independence -/

/-- The representative pairing limit respects `Close` in both arguments. -/
theorem physicalCauchyPairingLimit_welldef
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    {X X' Y Y' : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy}
    (hX : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Close X X')
    (hY : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Close Y Y') :
    CReal.Equiv
      (physicalCauchyPairingLimit hw0 hw1 half X Y)
      (physicalCauchyPairingLimit hw0 hw1 half X' Y') := by
  apply CReal.Equiv_of_convergesTo_leRat_close
    (physicalCauchyPairingSeq_converges hw0 hw1 half X Y)
    (physicalCauchyPairingSeq_converges hw0 hw1 half X' Y')
  intro epsilon hepsilon
  let D := centralPhysicalCutoffLinearSquaredSeminorm hw0 hw1 half
  let hXsymm := D.closeSymm hX
  let hYsymm := D.closeSymm hY
  let Nforward := physicalCauchyPairCloseRate hw0 hw1 half hX hY epsilon
  let Nbackward := physicalCauchyPairCloseRate
    hw0 hw1 half hXsymm hYsymm epsilon
  refine ⟨max Nforward Nbackward, fun n hn => ?_⟩
  have hnForward : Nforward <= n :=
    Nat.le_trans (Nat.le_max_left _ _) hn
  have hnBackward : Nbackward <= n :=
    Nat.le_trans (Nat.le_max_right _ _) hn
  exact ⟨
    physicalCauchyPairingSeq_close_diff_leRat
      hw0 hw1 half hX hY epsilon hepsilon n hnForward,
    physicalCauchyPairingSeq_close_diff_leRat
      hw0 hw1 half hXsymm hYsymm epsilon hepsilon n hnBackward⟩

/-! ## Axiom audit -/

#print axioms CReal.Equiv_of_convergesTo_leRat_close
#print axioms physicalCauchyPairingSeq_close_diff_leRat
#print axioms physicalCauchyPairingLimit_welldef

end YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerWellDefined
