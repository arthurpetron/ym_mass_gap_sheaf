/-
# Column normalization of the physical SU(2) Schur kernel

The inverse Schur coefficient is not naively symmetric.  Its correct
transpose law is weighted by the two exact channel Gram norms and by the
involutive parity arising from reversal of all three external legs.

We derive that law by evaluating one mixed Gram entry twice: once with the
original Schur row and once with the row of the reversed channel problem.
Squaring removes the parity and identifies the corresponding normalized
kernel entries.  The already proved row normalization in the reversed
problem then gives exact column normalization in the original problem.

Constructive contract: finite exact `Q'` algebra and explicit channel maps
only; no choice, `Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.SU2SchurReversalSymmetry

namespace YMGap.Continuum.SU2PhysicalSchurColumnNormalization

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantMixedRecouplingGNSCompleted
open YMGap.Continuum.SU2TransvectantAllLabelGramCompleted
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2DirectRightFixedOutputEnumeration
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2FixedLeftRightAssociatorSchur
open YMGap.Continuum.SU2OrderedRightGramOrthogonality
open YMGap.Continuum.SU2OrderedRightGramCasimirOrthogonality
open YMGap.Continuum.SU2OrderedRacahCasimirCapstone
open YMGap.Continuum.SU2OrderedRacahInteriorSchurBridge
open YMGap.Continuum.SU2OrderedLeftCasimirPairing
open YMGap.Continuum.SU2PhysicalSchurRecouplingKernel
open YMGap.Continuum.SU2SchurReversalSymmetry

local infix:50 " ≈ " => Q'.eqv

private theorem triMapInner_congr_right {a b c d : Nat}
    {L R R' : BForm → BForm → BForm → BForm}
    (h : TriMapEqv a b c d R R') :
    triMapInner a b c d L R ≈ triMapInner a b c d L R' := by
  exact Q'.eqv_trans _ (triMapInner a b c d R L) _
    (triMapInner_symm a b c d L R)
    (Q'.eqv_trans _ (triMapInner a b c d R' L) _
      (triMapInner_congr_left h)
      (triMapInner_symm a b c d R' L))

private theorem triMapInner_congr_both {a b c d : Nat}
    {L L' R R' : BForm → BForm → BForm → BForm}
    (hL : TriMapEqv a b c d L L')
    (hR : TriMapEqv a b c d R R') :
    triMapInner a b c d L R ≈ triMapInner a b c d L' R' := by
  exact Q'.eqv_trans _ _ _ (triMapInner_congr_left hL)
    (triMapInner_congr_right hR)

private theorem triMapInner_scale_two (a b c d : Nat) (p q : Q')
    (L R : BForm → BForm → BForm → BForm) :
    triMapInner a b c d
        (fun x y z => scaleForm p (L x y z))
        (fun x y z => scaleForm q (R x y z)) ≈
      (p * q) * triMapInner a b c d L R := by
  have hleft := triMapInner_scale_left a b c d p L
    (fun x y z => scaleForm q (R x y z))
  have hright : triMapInner a b c d L
      (fun x y z => scaleForm q (R x y z)) ≈
      q * triMapInner a b c d L R := by
    exact Q'.eqv_trans _
      (triMapInner a b c d (fun x y z => scaleForm q (R x y z)) L) _
      (triMapInner_symm a b c d _ _)
      (Q'.eqv_trans _ (q * triMapInner a b c d R L) _
        (triMapInner_scale_left a b c d q R L)
        (Q'.mul_eqv_congr_left q _ _ (triMapInner_symm a b c d R L)))
  exact Q'.eqv_trans _ _ _ hleft
    (Q'.eqv_trans _ (p * (q * triMapInner a b c d L R)) _
      (Q'.mul_eqv_congr_left p _ _ hright)
      (Q'.eqv_symm (Q'.mul_assoc_eqv p q _)))

/-- The two parity products accumulated by reversing a pair of channels. -/
def schurTransposePhase {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) : Q' :=
  reverseRightPhase qR * reverseLeftPhase qL

theorem schurTransposePhase_mul_self {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) :
    schurTransposePhase qL qR * schurTransposePhase qL qR ≈ 1 := by
  let A := reverseRightPhase qR
  let B := reverseLeftPhase qL
  have hA := reverseRightPhase_mul_self qR
  have hB := reverseLeftPhase_mul_self qL
  exact Q'.eqv_trans _ ((A * A) * (B * B)) _
    (by simp only [schurTransposePhase, A, B]; ring_qeqv)
    (Q'.eqv_trans _ (1 * (B * B)) _
      (Q'.mul_eqv_congr_right _ _ _ hA)
      (Q'.eqv_trans _ (1 * 1) _
        (Q'.mul_eqv_congr_left 1 _ _ hB)
        (Q'.one_mul_eqv 1)))

/-- Every proof-carrying right channel can be used directly in the exact
Schur pairing law, without retaining its enumeration index. -/
theorem fixedLeft_schur_pairing_arbitrary {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) :
    triMapInner a b c d (triLeft a b c d qL.intermediate)
        (triRight a b c d qR.intermediate) ≈
      fixedLeftRightDiagonalCoeff qL qR 0 *
        triRightChannelWeight a b c d qR.intermediate := by
  obtain ⟨target, htarget, htargetEq⟩ :=
    arbitrary_right_channel_is_enumerated qL qR
  have h := fixedLeft_schur_pairing_all qL target htarget
  simpa only [htargetEq] using h

/-- Reversing both channels multiplies their mixed invariant pairing by the
product of the four vertex parities and otherwise leaves it unchanged. -/
theorem reversed_mixed_pairing_eq_phase {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) :
    triMapInner c b a d
        (triLeft c b a d (reverseRightAsLeft qR).intermediate)
        (triRight c b a d (reverseLeftAsRight qL).intermediate) ≈
      schurTransposePhase qL qR *
        triMapInner a b c d
          (triLeft a b c d qL.intermediate)
          (triRight a b c d qR.intermediate) := by
  let L := triLeft a b c d qL.intermediate
  let R := triRight a b c d qR.intermediate
  let p := reverseRightPhase qR
  let q := reverseLeftPhase qL
  have hL : TriMapEqv c b a d
      (triLeft c b a d (reverseRightAsLeft qR).intermediate)
      (fun z y x => scaleForm p (R x y z)) := by
    intro k hk j hj i hi s hs
    simpa only [p, R] using reverseRight_triLeft qR
      (mono i) (mono j) (mono k) s
  have hR : TriMapEqv c b a d
      (triRight c b a d (reverseLeftAsRight qL).intermediate)
      (fun z y x => scaleForm q (L x y z)) := by
    intro k hk j hj i hi s hs
    simpa only [q, L] using reverseLeft_triRight qL
      (mono i) (mono j) (mono k) s
  have hcongr := triMapInner_congr_both hL hR
  have hscale := triMapInner_scale_two c b a d p q
    (fun z y x => R x y z) (fun z y x => L x y z)
  have hreverse := triMapInner_reverse a b c d R L
  refine Q'.eqv_trans _ _ _ hcongr ?_
  refine Q'.eqv_trans _ _ _ hscale ?_
  refine Q'.eqv_trans _ ((p * q) * triMapInner a b c d R L) _
    (Q'.mul_eqv_congr_left _ _ _ hreverse) ?_
  refine Q'.eqv_trans _ ((p * q) * triMapInner a b c d L R) _
    (Q'.mul_eqv_congr_left _ _ _ (triMapInner_symm a b c d R L)) ?_
  exact Q'.eqv_refl _

/-- **Exact Gram-weighted transpose law for inverse Schur coefficients.**
The raw inverse coefficient is not symmetric; the two Gram weights and the
explicit involutive reversal phase are load-bearing. -/
theorem schurCoefficient_gram_transpose {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) :
    fixedLeftRightDiagonalCoeff qL qR 0 *
        triRightChannelWeight a b c d qR.intermediate ≈
      (schurTransposePhase qL qR *
        fixedLeftRightDiagonalCoeff (reverseRightAsLeft qR)
          (reverseLeftAsRight qL) 0) *
        triLeftChannelWeight a b c d qL.intermediate := by
  let K := fixedLeftRightDiagonalCoeff qL qR 0
  let Kr := fixedLeftRightDiagonalCoeff (reverseRightAsLeft qR)
    (reverseLeftAsRight qL) 0
  let WL := triLeftChannelWeight a b c d qL.intermediate
  let WR := triRightChannelWeight a b c d qR.intermediate
  let phase := schurTransposePhase qL qR
  let mixed := triMapInner a b c d
    (triLeft a b c d qL.intermediate)
    (triRight a b c d qR.intermediate)
  let reversedMixed := triMapInner c b a d
    (triLeft c b a d (reverseRightAsLeft qR).intermediate)
    (triRight c b a d (reverseLeftAsRight qL).intermediate)
  have horiginal : mixed ≈ K * WR := by
    simpa only [mixed, K, WR] using fixedLeft_schur_pairing_arbitrary qL qR
  have hreversed : reversedMixed ≈ Kr * WL := by
    have h := fixedLeft_schur_pairing_arbitrary
      (reverseRightAsLeft qR) (reverseLeftAsRight qL)
    exact Q'.eqv_trans _ _ _ h
      (Q'.mul_eqv_congr_left Kr _ _
        (reverseLeft_rightWeight_eq_leftWeight qL))
  have hgeometry : reversedMixed ≈ phase * mixed := by
    simpa only [reversedMixed, phase, mixed] using
      reversed_mixed_pairing_eq_phase qL qR
  have hscaled : phase * (K * WR) ≈ Kr * WL := by
    exact Q'.eqv_trans _ (phase * mixed) _
      (Q'.mul_eqv_congr_left phase _ _ (Q'.eqv_symm horiginal))
      (Q'.eqv_trans _ reversedMixed _
        (Q'.eqv_symm hgeometry) hreversed)
  have hmul := Q'.mul_eqv_congr_left phase _ _ hscaled
  have hcollapse : phase * (phase * (K * WR)) ≈ K * WR := by
    exact Q'.eqv_trans _ ((phase * phase) * (K * WR)) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv phase phase (K * WR)))
      (Q'.eqv_trans _ (1 * (K * WR)) _
        (Q'.mul_eqv_congr_right _ _ _
          (schurTransposePhase_mul_self qL qR))
        (Q'.one_mul_eqv _))
  exact Q'.eqv_trans _ (phase * (phase * (K * WR))) _
    (Q'.eqv_symm hcollapse)
    (Q'.eqv_trans _ (phase * (Kr * WL)) _ hmul
      (Q'.eqv_symm (Q'.mul_assoc_eqv phase Kr WL)))

private theorem divPos_eqv_divPos_of_cross {p q p' q' : Q'}
    (hq : (0 : Q') < q) (hq' : (0 : Q') < q')
    (hcross : p * q' ≈ p' * q) :
    Q'.divPos p q hq ≈ Q'.divPos p' q' hq' := by
  let z := Q'.divPos p' q' hq'
  have hright : (z * q) * q' ≈ p' * q := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv z q q') ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left z _ _ (Q'.mul_comm_eqv q q')) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv z q' q)) ?_
    exact Q'.mul_eqv_congr_right _ _ q (Q'.divPos_mul_eqv p' q' hq')
  have hmul : p * q' ≈ (z * q) * q' :=
    Q'.eqv_trans _ _ _ hcross (Q'.eqv_symm hright)
  have hcancel : p ≈ z * q := by
    apply Q'.mul_left_cancel_of_pos hq'
    exact Q'.eqv_trans _ (p * q') _
      (Q'.mul_comm_eqv q' p)
      (Q'.eqv_trans _ _ _ hmul (Q'.mul_comm_eqv (z * q) q'))
  apply Q'.mul_left_cancel_of_pos hq
  exact Q'.eqv_trans _ p _
    (Q'.eqv_trans _
      (Q'.divPos p q hq * q) _
      (Q'.mul_comm_eqv q (Q'.divPos p q hq))
      (Q'.divPos_mul_eqv p q hq))
    (Q'.eqv_trans _ (z * q) _ hcancel (Q'.mul_comm_eqv z q))

private theorem divPos_eqv_congr {p p' q q' : Q'}
    (hq : (0 : Q') < q) (hq' : (0 : Q') < q')
    (hp : p ≈ p') (hden : q ≈ q') :
    Q'.divPos p q hq ≈ Q'.divPos p' q' hq' := by
  apply divPos_eqv_divPos_of_cross hq hq'
  exact Q'.eqv_trans _ (p' * q') _
    (Q'.mul_eqv_congr_right _ _ _ hp)
    (Q'.mul_eqv_congr_left p' _ _ (Q'.eqv_symm hden))

/-- One original kernel entry is exactly the corresponding entry of the
reversed Schur row.  This is the pointwise detailed-balance form of the
Gram-transpose identity. -/
theorem physicalSchurRecouplingKernel_reversal {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) :
    physicalSchurRecouplingKernelAt qL qR ≈
      physicalSchurRecouplingKernelAt (reverseRightAsLeft qR)
        (reverseLeftAsRight qL) := by
  let K := fixedLeftRightDiagonalCoeff qL qR 0
  let Kr := fixedLeftRightDiagonalCoeff (reverseRightAsLeft qR)
    (reverseLeftAsRight qL) 0
  let WL := triLeftChannelWeight a b c d qL.intermediate
  let WR := triRightChannelWeight a b c d qR.intermediate
  let phase := schurTransposePhase qL qR
  have htranspose := schurCoefficient_gram_transpose qL qR
  have hsquare : ((K * K) * WR) * WR ≈ ((Kr * Kr) * WL) * WL := by
    have hsq : (K * WR) * (K * WR) ≈
        ((phase * Kr) * WL) * ((phase * Kr) * WL) :=
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ htranspose)
        (Q'.mul_eqv_congr_left _ _ _ htranspose)
    exact Q'.eqv_trans _ _ _ (by ring_qeqv)
      (Q'.eqv_trans _ _ _ hsq
        (Q'.eqv_trans _
          ((phase * phase) * ((Kr * Kr) * WL) * WL) _
          (by ring_qeqv)
          (Q'.eqv_trans _
            (1 * ((Kr * Kr) * WL) * WL) _
            (Q'.mul_eqv_congr_right _ _ WL
              (Q'.mul_eqv_congr_right _ _ ((Kr * Kr) * WL)
                (schurTransposePhase_mul_self qL qR)))
            (by ring_qeqv))))
  have hratio := divPos_eqv_divPos_of_cross
    (left_channel_weight_pos_all qL)
    (right_channel_weight_pos_all qR) hsquare
  have hrevNum : physicalSchurRawKernelAt (reverseRightAsLeft qR)
      (reverseLeftAsRight qL) ≈ (Kr * Kr) * WL := by
    unfold physicalSchurRawKernelAt
    exact Q'.mul_eqv_congr_left (Kr * Kr) _ _
      (reverseLeft_rightWeight_eq_leftWeight qL)
  have hrevDen := reverseRight_leftWeight_eq_rightWeight qR
  exact Q'.eqv_trans _
      (Q'.divPos ((K * K) * WR) WL (left_channel_weight_pos_all qL)) _
    (by rfl)
    (Q'.eqv_trans _
      (Q'.divPos ((Kr * Kr) * WL) WR (right_channel_weight_pos_all qR)) _
      hratio
      (Q'.eqv_symm (by
        unfold physicalSchurRecouplingKernelAt
        exact divPos_eqv_congr
          (left_channel_weight_pos_all (reverseRightAsLeft qR))
          (right_channel_weight_pos_all qR)
          hrevNum hrevDen)))

/-- The original column over a fixed right channel, enumerated without choice
as the reversed problem's canonical right-channel row. -/
def physicalSchurRecouplingColumnMass {a b c d : Nat}
    (qR : FixedRightCGChannel a b c d) : Q' :=
  finiteHeadSum (fixedRightChannels c b a d).length (fun n =>
    physicalSchurRecouplingKernelAt
      (reverseRightAsLeft
        (enumeratedRightChannel (reverseRightAsLeft qR) n)) qR)

/-- **The physical SU(2) Schur kernel is column-normalized at every label.**
The source enumeration is explicit, complete, and duplicate-free because it
is the involutive image of the reversed problem's canonical right list. -/
theorem physicalSchurRecouplingKernel_column_normalized {a b c d : Nat}
    (qR : FixedRightCGChannel a b c d) :
    physicalSchurRecouplingColumnMass qR ≈ 1 := by
  let qLr := reverseRightAsLeft qR
  have hterms : physicalSchurRecouplingColumnMass qR ≈
      physicalSchurRecouplingRowMass qLr := by
    unfold physicalSchurRecouplingColumnMass
      physicalSchurRecouplingRowMass
    apply finiteHeadSum_eqv_congr
    intro n hn
    let target := enumeratedRightChannel qLr n
    have h := physicalSchurRecouplingKernel_reversal
      (reverseRightAsLeft target) qR
    simpa only [qLr, target,
      reverseLeftAsRight_reverseRightAsLeft] using h
  exact Q'.eqv_trans _ _ _ hterms
    (physicalSchurRecouplingKernel_row_normalized qLr)

end YMGap.Continuum.SU2PhysicalSchurColumnNormalization

#print axioms YMGap.Continuum.SU2PhysicalSchurColumnNormalization.schurTransposePhase_mul_self
#print axioms YMGap.Continuum.SU2PhysicalSchurColumnNormalization.fixedLeft_schur_pairing_arbitrary
#print axioms YMGap.Continuum.SU2PhysicalSchurColumnNormalization.reversed_mixed_pairing_eq_phase
#print axioms YMGap.Continuum.SU2PhysicalSchurColumnNormalization.schurCoefficient_gram_transpose
#print axioms YMGap.Continuum.SU2PhysicalSchurColumnNormalization.physicalSchurRecouplingKernel_reversal
#print axioms YMGap.Continuum.SU2PhysicalSchurColumnNormalization.physicalSchurRecouplingKernel_column_normalized
