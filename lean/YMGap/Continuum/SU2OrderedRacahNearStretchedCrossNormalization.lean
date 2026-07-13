/-
# Cross/Gram normalization for the first near-stretched Racah family

For `n=u+4`, the physical channel

  `(a,b,c;d;e,f) = (n,2,n;2u+6;n,n)`

has inner and outer contraction orders equal to one in both bracketings.
This module records the exact reversal symmetry of those two trivalent maps
and specializes the Casimir capstone to the one remaining scalar square.

The intended unsquared inverse-Schur coefficient is `-u/(u+6)`.  The final
section below isolates this value as a division-free cross-scale identity;
no positivity or abstract cross-normalization premise is hidden in it.
-/

import YMGap.Continuum.SU2OrderedRacahNearStretchedTwoTerm
import YMGap.Continuum.SU2OrderedRacahCasimirCapstone
import YMGap.Continuum.SU2TransvectantSwapParity
import YMGap.Continuum.SU2GeneralHahnAdjacentDifference
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.SU2OrderedRacahNearStretchedCrossNormalization

set_option maxHeartbeats 3000000
set_option maxRecDepth 24000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantLinearity
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantMixedRecouplingGNSCompleted
open YMGap.Continuum.SU2TransvectantSwapParity
open YMGap.Continuum.SU2TransvectantFactorialSeed
open YMGap.Continuum.SU2TransvectantAllOrder
open YMGap.Continuum.SU2GeneralShellHahnMatrix
open YMGap.Continuum.SU2GeneralHahnAdjacentDifference
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2OrderedRacahCollapsedHahnCarrier
open YMGap.Continuum.SU2OrderedRacahGuardedHahnCarrier
open YMGap.Continuum.SU2OrderedRacahNearStretchedTwoTerm
open YMGap.Continuum.SU2OrderedRacahCasimirCapstone
open YMGap.Continuum.SU2OrderedRacahInteriorSchurBridge
open YMGap.Continuum.SU2OrderedRightGramOrthogonality
open YMGap.Continuum.SU2OrderedRightGramCasimirOrthogonality
open YMGap.Continuum.SU2FixedLeftRightAssociatorSchur
open YMGap.Continuum.SU2FixedLeftRightOrderedAssociatorBridge
open YMGap.Continuum.SU2TransvectantAllLabelGramCompleted
open YMGap.Continuum.SixJKernel

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul,
               Int.mul_add, Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg,
               Int.one_mul, Int.mul_one, Int.zero_mul, Int.mul_zero,
               Int.add_zero, Int.zero_add] <;> ac_rfl))

/-! ## Reversal symmetry and equality of the two physical Gram weights -/

private theorem tprod_transpose (x y : BForm) :
    BForm2Eqv (transpose2 (tprod x y)) (tprod y x) := by
  intro i j
  unfold transpose2 tprod
  exact Q'.mul_comm_eqv _ _

private theorem tprod_congr_left (x : BForm) {y z : BForm}
    (h : BFormEqv y z) : BForm2Eqv (tprod x y) (tprod x z) := by
  intro i j
  exact Q'.mul_eqv_congr_left (x i) _ _ (h j)

private theorem tprod_scale_right (q : Q') (x y : BForm) :
    BForm2Eqv (tprod x (fun s => q * y s))
      (bscale q (tprod x y)) := by
  intro i j
  unfold tprod bscale
  refine Q'.eqv_trans _ ((x i * q) * y j) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
  refine Q'.eqv_trans _ ((q * x i) * y j) _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) ?_
  exact Q'.mul_assoc_eqv _ _ _

private theorem neg_neg_mul (x : Q') : (-1 : Q') * ((-1 : Q') * x) ≈ x := by
  ring_qeqv

/-- Reversing the first and third inputs exchanges the two order-one trees.
The inner and outer transvectant swaps each contribute `-1`, so the total
phase is positive. -/
theorem near_triLeft_reverse (u : Nat) (x y z : BForm) :
    BFormEqv
      (triLeft (nearN u) 2 (nearN u) (nearD u) (nearN u) x y z)
      (triRight (nearN u) 2 (nearN u) (nearD u) (nearN u) z y x) := by
  have hinnerOrder : couplingOrder (nearN u) 2 (nearN u) = 1 := by
    unfold couplingOrder nearN
    omega
  have hrightInnerOrder : couplingOrder 2 (nearN u) (nearN u) = 1 := by
    unfold couplingOrder nearN
    omega
  have houterOrder : couplingOrder (nearN u) (nearN u) (nearD u) = 1 := by
    unfold couplingOrder nearN nearD
    omega
  let A := transvect (nearN u) 2 1 (tprod x y)
  let B := transvect 2 (nearN u) 1 (tprod y x)
  have hinner : BFormEqv B (fun s => (-1 : Q') * A s) := by
    have hswap := transvect_transpose (nearN u) 2 1 (tprod x y)
    have hcongr := transvect_congr 2 (nearN u) 1 (tprod_transpose x y)
    intro s
    exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (hcongr s))
      (by simpa only [A, B, swapPhase] using hswap s)
  have htensor : BForm2Eqv (tprod z B)
      (bscale (-1) (tprod z A)) :=
    bform2Eqv_trans (tprod_congr_left z hinner)
      (tprod_scale_right (-1) z A)
  have hrightScale : BFormEqv
      (transvect (nearN u) (nearN u) 1 (tprod z B))
      (fun s => (-1 : Q') *
        transvect (nearN u) (nearN u) 1 (tprod z A) s) := by
    intro s
    exact Q'.eqv_trans _ _ _
      (transvect_congr (nearN u) (nearN u) 1 htensor s)
      (transvect_scale (nearN u) (nearN u) 1 (-1) (tprod z A) s)
  have houterSwap : BFormEqv
      (transvect (nearN u) (nearN u) 1 (tprod z A))
      (fun s => (-1 : Q') *
        transvect (nearN u) (nearN u) 1 (tprod A z) s) := by
    have hswap := transvect_transpose (nearN u) (nearN u) 1 (tprod A z)
    have hcongr := transvect_congr (nearN u) (nearN u) 1
      (tprod_transpose A z)
    intro s
    exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (hcongr s))
      (by simpa only [swapPhase] using hswap s)
  intro s
  unfold triLeft triRight
  rw [hinnerOrder, hrightInnerOrder, houterOrder]
  refine Q'.eqv_symm (Q'.eqv_trans _ _ _ (hrightScale s) ?_)
  refine Q'.eqv_trans _
    ((-1 : Q') * ((-1 : Q') *
      transvect (nearN u) (nearN u) 1 (tprod A z) s)) _
    (Q'.mul_eqv_congr_left (-1) _ _ (houterSwap s)) ?_
  simpa only [A] using neg_neg_mul
    (transvect (nearN u) (nearN u) 1 (tprod A z) s)

/-- The source and target Gram weights are equal.  This is a genuine physical
symmetry statement: it uses reversal of the two order-one Cayley trees and
then only reindexes the two equal `nearN` monomial windows. -/
theorem near_channel_weights_eq (u : Nat) :
    triLeftChannelWeight (nearN u) 2 (nearN u) (nearD u) (nearN u) ≈
      triRightChannelWeight (nearN u) 2 (nearN u) (nearD u) (nearN u) := by
  let L := triLeft (nearN u) 2 (nearN u) (nearD u) (nearN u)
  let R := triRight (nearN u) 2 (nearN u) (nearD u) (nearN u)
  let A : Nat → Nat → Nat → Nat → Q' := fun i j l s =>
    tvBinomQ (nearN u) i * tvBinomQ 2 j * tvBinomQ (nearN u) l *
      symMonomialNormSq (nearD u) s *
        (R (mono i) (mono j) (mono l) s *
          R (mono i) (mono j) (mono l) s)
  have hterm : ∀ i j l s,
      tvBinomQ (nearN u) i * tvBinomQ 2 j * tvBinomQ (nearN u) l *
          symMonomialNormSq (nearD u) s *
            (L (mono i) (mono j) (mono l) s *
              L (mono i) (mono j) (mono l) s) ≈
        A l j i s := by
    intro i j l s
    have hrev := near_triLeft_reverse u (mono i) (mono j) (mono l) s
    unfold A R
    have hsq := Q'.eqv_trans _
      (triRight (nearN u) 2 (nearN u) (nearD u) (nearN u)
          (mono l) (mono j) (mono i) s *
        L (mono i) (mono j) (mono l) s) _
      (Q'.mul_eqv_congr_right _ _ _ hrev)
      (Q'.mul_eqv_congr_left _ _ _ hrev)
    refine Q'.eqv_trans _
      (tvBinomQ (nearN u) i * tvBinomQ 2 j * tvBinomQ (nearN u) l *
        symMonomialNormSq (nearD u) s *
          (triRight (nearN u) 2 (nearN u) (nearD u) (nearN u)
              (mono l) (mono j) (mono i) s *
            triRight (nearN u) 2 (nearN u) (nearD u) (nearN u)
              (mono l) (mono j) (mono i) s)) _
      (Q'.mul_eqv_congr_left _ _ _ hsq) ?_
    ring_qeqv
  unfold triLeftChannelWeight triRightChannelWeight triMapInner
  refine Q'.eqv_trans _
    (finSum (fun i => finSum (fun j => finSum (fun l => finSum (fun s =>
      A l j i s) (nearD u + 1)) (nearN u + 1)) 3) (nearN u + 1)) _ ?_ ?_
  · refine finSum_eqv_congr_lt _ _ (nearN u + 1) (fun i hi => ?_)
    refine finSum_eqv_congr_lt _ _ 3 (fun j hj => ?_)
    refine finSum_eqv_congr_lt _ _ (nearN u + 1) (fun l hl => ?_)
    refine finSum_eqv_congr_lt _ _ (nearD u + 1) (fun s hs => ?_)
    exact hterm i j l s
  · let S : Nat → Nat → Nat → Q' := fun i j l =>
      finSum (fun s => A i j l s) (nearD u + 1)
    have hswapIJ := finSum_swap
      (fun i j => finSum (fun l => S l j i) (nearN u + 1))
      (nearN u + 1) 3
    have hswapIL : finSum
        (fun j => finSum (fun i => finSum (fun l => S l j i)
          (nearN u + 1)) (nearN u + 1)) 3 ≈
        finSum (fun j => finSum (fun l => finSum (fun i => S l j i)
          (nearN u + 1)) (nearN u + 1)) 3 := by
      refine finSum_eqv_congr_lt _ _ 3 (fun j hj => ?_)
      exact finSum_swap (fun i l => S l j i) (nearN u + 1) (nearN u + 1)
    have hswapJL := finSum_swap
      (fun j l => finSum (fun i => S l j i) (nearN u + 1))
      3 (nearN u + 1)
    refine Q'.eqv_trans _
      (finSum (fun j => finSum (fun i => finSum (fun l => S l j i)
        (nearN u + 1)) (nearN u + 1)) 3) _ ?_ ?_
    · simpa only [S] using hswapIJ
    refine Q'.eqv_trans _
      (finSum (fun j => finSum (fun l => finSum (fun i => S l j i)
        (nearN u + 1)) (nearN u + 1)) 3) _ hswapIL ?_
    simpa only [S, A, L, R] using hswapJL

/-! ## Exact specialization of the Casimir capstone -/

/-- The predicted signed inverse-Schur entry, `-u/(u+6)`, in raw `Q'`
storage.  The stored denominator is one less than the semantic denominator. -/
def nearInverseCoeffClosed (u : Nat) : Q' :=
  ⟨-Int.ofNat u, u + 5⟩

theorem nearInverseCoeffClosed_square (u : Nat) :
    nearInverseCoeffClosed u * nearInverseCoeffClosed u ≈
      nearKernelClosed u := by
  unfold nearInverseCoeffClosed nearKernelClosed Q'.mkN
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.den,
    Int.neg_mul, Int.mul_neg, Int.neg_neg]
  have hden : u + 5 + 1 = u + 6 := by omega
  have hsq : (u + 6) * (u + 6) - 1 + 1 = (u + 6) * (u + 6) := by
    exact Nat.sub_add_cancel (by
      exact Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (by omega) (by omega)))
  rw [hden, hsq]
  push_cast
  simp only [Int.ofNat_eq_natCast, Int.natCast_mul]
  ac_rfl

theorem nearInverseCoeffClosed_scale (u : Nat) :
    (Q'.ofNat u + 6) * nearInverseCoeffClosed u ≈ -Q'.ofNat u := by
  unfold nearInverseCoeffClosed
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.add_num_cast,
    Q'.add_den_cast, neg_num_cast, Q'.neg_den]
  simp only [Q'.ofNat_num_cast, Q'.den, Int.neg_mul, Int.mul_neg]
  have hden : u + 5 + 1 = u + 6 := by omega
  rw [hden]
  push_cast
  simp only [Int.ofNat_eq_natCast]
  rw [show (6 : Q').num = (6 : Int) by rfl]
  ac_rfl

/-- For this symmetric family, Casimir orthogonality and reversal symmetry
remove every Gram factor.  The complete collapsed Racah square is equivalent
to one scalar comparison: the square of the actual inverse Schur coefficient
must be `u²/(u+6)²`. -/
theorem near_collapsedRacahSquare_iff_inverseCoeffSquare (u : Nat) :
    CollapsedRacahSquareAt (nearLeftChannel u) (nearRightChannel u) ↔
      nearKernelClosed u ≈
        fixedLeftRightDiagonalCoeff (nearLeftChannel u)
            (nearRightChannel u) 0 *
          fixedLeftRightDiagonalCoeff (nearLeftChannel u)
            (nearRightChannel u) 0 := by
  let W := triRightChannelWeight (nearN u) 2 (nearN u) (nearD u) (nearN u)
  let K := fixedLeftRightDiagonalCoeff (nearLeftChannel u)
    (nearRightChannel u) 0
  have hcap := collapsedRacahSquare_iff_explicit_inverse_kernel_identity
    (nearLeftChannel u) (nearRightChannel u)
  have hW := near_channel_weights_eq u
  have hP := near_racahKernel_closed u
  have hpos : (0 : Q') < W := by
    simpa only [W, (near_intermediates u).2] using
      right_channel_weight_pos_all (nearRightChannel u)
  have hleft :
      triLeftChannelWeight (nearN u) 2 (nearN u) (nearD u)
          (nearLeftChannel u).intermediate *
        racahKernel6 (nearN u) 2 (nearN u) (nearD u)
          (nearLeftChannel u).intermediate (nearRightChannel u).intermediate ≈
      W * nearKernelClosed u := by
    rw [(near_intermediates u).1, (near_intermediates u).2]
    exact Q'.eqv_trans _
      (W * racahKernel6 (nearN u) 2 (nearN u) (nearD u)
        (nearN u) (nearN u)) _
      (Q'.mul_eqv_congr_right _ _ _ hW)
      (Q'.mul_eqv_congr_left W _ _ hP)
  constructor
  · intro hsquare
    have hbridge := hcap.mp hsquare
    have hscaled : W * nearKernelClosed u ≈ W * (K * K) := by
      exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hleft)
        (by simpa only [W, K, (near_intermediates u).2] using hbridge)
    exact Q'.mul_left_cancel_of_pos hpos hscaled
  · intro hscalar
    apply hcap.mpr
    refine Q'.eqv_trans _ (W * nearKernelClosed u) _ hleft ?_
    exact Q'.eqv_trans _ (W * (K * K)) _
      (Q'.mul_eqv_congr_left W _ _ hscalar)
      (by
        rw [(near_intermediates u).2]
        exact Q'.eqv_refl _)

/-- An exact unsquared evaluation of the inverse Schur entry closes the
physical collapsed Racah square. -/
theorem near_collapsedRacahSquare_of_inverseCoeff
    (u : Nat)
    (hcoeff : fixedLeftRightDiagonalCoeff (nearLeftChannel u)
        (nearRightChannel u) 0 ≈ nearInverseCoeffClosed u) :
    CollapsedRacahSquareAt (nearLeftChannel u) (nearRightChannel u) := by
  apply (near_collapsedRacahSquare_iff_inverseCoeffSquare u).2
  let K := fixedLeftRightDiagonalCoeff (nearLeftChannel u)
    (nearRightChannel u) 0
  have hK : K ≈ nearInverseCoeffClosed u := by
    simpa only [K] using hcoeff
  have hleft : nearInverseCoeffClosed u * nearInverseCoeffClosed u ≈
      K * nearInverseCoeffClosed u :=
    Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hK)
  have hright : K * nearInverseCoeffClosed u ≈ K * K :=
    Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hK)
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (nearInverseCoeffClosed_square u))
    (Q'.eqv_trans _ _ _ hleft hright)

/-! ## The explicit order-one/order-two recoupling polynomial -/

/-- Symbolic left `(1,1)` payload.  The variables are respectively the
family parameter and the three source monomial indices. -/
def nearLeftPayloadQ (U I J L : Q') : Q' :=
  let N := U + 4
  hahnRowOneSymbolic N 2 I J *
    hahnRowOneSymbolic N N (qSub (I + J) 1) L

/-- Symbolic right `(0,2)` payload. -/
def nearRightPayload0Q (U I J L : Q') : Q' :=
  let N := U + 4
  hahnRowTwoSymbolic N (N + 2) I (J + L)

/-- Symbolic right `(1,1)` payload. -/
def nearRightPayload1Q (U I J L : Q') : Q' :=
  let N := U + 4
  hahnRowOneSymbolic 2 N J L *
    hahnRowOneSymbolic N N I (qSub (J + L) 1)

/-- Symbolic right `(2,0)` payload. -/
def nearRightPayload2Q (U _I J L : Q') : Q' :=
  let N := U + 4
  hahnRowTwoSymbolic 2 N J L

private def eU : PolyExpr := .var 0
private def eI : PolyExpr := .var 1
private def eJ : PolyExpr := .var 2
private def eL : PolyExpr := .var 3
private def eOne : PolyExpr := .const 1
private def eTwo : PolyExpr := .const 2
private def eFour : PolyExpr := .const 4
private def eFive : PolyExpr := .const 5
private def eSix : PolyExpr := .const 6
private def eSub (x y : PolyExpr) : PolyExpr := .add x (.neg y)
private def ePred (x : PolyExpr) : PolyExpr := .add x (.const (-1))

private def rowOneExpr (M N X Y : PolyExpr) : PolyExpr :=
  .add (.mul X (eSub N Y)) (.neg (.mul (eSub M X) Y))

private def rowTwoExpr (M N X Y : PolyExpr) : PolyExpr :=
  .add
    (.add
      (.mul (.mul X (ePred X))
        (.mul (eSub N Y) (ePred (eSub N Y))))
      (.neg (.mul (.mul (.mul eTwo X) (eSub M X))
        (.mul Y (eSub N Y)))))
    (.mul (.mul (eSub M X) (ePred (eSub M X)))
      (.mul Y (ePred Y)))

private def eN : PolyExpr := .add eU eFour
private def nearLExpr : PolyExpr :=
  .mul (rowOneExpr eN eTwo eI eJ)
    (rowOneExpr eN eN (eSub (.add eI eJ) eOne) eL)
private def nearR0Expr : PolyExpr :=
  rowTwoExpr eN (.add eN eTwo) eI (.add eJ eL)
private def nearR1Expr : PolyExpr :=
  .mul (rowOneExpr eTwo eN eJ eL)
    (rowOneExpr eN eN eI (eSub (.add eJ eL) eOne))
private def nearR2Expr : PolyExpr := rowTwoExpr eTwo eN eJ eL

private def nearScaledLExpr : PolyExpr :=
  .mul (.mul (.add eU eFive) (.add eU eSix)) nearLExpr

private def nearScaledRExpr : PolyExpr :=
  .add
    (.add
      (.mul (.mul eTwo (.add eU eFour)) nearR0Expr)
      (.neg (.mul (.mul eU (.add eU eFive)) nearR1Expr)))
    (.neg (.mul (.mul (.mul eTwo (.add eU eFour))
      (.add eU eSix)) nearR2Expr))

private theorem nearScaled_normal :
    normalize nearScaledLExpr = normalize nearScaledRExpr := by decide

private def eZero : PolyExpr := .const 0
private def rowOne00Expr : PolyExpr := rowOneExpr eU eI eZero eZero
private def rowOneDiagExpr : PolyExpr := rowOneExpr eU eI eU eI
private def rowTwo200Expr : PolyExpr := rowTwoExpr eTwo eU eZero eZero
private def rowTwo201Expr : PolyExpr := rowTwoExpr eTwo eU eZero eOne
private def rowTwo210Expr : PolyExpr := rowTwoExpr eTwo eU eOne eZero

private theorem rowOne00_normal :
    normalize rowOne00Expr = normalize eZero := by decide
private theorem rowOneDiag_normal :
    normalize rowOneDiagExpr = normalize eZero := by decide
private theorem rowTwo200_normal :
    normalize rowTwo200Expr = normalize eZero := by decide
private theorem rowTwo201_normal :
    normalize rowTwo201Expr = normalize eZero := by decide
private theorem rowTwo210_normal :
    normalize rowTwo210Expr = normalize eZero := by decide

private def nearPayloadEnv (U I J L : Q') : Nat → Q'
  | 0 => U
  | 1 => I
  | 2 => J
  | _ => L

/-- **Exact polynomial recoupling identity.**  After clearing only the
positive scalar `(u+5)(u+6)`, the left `(1,1)` payload is the three physical
right payloads `(0,2)`, `(1,1)`, `(2,0)`.  The middle coefficient is
`-u(u+5)`; after cancelling `u+5` against the common scale this is precisely
the predicted inverse coefficient `-u/(u+6)`. -/
theorem near_payload_scaled_recoupling (U I J L : Q') :
    ((U + 5) * (U + 6)) * nearLeftPayloadQ U I J L ≈
      ((2 : Q') * (U + 4)) * nearRightPayload0Q U I J L +
        -((U * (U + 5)) * nearRightPayload1Q U I J L) +
        -((((2 : Q') * (U + 4)) * (U + 6)) *
          nearRightPayload2Q U I J L) := by
  have h := poly_identity_of_normal_eq nearScaledLExpr nearScaledRExpr
    nearScaled_normal (nearPayloadEnv U I J L)
  simpa only [nearScaledLExpr, nearScaledRExpr, nearLExpr, nearR0Expr,
    nearR1Expr, nearR2Expr, rowOneExpr, rowTwoExpr, nearPayloadEnv,
    nearLeftPayloadQ, nearRightPayload0Q, nearRightPayload1Q,
    nearRightPayload2Q, hahnRowOneSymbolic, hahnRowTwoSymbolic, qSub,
    qPred, eSub, ePred, eN, eU, eI, eJ, eL, eOne, eTwo, eFour, eFive,
    eSix, RingNormaliser.eval, RingNormaliser.ofInt_one] using h

private theorem hahnRowOne_zero_zero (M N : Q') :
    hahnRowOneSymbolic M N 0 0 ≈ 0 := by
  have h := poly_identity_of_normal_eq rowOne00Expr eZero
    rowOne00_normal (fun i => if i = 0 then M else N)
  simpa only [rowOne00Expr, rowOneExpr, eSub, eZero, eU, eI,
    hahnRowOneSymbolic, qSub, RingNormaliser.eval,
    RingNormaliser.ofInt_zero] using h

private theorem hahnRowOne_diag_zero (M N : Q') :
    hahnRowOneSymbolic M N M N ≈ 0 := by
  have h := poly_identity_of_normal_eq rowOneDiagExpr eZero
    rowOneDiag_normal (fun i => if i = 0 then M else N)
  simpa only [rowOneDiagExpr, rowOneExpr, eSub, eZero, eU, eI,
    hahnRowOneSymbolic, qSub, RingNormaliser.eval,
    RingNormaliser.ofInt_zero] using h

private theorem hahnRowTwo_200_zero (N : Q') :
    hahnRowTwoSymbolic 2 N 0 0 ≈ 0 := by
  have h := poly_identity_of_normal_eq rowTwo200Expr eZero
    rowTwo200_normal (fun _ => N)
  simpa only [rowTwo200Expr, rowTwoExpr, eSub, ePred, eZero, eU,
    eOne, eTwo, hahnRowTwoSymbolic, qSub, qPred,
    RingNormaliser.eval, RingNormaliser.ofInt_zero,
    RingNormaliser.ofInt_one] using h

private theorem hahnRowTwo_201_zero (N : Q') :
    hahnRowTwoSymbolic 2 N 0 1 ≈ 0 := by
  have h := poly_identity_of_normal_eq rowTwo201Expr eZero
    rowTwo201_normal (fun _ => N)
  simpa only [rowTwo201Expr, rowTwoExpr, eSub, ePred, eZero, eU,
    eOne, eTwo, hahnRowTwoSymbolic, qSub, qPred,
    RingNormaliser.eval, RingNormaliser.ofInt_zero,
    RingNormaliser.ofInt_one] using h

private theorem hahnRowTwo_210_zero (N : Q') :
    hahnRowTwoSymbolic 2 N 1 0 ≈ 0 := by
  have h := poly_identity_of_normal_eq rowTwo210Expr eZero
    rowTwo210_normal (fun _ => N)
  simpa only [rowTwo210Expr, rowTwoExpr, eSub, ePred, eZero, eU,
    eOne, eTwo, hahnRowTwoSymbolic, qSub, qPred,
    RingNormaliser.eval, RingNormaliser.ofInt_zero,
    RingNormaliser.ofInt_one] using h

/-! ## Physical right channels adjoining the middle `(1,1)` channel -/

def nearRightChannel0 (u : Nat) :
    FixedRightCGChannel (nearN u) 2 (nearN u) (nearD u) where
  p := 0
  p_le := by simp
  r := 2
  r_le := by unfold nearN; omega
  degree_eq := by unfold nearN nearD; omega

def nearRightChannel2 (u : Nat) :
    FixedRightCGChannel (nearN u) 2 (nearN u) (nearD u) where
  p := 2
  p_le := by unfold nearN; omega
  r := 0
  r_le := by simp
  degree_eq := by unfold nearN nearD; omega

theorem near_right_channel_orders (u : Nat) :
    (nearRightChannel0 u).p = 0 ∧ (nearRightChannel0 u).r = 2 ∧
    (nearRightChannel u).p = 1 ∧ (nearRightChannel u).r = 1 ∧
    (nearRightChannel2 u).p = 2 ∧ (nearRightChannel2 u).r = 0 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem near_right_intermediates (u : Nat) :
    (nearRightChannel0 u).intermediate = nearN u + 2 ∧
    (nearRightChannel u).intermediate = nearN u ∧
    (nearRightChannel2 u).intermediate = u + 2 := by
  constructor
  · change 2 + nearN u - 2 * 0 = nearN u + 2
    omega
  constructor
  · exact (near_intermediates u).2
  · change 2 + nearN u - 2 * 2 = u + 2
    unfold nearN
    omega

private theorem ofNat_add_eq (a b : Nat) :
    Q'.ofNat (a + b) = Q'.ofNat a + Q'.ofNat b := by
  change Q'.ofNat (a + b) = Q'.add (Q'.ofNat a) (Q'.ofNat b)
  unfold Q'.ofNat Q'.add Q'.den
  simp only [Int.ofNat_eq_natCast, Int.natCast_add]
  simp

private theorem ofNat_sub_eq (a b : Nat) (h : b ≤ a) :
    Q'.ofNat (a - b) = qSub (Q'.ofNat a) (Q'.ofNat b) := by
  unfold qSub
  change Q'.ofNat (a - b) = Q'.add (Q'.ofNat a) (Q'.neg (Q'.ofNat b))
  have hcast : Int.ofNat (a - b) = Int.ofNat a - Int.ofNat b :=
    Int.ofNat_sub h
  unfold Q'.ofNat Q'.add Q'.neg Q'.den
  rw [hcast]
  simp [Int.sub_eq_add_neg]

private theorem ofNat_pos_local (n : Nat) (hn : 0 < n) :
    (0 : Q') < Q'.ofNat n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact Q'.ofNat_succ_pos m

private theorem ofNat_add_ofNat_pos_right (u k : Nat) (hk : 0 < k) :
    (0 : Q') < Q'.ofNat u + Q'.ofNat k := by
  show (0 : Int) * (((Q'.ofNat u + Q'.ofNat k).den : Nat) : Int) <
    (Q'.ofNat u + Q'.ofNat k).num * (1 : Int)
  simp only [Int.zero_mul, Int.mul_one, Q'.add_num_cast,
    Q'.ofNat_num_cast, Q'.ofNat_den_cast]
  have hu : (0 : Int) ≤ Int.ofNat u := Int.natCast_nonneg u
  have hk' : (0 : Int) < Int.ofNat k := Int.ofNat_lt.mpr hk
  omega

private theorem nearN_cast (u : Nat) :
    Q'.ofNat (nearN u) = Q'.ofNat u + 4 := by
  unfold nearN
  simpa using ofNat_add_eq u 4

private theorem pred_sum_cast (i j : Nat) (h : 1 ≤ i + j) :
    qSub (Q'.ofNat i + Q'.ofNat j) 1 = Q'.ofNat (i + j - 1) := by
  rw [← ofNat_add_eq i j]
  exact (ofNat_sub_eq (i + j) 1 h).symm

private theorem sum_cast (i j : Nat) :
    Q'.ofNat i + Q'.ofNat j = Q'.ofNat (i + j) := by
  exact (ofNat_add_eq i j).symm

private theorem mul_eqv_zero_of_left {a b : Q'} (ha : a ≈ 0) :
    a * b ≈ 0 :=
  Q'.eqv_trans _ (0 * b) _
    (Q'.mul_eqv_congr_right _ _ _ ha) (Q'.zero_mul_eqv _)

/-- On the nonzero physical range, the literal left factorial payload is the
symbolic polynomial used by `near_payload_scaled_recoupling`. -/
theorem near_left_payload_eq_symbolic (u i j l : Nat)
    (hi : i ≤ nearN u) (hj : j ≤ 2) (hl : l ≤ nearN u)
    (hlo : 1 ≤ i + j) (hhi : i + j - 1 ≤ nearN u) :
    leftFactorialPayload (nearLeftChannel u) i j l ≈
      nearLeftPayloadQ (Q'.ofNat u) (Q'.ofNat i) (Q'.ofNat j)
        (Q'.ofNat l) := by
  have hinner := transvectFactorialCoeff_one_symbolic
    (nearN u) 2 i j hi hj
  have houter := transvectFactorialCoeff_one_symbolic
    (nearN u) (nearN u) (i + j - 1) l hhi hl
  have ht : i + j - i = j := by omega
  unfold leftFactorialPayload nearLeftChannel
  simp only [hahnEntry, FixedLeftCGChannel.intermediate]
  rw [ht]
  refine Q'.eqv_trans _
    (hahnRowOneSymbolic (Q'.ofNat (nearN u)) 2
        (Q'.ofNat i) (Q'.ofNat j) *
      hahnRowOneSymbolic (Q'.ofNat (nearN u)) (Q'.ofNat (nearN u))
        (Q'.ofNat (i + j - 1)) (Q'.ofNat l)) _
    (Q'.eqv_trans _
      (hahnRowOneSymbolic (Q'.ofNat (nearN u)) 2
          (Q'.ofNat i) (Q'.ofNat j) *
        transvectFactorialCoeff (nearN u) (nearN u) 1
          (i + j - 1) l) _
      (Q'.mul_eqv_congr_right _ _ _ hinner)
      (Q'.mul_eqv_congr_left _ _ _ houter)) ?_
  unfold nearLeftPayloadQ
  rw [← nearN_cast u, pred_sum_cast i j hlo]
  exact Q'.eqv_refl _

theorem near_left_payload_eq_symbolic_all (u i j l : Nat)
    (hi : i ≤ nearN u) (hj : j ≤ 2) (hl : l ≤ nearN u) :
    leftFactorialPayload (nearLeftChannel u) i j l ≈
      nearLeftPayloadQ (Q'.ofNat u) (Q'.ofNat i) (Q'.ofNat j)
        (Q'.ofNat l) := by
  by_cases hlo : 1 ≤ i + j
  · by_cases hhi : i + j - 1 ≤ nearN u
    · exact near_left_payload_eq_symbolic u i j l hi hj hl hlo hhi
    · have hiEq : i = nearN u := by omega
      have hjEq : j = 2 := by omega
      subst i
      subst j
      have hinner := transvectFactorialCoeff_one_symbolic
        (nearN u) 2 (nearN u) 2 (Nat.le_refl _) (Nat.le_refl _)
      have hzero : transvectFactorialCoeff (nearN u) 2 1 (nearN u) 2 ≈ 0 :=
        Q'.eqv_trans _ _ _ hinner
          (hahnRowOne_diag_zero (Q'.ofNat (nearN u)) 2)
      have hleft : leftFactorialPayload (nearLeftChannel u)
          (nearN u) 2 l ≈ 0 := by
        unfold leftFactorialPayload nearLeftChannel hahnEntry
        simp only [FixedLeftCGChannel.intermediate,
          show nearN u + 2 - nearN u = 2 by omega]
        exact mul_eqv_zero_of_left hzero
      refine Q'.eqv_trans _ 0 _ hleft ?_
      unfold nearLeftPayloadQ
      rw [← nearN_cast u]
      exact Q'.eqv_symm (mul_eqv_zero_of_left
        (hahnRowOne_diag_zero (Q'.ofNat (nearN u)) 2))
  · have hiEq : i = 0 := by omega
    have hjEq : j = 0 := by omega
    subst i
    subst j
    have hinner := transvectFactorialCoeff_one_symbolic
      (nearN u) 2 0 0 (Nat.zero_le _) (Nat.zero_le _)
    have hzero : transvectFactorialCoeff (nearN u) 2 1 0 0 ≈ 0 :=
      Q'.eqv_trans _ _ _ hinner
        (hahnRowOne_zero_zero (Q'.ofNat (nearN u)) 2)
    have hleft : leftFactorialPayload (nearLeftChannel u) 0 0 l ≈ 0 := by
      unfold leftFactorialPayload nearLeftChannel hahnEntry
      simp only [FixedLeftCGChannel.intermediate, Nat.zero_add, Nat.sub_zero]
      exact mul_eqv_zero_of_left hzero
    refine Q'.eqv_trans _ 0 _ hleft ?_
    unfold nearLeftPayloadQ
    exact Q'.eqv_symm (mul_eqv_zero_of_left
      (hahnRowOne_zero_zero (Q'.ofNat u + 4) 2))

theorem near_right0_payload_eq_symbolic (u i j l : Nat)
    (hi : i ≤ nearN u) (hj : j ≤ 2) (hl : l ≤ nearN u) :
    rightFactorialPayload (nearRightChannel0 u) i j l ≈
      nearRightPayload0Q (Q'.ofNat u) (Q'.ofNat i) (Q'.ofNat j)
        (Q'.ofNat l) := by
  have hjl : j + l ≤ nearN u + 2 := by omega
  have hzero := hahnEntry_zero 2 (nearN u) (j + l) j
  have htwo := transvectFactorialCoeff_two_symbolic
    (nearN u) (nearN u + 2) i (j + l) hi hjl
  have hp : (nearRightChannel0 u).p = 0 := (near_right_channel_orders u).1
  have hr : (nearRightChannel0 u).r = 2 := (near_right_channel_orders u).2.1
  have hm : (nearRightChannel0 u).intermediate = nearN u + 2 :=
    (near_right_intermediates u).1
  unfold rightFactorialPayload
  rw [hp, hr, hm]
  simp only [Nat.sub_zero]
  refine Q'.eqv_trans _
    (1 * transvectFactorialCoeff (nearN u) (nearN u + 2) 2 i (j + l)) _
    (Q'.mul_eqv_congr_right _ _ _ hzero) ?_
  refine Q'.eqv_trans _
    (transvectFactorialCoeff (nearN u) (nearN u + 2) 2 i (j + l)) _
    (Q'.one_mul_eqv _) ?_
  refine Q'.eqv_trans _
    (hahnRowTwoSymbolic (Q'.ofNat (nearN u))
      (Q'.ofNat (nearN u + 2)) (Q'.ofNat i) (Q'.ofNat (j + l))) _
    htwo ?_
  unfold nearRightPayload0Q
  rw [ofNat_add_eq (nearN u) 2, nearN_cast u, sum_cast j l]
  exact Q'.eqv_refl _

theorem near_right1_payload_eq_symbolic (u i j l : Nat)
    (hi : i ≤ nearN u) (hj : j ≤ 2) (hl : l ≤ nearN u)
    (hlo : 1 ≤ j + l) (hhi : j + l - 1 ≤ nearN u) :
    rightFactorialPayload (nearRightChannel u) i j l ≈
      nearRightPayload1Q (Q'.ofNat u) (Q'.ofNat i) (Q'.ofNat j)
        (Q'.ofNat l) := by
  have hinner := transvectFactorialCoeff_one_symbolic
    2 (nearN u) j l hj hl
  have houter := transvectFactorialCoeff_one_symbolic
    (nearN u) (nearN u) i (j + l - 1) hi hhi
  have ht : j + l - j = l := by omega
  have hp : (nearRightChannel u).p = 1 := (near_right_channel_orders u).2.2.1
  have hr : (nearRightChannel u).r = 1 := (near_right_channel_orders u).2.2.2.1
  have hm : (nearRightChannel u).intermediate = nearN u :=
    (near_right_intermediates u).2.1
  unfold rightFactorialPayload
  rw [hp, hr, hm]
  simp only [hahnEntry]
  rw [ht]
  refine Q'.eqv_trans _
    (hahnRowOneSymbolic (Q'.ofNat 2) (Q'.ofNat (nearN u))
        (Q'.ofNat j) (Q'.ofNat l) *
      hahnRowOneSymbolic (Q'.ofNat (nearN u)) (Q'.ofNat (nearN u))
        (Q'.ofNat i) (Q'.ofNat (j + l - 1))) _
    (Q'.eqv_trans _
      (hahnRowOneSymbolic (Q'.ofNat 2) (Q'.ofNat (nearN u))
          (Q'.ofNat j) (Q'.ofNat l) *
        transvectFactorialCoeff (nearN u) (nearN u) 1
          i (j + l - 1)) _
      (Q'.mul_eqv_congr_right _ _ _ hinner)
      (Q'.mul_eqv_congr_left _ _ _ houter)) ?_
  unfold nearRightPayload1Q
  rw [← nearN_cast u, pred_sum_cast j l hlo]
  exact Q'.eqv_refl _

theorem near_right1_payload_eq_symbolic_all (u i j l : Nat)
    (hi : i ≤ nearN u) (hj : j ≤ 2) (hl : l ≤ nearN u) :
    rightFactorialPayload (nearRightChannel u) i j l ≈
      nearRightPayload1Q (Q'.ofNat u) (Q'.ofNat i) (Q'.ofNat j)
        (Q'.ofNat l) := by
  by_cases hlo : 1 ≤ j + l
  · by_cases hhi : j + l - 1 ≤ nearN u
    · exact near_right1_payload_eq_symbolic u i j l hi hj hl hlo hhi
    · have hjEq : j = 2 := by omega
      have hlEq : l = nearN u := by omega
      subst j
      subst l
      have hinner := transvectFactorialCoeff_one_symbolic
        2 (nearN u) 2 (nearN u) (Nat.le_refl _) (Nat.le_refl _)
      have hzero : transvectFactorialCoeff 2 (nearN u) 1 2 (nearN u) ≈ 0 :=
        Q'.eqv_trans _ _ _ hinner
          (hahnRowOne_diag_zero 2 (Q'.ofNat (nearN u)))
      have hright : rightFactorialPayload (nearRightChannel u)
          i 2 (nearN u) ≈ 0 := by
        unfold rightFactorialPayload nearRightChannel hahnEntry
        simp only [FixedRightCGChannel.intermediate,
          show 2 + nearN u - 2 = nearN u by omega]
        exact mul_eqv_zero_of_left hzero
      refine Q'.eqv_trans _ 0 _ hright ?_
      unfold nearRightPayload1Q
      rw [← nearN_cast u]
      exact Q'.eqv_symm (mul_eqv_zero_of_left
        (hahnRowOne_diag_zero 2 (Q'.ofNat (nearN u))))
  · have hjEq : j = 0 := by omega
    have hlEq : l = 0 := by omega
    subst j
    subst l
    have hinner := transvectFactorialCoeff_one_symbolic
      2 (nearN u) 0 0 (Nat.zero_le _) (Nat.zero_le _)
    have hzero : transvectFactorialCoeff 2 (nearN u) 1 0 0 ≈ 0 :=
      Q'.eqv_trans _ _ _ hinner
        (hahnRowOne_zero_zero 2 (Q'.ofNat (nearN u)))
    have hright : rightFactorialPayload (nearRightChannel u) i 0 0 ≈ 0 := by
      unfold rightFactorialPayload nearRightChannel hahnEntry
      simp only [FixedRightCGChannel.intermediate, Nat.zero_add, Nat.sub_zero]
      exact mul_eqv_zero_of_left hzero
    refine Q'.eqv_trans _ 0 _ hright ?_
    unfold nearRightPayload1Q
    exact Q'.eqv_symm (mul_eqv_zero_of_left
      (hahnRowOne_zero_zero 2 (Q'.ofNat u + 4)))

theorem near_right2_payload_eq_symbolic (u i j l : Nat)
    (_hi : i ≤ nearN u) (hj : j ≤ 2) (hl : l ≤ nearN u) :
    rightFactorialPayload (nearRightChannel2 u) i j l ≈
      nearRightPayload2Q (Q'.ofNat u) (Q'.ofNat i) (Q'.ofNat j)
        (Q'.ofNat l) := by
  have hinner := transvectFactorialCoeff_two_symbolic
    2 (nearN u) j l hj hl
  have hzero := transvectFactorialCoeff_zero
    (nearN u) (2 + nearN u - 2 * 2) i (j + l - 2)
  have ht : j + l - j = l := by omega
  unfold rightFactorialPayload nearRightChannel2
  simp only [hahnEntry, FixedRightCGChannel.intermediate]
  rw [ht]
  refine Q'.eqv_trans _
    (transvectFactorialCoeff 2 (nearN u) 2 j l * 1) _
    (Q'.mul_eqv_congr_left _ _ _ hzero) ?_
  refine Q'.eqv_trans _
    (transvectFactorialCoeff 2 (nearN u) 2 j l) _
    (Q'.mul_one_eqv _) ?_
  refine Q'.eqv_trans _
    (hahnRowTwoSymbolic 2 (Q'.ofNat (nearN u))
      (Q'.ofNat j) (Q'.ofNat l)) _ hinner ?_
  unfold nearRightPayload2Q
  rw [← nearN_cast u]
  exact Q'.eqv_refl _

theorem near_physical_payload_scaled_recoupling (u i j l : Nat)
    (hi : i ≤ nearN u) (hj : j ≤ 2) (hl : l ≤ nearN u) :
    ((Q'.ofNat u + 5) * (Q'.ofNat u + 6)) *
        leftFactorialPayload (nearLeftChannel u) i j l ≈
      ((2 : Q') * (Q'.ofNat u + 4)) *
          rightFactorialPayload (nearRightChannel0 u) i j l +
        -((Q'.ofNat u * (Q'.ofNat u + 5)) *
          rightFactorialPayload (nearRightChannel u) i j l) +
        -((((2 : Q') * (Q'.ofNat u + 4)) * (Q'.ofNat u + 6)) *
          rightFactorialPayload (nearRightChannel2 u) i j l) := by
  have hL := near_left_payload_eq_symbolic_all u i j l hi hj hl
  have h0 := near_right0_payload_eq_symbolic u i j l hi hj hl
  have h1 := near_right1_payload_eq_symbolic_all u i j l hi hj hl
  have h2 := near_right2_payload_eq_symbolic u i j l hi hj hl
  have hpoly := near_payload_scaled_recoupling
    (Q'.ofNat u) (Q'.ofNat i) (Q'.ofNat j) (Q'.ofNat l)
  refine Q'.eqv_trans _
    (((Q'.ofNat u + 5) * (Q'.ofNat u + 6)) *
      nearLeftPayloadQ (Q'.ofNat u) (Q'.ofNat i) (Q'.ofNat j)
        (Q'.ofNat l)) _
    (Q'.mul_eqv_congr_left _ _ _ hL) ?_
  refine Q'.eqv_trans _ _ _ hpoly ?_
  exact Q'.add_eqv_congr'
    (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm h0))
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm h1))))
    (Q'.neg_eqv_congr _ _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm h2)))

private theorem near_left_payload_zero_below (u i j l : Nat)
    (hi : i ≤ nearN u) (hj : j ≤ 2) (hl : l ≤ nearN u)
    (hbelow : i + j < 1) :
    leftFactorialPayload (nearLeftChannel u) i j l ≈ 0 := by
  have hi0 : i = 0 := by omega
  have hj0 : j = 0 := by omega
  subst i
  subst j
  refine Q'.eqv_trans _
    (nearLeftPayloadQ (Q'.ofNat u) 0 0 (Q'.ofNat l)) _
    (near_left_payload_eq_symbolic_all u 0 0 l hi hj hl) ?_
  unfold nearLeftPayloadQ
  exact mul_eqv_zero_of_left (hahnRowOne_zero_zero (Q'.ofNat u + 4) 2)

private theorem near_right1_payload_zero_below (u i j l : Nat)
    (hi : i ≤ nearN u) (hj : j ≤ 2) (hl : l ≤ nearN u)
    (hbelow : j + l < 1) :
    rightFactorialPayload (nearRightChannel u) i j l ≈ 0 := by
  have hj0 : j = 0 := by omega
  have hl0 : l = 0 := by omega
  subst j
  subst l
  refine Q'.eqv_trans _
    (nearRightPayload1Q (Q'.ofNat u) (Q'.ofNat i) 0 0) _
    (near_right1_payload_eq_symbolic_all u i 0 0 hi hj hl) ?_
  unfold nearRightPayload1Q
  exact mul_eqv_zero_of_left (hahnRowOne_zero_zero 2 (Q'.ofNat u + 4))

private theorem near_right2_payload_zero_below (u i j l : Nat)
    (hi : i ≤ nearN u) (hj : j ≤ 2) (hl : l ≤ nearN u)
    (hbelow : j + l < 2) :
    rightFactorialPayload (nearRightChannel2 u) i j l ≈ 0 := by
  refine Q'.eqv_trans _
    (nearRightPayload2Q (Q'.ofNat u) (Q'.ofNat i)
      (Q'.ofNat j) (Q'.ofNat l)) _
    (near_right2_payload_eq_symbolic u i j l hi hj hl) ?_
  cases j with
  | zero =>
      cases l with
      | zero => exact hahnRowTwo_200_zero (Q'.ofNat u + 4)
      | succ l =>
          cases l with
          | zero => exact hahnRowTwo_201_zero (Q'.ofNat u + 4)
          | succ l => omega
  | succ j =>
      cases j with
      | zero =>
          cases l with
          | zero => exact hahnRowTwo_210_zero (Q'.ofNat u + 4)
          | succ l => omega
      | succ j => omega

private theorem near_guardedLeft_eq_shellPayload (u i j l s : Nat)
    (hi : i ≤ nearN u) (hj : j ≤ 2) (hl : l ≤ nearN u) :
    guardedLeftFactorialCoefficient (nearLeftChannel u) i j l s ≈
      if s + 2 = i + j + l then
        leftFactorialPayload (nearLeftChannel u) i j l else 0 := by
  unfold guardedLeftFactorialCoefficient leftFactorialPayload
  simp only [nearLeftChannel, FixedLeftCGChannel.intermediate]
  by_cases hinner : 1 ≤ i + j
  · rw [if_pos hinner]
    by_cases hs : s + 2 = i + j + l
    · rw [if_pos hs, if_pos]
      · exact Q'.eqv_refl _
      · omega
    · rw [if_neg hs, if_neg]
      · exact Q'.mul_zero_eqv _
      · intro h
        apply hs
        omega
  · rw [if_neg hinner]
    have hzero := near_left_payload_zero_below u i j l hi hj hl (by omega)
    by_cases hs : s + 2 = i + j + l
    · rw [if_pos hs]
      exact Q'.eqv_symm hzero
    · rw [if_neg hs]
      exact Q'.eqv_refl 0

private theorem near_guardedRight0_eq_shellPayload (u i j l s : Nat) :
    guardedRightFactorialCoefficient (nearRightChannel0 u) i j l s ≈
      if s + 2 = i + j + l then
        rightFactorialPayload (nearRightChannel0 u) i j l else 0 := by
  unfold guardedRightFactorialCoefficient rightFactorialPayload
  simp only [nearRightChannel0, Nat.zero_le, if_true, Nat.sub_zero,
    FixedRightCGChannel.intermediate]
  by_cases hs : s + 2 = i + j + l
  · rw [if_pos hs, if_pos (by omega)]
    exact Q'.eqv_refl _
  · rw [if_neg hs, if_neg]
    · exact Q'.mul_zero_eqv _
    · intro h
      apply hs
      omega

private theorem near_guardedRight1_eq_shellPayload (u i j l s : Nat)
    (hi : i ≤ nearN u) (hj : j ≤ 2) (hl : l ≤ nearN u) :
    guardedRightFactorialCoefficient (nearRightChannel u) i j l s ≈
      if s + 2 = i + j + l then
        rightFactorialPayload (nearRightChannel u) i j l else 0 := by
  unfold guardedRightFactorialCoefficient rightFactorialPayload
  simp only [nearRightChannel, FixedRightCGChannel.intermediate]
  by_cases hinner : 1 ≤ j + l
  · rw [if_pos hinner]
    by_cases hs : s + 2 = i + j + l
    · rw [if_pos hs, if_pos]
      · exact Q'.eqv_refl _
      · omega
    · rw [if_neg hs, if_neg]
      · exact Q'.mul_zero_eqv _
      · intro h
        apply hs
        omega
  · rw [if_neg hinner]
    have hzero := near_right1_payload_zero_below u i j l hi hj hl (by omega)
    by_cases hs : s + 2 = i + j + l
    · rw [if_pos hs]
      exact Q'.eqv_symm hzero
    · rw [if_neg hs]
      exact Q'.eqv_refl 0

private theorem near_guardedRight2_eq_shellPayload (u i j l s : Nat)
    (hi : i ≤ nearN u) (hj : j ≤ 2) (hl : l ≤ nearN u) :
    guardedRightFactorialCoefficient (nearRightChannel2 u) i j l s ≈
      if s + 2 = i + j + l then
        rightFactorialPayload (nearRightChannel2 u) i j l else 0 := by
  unfold guardedRightFactorialCoefficient rightFactorialPayload
  simp only [nearRightChannel2, FixedRightCGChannel.intermediate]
  by_cases hinner : 2 ≤ j + l
  · rw [if_pos hinner]
    by_cases hs : s + 2 = i + j + l
    · rw [if_pos hs, if_pos]
      · exact Q'.eqv_refl _
      · omega
    · rw [if_neg hs, if_neg]
      · exact Q'.mul_zero_eqv _
      · intro h
        apply hs
        omega
  · rw [if_neg hinner]
    have hzero := near_right2_payload_zero_below u i j l hi hj hl (by omega)
    by_cases hs : s + 2 = i + j + l
    · rw [if_pos hs]
      exact Q'.eqv_symm hzero
    · rw [if_neg hs]
      exact Q'.eqv_refl 0

/-- The symbolic polynomial identity is the actual physical recoupling row
on the complete monomial box.  It is kept denominator-free: the common scale
is `(u+5)(u+6)`. -/
theorem near_triMap_scaled_recoupling (u : Nat) :
    let U := Q'.ofNat u
    let D := (U + 5) * (U + 6)
    let B := (2 : Q') * (U + 4)
    let A := U * (U + 5)
    let G := ((2 : Q') * (U + 4)) * (U + 6)
    TriMapEqv (nearN u) 2 (nearN u) (nearD u)
      (fun x y z => scaleForm D
        (triLeft (nearN u) 2 (nearN u) (nearD u) (nearN u) x y z))
      (fun x y z => addForm
        (scaleForm B
          (triRight (nearN u) 2 (nearN u) (nearD u)
            (nearRightChannel0 u).intermediate x y z))
        (addForm
          (scaleForm (-A)
            (triRight (nearN u) 2 (nearN u) (nearD u)
              (nearRightChannel u).intermediate x y z))
          (scaleForm (-G)
            (triRight (nearN u) 2 (nearN u) (nearD u)
              (nearRightChannel2 u).intermediate x y z)))) := by
  dsimp only
  intro i hi j hj l hl s hsout
  have hi' : i ≤ nearN u := by omega
  have hj' : j ≤ 2 := by omega
  have hl' : l ≤ nearN u := by omega
  have hL0 := triLeft_monomial_eq_guardedHahn
    (nearLeftChannel u) i j l s
  have hLf := guardedLeftHahnCoefficient_eq_factorial
    (nearLeftChannel u) i j l s
  have hL := Q'.eqv_trans _ _ _ hL0 hLf
  have h00 := triRight_monomial_eq_guardedHahn
    (nearRightChannel0 u) i j l s
  have h0f := guardedRightHahnCoefficient_eq_factorial
    (nearRightChannel0 u) i j l s
  have h0 := Q'.eqv_trans _ _ _ h00 h0f
  have h10 := triRight_monomial_eq_guardedHahn
    (nearRightChannel u) i j l s
  have h1f := guardedRightHahnCoefficient_eq_factorial
    (nearRightChannel u) i j l s
  have h1 := Q'.eqv_trans _ _ _ h10 h1f
  have h20 := triRight_monomial_eq_guardedHahn
    (nearRightChannel2 u) i j l s
  have h2f := guardedRightHahnCoefficient_eq_factorial
    (nearRightChannel2 u) i j l s
  have h2 := Q'.eqv_trans _ _ _ h20 h2f
  have hgL := near_guardedLeft_eq_shellPayload u i j l s hi' hj' hl'
  have hg0 := near_guardedRight0_eq_shellPayload u i j l s
  have hg1 := near_guardedRight1_eq_shellPayload u i j l s hi' hj' hl'
  have hg2 := near_guardedRight2_eq_shellPayload u i j l s hi' hj' hl'
  by_cases hshell : s + 2 = i + j + l
  · rw [if_pos hshell] at hgL hg0 hg1 hg2
    have hcL := Q'.eqv_trans _ _ _ hL hgL
    have hc0 := Q'.eqv_trans _ _ _ h0 hg0
    have hc1 := Q'.eqv_trans _ _ _ h1 hg1
    have hc2 := Q'.eqv_trans _ _ _ h2 hg2
    have hp := near_physical_payload_scaled_recoupling u i j l hi' hj' hl'
    unfold scaleForm addForm
    refine Q'.eqv_trans _
      (((Q'.ofNat u + 5) * (Q'.ofNat u + 6)) *
        leftFactorialPayload (nearLeftChannel u) i j l) _
      (Q'.mul_eqv_congr_left _ _ _ hcL) ?_
    refine Q'.eqv_trans _ _ _ hp ?_
    have hrhs :
        ((2 : Q') * (Q'.ofNat u + 4)) *
              rightFactorialPayload (nearRightChannel0 u) i j l +
            -((Q'.ofNat u * (Q'.ofNat u + 5)) *
              rightFactorialPayload (nearRightChannel u) i j l) +
            -((((2 : Q') * (Q'.ofNat u + 4)) * (Q'.ofNat u + 6)) *
              rightFactorialPayload (nearRightChannel2 u) i j l) ≈
          ((2 : Q') * (Q'.ofNat u + 4)) *
              triRight (nearN u) 2 (nearN u) (nearD u)
                (nearRightChannel0 u).intermediate
                (mono i) (mono j) (mono l) s +
            (-(Q'.ofNat u * (Q'.ofNat u + 5))) *
              triRight (nearN u) 2 (nearN u) (nearD u)
                (nearRightChannel u).intermediate
                (mono i) (mono j) (mono l) s +
            (-( ((2 : Q') * (Q'.ofNat u + 4) * (Q'.ofNat u + 6)))) *
              triRight (nearN u) 2 (nearN u) (nearD u)
                (nearRightChannel2 u).intermediate
                (mono i) (mono j) (mono l) s := by
      have hsub := Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left
            ((2 : Q') * (Q'.ofNat u + 4)) _ _ (Q'.eqv_symm hc0))
          (Q'.neg_eqv_congr _ _
            (Q'.mul_eqv_congr_left
              (Q'.ofNat u * (Q'.ofNat u + 5)) _ _
              (Q'.eqv_symm hc1))))
        (Q'.neg_eqv_congr _ _
          (Q'.mul_eqv_congr_left
            (((2 : Q') * (Q'.ofNat u + 4)) * (Q'.ofNat u + 6)) _ _
            (Q'.eqv_symm hc2)))
      exact Q'.eqv_trans _ _ _ hsub (by ring_qeqv)
    exact Q'.eqv_trans _ _ _ hrhs (by ring_qeqv)
  · rw [if_neg hshell] at hgL hg0 hg1 hg2
    have hcL := Q'.eqv_trans _ _ _ hL hgL
    have hc0 := Q'.eqv_trans _ _ _ h0 hg0
    have hc1 := Q'.eqv_trans _ _ _ h1 hg1
    have hc2 := Q'.eqv_trans _ _ _ h2 hg2
    unfold scaleForm addForm
    refine Q'.eqv_trans _ (((Q'.ofNat u + 5) * (Q'.ofNat u + 6)) * 0) _
      (Q'.mul_eqv_congr_left _ _ _ hcL) ?_
    refine Q'.eqv_trans _ 0 _ (Q'.mul_zero_eqv _) ?_
    refine Q'.eqv_symm (Q'.eqv_trans _
      (((2 : Q') * (Q'.ofNat u + 4)) * 0 +
        ((-(Q'.ofNat u * (Q'.ofNat u + 5))) * 0 +
        (-( ((2 : Q') * (Q'.ofNat u + 4) * (Q'.ofNat u + 6)))) * 0)) _ ?_ ?_)
    · exact Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left _ _ _ hc0)
        (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left _ _ _ hc1)
          (Q'.mul_eqv_congr_left _ _ _ hc2))
    · ring_qeqv

/-! ## Pairing the recoupling row and cancelling the positive common scale -/

/-- Pairing the denominator-free three-channel recoupling row against the
middle right channel kills the `(0,2)` and `(2,0)` terms by the proved
all-label Casimir orthogonality law. -/
theorem near_scaled_cross_gram (u : Nat) :
    let U := Q'.ofNat u
    let C := triCrossChannelWeight (nearLeftChannel u) (nearRightChannel u)
    let W := triRightChannelWeight (nearN u) 2 (nearN u) (nearD u) (nearN u)
    ((U + 5) * (U + 6)) * C ≈ -(U * (U + 5)) * W := by
  dsimp only
  let L := triLeft (nearN u) 2 (nearN u) (nearD u) (nearN u)
  let R0 := triRight (nearN u) 2 (nearN u) (nearD u)
    (nearRightChannel0 u).intermediate
  let R1 := triRight (nearN u) 2 (nearN u) (nearD u)
    (nearRightChannel u).intermediate
  let R2 := triRight (nearN u) 2 (nearN u) (nearD u)
    (nearRightChannel2 u).intermediate
  let U := Q'.ofNat u
  let D := (U + 5) * (U + 6)
  let B := (2 : Q') * (U + 4)
  let A := U * (U + 5)
  let G := ((2 : Q') * (U + 4)) * (U + 6)
  let M := fun x y z => addForm
    (scaleForm B (R0 x y z))
    (addForm (scaleForm (-A) (R1 x y z))
      (scaleForm (-G) (R2 x y z)))
  have hrow : TriMapEqv (nearN u) 2 (nearN u) (nearD u)
      (fun x y z => scaleForm D (L x y z)) M := by
    simpa only [U, D, B, A, G, L, R0, R1, R2, M] using
      near_triMap_scaled_recoupling u
  have hpair := triMapInner_congr_left
    (R := R1) hrow
  have hleft := triMapInner_scale_left (nearN u) 2 (nearN u) (nearD u)
    D L R1
  have hadd0 := triMapInner_add_left (nearN u) 2 (nearN u) (nearD u)
    (fun x y z => scaleForm B (R0 x y z))
    (fun x y z => addForm (scaleForm (-A) (R1 x y z))
      (scaleForm (-G) (R2 x y z))) R1
  have hadd1 := triMapInner_add_left (nearN u) 2 (nearN u) (nearD u)
    (fun x y z => scaleForm (-A) (R1 x y z))
    (fun x y z => scaleForm (-G) (R2 x y z)) R1
  have hscale0 := triMapInner_scale_left (nearN u) 2 (nearN u) (nearD u)
    B R0 R1
  have hscale1 := triMapInner_scale_left (nearN u) 2 (nearN u) (nearD u)
    (-A) R1 R1
  have hscale2 := triMapInner_scale_left (nearN u) 2 (nearN u) (nearD u)
    (-G) R2 R1
  have hgram0 := rightChannel_gram_all
    (nearRightChannel0 u) (nearRightChannel u)
  have hgram1 := rightChannel_gram_all
    (nearRightChannel u) (nearRightChannel u)
  have hgram2 := rightChannel_gram_all
    (nearRightChannel2 u) (nearRightChannel u)
  have hp01 : (nearRightChannel0 u).p ≠ (nearRightChannel u).p := by
    intro h
    change 0 = 1 at h
    omega
  have hp21 : (nearRightChannel2 u).p ≠ (nearRightChannel u).p := by
    intro h
    change 2 = 1 at h
    omega
  have hgram0' : triMapInner (nearN u) 2 (nearN u) (nearD u) R0 R1 ≈ 0 := by
    simpa only [R0, R1, hp01, if_false] using hgram0
  have hgram1' : triMapInner (nearN u) 2 (nearN u) (nearD u) R1 R1 ≈
      triRightChannelWeight (nearN u) 2 (nearN u) (nearD u) (nearN u) := by
    simpa only [R1, if_pos rfl, (near_intermediates u).2] using hgram1
  have hgram2' : triMapInner (nearN u) 2 (nearN u) (nearD u) R2 R1 ≈ 0 := by
    simpa only [R2, R1, hp21, if_false] using hgram2
  have hright : triMapInner (nearN u) 2 (nearN u) (nearD u) M R1 ≈
      (-A) * triRightChannelWeight (nearN u) 2 (nearN u) (nearD u)
        (nearN u) := by
    refine Q'.eqv_trans _
      (triMapInner (nearN u) 2 (nearN u) (nearD u)
          (fun x y z => scaleForm B (R0 x y z)) R1 +
        triMapInner (nearN u) 2 (nearN u) (nearD u)
          (fun x y z => addForm (scaleForm (-A) (R1 x y z))
            (scaleForm (-G) (R2 x y z))) R1) _
      (by simpa only [M] using hadd0) ?_
    refine Q'.eqv_trans _
      (B * triMapInner (nearN u) 2 (nearN u) (nearD u) R0 R1 +
        ((-A) * triMapInner (nearN u) 2 (nearN u) (nearD u) R1 R1 +
          (-G) * triMapInner (nearN u) 2 (nearN u) (nearD u) R2 R1)) _ ?_ ?_
    · exact Q'.add_eqv_congr' hscale0
        (Q'.eqv_trans _ _ _ hadd1 (Q'.add_eqv_congr' hscale1 hscale2))
    refine Q'.eqv_trans _
      (B * 0 + ((-A) *
        triRightChannelWeight (nearN u) 2 (nearN u) (nearD u) (nearN u) +
        (-G) * 0)) _ ?_ ?_
    · exact Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left B _ _ hgram0')
        (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left (-A) _ _ hgram1')
          (Q'.mul_eqv_congr_left (-G) _ _ hgram2'))
    · refine Q'.eqv_trans _
        (0 + ((-A) *
          triRightChannelWeight (nearN u) 2 (nearN u) (nearD u) (nearN u) +
          0)) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (Q'.mul_zero_eqv B)
          (Q'.add_eqv_congr'
            (Q'.eqv_refl _)
            (Q'.mul_zero_eqv (-G)))
      · exact Q'.eqv_trans _
          ((-A) * triRightChannelWeight (nearN u) 2 (nearN u) (nearD u)
            (nearN u) + 0) _
          (Q'.eqv_of_eq (Q'.zero_add' _))
          (Q'.eqv_of_eq (Q'.add_zero' _))
  refine Q'.eqv_trans _
    (triMapInner (nearN u) 2 (nearN u) (nearD u)
      (fun x y z => scaleForm D (L x y z)) R1) _
    (Q'.eqv_symm hleft) ?_
  refine Q'.eqv_trans _
    (triMapInner (nearN u) 2 (nearN u) (nearD u) M R1) _ hpair ?_
  simpa only [U, D, A, L, R1, triCrossChannelWeight,
    (near_intermediates u).1, (near_intermediates u).2] using hright

/-- **Closed physical cross normalization.**  The exact signed factorial
cross carrier satisfies

`(u+6) * cross = -u * W_right`.

This proves the missing unsquared normalization, including the sign, without
division and without assuming the Racah square. -/
theorem near_collapsed_cross_scale (u : Nat) :
    (Q'.ofNat u + 6) *
        collapsedFactorialCrossSum (nearLeftChannel u) (nearRightChannel u) ≈
      (-Q'.ofNat u) *
        triRightChannelWeight (nearN u) 2 (nearN u) (nearD u) (nearN u) := by
  let C := triCrossChannelWeight (nearLeftChannel u) (nearRightChannel u)
  let X := (Q'.ofNat u + 6) * C
  let Y := (-Q'.ofNat u) *
    triRightChannelWeight (nearN u) 2 (nearN u) (nearD u) (nearN u)
  have hscaled := near_scaled_cross_gram u
  have hfactor : (Q'.ofNat u + 5) * X ≈ (Q'.ofNat u + 5) * Y := by
    refine Q'.eqv_trans _
      (((Q'.ofNat u + 5) * (Q'.ofNat u + 6)) * C) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    refine Q'.eqv_trans _
      (-(Q'.ofNat u * (Q'.ofNat u + 5)) *
        triRightChannelWeight (nearN u) 2 (nearN u) (nearD u) (nearN u)) _
      hscaled ?_
    unfold Y
    ring_qeqv
  have hpos : (0 : Q') < Q'.ofNat u + 5 := by
    exact ofNat_add_ofNat_pos_right u 5 (by omega)
  have hXY : X ≈ Y := Q'.mul_left_cancel_of_pos hpos hfactor
  have hcarrier := triCrossChannelWeight_eq_collapsedFactorialCrossSum
    (nearLeftChannel u) (nearRightChannel u)
  unfold X Y C at hXY
  exact Q'.eqv_trans _
    ((Q'.ofNat u + 6) *
      triCrossChannelWeight (nearLeftChannel u) (nearRightChannel u)) _
    (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hcarrier)) hXY

/-! ## Unsquared Schur coefficient and collapsed square -/

/-- The physical inverse Schur coefficient for the near-stretched family is
exactly `-u/(u+6)`.  The proof compares the cross carrier in two ways: the
three-channel transvectant row gives its explicit scale, while the arbitrary
Casimir capstone expresses it as the positive right Gram weight times the
inverse Schur coefficient. -/
theorem near_inverseSchurCoeff_closed (u : Nat) :
    fixedLeftRightDiagonalCoeff (nearLeftChannel u) (nearRightChannel u) 0 ≈
      nearInverseCoeffClosed u := by
  let U := Q'.ofNat u
  let W := triRightChannelWeight (nearN u) 2 (nearN u) (nearD u) (nearN u)
  let K := fixedLeftRightDiagonalCoeff (nearLeftChannel u)
    (nearRightChannel u) 0
  have hcross := near_collapsed_cross_scale u
  have hcap := collapsed_cross_inverse_normalization_arbitrary
    (nearLeftChannel u) (nearRightChannel u)
  have hcap' : collapsedFactorialCrossSum
        (nearLeftChannel u) (nearRightChannel u) ≈ W * K := by
    simpa only [W, K, (near_intermediates u).2] using hcap
  have hscaled : W * ((U + 6) * K) ≈ W * (-U) := by
    refine Q'.eqv_trans _ ((U + 6) * (W * K)) _ (by ring_qeqv) ?_
    refine Q'.eqv_trans _
      ((U + 6) * collapsedFactorialCrossSum
        (nearLeftChannel u) (nearRightChannel u)) _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hcap')) ?_
    refine Q'.eqv_trans _ ((-U) * W) _ ?_ (by ring_qeqv)
    simpa only [U, W] using hcross
  have hWpos : (0 : Q') < W := by
    simpa only [W, (near_intermediates u).2] using
      right_channel_weight_pos_all (nearRightChannel u)
  have hKscale : (U + 6) * K ≈ -U :=
    Q'.mul_left_cancel_of_pos hWpos hscaled
  have hclosed : (U + 6) * nearInverseCoeffClosed u ≈ -U := by
    simpa only [U] using nearInverseCoeffClosed_scale u
  have hdenPos : (0 : Q') < U + 6 := by
    unfold U
    exact ofNat_add_ofNat_pos_right u 6 (by omega)
  exact Q'.mul_left_cancel_of_pos hdenPos
    (Q'.eqv_trans _ (-U) _ hKscale (Q'.eqv_symm hclosed))

/-- Exact signed cross normalization after the inverse Schur coefficient has
been identified. -/
theorem near_collapsed_cross_closed (u : Nat) :
    collapsedFactorialCrossSum (nearLeftChannel u) (nearRightChannel u) ≈
      triRightChannelWeight (nearN u) 2 (nearN u) (nearD u) (nearN u) *
        nearInverseCoeffClosed u := by
  have hcap := collapsed_cross_inverse_normalization_arbitrary
    (nearLeftChannel u) (nearRightChannel u)
  refine Q'.eqv_trans _
    (triRightChannelWeight (nearN u) 2 (nearN u) (nearD u) (nearN u) *
      fixedLeftRightDiagonalCoeff (nearLeftChannel u)
        (nearRightChannel u) 0) _ ?_ ?_
  · simpa only [(near_intermediates u).2] using hcap
  · exact Q'.mul_eqv_congr_left _ _ _ (near_inverseSchurCoeff_closed u)

/-- **Near-stretched physical collapsed Racah square.**  For every `u`, the
ordered family `(u+4,2,u+4; 2u+6; u+4,u+4)` satisfies the exact signed
factorial cross/Gram square identity. -/
theorem near_collapsedRacahSquare (u : Nat) :
    CollapsedRacahSquareAt (nearLeftChannel u) (nearRightChannel u) :=
  near_collapsedRacahSquare_of_inverseCoeff u
    (near_inverseSchurCoeff_closed u)

end YMGap.Continuum.SU2OrderedRacahNearStretchedCrossNormalization

#print axioms YMGap.Continuum.SU2OrderedRacahNearStretchedCrossNormalization.near_collapsedRacahSquare
