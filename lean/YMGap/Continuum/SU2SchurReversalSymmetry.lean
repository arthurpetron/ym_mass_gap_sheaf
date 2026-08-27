/-
# Reversal symmetry of the physical SU(2) Schur channels

Reversing the three external legs exchanges the left- and right-associated
channel types.  The two binary vertices are reversed, so the corresponding
trilinear map acquires exactly the product of the two transvectant swap
phases.  Since that phase is involutive, diagonal Gram weights are unchanged.

This is the symmetry input for deriving column normalization from the already
proved row normalization.  It is deliberately stated before any finite-list
enumeration: the maps act on proof-carrying physical channels themselves.

Constructive contract: exact rational identities only, with no choice,
`Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.SU2PhysicalSchurRecouplingKernel
import YMGap.Constructive.FinSumAlg

namespace YMGap.Continuum.SU2SchurReversalSymmetry

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantLinearity
open YMGap.Continuum.SU2TransvectantSwapParity
open YMGap.Continuum.SU2OrderedRightNormalizationBridge
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantMixedRecouplingGNSCompleted
open YMGap.Continuum.SU2TransvectantAllLabelGramCompleted
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2PhysicalSchurRecouplingKernel
open YMGap.Continuum.SU2OrderedRacahInteriorSchurBridge
open YMGap.Continuum.SU2OrderedLeftCasimirPairing
open YMGap.Continuum.SU2TransvectantAllLabelGNSIsometryCompleted

local infix:50 " ≈ " => Q'.eqv

/-- Reverse a right-associated `(a,(b,c))` channel into the left-associated
`((c,b),a)` channel with the same two contraction orders. -/
def reverseRightAsLeft {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) :
    FixedLeftCGChannel c b a d where
  k := q.p
  k_le := Nat.le_min.mpr
    ⟨(Nat.le_min.mp q.p_le).2, (Nat.le_min.mp q.p_le).1⟩
  r := q.r
  r_le := by
    have hr := Nat.le_min.mp q.r_le
    apply Nat.le_min.mpr
    constructor
    · omega
    · exact hr.1
  degree_eq := by
    have h := q.degree_eq
    omega

/-- Reverse a left-associated `((a,b),c)` channel into the right-associated
`(c,(b,a))` channel with the same two contraction orders. -/
def reverseLeftAsRight {a b c d : Nat}
    (q : FixedLeftCGChannel a b c d) :
    FixedRightCGChannel c b a d where
  p := q.k
  p_le := Nat.le_min.mpr
    ⟨(Nat.le_min.mp q.k_le).2, (Nat.le_min.mp q.k_le).1⟩
  r := q.r
  r_le := by
    have hr := Nat.le_min.mp q.r_le
    apply Nat.le_min.mpr
    constructor
    · exact hr.2
    · omega
  degree_eq := by
    have h := q.degree_eq
    omega

@[simp] theorem reverseRightAsLeft_intermediate {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) :
    (reverseRightAsLeft q).intermediate = q.intermediate := by
  change c + b - 2 * q.p = b + c - 2 * q.p
  omega

@[simp] theorem reverseLeftAsRight_intermediate {a b c d : Nat}
    (q : FixedLeftCGChannel a b c d) :
    (reverseLeftAsRight q).intermediate = q.intermediate := by
  change b + a - 2 * q.k = a + b - 2 * q.k
  omega

/-- Reversing a right channel and then reversing back is definitionally
faithful to all contraction labels and proofs. -/
theorem reverseLeftAsRight_reverseRightAsLeft {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) :
    reverseLeftAsRight (reverseRightAsLeft q) = q := by
  cases q
  rfl

/-- Reversing a left channel and then reversing back is definitionally
faithful to all contraction labels and proofs. -/
theorem reverseRightAsLeft_reverseLeftAsRight {a b c d : Nat}
    (q : FixedLeftCGChannel a b c d) :
    reverseRightAsLeft (reverseLeftAsRight q) = q := by
  cases q
  rfl

/-- Product of the inner and outer swap phases for a right channel. -/
def reverseRightPhase {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) : Q' :=
  swapPhase q.p * swapPhase q.r

/-- Product of the inner and outer swap phases for a left channel. -/
def reverseLeftPhase {a b c d : Nat}
    (q : FixedLeftCGChannel a b c d) : Q' :=
  swapPhase q.k * swapPhase q.r

private theorem tprod_swapped_scaled (p : Q') (u v u' : BForm)
    (hu : BFormEqv u' (scaleForm p u)) :
    BForm2Eqv (tprod u' v) (bscale p (transpose2 (tprod v u))) := by
  intro i j
  unfold tprod bscale transpose2
  have hui := hu i
  change u' i ≈ p * u i at hui
  exact Q'.eqv_trans _ ((p * u i) * v j) _
    (Q'.mul_eqv_congr_right _ _ (v j) hui)
    (by ring_qeqv)

/-- Reversing the three arguments turns a right-associated channel into its
reversed left-associated channel, with exactly the two vertex swap phases. -/
theorem reverseRight_triLeft {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (x y z : BForm) :
    BFormEqv
      (triLeft c b a d (reverseRightAsLeft q).intermediate z y x)
      (scaleForm (reverseRightPhase q)
        (triRight a b c d q.intermediate x y z)) := by
  let inner := transvect b c q.p (tprod y z)
  let reversedInner := transvect c b q.p (tprod z y)
  have htranspose : BForm2Eqv (transpose2 (tprod y z)) (tprod z y) := by
    intro i j
    unfold transpose2 tprod
    exact Q'.mul_comm_eqv _ _
  have hinner0 := transvect_congr c b q.p htranspose
  have hinner1 := transvect_transpose b c q.p (tprod y z)
  have hinner : BFormEqv reversedInner (scaleForm (swapPhase q.p) inner) := by
    intro s
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_symm (by simpa only [reversedInner] using hinner0 s))
      (by simpa only [inner, scaleForm] using hinner1 s)
  have htensor := tprod_swapped_scaled (swapPhase q.p) inner x
    reversedInner hinner
  have houterCongr := transvect_congr q.intermediate a q.r htensor
  have houterScale := transvect_scale q.intermediate a q.r
    (swapPhase q.p) (transpose2 (tprod x inner))
  have houterSwap := transvect_transpose a q.intermediate q.r
    (tprod x inner)
  intro s
  unfold triLeft triRight
  rw [fixedLeft_inner_couplingOrder (reverseRightAsLeft q),
    fixedLeft_outer_couplingOrder (reverseRightAsLeft q),
    fixedRight_inner_couplingOrder q, fixedRight_outer_couplingOrder q,
    reverseRightAsLeft_intermediate q]
  exact Q'.eqv_trans _ _ _ (houterCongr s)
    (Q'.eqv_trans _ _ _ (houterScale s)
      (Q'.eqv_trans _
        (swapPhase q.p *
          (swapPhase q.r * transvect a q.intermediate q.r
            (tprod x inner) s)) _
        (Q'.mul_eqv_congr_left _ _ _ (houterSwap s))
        (by unfold reverseRightPhase scaleForm inner; ring_qeqv)))

private theorem phaseProduct_mul_self (k r : Nat) :
    (swapPhase k * swapPhase r) * (swapPhase k * swapPhase r) ≈ 1 := by
  refine Q'.eqv_trans _
    ((swapPhase k * swapPhase k) * (swapPhase r * swapPhase r)) _
    (by ring_qeqv) ?_
  refine Q'.eqv_trans _ (1 * 1) _ ?_ (Q'.one_mul_eqv 1)
  exact Q'.eqv_trans _
    (1 * (swapPhase r * swapPhase r)) _
    (Q'.mul_eqv_congr_right _ _ _ (swapPhase_mul_self k))
    (Q'.mul_eqv_congr_left _ _ _ (swapPhase_mul_self r))

/-- The symmetric reversal identity for an original left-associated channel. -/
theorem reverseLeft_triRight {a b c d : Nat}
    (q : FixedLeftCGChannel a b c d) (x y z : BForm) :
    BFormEqv
      (triRight c b a d (reverseLeftAsRight q).intermediate z y x)
      (scaleForm (reverseLeftPhase q)
        (triLeft a b c d q.intermediate x y z)) := by
  let p := reverseLeftPhase q
  have h := reverseRight_triLeft (reverseLeftAsRight q) z y x
  have h' : BFormEqv
      (triLeft a b c d q.intermediate x y z)
      (scaleForm p
        (triRight c b a d (reverseLeftAsRight q).intermediate z y x)) := by
    simpa only [reverseRightAsLeft_reverseLeftAsRight,
      reverseLeftAsRight_intermediate, reverseRightPhase, reverseLeftPhase, p]
      using h
  intro s
  have hp := Q'.mul_eqv_congr_left p _ _ (h' s)
  exact Q'.eqv_symm (Q'.eqv_trans _ _ _ hp
    (Q'.eqv_trans _ ((p * p) *
        triRight c b a d (reverseLeftAsRight q).intermediate z y x s) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.eqv_trans _ (1 *
          triRight c b a d (reverseLeftAsRight q).intermediate z y x s) _
        (Q'.mul_eqv_congr_right _ _ _
          (by simpa only [p, reverseLeftPhase] using
            phaseProduct_mul_self q.k q.r))
        (Q'.one_mul_eqv _))))

/-- Reversing both input maps and the external degrees leaves the exact
invariant Hilbert--Schmidt pairing unchanged. -/
theorem triMapInner_reverse (a b c d : Nat)
    (L R : BForm → BForm → BForm → BForm) :
    triMapInner c b a d (fun z y x => L x y z) (fun z y x => R x y z) ≈
      triMapInner a b c d L R := by
  let T : Nat → Nat → Nat → Nat → Q' := fun i j k s =>
    tvBinomQ a i * tvBinomQ b j * tvBinomQ c k *
      symMonomialNormSq d s *
        (L (mono i) (mono j) (mono k) s *
          R (mono i) (mono j) (mono k) s)
  unfold triMapInner
  have hterm :
      finSum (fun k => finSum (fun j => finSum (fun i => finSum (fun s =>
        tvBinomQ c k * tvBinomQ b j * tvBinomQ a i *
          symMonomialNormSq d s *
            (L (mono i) (mono j) (mono k) s *
              R (mono i) (mono j) (mono k) s)) (d + 1)) (a + 1))
        (b + 1)) (c + 1) ≈
      finSum (fun k => finSum (fun j => finSum (fun i => finSum (fun s =>
        T i j k s) (d + 1)) (a + 1)) (b + 1)) (c + 1) := by
    refine finSum_eqv_congr_lt _ _ (c + 1) (fun k hk => ?_)
    refine finSum_eqv_congr_lt _ _ (b + 1) (fun j hj => ?_)
    refine finSum_eqv_congr_lt _ _ (a + 1) (fun i hi => ?_)
    refine finSum_eqv_congr_lt _ _ (d + 1) (fun s hs => ?_)
    unfold T
    ring_qeqv
  refine Q'.eqv_trans _ _ _ hterm ?_
  have hji :
      finSum (fun k => finSum (fun j => finSum (fun i => finSum (fun s =>
          T i j k s) (d + 1)) (a + 1)) (b + 1)) (c + 1) ≈
        finSum (fun k => finSum (fun i => finSum (fun j => finSum (fun s =>
          T i j k s) (d + 1)) (b + 1)) (a + 1)) (c + 1) := by
    refine finSum_eqv_congr_lt _ _ (c + 1) (fun k hk => ?_)
    exact finSum_swap
      (fun j i => finSum (fun s => T i j k s) (d + 1)) (b + 1) (a + 1)
  refine Q'.eqv_trans _ _ _ hji ?_
  have hki := finSum_swap
    (fun k i => finSum (fun j => finSum (fun s => T i j k s) (d + 1))
      (b + 1)) (c + 1) (a + 1)
  refine Q'.eqv_trans _ _ _ hki ?_
  refine finSum_eqv_congr_lt _ _ (a + 1) (fun i hi => ?_)
  exact finSum_swap (fun k j => finSum (fun s => T i j k s) (d + 1))
    (c + 1) (b + 1)

private theorem triMapInner_scale_both (a b c d : Nat) (p : Q')
    (L R : BForm → BForm → BForm → BForm) :
    triMapInner a b c d
        (fun x y z => scaleForm p (L x y z))
        (fun x y z => scaleForm p (R x y z)) ≈
      (p * p) * triMapInner a b c d L R := by
  have hleft := triMapInner_scale_left a b c d p L
    (fun x y z => scaleForm p (R x y z))
  have hright : triMapInner a b c d L
      (fun x y z => scaleForm p (R x y z)) ≈
      p * triMapInner a b c d L R := by
    exact Q'.eqv_trans _
      (triMapInner a b c d (fun x y z => scaleForm p (R x y z)) L) _
      (triMapInner_symm a b c d _ _) 
      (Q'.eqv_trans _ (p * triMapInner a b c d R L) _
        (triMapInner_scale_left a b c d p R L)
        (Q'.mul_eqv_congr_left p _ _ (triMapInner_symm a b c d R L)))
  exact Q'.eqv_trans _ _ _ hleft
    (Q'.eqv_trans _ (p * (p * triMapInner a b c d L R)) _
      (Q'.mul_eqv_congr_left p _ _ hright)
      (Q'.eqv_symm (Q'.mul_assoc_eqv p p _)))

private theorem reverseRightPhase_mul_self {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) :
    reverseRightPhase q * reverseRightPhase q ≈ 1 := by
  exact phaseProduct_mul_self q.p q.r

private theorem reverseLeftPhase_mul_self {a b c d : Nat}
    (q : FixedLeftCGChannel a b c d) :
    reverseLeftPhase q * reverseLeftPhase q ≈ 1 := by
  exact phaseProduct_mul_self q.k q.r

/-- A right-channel Gram weight is exactly the left-channel Gram weight of
the reversed channel. -/
theorem reverseRight_leftWeight_eq_rightWeight {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) :
    triLeftChannelWeight c b a d (reverseRightAsLeft q).intermediate ≈
      triRightChannelWeight a b c d q.intermediate := by
  let R := triRight a b c d q.intermediate
  let p := reverseRightPhase q
  have hmap : TriMapEqv c b a d
      (triLeft c b a d (reverseRightAsLeft q).intermediate)
      (fun z y x => scaleForm p (R x y z)) := by
    intro k hk j hj i hi s hs
    simpa only [p, R] using reverseRight_triLeft q
      (mono i) (mono j) (mono k) s
  have hcongr := triMapInner_diagonal_congr_all_labels c b a d _ _ hmap
  have hreverse := triMapInner_reverse a b c d R R
  have hscale := triMapInner_scale_both c b a d p
    (fun z y x => R x y z) (fun z y x => R x y z)
  exact Q'.eqv_trans _ _ _ hcongr
    (Q'.eqv_trans _ _ _ hscale
      (Q'.eqv_trans _ (1 * triMapInner c b a d
          (fun z y x => R x y z) (fun z y x => R x y z)) _
        (Q'.mul_eqv_congr_right _ _ _ (reverseRightPhase_mul_self q))
        (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _)
          (by simpa only [R, triLeftChannelWeight, triRightChannelWeight]
            using hreverse))))

/-- A left-channel Gram weight is exactly the right-channel Gram weight of
the reversed channel. -/
theorem reverseLeft_rightWeight_eq_leftWeight {a b c d : Nat}
    (q : FixedLeftCGChannel a b c d) :
    triRightChannelWeight c b a d (reverseLeftAsRight q).intermediate ≈
      triLeftChannelWeight a b c d q.intermediate := by
  have h := reverseRight_leftWeight_eq_rightWeight (reverseLeftAsRight q)
  exact Q'.eqv_symm (by simpa only [reverseRightAsLeft_reverseLeftAsRight,
    reverseLeftAsRight_intermediate] using h)

end YMGap.Continuum.SU2SchurReversalSymmetry

#print axioms YMGap.Continuum.SU2SchurReversalSymmetry.reverseRightAsLeft
#print axioms YMGap.Continuum.SU2SchurReversalSymmetry.reverseLeftAsRight
#print axioms YMGap.Continuum.SU2SchurReversalSymmetry.reverseRight_triLeft
#print axioms YMGap.Continuum.SU2SchurReversalSymmetry.reverseLeft_triRight
#print axioms YMGap.Continuum.SU2SchurReversalSymmetry.triMapInner_reverse
#print axioms YMGap.Continuum.SU2SchurReversalSymmetry.reverseRight_leftWeight_eq_rightWeight
#print axioms YMGap.Continuum.SU2SchurReversalSymmetry.reverseLeft_rightWeight_eq_leftWeight
