/-
# Parameter commutation on the ORIGINAL complex physical bond carrier

The actual real resolvent of the same witnessed derivative graph carries
graph inputs and outputs together.  This gives a concrete graph-preserving
map for each scaled Cayley operator, and hence reorders two rational Cayley
factors.  Nothing here calibrates their parameter as physical time or
constructs a continuous one-parameter group.
-/

import YMGap.Continuum.BF4WilsonAllNomeBondOSScaledResolventCommutation
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayley
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency
import YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyCommutation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeLinear
  (completedAdd completedNeg completedSmul completedZero)
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
  (completedAdd_assoc completedNeg_add completedZero_add completedSmul_one
    completedSmul_zero completedSmul_mul completedAdd_zero)
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion (BondCompletion)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime
  (bondValue bondValue_injective)
open YMGap.Continuum.BF4WilsonAllNomeBondOSLinear
  (bondValue_add bondValue_smul bondValue_sub bondValue_negate bondValue_realSmul)
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar
  (rationalCauchy completedRealSmul_ofQ')
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency
  (imagScale negativeImagScale imagScale_smul cneg)
open YMGap.Continuum.BF4WilsonAllNomeBondOSDerivative
  (input output)
open YMGap.Continuum.BF4WilsonAllNomeBondOSScaledResolvent
  (resolvent resolventDomain input_resolventDomain graph_sum inverse_left
    resolvent_add resolvent_sub resolvent_smul shifted)
open YMGap.Continuum.BF4WilsonAllNomeBondOSScaledResolventCommutation
  (resolvent_graph_output)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSTime (add smul)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledImaginaryShifts
  (plus minus plusDomain)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "RH" => BondCompletion hw0 hw1 (width := width)
local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "D" => BF4WilsonAllNomeComplexBondOSDerivative.Domain hw0 hw1 (width := width)
local notation "RI" => BF4WilsonAllNomeBondOSDerivative.input hw0 hw1
local notation "RO" => BF4WilsonAllNomeBondOSDerivative.output hw0 hw1
local notation "In" => BF4WilsonAllNomeComplexBondOSDerivative.input hw0 hw1
local notation "Out" => BF4WilsonAllNomeComplexBondOSDerivative.output hw0 hw1
local notation "Add" => BF4WilsonAllNomeBondOSLinear.add hw0 hw1
local notation "Sub" => BF4WilsonAllNomeBondOSLinear.sub hw0 hw1
local notation "Scale" => BF4WilsonAllNomeBondOSLinear.smul hw0 hw1
local notation "Neg" => BF4WilsonAllNomeBondOSLinear.negate hw0 hw1
local notation "V" => bondValue hw0 hw1
local notation "A" => add hw0 hw1
local notation "R" => resolvent hw0 hw1
local notation "Dom" => resolventDomain hw0 hw1
local notation "C" => BF4WilsonAllNomeComplexBondOSScaledCayley.cayley hw0 hw1
local notation "P" => plus hw0 hw1
local notation "M" => minus hw0 hw1

private theorem real_neg_neg (x : RH) : Neg (Neg x) = x := by
  apply bondValue_injective hw0 hw1
  simp only [bondValue_negate]
  change completedSmul hw0 hw1 (-1)
      (completedSmul hw0 hw1 (-1) (V x)) = V x
  rw [completedSmul_mul,
    YMGap.Continuum.BF4WilsonAllNomeLinearLaws.completedSmul_congr hw0 hw1
      (by decide : Q'.eqv ((-1 : Q') * (-1)) 1),completedSmul_one]

private theorem cneg_smul (x : H) :
    cneg hw0 hw1 x =
      smul hw0 hw1 (ofQ' (-1)) (ofQ' 0)
        (rationalCauchy (-1)) (rationalCauchy 0) x := by
  apply Prod.ext
  · apply bondValue_injective hw0 hw1
    simp only [cneg, BF4WilsonAllNomeComplexBondOSTime.smul,
      bondValue_negate,bondValue_sub,bondValue_realSmul,
      completedRealSmul_ofQ',completedSmul_zero]
    change completedNeg hw0 hw1 (V x.1) =
      completedAdd hw0 hw1 (completedNeg hw0 hw1 (V x.1))
        (completedNeg hw0 hw1 (completedZero hw0 hw1 width))
    have hzero : completedNeg hw0 hw1 (completedZero hw0 hw1 width) =
        completedZero hw0 hw1 width := by
      have h := completedNeg_add hw0 hw1 (completedZero hw0 hw1 width)
      rw [completedAdd_zero] at h
      exact h
    rw [hzero,completedAdd_zero]
  · apply bondValue_injective hw0 hw1
    simp only [cneg, BF4WilsonAllNomeComplexBondOSTime.smul,
      bondValue_negate,bondValue_add,bondValue_realSmul,
      completedRealSmul_ofQ',completedSmul_zero]
    exact (completedZero_add hw0 hw1 _).symm

private theorem cayley_cneg (t : Q') (ht : (0 : Q') < t) (x : H) :
    C t ht (cneg hw0 hw1 x) = cneg hw0 hw1 (C t ht x) := by
  rw [cneg_smul,cneg_smul]
  exact BF4WilsonAllNomeComplexBondOSScaledCayley.cayley_smul hw0 hw1 t ht
    (ofQ' (-1)) (ofQ' 0) (rationalCauchy (-1)) (rationalCauchy 0) x

private theorem negativeImag_cneg (s : Q') (x : H) :
    negativeImagScale hw0 hw1 s x = cneg hw0 hw1 (imagScale hw0 hw1 s x) := by
  apply Prod.ext
  · change Scale s x.2 = Neg (Neg (Scale s x.2))
    exact (real_neg_neg hw0 hw1 _).symm
  · rfl

private theorem cayley_imagScale (s t : Q') (ht : (0 : Q') < t) (x : H) :
    C t ht (imagScale hw0 hw1 s x) =
      imagScale hw0 hw1 s (C t ht x) := by
  rw [imagScale_smul,imagScale_smul]
  exact BF4WilsonAllNomeComplexBondOSScaledCayley.cayley_smul hw0 hw1 t ht
    (ofQ' 0) (ofQ' s) (rationalCauchy 0) (rationalCauchy s) x

private theorem cayley_negativeImagScale (s t : Q') (ht : (0 : Q') < t) (x : H) :
    C t ht (negativeImagScale hw0 hw1 s x) =
      negativeImagScale hw0 hw1 s (C t ht x) := by
  rw [negativeImag_cneg,negativeImag_cneg,cayley_cneg,cayley_imagScale]

/-- Apply the already constructed real resolvent to BOTH original physical
components, not to an ambient coefficient surrogate. -/
def pairResolvent (s : Q') (hs : (0 : Q') < s) (x : H) : H :=
  (R s hs x.1, R s hs x.2)

/-- The actual graph image is represented by two existing resolvent-domain
points.  Its output pin follows from the real original-graph theorem. -/
def graphImage (s : Q') (hs : (0 : Q') < s) (d : D) : D :=
  (Dom s hs (RI d.1), Dom s hs (RI d.2))

theorem graphImage_input (s : Q') (hs : (0 : Q') < s) (d : D) :
    In (graphImage hw0 hw1 s hs d) = pairResolvent hw0 hw1 s hs (In d) := rfl

theorem graphImage_output (s : Q') (hs : (0 : Q') < s) (d : D) :
    Out (graphImage hw0 hw1 s hs d) = pairResolvent hw0 hw1 s hs (Out d) :=
  Prod.ext (resolvent_graph_output hw0 hw1 s hs d.1)
    (resolvent_graph_output hw0 hw1 s hs d.2)

private theorem pair_plus_image (s t : Q') (hs : (0 : Q') < s) (d : D) :
    pairResolvent hw0 hw1 s hs (P t d) =
      P t (graphImage hw0 hw1 s hs d) := by
  rw [BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency.plus_input_imag
    hw0 hw1 t (graphImage hw0 hw1 s hs d), graphImage_input, graphImage_output]
  apply Prod.ext
  · change R s hs (Sub (RI d.1) (Scale t (RO d.2))) =
      Sub (R s hs (RI d.1)) (Scale t (R s hs (RO d.2)))
    rw [resolvent_sub,resolvent_smul]
  · change R s hs (Add (RI d.2) (Scale t (RO d.1))) =
      Add (R s hs (RI d.2)) (Scale t (R s hs (RO d.1)))
    rw [resolvent_add,resolvent_smul]

private theorem pair_minus_image (s t : Q') (hs : (0 : Q') < s) (d : D) :
    pairResolvent hw0 hw1 s hs (M t d) =
      M t (graphImage hw0 hw1 s hs d) := by
  rw [BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency.minus_input_imag
    hw0 hw1 t (graphImage hw0 hw1 s hs d), graphImage_input, graphImage_output]
  apply Prod.ext
  · change R s hs (Add (RI d.1) (Scale t (RO d.2))) =
      Add (R s hs (RI d.1)) (Scale t (R s hs (RO d.2)))
    rw [resolvent_add,resolvent_smul]
  · change R s hs (Sub (RI d.2) (Scale t (RO d.1))) =
      Sub (R s hs (RI d.2)) (Scale t (R s hs (RO d.1)))
    rw [resolvent_sub,resolvent_smul]

/-- A scaled Cayley map commutes with EVERY rational positive resolvent of
its same derivative graph.  This is proved by transporting the constructed
plus/minus graph preimage, not by an unproved operator calculus. -/
theorem cayley_pairResolvent_commute (s t : Q')
    (hs : (0 : Q') < s) (ht : (0 : Q') < t) (x : H) :
    C t ht (pairResolvent hw0 hw1 s hs x) =
      pairResolvent hw0 hw1 s hs (C t ht x) := by
  let d := plusDomain hw0 hw1 t ht x
  have hp : P t d = x :=
    BF4WilsonAllNomeComplexBondOSScaledImaginaryShifts.plus_right hw0 hw1 t ht x
  calc
    C t ht (pairResolvent hw0 hw1 s hs x) =
        C t ht (pairResolvent hw0 hw1 s hs (P t d)) := by rw [hp]
    _ = C t ht (P t (graphImage hw0 hw1 s hs d)) := by
      rw [pair_plus_image]
    _ = M t (graphImage hw0 hw1 s hs d) := by
      unfold BF4WilsonAllNomeComplexBondOSScaledCayley.cayley
      rw [BF4WilsonAllNomeComplexBondOSScaledCayley.plus_left]
    _ = pairResolvent hw0 hw1 s hs (M t d) :=
      (pair_minus_image hw0 hw1 s t hs d).symm
    _ = pairResolvent hw0 hw1 s hs (C t ht x) := rfl

private theorem real_scale_one (x : RH) : Scale (1 : Q') x = x := by
  apply bondValue_injective hw0 hw1
  rw [bondValue_smul,completedSmul_one]

private def onePos : (0 : Q') < 1 := by decide

private def unitShift (d : D) : H :=
  (shifted hw0 hw1 1 d.1,shifted hw0 hw1 1 d.2)

private def unitDomain (x : H) : D :=
  (Dom 1 (onePos) x.1,Dom 1 (onePos) x.2)

private theorem unitShift_add (d : D) : unitShift hw0 hw1 d = A (In d) (Out d) := by
  apply Prod.ext
  · change Add (RI d.1) (Scale 1 (RO d.1)) = Add (RI d.1) (RO d.1)
    rw [real_scale_one]
  · change Add (RI d.2) (Scale 1 (RO d.2)) = Add (RI d.2) (RO d.2)
    rw [real_scale_one]

private theorem unitDomain_input (x : H) :
    In (unitDomain hw0 hw1 x) = pairResolvent hw0 hw1 1 (onePos) x := rfl

private theorem unitDomain_graph_sum (x : H) :
    A (In (unitDomain hw0 hw1 x)) (Out (unitDomain hw0 hw1 x)) = x := by
  apply Prod.ext
  · change Add (R 1 (onePos) x.1) (RO (Dom 1 (onePos) x.1)) = x.1
    have h := graph_sum hw0 hw1 1 (onePos) x.1
    rw [real_scale_one] at h
    exact h
  · change Add (R 1 (onePos) x.2) (RO (Dom 1 (onePos) x.2)) = x.2
    have h := graph_sum hw0 hw1 1 (onePos) x.2
    rw [real_scale_one] at h
    exact h

private theorem unitShift_resolvent (d : D) :
    pairResolvent hw0 hw1 1 (onePos) (unitShift hw0 hw1 d) = In d := by
  apply Prod.ext
  · have h := congrArg RI (inverse_left hw0 hw1 1 (onePos) d.1)
    rw [input_resolventDomain] at h
    exact h
  · have h := congrArg RI (inverse_left hw0 hw1 1 (onePos) d.2)
    rw [input_resolventDomain] at h
    exact h

/-- The concrete graph witness for the Cayley image uses only the ORIGINAL
unit resolvent and the already constructed original domain quotients. -/
def graphMap (t : Q') (ht : (0 : Q') < t) (d : D) : D :=
  unitDomain hw0 hw1 (C t ht (unitShift hw0 hw1 d))

theorem graphMap_input (t : Q') (ht : (0 : Q') < t) (d : D) :
    In (graphMap hw0 hw1 t ht d) = C t ht (In d) := by
  calc
    In (graphMap hw0 hw1 t ht d) =
        pairResolvent hw0 hw1 1 (onePos)
          (C t ht (unitShift hw0 hw1 d)) := unitDomain_input hw0 hw1 _
    _ = C t ht (pairResolvent hw0 hw1 1 (onePos) (unitShift hw0 hw1 d)) :=
      (cayley_pairResolvent_commute hw0 hw1 1 t (onePos) ht _).symm
    _ = C t ht (In d) := by rw [unitShift_resolvent]

private theorem real_add_left_cancel (a b c : RH) (h : Add a b = Add a c) : b = c := by
  apply bondValue_injective hw0 hw1
  have hv := congrArg V h
  simp only [bondValue_add] at hv
  have hc := congrArg (completedAdd hw0 hw1 (completedNeg hw0 hw1 (V a))) hv
  have hb : completedAdd hw0 hw1 (completedNeg hw0 hw1 (V a))
      (completedAdd hw0 hw1 (V a) (V b)) = V b := by
    rw [← completedAdd_assoc,completedNeg_add,completedZero_add]
  have hc' : completedAdd hw0 hw1 (completedNeg hw0 hw1 (V a))
      (completedAdd hw0 hw1 (V a) (V c)) = V c := by
    rw [← completedAdd_assoc,completedNeg_add,completedZero_add]
  rw [hb,hc'] at hc
  exact hc

private theorem pair_add_left_cancel (a b c : H) (h : A a b = A a c) : b = c :=
  Prod.ext
    (real_add_left_cancel hw0 hw1 a.1 b.1 c.1 (congrArg Prod.fst h))
    (real_add_left_cancel hw0 hw1 a.2 b.2 c.2 (congrArg Prod.snd h))

/-- BOTH completed graph components of the actual Cayley image, without
assuming that an arbitrary output already lies in the domain. -/
theorem graphMap_output (t : Q') (ht : (0 : Q') < t) (d : D) :
    Out (graphMap hw0 hw1 t ht d) = C t ht (Out d) := by
  let q := graphMap hw0 hw1 t ht d
  have hgraph : A (In q) (Out q) = C t ht (unitShift hw0 hw1 d) :=
    unitDomain_graph_sum hw0 hw1 _
  have hlin : C t ht (unitShift hw0 hw1 d) =
      A (C t ht (In d)) (C t ht (Out d)) := by
    rw [unitShift_add]
    exact BF4WilsonAllNomeComplexBondOSScaledCayley.cayley_add hw0 hw1 t ht _ _
  have h : A (C t ht (In d)) (Out q) =
      A (C t ht (In d)) (C t ht (Out d)) := by
    have hh := hgraph.trans hlin
    change A (In (graphMap hw0 hw1 t ht d)) (Out q) =
      A (C t ht (In d)) (C t ht (Out d)) at hh
    rw [graphMap_input hw0 hw1 t ht d] at hh
    exact hh
  exact pair_add_left_cancel hw0 hw1 _ _ _ h

/-- The original plus shift of a graph point is preserved under an arbitrary
scaled Cayley map.  The graph witness is constructed, not postulated. -/
theorem cayley_graph_plus (s t : Q') (ht : (0 : Q') < t) (d : D) :
    C t ht (P s d) = P s (graphMap hw0 hw1 t ht d) := by
  change C t ht (A (In d) (imagScale hw0 hw1 s (Out d))) =
    A (In (graphMap hw0 hw1 t ht d))
      (imagScale hw0 hw1 s (Out (graphMap hw0 hw1 t ht d)))
  rw [BF4WilsonAllNomeComplexBondOSScaledCayley.cayley_add,
    cayley_imagScale,graphMap_input,graphMap_output]

/-- The opposite original graph shift is preserved by the same concrete
witness, with the signed imaginary term retained. -/
theorem cayley_graph_minus (s t : Q') (ht : (0 : Q') < t) (d : D) :
    C t ht (M s d) = M s (graphMap hw0 hw1 t ht d) := by
  change C t ht (A (In d) (negativeImagScale hw0 hw1 s (Out d))) =
    A (In (graphMap hw0 hw1 t ht d))
      (negativeImagScale hw0 hw1 s (Out (graphMap hw0 hw1 t ht d)))
  rw [BF4WilsonAllNomeComplexBondOSScaledCayley.cayley_add,
    cayley_negativeImagScale,graphMap_input,graphMap_output]

/-- Cayley maps at any two positive rational parameters commute on the
ACTUAL complex physical bond completion.  This is a same-graph reordering
law, not a time-group or logarithm identification. -/
theorem cayley_commute (s t : Q') (hs : (0 : Q') < s)
    (ht : (0 : Q') < t) (x : H) :
    C t ht (C s hs x) = C s hs (C t ht x) := by
  let d := plusDomain hw0 hw1 s hs x
  let q := graphMap hw0 hw1 t ht d
  have hp : P s d = x :=
    BF4WilsonAllNomeComplexBondOSScaledImaginaryShifts.plus_right hw0 hw1 s hs x
  calc
    C t ht (C s hs x) = C t ht (M s d) := rfl
    _ = M s q := cayley_graph_minus hw0 hw1 s t ht d
    _ = C s hs (P s q) := by
      unfold BF4WilsonAllNomeComplexBondOSScaledCayley.cayley
      rw [BF4WilsonAllNomeComplexBondOSScaledCayley.plus_left]
    _ = C s hs (C t ht (P s d)) :=
      congrArg (C s hs) (cayley_graph_plus hw0 hw1 s t ht d).symm
    _ = C s hs (C t ht x) := by rw [hp]

#print axioms pairResolvent
#print axioms graphImage
#print axioms graphImage_input
#print axioms graphImage_output
#print axioms cayley_pairResolvent_commute
#print axioms graphMap
#print axioms graphMap_input
#print axioms graphMap_output
#print axioms cayley_graph_plus
#print axioms cayley_graph_minus
#print axioms cayley_commute

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyCommutation
