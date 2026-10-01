/-
# Distinct positive-rational resolvents of the SAME original physical graph

The construction acts on the existing fixed-nome, fixed-width physical bond
completion.  The graph-commutation proof uses only the two actual inverse laws
and rational linearity of the witnessed derivative domain; in particular it
does not divide by the parameter difference or assume an invariant domain.

This is an algebraic reordering input for future scaled-Cayley products, not
a physical-time group, Hamiltonian calibration, or continuum statement.
-/

import YMGap.Continuum.BF4WilsonAllNomeBondOSScaledResolvent

namespace YMGap.Continuum.BF4WilsonAllNomeBondOSScaledResolventCommutation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4WilsonAllNomeLinear
  (completedAdd completedNeg completedSmul)
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
  (completedAdd_assoc completedNeg_add completedZero_add completedSmul_mul
    completedSmul_congr completedSmul_one)
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion (BondCompletion)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime
  (bondValue bondValue_injective)
open YMGap.Continuum.BF4WilsonAllNomeBondOSLinear
  (bondValue_add bondValue_smul)
open YMGap.Continuum.BF4WilsonAllNomeBondOSDerivative
  (Domain input output)
open YMGap.Continuum.BF4WilsonAllNomeBondOSScaledResolvent
  (resolvent resolventDomain input_resolventDomain graph_sum shifted inverse_left
    resolvent_add resolvent_smul reciprocal time_reciprocal)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => BondCompletion hw0 hw1 (width := width)
local notation "D" => Domain hw0 hw1 (width := width)
local notation "V" => bondValue hw0 hw1
local notation "Add" => BF4WilsonAllNomeBondOSLinear.add hw0 hw1
local notation "Scale" => BF4WilsonAllNomeBondOSLinear.smul hw0 hw1
local notation "In" => input hw0 hw1
local notation "Out" => output hw0 hw1
local notation "R" => resolvent hw0 hw1
local notation "Dom" => resolventDomain hw0 hw1

private theorem add_left_cancel (a b c : H)
    (h : Add a b = Add a c) : b = c := by
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

private theorem scale_injective (s : Q') (hs : (0 : Q') < s)
    (a b : H) (h : Scale s a = Scale s b) : a = b := by
  apply bondValue_injective hw0 hw1
  have hv := congrArg V h
  simp only [bondValue_smul] at hv
  have hc := congrArg (completedSmul hw0 hw1 (reciprocal s hs)) hv
  rw [completedSmul_mul,completedSmul_mul] at hc
  have hrec : ((reciprocal s hs)*s).eqv 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (reciprocal s hs) s)
      (time_reciprocal s hs)
  rw [completedSmul_congr hw0 hw1 hrec,
    completedSmul_congr hw0 hw1 hrec,
    completedSmul_one,completedSmul_one] at hc
  exact hc

/-- An actual graph point `(u,v)` is carried by the original resolvent to
the actual graph point `(R_s u,R_s v)`.  The latter point is the already
constructed `resolventDomain_s u`; no new domain witness is assumed. -/
theorem resolvent_graph_output (s : Q') (hs : (0 : Q') < s) (d : D) :
    Out (Dom s hs (In d)) = R s hs (Out d) := by
  let u := In d
  let v := Out d
  have hleft : Add (R s hs u) (Scale s (R s hs v)) = u := by
    calc
      Add (R s hs u) (Scale s (R s hs v)) =
          R s hs (Add u (Scale s v)) := by
            rw [resolvent_add,resolvent_smul]
      _ = R s hs (shifted hw0 hw1 s d) := rfl
      _ = u := by
        have h := congrArg In (inverse_left hw0 hw1 s hs d)
        rw [input_resolventDomain] at h
        exact h
  have hright := graph_sum hw0 hw1 s hs u
  have hc : Scale s (Out (Dom s hs u)) = Scale s (R s hs v) :=
    add_left_cancel hw0 hw1 (R s hs u) _ _ (hright.trans hleft.symm)
  exact scale_injective hw0 hw1 s hs _ _ hc

/-- Resolvents of the SAME original derivative graph commute for every pair
of positive rational parameters, including equal ones.  No `s-t` division
or external functional calculus enters the construction. -/
theorem resolvent_commute (s t : Q')
    (hs : (0 : Q') < s) (ht : (0 : Q') < t) (x : H) :
    R s hs (R t ht x) = R t ht (R s hs x) := by
  let d := Dom t ht x
  let q := Dom s hs (R t ht x)
  have hq : Out q = R s hs (Out d) := by
    change Out (Dom s hs (In d)) = R s hs (Out d)
    exact resolvent_graph_output hw0 hw1 s hs d
  have hshift : shifted hw0 hw1 t q = R s hs x := by
    calc
      shifted hw0 hw1 t q =
          Add (R s hs (R t ht x)) (Scale t (R s hs (Out d))) := by
            change Add (In q) (Scale t (Out q)) = _
            rw [hq,input_resolventDomain]
      _ = R s hs (Add (R t ht x) (Scale t (Out d))) := by
            rw [resolvent_add,resolvent_smul]
      _ = R s hs x := by rw [graph_sum hw0 hw1 t ht x]
  have hdom : Dom t ht (R s hs x) = q := by
    rw [← hshift,inverse_left]
  calc
    R s hs (R t ht x) = In q := rfl
    _ = In (Dom t ht (R s hs x)) := by rw [hdom]
    _ = R t ht (R s hs x) := rfl

#print axioms resolvent_graph_output
#print axioms resolvent_commute

end YMGap.Continuum.BF4WilsonAllNomeBondOSScaledResolventCommutation
