/-
# Rational subgap inverse on the completed physical bond vacuum complement

The supplied physical bond rows retain their original time-range witnesses.
Dependent quotient recursion uses the orthogonality proposition without
selecting a representative of the physical bond class.  All statements are at
fixed nome and width, in the original dimensionless lattice-time units.
-/

import YMGap.Continuum.BF4WilsonAllNomeBondOSResolvent
import YMGap.Continuum.BF4WilsonAllNomeSectorSubgapResolvent

namespace YMGap.Continuum.BF4WilsonAllNomeBondOSSubgapResolvent

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
  (completedInner unitState)
open YMGap.Continuum.BF4WilsonAllNomeSectorDerivative
  (DomainPoint domainSetoid)
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion
  (BondCompletion Rows rowSetoid toSectorRep close_iff_limit_eq bondCompletedInner)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime
  (bondValue bondValue_injective bondValue_inner vacuum bondValue_ofSource)
open YMGap.Continuum.BF4WilsonAllNomeBondOSRealization (image_unit)
open YMGap.Continuum.BF4WilsonAllNomeBondOSDerivative
  (Domain input bondValue_input_mk input_injective)
open YMGap.Continuum.BF4WilsonAllNomeBondOSResolvent
  (shifted bondValue_shifted_mk)
open YMGap.Continuum.BF4WilsonAllNomeSectorVacuumInverse
  (Centered val)
open YMGap.Continuum.BF4WilsonAllNomeLogCoreGap
  (coreMargin coreMargin_positive)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => BondCompletion hw0 hw1 (width := width)
local notation "D" => Domain hw0 hw1 (width := width)
local notation "P" => DomainPoint hw0 hw1 (width := width)
local notation "B" => completedInner hw0 hw1
local notation "U" => unitState hw0 hw1 width
local notation "delta" => coreMargin hw0 hw1 width
local notation "Class" => Quotient.mk (domainSetoid hw0 hw1 (width := width))
local notation "RClass" => Quotient.mk (rowSetoid hw0 hw1 (width := width))

/-- The ordinary vacuum-orthogonal subtype of the completed physical bond
carrier; this is not a smaller represented-source subspace. -/
def CenteredBond : Type :=
  {x : H // bondCompletedInner hw0 hw1
    (vacuum hw0 hw1 (width := width)) x = RCzero}

private theorem vacuum_value :
    bondValue hw0 hw1 (vacuum hw0 hw1 (width := width)) = U := by
  rw [vacuum, bondValue_ofSource, image_unit]

private def rowCentered (X : Rows hw0 hw1 (width := width))
    (hx : bondCompletedInner hw0 hw1
      (vacuum hw0 hw1 (width := width)) (RClass X) = RCzero) :
    Centered hw0 hw1 (width := width) where
  state := toSectorRep hw0 hw1 X
  orthogonal := by
    rw [bondValue_inner, vacuum_value] at hx
    exact hx

private def rowDomain (a : Q') (ha0 : (0 : Q') ≤ a) (ha : a < delta)
    (X : Rows hw0 hw1 (width := width))
    (hx : bondCompletedInner hw0 hw1
      (vacuum hw0 hw1 (width := width)) (RClass X) = RCzero) : D :=
  Class (BF4WilsonAllNomeSectorSubgapResolvent.domainPoint hw0 hw1
    a ha0 ha (rowCentered hw0 hw1 X hx))

private theorem rowDomain_congr (a : Q') (ha0 : (0 : Q') ≤ a) (ha : a < delta)
    (X Y : Rows hw0 hw1 (width := width))
    (hx : bondCompletedInner hw0 hw1
      (vacuum hw0 hw1 (width := width)) (RClass X) = RCzero)
    (hy : bondCompletedInner hw0 hw1
      (vacuum hw0 hw1 (width := width)) (RClass Y) = RCzero)
    (hxy : (rowSetoid hw0 hw1 (width := width)).r X Y) :
    rowDomain hw0 hw1 a ha0 ha X hx = rowDomain hw0 hw1 a ha0 ha Y hy := by
  apply Quotient.sound
  apply BF4WilsonAllNomeSectorSubgapInjective.input_injective hw0 hw1 a ha
    _ _
    (BF4WilsonAllNomeSectorSubgapResolvent.input_orthogonal hw0 hw1 a ha0 ha _)
    (BF4WilsonAllNomeSectorSubgapResolvent.input_orthogonal hw0 hw1 a ha0 ha _)
  rw [BF4WilsonAllNomeSectorSubgapResolvent.inverse_right,
    BF4WilsonAllNomeSectorSubgapResolvent.inverse_right]
  exact (close_iff_limit_eq hw0 hw1 X Y).mp hxy

/-- The dependent codomain consumes a Prop proof of orthogonality while the
quotient recursor retains the Type-valued source-row witness. -/
private theorem prop_functions_heq {pProp qProp : Prop} (hpq : pProp = qProp)
    (f : pProp → D) (g : qProp → D)
    (h : ∀ (hp : pProp) (hq : qProp), f hp = g hq) : HEq f g := by
  cases hpq
  apply heq_of_eq
  funext hp
  exact h hp hp

private def domainFunction (a : Q') (ha0 : (0 : Q') ≤ a) (ha : a < delta)
    (x : H) :
    (bondCompletedInner hw0 hw1 (vacuum hw0 hw1 (width := width)) x = RCzero) → D :=
  Quotient.hrecOn x
    (fun X hx => rowDomain hw0 hw1 a ha0 ha X hx)
    (fun X Y hxy => by
      have hq : RClass X = RClass Y := Quotient.sound hxy
      apply prop_functions_heq hw0 hw1
        (congrArg (fun z : H =>
          bondCompletedInner hw0 hw1
            (vacuum hw0 hw1 (width := width)) z = RCzero) hq)
      intro hx hy
      exact rowDomain_congr hw0 hw1 a ha0 ha X Y hx hy hxy)

/-- A witnessed original derivative-domain point for every orthogonal
completed physical bond class. -/
def resolventDomain (a : Q') (ha0 : (0 : Q') ≤ a) (ha : a < delta)
    (x : CenteredBond hw0 hw1 (width := width)) : D :=
  domainFunction hw0 hw1 a ha0 ha x.val x.property

private theorem resolventDomain_mk (a : Q') (ha0 : (0 : Q') ≤ a)
    (ha : a < delta) (X : Rows hw0 hw1 (width := width))
    (hx : bondCompletedInner hw0 hw1
      (vacuum hw0 hw1 (width := width)) (RClass X) = RCzero) :
    resolventDomain hw0 hw1 a ha0 ha ⟨RClass X, hx⟩ =
      rowDomain hw0 hw1 a ha0 ha X hx := rfl

def resolvent (a : Q') (ha0 : (0 : Q') ≤ a) (ha : a < delta)
    (x : CenteredBond hw0 hw1 (width := width)) : H :=
  input hw0 hw1 (resolventDomain hw0 hw1 a ha0 ha x)

theorem input_orthogonal (a : Q') (ha0 : (0 : Q') ≤ a) (ha : a < delta)
    (x : CenteredBond hw0 hw1 (width := width)) :
    bondCompletedInner hw0 hw1 (vacuum hw0 hw1 (width := width))
      (resolvent hw0 hw1 a ha0 ha x) = RCzero := by
  obtain ⟨x, hx⟩ := x
  revert hx
  refine Quotient.inductionOn x ?_
  intro X hx
  unfold resolvent
  rw [resolventDomain_mk, bondValue_inner, vacuum_value]
  unfold rowDomain
  rw [bondValue_input_mk]
  exact BF4WilsonAllNomeSectorSubgapResolvent.input_orthogonal hw0 hw1
    a ha0 ha _

/-- The negative shifted graph reaches every centered physical bond class. -/
theorem inverse_right (a : Q') (ha0 : (0 : Q') ≤ a) (ha : a < delta)
    (x : CenteredBond hw0 hw1 (width := width)) :
    shifted hw0 hw1 (-a) (resolventDomain hw0 hw1 a ha0 ha x) = x.val := by
  apply bondValue_injective hw0 hw1
  obtain ⟨x, hx⟩ := x
  revert hx
  refine Quotient.inductionOn x ?_
  intro X hx
  rw [resolventDomain_mk]
  unfold rowDomain
  rw [bondValue_shifted_mk]
  exact BF4WilsonAllNomeSectorSubgapResolvent.inverse_right hw0 hw1
    a ha0 ha (rowCentered hw0 hw1 X hx)

/-- Every original centered derivative-domain input has a centered shifted
physical bond value. -/
def shiftedCentered (a : Q') (p : D)
    (hp : bondCompletedInner hw0 hw1
      (vacuum hw0 hw1 (width := width)) (input hw0 hw1 p) = RCzero) :
    CenteredBond hw0 hw1 (width := width) where
  val := shifted hw0 hw1 (-a) p
  property := by
    revert hp
    refine Quotient.inductionOn p ?_
    intro q hp
    rw [bondValue_inner, vacuum_value, bondValue_shifted_mk]
    have hq : B U q.input.val = RCzero := by
      rw [bondValue_inner, vacuum_value, bondValue_input_mk] at hp
      exact hp
    exact (BF4WilsonAllNomeSectorSubgapResolvent.shiftedCentered hw0 hw1
      a q hq).orthogonal

private theorem shifted_injective (a : Q') (ha : a < delta)
    (p q : D)
    (hp : bondCompletedInner hw0 hw1
      (vacuum hw0 hw1 (width := width)) (input hw0 hw1 p) = RCzero)
    (hq : bondCompletedInner hw0 hw1
      (vacuum hw0 hw1 (width := width)) (input hw0 hw1 q) = RCzero)
    (h : shifted hw0 hw1 (-a) p = shifted hw0 hw1 (-a) q) : p = q := by
  apply input_injective hw0 hw1
  apply bondValue_injective hw0 hw1
  revert hp hq h
  refine Quotient.inductionOn₂ p q ?_
  intro s t hp hq h
  rw [bondValue_inner, vacuum_value, bondValue_input_mk] at hp hq
  rw [bondValue_input_mk, bondValue_input_mk]
  apply BF4WilsonAllNomeSectorSubgapInjective.input_injective hw0 hw1 a ha
    s t hp hq
  have hs := congrArg (bondValue hw0 hw1) h
  rw [bondValue_shifted_mk, bondValue_shifted_mk] at hs
  exact hs

/-- The same constructed inverse is a left inverse on every centered
physical derivative-domain point. -/
theorem inverse_left (a : Q') (ha0 : (0 : Q') ≤ a) (ha : a < delta)
    (p : D)
    (hp : bondCompletedInner hw0 hw1
      (vacuum hw0 hw1 (width := width)) (input hw0 hw1 p) = RCzero) :
    resolventDomain hw0 hw1 a ha0 ha
      (shiftedCentered hw0 hw1 a p hp) = p := by
  apply shifted_injective hw0 hw1 a ha _ p
    (input_orthogonal hw0 hw1 a ha0 ha _) hp
  exact inverse_right hw0 hw1 a ha0 ha
    (shiftedCentered hw0 hw1 a p hp)

/-- Sharp fixed-nome, fixed-width squared-norm cap on the physical bond
vacuum complement. -/
theorem norm_bound (a : Q') (ha0 : (0 : Q') ≤ a) (ha : a < delta)
    (x : CenteredBond hw0 hw1 (width := width)) :
    let d := delta - a
    let r := Q'.recipPos d (ClusteringImpliesGap.sub_pos_of_lt ha)
    RCle (bondCompletedInner hw0 hw1
      (resolvent hw0 hw1 a ha0 ha x) (resolvent hw0 hw1 a ha0 ha x))
      (RCscale (r*r) (bondCompletedInner hw0 hw1 x.val x.val)) := by
  obtain ⟨x, hx⟩ := x
  revert hx
  refine Quotient.inductionOn x ?_
  intro X hx
  unfold resolvent
  rw [resolventDomain_mk]
  rw [bondValue_inner, bondValue_inner]
  unfold rowDomain
  rw [bondValue_input_mk]
  exact BF4WilsonAllNomeSectorSubgapResolvent.norm_bound hw0 hw1
    a ha0 ha (rowCentered hw0 hw1 X hx)

#print axioms CenteredBond
#print axioms resolventDomain
#print axioms resolvent
#print axioms input_orthogonal
#print axioms inverse_right
#print axioms shiftedCentered
#print axioms inverse_left
#print axioms norm_bound

end YMGap.Continuum.BF4WilsonAllNomeBondOSSubgapResolvent
