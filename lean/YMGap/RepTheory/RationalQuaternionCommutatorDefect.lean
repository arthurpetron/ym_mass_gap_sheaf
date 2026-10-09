/-
# Exact nonabelian commutator trace residual

The two rotated orders have opposite quadratic trace terms at a noncentral
base. Actual stereographic UnitNorm factors and a four-link plaquette word
are retained. These are exact rational identities and a computed sign
fixture, not derivative, smoothness, Hessian, or retention estimates.

There is no cross-link Hessian consumer here. In particular this leaf does
not identify its word with an original BF4 RatPoly observable or integrate
it against the original action; that carrier/action pin remains separate.
-/

import YMGap.RepTheory.RationalQuaternionSphereNets

namespace YMGap.RepTheory.RationalQuaternionCommutatorDefect

set_option autoImplicit false

open YMGap.Constructive
open YMGap.RepTheory.RationalQuaternion
open YMGap.RepTheory.RationalQuaternionSphereNets
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv
private abbrev PE := PolyExpr
local instance : Add PE := ⟨.add⟩
local instance : Mul PE := ⟨.mul⟩
local instance : Neg PE := ⟨.neg⟩
local instance (n : Nat) : OfNat PE n := ⟨.const (Int.ofNat n)⟩

private theorem ac {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a+c ≈ b+d :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right a b c h) (Q'.add_eqv_congr_left b c d k)

private theorem mc {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

def axisI (c s : Q') : RationalQuaternion := ⟨c,s,0,0⟩
def axisJ (c s : Q') : RationalQuaternion := ⟨c,0,s,0⟩
def axisK (c s : Q') : RationalQuaternion := ⟨c,0,0,s⟩
def trace2 (a : RationalQuaternion) : Q' := 2*a.r

def rawCommutator (a b : RationalQuaternion) : RationalQuaternion :=
  mul (mul (mul a b) (conj a)) (conj b)

/-- False is i,j; true is j,i. -/
def axisCommutator (swapped : Bool) (c s : Q') : RationalQuaternion :=
  if swapped then rawCommutator (axisJ c s) (axisI c s)
  else rawCommutator (axisI c s) (axisJ c s)

private structure QE where
  r : PE
  i : PE
  j : PE
  k : PE

private def qm (x y : QE) : QE :=
  ⟨(x.r*y.r + -(x.i*y.i)) + (-(x.j*y.j) + -(x.k*y.k)),
   (x.r*y.i+x.i*y.r)+(x.j*y.k + -(x.k*y.j)),
   (x.r*y.j + -(x.i*y.k))+(x.j*y.r+x.k*y.i),
   (x.r*y.k+x.i*y.j)+(-(x.j*y.i)+x.k*y.r)⟩
private def qc (x : QE) : QE := ⟨x.r,-x.i,-x.j,-x.k⟩
private def qi : QE := ⟨.var 0,.var 1,0,0⟩
private def qj : QE := ⟨.var 0,0,.var 1,0⟩
private def qcomm (swapped : Bool) : QE :=
  if swapped then qm (qm (qm qj qi) (qc qj)) (qc qi)
  else qm (qm (qm qi qj) (qc qi)) (qc qj)
private def qclosed (swapped : Bool) : QE :=
  let c : PE := .var 0
  let s : PE := .var 1
  ⟨(c*c+s*s)*(c*c+s*s) + -(2*s*s*s*s),
    if swapped then -(2*c*s*s*s) else 2*c*s*s*s,
    if swapped then 2*c*s*s*s else -(2*c*s*s*s),
    if swapped then -(2*c*c*s*s) else 2*c*c*s*s⟩
private def qe (rho : Nat → Q') (x : QE) : RationalQuaternion :=
  ⟨eval rho x.r,eval rho x.i,eval rho x.j,eval rho x.k⟩

private theorem qcomm_normal (swapped : Bool) :
    normalize (qcomm swapped).r = normalize (qclosed swapped).r ∧
    normalize (qcomm swapped).i = normalize (qclosed swapped).i ∧
    normalize (qcomm swapped).j = normalize (qclosed swapped).j ∧
    normalize (qcomm swapped).k = normalize (qclosed swapped).k := by
  cases swapped <;> decide

/-- Symbolic raw Hamilton identity, without unit-radius assumptions. -/
theorem axisCommutator_closed (swapped : Bool) (c s : Q') :
    (axisCommutator swapped c s).Equivalent
      ⟨(c*c+s*s)*(c*c+s*s) + -(2*s*s*s*s),
       if swapped then -(2*c*s*s*s) else 2*c*s*s*s,
       if swapped then 2*c*s*s*s else -(2*c*s*s*s),
       if swapped then -(2*c*c*s*s) else 2*c*c*s*s⟩ := by
  let rho : Nat → Q' := fun | 0 => c | _ => s
  have h := qcomm_normal swapped
  have he : (qe rho (qcomm swapped)).Equivalent (qe rho (qclosed swapped)) :=
    ⟨poly_identity_of_normal_eq _ _ h.1 rho,
     poly_identity_of_normal_eq _ _ h.2.1 rho,
     poly_identity_of_normal_eq _ _ h.2.2.1 rho,
     poly_identity_of_normal_eq _ _ h.2.2.2 rho⟩
  cases swapped <;> exact he

private def defectExpr (swapped : Bool) (c s p0 p3 : PE) : PE :=
  -(4*p0*s*s*s*s) + (if swapped then 4*p3*c*c*s*s else -(4*p3*c*c*s*s))
def defectFormula (swapped : Bool) (c s p0 p3 : Q') : Q' :=
  -(4*p0*s*s*s*s) + (if swapped then 4*p3*c*c*s*s else -(4*p3*c*c*s*s))

private theorem trace_normal (swapped : Bool) :
    normalize (2*(qm (qclosed swapped) ⟨.var 2,0,0,.var 3⟩).r + -(2*(.var 2))) =
      normalize (2*(.var 2)*(((.var 0)*(.var 0)+(.var 1)*(.var 1))*
        ((.var 0)*(.var 0)+(.var 1)*(.var 1)) + -1) +
        defectExpr swapped (.var 0) (.var 1) (.var 2) (.var 3)) := by
  cases swapped <;> decide

/-- The nonunit formula retains the explicit radius defect. -/
theorem trace_defect_raw (swapped : Bool) (c s p0 p3 : Q') :
    trace2 (mul (axisCommutator swapped c s) (axisK p0 p3)) + -(2*p0) ≈
      2*p0*((c*c+s*s)*(c*c+s*s) + -1) + defectFormula swapped c s p0 p3 := by
  have h := mul_congr (axisCommutator_closed swapped c s)
    (semanticSetoid.iseqv.refl (axisK p0 p3))
  refine Q'.eqv_trans _ _ _ (ac (mc (Q'.eqv_refl 2) h.1) (Q'.eqv_refl _)) ?_
  have he := poly_identity_of_normal_eq _ _ (trace_normal swapped)
    (fun | 0 => c | 1 => s | 2 => p0 | _ => p3)
  cases swapped <;> exact he

/-- The useful residual at unit radius; the rotated order changes its sign. -/
theorem trace_defect_unit (swapped : Bool) (c s p0 p3 : Q') (hu : c*c+s*s ≈ 1) :
    trace2 (mul (axisCommutator swapped c s) (axisK p0 p3)) + -(2*p0) ≈
      defectFormula swapped c s p0 p3 := by
  have hs : (c*c+s*s)*(c*c+s*s) ≈ 1 :=
    Q'.eqv_trans _ _ _ (mc hu hu) (by decide)
  have hz : (c*c+s*s)*(c*c+s*s) + -1 ≈ 0 :=
    Q'.eqv_trans _ _ _ (ac hs (Q'.eqv_refl (-1))) (by decide)
  exact Q'.eqv_trans _ _ _ (trace_defect_raw swapped c s p0 p3)
    (Q'.eqv_trans _ _ _ (ac (Q'.eqv_trans _ _ _ (mc (Q'.eqv_refl _) hz)
      (QPoly.q_mul_zero _)) (Q'.eqv_refl _)) (QPoly.q_zero_add_eqv _))

def denominator1 (t : Q') : Q' := 1+t*t
theorem denominator1_positive (t : Q') : (0 : Q') < denominator1 t :=
  Q'.pos_add_nonneg (by decide) (SumOfSquares.q_mul_self_nonneg t)
def reciprocal1 (t : Q') : Q' := Q'.recipPos (denominator1 t) (denominator1_positive t)
def cosine (t : Q') : Q' := reciprocal1 t*(1 + -(t*t))
def sine (t : Q') : Q' := reciprocal1 t*(2*t)

def rotationI (t : Q') : UnitNorm := stereographic ⟨t,0,0⟩
def rotationJ (t : Q') : UnitNorm := stereographic ⟨0,t,0⟩
def basePoint (q : Q') : UnitNorm := stereographic ⟨0,0,q⟩

private theorem norm3_i (t : Q') : norm3 ⟨t,0,0⟩ = t*t := by
  simp only [norm3, show (0 : Q')*0=0 from rfl, Q'.add_zero']
private theorem norm3_j (t : Q') : norm3 ⟨0,t,0⟩ = t*t := by
  simp only [norm3, show (0 : Q')*0=0 from rfl, Q'.add_zero', Q'.zero_add']
private theorem norm3_k (t : Q') : norm3 ⟨0,0,t⟩ = t*t := by
  simp only [norm3, show (0 : Q')*0=0 from rfl, Q'.zero_add']

private theorem reciprocal_transport {a b : Q'} (ha : (0 : Q') < a)
    (hb : (0 : Q') < b) (h : a=b) : Q'.recipPos a ha = Q'.recipPos b hb := by
  cases h
  rfl

theorem rotationI_shape (t : Q') : (rotationI t).val.Equivalent (axisI (cosine t) (sine t)) := by
  have hd : denominator ⟨t,0,0⟩ = denominator1 t := congrArg (fun z => 1+z) (norm3_i t)
  have hr : Q'.recipPos (denominator ⟨t,0,0⟩) (denominator_positive _) = reciprocal1 t :=
    reciprocal_transport (denominator_positive _) (denominator1_positive t) hd
  change (Q'.recipPos (denominator ⟨t,0,0⟩) (denominator_positive _) *(1 + -norm3 ⟨t,0,0⟩) ≈ cosine t) ∧
    (Q'.recipPos (denominator ⟨t,0,0⟩) (denominator_positive _) *(2*t) ≈ sine t) ∧
    (Q'.recipPos (denominator ⟨t,0,0⟩) (denominator_positive _) *(2*0) ≈ 0) ∧
    (Q'.recipPos (denominator ⟨t,0,0⟩) (denominator_positive _) *(2*0) ≈ 0)
  rw [hr, norm3_i]
  exact ⟨Q'.eqv_refl _,Q'.eqv_refl _,QPoly.q_mul_zero _,QPoly.q_mul_zero _⟩

theorem rotationJ_shape (t : Q') : (rotationJ t).val.Equivalent (axisJ (cosine t) (sine t)) := by
  have hd : denominator ⟨0,t,0⟩ = denominator1 t := congrArg (fun z => 1+z) (norm3_j t)
  have hr : Q'.recipPos (denominator ⟨0,t,0⟩) (denominator_positive _) = reciprocal1 t :=
    reciprocal_transport (denominator_positive _) (denominator1_positive t) hd
  change (Q'.recipPos (denominator ⟨0,t,0⟩) (denominator_positive _) *(1 + -norm3 ⟨0,t,0⟩) ≈ cosine t) ∧
    (Q'.recipPos (denominator ⟨0,t,0⟩) (denominator_positive _) *(2*0) ≈ 0) ∧
    (Q'.recipPos (denominator ⟨0,t,0⟩) (denominator_positive _) *(2*t) ≈ sine t) ∧
    (Q'.recipPos (denominator ⟨0,t,0⟩) (denominator_positive _) *(2*0) ≈ 0)
  rw [hr, norm3_j]
  exact ⟨Q'.eqv_refl _,QPoly.q_mul_zero _,Q'.eqv_refl _,QPoly.q_mul_zero _⟩

theorem basePoint_shape (q : Q') : (basePoint q).val.Equivalent (axisK (cosine q) (sine q)) := by
  have hd : denominator ⟨0,0,q⟩ = denominator1 q := congrArg (fun z => 1+z) (norm3_k q)
  have hr : Q'.recipPos (denominator ⟨0,0,q⟩) (denominator_positive _) = reciprocal1 q :=
    reciprocal_transport (denominator_positive _) (denominator1_positive q) hd
  change (Q'.recipPos (denominator ⟨0,0,q⟩) (denominator_positive _) *(1 + -norm3 ⟨0,0,q⟩) ≈ cosine q) ∧
    (Q'.recipPos (denominator ⟨0,0,q⟩) (denominator_positive _) *(2*0) ≈ 0) ∧
    (Q'.recipPos (denominator ⟨0,0,q⟩) (denominator_positive _) *(2*0) ≈ 0) ∧
    (Q'.recipPos (denominator ⟨0,0,q⟩) (denominator_positive _) *(2*q) ≈ sine q)
  rw [hr, norm3_k]
  exact ⟨Q'.eqv_refl _,QPoly.q_mul_zero _,QPoly.q_mul_zero _,Q'.eqv_refl _⟩

theorem cosine_sine_unit (t : Q') : cosine t*cosine t+sine t*sine t ≈ 1 := by
  have h := Q'.eqv_trans _ _ _ (Q'.eqv_symm (normSq_congr (rotationI_shape t))) (rotationI t).unitNorm
  simpa only [axisI, normSq, show (0 : Q')*0=0 from rfl, Q'.add_zero'] using h

def unitCommutator (a b : UnitNorm) : UnitNorm :=
  UnitNorm.mul (UnitNorm.mul (UnitNorm.mul a b) (UnitNorm.conj a)) (UnitNorm.conj b)
def plaquetteWord (u0 u1 u2 u3 : UnitNorm) : UnitNorm :=
  UnitNorm.mul (UnitNorm.mul (UnitNorm.mul u0 u1) (UnitNorm.conj u2)) (UnitNorm.conj u3)

/-- Four genuine unit links, with the base factor in the fourth link. -/
theorem plaquetteWord_pin (a b P : UnitNorm) :
    (plaquetteWord a b a (UnitNorm.mul (UnitNorm.conj P) b)).Equivalent
      (UnitNorm.mul (unitCommutator a b) P) := by
  have hr := UnitNorm.semanticSetoid.iseqv.refl
  have hc := UnitNorm.semanticSetoid.iseqv.trans (UnitNorm.conj_mul (UnitNorm.conj P) b)
    (UnitNorm.mul_congr (hr _) (UnitNorm.conj_conj P))
  exact UnitNorm.semanticSetoid.iseqv.trans (UnitNorm.mul_congr (hr _) hc)
    (UnitNorm.semanticSetoid.iseqv.symm (UnitNorm.mul_assoc _ _ _))

private theorem rawCommutator_congr {a a' b b' : RationalQuaternion}
    (ha : a.Equivalent a') (hb : b.Equivalent b') :
    (rawCommutator a b).Equivalent (rawCommutator a' b') :=
  mul_congr (mul_congr (mul_congr ha hb) (conj_congr ha)) (conj_congr hb)

def rotatedCommutator (swapped : Bool) (t : Q') : UnitNorm :=
  if swapped then unitCommutator (rotationJ t) (rotationI t)
  else unitCommutator (rotationI t) (rotationJ t)

def rotatedPlaquette (swapped : Bool) (t q : Q') : UnitNorm :=
  if swapped then plaquetteWord (rotationJ t) (rotationI t) (rotationJ t)
    (UnitNorm.mul (UnitNorm.conj (basePoint q)) (rotationI t))
  else plaquetteWord (rotationI t) (rotationJ t) (rotationI t)
    (UnitNorm.mul (UnitNorm.conj (basePoint q)) (rotationJ t))

theorem rotatedPlaquette_pin (swapped : Bool) (t q : Q') :
    (rotatedPlaquette swapped t q).Equivalent
      (UnitNorm.mul (rotatedCommutator swapped t) (basePoint q)) := by
  cases swapped <;> exact plaquetteWord_pin _ _ _

def actualDefect (swapped : Bool) (t q : Q') : Q' :=
  trace2 (UnitNorm.mul (rotatedCommutator swapped t) (basePoint q)).val +
    -trace2 (basePoint q).val

theorem actualDefect_formula (swapped : Bool) (t q : Q') :
    actualDefect swapped t q ≈ defectFormula swapped (cosine t) (sine t) (cosine q) (sine q) := by
  have hk : (rotatedCommutator swapped t).val.Equivalent (axisCommutator swapped (cosine t) (sine t)) := by
    cases swapped
    · exact rawCommutator_congr (rotationI_shape t) (rotationJ_shape t)
    · exact rawCommutator_congr (rotationJ_shape t) (rotationI_shape t)
  have hp := mul_congr hk (basePoint_shape q)
  exact Q'.eqv_trans _ _ _ (ac (mc (Q'.eqv_refl 2) hp.1)
    (Q'.neg_eqv_congr _ _ (mc (Q'.eqv_refl 2) (basePoint_shape q).1)))
    (trace_defect_unit swapped _ _ _ _ (cosine_sine_unit t))

def fourth (a : Q') : Q' := (a*a)*(a*a)
def clearedNumerator (swapped : Bool) (t p0 p3 : Q') : Q' :=
  -(64*p0*t*t*t*t) + (if swapped then 16*p3*t*t*(1 + -(t*t))*(1 + -(t*t))
    else -(16*p3*t*t*(1 + -(t*t))*(1 + -(t*t))))
private def fourthExpr (a : PE) : PE := (a*a)*(a*a)
private def numeratorExpr (swapped : Bool) (t p0 p3 : PE) : PE :=
  -(64*p0*t*t*t*t) + (if swapped then 16*p3*t*t*(1 + -(t*t))*(1 + -(t*t))
    else -(16*p3*t*t*(1 + -(t*t))*(1 + -(t*t))))

private theorem clearing_normal (swapped : Bool) :
    normalize (fourthExpr (.var 2)*defectExpr swapped ((.var 1)*(1 + -((.var 0)*(.var 0))))
      ((.var 1)*(2*(.var 0))) (.var 3) (.var 4)) =
    normalize (fourthExpr ((.var 2)*(.var 1))*numeratorExpr swapped (.var 0) (.var 3) (.var 4)) := by
  cases swapped <;> decide

/-- Exact cleared rational t identity on the actual stereographic unit words. -/
theorem actualDefect_cleared (swapped : Bool) (t q : Q') :
    fourth (denominator1 t)*actualDefect swapped t q ≈
      clearedNumerator swapped t (cosine q) (sine q) := by
  have h := Q'.mul_recipPos_eqv (denominator1 t) (denominator1_positive t)
  have hs : (denominator1 t*reciprocal1 t)*(denominator1 t*reciprocal1 t) ≈ 1 :=
    Q'.eqv_trans _ _ _ (mc h h) (by decide)
  have hf : fourth (denominator1 t*reciprocal1 t) ≈ 1 :=
    Q'.eqv_trans _ _ _ (mc hs hs) (by decide)
  refine Q'.eqv_trans _ _ _ (mc (Q'.eqv_refl _) (actualDefect_formula swapped t q)) ?_
  have he := poly_identity_of_normal_eq _ _ (clearing_normal swapped)
    (fun | 0 => t | 1 => reciprocal1 t | 2 => denominator1 t | 3 => cosine q | _ => sine q)
  have hc : fourth (denominator1 t)*defectFormula swapped (cosine t) (sine t) (cosine q) (sine q) ≈
      fourth (denominator1 t*reciprocal1 t)*clearedNumerator swapped t (cosine q) (sine q) := by
    cases swapped <;> exact he
  exact Q'.eqv_trans _ _ _ hc (Q'.eqv_trans _ _ _ (mc hf (Q'.eqv_refl _)) (Q'.one_mul_eqv _))

def tenth : Q' := Q'.mkPos 1 10 (by decide)
/-- Same noncentral base and rotation size: opposite nonzero trace signs. -/
theorem tenth_opposite_signs : actualDefect false tenth tenth < 0 ∧ 0 < actualDefect true tenth tenth := by
  decide

end YMGap.RepTheory.RationalQuaternionCommutatorDefect

#print axioms YMGap.RepTheory.RationalQuaternionCommutatorDefect.axisCommutator_closed
#print axioms YMGap.RepTheory.RationalQuaternionCommutatorDefect.trace_defect_raw
#print axioms YMGap.RepTheory.RationalQuaternionCommutatorDefect.trace_defect_unit
#print axioms YMGap.RepTheory.RationalQuaternionCommutatorDefect.denominator1_positive
#print axioms YMGap.RepTheory.RationalQuaternionCommutatorDefect.rotationI_shape
#print axioms YMGap.RepTheory.RationalQuaternionCommutatorDefect.rotationJ_shape
#print axioms YMGap.RepTheory.RationalQuaternionCommutatorDefect.basePoint_shape
#print axioms YMGap.RepTheory.RationalQuaternionCommutatorDefect.cosine_sine_unit
#print axioms YMGap.RepTheory.RationalQuaternionCommutatorDefect.plaquetteWord_pin
#print axioms YMGap.RepTheory.RationalQuaternionCommutatorDefect.rotatedPlaquette_pin
#print axioms YMGap.RepTheory.RationalQuaternionCommutatorDefect.actualDefect_formula
#print axioms YMGap.RepTheory.RationalQuaternionCommutatorDefect.actualDefect_cleared
#print axioms YMGap.RepTheory.RationalQuaternionCommutatorDefect.tenth_opposite_signs
