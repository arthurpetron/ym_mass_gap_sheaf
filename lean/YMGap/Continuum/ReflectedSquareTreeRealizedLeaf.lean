/-
# Exact polynomial and weight realizations of retained leaves

The output contains the actual tree path and coefficient-level polynomial
pin. Products and finite-sum insertion preserve both pins constructively.
These are certificate constructors, not an assertion that a desired
polynomial is realizable in an arbitrary tree.
-/

import YMGap.Continuum.ReflectedSquareTreeRetainedChannel

namespace YMGap.Continuum.ReflectedSquareTreeRealizedLeaf

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra
open YMGap.Continuum.ReflectedSquareTreeRetainedChannel
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

structure RealizedLeaf (t : SquareTree) (p : RatPoly) (w : Q') where
  leaf : Leaf t
  weight_pin : leaf.weight.eqv w
  channel_pin : RatPolyCoeffEqv leaf.channel p

namespace RealizedLeaf

def ofUnit {t : SquareTree} (u : UnitLeaf t) : RealizedLeaf t polyOne 1 :=
  ⟨u.leaf, u.weight_one, u.channel_one⟩

def left {s t : SquareTree} {p : RatPoly} {w : Q'} (l : RealizedLeaf s p w) : RealizedLeaf (.add s t) p w :=
  ⟨.left l.leaf, l.weight_pin, l.channel_pin⟩

def right {s t : SquareTree} {p : RatPoly} {w : Q'} (l : RealizedLeaf t p w) : RealizedLeaf (.add s t) p w :=
  ⟨.right l.leaf, l.weight_pin, l.channel_pin⟩

def scale {t : SquareTree} {p : RatPoly} {w : Q'} (a : Q') (l : RealizedLeaf t p w) :
    RealizedLeaf (t.scale a) p (a * w) where
  leaf := l.leaf.scale a
  weight_pin := by rw [Leaf.scale_weight]; exact Q'.mul_eqv_congr_left _ _ _ l.weight_pin
  channel_pin := by rw [Leaf.scale_channel]; exact l.channel_pin

def reweight {t : SquareTree} {p : RatPoly} {w v : Q'} (l : RealizedLeaf t p w) (h : w.eqv v) :
    RealizedLeaf t p v := ⟨l.leaf, Q'.eqv_trans _ _ _ l.weight_pin h, l.channel_pin⟩

def recode {t : SquareTree} {p q : RatPoly} {w : Q'} (l : RealizedLeaf t p w) (h : RatPolyCoeffEqv p q) :
    RealizedLeaf t q w := ⟨l.leaf, l.weight_pin, l.channel_pin.trans h⟩

def product {s t : SquareTree} {p q : RatPoly} {w v : Q'}
    (l : RealizedLeaf s p w) (r : RealizedLeaf t q v) : RealizedLeaf (s.product t) (polyMul p q) (w * v) where
  leaf := l.leaf.product r.leaf
  weight_pin := by
    rw [Leaf.product_weight]
    exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ l.weight_pin)
      (Q'.mul_eqv_congr_left _ _ _ r.weight_pin)
  channel_pin := by rw [Leaf.product_channel]; exact l.channel_pin.mul r.channel_pin

/-- Membership guides a decidable scan; no witness is extracted from Prop. -/
def inSum {A : Type} [DecidableEq A] (f : A → SquareTree) (a : A)
    {p : RatPoly} {w : Q'} (l : RealizedLeaf (f a) p w) :
    (xs : List A) → a ∈ xs → RealizedLeaf (SquareTree.sum f xs) p w
  | [], h => False.elim (List.not_mem_nil h)
  | b :: xs, h => if hab : a = b then by
      subst b
      exact l.left
    else (inSum f a l xs (List.mem_cons.mp h |>.resolve_left hab)).right

theorem weight_positive {t : SquareTree} {p : RatPoly} {w : Q'} (l : RealizedLeaf t p w)
    (hw : (0 : Q') < w) : (0 : Q') < l.leaf.weight :=
  Q'.pos_of_lt_of_le hw (Q'.ge_of_eqv l.weight_pin)

end RealizedLeaf

end YMGap.Continuum.ReflectedSquareTreeRealizedLeaf

#print axioms YMGap.Continuum.ReflectedSquareTreeRealizedLeaf.RealizedLeaf
#print axioms YMGap.Continuum.ReflectedSquareTreeRealizedLeaf.RealizedLeaf.ofUnit
#print axioms YMGap.Continuum.ReflectedSquareTreeRealizedLeaf.RealizedLeaf.left
#print axioms YMGap.Continuum.ReflectedSquareTreeRealizedLeaf.RealizedLeaf.right
#print axioms YMGap.Continuum.ReflectedSquareTreeRealizedLeaf.RealizedLeaf.scale
#print axioms YMGap.Continuum.ReflectedSquareTreeRealizedLeaf.RealizedLeaf.reweight
#print axioms YMGap.Continuum.ReflectedSquareTreeRealizedLeaf.RealizedLeaf.recode
#print axioms YMGap.Continuum.ReflectedSquareTreeRealizedLeaf.RealizedLeaf.product
#print axioms YMGap.Continuum.ReflectedSquareTreeRealizedLeaf.RealizedLeaf.inSum
#print axioms YMGap.Continuum.ReflectedSquareTreeRealizedLeaf.RealizedLeaf.weight_positive
