/-
# Partial retention of an actual reflected-square forest

Pruning is explicit Type-valued path data. It can keep a whole subtree,
discard branches, and combine those operations. Products preserve pruning,
so selecting local channels does not require selecting a single channel
in every other factor. All spectator subtrees may remain intact.

For nonnegative original weights, pruning lowers the original Haar-square
sum, also after multiplication by any signed polynomial. There is no
independence assumption, new positivity premise or strictly positive floor.
-/

import YMGap.Continuum.ReflectedSquareTreeRetainedChannel

namespace YMGap.Continuum.ReflectedSquareTreePruning

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra
open YMGap.Continuum.BF4ExactSlabAllCutoffReflectionPositivity
open YMGap.Continuum.ReflectedSquareTreeRetainedChannel
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

inductive Pruning : SquareTree → SquareTree → Type where
  | keep (t : SquareTree) : Pruning t t
  | discard (t : SquareTree) : Pruning .zero t
  | left {s t u : SquareTree} : Pruning s t → Pruning s (.add t u)
  | right {s t u : SquareTree} : Pruning s u → Pruning s (.add t u)
  | add {a b s t : SquareTree} : Pruning a s → Pruning b t → Pruning (.add a b) (.add s t)
  | trans {r s t : SquareTree} : Pruning r s → Pruning s t → Pruning r t

namespace Pruning

def ofLeaf : {t : SquareTree} → (l : Leaf t) → Pruning (.term l.weight l.channel) t
  | _, .here w p => .keep (.term w p)
  | _, .left l => .left (ofLeaf l)
  | _, .right l => .right (ofLeaf l)

theorem nonnegative : {s t : SquareTree} → Pruning s t → t.Nonnegative → s.Nonnegative
  | _, _, .keep _, h => h
  | _, _, .discard _, _ => True.intro
  | _, _, .left p, h => nonnegative p h.1
  | _, _, .right p, h => nonnegative p h.2
  | _, _, .add p q, h => ⟨nonnegative p h.1, nonnegative q h.2⟩
  | _, _, .trans p q, h => nonnegative p (nonnegative q h)

def multiplyTerm (a : Q') (p : RatPoly) : {s t : SquareTree} → Pruning s t →
    Pruning (s.multiplyTerm a p) (t.multiplyTerm a p)
  | _, _, .keep t => .keep (t.multiplyTerm a p)
  | _, _, .discard t => .discard (t.multiplyTerm a p)
  | _, _, .left h => .left (multiplyTerm a p h)
  | _, _, .right h => .right (multiplyTerm a p h)
  | _, _, .add h k => .add (multiplyTerm a p h) (multiplyTerm a p k)
  | _, _, .trans h k => .trans (multiplyTerm a p h) (multiplyTerm a p k)

/-- All channels of the supplied left spectator tree are retained. -/
def productRight (s : SquareTree) {a b : SquareTree} (h : Pruning a b) :
    Pruning (s.product a) (s.product b) :=
  match s with
  | .zero => .keep .zero
  | .term w p => h.multiplyTerm w p
  | .add s t => .add (productRight s h) (productRight t h)

/-- All channels of the supplied right spectator tree are retained. -/
def productLeft {a b : SquareTree} (h : Pruning a b) (t : SquareTree) :
    Pruning (a.product t) (b.product t) :=
  match h with
  | .keep s => .keep (s.product t)
  | .discard s => .discard (s.product t)
  | .left h => .left (productLeft h t)
  | .right h => .right (productLeft h t)
  | .add h k => .add (productLeft h t) (productLeft k t)
  | .trans h k => .trans (productLeft h t) (productLeft k t)

def product {a b s t : SquareTree} (h : Pruning a b) (k : Pruning s t) :
    Pruning (a.product s) (b.product t) :=
  (h.productLeft s).trans (productRight b k)

theorem haarSquareSum_le (blocks : Nat) : {s t : SquareTree} → Pruning s t → t.Nonnegative →
    haarSquareSum blocks s ≤ haarSquareSum blocks t
  | _, _, .keep _, _ => Q'.le_refl' _
  | _, _, .discard t, h => haarSquareSum_nonnegative blocks t h
  | _, .add _ t, .left p, h => Q'.le_trans' _ _ _ (haarSquareSum_le blocks p h.1)
      (Q'.add_le_self_of_nonneg _ _ (haarSquareSum_nonnegative blocks t h.2))
  | _, .add s _, .right p, h => Q'.le_trans' _ _ _ (haarSquareSum_le blocks p h.2)
      (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ (haarSquareSum_nonnegative blocks s h.1))
        (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))
  | _, _, .add p q, h => Q'.add_le_add (haarSquareSum_le blocks p h.1) (haarSquareSum_le blocks q h.2)
  | _, _, .trans p q, h => Q'.le_trans' _ _ _ (haarSquareSum_le blocks p (q.nonnegative h))
      (haarSquareSum_le blocks q h)

/-- Arbitrary shared-variable signed insertions survive the partial retention. -/
theorem dressed_value_le {s t : SquareTree} (h : Pruning s t) (ht : t.Nonnegative)
    (blocks : Nat) (p : RatPoly) :
    haarSquareSum blocks (s.multiplyTerm 1 p) ≤ haarSquareSum blocks (t.multiplyTerm 1 p) :=
  (h.multiplyTerm 1 p).haarSquareSum_le blocks
    (SquareTree.multiplyTerm_nonnegative 1 p Q'.zero_le_one t ht)

end Pruning

end YMGap.Continuum.ReflectedSquareTreePruning

#print axioms YMGap.Continuum.ReflectedSquareTreePruning.Pruning
#print axioms YMGap.Continuum.ReflectedSquareTreePruning.Pruning.ofLeaf
#print axioms YMGap.Continuum.ReflectedSquareTreePruning.Pruning.nonnegative
#print axioms YMGap.Continuum.ReflectedSquareTreePruning.Pruning.multiplyTerm
#print axioms YMGap.Continuum.ReflectedSquareTreePruning.Pruning.productRight
#print axioms YMGap.Continuum.ReflectedSquareTreePruning.Pruning.productLeft
#print axioms YMGap.Continuum.ReflectedSquareTreePruning.Pruning.product
#print axioms YMGap.Continuum.ReflectedSquareTreePruning.Pruning.haarSquareSum_le
#print axioms YMGap.Continuum.ReflectedSquareTreePruning.Pruning.dressed_value_le
