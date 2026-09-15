/-
# Exact all-spin channel paths under a change of physical link coordinates

The shape and weights of the original representation Gram tree depend on
spin, column and tensor row, not on the quaternion polynomial inserted in
that representation. Structural recursion transports EVERY original leaf
to the same branch at another quaternion, preserving its exact weight.
It also transports any supplied relation between the actual column entries
to the selected polynomial. No leaf is chosen from erased existence.

This changes the coordinate polynomial in the SAME representation formula;
it does not assert that two different link polynomials are equal, or that
their interacting Haar amplitudes agree. Geometric pullback and growing-
volume amplitude/normalization estimates remain separate obligations.
-/

import YMGap.Continuum.BF4ExactSlabAllSpinRetainedChannels

namespace YMGap.Continuum.BF4ExactSlabGramChannelTransport

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RationalQuaternionRatPoly
open YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra
open YMGap.Continuum.ReflectedSquareTreeRetainedChannel
open YMGap.Continuum.BF4ExactSlabAllSpinRetainedChannels
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionPolynomialTensorHermitian
open YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomialBasis
open YMGap.Continuum.SU2QuaternionSymmetricPowerKernelGram

/-- Type-level matching paths, retaining each rational weight literally. -/
inductive SameWeights : SquareTree → SquareTree → Type where
  | zero : SameWeights .zero .zero
  | term (w : Q') (p q : RatPoly) : SameWeights (.term w p) (.term w q)
  | add {s s' t t' : SquareTree} : SameWeights s s' → SameWeights t t' →
      SameWeights (.add s t) (.add s' t')

namespace SameWeights

def mapLeaf : {s t : SquareTree} → SameWeights s t → Leaf s → Leaf t
  | _, _, .term w _ q, .here _ _ => .here w q
  | _, _, .add h _, .left l => .left (h.mapLeaf l)
  | _, _, .add _ h, .right l => .right (h.mapLeaf l)

theorem mapLeaf_weight : {s t : SquareTree} → (h : SameWeights s t) → (l : Leaf s) →
    (h.mapLeaf l).weight = l.weight
  | _, _, .term _ _ _, .here _ _ => rfl
  | _, _, .add h _, .left l => h.mapLeaf_weight l
  | _, _, .add _ h, .right l => h.mapLeaf_weight l

def scale (a : Q') : {s t : SquareTree} → SameWeights s t → SameWeights (s.scale a) (t.scale a)
  | _, _, .zero => .zero
  | _, _, .term w p q => .term (a*w) p q
  | _, _, .add h k => .add (h.scale a) (k.scale a)

def prefixTransport (f g : Nat → SquareTree) (h : ∀ i, SameWeights (f i) (g i)) :
    (n : Nat) → SameWeights (SquareTree.prefixSum f n) (SquareTree.prefixSum g n)
  | 0 => .zero
  | n+1 => .add (prefixTransport f g h n) (h n)

/-- A relation on the original source and target leaf polynomials. -/
def Relates (R : RatPoly → RatPoly → Prop) :
    {s t : SquareTree} → SameWeights s t → Prop
  | _, _, .zero => True
  | _, _, .term _ p q => R p q
  | _, _, .add h k => Relates R h ∧ Relates R k

theorem mapLeaf_relates (R : RatPoly → RatPoly → Prop) :
    {s t : SquareTree} → (h : SameWeights s t) → h.Relates R → (l : Leaf s) →
      R l.channel (h.mapLeaf l).channel
  | _, _, .term _ _ _, h, .here _ _ => h
  | _, _, .add h _, hR, .left l => h.mapLeaf_relates R hR.1 l
  | _, _, .add _ h, hR, .right l => h.mapLeaf_relates R hR.2 l

theorem scale_relates (R : RatPoly → RatPoly → Prop) (a : Q') :
    {s t : SquareTree} → (h : SameWeights s t) → h.Relates R → (h.scale a).Relates R
  | _, _, .zero, _ => True.intro
  | _, _, .term _ _ _, h => h
  | _, _, .add h k, hR => ⟨h.scale_relates R a hR.1, k.scale_relates R a hR.2⟩

theorem prefix_relates (R : RatPoly → RatPoly → Prop) (f g : Nat → SquareTree)
    (h : ∀ i, SameWeights (f i) (g i)) (hR : ∀ i, (h i).Relates R) :
    ∀ n, (prefixTransport f g h n).Relates R
  | 0 => True.intro
  | n+1 => ⟨prefix_relates R f g h hR n, hR n⟩

end SameWeights

def tensorTransport : (n : Nat) → (x y : PolyTensor n) →
    SameWeights (tensorSquares n x) (tensorSquares n y)
  | 0, x, y => .add (.term 1 x.1 y.1) (.term 1 x.2 y.2)
  | n+1, x, y => .add (tensorTransport n (x false) (y false)) (tensorTransport n (x true) (y true))

def TensorRelates (R : RatPoly → RatPoly → Prop) : (n : Nat) → PolyTensor n → PolyTensor n → Prop
  | 0, x, y => R x.1 y.1 ∧ R x.2 y.2
  | n+1, x, y => ∀ b, TensorRelates R n (x b) (y b)

theorem tensorTransport_relates (R : RatPoly → RatPoly → Prop) :
    ∀ n (x y : PolyTensor n), TensorRelates R n x y → (tensorTransport n x y).Relates R
  | 0, _, _, h => h
  | n+1, x, y, h => ⟨tensorTransport_relates R n (x false) (y false) (h false),
      tensorTransport_relates R n (x true) (y true) (h true)⟩

/-- Every spin, including all tensor rows and both real/imaginary components. -/
def gramTransport (q r : RatPolyQuaternion) (spin : Nat) : SameWeights (gramSquares q spin) (gramSquares r spin) :=
  SameWeights.prefixTransport _ _ (fun k =>
    (tensorTransport spin (polynomialColumn q spin k) (polynomialColumn r spin k)).scale (basisInverseWeight spin k)) (spin+1)

theorem gramTransport_relates (R : RatPoly → RatPoly → Prop) (q r : RatPolyQuaternion) (spin : Nat)
    (h : ∀ k, TensorRelates R spin (polynomialColumn q spin k) (polynomialColumn r spin k)) :
    (gramTransport q r spin).Relates R :=
  SameWeights.prefix_relates R _ _ _ (fun k => SameWeights.scale_relates R _ _
    (tensorTransport_relates R spin _ _ (h k))) (spin+1)

def transport (q r : RatPolyQuaternion) (c : GramChannel q) : GramChannel r :=
  ⟨c.spin, (gramTransport q r c.spin).mapLeaf c.leaf⟩

theorem transport_spin (q r : RatPolyQuaternion) (c : GramChannel q) : (transport q r c).spin = c.spin := rfl

theorem transport_weight (q r : RatPolyQuaternion) (c : GramChannel q) :
    (transport q r c).leaf.weight = c.leaf.weight :=
  (gramTransport q r c.spin).mapLeaf_weight c.leaf

theorem transport_channel (R : RatPoly → RatPoly → Prop) (q r : RatPolyQuaternion) (c : GramChannel q)
    (h : ∀ k, TensorRelates R c.spin (polynomialColumn q c.spin k) (polynomialColumn r c.spin k)) :
    R c.leaf.channel (transport q r c).leaf.channel :=
  (gramTransport q r c.spin).mapLeaf_relates R (gramTransport_relates R q r c.spin h) c.leaf

end YMGap.Continuum.BF4ExactSlabGramChannelTransport

#print axioms YMGap.Continuum.BF4ExactSlabGramChannelTransport.SameWeights
#print axioms YMGap.Continuum.BF4ExactSlabGramChannelTransport.SameWeights.mapLeaf
#print axioms YMGap.Continuum.BF4ExactSlabGramChannelTransport.SameWeights.mapLeaf_weight
#print axioms YMGap.Continuum.BF4ExactSlabGramChannelTransport.SameWeights.scale
#print axioms YMGap.Continuum.BF4ExactSlabGramChannelTransport.SameWeights.prefixTransport
#print axioms YMGap.Continuum.BF4ExactSlabGramChannelTransport.SameWeights.Relates
#print axioms YMGap.Continuum.BF4ExactSlabGramChannelTransport.SameWeights.mapLeaf_relates
#print axioms YMGap.Continuum.BF4ExactSlabGramChannelTransport.SameWeights.scale_relates
#print axioms YMGap.Continuum.BF4ExactSlabGramChannelTransport.SameWeights.prefix_relates
#print axioms YMGap.Continuum.BF4ExactSlabGramChannelTransport.tensorTransport
#print axioms YMGap.Continuum.BF4ExactSlabGramChannelTransport.TensorRelates
#print axioms YMGap.Continuum.BF4ExactSlabGramChannelTransport.tensorTransport_relates
#print axioms YMGap.Continuum.BF4ExactSlabGramChannelTransport.gramTransport
#print axioms YMGap.Continuum.BF4ExactSlabGramChannelTransport.gramTransport_relates
#print axioms YMGap.Continuum.BF4ExactSlabGramChannelTransport.transport
#print axioms YMGap.Continuum.BF4ExactSlabGramChannelTransport.transport_spin
#print axioms YMGap.Continuum.BF4ExactSlabGramChannelTransport.transport_weight
#print axioms YMGap.Continuum.BF4ExactSlabGramChannelTransport.transport_channel
