/-
Track 11.7-fusion / R4y -- reflected parametric endpoint-ratio certificates.

`P2HalfTimeEndpointRatioCompiler` proves the closed arithmetic formula for
every coefficient in the adjacent parity-triangle slack.  This module turns
that formula into an executable reflected certificate:

  * variable `a` is the nonnegative endpoint increment `d_a` (with `d_0`
    the terminal coefficient);
  * endpoint coefficient `x_i` is the prefix `d_0+...+d_i`;
  * `endpointTriangleExpr m` is the exact ordered parity triangle at depth
    `m`;
  * `positiveEndpointSlackExpr R m` is the manifest quadratic increment sum
    with the closed threshold-count coefficients;
  * `EndpointRatioCertificate R m` asks the proved ring normaliser to check
    that this manifest sum is the scaled adjacent-depth slack.

The compiler theorem consumes that decidable certificate and nonnegative
increments, returning the cross-multiplied endpoint ratio.  Concrete depths
8, 9, and 10 are checked below; depth 10 is the first new ratio obtained
without a handwritten reflected polynomial table.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2HalfTimeEndpointRatioCompiler
import YMGap.Constructive.Soundness

namespace YMGap.Continuum.P2HalfTimeEndpointRatioCertificateCompiler

set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.P2HalfTimeEndpointRatioCompiler

/-- A right-nested finite sum in the reflected polynomial syntax. -/
def polyFsum (f : Nat -> PolyExpr) : Nat -> PolyExpr
  | 0 => .const 0
  | n + 1 => .add (polyFsum f n) (f n)

/-- Monotone endpoint coefficient `x_i=d_0+...+d_i` as reflected syntax. -/
def endpointPrefixExpr (i : Nat) : PolyExpr :=
  polyFsum PolyExpr.var (i + 1)

/-- Decidable membership in the ordered endpoint parity triangle. -/
def endpointPairActive (m i j : Nat) : Bool :=
  decide (i + j <= m ∧ (i + j + m) % 2 = 0)

/-- Exact parity-triangle quadratic form in the monotone prefix variables. -/
def endpointTriangleExpr (m : Nat) : PolyExpr :=
  polyFsum (fun i =>
    polyFsum (fun j =>
      if endpointPairActive m i j then
        .mul (endpointPrefixExpr i) (endpointPrefixExpr j)
      else .const 0) (m + 1)) (m + 1)

/-- Cross-multiplied adjacent-depth slack
`R*E_m-(R+1)*E_(m-1)`. -/
def endpointScaledSlackExpr (R m : Nat) : PolyExpr :=
  .add
    (.mul (.const (Int.ofNat R)) (endpointTriangleExpr m))
    (.neg (.mul (.const (Int.ofNat (R + 1)))
      (endpointTriangleExpr (m - 1))))

/-- Closed coefficient of the ordered increment monomial `d_a*d_b`. -/
def endpointSlackCoefficient (R m a b : Nat) : Nat :=
  R * thresholdTriangleCount m a b -
    (R + 1) * thresholdTriangleCount (m - 1) a b

/-- One manifestly nonnegative reflected slack monomial. -/
def positiveEndpointSlackTerm (R m a b : Nat) : PolyExpr :=
  .mul (.const (Int.ofNat (endpointSlackCoefficient R m a b)))
    (.mul (.var a) (.var b))

/-- Manifest quadratic increment expansion of the endpoint slack. -/
def positiveEndpointSlackExpr (R m : Nat) : PolyExpr :=
  polyFsum (fun a =>
    polyFsum (fun b => positiveEndpointSlackTerm R m a b) (m + 1))
    (m + 1)

/-- Kernel-decidable reflection certificate for one endpoint depth. -/
def EndpointRatioCertificate (R m : Nat) : Prop :=
  normalize (endpointScaledSlackExpr R m) =
    normalize (positiveEndpointSlackExpr R m)

/-- Evaluation of a reflected finite sum of nonnegative expressions is
nonnegative. -/
theorem eval_polyFsum_nonneg (rho : Nat -> Q') (f : Nat -> PolyExpr)
    (hf : forall i, (0 : Q') <= eval rho (f i)) :
    forall n, (0 : Q') <= eval rho (polyFsum f n)
  | 0 => Q'.le_refl' 0
  | n + 1 => by
      exact Q'.zero_le_add _ _ (eval_polyFsum_nonneg rho f hf n) (hf n)

private theorem ofInt_ofNat_nonneg (n : Nat) :
    (0 : Q') <= Q'.ofInt (Int.ofNat n) := by
  show (0 : Int) * (1 : Int) <= Int.ofNat n * (1 : Int)
  simp

/-- The generated positive slack evaluates nonnegatively for every
nonnegative increment environment. -/
theorem positiveEndpointSlackExpr_nonneg
    (R m : Nat) (rho : Nat -> Q') (hrho : forall i, (0 : Q') <= rho i) :
    (0 : Q') <= eval rho (positiveEndpointSlackExpr R m) := by
  apply eval_polyFsum_nonneg
  intro a
  apply eval_polyFsum_nonneg
  intro b
  exact Q'.mul_nonneg _ _
    (ofInt_ofNat_nonneg (endpointSlackCoefficient R m a b))
    (Q'.mul_nonneg _ _ (hrho a) (hrho b))

/-- Sound reflected compiler: a closed kernel certificate plus nonnegative
increments proves the scaled adjacent-depth endpoint ratio. -/
theorem endpointRatio_of_certificate
    (R m : Nat) (_hm : 0 < m) (rho : Nat -> Q')
    (hrho : forall i, (0 : Q') <= rho i)
    (certificate : EndpointRatioCertificate R m) :
    Q'.ofInt (Int.ofNat (R + 1)) * eval rho (endpointTriangleExpr (m - 1)) <=
      Q'.ofInt (Int.ofNat R) * eval rho (endpointTriangleExpr m) := by
  have heq :
      (eval rho (endpointScaledSlackExpr R m)).eqv
        (eval rho (positiveEndpointSlackExpr R m)) :=
    poly_identity_of_normal_eq _ _ certificate rho
  have hpositive := positiveEndpointSlackExpr_nonneg R m rho hrho
  have hslack : (0 : Q') <= eval rho (endpointScaledSlackExpr R m) :=
    Q'.le_trans' _ _ _ hpositive (Q'.ge_of_eqv heq)
  apply Q'.le_of_sub_nonneg
  simpa only [endpointScaledSlackExpr, eval] using hslack

/-! ## Concrete regression certificates and the first table-free depth -/

theorem endpointRatioCertificate_eight : EndpointRatioCertificate 4 8 := by
  unfold EndpointRatioCertificate
  decide

theorem endpointRatioCertificate_nine : EndpointRatioCertificate 5 9 := by
  unfold EndpointRatioCertificate
  decide

/-- First new endpoint ratio generated without spelling out its quadratic
increment slack: `6*E_9 <= 5*E_10`. -/
theorem endpointRatioCertificate_ten : EndpointRatioCertificate 5 10 := by
  unfold EndpointRatioCertificate
  decide

theorem endpointRatio_ten (rho : Nat -> Q')
    (hrho : forall i, (0 : Q') <= rho i) :
    Q'.ofNat 6 * eval rho (endpointTriangleExpr 9) <=
      Q'.ofNat 5 * eval rho (endpointTriangleExpr 10) := by
  simpa only [Q'.ofInt, Q'.ofNat] using
    endpointRatio_of_certificate 5 10 (by decide) rho hrho
      endpointRatioCertificate_ten

end YMGap.Continuum.P2HalfTimeEndpointRatioCertificateCompiler

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2HalfTimeEndpointRatioCertificateCompiler.eval_polyFsum_nonneg
#print axioms YMGap.Continuum.P2HalfTimeEndpointRatioCertificateCompiler.positiveEndpointSlackExpr_nonneg
#print axioms YMGap.Continuum.P2HalfTimeEndpointRatioCertificateCompiler.endpointRatio_of_certificate
#print axioms YMGap.Continuum.P2HalfTimeEndpointRatioCertificateCompiler.endpointRatioCertificate_ten
#print axioms YMGap.Continuum.P2HalfTimeEndpointRatioCertificateCompiler.endpointRatio_ten
