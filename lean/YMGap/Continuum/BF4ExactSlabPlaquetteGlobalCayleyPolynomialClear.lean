/-
# Global division-free Cayley polynomial clearing

The common-denominator Cayley numerator can be written without a reciprocal:
for a common scale denominator `D` and a triple `a`, use the raw quaternion

  (D^2 - |a|^2, 2 D a).

The product of four such raw quaternions satisfies the exact cleared Cayley
identity for every rational `D` and every four triples.  No positivity,
inverse chart or sign sector occurs in this algebraic core.  Subsequent
consumers can therefore attach actual unit links through their polynomial
unit-norm equations, including the south-pole chart boundary.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteSignedCayleyPolynomialClear

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyPolynomialClear

set_option autoImplicit false
set_option maxRecDepth 10000

open YMGap.Constructive
open YMGap.RepTheory
open YMGap.RepTheory.RationalQuaternion
open YMGap.RepTheory.RationalQuaternionSphereNets
open YMGap.RepTheory.RationalQuaternionCommutatorDefect (plaquetteWord)
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactSlabPlaquetteCayleyExpansion
open YMGap.Continuum.BF4ExactSlabPlaquetteCayleyCommonDenominator
open YMGap.Continuum.BF4ExactSlabPlaquetteSignedCayleyPolynomialClear
open YMGap.Continuum.BF4ExactSlabPlaquetteDeficit
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.QuaternionHaarFiniteProductOrder (environment)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress

local infix:50 " ≈ " => Q'.eqv

/-- Division-free raw quaternion at common denominator `D`. -/
def commonRaw (D : Q') (a : Triple) : RationalQuaternion :=
  ⟨pow2 D + -norm3 a, 2 * D * a.x, 2 * D * a.y, 2 * D * a.z⟩

/-- Left-associated product of four division-free raw quaternions. -/
def commonRawWord (D : Q') (a b c d : Triple) : RationalQuaternion :=
  RationalQuaternion.mul
    (RationalQuaternion.mul
      (RationalQuaternion.mul (commonRaw D a) (commonRaw D b))
      (commonRaw D c))
    (commonRaw D d)

private abbrev PE := PolyExpr

local instance : Add PE := ⟨.add⟩
local instance : Mul PE := ⟨.mul⟩
local instance : Neg PE := ⟨.neg⟩
local instance (n : Nat) : OfNat PE n := ⟨.const (Int.ofNat n)⟩

private structure VE where
  x : PE
  y : PE
  z : PE

private structure QE where
  r : PE
  i : PE
  j : PE
  k : PE

private def ev (offset : Nat) : VE :=
  ⟨.var offset, .var (offset + 1), .var (offset + 2)⟩

private def eadd3 (a b : VE) : VE :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

private def edot3 (a b : VE) : PE :=
  (a.x * b.x + a.y * b.y) + a.z * b.z

private def enorm3 (a : VE) : PE := edot3 a a

private def ecross3 (a b : VE) : VE :=
  ⟨a.y * b.z + -(a.z * b.y),
    a.z * b.x + -(a.x * b.z),
    a.x * b.y + -(a.y * b.x)⟩

private def edet3 (a b c : VE) : PE := edot3 (ecross3 a b) c

private def eqmul (a b : QE) : QE :=
  ⟨(a.r * b.r + -(a.i * b.i)) + (-(a.j * b.j) + -(a.k * b.k)),
    (a.r * b.i + a.i * b.r) + (a.j * b.k + -(a.k * b.j)),
    (a.r * b.j + -(a.i * b.k)) + (a.j * b.r + a.k * b.i),
    (a.r * b.k + a.i * b.j) + (-(a.j * b.i) + a.k * b.r)⟩

private def epow2 (D : PE) : PE := D * D
private def epow3 (D : PE) : PE := epow2 D * D
private def epow4 (D : PE) : PE := epow2 D * epow2 D
private def epow5 (D : PE) : PE := epow4 D * D
private def epow6 (D : PE) : PE := epow4 D * epow2 D

private theorem ac {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) :
    a + c ≈ b + d :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ h)
    (Q'.add_eqv_congr_left _ _ _ k)

private theorem mc {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) :
    a * c ≈ b * d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

private theorem nc {a b : Q'} (h : a ≈ b) : -a ≈ -b :=
  Q'.neg_eqv_congr _ _ h

def escalarFormula
    (ra rb rc rd pab pac pad pbc pbd pcd tabc tabd tacd tbcd f : PE) : PE :=
  ((ra * rb * rc * rd +
      -(((pab * rc * rd + pac * rb * rd) + pad * rb * rc) +
        ((pbc * ra * rd + pbd * ra * rc) + pcd * ra * rb))) +
    -((tabc * rd + tabd * rc) + (tacd * rb + tbcd * ra))) + f

private def scalarFormula
    (ra rb rc rd pab pac pad pbc pbd pcd tabc tabd tacd tbcd f : Q') : Q' :=
  ((ra * rb * rc * rd +
      -(((pab * rc * rd + pac * rb * rd) + pad * rb * rc) +
        ((pbc * ra * rd + pbd * ra * rc) + pcd * ra * rb))) +
    -((tabc * rd + tabd * rc) + (tacd * rb + tbcd * ra))) + f

def efourVector (a b c d : VE) : PE :=
  edot3 a b * edot3 c d +
    -(edot3 (ecross3 a b) (ecross3 c d))

private def fourVector (a b c d : Triple) : Q' :=
  dot3 a b * dot3 c d +
    -(dot3 (cross3 a b) (cross3 c d))

def fourScalarLeftExpression : PolyExpr :=
  (eqmul (eqmul (eqmul
    ⟨.var 0, .var 4, .var 5, .var 6⟩
    ⟨.var 1, .var 7, .var 8, .var 9⟩)
    ⟨.var 2, .var 10, .var 11, .var 12⟩)
    ⟨.var 3, .var 13, .var 14, .var 15⟩).r

def fourScalarRightExpression : PolyExpr :=
  escalarFormula (.var 0) (.var 1) (.var 2) (.var 3)
    (edot3 (ev 4) (ev 7)) (edot3 (ev 4) (ev 10))
    (edot3 (ev 4) (ev 13)) (edot3 (ev 7) (ev 10))
    (edot3 (ev 7) (ev 13)) (edot3 (ev 10) (ev 13))
    (edet3 (ev 4) (ev 7) (ev 10))
    (edet3 (ev 4) (ev 7) (ev 13))
    (edet3 (ev 4) (ev 10) (ev 13))
    (edet3 (ev 7) (ev 10) (ev 13))
    (efourVector (ev 4) (ev 7) (ev 10) (ev 13))

theorem four_scalar_normal :
    normalize fourScalarLeftExpression =
      normalize fourScalarRightExpression := by
  decide

private def vectorQuaternion (r : Q') (a : Triple) : RationalQuaternion :=
  ⟨r, a.x, a.y, a.z⟩

private theorem four_scalar (ra rb rc rd : Q') (a b c d : Triple) :
    (RationalQuaternion.mul
      (RationalQuaternion.mul
        (RationalQuaternion.mul (vectorQuaternion ra a) (vectorQuaternion rb b))
        (vectorQuaternion rc c))
      (vectorQuaternion rd d)).r ≈
    scalarFormula ra rb rc rd
      (dot3 a b) (dot3 a c) (dot3 a d)
      (dot3 b c) (dot3 b d) (dot3 c d)
      (det3 a b c) (det3 a b d) (det3 a c d) (det3 b c d)
      (fourVector a b c d) :=
  poly_identity_of_normal_eq _ _ four_scalar_normal
    (fun
      | 0 => ra
      | 1 => rb
      | 2 => rc
      | 3 => rd
      | 4 => a.x
      | 5 => a.y
      | 6 => a.z
      | 7 => b.x
      | 8 => b.y
      | 9 => b.z
      | 10 => c.x
      | 11 => c.y
      | 12 => c.z
      | 13 => d.x
      | 14 => d.y
      | _ => d.z)

private theorem scalarFormula_congr (ra rb rc rd : Q')
    {pab pac pad pbc pbd pcd tabc tabd tacd tbcd f : Q'}
    {pab' pac' pad' pbc' pbd' pcd' tabc' tabd' tacd' tbcd' f' : Q'}
    (hab : pab ≈ pab') (hac : pac ≈ pac') (had : pad ≈ pad')
    (hbc : pbc ≈ pbc') (hbd : pbd ≈ pbd') (hcd : pcd ≈ pcd')
    (habc : tabc ≈ tabc') (habd : tabd ≈ tabd')
    (hacd : tacd ≈ tacd') (hbcd : tbcd ≈ tbcd') (hf : f ≈ f') :
    scalarFormula ra rb rc rd pab pac pad pbc pbd pcd tabc tabd tacd tbcd f ≈
      scalarFormula ra rb rc rd pab' pac' pad' pbc' pbd' pcd'
        tabc' tabd' tacd' tbcd' f' := by
  have mm (x y u v : Q') (h : x ≈ y) : x * u * v ≈ y * u * v :=
    mc (mc h (Q'.eqv_refl u)) (Q'.eqv_refl v)
  exact ac (ac (ac (Q'.eqv_refl _) (nc
    (ac (ac (ac (mm _ _ rc rd hab) (mm _ _ rb rd hac))
      (mm _ _ rb rc had))
      (ac (ac (mm _ _ ra rd hbc) (mm _ _ ra rc hbd))
        (mm _ _ ra rb hcd)))))
    (nc (ac (ac (mc habc (Q'.eqv_refl rd)) (mc habd (Q'.eqv_refl rc)))
      (ac (mc hacd (Q'.eqv_refl rb)) (mc hbcd (Q'.eqv_refl ra)))))) hf

private def escale3 (scale : PE) (a : VE) : VE :=
  ⟨scale * a.x, scale * a.y, scale * a.z⟩

theorem dot_scaled_normal :
    normalize
      (edot3 (escale3 (.var 0) (ev 1)) (escale3 (.var 0) (ev 4))) =
      normalize ((.var 0 * .var 0) * edot3 (ev 1) (ev 4)) := by
  decide

private theorem dot_scaled (scale : Q') (a b : Triple) :
    dot3 (scale3 scale a) (scale3 scale b) ≈
      (scale * scale) * dot3 a b :=
  poly_identity_of_normal_eq
    (edot3 (escale3 (.var 0) (ev 1)) (escale3 (.var 0) (ev 4)))
    ((.var 0 * .var 0) * edot3 (ev 1) (ev 4)) dot_scaled_normal
    (fun
      | 0 => scale
      | 1 => a.x
      | 2 => a.y
      | 3 => a.z
      | 4 => b.x
      | 5 => b.y
      | _ => b.z)

theorem det_scaled_normal :
    normalize
      (edet3 (escale3 (.var 0) (ev 1)) (escale3 (.var 0) (ev 4))
        (escale3 (.var 0) (ev 7))) =
      normalize
        (((.var 0 * .var 0) * .var 0) * edet3 (ev 1) (ev 4) (ev 7)) := by
  decide

private theorem det_scaled (scale : Q') (a b c : Triple) :
    det3 (scale3 scale a) (scale3 scale b) (scale3 scale c) ≈
      ((scale * scale) * scale) * det3 a b c :=
  poly_identity_of_normal_eq
    (edet3 (escale3 (.var 0) (ev 1)) (escale3 (.var 0) (ev 4))
      (escale3 (.var 0) (ev 7)))
    (((.var 0 * .var 0) * .var 0) * edet3 (ev 1) (ev 4) (ev 7))
    det_scaled_normal
    (fun
      | 0 => scale
      | 1 => a.x
      | 2 => a.y
      | 3 => a.z
      | 4 => b.x
      | 5 => b.y
      | 6 => b.z
      | 7 => c.x
      | 8 => c.y
      | _ => c.z)

theorem fourVector_scaled_normal :
    normalize
      (efourVector (escale3 (.var 0) (ev 1)) (escale3 (.var 0) (ev 4))
        (escale3 (.var 0) (ev 7)) (escale3 (.var 0) (ev 10))) =
      normalize
        (((.var 0 * .var 0) * (.var 0 * .var 0)) *
          efourVector (ev 1) (ev 4) (ev 7) (ev 10)) := by
  decide

private theorem fourVector_scaled (scale : Q') (a b c d : Triple) :
    fourVector (scale3 scale a) (scale3 scale b)
        (scale3 scale c) (scale3 scale d) ≈
      ((scale * scale) * (scale * scale)) * fourVector a b c d :=
  poly_identity_of_normal_eq
    (efourVector (escale3 (.var 0) (ev 1)) (escale3 (.var 0) (ev 4))
      (escale3 (.var 0) (ev 7)) (escale3 (.var 0) (ev 10)))
    (((.var 0 * .var 0) * (.var 0 * .var 0)) *
      efourVector (ev 1) (ev 4) (ev 7) (ev 10))
    fourVector_scaled_normal
    (fun
      | 0 => scale
      | 1 => a.x
      | 2 => a.y
      | 3 => a.z
      | 4 => b.x
      | 5 => b.y
      | 6 => b.z
      | 7 => c.x
      | 8 => c.y
      | 9 => c.z
      | 10 => d.x
      | 11 => d.y
      | _ => d.z)

private def commonRawScalar (D : Q') (a b c d : Triple) : Q' :=
  let scale := 2 * D
  scalarFormula
    (pow2 D + -norm3 a) (pow2 D + -norm3 b)
    (pow2 D + -norm3 c) (pow2 D + -norm3 d)
    ((scale * scale) * dot3 a b) ((scale * scale) * dot3 a c)
    ((scale * scale) * dot3 a d) ((scale * scale) * dot3 b c)
    ((scale * scale) * dot3 b d) ((scale * scale) * dot3 c d)
    (((scale * scale) * scale) * det3 a b c)
    (((scale * scale) * scale) * det3 a b d)
    (((scale * scale) * scale) * det3 a c d)
    (((scale * scale) * scale) * det3 b c d)
    (((scale * scale) * (scale * scale)) * fourVector a b c d)

private theorem commonRawWord_scalar (D : Q') (a b c d : Triple) :
    (commonRawWord D a b c d).r ≈ commonRawScalar D a b c d := by
  let scale := 2 * D
  have hfour := four_scalar
    (pow2 D + -norm3 a) (pow2 D + -norm3 b)
    (pow2 D + -norm3 c) (pow2 D + -norm3 d)
    (scale3 scale a) (scale3 scale b) (scale3 scale c) (scale3 scale d)
  exact Q'.eqv_trans _ _ _ hfour
    (scalarFormula_congr _ _ _ _
      (dot_scaled scale a b) (dot_scaled scale a c) (dot_scaled scale a d)
      (dot_scaled scale b c) (dot_scaled scale b d) (dot_scaled scale c d)
      (det_scaled scale a b c) (det_scaled scale a b d)
      (det_scaled scale a c d) (det_scaled scale b c d)
      (fourVector_scaled scale a b c d))

private def pairDots (a b c d : Triple) : Q' :=
  ((dot3 a b + dot3 a c) + dot3 a d) +
    ((dot3 b c + dot3 b d) + dot3 c d)

theorem norm_sum_normal :
    normalize
      (enorm3 (eadd3 (eadd3 (eadd3 (ev 0) (ev 3)) (ev 6)) (ev 9))) =
      normalize
        ((((enorm3 (ev 0) + enorm3 (ev 3)) + enorm3 (ev 6)) +
          enorm3 (ev 9)) +
        2 * (((edot3 (ev 0) (ev 3) + edot3 (ev 0) (ev 6)) +
          edot3 (ev 0) (ev 9)) +
          ((edot3 (ev 3) (ev 6) + edot3 (ev 3) (ev 9)) +
            edot3 (ev 6) (ev 9)))) := by
  decide

private theorem norm_sum (a b c d : Triple) :
    norm3 (add3 (add3 (add3 a b) c) d) ≈
      (((norm3 a + norm3 b) + norm3 c) + norm3 d) +
        2 * pairDots a b c d := by
  let x := ev 0
  let y := ev 3
  let z := ev 6
  let w := ev 9
  exact poly_identity_of_normal_eq
    (enorm3 (eadd3 (eadd3 (eadd3 x y) z) w))
    ((((enorm3 x + enorm3 y) + enorm3 z) + enorm3 w) +
      2 * (((edot3 x y + edot3 x z) + edot3 x w) +
        ((edot3 y z + edot3 y w) + edot3 z w)))
    norm_sum_normal
    (fun
      | 0 => a.x
      | 1 => a.y
      | 2 => a.z
      | 3 => b.x
      | 4 => b.y
      | 5 => b.z
      | 6 => c.x
      | 7 => c.y
      | 8 => c.z
      | 9 => d.x
      | 10 => d.y
      | _ => d.z)

private def ePairDots (pab pac pad pbc pbd pcd : PE) : PE :=
  ((pab + pac) + pad) + ((pbc + pbd) + pcd)

private def eInvariantH2
    (na nb nc nd pab pac pad pbc pbd pcd : PE) : PE :=
  4 * ((((na + nb) + nc) + nd) +
    2 * ePairDots pab pac pad pbc pbd pcd)

private def eInvariantH3 (tabc tabd tacd tbcd : PE) : PE :=
  16 * ((tabc + tabd) + (tacd + tbcd))

private def eInvariantH4
    (na nb nc nd pab pac pad pbc pbd pcd f : PE) : PE :=
  -(8 * ((pab * (nc + nd) + pac * (nb + nd)) +
    pad * (nb + nc) +
    ((pbc * (na + nd) + pbd * (na + nc)) + pcd * (na + nb)))) +
  -(32 * f)

private def eInvariantH5
    (na nb nc nd tabc tabd tacd tbcd : PE) : PE :=
  -(16 * ((tabc * nd + tabd * nc) + (tacd * nb + tbcd * na)))

private def eInvariantH6
    (na nb nc nd pab pac pad pbc pbd pcd : PE) : PE :=
  4 * ((na * nb * nc + na * nb * nd) + (na * nc * nd + nb * nc * nd)) +
  8 * ((pab * (nc * nd) + pac * (nb * nd)) + pad * (nb * nc) +
    ((pbc * (na * nd) + pbd * (na * nc)) + pcd * (na * nb)))

def eInvariantDenominator (D na nb nc nd : PE) : PE :=
  (((epow2 D + na) * (epow2 D + nb)) * (epow2 D + nc)) *
    (epow2 D + nd)

def eInvariantRawScalar
    (D na nb nc nd pab pac pad pbc pbd pcd tabc tabd tacd tbcd f : PE) : PE :=
  let scale := 2 * D
  escalarFormula
    (epow2 D + -na) (epow2 D + -nb)
    (epow2 D + -nc) (epow2 D + -nd)
    ((scale * scale) * pab) ((scale * scale) * pac)
    ((scale * scale) * pad) ((scale * scale) * pbc)
    ((scale * scale) * pbd) ((scale * scale) * pcd)
    (((scale * scale) * scale) * tabc)
    (((scale * scale) * scale) * tabd)
    (((scale * scale) * scale) * tacd)
    (((scale * scale) * scale) * tbcd)
    (((scale * scale) * (scale * scale)) * f)

def eInvariantDeficit
    (D na nb nc nd pab pac pad pbc pbd pcd tabc tabd tacd tbcd f : PE) : PE :=
  ((((epow6 D * eInvariantH2 na nb nc nd pab pac pad pbc pbd pcd +
      epow5 D * eInvariantH3 tabc tabd tacd tbcd) +
      epow4 D * eInvariantH4 na nb nc nd pab pac pad pbc pbd pcd f) +
      epow3 D * eInvariantH5 na nb nc nd tabc tabd tacd tbcd) +
      epow2 D * eInvariantH6 na nb nc nd pab pac pad pbc pbd pcd)

def invariantLeftExpression : PolyExpr :=
  2 * eInvariantDenominator (.var 0) (.var 1) (.var 2) (.var 3) (.var 4) +
    -(2 * eInvariantRawScalar
      (.var 0) (.var 1) (.var 2) (.var 3) (.var 4)
      (.var 5) (.var 6) (.var 7) (.var 8) (.var 9) (.var 10)
      (.var 11) (.var 12) (.var 13) (.var 14) (.var 15))

def invariantDeficitExpression : PolyExpr :=
  eInvariantDeficit
    (.var 0) (.var 1) (.var 2) (.var 3) (.var 4)
    (.var 5) (.var 6) (.var 7) (.var 8) (.var 9) (.var 10)
    (.var 11) (.var 12) (.var 13) (.var 14) (.var 15)

theorem invariant_normal :
    normalize invariantLeftExpression =
      normalize invariantDeficitExpression := by
  decide

private def invariantEnvironment (D : Q') (a b c d : Triple) : Nat → Q'
  | 0 => D
  | 1 => norm3 a
  | 2 => norm3 b
  | 3 => norm3 c
  | 4 => norm3 d
  | 5 => dot3 a b
  | 6 => dot3 a c
  | 7 => dot3 a d
  | 8 => dot3 b c
  | 9 => dot3 b d
  | 10 => dot3 c d
  | 11 => det3 a b c
  | 12 => det3 a b d
  | 13 => det3 a c d
  | 14 => det3 b c d
  | _ => fourVector a b c d

/-- Coordinatewise scalar multiplication of a rational quaternion. -/
def qscale (scale : Q') (q : RationalQuaternion) : RationalQuaternion :=
  ⟨scale * q.r, scale * q.i, scale * q.j, scale * q.k⟩

private def quaternionTrans {a b c : RationalQuaternion}
    (h : a.Equivalent b) (k : b.Equivalent c) : a.Equivalent c :=
  ⟨Q'.eqv_trans _ _ _ h.1 k.1,
    Q'.eqv_trans _ _ _ h.2.1 k.2.1,
    Q'.eqv_trans _ _ _ h.2.2.1 k.2.2.1,
    Q'.eqv_trans _ _ _ h.2.2.2 k.2.2.2⟩

private def quaternionSymm {a b : RationalQuaternion}
    (h : a.Equivalent b) : b.Equivalent a :=
  ⟨Q'.eqv_symm h.1, Q'.eqv_symm h.2.1,
    Q'.eqv_symm h.2.2.1, Q'.eqv_symm h.2.2.2⟩

private theorem commonRaw_denominator_congr
    {D E : Q'} (hDE : D ≈ E) (a : Triple) :
    (commonRaw D a).Equivalent (commonRaw E a) :=
  ⟨ac (mc hDE hDE) (Q'.eqv_refl _),
    mc (mc (Q'.eqv_refl 2) hDE) (Q'.eqv_refl a.x),
    mc (mc (Q'.eqv_refl 2) hDE) (Q'.eqv_refl a.y),
    mc (mc (Q'.eqv_refl 2) hDE) (Q'.eqv_refl a.z)⟩

private theorem clearedFactor_denominator_congr
    {D E : Q'} (hDE : D ≈ E) (a : Triple) :
    clearedFactor D a ≈ clearedFactor E a :=
  ac (mc hDE hDE) (Q'.eqv_refl _)

private theorem qscale_scale_congr {scale target : Q'}
    (h : scale ≈ target) (q : RationalQuaternion) :
    (qscale scale q).Equivalent (qscale target q) :=
  ⟨mc h (Q'.eqv_refl q.r), mc h (Q'.eqv_refl q.i),
    mc h (Q'.eqv_refl q.j), mc h (Q'.eqv_refl q.k)⟩

private theorem unit_chart_residual_zero (x : UnitNorm) :
    1 + -(x.val.r * x.val.r + norm3 (chartNumerator x)) ≈ 0 := by
  have hnorm : x.val.r * x.val.r + norm3 (chartNumerator x) ≈ 1 :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.var 0 * .var 0 +
          ((.var 1 * .var 1 + .var 2 * .var 2) + .var 3 * .var 3))
        ((.var 0 * .var 0 + .var 1 * .var 1) +
          (.var 2 * .var 2 + .var 3 * .var 3))
        (by decide)
        (fun
          | 0 => x.val.r
          | 1 => x.val.i
          | 2 => x.val.j
          | _ => x.val.k))
      x.unitNorm
  exact Q'.eqv_trans _ _ _ (ac (Q'.eqv_refl 1) (nc hnorm)) (by decide)

private theorem local_commonRaw_chart_clear (x : UnitNorm) (complement : Q') :
    let D := chartDenominator x * complement
    let a := scale3 complement (chartNumerator x)
    (commonRaw D a).Equivalent (qscale (clearedFactor D a) x.val) := by
  dsimp only
  let r := x.val.r
  let i := x.val.i
  let j := x.val.j
  let k := x.val.k
  let residual := 1 + -(r * r + norm3 (chartNumerator x))
  have hres : residual ≈ 0 := unit_chart_residual_zero x
  have hscalar :
      (commonRaw (chartDenominator x * complement)
          (scale3 complement (chartNumerator x))).r ≈
        clearedFactor (chartDenominator x * complement)
            (scale3 complement (chartNumerator x)) * r +
          (complement * complement) * (1 + r) * residual := by
    simpa only [commonRaw, clearedFactor, pow2, chartDenominator,
      chartNumerator, scale3, norm3, epow2, enorm3, edot3, escale3, ev,
      r, i, j, k, residual] using
      (poly_identity_of_normal_eq
        (epow2 ((1 + (.var 0 : PE)) * (.var 1 : PE)) +
          -enorm3 (escale3 (.var 1) (ev 2)))
        ((epow2 ((1 + (.var 0 : PE)) * (.var 1 : PE)) +
            enorm3 (escale3 (.var 1) (ev 2))) * (.var 0 : PE) +
          epow2 (.var 1) * (1 + (.var 0 : PE)) *
            (1 + -(epow2 (.var 0) + enorm3 (ev 2))))
        (by decide)
        (fun
          | 0 => r
          | 1 => complement
          | 2 => i
          | 3 => j
          | _ => k))
  have hcomponent (value : Q') :
      2 * (chartDenominator x * complement) * (complement * value) ≈
        clearedFactor (chartDenominator x * complement)
            (scale3 complement (chartNumerator x)) * value +
          (complement * complement) * residual * value := by
    simpa only [clearedFactor, pow2, chartDenominator, chartNumerator,
      scale3, norm3, epow2, enorm3, edot3, escale3, ev,
      r, i, j, k, residual] using
      (poly_identity_of_normal_eq
        (2 * ((1 + (.var 0 : PE)) * (.var 1 : PE)) *
          ((.var 1 : PE) * (.var 5 : PE)))
        ((epow2 ((1 + (.var 0 : PE)) * (.var 1 : PE)) +
            enorm3 (escale3 (.var 1) (ev 2))) * (.var 5 : PE) +
          epow2 (.var 1) *
            (1 + -(epow2 (.var 0) + enorm3 (ev 2))) * (.var 5 : PE))
        (by decide)
        (fun
          | 0 => r
          | 1 => complement
          | 2 => i
          | 3 => j
          | 4 => k
          | _ => value))
  have hscalarCorrection :
      (complement * complement) * (1 + r) * residual ≈ 0 :=
    Q'.eqv_trans _ _ _
      (mc (Q'.eqv_refl ((complement * complement) * (1 + r))) hres)
      (Q'.mul_zero_eqv _)
  have hvectorCorrection (value : Q') :
      (complement * complement) * residual * value ≈ 0 := by
    have hreorder :
        (complement * complement) * residual * value ≈
          ((complement * complement) * value) * residual :=
      poly_identity_of_normal_eq
        ((.var 0 * .var 0) * .var 1 * .var 2)
        (((.var 0 * .var 0) * .var 2) * .var 1)
        (by decide) (fun | 0 => complement | 1 => residual | _ => value)
    exact Q'.eqv_trans _ _ _ hreorder
      (Q'.eqv_trans _ _ _
        (mc (Q'.eqv_refl ((complement * complement) * value)) hres)
        (Q'.mul_zero_eqv _))
  refine ⟨Q'.eqv_trans _ _ _ hscalar
      (Q'.eqv_trans _ _ _
        (ac (Q'.eqv_refl _) hscalarCorrection)
        (Q'.eqv_of_eq (Q'.add_zero' _))), ?_, ?_, ?_⟩
  · exact Q'.eqv_trans _ _ _ (hcomponent i)
      (Q'.eqv_trans _ _ _
        (ac (Q'.eqv_refl _) (hvectorCorrection i))
        (Q'.eqv_of_eq (Q'.add_zero' _)))
  · exact Q'.eqv_trans _ _ _ (hcomponent j)
      (Q'.eqv_trans _ _ _
        (ac (Q'.eqv_refl _) (hvectorCorrection j))
        (Q'.eqv_of_eq (Q'.add_zero' _)))
  · exact Q'.eqv_trans _ _ _ (hcomponent k)
      (Q'.eqv_trans _ _ _
        (ac (Q'.eqv_refl _) (hvectorCorrection k))
        (Q'.eqv_of_eq (Q'.add_zero' _)))

private theorem commonRaw_chart_clear_of_denominator
    (D complement : Q') (x : UnitNorm)
    (hD : D ≈ chartDenominator x * complement) :
    let a := scale3 complement (chartNumerator x)
    (commonRaw D a).Equivalent (qscale (clearedFactor D a) x.val) := by
  dsimp only
  let targetD := chartDenominator x * complement
  let a := scale3 complement (chartNumerator x)
  have hraw := commonRaw_denominator_congr hD a
  have hlocal := local_commonRaw_chart_clear x complement
  have hfactor := clearedFactor_denominator_congr hD a
  exact quaternionTrans hraw
    (quaternionTrans hlocal (quaternionSymm (qscale_scale_congr hfactor x.val)))

private theorem scaled_product (d f x y : Q') :
    (d * x) * (f * y) ≈ (d * f) * (x * y) :=
  poly_identity_of_normal_eq
    ((.var 0 * .var 2) * (.var 1 * .var 3))
    ((.var 0 * .var 1) * (.var 2 * .var 3))
    (by decide) (fun | 0 => d | 1 => f | 2 => x | _ => y)

private theorem scaled_add (scale : Q') {x y targetX targetY : Q'}
    (hx : x ≈ scale * targetX) (hy : y ≈ scale * targetY) :
    x + y ≈ scale * (targetX + targetY) :=
  Q'.eqv_trans _ _ _ (ac hx hy)
    (Q'.eqv_symm (Q'.mul_add_eqv scale targetX targetY))

private theorem scaled_neg (scale : Q') {x target : Q'}
    (h : x ≈ scale * target) : -x ≈ scale * (-target) :=
  Q'.eqv_trans _ _ _ (nc h)
    (poly_identity_of_normal_eq
      (-((.var 0) * (.var 1))) (.var 0 * -(.var 1))
      (by decide) (fun | 0 => scale | _ => target))

private theorem scaled_mul (d f : Q') (a b : RationalQuaternion) :
    (RationalQuaternion.mul (qscale d a) (qscale f b)).Equivalent
      (qscale (d * f) (RationalQuaternion.mul a b)) := by
  have hp (x y : Q') : (d * x) * (f * y) ≈ (d * f) * (x * y) :=
    scaled_product d f x y
  exact ⟨scaled_add (d * f)
      (scaled_add (d * f) (hp a.r b.r) (scaled_neg (d * f) (hp a.i b.i)))
      (scaled_add (d * f) (scaled_neg (d * f) (hp a.j b.j))
        (scaled_neg (d * f) (hp a.k b.k))),
    scaled_add (d * f)
      (scaled_add (d * f) (hp a.r b.i) (hp a.i b.r))
      (scaled_add (d * f) (hp a.j b.k) (scaled_neg (d * f) (hp a.k b.j))),
    scaled_add (d * f)
      (scaled_add (d * f) (hp a.r b.j) (scaled_neg (d * f) (hp a.i b.k)))
      (scaled_add (d * f) (hp a.j b.r) (hp a.k b.i)),
    scaled_add (d * f)
      (scaled_add (d * f) (hp a.r b.k) (hp a.i b.j))
      (scaled_add (d * f) (scaled_neg (d * f) (hp a.j b.i)) (hp a.k b.r))⟩

private theorem clear_mul {d f : Q'} {a b p q : RationalQuaternion}
    (h : (qscale d a).Equivalent p) (k : (qscale f b).Equivalent q) :
    (qscale (d * f) (RationalQuaternion.mul a b)).Equivalent
      (RationalQuaternion.mul p q) :=
  quaternionTrans (quaternionSymm (scaled_mul d f a b))
    (RationalQuaternion.mul_congr h k)

private theorem common_split_first (a b c d : UnitNorm) :
    commonChartDenominator a b c d ≈
      chartDenominator a * firstComplement a b c d := by
  unfold commonChartDenominator firstComplement
  exact poly_identity_of_normal_eq
    (((.var 0 * .var 1) * .var 2) * .var 3)
    (.var 0 * ((.var 1 * .var 2) * .var 3))
    (by decide) (fun
      | 0 => chartDenominator a
      | 1 => chartDenominator b
      | 2 => chartDenominator c
      | _ => chartDenominator d)

private theorem common_split_second (a b c d : UnitNorm) :
    commonChartDenominator a b c d ≈
      chartDenominator b * secondComplement a b c d := by
  unfold commonChartDenominator secondComplement
  exact poly_identity_of_normal_eq
    (((.var 0 * .var 1) * .var 2) * .var 3)
    (.var 1 * ((.var 0 * .var 2) * .var 3))
    (by decide) (fun
      | 0 => chartDenominator a
      | 1 => chartDenominator b
      | 2 => chartDenominator c
      | _ => chartDenominator d)

private theorem common_split_third (a b c d : UnitNorm) :
    commonChartDenominator a b c d ≈
      chartDenominator c * thirdComplement a b c d := by
  unfold commonChartDenominator thirdComplement
  exact poly_identity_of_normal_eq
    (((.var 0 * .var 1) * .var 2) * .var 3)
    (.var 2 * ((.var 0 * .var 1) * .var 3))
    (by decide) (fun
      | 0 => chartDenominator a
      | 1 => chartDenominator b
      | 2 => chartDenominator c
      | _ => chartDenominator d)

private theorem common_split_fourth (a b c d : UnitNorm) :
    commonChartDenominator a b c d ≈
      chartDenominator d * fourthComplement a b c d := by
  unfold commonChartDenominator fourthComplement
  exact poly_identity_of_normal_eq
    (((.var 0 * .var 1) * .var 2) * .var 3)
    (.var 3 * ((.var 0 * .var 1) * .var 2))
    (by decide) (fun
      | 0 => chartDenominator a
      | 1 => chartDenominator b
      | 2 => chartDenominator c
      | _ => chartDenominator d)

/-- Exact raw common-denominator Cayley identity.  This is a polynomial
identity with no reciprocal, positivity premise, chart branch or unit-norm
hypothesis. -/
theorem commonRawWord_cayley_cleared
    (D : Q') (a b c d : Triple) :
    2 * clearedCayleyDenominator D a b c d +
        -(2 * (commonRawWord D a b c d).r) ≈
      clearedCayleyDeficit D a b c d := by
  have hpoly := poly_identity_of_normal_eq _ _ invariant_normal
    (invariantEnvironment D a b c d)
  have h2 :
      4 * ((((norm3 a + norm3 b) + norm3 c) + norm3 d) +
          2 * pairDots a b c d) ≈ H2 a b c d :=
    mc (Q'.eqv_refl 4) (Q'.eqv_symm (norm_sum a b c d))
  have hright :
      eval (invariantEnvironment D a b c d)
        (eInvariantDeficit
          (.var 0) (.var 1) (.var 2) (.var 3) (.var 4)
          (.var 5) (.var 6) (.var 7) (.var 8) (.var 9) (.var 10)
          (.var 11) (.var 12) (.var 13) (.var 14) (.var 15)) ≈
      clearedCayleyDeficit D a b c d :=
    ac (ac (ac (ac
      (mc (Q'.eqv_refl _) h2)
      (Q'.eqv_refl _)) (Q'.eqv_refl _)) (Q'.eqv_refl _))
      (Q'.eqv_refl _)
  exact Q'.eqv_trans _ _ _
    (ac (Q'.eqv_refl _)
      (nc (mc (Q'.eqv_refl 2) (commonRawWord_scalar D a b c d))))
    (Q'.eqv_trans _ _ _ hpoly hright)

/-- Four arbitrary actual unit links satisfy the denominator-cleared Cayley
identity globally.  In particular, the identity remains valid when one or
more factors are the south pole, where the ordinary inverse chart is absent. -/
theorem unitWord_global_cayley_polynomial_cleared (a b c d : UnitNorm) :
    let D := commonChartDenominator a b c d
    let p := firstClearedTriple a b c d
    let q := secondClearedTriple a b c d
    let r := thirdClearedTriple a b c d
    let s := fourthClearedTriple a b c d
    clearedCayleyDenominator D p q r s *
        (2 + -(2 *
          (UnitNorm.mul (UnitNorm.mul (UnitNorm.mul a b) c) d).val.r)) ≈
      clearedCayleyDeficit D p q r s := by
  dsimp only
  let D := commonChartDenominator a b c d
  let p := firstClearedTriple a b c d
  let q := secondClearedTriple a b c d
  let r := thirdClearedTriple a b c d
  let s := fourthClearedTriple a b c d
  change clearedCayleyDenominator D p q r s *
      (2 + -(2 *
        (UnitNorm.mul (UnitNorm.mul (UnitNorm.mul a b) c) d).val.r)) ≈
    clearedCayleyDeficit D p q r s
  have hp :
      (commonRaw D p).Equivalent (qscale (clearedFactor D p) a.val) := by
    simpa only [D, p, firstClearedTriple] using
      (commonRaw_chart_clear_of_denominator
        (commonChartDenominator a b c d) (firstComplement a b c d) a
        (common_split_first a b c d))
  have hq :
      (commonRaw D q).Equivalent (qscale (clearedFactor D q) b.val) := by
    simpa only [D, q, secondClearedTriple] using
      (commonRaw_chart_clear_of_denominator
        (commonChartDenominator a b c d) (secondComplement a b c d) b
        (common_split_second a b c d))
  have hr :
      (commonRaw D r).Equivalent (qscale (clearedFactor D r) c.val) := by
    simpa only [D, r, thirdClearedTriple] using
      (commonRaw_chart_clear_of_denominator
        (commonChartDenominator a b c d) (thirdComplement a b c d) c
        (common_split_third a b c d))
  have hs :
      (commonRaw D s).Equivalent (qscale (clearedFactor D s) d.val) := by
    simpa only [D, s, fourthClearedTriple] using
      (commonRaw_chart_clear_of_denominator
        (commonChartDenominator a b c d) (fourthComplement a b c d) d
        (common_split_fourth a b c d))
  have hword := clear_mul
    (clear_mul
      (clear_mul (quaternionSymm hp) (quaternionSymm hq))
      (quaternionSymm hr))
    (quaternionSymm hs)
  have hscalar :
      clearedCayleyDenominator D p q r s *
          (UnitNorm.mul (UnitNorm.mul (UnitNorm.mul a b) c) d).val.r ≈
        (commonRawWord D p q r s).r := by
    simpa only [clearedCayleyDenominator, commonRawWord, UnitNorm.mul] using hword.1
  have hdistribute (x y : Q') :
      x * (2 + -(2 * y)) ≈ 2 * x + -(2 * (x * y)) :=
    poly_identity_of_normal_eq
      (.var 0 * (2 + -(2 * .var 1)))
      (2 * .var 0 + -(2 * (.var 0 * .var 1)))
      (by decide) (fun | 0 => x | _ => y)
  exact Q'.eqv_trans _ _ _ (hdistribute _ _)
    (Q'.eqv_trans _ _ _
      (ac (Q'.eqv_refl _) (nc (mc (Q'.eqv_refl 2) hscalar)))
      (commonRawWord_cayley_cleared D p q r s))

/-- The SAME ORIGINAL corrected-slab plaquette scalar has a global
division-free Cayley identity.  The third and fourth factors are the literal
group inverses from the plaquette orientation.  No chart sign, sector
indicator, reciprocal, positivity premise, distinct-link premise or measure
change occurs. -/
theorem original_plaquette_global_cayley_polynomial_cleared
    (extent : Nat) (qs : Nat → UnitNorm) (face : Z4Plaq) :
    let u0 := linkValue extent qs (face.1, (dirsOf face.2).1)
    let u1 := linkValue extent qs
      (addE face.1 (dirsOf face.2).1, (dirsOf face.2).2)
    let u2 := linkValue extent qs
      (addE face.1 (dirsOf face.2).2, (dirsOf face.2).1)
    let u3 := linkValue extent qs (face.1, (dirsOf face.2).2)
    let v2 := UnitNorm.inv u2
    let v3 := UnitNorm.inv u3
    let D := commonChartDenominator u0 u1 v2 v3
    let p := firstClearedTriple u0 u1 v2 v3
    let q := secondClearedTriple u0 u1 v2 v3
    let r := thirdClearedTriple u0 u1 v2 v3
    let s := fourthClearedTriple u0 u1 v2 v3
    clearedCayleyDenominator D p q r s *
        (2 + -(2 * evalRatPoly (environment qs)
          (correctedSlabPlaquettePolynomial extent face).scalar)) ≈
      clearedCayleyDeficit D p q r s := by
  dsimp only
  let u0 := linkValue extent qs (face.1, (dirsOf face.2).1)
  let u1 := linkValue extent qs
    (addE face.1 (dirsOf face.2).1, (dirsOf face.2).2)
  let u2 := linkValue extent qs
    (addE face.1 (dirsOf face.2).2, (dirsOf face.2).1)
  let u3 := linkValue extent qs (face.1, (dirsOf face.2).2)
  let v2 := UnitNorm.inv u2
  let v3 := UnitNorm.inv u3
  let D := commonChartDenominator u0 u1 v2 v3
  let p := firstClearedTriple u0 u1 v2 v3
  let q := secondClearedTriple u0 u1 v2 v3
  let r := thirdClearedTriple u0 u1 v2 v3
  let s := fourthClearedTriple u0 u1 v2 v3
  change clearedCayleyDenominator D p q r s *
      (2 + -(2 * evalRatPoly (environment qs)
        (correctedSlabPlaquettePolynomial extent face).scalar)) ≈
    clearedCayleyDeficit D p q r s
  have horiginal :
      evalRatPoly (environment qs)
          (correctedSlabPlaquettePolynomial extent face).scalar ≈
        (UnitNorm.mul (UnitNorm.mul (UnitNorm.mul u0 u1) v2) v3).val.r := by
    simpa only [u0, u1, u2, u3, v2, v3, plaquetteValue] using
      (plaquette_scalar_pin extent qs face)
  have hbracket :
      2 + -(2 * evalRatPoly (environment qs)
          (correctedSlabPlaquettePolynomial extent face).scalar) ≈
        2 + -(2 *
          (UnitNorm.mul (UnitNorm.mul (UnitNorm.mul u0 u1) v2) v3).val.r) :=
    ac (Q'.eqv_refl 2) (nc (mc (Q'.eqv_refl 2) horiginal))
  exact Q'.eqv_trans _ _ _
    (mc (Q'.eqv_refl (clearedCayleyDenominator D p q r s)) hbracket)
    (unitWord_global_cayley_polynomial_cleared u0 u1 v2 v3)

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyPolynomialClear

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyPolynomialClear.commonRawWord_cayley_cleared
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyPolynomialClear.unitWord_global_cayley_polynomial_cleared
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyPolynomialClear.original_plaquette_global_cayley_polynomial_cleared
