/-
# Exact Cayley-chart expansion of the ORIGINAL ordered plaquette scalar

For arbitrary rational chart directions and chart size, the denominator-cleared
fundamental trace deficit is an EXACT polynomial of degrees two through six.
The cubic and quartic terms are retained with their Hamilton-product signs.
The final consumer uses the original corrected-slab polynomial scalar pin and
four explicit link-value/chart identifications. Repeated links and the original
fallback are not replaced by independent variables.

This is source matching only. It supplies no small-chart heat-action expansion,
Haar-Jacobian estimate, Gaussian comparison, analytic remainder bound, original
interacting response estimate, physical scaling, or mass gap. In particular the
normalized quartic coefficient additionally contains the denominator correction.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteDeficit
import YMGap.RepTheory.RationalQuaternionCommutatorDefect

namespace YMGap.Continuum.BF4ExactSlabPlaquetteCayleyExpansion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.RepTheory
open YMGap.RepTheory.RationalQuaternion
open YMGap.RepTheory.RationalQuaternionSphereNets
open YMGap.RepTheory.RationalQuaternionCommutatorDefect (plaquetteWord)
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactSlabPlaquetteDeficit
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.QuaternionHaarFiniteProductOrder (environment)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress

local infix:50 " ≈ " => Q'.eqv
private abbrev PE := PolyExpr
local instance : Add PE := ⟨.add⟩
local instance : Mul PE := ⟨.mul⟩
local instance : Neg PE := ⟨.neg⟩
local instance (n : Nat) : OfNat PE n := ⟨.const (Int.ofNat n)⟩

def add3 (a b : Triple) : Triple := ⟨a.x+b.x,a.y+b.y,a.z+b.z⟩
def neg3 (a : Triple) : Triple := ⟨-a.x,-a.y,-a.z⟩
def scale3 (e : Q') (a : Triple) : Triple := ⟨e*a.x,e*a.y,e*a.z⟩
def dot3 (a b : Triple) : Q' := (a.x*b.x+a.y*b.y)+a.z*b.z
def cross3 (a b : Triple) : Triple :=
  ⟨a.y*b.z + -(a.z*b.y), a.z*b.x + -(a.x*b.z), a.x*b.y + -(a.y*b.x)⟩
def det3 (a b c : Triple) : Q' := dot3 (cross3 a b) c

def pairCrosses (a b c d : Triple) : Triple :=
  add3 (add3 (add3 (cross3 a b) (cross3 a c)) (cross3 a d))
    (add3 (add3 (cross3 b c) (cross3 b d)) (cross3 c d))

private def pairDots (a b c d : Triple) : Q' :=
  ((dot3 a b+dot3 a c)+dot3 a d)+((dot3 b c+dot3 b d)+dot3 c d)

/-- Quadratic coefficient for the four DIRECTED chart vectors. -/
def H2 (a b c d : Triple) : Q' := 4*norm3 (add3 (add3 (add3 a b) c) d)

/-- Cubic coefficient; equivalently 16 times sum-vectors dot sum-pair-crosses. -/
def H3 (a b c d : Triple) : Q' :=
  16*((det3 a b c+det3 a b d)+(det3 a c d+det3 b c d))

/-- Cleared quartic coefficient, not the normalized quartic coefficient. -/
def H4 (a b c d : Triple) : Q' :=
  -(8*((dot3 a b*(norm3 c+norm3 d)+dot3 a c*(norm3 b+norm3 d))+
    dot3 a d*(norm3 b+norm3 c)+
    ((dot3 b c*(norm3 a+norm3 d)+dot3 b d*(norm3 a+norm3 c))+
      dot3 c d*(norm3 a+norm3 b)))) +
  -(32*(dot3 a b*dot3 c d + -(dot3 (cross3 a b) (cross3 c d))))

def H5 (a b c d : Triple) : Q' :=
  -(16*((det3 a b c*norm3 d+det3 a b d*norm3 c)+
    (det3 a c d*norm3 b+det3 b c d*norm3 a)))

def H6 (a b c d : Triple) : Q' :=
  4*((norm3 a*norm3 b*norm3 c+norm3 a*norm3 b*norm3 d)+
    (norm3 a*norm3 c*norm3 d+norm3 b*norm3 c*norm3 d)) +
  8*((dot3 a b*(norm3 c*norm3 d)+dot3 a c*(norm3 b*norm3 d))+
    dot3 a d*(norm3 b*norm3 c)+
    ((dot3 b c*(norm3 a*norm3 d)+dot3 b d*(norm3 a*norm3 c))+
      dot3 c d*(norm3 a*norm3 b)))

private def factor (e : Q') (a : Triple) : Q' := 1+(e*e)*norm3 a

/-- Product of the four positive chart denominators, in directed-vector form. -/
def cayleyDenominator (e : Q') (a b c d : Triple) : Q' :=
  ((factor e a*factor e b)*factor e c)*factor e d

/-- Exact finite polynomial; its residual consists of the displayed fifth and
sixth degree terms, not a supplied analytic big-O estimate. -/
def cayleyDeficit (e : Q') (a b c d : Triple) : Q' :=
  ((((e*e)*H2 a b c d+((e*e)*e)*H3 a b c d)+
    ((e*e)*(e*e))*H4 a b c d)+
    (((e*e)*(e*e))*e)*H5 a b c d)+
    (((e*e)*(e*e))*(e*e))*H6 a b c d

private theorem ac {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a+c ≈ b+d :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ h) (Q'.add_eqv_congr_left _ _ _ k)
private theorem mc {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)
private theorem nc {a b : Q'} (h : a ≈ b) : -a ≈ -b := Q'.neg_eqv_congr _ _ h

private structure VE where
  x : PE
  y : PE
  z : PE
private def ev (n : Nat) : VE := ⟨.var n,.var (n+1),.var (n+2)⟩
private def edot (a b : VE) : PE := (a.x*b.x+a.y*b.y)+a.z*b.z
private def ecross (a b : VE) : VE :=
  ⟨a.y*b.z + -(a.z*b.y), a.z*b.x + -(a.x*b.z), a.x*b.y + -(a.y*b.x)⟩
private def edet (a b c : VE) : PE := edot (ecross a b) c
private def eadd (a b : VE) : VE := ⟨a.x+b.x,a.y+b.y,a.z+b.z⟩
private def epairCrosses (a b c d : VE) : VE :=
  eadd (eadd (eadd (ecross a b) (ecross a c)) (ecross a d))
    (eadd (eadd (ecross b c) (ecross b d)) (ecross c d))

/-- The ordered triple sum is exactly B dot the ordered pair-cross sum. -/
theorem H3_dot_cross (a b c d : Triple) :
    H3 a b c d ≈
      16*dot3 (add3 (add3 (add3 a b) c) d) (pairCrosses a b c d) := by
  let x := ev 0
  let y := ev 3
  let z := ev 6
  let w := ev 9
  exact poly_identity_of_normal_eq
    (16*((edet x y z+edet x y w)+(edet x z w+edet y z w)))
    (16*edot (eadd (eadd (eadd x y) z) w) (epairCrosses x y z w))
    (by decide)
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

private structure QE where
  r : PE
  i : PE
  j : PE
  k : PE
private def qm (a b : QE) : QE :=
  ⟨(a.r*b.r + -(a.i*b.i))+(-(a.j*b.j)+ -(a.k*b.k)),
    (a.r*b.i+a.i*b.r)+(a.j*b.k + -(a.k*b.j)),
    (a.r*b.j + -(a.i*b.k))+(a.j*b.r+a.k*b.i),
    (a.r*b.k+a.i*b.j)+(-(a.j*b.i)+a.k*b.r)⟩
private def eqv (r : PE) (a : VE) : QE := ⟨r,a.x,a.y,a.z⟩
private def escalarFormula (ra rb rc rd pab pac pad pbc pbd pcd tabc tabd tacd tbcd f : PE) : PE :=
  ((ra*rb*rc*rd + -(((pab*rc*rd+pac*rb*rd)+pad*rb*rc)+
    ((pbc*ra*rd+pbd*ra*rc)+pcd*ra*rb))) +
    -((tabc*rd+tabd*rc)+(tacd*rb+tbcd*ra)))+f
private def scalarFormula (ra rb rc rd pab pac pad pbc pbd pcd tabc tabd tacd tbcd f : Q') : Q' :=
  ((ra*rb*rc*rd + -(((pab*rc*rd+pac*rb*rd)+pad*rb*rc)+
    ((pbc*ra*rd+pbd*ra*rc)+pcd*ra*rb))) +
    -((tabc*rd+tabd*rc)+(tacd*rb+tbcd*ra)))+f
private def fourVector (a b c d : Triple) : Q' :=
  dot3 a b*dot3 c d + -(dot3 (cross3 a b) (cross3 c d))
private def efourVector (a b c d : VE) : PE :=
  edot a b*edot c d + -(edot (ecross a b) (ecross c d))

-- A generic degree-four Hamilton scalar identity: no chart norms or powers
-- are unfolded into its coordinate certificate.
private theorem four_scalar_normal :
    normalize (qm (qm (qm (eqv (.var 0) (ev 4)) (eqv (.var 1) (ev 7)))
      (eqv (.var 2) (ev 10))) (eqv (.var 3) (ev 13))).r =
    normalize (escalarFormula (.var 0) (.var 1) (.var 2) (.var 3)
      (edot (ev 4) (ev 7)) (edot (ev 4) (ev 10)) (edot (ev 4) (ev 13))
      (edot (ev 7) (ev 10)) (edot (ev 7) (ev 13)) (edot (ev 10) (ev 13))
      (edet (ev 4) (ev 7) (ev 10)) (edet (ev 4) (ev 7) (ev 13))
      (edet (ev 4) (ev 10) (ev 13)) (edet (ev 7) (ev 10) (ev 13))
      (efourVector (ev 4) (ev 7) (ev 10) (ev 13))) := by decide

private def vectorQuaternion (r : Q') (a : Triple) : RationalQuaternion := ⟨r,a.x,a.y,a.z⟩
private theorem four_scalar (ra rb rc rd : Q') (a b c d : Triple) :
    (RationalQuaternion.mul (RationalQuaternion.mul
      (RationalQuaternion.mul (vectorQuaternion ra a) (vectorQuaternion rb b))
      (vectorQuaternion rc c)) (vectorQuaternion rd d)).r ≈
    scalarFormula ra rb rc rd (dot3 a b) (dot3 a c) (dot3 a d)
      (dot3 b c) (dot3 b d) (dot3 c d) (det3 a b c) (det3 a b d)
      (det3 a c d) (det3 b c d) (fourVector a b c d) :=
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
    (habc : tabc ≈ tabc') (habd : tabd ≈ tabd') (hacd : tacd ≈ tacd')
    (hbcd : tbcd ≈ tbcd') (hf : f ≈ f') :
    scalarFormula ra rb rc rd pab pac pad pbc pbd pcd tabc tabd tacd tbcd f ≈
    scalarFormula ra rb rc rd pab' pac' pad' pbc' pbd' pcd' tabc' tabd' tacd' tbcd' f' := by
  have mm (x y u v : Q') (h : x ≈ y) : x*u*v ≈ y*u*v :=
    mc (mc h (Q'.eqv_refl u)) (Q'.eqv_refl v)
  exact ac (ac (ac (Q'.eqv_refl _) (nc
    (ac (ac (ac (mm _ _ rc rd hab) (mm _ _ rb rd hac)) (mm _ _ rb rc had))
      (ac (ac (mm _ _ ra rd hbc) (mm _ _ ra rc hbd)) (mm _ _ ra rb hcd)))))
    (nc (ac (ac (mc habc (Q'.eqv_refl rd)) (mc habd (Q'.eqv_refl rc)))
      (ac (mc hacd (Q'.eqv_refl rb)) (mc hbcd (Q'.eqv_refl ra)))))) hf

private def escale (s : PE) (a : VE) : VE := ⟨s*a.x,s*a.y,s*a.z⟩
private theorem dot_scaled (s : Q') (a b : Triple) :
    dot3 (scale3 s a) (scale3 s b) ≈ (s*s)*dot3 a b :=
  poly_identity_of_normal_eq (edot (escale (.var 0) (ev 1)) (escale (.var 0) (ev 4)))
    ((.var 0*.var 0)*edot (ev 1) (ev 4)) (by decide)
    (fun
      | 0 => s
      | 1 => a.x
      | 2 => a.y
      | 3 => a.z
      | 4 => b.x
      | 5 => b.y
      | _ => b.z)
private theorem det_scaled (s : Q') (a b c : Triple) :
    det3 (scale3 s a) (scale3 s b) (scale3 s c) ≈ ((s*s)*s)*det3 a b c :=
  poly_identity_of_normal_eq
    (edet (escale (.var 0) (ev 1)) (escale (.var 0) (ev 4)) (escale (.var 0) (ev 7)))
    (((.var 0*.var 0)*.var 0)*edet (ev 1) (ev 4) (ev 7)) (by decide)
    (fun
      | 0 => s
      | 1 => a.x
      | 2 => a.y
      | 3 => a.z
      | 4 => b.x
      | 5 => b.y
      | 6 => b.z
      | 7 => c.x
      | 8 => c.y
      | _ => c.z)
private theorem fourVector_scaled (s : Q') (a b c d : Triple) :
    fourVector (scale3 s a) (scale3 s b) (scale3 s c) (scale3 s d) ≈
      ((s*s)*(s*s))*fourVector a b c d :=
  poly_identity_of_normal_eq
    (efourVector (escale (.var 0) (ev 1)) (escale (.var 0) (ev 4))
      (escale (.var 0) (ev 7)) (escale (.var 0) (ev 10)))
    (((.var 0*.var 0)*(.var 0*.var 0))*efourVector (ev 1) (ev 4) (ev 7) (ev 10))
    (by decide)
    (fun
      | 0 => s
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

private def efactor (e n : PE) : PE := 1+(e*e)*n
private def eden (e na nb nc nd : PE) : PE :=
  ((efactor e na*efactor e nb)*efactor e nc)*efactor e nd
private def epairs (a b c d : VE) : PE :=
  ((edot a b+edot a c)+edot a d)+((edot b c+edot b d)+edot c d)
private def eh2 (na nb nc nd pab pac pad pbc pbd pcd : PE) : PE :=
  4*(((na+nb)+nc)+nd+2*(((pab+pac)+pad)+((pbc+pbd)+pcd)))
private def eh3 (tabc tabd tacd tbcd : PE) : PE := 16*((tabc+tabd)+(tacd+tbcd))
private def eh4 (na nb nc nd pab pac pad pbc pbd pcd f : PE) : PE :=
  -(8*((pab*(nc+nd)+pac*(nb+nd))+pad*(nb+nc)+
    ((pbc*(na+nd)+pbd*(na+nc))+pcd*(na+nb)))) + -(32*f)
private def eh5 (na nb nc nd tabc tabd tacd tbcd : PE) : PE :=
  -(16*((tabc*nd+tabd*nc)+(tacd*nb+tbcd*na)))
private def eh6 (na nb nc nd pab pac pad pbc pbd pcd : PE) : PE :=
  4*((na*nb*nc+na*nb*nd)+(na*nc*nd+nb*nc*nd)) +
  8*((pab*(nc*nd)+pac*(nb*nd))+pad*(nb*nc)+
    ((pbc*(na*nd)+pbd*(na*nc))+pcd*(na*nb)))
private def eexpansion (e na nb nc nd pab pac pad pbc pbd pcd tabc tabd tacd tbcd f : PE) : PE :=
  ((((e*e)*eh2 na nb nc nd pab pac pad pbc pbd pcd+((e*e)*e)*eh3 tabc tabd tacd tbcd)+
    ((e*e)*(e*e))*eh4 na nb nc nd pab pac pad pbc pbd pcd f)+
    (((e*e)*(e*e))*e)*eh5 na nb nc nd tabc tabd tacd tbcd)+
    (((e*e)*(e*e))*(e*e))*eh6 na nb nc nd pab pac pad pbc pbd pcd
private def erawScalar (e na nb nc nd pab pac pad pbc pbd pcd tabc tabd tacd tbcd f : PE) : PE :=
  let s := 2*e
  escalarFormula (1 + -((e*e)*na)) (1 + -((e*e)*nb))
    (1 + -((e*e)*nc)) (1 + -((e*e)*nd))
    ((s*s)*pab) ((s*s)*pac) ((s*s)*pad) ((s*s)*pbc) ((s*s)*pbd) ((s*s)*pcd)
    (((s*s)*s)*tabc) (((s*s)*s)*tabd) (((s*s)*s)*tacd) (((s*s)*s)*tbcd)
    (((s*s)*(s*s))*f)

-- Norms, pair dots, triple determinants and the four-vector scalar are now
-- independent scalar variables. No Hamilton coordinates are expanded here.
private theorem scalar_normal :
    normalize (2*eden (.var 0) (.var 1) (.var 2) (.var 3) (.var 4) +
      -(2*erawScalar (.var 0) (.var 1) (.var 2) (.var 3) (.var 4)
        (.var 5) (.var 6) (.var 7) (.var 8) (.var 9) (.var 10)
        (.var 11) (.var 12) (.var 13) (.var 14) (.var 15))) =
    normalize (eexpansion (.var 0) (.var 1) (.var 2) (.var 3) (.var 4)
      (.var 5) (.var 6) (.var 7) (.var 8) (.var 9) (.var 10)
      (.var 11) (.var 12) (.var 13) (.var 14) (.var 15)) := by decide

private def raw (e : Q') (a : Triple) : RationalQuaternion :=
  ⟨1 + -((e*e)*norm3 a),2*e*a.x,2*e*a.y,2*e*a.z⟩
private def rawWord (e : Q') (a b c d : Triple) : RationalQuaternion :=
  RationalQuaternion.mul (RationalQuaternion.mul
    (RationalQuaternion.mul (raw e a) (raw e b)) (raw e c)) (raw e d)

private def rawScalar (e : Q') (a b c d : Triple) : Q' :=
  let s := 2*e
  scalarFormula (raw e a).r (raw e b).r (raw e c).r (raw e d).r
    ((s*s)*dot3 a b) ((s*s)*dot3 a c) ((s*s)*dot3 a d)
    ((s*s)*dot3 b c) ((s*s)*dot3 b d) ((s*s)*dot3 c d)
    (((s*s)*s)*det3 a b c) (((s*s)*s)*det3 a b d)
    (((s*s)*s)*det3 a c d) (((s*s)*s)*det3 b c d)
    (((s*s)*(s*s))*fourVector a b c d)
private theorem raw_scalar (e : Q') (a b c d : Triple) :
    (rawWord e a b c d).r ≈ rawScalar e a b c d :=
  Q'.eqv_trans _ _ _ (four_scalar (raw e a).r (raw e b).r (raw e c).r (raw e d).r
    (scale3 (2*e) a) (scale3 (2*e) b) (scale3 (2*e) c) (scale3 (2*e) d))
    (scalarFormula_congr _ _ _ _
      (dot_scaled (2*e) a b) (dot_scaled (2*e) a c) (dot_scaled (2*e) a d)
      (dot_scaled (2*e) b c) (dot_scaled (2*e) b d) (dot_scaled (2*e) c d)
      (det_scaled (2*e) a b c) (det_scaled (2*e) a b d)
      (det_scaled (2*e) a c d) (det_scaled (2*e) b c d)
      (fourVector_scaled (2*e) a b c d))

private theorem norm_sum (a b c d : Triple) :
    norm3 (add3 (add3 (add3 a b) c) d) ≈
      (((norm3 a+norm3 b)+norm3 c)+norm3 d)+2*pairDots a b c d := by
  let x := ev 0
  let y := ev 3
  let z := ev 6
  let w := ev 9
  exact poly_identity_of_normal_eq
    (((((x.x+y.x)+z.x)+w.x)*(((x.x+y.x)+z.x)+w.x)+
      (((x.y+y.y)+z.y)+w.y)*(((x.y+y.y)+z.y)+w.y))+
      (((x.z+y.z)+z.z)+w.z)*(((x.z+y.z)+z.z)+w.z))
    ((((edot x x+edot y y)+edot z z)+edot w w)+2*epairs x y z w)
    (by decide)
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

private theorem raw_expansion (e : Q') (a b c d : Triple) :
    2*cayleyDenominator e a b c d + -(2*(rawWord e a b c d).r) ≈
      cayleyDeficit e a b c d := by
  have h := poly_identity_of_normal_eq _ _ scalar_normal
    (fun
      | 0 => e
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
      | _ => fourVector a b c d)
  have h2 :
      4*((((norm3 a+norm3 b)+norm3 c)+norm3 d)+2*pairDots a b c d) ≈ H2 a b c d :=
    mc (Q'.eqv_refl 4) (Q'.eqv_symm (norm_sum a b c d))
  exact Q'.eqv_trans _ _ _
    (ac (Q'.eqv_refl _) (nc (mc (Q'.eqv_refl 2) (raw_scalar e a b c d))))
    (Q'.eqv_trans _ _ _ h
      (ac (ac (ac (ac (mc (Q'.eqv_refl _) h2) (Q'.eqv_refl _))
        (Q'.eqv_refl _)) (Q'.eqv_refl _)) (Q'.eqv_refl _)))

private def qscale (d : Q') (q : RationalQuaternion) : RationalQuaternion :=
  ⟨d*q.r,d*q.i,d*q.j,d*q.k⟩
private def eqtrans {a b c : RationalQuaternion} (h : a.Equivalent b)
    (k : b.Equivalent c) : a.Equivalent c :=
  ⟨Q'.eqv_trans _ _ _ h.1 k.1,Q'.eqv_trans _ _ _ h.2.1 k.2.1,
    Q'.eqv_trans _ _ _ h.2.2.1 k.2.2.1,Q'.eqv_trans _ _ _ h.2.2.2 k.2.2.2⟩
private def eqsymm {a b : RationalQuaternion} (h : a.Equivalent b) : b.Equivalent a :=
  ⟨Q'.eqv_symm h.1,Q'.eqv_symm h.2.1,Q'.eqv_symm h.2.2.1,Q'.eqv_symm h.2.2.2⟩

private theorem scaled_product (d f x y : Q') :
    (d*x)*(f*y) ≈ (d*f)*(x*y) :=
  poly_identity_of_normal_eq ((.var 0*.var 2)*(.var 1*.var 3))
    ((.var 0*.var 1)*(.var 2*.var 3)) (by decide)
    (fun
      | 0 => d
      | 1 => f
      | 2 => x
      | _ => y)

private theorem scaled_add (s : Q') {x y x' y' : Q'}
    (h : x ≈ s*x') (k : y ≈ s*y') : x+y ≈ s*(x'+y') :=
  Q'.eqv_trans _ _ _ (ac h k) (Q'.eqv_symm (Q'.mul_add_eqv s x' y'))

private theorem scaled_neg (s : Q') {x x' : Q'} (h : x ≈ s*x') : -x ≈ s*(-x') :=
  Q'.eqv_trans _ _ _ (nc h)
    (poly_identity_of_normal_eq (-((.var 0)*(.var 1))) (.var 0* -(.var 1))
      (by decide) (fun | 0 => s | _ => x'))

-- Bilinearity is assembled one signed scalar term at a time. No reflected
-- four-coordinate tuple or large definitional reduction is needed here.
private theorem scaled_mul (d f : Q') (a b : RationalQuaternion) :
    (RationalQuaternion.mul (qscale d a) (qscale f b)).Equivalent
      (qscale (d*f) (RationalQuaternion.mul a b)) := by
  have hp (x y : Q') : (d*x)*(f*y) ≈ (d*f)*(x*y) := scaled_product d f x y
  exact ⟨scaled_add (d*f)
      (scaled_add (d*f) (hp a.r b.r) (scaled_neg (d*f) (hp a.i b.i)))
      (scaled_add (d*f) (scaled_neg (d*f) (hp a.j b.j)) (scaled_neg (d*f) (hp a.k b.k))),
    scaled_add (d*f)
      (scaled_add (d*f) (hp a.r b.i) (hp a.i b.r))
      (scaled_add (d*f) (hp a.j b.k) (scaled_neg (d*f) (hp a.k b.j))),
    scaled_add (d*f)
      (scaled_add (d*f) (hp a.r b.j) (scaled_neg (d*f) (hp a.i b.k)))
      (scaled_add (d*f) (hp a.j b.r) (hp a.k b.i)),
    scaled_add (d*f)
      (scaled_add (d*f) (hp a.r b.k) (hp a.i b.j))
      (scaled_add (d*f) (scaled_neg (d*f) (hp a.j b.i)) (hp a.k b.r))⟩

private theorem clear_mul {d f : Q'} {a b p q : RationalQuaternion}
    (h : (qscale d a).Equivalent p) (k : (qscale f b).Equivalent q) :
    (qscale (d*f) (RationalQuaternion.mul a b)).Equivalent (RationalQuaternion.mul p q) :=
  eqtrans (eqsymm (scaled_mul d f a b)) (RationalQuaternion.mul_congr h k)

private theorem norm_scaled (e : Q') (a : Triple) :
    norm3 (scale3 e a) ≈ (e*e)*norm3 a :=
  poly_identity_of_normal_eq
    (((.var 0*.var 1)*(.var 0*.var 1)+(.var 0*.var 2)*(.var 0*.var 2))+
      (.var 0*.var 3)*(.var 0*.var 3))
    ((.var 0*.var 0)*((.var 1*.var 1+.var 2*.var 2)+.var 3*.var 3))
    (by decide) (fun | 0 => e | 1 => a.x | 2 => a.y | _ => a.z)

private theorem clear_coordinate (d r x y : Q') (h : d*r ≈ 1) (k : x ≈ y) :
    d*(r*x) ≈ y :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv d r x))
    (Q'.eqv_trans _ _ _ (mc h k) (Q'.one_mul_eqv y))

private theorem chart_clear (e : Q') (a : Triple) :
    (qscale (factor e a) (stereographic (scale3 e a)).val).Equivalent (raw e a) := by
  have hd : denominator (scale3 e a) ≈ factor e a := ac (Q'.eqv_refl 1) (norm_scaled e a)
  have hr : factor e a*Q'.recipPos (denominator (scale3 e a))
      (denominator_positive (scale3 e a)) ≈ 1 :=
    Q'.eqv_trans _ _ _ (mc (Q'.eqv_symm hd) (Q'.eqv_refl _))
      (Q'.mul_recipPos_eqv _ _)
  have ha (x : Q') : 2*(e*x) ≈ 2*e*x := Q'.eqv_symm (Q'.mul_assoc_eqv 2 e x)
  exact ⟨clear_coordinate _ _ _ _ hr (ac (Q'.eqv_refl 1) (nc (norm_scaled e a))),
    clear_coordinate _ _ _ _ hr (ha a.x),clear_coordinate _ _ _ _ hr (ha a.y),
    clear_coordinate _ _ _ _ hr (ha a.z)⟩

private theorem neg_norm (a : Triple) : norm3 (neg3 a) ≈ norm3 a :=
  poly_identity_of_normal_eq
    ((-(.var 0)* -(.var 0)+ -(.var 1)* -(.var 1))+ -(.var 2)* -(.var 2))
    ((.var 0*.var 0+.var 1*.var 1)+.var 2*.var 2)
    (by decide) (fun | 0 => a.x | 1 => a.y | _ => a.z)

private theorem neg_mul (d x : Q') : d*(-x) ≈ -(d*x) :=
  poly_identity_of_normal_eq (.var 0* -(.var 1)) (-((.var 0)*(.var 1)))
    (by decide) (fun | 0 => d | _ => x)

private theorem inverse_chart_clear (e : Q') (a : Triple) :
    (qscale (factor e (neg3 a)) (UnitNorm.inv (stereographic (scale3 e a))).val).Equivalent
      (raw e (neg3 a)) := by
  have hf : factor e (neg3 a) ≈ factor e a := ac (Q'.eqv_refl 1)
    (mc (Q'.eqv_refl _) (neg_norm a))
  have hc := chart_clear e a
  have hn (x y : Q') (h : factor e a*x ≈ y) : factor e (neg3 a)*(-x) ≈ -y :=
    Q'.eqv_trans _ _ _ (mc hf (Q'.eqv_refl _))
      (Q'.eqv_trans _ _ _ (neg_mul _ _) (nc h))
  have hi (x : Q') : -(2*e*x) ≈ 2*e*(-x) := Q'.eqv_symm (neg_mul (2*e) x)
  exact ⟨Q'.eqv_trans _ _ _ (mc hf (Q'.eqv_refl _))
      (Q'.eqv_trans _ _ _ hc.1
        (ac (Q'.eqv_refl 1) (nc (mc (Q'.eqv_refl _) (Q'.eqv_symm (neg_norm a)))))),
    Q'.eqv_trans _ _ _ (hn _ _ hc.2.1) (hi a.x),
    Q'.eqv_trans _ _ _ (hn _ _ hc.2.2.1) (hi a.y),
    Q'.eqv_trans _ _ _ (hn _ _ hc.2.2.2) (hi a.z)⟩

/-- Exact cleared trace deficit of the actual left-associated stereographic
plaquette word. The directed vectors are a,b,-c,-d; e may be any rational. -/
theorem plaquetteWord_cayley_cleared (e : Q') (a b c d : Triple) :
    cayleyDenominator e a b (neg3 c) (neg3 d)*
      (2 + -(2*(plaquetteWord (stereographic (scale3 e a)) (stereographic (scale3 e b))
        (stereographic (scale3 e c)) (stereographic (scale3 e d))).val.r)) ≈
    cayleyDeficit e a b (neg3 c) (neg3 d) := by
  have hword := clear_mul (clear_mul (clear_mul (chart_clear e a) (chart_clear e b))
    (inverse_chart_clear e c)) (inverse_chart_clear e d)
  have hscalar : cayleyDenominator e a b (neg3 c) (neg3 d)*
      (plaquetteWord (stereographic (scale3 e a)) (stereographic (scale3 e b))
        (stereographic (scale3 e c)) (stereographic (scale3 e d))).val.r ≈
      (rawWord e a b (neg3 c) (neg3 d)).r := hword.1
  have hdistribute (x y : Q') : x*(2 + -(2*y)) ≈ 2*x + -(2*(x*y)) :=
    poly_identity_of_normal_eq (.var 0*(2 + -(2*.var 1)))
      (2*.var 0 + -(2*(.var 0*.var 1))) (by decide) (fun | 0 => x | _ => y)
  exact Q'.eqv_trans _ _ _ (hdistribute _ _)
    (Q'.eqv_trans _ _ _ (ac (Q'.eqv_refl _) (nc (mc (Q'.eqv_refl 2) hscalar)))
      (raw_expansion e a b (neg3 c) (neg3 d)))

/-- The SAME original corrected-slab scalar, under four explicit chart pins.
No distinct-link, independence, membership, measure, or expansion premise is
assumed. The original linkValue fallback and all repeated occurrences remain. -/
theorem original_plaquette_cayley_cleared (extent : Nat) (qs : Nat → UnitNorm)
    (face : Z4Plaq) (e : Q') (a b c d : Triple)
    (ha : (linkValue extent qs (face.1,(dirsOf face.2).1)).Equivalent
      (stereographic (scale3 e a)))
    (hb : (linkValue extent qs (addE face.1 (dirsOf face.2).1,(dirsOf face.2).2)).Equivalent
      (stereographic (scale3 e b)))
    (hc : (linkValue extent qs (addE face.1 (dirsOf face.2).2,(dirsOf face.2).1)).Equivalent
      (stereographic (scale3 e c)))
    (hd : (linkValue extent qs (face.1,(dirsOf face.2).2)).Equivalent
      (stereographic (scale3 e d))) :
    cayleyDenominator e a b (neg3 c) (neg3 d)*
      (2 + -(2*evalRatPoly (environment qs)
        (correctedSlabPlaquettePolynomial extent face).scalar)) ≈
    cayleyDeficit e a b (neg3 c) (neg3 d) := by
  have hword : (plaquetteValue extent qs face).Equivalent
      (plaquetteWord (stereographic (scale3 e a)) (stereographic (scale3 e b))
        (stereographic (scale3 e c)) (stereographic (scale3 e d))) :=
    UnitNorm.mul_congr (UnitNorm.mul_congr (UnitNorm.mul_congr ha hb)
      (UnitNorm.inv_congr hc)) (UnitNorm.inv_congr hd)
  have hscalar := Q'.eqv_trans _ _ _ (plaquette_scalar_pin extent qs face) hword.1
  exact Q'.eqv_trans _ _ _ (mc (Q'.eqv_refl _)
    (ac (Q'.eqv_refl 2) (nc (mc (Q'.eqv_refl 2) hscalar))))
    (plaquetteWord_cayley_cleared e a b c d)

end YMGap.Continuum.BF4ExactSlabPlaquetteCayleyExpansion

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCayleyExpansion.plaquetteWord_cayley_cleared
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCayleyExpansion.original_plaquette_cayley_cleared
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCayleyExpansion.H3_dot_cross
