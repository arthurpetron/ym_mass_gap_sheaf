/-
# Torus RP (e1): link observables and the `hW` target statement

`Obs` is a syntax of polynomial observables in link-quaternion coordinates, and `evalI img e` evaluates it with link
images `img`. `sub_evalI`: a `RingSub` that sends each used link variable to `img'` sends `evalI img e` to
`evalI img' e` (PE). `rcomp_obs`: the composed torus→layout reindexing turns `eval torusLinks e` into
`eval layout e`.

`TorusRP M hM β K` is the **target statement for `hW`**, using `T_K` with `wilsonA`, as in `SU2TorusRPKernel`'s
`tkProd`/`hW`. It states that for every observable `e` on positive links,
`0 ≤ ∫_{|torusLinks|} Θ(e)·e·Π_{torusPlaquettes} T_K[torusLinks]`, where Θ = `thetaPoly` on `torusLinks (2M)`.
It is stated here and **not proved**.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**
-/

import YMGap.Continuum.SU2TorusRPTorusX
import YMGap.Continuum.SU2TorusRPThetaTK

namespace YMGap.Continuum.SU2TorusRPObs

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.SU2HaarAlgebra (PE pe_trans pe_refl pe_append)
open YMGap.Continuum.SU2HaarL1Activity (prodPoly)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.SU2TorusRPSubst (RingSub QPE qsub pe_mul2 pe_neg pe_smul)
open YMGap.Continuum.SU2TorusRPGeom (reflLink)
open YMGap.Continuum.SU2TorusRPChoosePC (Pt Ct)
open YMGap.Continuum.SU2TorusMultiLinkPolyGibbs (linkVar)

inductive Obs
  | const (c : Q')
  | var (ℓ : Z4Link) (k : Nat)
  | add (a b : Obs)
  | mul (a b : Obs)
  | neg (a : Obs)

/-- Component `k` of a polynomial quaternion (`0` scalar, `1` i, `2` j, otherwise k). -/
def comp (q : PolyQuaternion) : Nat → RatPoly
  | 0 => q.scalar
  | 1 => q.iPart
  | 2 => q.jPart
  | _ => q.kPart

def evalI (img : Z4Link → PolyQuaternion) : Obs → RatPoly
  | .const c => polySmul c polyOne
  | .var ℓ k => comp (img ℓ) k
  | .add a b => polyAdd (evalI img a) (evalI img b)
  | .mul a b => polyMul (evalI img a) (evalI img b)
  | .neg a => polyNeg (evalI img a)

/-- Evaluation in the link order `L`. -/
def eval (L : List Z4Link) (e : Obs) : RatPoly := evalI (linkVar L) e

def OnLinks (P : Z4Link → Prop) : Obs → Prop
  | .const _ => True
  | .var ℓ _ => P ℓ
  | .add a b => OnLinks P a ∧ OnLinks P b
  | .mul a b => OnLinks P a ∧ OnLinks P b
  | .neg a => OnLinks P a

theorem comp_qpe {n : Nat} {q r : PolyQuaternion} (h : QPE n q r) : ∀ k, PE n (comp q k) (comp r k)
  | 0 => h.s
  | 1 => h.i
  | 2 => h.j
  | _ + 3 => h.k

theorem sub_evalI {n : Nat} {S : RatPoly → RatPoly} (hS : RingSub n S) (P : Z4Link → Prop)
    (img img' : Z4Link → PolyQuaternion) (himg : ∀ ℓ, P ℓ → QPE n (qsub S (img ℓ)) (img' ℓ)) :
    ∀ e : Obs, OnLinks P e → PE n (S (evalI img e)) (evalI img' e)
  | .const c, _ => pe_trans n (hS.smul c polyOne) (pe_smul n c hS.one)
  | .var ℓ k, h => by
    have := comp_qpe (himg ℓ h) k
    cases k with
    | zero => exact this
    | succ k => cases k with
      | zero => exact this
      | succ k => cases k with
        | zero => exact this
        | succ k => exact this
  | .add a b, h => pe_trans n (hS.add _ _)
      (pe_append n (sub_evalI hS P img img' himg a h.1) (sub_evalI hS P img img' himg b h.2))
  | .mul a b, h => pe_trans n (hS.mul _ _)
      (pe_mul2 n (sub_evalI hS P img img' himg a h.1) (sub_evalI hS P img img' himg b h.2))
  | .neg a, h => pe_trans n (hS.neg _) (pe_neg n (sub_evalI hS P img img' himg a h))

variable {M : Nat} (hM : 1 ≤ M)

/-- The composed torus→layout reindexing transports torus-order observables to layout-order ones. -/
theorem rcomp_obs (r : List (YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection.QuaternionBlockInvolution
      (torusLinks (2 * M)).length))
    (hr : ∀ ℓ, YMGap.Continuum.SU2TorusRPPermX.imap r ((torusLinks (2 * M)).idxOf ℓ) =
      (Pt M ++ Ct M ++ (Pt M).map (reflLink M)).idxOf ℓ)
    (e : Obs) (he : OnLinks (· ∈ torusLinks (2 * M)) e) :
    PE (torusLinks (2 * M)).length (YMGap.Continuum.SU2TorusRPPermX.rcomp r (eval (torusLinks (2 * M)) e))
      (eval (Pt M ++ Ct M ++ (Pt M).map (reflLink M)) e) :=
  sub_evalI (YMGap.Continuum.SU2TorusRPPermCoord.rcomp_ringSub r) _ _ _ (fun ℓ hℓ => by
    have := (YMGap.Continuum.SU2TorusRPPermCoord.rcomp_coord r _
      (YMGap.Continuum.SU2TorusRPSwap.idx_lt ℓ _ hℓ)).2
    unfold linkVar; rw [← hr ℓ]; exact this) e he

theorem tl_box (ℓ : Z4Link) (h : ℓ ∈ torusLinks (2 * M)) : InBox (2 * M) ℓ.1 :=
  (YMGap.Continuum.SU2TorusRPTorusZ.mem_tl ℓ).1 h

include hM in
theorem tl_cl (ℓ : Z4Link) (h : ℓ ∈ torusLinks (2 * M)) : reflLink M ℓ ∈ torusLinks (2 * M) :=
  (YMGap.Continuum.SU2TorusRPTorusZ.mem_tl _).2 (YMGap.Continuum.SU2TorusRPMirGeom.refl_box hM ℓ (tl_box ℓ h))

/-- The torus Θ on `torusLinks (2M)` order. -/
def thetaT (X : RatPoly) : RatPoly :=
  YMGap.Continuum.SU2TorusRPThetaTK.thetaPoly hM (torusLinks (2 * M)) (torusLinks_nodup _) tl_box (tl_cl hM) X

/-- **Target statement for `hW` (NOT PROVED):** RP for the actual torus `T_K` measure (`wilsonA` weights), with
observables on positive links. -/
def TorusRP (β : Q') (K : Nat) : Prop :=
  ∀ e : Obs, OnLinks (· ∈ Pt M) e →
    (0 : Q') ≤ quaternionHaar (torusLinks (2 * M)).length
      (polyMul (polyMul (thetaT hM (eval (torusLinks (2 * M)) e)) (eval (torusLinks (2 * M)) e))
        (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK (torusLinks (2 * M)) (2 * M) β K)
          (torusPlaquettes (2 * M))))

end YMGap.Continuum.SU2TorusRPObs

#print axioms YMGap.Continuum.SU2TorusRPObs.sub_evalI
#print axioms YMGap.Continuum.SU2TorusRPObs.rcomp_obs
#print axioms YMGap.Continuum.SU2TorusRPObs.TorusRP
