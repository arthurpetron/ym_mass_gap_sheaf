/-
# Torus RP (d4d): the split acting on the actual torus `Π T_K`

For any `RingSub` `S` on `n` blocks with known coordinate images `img b` (`b < n`), `S (Π_ps T_K)` is PE to the
product of `T_K` of the image words (`subst_prod`). For a Haar-invariant split chain this gives
`∫ Π_ps T_K = ∫ Π_ps T_K[img]` (`split_prod_haar`) — the crossing split on the concrete integrand, with
`img` = `U_s ↦ U_m* U_s` from `step_coord_sel`/`step_coord_other`.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**
-/

import YMGap.Continuum.SU2TorusRPStepCoord

namespace YMGap.Continuum.SU2TorusRPSplitTK

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2HaarAlgebra (PE pe_refl pe_trans)
open YMGap.Continuum.SU2HaarL1Activity (prodPoly)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.SU2TorusRPSubst (RingSub QPE qsub qpe_trans qpe_mul qpe_conj pe_mul2 TK_word_sub prodPoly_sub
  wilsonPoly_pe)
open YMGap.Continuum.SU2TorusMultiLinkPolyGibbs (linkVar plaqWord)
open YMGap.Continuum.SU2WilsonCharacterPower (wilsonPoly)
open YMGap.Continuum.SU2WilsonActivity (wilsonA)
open PolyQuaternion (mul conj)

variable {n : Nat} (links : List Z4Link) (N : Nat) (β : Q') (K : Nat)

/-- The four link indices of a plaquette. -/
def plaqIdx (p : Z4Plaq) : List Nat :=
  [links.idxOf (p.1, (dirsOf p.2).1), links.idxOf (tAdd N p.1 (dirsOf p.2).1, (dirsOf p.2).2),
   links.idxOf (tAdd N p.1 (dirsOf p.2).2, (dirsOf p.2).1), links.idxOf (p.1, (dirsOf p.2).2)]

/-- Image plaquette word. -/
def imgWord (img : Nat → PolyQuaternion) (p : Z4Plaq) : PolyQuaternion :=
  mul (mul (img (links.idxOf (p.1, (dirsOf p.2).1))) (img (links.idxOf (tAdd N p.1 (dirsOf p.2).1, (dirsOf p.2).2))))
    (mul (conj (img (links.idxOf (tAdd N p.1 (dirsOf p.2).2, (dirsOf p.2).1))))
      (conj (img (links.idxOf (p.1, (dirsOf p.2).2)))))

def imgTK (img : Nat → PolyQuaternion) (p : Z4Plaq) : RatPoly :=
  wilsonPoly (imgWord links N img p).scalar (wilsonA β) K

theorem prod_congr {F G : Z4Plaq → RatPoly} : ∀ ps : List Z4Plaq, (∀ p ∈ ps, PE n (F p) (G p)) →
    PE n (prodPoly F ps) (prodPoly G ps)
  | [], _ => pe_refl _ _
  | p :: ps, h => pe_mul2 n (h p (List.mem_cons_self ..)) (prod_congr ps fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem subst_TK {S : RatPoly → RatPoly} (hS : RingSub n S) (img : Nat → PolyQuaternion)
    (himg : ∀ b, b < n → QPE n (qsub S (PolyQuaternion.coordinateVariable b)) (img b))
    (p : Z4Plaq) (hp : ∀ b ∈ plaqIdx links N p, b < n) :
    PE n (S (YMGap.Continuum.SU2WilsonPolymerIdentity.TK links N β K p)) (imgTK links N β K img p) := by
  unfold YMGap.Continuum.SU2WilsonPolymerIdentity.TK imgTK plaqWord
  refine pe_trans n (TK_word_sub hS _ _ _ _ _ K) (wilsonPoly_pe n ?_ _ K)
  have h1 := himg _ (hp _ (List.mem_cons_self ..))
  have h2 := himg _ (hp _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have h3 := himg _ (hp _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
  have h4 := himg _ (hp _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_self ..)))))
  exact (qpe_mul (qpe_mul h1 h2) (qpe_mul (qpe_conj h3) (qpe_conj h4))).s

theorem subst_prod {S : RatPoly → RatPoly} (hS : RingSub n S) (img : Nat → PolyQuaternion)
    (himg : ∀ b, b < n → QPE n (qsub S (PolyQuaternion.coordinateVariable b)) (img b))
    (ps : List Z4Plaq) (hps : ∀ p ∈ ps, ∀ b ∈ plaqIdx links N p, b < n) :
    PE n (S (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK links N β K) ps))
      (prodPoly (imgTK links N β K img) ps) :=
  pe_trans n (prodPoly_sub hS _ ps) (prod_congr ps fun p hp => subst_TK links N β K hS img himg p (hps p hp))

/-- **Concrete split on the torus `Π T_K`** for any Haar-invariant ring substitution. -/
theorem split_prod_haar {S : RatPoly → RatPoly} (hS : RingSub n S) (ps : List Z4Plaq)
    (hinv : (quaternionHaar n (S (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK links N β K) ps))).eqv
      (quaternionHaar n (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK links N β K) ps)))
    (img : Nat → PolyQuaternion)
    (himg : ∀ b, b < n → QPE n (qsub S (PolyQuaternion.coordinateVariable b)) (img b))
    (hps : ∀ p ∈ ps, ∀ b ∈ plaqIdx links N p, b < n) :
    (quaternionHaar n (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK links N β K) ps)).eqv
      (quaternionHaar n (prodPoly (imgTK links N β K img) ps)) :=
  YMGap.Continuum.SU2TorusRPCompOn.haar_step S hinv (subst_prod links N β K hS img himg ps hps)

end YMGap.Continuum.SU2TorusRPSplitTK

#print axioms YMGap.Continuum.SU2TorusRPSplitTK.subst_prod
#print axioms YMGap.Continuum.SU2TorusRPSplitTK.split_prod_haar
