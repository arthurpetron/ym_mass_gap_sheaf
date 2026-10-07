/-
# Torus RP bridge, items 2–3: crossing-word and reflected-plaquette scalar identities

These are coefficient-level identities (`RatPolyCoeffEqv`) for arbitrary `PolyQuaternion`s. They are derived by
chaining `PolyQuaternionCoeffEqv.mul_assoc` with four small normalizer lemmas on at most 2 quaternions (8 variables,
degree 2), with no big `decide`:
* `conj_mul : conj(q r) ≅ conj r · conj q`, `conj_conj : conj(conj q) ≅ q`;
* `scalar_comm : Re(q r) ≅ Re(r q)`;
* `scalar_mul_conj : Re(X · conj Y) ≅ Σ_c X_c Y_c` (`dot`).

Results:
* **(2) crossing word, cut 1** (`cross_word_cut1`): the plaquette word `V·L'·U*·L*` with the split links
  `L = A*·B` and `L' = A'*·B'` has `Re ≅ dot X Y`, where `X = (A·V)·A'*` and `Y = (B·U)·B'*`.
  Under Θ: B ↦ A, U ↦ V, B' ↦ A', so `X = Θ Y`.
* **(3) reflected plaquette** (`refl_word`): `Re((c·b*)·(a*·(d*)*)) ≅ Re((a·b)·(c*·d*))`. The reflected copy of a
  positive temporal plaquette `(a·b)·(c*·d*)`, with reflected temporal links stored as conjugates, has the same
  scalar as the original word in the reflected variables.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN** (bridge item 4 is not landed). Valid for every coupling.
-/

import YMGap.Continuum.SU2TorusRPSplitSel
import YMGap.Continuum.SU2CharacterSquareIdentity

namespace YMGap.Continuum.SU2TorusRPWord

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

local infix:50 " ≅ " => RatPolyCoeffEqv
local infix:50 " ≅q " => PolyQuaternionCoeffEqv

open PolyQuaternion (mul conj)

def env2 (q r : PolyQuaternion) : Nat → RatPoly
  | 0 => q.scalar | 1 => q.iPart | 2 => q.jPart | 3 => q.kPart
  | 4 => r.scalar | 5 => r.iPart | 6 => r.jPart | 7 => r.kPart
  | _ => polyZero

abbrev E0 := PolyQuaternionExpr.coordinate 0
abbrev E4 := PolyQuaternionExpr.coordinate 4

theorem conj_mul (q r : PolyQuaternion) : conj (mul q r) ≅q mul (conj r) (conj q) := by
  let L := PolyQuaternionExpr.conj (PolyQuaternionExpr.mul E0 E4)
  let R := PolyQuaternionExpr.mul (PolyQuaternionExpr.conj E4) (PolyQuaternionExpr.conj E0)
  constructor
  · simpa [L, R, PolyQuaternionExpr.mul, PolyQuaternionExpr.conj, PolyQuaternionExpr.coordinate, coeffEvalExpr,
      env2, mul, conj] using coeffEvalExpr_eqv_of_normalize_eq L.scalar R.scalar (by decide) (env2 q r)
  · simpa [L, R, PolyQuaternionExpr.mul, PolyQuaternionExpr.conj, PolyQuaternionExpr.coordinate, coeffEvalExpr,
      env2, mul, conj] using coeffEvalExpr_eqv_of_normalize_eq L.iPart R.iPart (by decide) (env2 q r)
  · simpa [L, R, PolyQuaternionExpr.mul, PolyQuaternionExpr.conj, PolyQuaternionExpr.coordinate, coeffEvalExpr,
      env2, mul, conj] using coeffEvalExpr_eqv_of_normalize_eq L.jPart R.jPart (by decide) (env2 q r)
  · simpa [L, R, PolyQuaternionExpr.mul, PolyQuaternionExpr.conj, PolyQuaternionExpr.coordinate, coeffEvalExpr,
      env2, mul, conj] using coeffEvalExpr_eqv_of_normalize_eq L.kPart R.kPart (by decide) (env2 q r)

theorem negneg (p : RatPoly) : polyNeg (polyNeg p) ≅ p := by
  have h := coeffEvalExpr_eqv_of_normalize_eq (.neg (.neg (.var 0))) (.var 0) (by decide) (fun _ => p)
  simpa [coeffEvalExpr] using h

theorem conj_conj (q : PolyQuaternion) : conj (conj q) ≅q q :=
  ⟨RatPolyCoeffEqv.refl _, negneg _, negneg _, negneg _⟩

theorem scalar_comm (q r : PolyQuaternion) : (mul q r).scalar ≅ (mul r q).scalar := by
  let L := PolyQuaternionExpr.mul E0 E4
  let R := PolyQuaternionExpr.mul E4 E0
  simpa [L, R, PolyQuaternionExpr.mul, PolyQuaternionExpr.coordinate, coeffEvalExpr, env2, mul] using
    coeffEvalExpr_eqv_of_normalize_eq L.scalar R.scalar (by decide) (env2 q r)

/-- `Σ_c X_c Y_c`. -/
def dot (X Y : PolyQuaternion) : RatPoly :=
  polyAdd (polyMul X.scalar Y.scalar)
    (polyAdd (polyMul X.iPart Y.iPart) (polyAdd (polyMul X.jPart Y.jPart) (polyMul X.kPart Y.kPart)))

theorem scalar_mul_conj (X Y : PolyQuaternion) : (mul X (conj Y)).scalar ≅ dot X Y := by
  let L := PolyQuaternionExpr.mul E0 (PolyQuaternionExpr.conj E4)
  let R : PolyExpr := .add (.mul (.var 0) (.var 4)) (.add (.mul (.var 1) (.var 5))
    (.add (.mul (.var 2) (.var 6)) (.mul (.var 3) (.var 7))))
  simpa [L, R, PolyQuaternionExpr.mul, PolyQuaternionExpr.conj, PolyQuaternionExpr.coordinate, coeffEvalExpr,
    env2, mul, conj, dot] using coeffEvalExpr_eqv_of_normalize_eq L.scalar R (by decide) (env2 X Y)

/-! ## Chaining helpers -/

theorem qrefl (q : PolyQuaternion) : q ≅q q := PolyQuaternionCoeffEqv.refl q
theorem qmul {a a' b b' : PolyQuaternion} (h : a ≅q a') (h' : b ≅q b') : mul a b ≅q mul a' b' :=
  PolyQuaternionCoeffEqv.mul h h'
theorem qassoc (a b c : PolyQuaternion) : mul (mul a b) c ≅q mul a (mul b c) :=
  PolyQuaternionCoeffEqv.mul_assoc a b c
theorem qtrans {a b c : PolyQuaternion} (h : a ≅q b) (h' : b ≅q c) : a ≅q c := PolyQuaternionCoeffEqv.trans h h'
theorem qsymm {a b : PolyQuaternion} (h : a ≅q b) : b ≅q a := PolyQuaternionCoeffEqv.symm h

/-- **(2) Crossing word at cut 1.** -/
theorem cross_word_cut1 (V U A A' B B' : PolyQuaternion) :
    (mul (mul V (mul (conj A') B')) (mul (conj U) (conj (mul (conj A) B)))).scalar ≅
      dot (mul (mul A V) (conj A')) (mul (mul B U) (conj B')) := by
  let G := mul V (conj A')
  let H := mul B' (mul (conj U) (conj B))
  -- conj(A*·B) ≅ B*·A
  have hc : conj (mul (conj A) B) ≅q mul (conj B) A :=
    qtrans (conj_mul _ _) (qmul (qrefl _) (conj_conj A))
  -- W ≅ (G·H)·A
  have hW : mul (mul V (mul (conj A') B')) (mul (conj U) (conj (mul (conj A) B))) ≅q mul (mul G H) A := by
    refine qtrans (qmul (qsymm (qassoc V (conj A') B')) (qmul (qrefl _) hc)) ?_
    refine qtrans (qassoc G B' _) ?_
    refine qtrans (qmul (qrefl G) (qmul (qrefl B') (qsymm (qassoc (conj U) (conj B) A)))) ?_
    refine qtrans (qmul (qrefl G) (qsymm (qassoc B' (mul (conj U) (conj B)) A))) ?_
    exact qsymm (qassoc G H A)
  -- conj Y ≅ H
  have hY : conj (mul (mul B U) (conj B')) ≅q H :=
    qtrans (conj_mul _ _) (qtrans (qmul (conj_conj B') (conj_mul B U)) (qrefl _))
  refine hW.scalar.trans ((scalar_comm _ _).trans ?_)
  refine (qsymm (qassoc A G H)).scalar.trans ?_
  have hX : mul (mul A G) H ≅q mul (mul (mul A V) (conj A')) (conj (mul (mul B U) (conj B'))) :=
    qmul (qsymm (qassoc A V (conj A'))) (qsymm hY)
  exact hX.scalar.trans (scalar_mul_conj _ _)

/-- **(2') Crossing word at cut 2:** `U·L'·V*·L*` with `L = B·A*`, `L' = B'·A'*`. -/
theorem cross_word_cut2 (V U A A' B B' : PolyQuaternion) :
    (mul (mul U (mul B' (conj A'))) (mul (conj V) (conj (mul B (conj A))))).scalar ≅
      dot (mul (mul (conj B) U) B') (mul (mul (conj A) V) A') := by
  let G := mul U B'
  let K := mul (conj A') (mul (conj V) A)
  have hc : conj (mul B (conj A)) ≅q mul A (conj B) :=
    qtrans (conj_mul _ _) (qmul (conj_conj A) (qrefl _))
  have hW : mul (mul U (mul B' (conj A'))) (mul (conj V) (conj (mul B (conj A)))) ≅q mul (mul G K) (conj B) := by
    refine qtrans (qmul (qsymm (qassoc U B' (conj A'))) (qmul (qrefl _) hc)) ?_
    refine qtrans (qassoc G (conj A') _) ?_
    refine qtrans (qmul (qrefl G) (qmul (qrefl _) (qsymm (qassoc (conj V) A (conj B))))) ?_
    refine qtrans (qmul (qrefl G) (qsymm (qassoc (conj A') (mul (conj V) A) (conj B)))) ?_
    exact qsymm (qassoc G K (conj B))
  have hX : conj (mul (mul (conj A) V) A') ≅q K :=
    qtrans (conj_mul _ _) (qmul (qrefl _) (qtrans (conj_mul _ _) (qmul (qrefl _) (conj_conj A))))
  refine hW.scalar.trans ((scalar_comm _ _).trans ?_)
  refine (qsymm (qassoc (conj B) G K)).scalar.trans ?_
  have hY : mul (mul (conj B) G) K ≅q mul (mul (mul (conj B) U) B') (conj (mul (mul (conj A) V) A')) :=
    qmul (qsymm (qassoc (conj B) U B')) (qsymm hX)
  exact hY.scalar.trans (scalar_mul_conj _ _)

end YMGap.Continuum.SU2TorusRPWord

#print axioms YMGap.Continuum.SU2TorusRPWord.cross_word_cut1
#print axioms YMGap.Continuum.SU2TorusRPWord.cross_word_cut2
