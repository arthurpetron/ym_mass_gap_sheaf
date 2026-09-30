/-
Explicit original-carrier representatives for supplied dyadic mesh actions.
Every representative is a computed diagonal of witnessed Cauchy rows; no
representative of an arbitrary quotient-valued sequence is selected.
-/

import YMGap.Continuum.BF4WilsonAllNomeDyadicSemigroup
import YMGap.Continuum.BF4WilsonAllNomeNestedRootCompatibility

namespace YMGap.Continuum.BF4WilsonAllNomeDyadicRepresentatives

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.NonnegativeDyadicTime
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (Completion)
open YMGap.Continuum.BF4WilsonAllNomeDistance (distanceData)
open YMGap.Continuum.BF4WilsonAllNomeNestedRootBasics (root)
open YMGap.Continuum.BF4WilsonAllNomeNestedRootCompatibility (rootRows limit_rootRows)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSemigroup

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))

/-- The root-row diagonal is an actual `D.Cauchy`, with both rates retained. -/
def rootRepresentative (k : Nat) (X : (D).Cauchy) : (D).Cauchy :=
  CRealSeminormCauchyRows.diagonalCauchy (distanceData hw0 hw1 (width := width))
    (rootRows hw0 hw1 k X)

theorem rootRepresentative_pin (k : Nat) (X : (D).Cauchy) :
    Class (rootRepresentative hw0 hw1 k X) =
      root hw0 hw1 k (Class X) := by
  change BF4WilsonAllNomeCauchyRows.limit hw0 hw1 (rootRows hw0 hw1 k X) = _
  exact limit_rootRows hw0 hw1 k X

/-- Finite iteration of computed root representatives, at one supplied mesh. -/
def meshRepresentative (depth : Nat) : Nat → (D).Cauchy → (D).Cauchy
  | 0, X => X
  | steps + 1, X => rootRepresentative hw0 hw1 depth
      (meshRepresentative depth steps X)

theorem meshRepresentative_pin (depth steps : Nat) (X : (D).Cauchy) :
    Class (meshRepresentative hw0 hw1 depth steps X) =
      meshAction hw0 hw1 depth steps (Class X) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      change Class (rootRepresentative hw0 hw1 depth
        (meshRepresentative hw0 hw1 depth steps X)) =
        root hw0 hw1 depth (meshAction hw0 hw1 depth steps (Class X))
      rw [rootRepresentative_pin, ih]

/-- A supplied mesh point returns its original Cauchy representative and an
exact completion pin to the already-defined dyadic action. -/
def suppliedMeshCertificate (p : MeshPoint) (X : (D).Cauchy) :
    {Y : (D).Cauchy // Class Y = action hw0 hw1 (embed p) (Class X)} :=
  ⟨meshRepresentative hw0 hw1 p.depth p.steps X, by
    rw [meshRepresentative_pin]
    exact (action_embed hw0 hw1 p (Class X)).symm⟩

#print axioms rootRepresentative
#print axioms rootRepresentative_pin
#print axioms meshRepresentative
#print axioms meshRepresentative_pin
#print axioms suppliedMeshCertificate

end YMGap.Continuum.BF4WilsonAllNomeDyadicRepresentatives
