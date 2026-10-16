/-
# Explicit coordinate paths between arbitrary Z4 plaquettes

Every pair of plaquettes is joined by a literal shared-link `AdjPath`.  The
path first changes the source plane to `p01`, moves the four base coordinates
one at a time, and changes from `p01` to the target plane.  Motions in the
`x0` and `x1` directions cost one plaquette edge per coordinate step; `x2`
and `x3` use a perpendicular-plane bridge and cost three.  The two plane
changes cost at most four edges in total.

This gives a thin path whose length is linear in coordinate differences.  It
does not assert physical-box membership, a covariance estimate, an exterior
face sum, or a continuum or mass-gap conclusion.
-/

import YMGap.Continuum.BF4ExactSlabPlaquettePairPathCarrier

namespace YMGap.Continuum.Z4PlaquetteCoordinateAdjPath

set_option autoImplicit false

open YMGap.Continuum.AdjSpanningBuild (adjacentSymm)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.PinnedCluster
open YMGap.Continuum.SepLatticeZ4Linf
open Dir4 Z4Plane

theorem natDist_add_right (left right shift : Nat) :
    natDist (left + shift) (right + shift) = natDist left right := by
  unfold natDist
  rw [Nat.add_sub_add_right, Nat.add_sub_add_right]

theorem natDist_add_left (shift left right : Nat) :
    natDist (shift + left) (shift + right) = natDist left right := by
  unfold natDist
  rw [Nat.add_sub_add_left, Nat.add_sub_add_left]

/-- Concatenation of two adjacency paths. -/
def pathTrans {S : SepLattice} : {first middle last : S.toLattice.Plaquette} →
    AdjPath S first middle → AdjPath S middle last → AdjPath S first last
  | _, _, _, .single _, right => right
  | _, _, _, .cons adjacent rest, right =>
      .cons adjacent (pathTrans rest right)

theorem pathTrans_pathLen {S : SepLattice}
    {first middle last : S.toLattice.Plaquette}
    (left : AdjPath S first middle) (right : AdjPath S middle last) :
    (pathTrans left right).pathLen = left.pathLen + right.pathLen := by
  induction left with
  | single _ => simp [pathTrans, AdjPath.pathLen]
  | cons _ rest ih =>
      simp only [pathTrans, AdjPath.pathLen]
      rw [ih]
      omega

/-- Reversal of an adjacency path, using symmetry of shared-link adjacency. -/
def pathReverse {S : SepLattice} : {first last : S.toLattice.Plaquette} →
    AdjPath S first last → AdjPath S last first
  | _, _, .single plaquette => .single plaquette
  | first, _, .cons adjacent rest =>
      pathTrans (pathReverse rest)
        (.cons (adjacentSymm adjacent) (.single first))

theorem pathReverse_pathLen {S : SepLattice}
    {first last : S.toLattice.Plaquette}
    (path : AdjPath S first last) :
    (pathReverse path).pathLen = path.pathLen := by
  induction path with
  | single _ => rfl
  | @cons first next last adjacent rest ih =>
      rw [pathReverse, pathTrans_pathLen, ih]
      simp [AdjPath.pathLen]

/-- Change either endpoint by definitional equality without changing the
underlying path data. -/
def pathCast {S : SepLattice}
    {first last newFirst newLast : S.toLattice.Plaquette}
    (hfirst : first = newFirst) (hlast : last = newLast)
    (path : AdjPath S first last) : AdjPath S newFirst newLast := by
  subst newFirst
  subst newLast
  exact path

theorem pathCast_pathLen {S : SepLattice}
    {first last newFirst newLast : S.toLattice.Plaquette}
    (hfirst : first = newFirst) (hlast : last = newLast)
    (path : AdjPath S first last) :
    (pathCast hfirst hlast path).pathLen = path.pathLen := by
  subst newFirst
  subst newLast
  rfl

private def edge (left right : Z4Plaq) (link : Z4Link)
    (hleft : link ∈ edgesOf left) (hright : link ∈ edgesOf right) :
    z4Lattice.Adjacent left right :=
  ⟨link, decide_eq_true hleft, decide_eq_true hright⟩

/-- Change a plaquette plane at one fixed vertex to the `p01` anchor plane. -/
def planeToAnchor (vertex : Z4Vertex) :
    (plane : Z4Plane) →
      AdjPath z4SepLinf (vertex, plane) (vertex, p01)
  | p01 => .single _
  | p02 => .cons
      (edge _ _ (vertex, x0)
        (by simp [edgesOf, dirsOf]) (by simp [edgesOf, dirsOf]))
      (.single _)
  | p03 => .cons
      (edge _ _ (vertex, x0)
        (by simp [edgesOf, dirsOf]) (by simp [edgesOf, dirsOf]))
      (.single _)
  | p12 => .cons
      (edge _ _ (vertex, x1)
        (by simp [edgesOf, dirsOf]) (by simp [edgesOf, dirsOf]))
      (.single _)
  | p13 => .cons
      (edge _ _ (vertex, x1)
        (by simp [edgesOf, dirsOf]) (by simp [edgesOf, dirsOf]))
      (.single _)
  | p23 => .cons
      (edge (vertex, p23) (vertex, p02) (vertex, x2)
        (by simp [edgesOf, dirsOf]) (by simp [edgesOf, dirsOf]))
      (.cons
        (edge _ _ (vertex, x0)
          (by simp [edgesOf, dirsOf]) (by simp [edgesOf, dirsOf]))
        (.single _))

theorem planeToAnchor_pathLen_le (vertex : Z4Vertex) (plane : Z4Plane) :
    (planeToAnchor vertex plane).pathLen ≤ 2 := by
  cases plane <;> simp [planeToAnchor, AdjPath.pathLen]

/-- Cost of one positive coordinate step while retaining the `p01` plane. -/
def anchorStepCost : Dir4 → Nat
  | x0 | x1 => 1
  | x2 | x3 => 3

/-- One positive coordinate step of a `p01` anchor plaquette.  Orthogonal
directions use `p02` or `p03` as a two-edge bridge. -/
def anchorStep (vertex : Z4Vertex) :
    (direction : Dir4) →
      AdjPath z4SepLinf (vertex, p01) (addE vertex direction, p01)
  | x0 => .cons
      (edge _ _ (addE vertex x0, x1)
        (by simp [edgesOf, dirsOf]) (by simp [edgesOf, dirsOf]))
      (.single _)
  | x1 => .cons
      (edge _ _ (addE vertex x1, x0)
        (by simp [edgesOf, dirsOf]) (by simp [edgesOf, dirsOf]))
      (.single _)
  | x2 => .cons
      (edge (vertex, p01) (vertex, p02) (vertex, x0)
        (by simp [edgesOf, dirsOf]) (by simp [edgesOf, dirsOf]))
      (.cons
        (edge (vertex, p02) (addE vertex x2, p02)
          (addE vertex x2, x0)
          (by simp [edgesOf, dirsOf]) (by simp [edgesOf, dirsOf]))
        (.cons
          (edge (addE vertex x2, p02) (addE vertex x2, p01)
            (addE vertex x2, x0)
            (by simp [edgesOf, dirsOf]) (by simp [edgesOf, dirsOf]))
          (.single _)))
  | x3 => .cons
      (edge (vertex, p01) (vertex, p03) (vertex, x0)
        (by simp [edgesOf, dirsOf]) (by simp [edgesOf, dirsOf]))
      (.cons
        (edge (vertex, p03) (addE vertex x3, p03)
          (addE vertex x3, x0)
          (by simp [edgesOf, dirsOf]) (by simp [edgesOf, dirsOf]))
        (.cons
          (edge (addE vertex x3, p03) (addE vertex x3, p01)
            (addE vertex x3, x0)
            (by simp [edgesOf, dirsOf]) (by simp [edgesOf, dirsOf]))
          (.single _)))

theorem anchorStep_pathLen (vertex : Z4Vertex) (direction : Dir4) :
    (anchorStep vertex direction).pathLen = anchorStepCost direction := by
  cases direction <;> simp [anchorStep, anchorStepCost, AdjPath.pathLen]

/-- Repeated positive steps in one coordinate direction. -/
def addEIter (vertex : Z4Vertex) (direction : Dir4) : Nat → Z4Vertex
  | 0 => vertex
  | steps + 1 => addE (addEIter vertex direction steps) direction

def forwardPath (vertex : Z4Vertex) (direction : Dir4) :
    (steps : Nat) →
      AdjPath z4SepLinf (vertex, p01)
        (addEIter vertex direction steps, p01)
  | 0 => .single _
  | steps + 1 =>
      pathTrans (forwardPath vertex direction steps)
        (anchorStep (addEIter vertex direction steps) direction)

theorem forwardPath_pathLen (vertex : Z4Vertex) (direction : Dir4)
    (steps : Nat) :
    (forwardPath vertex direction steps).pathLen =
      anchorStepCost direction * steps := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [forwardPath, pathTrans_pathLen, ih]
      have hstep := anchorStep_pathLen
        (addEIter vertex direction steps) direction
      calc
        anchorStepCost direction * steps +
            (anchorStep (addEIter vertex direction steps) direction).pathLen =
          anchorStepCost direction * steps + anchorStepCost direction :=
            congrArg
              (fun value => anchorStepCost direction * steps + value) hstep
        _ = anchorStepCost direction * (steps + 1) := by
          rw [Nat.mul_add, Nat.mul_one]

theorem addEIter_x0 (a b c d steps : Nat) :
    addEIter (a, b, c, d) x0 steps = (a + steps, b, c, d) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      simp [addEIter, ih, addE, Nat.add_assoc]

theorem addEIter_x1 (a b c d steps : Nat) :
    addEIter (a, b, c, d) x1 steps = (a, b + steps, c, d) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      simp [addEIter, ih, addE, Nat.add_assoc]

theorem addEIter_x2 (a b c d steps : Nat) :
    addEIter (a, b, c, d) x2 steps = (a, b, c + steps, d) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      simp [addEIter, ih, addE, Nat.add_assoc]

theorem addEIter_x3 (a b c d steps : Nat) :
    addEIter (a, b, c, d) x3 steps = (a, b, c, d + steps) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      simp [addEIter, ih, addE, Nat.add_assoc]

/-- Move only the first coordinate, in whichever direction is needed. -/
def x0Path (a b c d target : Nat) :
    AdjPath z4SepLinf ((a, b, c, d), p01)
      ((target, b, c, d), p01) := by
  by_cases h : a ≤ target
  · have path := forwardPath (a, b, c, d) x0 (target - a)
    exact pathCast rfl
      (by rw [addEIter_x0, Nat.add_sub_of_le h]) path
  · have hreverse : target ≤ a := by omega
    have path := pathReverse
      (forwardPath (target, b, c, d) x0 (a - target))
    exact pathCast
      (by rw [addEIter_x0, Nat.add_sub_of_le hreverse]) rfl path

theorem x0Path_pathLen (a b c d target : Nat) :
    (x0Path a b c d target).pathLen = natDist a target := by
  unfold x0Path
  split
  · next h =>
      rw [pathCast_pathLen, forwardPath_pathLen]
      unfold anchorStepCost natDist
      rw [Nat.sub_eq_zero_of_le h, Nat.zero_add, Nat.one_mul]
  · next h =>
      have hreverse : target ≤ a := by omega
      rw [pathCast_pathLen, pathReverse_pathLen, forwardPath_pathLen]
      unfold anchorStepCost natDist
      rw [Nat.sub_eq_zero_of_le hreverse, Nat.add_zero, Nat.one_mul]

/-- Move only the second coordinate, in whichever direction is needed. -/
def x1Path (a b c d target : Nat) :
    AdjPath z4SepLinf ((a, b, c, d), p01)
      ((a, target, c, d), p01) := by
  by_cases h : b ≤ target
  · have path := forwardPath (a, b, c, d) x1 (target - b)
    exact pathCast rfl
      (by rw [addEIter_x1, Nat.add_sub_of_le h]) path
  · have hreverse : target ≤ b := by omega
    have path := pathReverse
      (forwardPath (a, target, c, d) x1 (b - target))
    exact pathCast
      (by rw [addEIter_x1, Nat.add_sub_of_le hreverse]) rfl path

theorem x1Path_pathLen (a b c d target : Nat) :
    (x1Path a b c d target).pathLen = natDist b target := by
  unfold x1Path
  split
  · next h =>
      rw [pathCast_pathLen, forwardPath_pathLen]
      unfold anchorStepCost natDist
      rw [Nat.sub_eq_zero_of_le h, Nat.zero_add, Nat.one_mul]
  · next h =>
      have hreverse : target ≤ b := by omega
      rw [pathCast_pathLen, pathReverse_pathLen, forwardPath_pathLen]
      unfold anchorStepCost natDist
      rw [Nat.sub_eq_zero_of_le hreverse, Nat.add_zero, Nat.one_mul]

/-- Move only the third coordinate, in whichever direction is needed. -/
def x2Path (a b c d target : Nat) :
    AdjPath z4SepLinf ((a, b, c, d), p01)
      ((a, b, target, d), p01) := by
  by_cases h : c ≤ target
  · have path := forwardPath (a, b, c, d) x2 (target - c)
    exact pathCast rfl
      (by rw [addEIter_x2, Nat.add_sub_of_le h]) path
  · have hreverse : target ≤ c := by omega
    have path := pathReverse
      (forwardPath (a, b, target, d) x2 (c - target))
    exact pathCast
      (by rw [addEIter_x2, Nat.add_sub_of_le hreverse]) rfl path

theorem x2Path_pathLen (a b c d target : Nat) :
    (x2Path a b c d target).pathLen = 3 * natDist c target := by
  by_cases h : c ≤ target
  · simp [x2Path, h, pathCast_pathLen, forwardPath_pathLen,
      anchorStepCost, natDist]
  · have hreverse : target ≤ c := by omega
    simp [x2Path, h, pathCast_pathLen, pathReverse_pathLen,
      forwardPath_pathLen, anchorStepCost, natDist]
    omega

/-- Move only the time coordinate, in whichever direction is needed. -/
def x3Path (a b c d target : Nat) :
    AdjPath z4SepLinf ((a, b, c, d), p01)
      ((a, b, c, target), p01) := by
  by_cases h : d ≤ target
  · have path := forwardPath (a, b, c, d) x3 (target - d)
    exact pathCast rfl
      (by rw [addEIter_x3, Nat.add_sub_of_le h]) path
  · have hreverse : target ≤ d := by omega
    have path := pathReverse
      (forwardPath (a, b, c, target) x3 (d - target))
    exact pathCast
      (by rw [addEIter_x3, Nat.add_sub_of_le hreverse]) rfl path

theorem x3Path_pathLen (a b c d target : Nat) :
    (x3Path a b c d target).pathLen = 3 * natDist d target := by
  by_cases h : d ≤ target
  · simp [x3Path, h, pathCast_pathLen, forwardPath_pathLen,
      anchorStepCost, natDist]
  · have hreverse : target ≤ d := by omega
    simp [x3Path, h, pathCast_pathLen, pathReverse_pathLen,
      forwardPath_pathLen, anchorStepCost, natDist]
    omega

/-- Coordinate-by-coordinate path between two `p01` anchors. -/
def anchorCoordinatePath
    (a b c d targetA targetB targetC targetD : Nat) :
    AdjPath z4SepLinf ((a, b, c, d), p01)
      ((targetA, targetB, targetC, targetD), p01) :=
  pathTrans (x0Path a b c d targetA)
    (pathTrans (x1Path targetA b c d targetB)
      (pathTrans (x2Path targetA targetB c d targetC)
        (x3Path targetA targetB targetC d targetD)))

theorem anchorCoordinatePath_pathLen
    (a b c d targetA targetB targetC targetD : Nat) :
    (anchorCoordinatePath a b c d targetA targetB targetC targetD).pathLen =
      natDist a targetA + natDist b targetB +
        3 * natDist c targetC + 3 * natDist d targetD := by
  unfold anchorCoordinatePath
  rw [pathTrans_pathLen, pathTrans_pathLen, pathTrans_pathLen,
    x0Path_pathLen, x1Path_pathLen, x2Path_pathLen, x3Path_pathLen]
  omega

/-- Explicit thin shared-link path between arbitrary plaquettes. -/
def plaquetteCoordinatePath
    (a b c d targetA targetB targetC targetD : Nat)
    (sourcePlane targetPlane : Z4Plane) :
    AdjPath z4SepLinf ((a, b, c, d), sourcePlane)
      ((targetA, targetB, targetC, targetD), targetPlane) :=
  pathTrans (planeToAnchor (a, b, c, d) sourcePlane)
    (pathTrans
      (anchorCoordinatePath a b c d targetA targetB targetC targetD)
      (pathReverse
        (planeToAnchor (targetA, targetB, targetC, targetD) targetPlane)))

/-- Weighted Manhattan length plus a fixed four-edge plane-change overhead. -/
theorem plaquetteCoordinatePath_pathLen_le
    (a b c d targetA targetB targetC targetD : Nat)
    (sourcePlane targetPlane : Z4Plane) :
    (plaquetteCoordinatePath a b c d targetA targetB targetC targetD
      sourcePlane targetPlane).pathLen ≤
      natDist a targetA + natDist b targetB +
        3 * natDist c targetC + 3 * natDist d targetD + 4 := by
  rw [plaquetteCoordinatePath, pathTrans_pathLen, pathTrans_pathLen,
    anchorCoordinatePath_pathLen, pathReverse_pathLen]
  have hsource := planeToAnchor_pathLen_le (a, b, c, d) sourcePlane
  have htarget := planeToAnchor_pathLen_le
    (targetA, targetB, targetC, targetD) targetPlane
  omega

end YMGap.Continuum.Z4PlaquetteCoordinateAdjPath

#print axioms YMGap.Continuum.Z4PlaquetteCoordinateAdjPath.pathTrans
#print axioms YMGap.Continuum.Z4PlaquetteCoordinateAdjPath.pathReverse
#print axioms YMGap.Continuum.Z4PlaquetteCoordinateAdjPath.natDist_add_right
#print axioms YMGap.Continuum.Z4PlaquetteCoordinateAdjPath.natDist_add_left
#print axioms YMGap.Continuum.Z4PlaquetteCoordinateAdjPath.planeToAnchor
#print axioms YMGap.Continuum.Z4PlaquetteCoordinateAdjPath.planeToAnchor_pathLen_le
#print axioms YMGap.Continuum.Z4PlaquetteCoordinateAdjPath.anchorStep
#print axioms YMGap.Continuum.Z4PlaquetteCoordinateAdjPath.anchorStep_pathLen
#print axioms YMGap.Continuum.Z4PlaquetteCoordinateAdjPath.forwardPath
#print axioms YMGap.Continuum.Z4PlaquetteCoordinateAdjPath.forwardPath_pathLen
#print axioms YMGap.Continuum.Z4PlaquetteCoordinateAdjPath.x0Path
#print axioms YMGap.Continuum.Z4PlaquetteCoordinateAdjPath.x0Path_pathLen
#print axioms YMGap.Continuum.Z4PlaquetteCoordinateAdjPath.x1Path
#print axioms YMGap.Continuum.Z4PlaquetteCoordinateAdjPath.x1Path_pathLen
#print axioms YMGap.Continuum.Z4PlaquetteCoordinateAdjPath.x2Path
#print axioms YMGap.Continuum.Z4PlaquetteCoordinateAdjPath.x2Path_pathLen
#print axioms YMGap.Continuum.Z4PlaquetteCoordinateAdjPath.x3Path
#print axioms YMGap.Continuum.Z4PlaquetteCoordinateAdjPath.x3Path_pathLen
#print axioms YMGap.Continuum.Z4PlaquetteCoordinateAdjPath.anchorCoordinatePath
#print axioms YMGap.Continuum.Z4PlaquetteCoordinateAdjPath.anchorCoordinatePath_pathLen
#print axioms YMGap.Continuum.Z4PlaquetteCoordinateAdjPath.plaquetteCoordinatePath
#print axioms YMGap.Continuum.Z4PlaquetteCoordinateAdjPath.plaquetteCoordinatePath_pathLen_le
