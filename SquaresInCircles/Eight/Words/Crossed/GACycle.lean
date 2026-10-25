module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Frames.Signed.Coordinates
public import SquaresInCircles.Eight.Owners.Hard.OuterOrder
public import SquaresInCircles.Eight.Words.Middle.Canonicalization
public import SquaresInCircles.Eight.Words.Middle.AAdvanceContraction

/-!
# Eight squares: lifting the crossed GA output to the hard cycle

In `crossedGACycle` only the G frame and the G and A points change. The original common AB frame
keeps its selected weak zero axis because A's tangent is fixed. HG0 and GA0 are the contacts of
the output (`HardInput.fromCrossedGAData`); all other selected physical axes and the original E
point are kept.
-/

section
/-!
## A crossed GA-alignment output

A temporary lift of the primary circle gives no nonincrease of the original circle, so
`CrossedGAData` records what the construction supplies: containment at the same q, every
inherited strict A deficit (`A_loss`), and a strict A deficit when G moves (`A_strict`).
`CrossedGAOutput` adds that at zero G motion the two original points are kept.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight

structure CrossedGAData (q : ℝ) (H G A : SignedPoint) (r z : ℝ) where
  pointG : SignedPoint
  pointA : SignedPoint
  G_sorted : pointG.Sorted
  G_avoids : pointG.AvoidsCore
  G_contained : pointG.Contained q
  G_nonpos : pointG.y≤0
  A_sorted : pointA.Sorted
  A_avoids : pointA.AvoidsCore
  A_contained : pointA.Contained q
  A_tangent : pointA.y=A.y
  HG_zero : zeroFeasible H pointG r 0
  GA_hard : quarterFeasible pointG pointA 0 0
  A_strict : 0<z → pointA.circle<q
  A_loss : A.circle<q → pointA.circle<q

/-- The identity at zero motion belongs to the noncanceling alignment. An HG2-to-HG0 owner
conversion may move G even when its frame is already common, and so uses `CrossedGAData`. -/
structure CrossedGAOutput (q : ℝ) (H G A : SignedPoint) (r z : ℝ)
    extends CrossedGAData q H G A r z where
  at_zero : z=0 → pointG=G ∧ pointA=A

end SquaresInCircles.Eight
end
end
end

section
/-!
## Reflecting an actual GA output back to the original BT side

Reflection is used on the local three-point
output only.  The resulting data fixes the original B tangent, records
its original strict circle deficit, and supplies literal BT2 and TD2
contacts.  In particular no assertion about a reflected E sign is used.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight

structure CrossedBTData (q : ℝ) (B T D : SignedPoint) (r z : ℝ) where
  pointT : SignedPoint
  pointB : SignedPoint
  T_sorted : pointT.Sorted
  T_avoids : pointT.AvoidsCore
  T_contained : pointT.Contained q
  T_nonneg : 0≤pointT.y
  B_sorted : pointB.Sorted
  B_avoids : pointB.AvoidsCore
  B_contained : pointB.Contained q
  B_tangent : pointB.y=B.y
  TD_two : zeroFeasible pointT D r 2
  BT_hard : quarterFeasible pointB pointT 0 2
  B_strict : 0<z → pointB.circle<q
  B_loss : B.circle<q → pointB.circle<q

structure CrossedBTOutput (q : ℝ) (B T D : SignedPoint) (r z : ℝ)
    extends CrossedBTData q B T D r z where
  at_zero : z=0 → pointT=T ∧ pointB=B

def CrossedGAData.reflectBT {q r z : ℝ} {B T D : SignedPoint}
    (O : CrossedGAData q D.reflect T.reflect B.reflect r z) :
    CrossedBTData q B T D r z where
  pointT := O.pointG.reflect
  pointB := O.pointA.reflect
  T_sorted := by simpa using O.G_sorted
  T_avoids := by simpa using O.G_avoids
  T_contained := by simpa using O.G_contained
  T_nonneg := by dsimp [SignedPoint.reflect]; linarith [O.G_nonpos]
  B_sorted := by simpa using O.A_sorted
  B_avoids := by simpa using O.A_avoids
  B_contained := by simpa using O.A_contained
  B_tangent := by
    have hy := O.A_tangent
    change O.pointA.y= -B.y at hy
    change -O.pointA.y=B.y
    linarith
  TD_two := by
    simpa [reflectedOwner] using
      (zeroFeasible_reflect D.reflect O.pointG r 0).2 O.HG_zero
  BT_hard := by
    simpa [reflectedOwner] using
      (quarterFeasible_reflect O.pointG O.pointA 0 0).2 O.GA_hard
  B_strict := fun h => by simpa using O.A_strict h
  B_loss := by
    intro h
    simpa using O.A_loss (by simpa using h)

def CrossedGAOutput.reflectBT {q r z : ℝ} {B T D : SignedPoint}
    (O : CrossedGAOutput q D.reflect T.reflect B.reflect r z) :
    CrossedBTOutput q B T D r z where
  toCrossedBTData := O.toCrossedGAData.reflectBT
  at_zero := by
    intro hz
    obtain ⟨hG,hA⟩ := O.at_zero hz
    constructor <;> simp [CrossedGAData.reflectBT,hG,hA]

end SquaresInCircles.Eight
end
end
end

section
/-!
## The BT-side move at the original E

In `crossedBTCycle`, T moves to B's original frame and only the T and B points change. The
selected AB axis is kept at the common frame; the output selects BT2 and TD2
(`HardInput.fromCrossedBTData`). Every other original physical witness, the H, D and E points and
frames, and the strict endpoint budget carry over.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight
open Candidate
namespace SignedCycle

def crossedBTCycle (C : SignedCycle) (P Q : SignedPoint) : SignedCycle where
  point := ![C.point H,C.point G,C.point A,Q,P,C.point D,C.point E]
  theta := ![C.theta H,C.theta G,C.theta A,C.theta B,C.theta B,C.theta D,C.theta E]

theorem crossedBTCycle_theta (C : SignedCycle) (P Q : SignedPoint) (i : Vertex) :
    (crossedBTCycle C P Q).theta i=if i=T then C.theta B else C.theta i := by
  fin_cases i <;> simp [crossedBTCycle,H,G,A,B,T,D,E]

theorem crossedBTCycle_spread {C : SignedCycle} (h : C.Spread) (P Q : SignedPoint) :
    (crossedBTCycle C P Q).Spread := by
  intro i j
  rw [crossedBTCycle_theta,crossedBTCycle_theta]
  by_cases hi : i=T <;> by_cases hj : j=T
  · simpa [hi,hj] using h B B
  · simpa [hi,hj] using h B j
  · simpa [hi,hj] using h i B
  · simpa [hi,hj] using h i j

def Witnesses.crossedBTData {q : ℝ} {C : SignedCycle} (w : C.Witnesses)
    (hAB : C.theta A=C.theta B)
    (O : CrossedBTData q (C.point B) (C.point T) (C.point D)
      (C.theta D-C.theta B) (C.theta B-C.theta T)) :
    (crossedBTCycle C O.pointT O.pointB).Witnesses where
  owner i := if i=B ∨ i=T then 2 else w.owner i
  feasible := by
    intro i
    fin_cases i
    · simpa [crossedBTCycle,Feasible,slack,edge,word,delta,next,H,G,B,T] using w.feasible H
    · simpa [crossedBTCycle,Feasible,slack,edge,word,delta,next,G,A,B,T] using w.feasible G
    · have hj : w.owner 2=0 ∨ w.owner 2=2 := by
        simpa [normalOwners,A] using w.allowed A
      have hAB' : C.theta 3=C.theta 2 := hAB.symm
      have hBt : O.pointB.y=(C.point 3).y := O.B_tangent
      rcases hj with hj | hj <;>
        simpa [crossedBTCycle,Feasible,slack,edge,word,delta,next,A,B,T,
          hAB',hj,zeroProjection,hBt] using w.feasible A
    · simpa [crossedBTCycle,Feasible,slack,edge,word,delta,next,B,T,
        quarterFeasible,sub_nonneg] using O.BT_hard
    · simpa [crossedBTCycle,Feasible,slack,edge,word,delta,next,B,T,D,
        zeroFeasible,sub_nonneg] using O.TD_two
    · simpa [crossedBTCycle,Feasible,slack,edge,word,delta,next,B,T,D,E] using w.feasible D
    · simpa [crossedBTCycle,Feasible,slack,edge,word,delta,next,B,T,E,H] using w.feasible E
  allowed := by
    intro i
    by_cases hi : i=B ∨ i=T
    · rcases hi with rfl | rfl <;> norm_num [normalOwners,B,T]
    · simpa [hi] using w.allowed i

def HardOuterGeometry.fromCrossedBTData {q : ℝ} (I : HardOuterGeometry q)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (O : CrossedBTData q (I.cycle.point B) (I.cycle.point T) (I.cycle.point D)
      (I.cycle.theta D-I.cycle.theta B) (I.cycle.theta B-I.cycle.theta T)) :
    HardOuterGeometry q where
  cycle := crossedBTCycle I.cycle O.pointT O.pointB
  necessary := {
    sorted := by
      intro i
      fin_cases i
      · exact I.necessary.sorted H
      · exact I.necessary.sorted G
      · exact I.necessary.sorted A
      · exact O.B_sorted
      · exact O.T_sorted
      · exact I.necessary.sorted D
      · exact I.necessary.sorted E
    contained := by
      intro i
      fin_cases i
      · exact I.necessary.contained H
      · exact I.necessary.contained G
      · exact I.necessary.contained A
      · exact O.B_contained
      · exact O.T_contained
      · exact I.necessary.contained D
      · exact I.necessary.contained E
    core := by
      intro i
      fin_cases i
      · exact I.necessary.core H
      · exact I.necessary.core G
      · exact I.necessary.core A
      · exact O.B_avoids
      · exact O.T_avoids
      · exact I.necessary.core D
      · exact I.necessary.core E
    spread := crossedBTCycle_spread I.necessary.spread O.pointT O.pointB }
  anchors_normal := {
    H_nonneg := I.anchors_normal.H_nonneg
    A_nonneg := I.anchors_normal.A_nonneg
    B_nonpos := by simpa [crossedBTCycle,B,O.B_tangent] using I.anchors_normal.B_nonpos
    D_nonpos := I.anchors_normal.D_nonpos }
  witnesses := I.witnesses.crossedBTData hAB O
  GA_hard := by
    simpa [crossedBTCycle,Feasible,slack,edge,word,delta,next,G,A] using I.GA_hard
  BT_hard := by
    simpa [crossedBTCycle,Feasible,slack,edge,word,delta,next,B,T,
      quarterFeasible,sub_nonneg] using O.BT_hard
  zero_signs := {
    HG_canceling := by
      intro hh
      have hj : I.witnesses.owner H=2 := by
        simpa [Witnesses.crossedBTData,H,T,B] using hh
      exact I.zero_signs.HG_canceling hj
    TD_canceling := by
      intro hh
      simp [Witnesses.crossedBTData,B,T] at hh }
  endpoint_bound := by
    intro hq
    exact I.endpoint_bound hq

def HardInput.fromCrossedBTData {q : ℝ} (I : HardInput q)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (O : CrossedBTData q (I.cycle.point B) (I.cycle.point T) (I.cycle.point D)
      (I.cycle.theta D-I.cycle.theta B) (I.cycle.theta B-I.cycle.theta T)) :
    HardInput q where
  cycle := (I.outerGeometry.fromCrossedBTData hAB O).cycle
  necessary := (I.outerGeometry.fromCrossedBTData hAB O).necessary
  anchors_normal := (I.outerGeometry.fromCrossedBTData hAB O).anchors_normal
  E_nonpos := I.E_nonpos
  witnesses := (I.outerGeometry.fromCrossedBTData hAB O).witnesses
  GA_hard := (I.outerGeometry.fromCrossedBTData hAB O).GA_hard
  BT_hard := (I.outerGeometry.fromCrossedBTData hAB O).BT_hard
  zero_signs := (I.outerGeometry.fromCrossedBTData hAB O).zero_signs
  E_radial := I.E_radial

end SignedCycle
end SquaresInCircles.Eight
end
end
end

section
/-!
## Realizing strict crossed cap-sum slack at the actual radius

The two middle points are constructed on their
literal hard-contact lines with transverse corners strictly below the
two actual-q caps.  Their tangents sum to one and both circles are
strictly below q.  The supplied inverse-HG point is kept literally;
the final-endpoint wrapper constructs that point on its q-circle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight

structure CrossedClampData (q : ℝ) (H T : SignedPoint) (r u : ℝ) where
  pointG : SignedPoint
  pointA : SignedPoint
  pointB : SignedPoint
  G_sorted : pointG.Sorted
  G_avoids : pointG.AvoidsCore
  G_contained : pointG.Contained q
  G_nonpos : pointG.y≤0
  A_sorted : pointA.Sorted
  A_avoids : pointA.AvoidsCore
  A_strict : pointA.circle<q
  A_nonneg : 0≤pointA.y
  B_sorted : pointB.Sorted
  B_avoids : pointB.AvoidsCore
  B_strict : pointB.circle<q
  B_nonpos : pointB.y≤0
  tangent_sum : pointA.y-pointB.y=1
  HG_zero : zeroFeasible H pointG r 0
  GA_hard : quarterFeasible pointG pointA 0 0
  AB_zero : zeroFeasible pointA pointB 0 0
  AB_two : zeroFeasible pointA pointB 0 2
  BT_hard : quarterFeasible pointB T (-u) 2

namespace CrossedClampConstruction
open HardSplitCap MiddleClampConstruction

theorem actual_data_of_caps {q r u : ℝ} {H G T : SignedPoint}
    (hGs : G.Sorted) (hGc : G.AvoidsCore) (hGq : G.Contained q) (hGy : G.y≤0)
    (hHG : zeroFeasible H G r 0)
    (hA : MiddleHardCap.Feasible q (1/2-G.y))
    (hB : MiddleHardCap.Feasible q (1/2+T.y))
    (hu : u∈Icc 0 frameCap)
    (hLA : 1/2≤cap q (1/2-G.y) 0)
    (hLB : 1/2≤cap q (1/2+T.y) u)
    (hsum : 2<cap q (1/2-G.y) 0+cap q (1/2+T.y) u) :
    ∃ O : CrossedClampData q H T r u, O.pointG=G := by
  let LA := cap q (1/2-G.y) 0
  let LB := cap q (1/2+T.y) u
  have hzero : (0 : ℝ)∈Icc 0 (7/10) := by norm_num
  have hLAupper : LA<7/5 := cap_upper hA hzero hLA
  have hLBupper : LB<7/5 := cap_upper hB hu hLB
  let YA := (2+LA-LB)/2
  let YB := (2+LB-LA)/2
  have hYA : 1/2<YA := by dsimp [YA,LA,LB] at *; linarith
  have hYB : 1/2<YB := by dsimp [YB,LA,LB] at *; linarith
  have hYAcap : YA<cap q (1/2-G.y) 0 := by dsimp [YA,LA,LB]; linarith
  have hYBcap : YB<cap q (1/2+T.y) u := by dsimp [YB,LA,LB]; linarith
  obtain ⟨hAs,hAc,hAy,hAq,hGA⟩ := contactPoint_properties hA hzero hYA hYAcap
  obtain ⟨hBs,hBc,hBy,hBq,hBT⟩ := contactPoint_properties hB hu hYB hYBcap
  let P := contactPoint (1/2-G.y) YA 0
  let Q := (contactPoint (1/2+T.y) YB u).reflect
  have hAB : P.y-Q.y=1 := by
    dsimp [P,Q,contactPoint,SignedPoint.reflect,YA,YB]
    ring
  refine ⟨{
    pointG := G
    pointA := P
    pointB := Q
    G_sorted := hGs
    G_avoids := hGc
    G_contained := hGq
    G_nonpos := hGy
    A_sorted := hAs
    A_avoids := hAc
    A_strict := hAq
    A_nonneg := hAy.le
    B_sorted := by simpa [Q] using hBs
    B_avoids := by simpa [Q] using hBc
    B_strict := by simpa [Q] using hBq
    B_nonpos := by simpa [Q,SignedPoint.reflect] using neg_nonpos.mpr hBy.le
    tangent_sum := hAB
    HG_zero := hHG
    GA_hard := ?_
    AB_zero := by simp [zeroFeasible,zeroProjection,hAB]
    AB_two := by simp [zeroFeasible,zeroProjection,hAB]
    BT_hard := ?_ },rfl⟩
  · change P.a*Real.cos 0-P.y*Real.sin 0=edgeWidth 0+(1/2-G.y)-1/2 at hGA
    simp only [Real.cos_zero,Real.sin_zero,mul_one,mul_zero,sub_zero,edgeWidth_zero] at hGA
    simpa [quarterFeasible,quarterProjection] using (show (1:ℝ)≤G.y+P.a by linarith)
  · change Q.a*Real.cos (-u)-Q.y*Real.sin (-u)-T.y≥edgeWidth (-u)
    rw [Real.cos_neg,Real.sin_neg,edgeWidth_neg]
    have hQa : Q.a=(contactPoint (1/2+T.y) YB u).a := rfl
    have hQy : Q.y= -(contactPoint (1/2+T.y) YB u).y := rfl
    rw [hQa,hQy]
    linarith

end CrossedClampConstruction
end SquaresInCircles.Eight
end
end
end

section
/-!
## Cycle realization of the crossed common-frame clamp

In `crossedClampCycle`, G, A and B take a common frame `β` inside the original H/A interval. H,
T, D and E, their frames, and the retained TD, DE and EH witnesses stay fixed, so the local
invariant endpoint budget survives also after physical reflection
(`HardInput.fromCrossedClamp`). The strict middle losses are at the q of the source,
independently of earlier deficits.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SignedCycle
open Candidate

def crossedClampCycle (C : SignedCycle) (P Q R : SignedPoint) (β : ℝ) : SignedCycle where
  point := ![C.point H,P,Q,R,C.point T,C.point D,C.point E]
  theta := ![C.theta H,β,β,β,C.theta T,C.theta D,C.theta E]

theorem crossedClampCycle_theta (C : SignedCycle) (P Q R : SignedPoint) (β : ℝ) (i : Vertex) :
    (crossedClampCycle C P Q R β).theta i=
      if i=G ∨ i=A ∨ i=B then β else C.theta i := by
  fin_cases i <;> simp [crossedClampCycle,H,G,A,B,T,D,E]

theorem crossedClampCycle_spread {C : SignedCycle} (hC : C.Spread)
    (P Q R : SignedPoint) {β : ℝ} (hβ : β∈Icc (C.theta H) (C.theta A)) :
    (crossedClampCycle C P Q R β).Spread := by
  have hb (i : Vertex) : |β-C.theta i|≤frameCap := by
    have hh := abs_le.mp (hC H i)
    have ha := abs_le.mp (hC A i)
    apply abs_le.mpr
    constructor <;> linarith [hβ.1,hβ.2]
  intro i j
  rw [crossedClampCycle_theta,crossedClampCycle_theta]
  by_cases hi : i=G ∨ i=A ∨ i=B <;> by_cases hj : j=G ∨ j=A ∨ j=B
  · simp [hi,hj,frameCap]; norm_num
  · simpa [hi,hj] using hb j
  · simpa [hi,hj,abs_sub_comm] using hb i
  · simpa [hi,hj] using hC i j

def Witnesses.crossedClamp {q β : ℝ} {C : SignedCycle} (w : C.Witnesses)
    (O : CrossedClampData q (C.point H) (C.point T)
      (β-C.theta H) (β-C.theta T)) :
    (crossedClampCycle C O.pointG O.pointA O.pointB β).Witnesses where
  owner i := if i=H ∨ i=G then 0 else if i=B then 2 else w.owner i
  feasible := by
    intro i
    fin_cases i
    · simpa [crossedClampCycle,Feasible,slack,edge,word,delta,next,H,G,A,B,
        zeroFeasible,sub_nonneg] using O.HG_zero
    · simpa [crossedClampCycle,Feasible,slack,edge,word,delta,next,H,G,A,B,
        quarterFeasible,sub_nonneg] using O.GA_hard
    · have hj : w.owner 2=0 ∨ w.owner 2=2 := by
        simpa [normalOwners,A] using w.allowed A
      rcases hj with hj | hj
      · simpa [crossedClampCycle,Feasible,slack,edge,word,delta,next,H,G,A,B,hj,
          zeroFeasible,sub_nonneg] using O.AB_zero
      · simpa [crossedClampCycle,Feasible,slack,edge,word,delta,next,H,G,A,B,hj,
          zeroFeasible,sub_nonneg] using O.AB_two
    · simpa [crossedClampCycle,Feasible,slack,edge,word,delta,next,H,G,B,T,
        quarterFeasible,sub_nonneg,neg_sub] using O.BT_hard
    · simpa [crossedClampCycle,Feasible,slack,edge,word,delta,next,H,G,B,T,D] using w.feasible T
    · simpa [crossedClampCycle,Feasible,slack,edge,word,delta,next,H,G,B,D,E] using w.feasible D
    · simpa [crossedClampCycle,Feasible,slack,edge,word,delta,next,H,G,B,E] using w.feasible E
  allowed := by
    intro i
    by_cases hi : i=H ∨ i=G
    · rcases hi with rfl | rfl <;> norm_num [normalOwners,H,G,B]
    by_cases hiB : i=B
    · subst i
      norm_num [normalOwners,H,G,B]
    · simpa [hi,hiB] using w.allowed i

def HardOuterGeometry.fromCrossedClamp {q β : ℝ} (I : HardOuterGeometry q)
    (hβ : β∈Icc (I.cycle.theta H) (I.cycle.theta A))
    (O : CrossedClampData q (I.cycle.point H) (I.cycle.point T)
      (β-I.cycle.theta H) (β-I.cycle.theta T)) : HardOuterGeometry q where
  cycle := crossedClampCycle I.cycle O.pointG O.pointA O.pointB β
  necessary := {
    sorted := by
      intro i
      fin_cases i
      · exact I.necessary.sorted H
      · exact O.G_sorted
      · exact O.A_sorted
      · exact O.B_sorted
      · exact I.necessary.sorted T
      · exact I.necessary.sorted D
      · exact I.necessary.sorted E
    contained := by
      intro i
      fin_cases i
      · exact I.necessary.contained H
      · exact O.G_contained
      · exact O.A_strict.le
      · exact O.B_strict.le
      · exact I.necessary.contained T
      · exact I.necessary.contained D
      · exact I.necessary.contained E
    core := by
      intro i
      fin_cases i
      · exact I.necessary.core H
      · exact O.G_avoids
      · exact O.A_avoids
      · exact O.B_avoids
      · exact I.necessary.core T
      · exact I.necessary.core D
      · exact I.necessary.core E
    spread := crossedClampCycle_spread I.necessary.spread O.pointG O.pointA O.pointB hβ }
  anchors_normal := {
    H_nonneg := I.anchors_normal.H_nonneg
    A_nonneg := O.A_nonneg
    B_nonpos := O.B_nonpos
    D_nonpos := I.anchors_normal.D_nonpos }
  witnesses := I.witnesses.crossedClamp O
  GA_hard := by
    simpa [crossedClampCycle,Feasible,slack,edge,word,delta,next,G,A,
      quarterFeasible,sub_nonneg] using O.GA_hard
  BT_hard := by
    simpa [crossedClampCycle,Feasible,slack,edge,word,delta,next,B,T,
      quarterFeasible,sub_nonneg,neg_sub] using O.BT_hard
  zero_signs := {
    HG_canceling := by
      intro hh
      simp [Witnesses.crossedClamp,H,G] at hh
    TD_canceling := by
      intro hh
      have hj : I.witnesses.owner T=0 := by
        simpa [Witnesses.crossedClamp,H,G,B,T] using hh
      exact I.zero_signs.TD_canceling hj }
  endpoint_bound := by
    intro hq
    exact I.endpoint_bound hq

def HardInput.fromCrossedClamp {q β : ℝ} (I : HardInput q)
    (hβ : β∈Icc (I.cycle.theta H) (I.cycle.theta A))
    (O : CrossedClampData q (I.cycle.point H) (I.cycle.point T)
      (β-I.cycle.theta H) (β-I.cycle.theta T)) : HardInput q where
  cycle := (I.outerGeometry.fromCrossedClamp hβ O).cycle
  necessary := (I.outerGeometry.fromCrossedClamp hβ O).necessary
  anchors_normal := (I.outerGeometry.fromCrossedClamp hβ O).anchors_normal
  E_nonpos := I.E_nonpos
  witnesses := (I.outerGeometry.fromCrossedClamp hβ O).witnesses
  GA_hard := (I.outerGeometry.fromCrossedClamp hβ O).GA_hard
  BT_hard := (I.outerGeometry.fromCrossedClamp hβ O).BT_hard
  zero_signs := (I.outerGeometry.fromCrossedClamp hβ O).zero_signs
  E_radial := I.E_radial

/-- Any realized cap-sum state is strictly above the unchanged T frame. In particular the
continuation cannot reach T before H. -/
theorem HardOuterGeometry.crossedClamp_after_T {q β : ℝ}
    (I : HardOuterGeometry q) (hq : q≤qCap)
    (hβ : β∈Icc (I.cycle.theta H) (I.cycle.theta A))
    (O : CrossedClampData q (I.cycle.point H) (I.cycle.point T)
      (β-I.cycle.theta H) (β-I.cycle.theta T)) : I.cycle.theta T<β :=
  (I.fromCrossedClamp hβ O).intermediate_order hq

end SquaresInCircles.Eight.SignedCycle
end
end
end

section
/-!
## The actual-circle inverse HG cap on the complete clamp interval

The inverse is an explicit positive rotated
circle point.  Its transverse corner decreases with the HG error, stays
strictly between .52 and .75, and therefore never encounters the G
tangent floor.  Its induced A cap is always greater than .92.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CrossedClampInverse

def M (b r : ℝ) : ℝ := 1/2+Real.cos r+Real.sin r-b
def W (q b r : ℝ) : ℝ := Real.sqrt (q-(M b r)^2)
def D (q b r : ℝ) : ℝ := M b r*Real.cos r-W q b r*Real.sin r
def X (q b r : ℝ) : ℝ := M b r*Real.sin r+W q b r*Real.cos r
def D1 (q b r : ℝ) : ℝ := X q b r*(Real.cos r-Real.sin r-W q b r)/W q b r
def cap (q b r : ℝ) : ℝ := Real.sqrt (q-(D q b r+1)^2)
def point (q b r : ℝ) : SignedPoint := SignedPoint.outerAt q (1/2-D q b r)

structure Domain (q b : ℝ) : Prop where
  floor : qLow≤q
  ceiling : q≤qCap
  tangent : b∈Ioo (3/4 : ℝ) (9/10)

theorem trig {r : ℝ} (hr : r∈Icc (0:ℝ) (1/25)) :
    r∈Icc 0 frameCap ∧ 0≤Real.sin r ∧ Real.sin r≤1/25 ∧
      1249/1250≤Real.cos r ∧ 1≤Real.cos r+Real.sin r := by
  have hi : r∈Icc 0 frameCap := ⟨hr.1,by dsimp [frameCap]; linarith [hr.2]⟩
  have hs := (transport_trig hi).2.2.1
  have hsu := (Real.sin_le hr.1).trans hr.2
  have h2 := pow_le_pow_left₀ hr.1 hr.2 2
  have hc : 1249/1250≤Real.cos r := by nlinarith [Real.one_sub_sq_div_two_le_cos (x := r)]
  have hw := edgeWidth_ge_one r
  rw [edgeWidth_positive_formula hi] at hw
  exact ⟨hi,hs,hsu,hc,by linarith⟩

theorem M_bounds {q b r : ℝ} (S : Domain q b) (hr : r∈Icc (0:ℝ) (1/25)) :
    M b r∈Ioo (3/5 : ℝ) (79/100) := by
  have ht := trig hr
  dsimp [M]
  constructor <;> linarith [S.tangent.1,S.tangent.2,ht.2.2.1,ht.2.2.2.2,Real.cos_le_one r]

theorem W_bounds {q b r : ℝ} (S : Domain q b) (hr : r∈Icc (0:ℝ) (1/25)) :
    W q b r∈Ioo (9/5 : ℝ) (99/50) ∧ (W q b r)^2=q-(M b r)^2 := by
  have hm := M_bounds S hr
  have hml : 0≤M b r := by linarith [hm.1]
  have hm2 := pow_lt_pow_left₀ hm.2 hml (by decide : (2:ℕ)≠0)
  have hrad : 0≤q-(M b r)^2 := by
    have hq := S.floor
    dsimp [qLow] at hq
    nlinarith
  have hw2 : (W q b r)^2=q-(M b r)^2 := Real.sq_sqrt hrad
  have hw0 : 0≤W q b r := Real.sqrt_nonneg _
  have hqL := S.floor
  have hqU := S.ceiling
  dsimp [qLow,qCap] at hqL hqU
  refine ⟨⟨?_,?_⟩,hw2⟩ <;> nlinarith [sq_nonneg (M b r)]

theorem X_pos {q b r : ℝ} (S : Domain q b) (hr : r∈Icc (0:ℝ) (1/25)) :
    0<X q b r := by
  have ht := trig hr
  have hm := M_bounds S hr
  have hw := W_bounds S hr
  have hp := mul_nonneg (show 0≤M b r by linarith [hm.1]) ht.2.1
  have hq := mul_pos (show 0<W q b r by linarith [hw.1.1])
    (show 0<Real.cos r by linarith [ht.2.2.2.1])
  dsimp [X]
  linarith

theorem norm {q b r : ℝ} (S : Domain q b) (hr : r∈Icc (0:ℝ) (1/25)) :
    (X q b r)^2+(D q b r)^2=q := by
  have hw := (W_bounds S hr).2
  calc
    _ = ((M b r)^2+(W q b r)^2)*((Real.sin r)^2+(Real.cos r)^2) := by dsimp [X,D]; ring
    _ = q := by rw [Real.sin_sq_add_cos_sq,mul_one,hw]; ring

theorem contact (q b r : ℝ) :
    X q b r*Real.sin r+D q b r*Real.cos r=M b r := by
  dsimp [X,D]
  linear_combination M b r*Real.sin_sq_add_cos_sq r

theorem reverse (q b r : ℝ) :
    X q b r*Real.cos r-D q b r*Real.sin r=W q b r := by
  dsimp [X,D]
  linear_combination W q b r*Real.sin_sq_add_cos_sq r

theorem M_hasDerivAt (b r : ℝ) : HasDerivAt (M b) (Real.cos r-Real.sin r) r := by
  have h : HasDerivAt (fun x => 1/2+Real.cos x+Real.sin x-b) (-Real.sin r+Real.cos r) r :=
    (((Real.hasDerivAt_cos r).const_add (1/2)).fun_add (Real.hasDerivAt_sin r)).sub_const b
  have e : Real.cos r-Real.sin r=-Real.sin r+Real.cos r := by ring
  rw [e]
  exact h

theorem W_hasDerivAt {q b r : ℝ} (S : Domain q b) (hr : r∈Icc (0:ℝ) (1/25)) :
    HasDerivAt (W q b) (-M b r*(Real.cos r-Real.sin r)/W q b r) r := by
  have hw := W_bounds S hr
  have hr0 : q-(M b r)^2≠0 := by nlinarith [hw.1.1,hw.2]
  have hd := (((M_hasDerivAt b r).pow 2).const_sub q).sqrt hr0
  convert hd using 1
  · rfl
  · dsimp [W]
    field_simp [show Real.sqrt (q-(M b r)^2)≠0 by change W q b r≠0; linarith [hw.1.1]]

theorem D_hasDerivAt {q b r : ℝ} (S : Domain q b) (hr : r∈Icc (0:ℝ) (1/25)) :
    HasDerivAt (D q b) (D1 q b r) r := by
  have hw := W_bounds S hr
  have hd := ((M_hasDerivAt b r).mul (Real.hasDerivAt_cos r)).sub
    ((W_hasDerivAt S hr).mul (Real.hasDerivAt_sin r))
  convert hd using 1
  · rfl
  · dsimp [D1,X]
    field_simp [show W q b r≠0 by linarith [hw.1.1]]
    ring

theorem D1_neg {q b r : ℝ} (S : Domain q b) (hr : r∈Icc (0:ℝ) (1/25)) :
    D1 q b r<0 := by
  have hw := W_bounds S hr
  have ht := trig hr
  have hneg : Real.cos r-Real.sin r-W q b r<0 := by linarith [hw.1.1,ht.2.1,Real.cos_le_one r]
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (X_pos S hr) hneg)
    (by linarith [hw.1.1])

theorem D_antitone {q b : ℝ} (S : Domain q b) :
    AntitoneOn (D q b) (Icc (0:ℝ) (1/25)) := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun r hr => (D_hasDerivAt S hr).continuousAt.continuousWithinAt
  · intro r hr
    exact D_hasDerivAt S (Ioo_subset_Icc_self hr)
  · intro r hr
    exact (D1_neg S (Ioo_subset_Icc_self hr)).le

theorem D_bounds {q b r : ℝ} (S : Domain q b) (hr : r∈Icc (0:ℝ) (1/25)) :
    D q b r∈Ioo (13/25 : ℝ) (3/4) := by
  have ht := trig hr
  have hm := M_bounds S hr
  have hw := W_bounds S hr
  have hmc := mul_lt_mul_of_pos_right hm.1 (show 0<Real.cos r by linarith [ht.2.2.2.1])
  have hmc' := mul_le_mul_of_nonneg_left ht.2.2.2.1 (by norm_num : (0:ℝ)≤3/5)
  have hws := mul_le_mul hw.1.2.le ht.2.2.1 ht.2.1 (by norm_num : (0:ℝ)≤99/50)
  have hD0 : D q b 0=3/2-b := by simp [D,M]; ring
  have hu := D_antitone S (show (0:ℝ)∈Icc 0 (1/25) by norm_num) hr hr.1
  rw [hD0] at hu
  constructor
  · dsimp [D]
    nlinarith
  · linarith [S.tangent.1]

theorem feasible {q b r : ℝ} (S : Domain q b) (hr : r∈Icc (0:ℝ) (1/25)) :
    MiddleHardCap.Feasible q (D q b r) := by
  have hd := D_bounds S hr
  have hq := S.floor
  dsimp [qLow] at hq
  have h2 := pow_le_pow_left₀ (show 0≤D q b r+1 by linarith [hd.1])
    (show D q b r+1≤7/4 by linarith [hd.2]) 2
  exact ⟨S.ceiling,by linarith [hd.1],by nlinarith⟩

theorem cap_bounds {q b r : ℝ} (S : Domain q b) (hr : r∈Icc (0:ℝ) (1/25)) :
    23/25<cap q b r ∧ cap q b r≤Real.sqrt (q-9/4) ∧
      cap q b r<1291/1000 ∧ (cap q b r)^2+(D q b r+1)^2=q := by
  have hd := D_bounds S hr
  have hfeas := feasible S hr
  have hrad : 0≤q-(D q b r+1)^2 := by linarith [hfeas.corner]
  have hs : (cap q b r)^2=q-(D q b r+1)^2 := Real.sq_sqrt hrad
  have hs0 : 0≤cap q b r := Real.sqrt_nonneg _
  have h2 := pow_le_pow_left₀ (show 0≤D q b r+1 by linarith [hd.1])
    (show D q b r+1≤7/4 by linarith [hd.2]) 2
  have hlow := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤38/25)
    (show 38/25≤D q b r+1 by linarith [hd.1]) 2
  have hqL := S.floor
  have hqU := S.ceiling
  dsimp [qLow,qCap] at hqL hqU
  refine ⟨by nlinarith,?_,by nlinarith,by linarith⟩
  exact Real.sqrt_le_sqrt (by nlinarith [hd.1])

theorem cap_eq_hard_cap (q b r : ℝ) :
    cap q b r=HardSplitCap.cap q (D q b r) 0 := by
  simp [cap,HardSplitCap.cap,HardSplitCap.root,HardSplitCap.contact]

end SquaresInCircles.Eight.CrossedClampInverse
end
end
end

section
/-!
## Original-contact majorization and actual inverse-circle realization

Rotating the original G corner shows that its
transverse corner is at least the explicit inverse cap.  The aligned GA
contact therefore places the original A transverse corner below the A
cap.  Conversely the inverse circle point realizes HG0 exactly at every
time of the proposed clamp, with the original H fixed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CrossedClampInverse

theorem radius_eq {q b r : ℝ} (S : Domain q b) (hr : r∈Icc (0:ℝ) (1/25)) :
    Real.sqrt (q-(D q b r)^2)=X q b r := by
  rw [show q-(D q b r)^2=(X q b r)^2 by nlinarith [norm S hr]]
  exact Real.sqrt_sq (X_pos S hr).le

theorem point_primary {q b r : ℝ} (S : Domain q b) (hr : r∈Icc (0:ℝ) (1/25)) :
    (point q b r).a=X q b r-1/2 := by
  have hd := D_bounds S hr
  have hy : |1/2-D q b r|+1/2=D q b r := by
    rw [abs_of_nonpos (by linarith [hd.1] : 1/2-D q b r≤0)]
    ring
  simp only [point,SignedPoint.outerAt,hy,radius_eq S hr]

theorem point_transverse (q b r : ℝ) : 1/2-(point q b r).y=D q b r := by
  dsimp [point,SignedPoint.outerAt]
  ring

theorem point_properties {q r : ℝ} {H : SignedPoint}
    (S : Domain q H.y) (hr : r∈Icc (0:ℝ) (1/25)) :
    (point q H.y r).Sorted ∧ (point q H.y r).AvoidsCore ∧
      (point q H.y r).Contained q ∧ (point q H.y r).y≤0 ∧
      zeroFeasible H (point q H.y r) r 0 := by
  have hd := D_bounds S hr
  have hy : 1/2-D q H.y r≤0 := by linarith [hd.1]
  have hdiag : |1/2-D q H.y r|≤diagonalCoordinate q := by
    rw [abs_of_nonpos hy]
    linarith [hd.2,(uniform_circle_reserves S.floor S.ceiling).1]
  obtain ⟨hGs,hGq,hGc⟩ := SignedPoint.outerAt_spec S.floor hdiag
  refine ⟨hGs,hGc,hGq.le,hy,?_⟩
  have hp := point_primary S hr
  have hc := contact q H.y r
  rw [zeroFeasible,edgeWidth_positive_formula (trig hr).1]
  simp only [zeroProjection,Matrix.cons_val_zero,hp]
  change (1+Real.cos r+Real.sin r)/2≤
    H.y+(X q H.y r-1/2)*Real.sin r-(1/2-D q H.y r)*Real.cos r
  dsimp [M] at hc
  nlinarith

theorem original_transverse_lower {q r : ℝ} {H G : SignedPoint}
    (S : Domain q H.y) (hr : r∈Icc (0:ℝ) (1/25))
    (hGs : G.Sorted) (hGq : G.Contained q) (hGy : G.y≤0)
    (hHG : zeroFeasible H G r 0) : D q H.y r≤1/2-G.y := by
  let P := (G.a+1/2)*Real.sin r+(1/2-G.y)*Real.cos r
  let R := (G.a+1/2)*Real.cos r-(1/2-G.y)*Real.sin r
  have ht := transport_trig (trig hr).1
  have hsort : 1/2-G.y≤G.a+1/2 := by
    have hh := hGs.2
    rw [abs_of_nonpos hGy] at hh
    linarith
  have hR0 : 0≤R := by
    have hp := mul_nonneg (show 0≤G.a+G.y by linarith)
      (show 0≤Real.cos r by linarith [ht.1])
    have hq := mul_nonneg (show 0≤1/2-G.y by linarith)
      (show 0≤Real.cos r-Real.sin r by linarith [ht.2.2.2.2])
    dsimp [R]
    nlinarith
  have hP : M H.y r≤P := by
    rw [zeroFeasible,edgeWidth_positive_formula (trig hr).1] at hHG
    simp only [zeroProjection,Matrix.cons_val_zero] at hHG
    dsimp [M,P]
    linarith
  have hrot : P^2+R^2=G.circle := by
    dsimp [P,R,SignedPoint.circle]
    rw [abs_of_nonpos hGy]
    linear_combination (((G.a+1/2)^2+(1/2-G.y)^2)*Real.sin_sq_add_cos_sq r)
  have hP2 := pow_le_pow_left₀ (show 0≤M H.y r by linarith [(M_bounds S hr).1]) hP 2
  have hw := W_bounds S hr
  have hc : G.circle≤q := hGq
  have hRW2 : R^2≤(W q H.y r)^2 := by rw [hw.2]; linarith
  have hR : R≤W q H.y r := le_of_pow_le_pow_left₀ (by norm_num) (by linarith [hw.1.1]) hRW2
  have hback : P*Real.cos r-R*Real.sin r=1/2-G.y := by
    dsimp [P,R]
    linear_combination (1/2-G.y)*Real.sin_sq_add_cos_sq r
  have hPc := mul_le_mul_of_nonneg_right hP (show 0≤Real.cos r by linarith [ht.1])
  have hRs := mul_le_mul_of_nonneg_right hR ht.2.2.1
  dsimp [D]
  linarith

theorem original_middle_cap {q r : ℝ} {H G A : SignedPoint}
    (S : Domain q H.y) (hr : r∈Icc (0:ℝ) (1/25))
    (hGs : G.Sorted) (hGq : G.Contained q) (hGy : G.y≤0)
    (hAq : A.Contained q) (hAy : 0≤A.y)
    (hHG : zeroFeasible H G r 0) (hGA : quarterFeasible G A 0 0) :
    A.y+1/2≤cap q H.y r := by
  have hd := original_transverse_lower S hr hGs hGq hGy hHG
  have hga : 1≤G.y+A.a := by simpa [quarterFeasible,quarterProjection] using hGA
  have hprimary : D q H.y r+1≤A.a+1/2 := by linarith
  have hp2 := pow_le_pow_left₀ (show 0≤D q H.y r+1 by linarith [(D_bounds S hr).1]) hprimary 2
  have hAc : (A.a+1/2)^2+(A.y+1/2)^2≤q := by
    simpa [SignedPoint.Contained,SignedPoint.circle,abs_of_nonneg hAy] using hAq
  have hc := cap_bounds S hr
  nlinarith [hc.1,hc.2.2.2]

theorem realize {q r u : ℝ} {H T : SignedPoint}
    (S : Domain q H.y) (hr : r∈Icc (0:ℝ) (1/25))
    (hB : MiddleHardCap.Feasible q (1/2+T.y)) (hu : u∈Icc 0 frameCap)
    (hLB : 1/2≤HardSplitCap.cap q (1/2+T.y) u)
    (hsum : 2<cap q H.y r+HardSplitCap.cap q (1/2+T.y) u) :
    Nonempty (CrossedClampData q H T r u) := by
  obtain ⟨hGs,hGc,hGq,hGy,hHG⟩ := point_properties S hr
  have hA : MiddleHardCap.Feasible q (1/2-(point q H.y r).y) := by
    rw [point_transverse]
    exact feasible S hr
  have hLA : 1/2≤HardSplitCap.cap q (1/2-(point q H.y r).y) 0 := by
    rw [point_transverse,←cap_eq_hard_cap]
    linarith [(cap_bounds S hr).1]
  have hsum' : 2<HardSplitCap.cap q (1/2-(point q H.y r).y) 0+
      HardSplitCap.cap q (1/2+T.y) u := by
    rwa [point_transverse,←cap_eq_hard_cap]
  obtain ⟨O,_⟩ := CrossedClampConstruction.actual_data_of_caps
    hGs hGc hGq hGy hHG hA hB hu hLA hLB hsum'
  exact ⟨O⟩

end SquaresInCircles.Eight.CrossedClampInverse
end
end
end

section
@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight
open Candidate
namespace SignedCycle

def crossedGACycle (C : SignedCycle) (P Q : SignedPoint) : SignedCycle where
  point := ![C.point H,P,Q,C.point B,C.point T,C.point D,C.point E]
  theta := ![C.theta H,C.theta A,C.theta A,C.theta B,C.theta T,C.theta D,C.theta E]

theorem crossedGACycle_theta (C : SignedCycle) (P Q : SignedPoint) (i : Vertex) :
    (crossedGACycle C P Q).theta i=if i=G then C.theta A else C.theta i := by
  fin_cases i <;> simp [crossedGACycle,H,G,A,B,T,D,E]

theorem crossedGACycle_spread {C : SignedCycle} (h : C.Spread) (P Q : SignedPoint) :
    (crossedGACycle C P Q).Spread := by
  intro i j
  rw [crossedGACycle_theta,crossedGACycle_theta]
  by_cases hi : i=G <;> by_cases hj : j=G
  · simpa [hi,hj] using h A A
  · simpa [hi,hj] using h A j
  · simpa [hi,hj] using h i A
  · simpa [hi,hj] using h i j

def Witnesses.crossedGAData {q : ℝ} {C : SignedCycle} (w : C.Witnesses)
    (hAB : C.theta A=C.theta B)
    (O : CrossedGAData q (C.point H) (C.point G) (C.point A)
      (C.theta A-C.theta H) (C.theta G-C.theta A)) :
    (crossedGACycle C O.pointG O.pointA).Witnesses where
  owner i := if i=H ∨ i=G then 0 else w.owner i
  feasible := by
    intro i
    fin_cases i
    · simpa [crossedGACycle,Feasible,slack,edge,word,delta,next,H,G,A,
        zeroFeasible,sub_nonneg] using O.HG_zero
    · simpa [crossedGACycle,Feasible,slack,edge,word,delta,next,H,G,A,
        quarterFeasible,sub_nonneg] using O.GA_hard
    · have hj : w.owner 2=0 ∨ w.owner 2=2 := by
        simpa [normalOwners,A] using w.allowed A
      have hAB' : C.theta 3=C.theta 2 := hAB.symm
      have hAt : O.pointA.y=(C.point 2).y := O.A_tangent
      rcases hj with hj | hj <;>
        simpa [crossedGACycle,Feasible,slack,edge,word,delta,next,H,G,A,B,
          hAB',hj,zeroProjection,hAt] using w.feasible A
    · simpa [crossedGACycle,Feasible,slack,edge,word,delta,next,H,G,B,T] using w.feasible B
    · simpa [crossedGACycle,Feasible,slack,edge,word,delta,next,H,G,T,D] using w.feasible T
    · simpa [crossedGACycle,Feasible,slack,edge,word,delta,next,H,G,D,E] using w.feasible D
    · simpa [crossedGACycle,Feasible,slack,edge,word,delta,next,H,G,E] using w.feasible E
  allowed := by
    intro i
    by_cases hi : i=H ∨ i=G
    · rcases hi with rfl | rfl <;> norm_num [normalOwners,H,G]
    · simpa [hi] using w.allowed i

def HardInput.fromCrossedGAData {q : ℝ} (I : HardInput q)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (O : CrossedGAData q (I.cycle.point H) (I.cycle.point G) (I.cycle.point A)
      (I.cycle.theta A-I.cycle.theta H) (I.cycle.theta G-I.cycle.theta A)) : HardInput q where
  cycle := crossedGACycle I.cycle O.pointG O.pointA
  necessary := {
    sorted := by
      intro i
      fin_cases i
      · exact I.necessary.sorted H
      · exact O.G_sorted
      · exact O.A_sorted
      · exact I.necessary.sorted B
      · exact I.necessary.sorted T
      · exact I.necessary.sorted D
      · exact I.necessary.sorted E
    contained := by
      intro i
      fin_cases i
      · exact I.necessary.contained H
      · exact O.G_contained
      · exact O.A_contained
      · exact I.necessary.contained B
      · exact I.necessary.contained T
      · exact I.necessary.contained D
      · exact I.necessary.contained E
    core := by
      intro i
      fin_cases i
      · exact I.necessary.core H
      · exact O.G_avoids
      · exact O.A_avoids
      · exact I.necessary.core B
      · exact I.necessary.core T
      · exact I.necessary.core D
      · exact I.necessary.core E
    spread := crossedGACycle_spread I.necessary.spread O.pointG O.pointA }
  anchors_normal := {
    H_nonneg := I.anchors_normal.H_nonneg
    A_nonneg := by simpa [crossedGACycle,A,O.A_tangent] using I.anchors_normal.A_nonneg
    B_nonpos := I.anchors_normal.B_nonpos
    D_nonpos := I.anchors_normal.D_nonpos }
  E_nonpos := I.E_nonpos
  witnesses := I.witnesses.crossedGAData hAB O
  GA_hard := by
    simpa [crossedGACycle,Feasible,slack,edge,word,delta,next,H,G,A,
      quarterFeasible,sub_nonneg] using O.GA_hard
  BT_hard := by
    simpa [crossedGACycle,Feasible,slack,edge,word,delta,next,B,T] using I.BT_hard
  zero_signs := {
    HG_canceling := by
      intro hh
      simp [Witnesses.crossedGAData,H,G] at hh
    TD_canceling := by
      intro hh
      have hj : I.witnesses.owner T=0 := by simpa [Witnesses.crossedGAData,H,T,G] using hh
      exact I.zero_signs.TD_canceling hj }
  E_radial := I.E_radial

/-- The same geometric move, before an E sign is chosen. Its strict endpoint budget is the
budget of the source: H, D and E, and their frames, have not moved. -/
def HardOuterGeometry.fromCrossedGAData {q : ℝ} (I : HardOuterGeometry q)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (O : CrossedGAData q (I.cycle.point H) (I.cycle.point G) (I.cycle.point A)
      (I.cycle.theta A-I.cycle.theta H) (I.cycle.theta G-I.cycle.theta A)) :
    HardOuterGeometry q where
  cycle := crossedGACycle I.cycle O.pointG O.pointA
  necessary := {
    sorted := by
      intro i
      fin_cases i
      · exact I.necessary.sorted H
      · exact O.G_sorted
      · exact O.A_sorted
      · exact I.necessary.sorted B
      · exact I.necessary.sorted T
      · exact I.necessary.sorted D
      · exact I.necessary.sorted E
    contained := by
      intro i
      fin_cases i
      · exact I.necessary.contained H
      · exact O.G_contained
      · exact O.A_contained
      · exact I.necessary.contained B
      · exact I.necessary.contained T
      · exact I.necessary.contained D
      · exact I.necessary.contained E
    core := by
      intro i
      fin_cases i
      · exact I.necessary.core H
      · exact O.G_avoids
      · exact O.A_avoids
      · exact I.necessary.core B
      · exact I.necessary.core T
      · exact I.necessary.core D
      · exact I.necessary.core E
    spread := crossedGACycle_spread I.necessary.spread O.pointG O.pointA }
  anchors_normal := {
    H_nonneg := I.anchors_normal.H_nonneg
    A_nonneg := by simpa [crossedGACycle,A,O.A_tangent] using I.anchors_normal.A_nonneg
    B_nonpos := I.anchors_normal.B_nonpos
    D_nonpos := I.anchors_normal.D_nonpos }
  witnesses := I.witnesses.crossedGAData hAB O
  GA_hard := by
    simpa [crossedGACycle,Feasible,slack,edge,word,delta,next,H,G,A,
      quarterFeasible,sub_nonneg] using O.GA_hard
  BT_hard := by
    simpa [crossedGACycle,Feasible,slack,edge,word,delta,next,B,T] using I.BT_hard
  zero_signs := {
    HG_canceling := by
      intro hh
      simp [Witnesses.crossedGAData,H,G] at hh
    TD_canceling := by
      intro hh
      have hj : I.witnesses.owner T=0 := by
        simpa [Witnesses.crossedGAData,H,T,G] using hh
      exact I.zero_signs.TD_canceling hj }
  endpoint_bound := by
    intro hq
    exact I.endpoint_bound hq

end SignedCycle
end SquaresInCircles.Eight
end
end
end
