module

public import SquaresInCircles.Eight.TableFree.FrameMidHighVaryingCalculus
public import SquaresInCircles.Eight.TableFree.StationaryIntervalAlgebra
public import SquaresInCircles.Eight.TableFree.HighOrderTaylor
public import SquaresInCircles.Eight.TableFree.SecondOuterReferenceTrig

/-!
# Fixed references for the two complete varying supports

The norm bounds are positive square comparisons at the four geometric
endpoints and the single tangent reference `14/25`.  Ordered-field
interval operations substitute the actual circle endpoint, radius,
Taylor bounds and π enclosure into the actual value and derivatives.
There is no interval subdivision, sampled sign, or root-location input.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameMidHighVaryingReferences
open FramePair FrameDiagonalArc FrameDiagonalLabels FrameMidHighVaryingCalculus
open StationaryPrimitives (Interval)

def aBox : Interval a2 := Interval.of_bounds ⟨a2_precise.1.le,a2_precise.2.le⟩
def rBox : Interval R := Interval.of_bounds ⟨R_precise.1.le,R_precise.2.le⟩
def piBox : Interval Real.pi := Interval.of_bounds
  ⟨Arithmetic.pi_hand_enclosure.1.le,Arithmetic.pi_hand_enclosure.2.le⟩
def bBox : Interval b2 := by
  convert (Interval.point (3/5:ℝ)).mul aBox using 1
  exact b2_eq.symm
def xBox : Interval X := ((Interval.point 1).add aBox).sub bBox
def yBox : Interval Y := ((Interval.point 1).sub aBox).sub bBox

def markerBox : Interval M2 := by
  let h := (((piBox.div (Interval.point 4) (by norm_num [Interval.point])).
    add (Interval.point (85723/40000))).sub ((Interval.point k).mul aBox)).
    add ((Interval.point q).mul bBox)
  convert h using 1
  simp only [M2,M,A_b2,cM]

def sinBox {x : ℝ} (hx : 0≤x) : Interval (Real.sin x) :=
  Interval.of_bounds ⟨HighOrderTaylor.S11_le_sin hx,Arithmetic.sin_le_sin9 hx⟩
def cosBox {x : ℝ} (hx : 0≤x) : Interval (Real.cos x) :=
  Interval.of_bounds ⟨Arithmetic.cos10_le_cos hx,SecondWord.ReferenceTrig.cos_le_cos12 hx⟩

structure SupportIntervals (i : Bool) (x : ℝ) where
  value : Interval (F i x)
  first : Interval (Fd i x)
  second : Interval (Fdd i x)

def supportIntervals (i : Bool) {x : ℝ} (hx : 0≤x)
    (Z : Interval (N i x)) (hZ : 0<Z.lo) : SupportIntervals i x := by
  let l := Interval.point (lam i x)
  let m' := Interval.point (m i)
  let s := sinBox hx
  let c := cosBox hx
  let small := Interval.point (9/100:ℝ)
  let two := Interval.point (2:ℝ)
  let n1 := (Interval.point (T i x)).div Z hZ
  let n2 := (Interval.point (Delta i)).div Z.cube (Interval.cube_lo_pos hZ)
  refine ⟨?_,?_,?_⟩
  · exact (((((((Interval.point x).add small).add markerBox).add (two.mul l)).
      sub ((Interval.point (sign i*u)).mul rBox)).
      add (((l.mul xBox).sub small).mul c)).
      add (((l.mul yBox).sub small).mul s)).sub (rBox.mul Z)
  · exact ((((Interval.point 1).sub (two.mul m')).
      add ((((l.mul yBox).sub small).sub (m'.mul xBox)).mul c)).
      add ((((l.mul xBox).neg.add small).sub (m'.mul yBox)).mul s)).sub (rBox.mul n1)
  · exact (((((l.mul xBox).neg.add small).sub ((two.mul m').mul yBox)).mul c).
      add ((((l.mul yBox).neg.add small).add ((two.mul m').mul xBox)).mul s)).
      sub (rBox.mul n2)

theorem norm_reference {i : Bool} {x l h : ℝ} (hl : 0<l)
    (hlh : l<h)
    (hl2 : l^2<(lam i x-sign i*u)^2+(lam i x-v)^2)
    (hh2 : (lam i x-sign i*u)^2+(lam i x-v)^2<h^2) :
    N i x∈Icc l h := by
  have hn := N_pos i x
  have hs := N_sq i x
  constructor <;> nlinarith

def positiveLeftNorm : Interval (N true (1/10)) := Interval.of_bounds
  (norm_reference (l := (54881673/100000000:ℝ)) (h := (27440839/50000000:ℝ))
    (by norm_num) (by norm_num)
    (by norm_num [lam,origin,m,sign,u,v]) (by norm_num [lam,origin,m,sign,u,v]))
def positiveRightNorm : Interval (N true (21/50)) := Interval.of_bounds
  (norm_reference (l := (40288043/100000000:ℝ)) (h := (5036006/12500000:ℝ))
    (by norm_num) (by norm_num)
    (by norm_num [lam,origin,m,sign,u,v]) (by norm_num [lam,origin,m,sign,u,v]))
def negativeLeftNorm : Interval (N false (2/5)) := Interval.of_bounds
  (norm_reference (l := (58345669/100000000:ℝ)) (h := (29172837/50000000:ℝ))
    (by norm_num) (by norm_num)
    (by norm_num [lam,origin,m,sign,u,v]) (by norm_num [lam,origin,m,sign,u,v]))
def negativeRightNorm : Interval (N false (3/5)) := Interval.of_bounds
  (norm_reference (l := (51371303/100000000:ℝ)) (h := (12842827/25000000:ℝ))
    (by norm_num) (by norm_num)
    (by norm_num [lam,origin,m,sign,u,v]) (by norm_num [lam,origin,m,sign,u,v]))
def negativeTangentNorm : Interval (N false (14/25)) := Interval.of_bounds
  (norm_reference (l := (52678261/100000000:ℝ)) (h := (26339133/50000000:ℝ))
    (by norm_num) (by norm_num)
    (by norm_num [lam,origin,m,sign,u,v]) (by norm_num [lam,origin,m,sign,u,v]))

def positiveLeft := supportIntervals true (show (0:ℝ)≤1/10 by norm_num)
  positiveLeftNorm (by norm_num [positiveLeftNorm,Interval.of_bounds])
def positiveRight := supportIntervals true (show (0:ℝ)≤21/50 by norm_num)
  positiveRightNorm (by norm_num [positiveRightNorm,Interval.of_bounds])
def negativeLeft := supportIntervals false (show (0:ℝ)≤2/5 by norm_num)
  negativeLeftNorm (by norm_num [negativeLeftNorm,Interval.of_bounds])
def negativeRight := supportIntervals false (show (0:ℝ)≤3/5 by norm_num)
  negativeRightNorm (by norm_num [negativeRightNorm,Interval.of_bounds])
def negativeTangent := supportIntervals false (show (0:ℝ)≤14/25 by norm_num)
  negativeTangentNorm (by norm_num [negativeTangentNorm,Interval.of_bounds])

theorem positive_endpoint_curvature :
    (4/25:ℝ)<Fdd true (1/10) ∧ (4/25:ℝ)<Fdd true (21/50) := by
  have hl : (4/25:ℝ)<positiveLeft.second.lo := by
    norm_num [positiveLeft,supportIntervals,positiveLeftNorm,
      aBox,rBox,bBox,xBox,yBox,sinBox,cosBox,lam,origin,m,sign,u,v,Delta,T,
      Interval.point,Interval.of_bounds,Interval.add,Interval.sub,Interval.neg,
      Interval.mul,Interval.div,Interval.inv,Interval.square,Interval.cube,
      HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
      SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8]
  have hr : (4/25:ℝ)<positiveRight.second.lo := by
    norm_num [positiveRight,supportIntervals,positiveRightNorm,
      aBox,rBox,bBox,xBox,yBox,sinBox,cosBox,lam,origin,m,sign,u,v,Delta,T,
      Interval.point,Interval.of_bounds,Interval.add,Interval.sub,Interval.neg,
      Interval.mul,Interval.div,Interval.inv,Interval.square,Interval.cube,
      HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
      SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8]
  exact ⟨hl.trans_le positiveLeft.second.mem.1,hr.trans_le positiveRight.second.mem.1⟩

theorem positive_final_slope : Fd true (21/50)<-(2/25:ℝ) := by
  have hh : positiveRight.first.hi<-(2/25:ℝ) := by
    norm_num [positiveRight,supportIntervals,positiveRightNorm,
      aBox,rBox,bBox,xBox,yBox,sinBox,cosBox,lam,origin,m,sign,u,v,Delta,T,
      Interval.point,Interval.of_bounds,Interval.add,Interval.sub,Interval.neg,
      Interval.mul,Interval.div,Interval.inv,Interval.square,Interval.cube,
      HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
      SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8]
  exact positiveRight.first.mem.2.trans_lt hh

theorem positive_final_value : (899/1000:ℝ)<F true (21/50) := by
  have hh : (899/1000:ℝ)<positiveRight.value.lo := by
    norm_num [positiveRight,supportIntervals,positiveRightNorm,markerBox,piBox,
      aBox,rBox,bBox,xBox,yBox,sinBox,cosBox,lam,origin,m,sign,u,v,k,q,
      Interval.point,Interval.of_bounds,Interval.add,Interval.sub,Interval.neg,
      Interval.mul,Interval.div,Interval.inv,Interval.square,Interval.cube,
      HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
      SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8]
  exact hh.trans_le positiveRight.value.mem.1

theorem negative_endpoint_curvature :
    (3/5:ℝ)<Fdd false (2/5) ∧ (3/5:ℝ)<Fdd false (3/5) := by
  have hl : (3/5:ℝ)<negativeLeft.second.lo := by
    norm_num [negativeLeft,supportIntervals,negativeLeftNorm,
      aBox,rBox,bBox,xBox,yBox,sinBox,cosBox,lam,origin,m,sign,u,v,Delta,T,
      Interval.point,Interval.of_bounds,Interval.add,Interval.sub,Interval.neg,
      Interval.mul,Interval.div,Interval.inv,Interval.square,Interval.cube,
      HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
      SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8]
  have hr : (3/5:ℝ)<negativeRight.second.lo := by
    norm_num [negativeRight,supportIntervals,negativeRightNorm,
      aBox,rBox,bBox,xBox,yBox,sinBox,cosBox,lam,origin,m,sign,u,v,Delta,T,
      Interval.point,Interval.of_bounds,Interval.add,Interval.sub,Interval.neg,
      Interval.mul,Interval.div,Interval.inv,Interval.square,Interval.cube,
      HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
      SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8]
  exact ⟨hl.trans_le negativeLeft.second.mem.1,hr.trans_le negativeRight.second.mem.1⟩

theorem negative_tangent_value : (89273/100000:ℝ)<F false (14/25) := by
  have hh : (89273/100000:ℝ)<negativeTangent.value.lo := by
    norm_num [negativeTangent,supportIntervals,negativeTangentNorm,markerBox,piBox,
      aBox,rBox,bBox,xBox,yBox,sinBox,cosBox,lam,origin,m,sign,u,v,k,q,
      Interval.point,Interval.of_bounds,Interval.add,Interval.sub,Interval.neg,
      Interval.mul,Interval.div,Interval.inv,Interval.square,Interval.cube,
      HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
      SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8]
  exact hh.trans_le negativeTangent.value.mem.1

theorem negative_tangent_slope : |Fd false (14/25)|<(7/5000:ℝ) := by
  have hl : -(7/5000:ℝ)<negativeTangent.first.lo := by
    norm_num [negativeTangent,supportIntervals,negativeTangentNorm,
      aBox,rBox,bBox,xBox,yBox,sinBox,cosBox,lam,origin,m,sign,u,v,Delta,T,
      Interval.point,Interval.of_bounds,Interval.add,Interval.sub,Interval.neg,
      Interval.mul,Interval.div,Interval.inv,Interval.square,Interval.cube,
      HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
      SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8]
  have hr : negativeTangent.first.hi<(7/5000:ℝ) := by
    norm_num [negativeTangent,supportIntervals,negativeTangentNorm,
      aBox,rBox,bBox,xBox,yBox,sinBox,cosBox,lam,origin,m,sign,u,v,Delta,T,
      Interval.point,Interval.of_bounds,Interval.add,Interval.sub,Interval.neg,
      Interval.mul,Interval.div,Interval.inv,Interval.square,Interval.cube,
      HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
      SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8]
  exact abs_lt.mpr ⟨hl.trans_le negativeTangent.first.mem.1,
    negativeTangent.first.mem.2.trans_lt hr⟩

end SquaresInCircles.Eight.TableFree.FrameMidHighVaryingReferences
