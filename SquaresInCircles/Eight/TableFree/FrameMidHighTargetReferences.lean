module

public import SquaresInCircles.Eight.TableFree.FrameMidHighTargetCalculus

/-!
# Endpoint comparisons for the target-high support

At each actual endpoint the linear part has an explicit rational lower
bound.  Squaring its remaining positive reserve bounds the single norm.
The two near-quarter references use the exact addition formulas at
`π/2 ± .02`.  Every comparison is a fixed endpoint calculation, with
no sampled interval or root enclosure.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameMidHighTargetReferences
open FramePair FrameDiagonalArc FrameDiagonalLabels FrameMidHighTargetCalculus
open StationaryPrimitives (Interval)
open FrameMidHighVaryingReferences (rBox piBox sinBox cosBox)

def gamma : ℝ := 4463/5000
def radiusUpper : ℝ := 139921407/50000000
def aBox : Interval a1 := Interval.of_bounds ⟨a1_precise.1.le,a1_precise.2.le⟩
def bBox : Interval b1 := by
  convert (Interval.point (2/5:ℝ)).mul aBox using 1
  exact b1_eq.symm
def markerConstantBox : Interval cM :=
  (piBox.div (Interval.point 4) (by norm_num [Interval.point])).add
    (Interval.point (85723/40000))

def constantBox (i j : Bool) (l : ℝ) : Interval (K i j l) :=
  (((((Interval.point (9/100+l)).add ((Interval.point (sign i)).mul markerConstantBox)).
    add ((Interval.point (sign j*u)).mul rBox)).
    add ((Interval.point (-sign i*k-l)).mul aBox)).
    add ((Interval.point (sign i*(q-l))).mul bBox))

def baseValue (before i j : Bool) (l x : ℝ) : ℝ :=
  if before then K i j l+x+(2*l-9/100)*Real.sin x-(9/100)*Real.cos x
  else K i j l+x+(2*l-9/100)*(Real.sin x-Real.cos x)

def baseBox (before i j : Bool) (l : ℝ) {x : ℝ}
    (X : Interval x) (S : Interval (Real.sin x)) (C : Interval (Real.cos x)) :
    Interval (baseValue before i j l x) := by
  cases before
  · exact ((constantBox i j l).add X).add
      ((Interval.point (2*l-9/100)).mul (S.sub C))
  · exact ((((constantBox i j l).add X).add
      ((Interval.point (2*l-9/100)).mul S)).sub ((Interval.point (9/100)).mul C))

def energyBox (j : Bool) (l : ℝ) {x : ℝ}
    (S : Interval (Real.sin x)) (C : Interval (Real.cos x)) :
    Interval (energyA l+energyB j l*Real.cos x+energyC j l*Real.sin x) :=
  ((Interval.point (energyA l)).add ((Interval.point (energyB j l)).mul C)).
    add ((Interval.point (energyC j l)).mul S)

theorem reference_lower (before i j : Bool) {l x : ℝ} (hl : Allowed l)
    (X : Interval x) (S : Interval (Real.sin x)) (C : Interval (Real.cos x))
    (hreserve : gamma<(baseBox before i j l X S C).lo)
    (hsquare : (energyBox j l S C).hi<
      (((baseBox before i j l X S C).lo-gamma)/radiusUpper)^2) :
    gamma<(if before then F i j l x else after i j l x) := by
  let B := baseBox before i j l X S C
  let E := energyBox j l S C
  let cap : ℝ := (B.lo-gamma)/radiusUpper
  have hcap : 0<cap := div_pos (sub_pos.mpr hreserve) (by norm_num [radiusUpper])
  have hn := N_pos (j := j) hl x
  have hsq : (N j l x)^2<cap^2 := by
    rw [N_sq hl]
    exact E.mem.2.trans_lt hsquare
  have hncap : N j l x<cap := by nlinarith
  have hprod : R*N j l x<radiusUpper*cap :=
    (mul_lt_mul_of_pos_left hncap R_pos).trans
      (mul_lt_mul_of_pos_right R_precise.2 hcap)
  have heq : radiusUpper*cap=B.lo-gamma := by dsimp [cap,radiusUpper]; ring
  have hidentity : (if before then F i j l x else after i j l x)=
      baseValue before i j l x-R*N j l x := by cases before <;> rfl
  rw [hidentity]
  rw [heq] at hprod
  linarith [B.mem.1]

def quarter (after : Bool) : ℝ := Real.pi/2+sign after/50

theorem quarter_trig (after : Bool) :
    Real.sin (quarter after)=Real.cos (1/50:ℝ) ∧
      Real.cos (quarter after)=-sign after*Real.sin (1/50:ℝ) := by
  cases after <;>
    simp [quarter,sign,Real.sin_add,Real.cos_add,Real.sin_neg,Real.cos_neg]

def quarterX (after : Bool) : Interval (quarter after) :=
  (piBox.div (Interval.point 2) (by norm_num [Interval.point])).add
    (Interval.point (sign after/50))
def quarterS (after : Bool) : Interval (Real.sin (quarter after)) := by
  rw [(quarter_trig after).1]
  exact cosBox (show (0:ℝ)≤1/50 by norm_num)
def quarterC (after : Bool) : Interval (Real.cos (quarter after)) := by
  rw [(quarter_trig after).2]
  exact (Interval.point (-sign after)).mul (sinBox (show (0:ℝ)≤1/50 by norm_num))

theorem positive_left : gamma<F true true (7/20) (7/10) := by
  apply reference_lower true true true (Or.inl rfl)
    (Interval.point (7/10)) (sinBox (show (0:ℝ)≤7/10 by norm_num))
    (cosBox (show (0:ℝ)≤7/10 by norm_num)) <;>
    norm_num [baseBox,energyBox,constantBox,markerConstantBox,aBox,bBox,rBox,piBox,
      sinBox,cosBox,gamma,radiusUpper,energyA,energyB,energyC,sign,u,v,k,q,
      Interval.point,Interval.of_bounds,Interval.add,Interval.sub,Interval.neg,
      Interval.mul,Interval.div,Interval.inv,HighOrderTaylor.S11,Arithmetic.sin9,
      Arithmetic.sin7,SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8]

theorem positive_right : gamma<F true true (7/20) (93/100) := by
  apply reference_lower true true true (Or.inl rfl)
    (Interval.point (93/100)) (sinBox (show (0:ℝ)≤93/100 by norm_num))
    (cosBox (show (0:ℝ)≤93/100 by norm_num)) <;>
    norm_num [baseBox,energyBox,constantBox,markerConstantBox,aBox,bBox,rBox,piBox,
      sinBox,cosBox,gamma,radiusUpper,energyA,energyB,energyC,sign,u,v,k,q,
      Interval.point,Interval.of_bounds,Interval.add,Interval.sub,Interval.neg,
      Interval.mul,Interval.div,Interval.inv,HighOrderTaylor.S11,Arithmetic.sin9,
      Arithmetic.sin7,SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8]

theorem negative_left : gamma<F false false (2/5) (6/5) := by
  apply reference_lower true false false (Or.inr rfl)
    (Interval.point (6/5)) (sinBox (show (0:ℝ)≤6/5 by norm_num))
    (cosBox (show (0:ℝ)≤6/5 by norm_num)) <;>
    norm_num [baseBox,energyBox,constantBox,markerConstantBox,aBox,bBox,rBox,piBox,
      sinBox,cosBox,gamma,radiusUpper,energyA,energyB,energyC,sign,u,v,k,q,
      Interval.point,Interval.of_bounds,Interval.add,Interval.sub,Interval.neg,
      Interval.mul,Interval.div,Interval.inv,HighOrderTaylor.S11,Arithmetic.sin9,
      Arithmetic.sin7,SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8]

theorem negative_right : gamma<F false false (2/5) (71/50) := by
  apply reference_lower true false false (Or.inr rfl)
    (Interval.point (71/50)) (sinBox (show (0:ℝ)≤71/50 by norm_num))
    (cosBox (show (0:ℝ)≤71/50 by norm_num)) <;>
    norm_num [baseBox,energyBox,constantBox,markerConstantBox,aBox,bBox,rBox,piBox,
      sinBox,cosBox,gamma,radiusUpper,energyA,energyB,energyC,sign,u,v,k,q,
      Interval.point,Interval.of_bounds,Interval.add,Interval.sub,Interval.neg,
      Interval.mul,Interval.div,Interval.inv,HighOrderTaylor.S11,Arithmetic.sin9,
      Arithmetic.sin7,SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8]

theorem opposite_left : gamma<F false true (2/5) (13/10) := by
  apply reference_lower true false true (Or.inr rfl)
    (Interval.point (13/10)) (sinBox (show (0:ℝ)≤13/10 by norm_num))
    (cosBox (show (0:ℝ)≤13/10 by norm_num)) <;>
    norm_num [baseBox,energyBox,constantBox,markerConstantBox,aBox,bBox,rBox,piBox,
      sinBox,cosBox,gamma,radiusUpper,energyA,energyB,energyC,sign,u,v,k,q,
      Interval.point,Interval.of_bounds,Interval.add,Interval.sub,Interval.neg,
      Interval.mul,Interval.div,Interval.inv,HighOrderTaylor.S11,Arithmetic.sin9,
      Arithmetic.sin7,SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8]

theorem opposite_before_quarter : gamma<F false true (2/5) (Real.pi/2-1/50) := by
  have hh := reference_lower true false true (Or.inr (rfl : (2/5:ℝ)=2/5))
    (quarterX false) (quarterS false) (quarterC false)
  have hreserve : gamma<(baseBox true false true (2/5)
      (quarterX false) (quarterS false) (quarterC false)).lo := by
    norm_num [baseBox,constantBox,markerConstantBox,aBox,bBox,rBox,piBox,
      quarterX,quarterS,quarterC,sinBox,cosBox,gamma,sign,u,v,k,q,
      Interval.point,Interval.of_bounds,Interval.add,Interval.sub,Interval.neg,
      Interval.mul,Interval.div,Interval.inv,HighOrderTaylor.S11,Arithmetic.sin9,
      Arithmetic.sin7,SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8]
  have hsquare : (energyBox true (2/5) (quarterS false) (quarterC false)).hi<
      (((baseBox true false true (2/5) (quarterX false) (quarterS false)
        (quarterC false)).lo-gamma)/radiusUpper)^2 := by
    norm_num [baseBox,energyBox,constantBox,markerConstantBox,aBox,bBox,rBox,piBox,
      quarterX,quarterS,quarterC,sinBox,cosBox,gamma,radiusUpper,
      energyA,energyB,energyC,sign,u,v,k,q,
      Interval.point,Interval.of_bounds,Interval.add,Interval.sub,Interval.neg,
      Interval.mul,Interval.div,Interval.inv,HighOrderTaylor.S11,Arithmetic.sin9,
      Arithmetic.sin7,SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8]
  simpa [quarter,sign,sub_eq_add_neg] using hh hreserve hsquare

theorem opposite_after_quarter : gamma<after false true (2/5) (Real.pi/2+1/50) := by
  have hh := reference_lower false false true (Or.inr (rfl : (2/5:ℝ)=2/5))
    (quarterX true) (quarterS true) (quarterC true)
  have hreserve : gamma<(baseBox false false true (2/5)
      (quarterX true) (quarterS true) (quarterC true)).lo := by
    norm_num [baseBox,constantBox,markerConstantBox,aBox,bBox,rBox,piBox,
      quarterX,quarterS,quarterC,sinBox,cosBox,gamma,sign,u,v,k,q,
      Interval.point,Interval.of_bounds,Interval.add,Interval.sub,Interval.neg,
      Interval.mul,Interval.div,Interval.inv,HighOrderTaylor.S11,Arithmetic.sin9,
      Arithmetic.sin7,SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8]
  have hsquare : (energyBox true (2/5) (quarterS true) (quarterC true)).hi<
      (((baseBox false false true (2/5) (quarterX true) (quarterS true)
        (quarterC true)).lo-gamma)/radiusUpper)^2 := by
    norm_num [baseBox,energyBox,constantBox,markerConstantBox,aBox,bBox,rBox,piBox,
      quarterX,quarterS,quarterC,sinBox,cosBox,gamma,radiusUpper,
      energyA,energyB,energyC,sign,u,v,k,q,
      Interval.point,Interval.of_bounds,Interval.add,Interval.sub,Interval.neg,
      Interval.mul,Interval.div,Interval.inv,HighOrderTaylor.S11,Arithmetic.sin9,
      Arithmetic.sin7,SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8]
  simpa [quarter,sign] using hh hreserve hsquare

end SquaresInCircles.Eight.TableFree.FrameMidHighTargetReferences
