module

public import SquaresInCircles.Eight.TableFree.SecondMixedPositiveSourceThreeContact
public import SquaresInCircles.Eight.TableFree.SecondMixedPositiveEarlyPolynomial
public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreeReferenceAlgebra

/-!
# Exact references for the early transverse quadratic

The reference target is B=.24. Its actual radical, label and slope
determine all five harmonic coefficients of the quadratic minimum.
Every coefficient cage is proved from that fixed physical circle point.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.PositiveSource.Early
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)
open PositiveThree (Lower lowerAngle lower_trig)
open StationaryPrimitives (Interval)
open OppositeThree.ReferenceAlgebra

def r : ℝ := 6/25
def m : ℝ := 143/100
def G (φ : ℝ) : ℝ := F r φ-(FB r φ)^2/(2*m)
def c0 : ℝ := -e+g/2-L r-g^2*(1+(ratio r)^2)/(4*m)-(LLabel.d1 r)^2/(2*m)
def cSin : ℝ := g*(1-U r)+g*LLabel.d1 r*ratio r/m
def cCos : ℝ := g*(r+1/2)+g*LLabel.d1 r/m
def cTwo : ℝ := -g^2*(1-(ratio r)^2)/(4*m)
def cMix : ℝ := -g^2*ratio r/(2*m)

lemma harmonic (φ : ℝ) : G φ=φ+c0+cSin*Real.sin φ+cCos*Real.cos φ+
    cTwo*Real.cos (2*φ)+cMix*Real.sin (2*φ) := by
  dsimp [G,F,source,FB,c0,cSin,cCos,cTwo,cMix,U,m]
  rw [Real.cos_two_mul,Real.sin_two_mul]
  linear_combination -(50/143)*g^2*(ratio r)^2*(Real.sin_sq_add_cos_sq φ)

local macro "coefficient_reference" : tactic => `(tactic|
  norm_num [shifted,radicand,rootThree,rootStep,coordinate,ratioBox,ratioDBox,labelBox,firstBox,secondBox,
    r,m,g,e,EdgeThreeAligned.gp,EdgeThreeAligned.ep,LLabel,RoleLabel.eval,Q0,
    Interval.point,Interval.of_bounds,Interval.add,Interval.sub,Interval.neg,
    Interval.mul,Interval.square,Interval.cube,Interval.inv,Interval.div])

lemma coefficients :
    -(204013/1000000:ℝ)<c0 ∧ -(159591/250000:ℝ)<cSin ∧
    (168423/125000:ℝ)<cCos ∧ cTwo<-(79539/500000:ℝ) ∧
    -(153197/1000000:ℝ)<cMix := by
  let X := shifted (Interval.point r) (9/5) (by norm_num) (by coefficient_reference)
  have hX : 0<X.lo := by dsimp [X]; coefficient_reference
  let R := ratioBox (Interval.point r) X hX
  let J := labelBox LLabel (Interval.point r) X
  let D := firstBox LLabel (Interval.point r) X hX
  let C₀ : Interval c0 := (((Interval.point (-e+g/2)).sub J).sub
    (((Interval.point (g^2)).mul ((Interval.point 1).add R.square)).div
      (Interval.point (4*m)) (by norm_num [Interval.point,m]))).sub
        (D.square.div (Interval.point (2*m)) (by norm_num [Interval.point,m]))
  let C₁ : Interval cSin := ((Interval.point g).mul ((Interval.point 1).sub X)).add
    ((((Interval.point g).mul D).mul R).div (Interval.point m) (by norm_num [Interval.point,m]))
  let C₂ : Interval cCos := (Interval.point (g*(r+1/2))).add
    (((Interval.point g).mul D).div (Interval.point m) (by norm_num [Interval.point,m]))
  let C₃ : Interval cTwo := ((Interval.point (-g^2)).mul ((Interval.point 1).sub R.square)).div
    (Interval.point (4*m)) (by norm_num [Interval.point,m])
  let C₄ : Interval cMix := ((Interval.point (-g^2)).mul R).div
    (Interval.point (2*m)) (by norm_num [Interval.point,m])
  have h0 : -(204013/1000000:ℝ)<C₀.lo := by dsimp [C₀,D,J,R,X]; coefficient_reference
  have h1 : -(159591/250000:ℝ)<C₁.lo := by dsimp [C₁,D,R,X]; coefficient_reference
  have h2 : (168423/125000:ℝ)<C₂.lo := by dsimp [C₂,D,X]; coefficient_reference
  have h3 : C₃.hi<-(79539/500000:ℝ) := by dsimp [C₃,R,X]; coefficient_reference
  have h4 : -(153197/1000000:ℝ)<C₄.lo := by dsimp [C₄,R,X]; coefficient_reference
  exact ⟨h0.trans_le C₀.mem.1,h1.trans_le C₁.mem.1,h2.trans_le C₂.mem.1,
    C₃.mem.2.trans_lt h3,h4.trans_le C₄.mem.1⟩

lemma trig_13 : (9635581/10000000:ℝ)<Real.sin (13/10) ∧
    (2674988/10000000:ℝ)<Real.cos (13/10) := by
  have hs := HighOrderTaylor.S15_le_sin (x := (13/10:ℝ)) (by norm_num)
  have hc := HighOrderTaylor.C14_le_cos (x := (13/10:ℝ)) (by norm_num)
  norm_num [HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,
    HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8] at hs hc
  exact ⟨by linarith,by linarith⟩

lemma reference_31 :
    (2243/5000:ℝ)<ratio (31/100) ∧ (133/200:ℝ)<ratioD (31/100) ∧
    LLabel.d1 (31/100)<(1793/2500:ℝ) ∧ LLabel.d2 (31/100)<-(113/125:ℝ) := by
  let X := shifted (Interval.point (31/100:ℝ)) (9/5) (by norm_num) (by coefficient_reference)
  have hX : 0<X.lo := by dsimp [X]; coefficient_reference
  let R := ratioBox (Interval.point (31/100:ℝ)) X hX
  let R₁ := ratioDBox X hX
  let D := firstBox LLabel (Interval.point (31/100:ℝ)) X hX
  let D₁ := secondBox LLabel (Interval.point (31/100:ℝ)) X hX
  have h0 : (2243/5000:ℝ)<R.lo := by dsimp [R,X]; coefficient_reference
  have h1 : (133/200:ℝ)<R₁.lo := by dsimp [R₁,X]; coefficient_reference
  have h2 : D.hi<(1793/2500:ℝ) := by dsimp [D,X]; coefficient_reference
  have h3 : D₁.hi<-(113/125:ℝ) := by dsimp [D₁,X]; coefficient_reference
  exact ⟨h0.trans_le R.mem.1,h1.trans_le R₁.mem.1,D.mem.2.trans_lt h2,D₁.mem.2.trans_lt h3⟩

lemma derivative_references : 0<FB (31/100) (13/10) ∧ 0<FB outerDiagonal (13/10) := by
  have hh := reference_31
  have ht := trig_13
  have hp := mul_le_mul hh.1.le ht.1.le (by norm_num : (0:ℝ)≤9635581/10000000)
    (by linarith [hh.1] : 0≤ratio (31/100))
  constructor
  · dsimp [FB,g,EdgeThreeAligned.gp]
    nlinarith [hh.2.2.1,ht.2]
  · rw [FB,ratio_diagonal,L_first_diagonal]
    dsimp [g,EdgeThreeAligned.gp]
    linarith [ht.1,ht.2,fine_outer_endpoint_bounds.2]

lemma curvature_reference : m<g*ratioD (31/100)*(19121/25000)-LLabel.d2 (31/100) := by
  have hh := reference_31
  dsimp [m,g,EdgeThreeAligned.gp]
  linarith [hh.2.1,hh.2.2.2]

end SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.PositiveSource.Early
