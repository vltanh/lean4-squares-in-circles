module

public import SquaresInCircles.Eight.Stationary.EqualityGeometry

/-!
# Eight squares: bounds on the box of parameters

Eighteen quantities of the model, as functions of the parameters (`boxData`): the cosine and sine
of the central frame and of its angle to the frame of `H` and `G`, the coordinates of the centre in
the frame of the central square, the seven separation margins of the central square, the room
left in the containment of `T` and `G`, the height of the highest point of `H`, and the height of
the highest point and the abscissa of the leftmost point of `G` when `eta = etaMax`. They are the
interval expressions of `Generated/EqualityBox.lean` (`box_interpretation`), so on the box `InBox`
each lies between the rational bounds `boxLower` and `boxUpper` (`box_data_bounds`).
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Stationary
open Coordinates EqualityParameters Arithmetic

def rawTiltWidth (p : EqualityParameters) : ℝ :=
  (1+sharpData.c*p.C+sharpData.s*p.S+sharpData.c*p.S-sharpData.s*p.C)/2

def boxData (p : EqualityParameters) : Fin 18 → ℝ :=
  ![p.C,
    p.S,
    sharpData.c*p.C+sharpData.s*p.S,
    sharpData.c*p.S-sharpData.s*p.C,
    p.C*p.x+p.S*p.y,
    -p.S*p.x+p.C*p.y,
    (sharpData.pA).1-p.x-(1+p.C+p.S)/2,
    p.C*((sharpData.pB).1-p.x)+p.S*((sharpData.pB).2-p.y)-(1+p.C+p.S)/2,
    -p.S*((sharpData.pD).1-p.x)+p.C*((sharpData.pD).2-p.y)-(1+p.C+p.S)/2,
    -((sharpData.pE).1-p.x)-(1+p.C+p.S)/2,
    -p.C*((sharpData.pH).1-p.x)-p.S*((sharpData.pH).2-p.y)-rawTiltWidth p,
    sharpData.s*((sharpData.pG p.eta).1-p.x)-sharpData.c*((sharpData.pG p.eta).2-p.y)-rawTiltWidth p,
    p.z-p.y-(1+p.C+p.S)/2,
    qStar-((sharpData.x₂-1)^2+(p.z+1/2)^2),
    qStar-((sharpData.h₁+2)^2+(sharpData.h₂+p.eta)^2),
    sharpData.s*(sharpData.h₁+1)+sharpData.c*(sharpData.h₂+1),
    sharpData.s*(sharpData.h₁+2)-sharpData.c/12,
    sharpData.c*(sharpData.h₁+1)+sharpData.s/12]
def boxLower : Fin 18 → ℝ := ![(979/1000),(39/200),(99/100),(9/125),(-139/1000),(-3/100),(1/100),(1/100),(1/100),(1/100),(1/100),(1/100),(1/100),(11/200),(56/125),-1,(-1/100),(-71/200)]
def boxUpper : Fin 18 → ℝ := ![(981/1000),(201/1000),1,(2/25),(139/1000),(3/100),1,1,1,1,1,1,1,(2/25),(12/25),(-3/10),(-1/250),(-7/20)]
def boxExpressions : Fin 18 → ScalarExpr 8 := ![EqualityGenerated.centralCosineExpression, EqualityGenerated.centralSineExpression, EqualityGenerated.relativeCosineExpression, EqualityGenerated.relativeSineExpression, EqualityGenerated.coreFirstExpression, EqualityGenerated.coreSecondExpression, EqualityGenerated.AMarginExpression, EqualityGenerated.BMarginExpression, EqualityGenerated.DMarginExpression, EqualityGenerated.EMarginExpression, EqualityGenerated.HMarginExpression, EqualityGenerated.GMarginExpression, EqualityGenerated.TMarginExpression, EqualityGenerated.topDiskReserveExpression, EqualityGenerated.tiltedDiskReserveExpression, EqualityGenerated.topHExpression, EqualityGenerated.topGExpression, EqualityGenerated.leftGExpression]

private theorem box_interpretation_0 (p : EqualityParameters) :
    (boxExpressions 0).eval (boxEnv p)=boxData p 0 := by
  simp only [boxExpressions,boxData,rawTiltWidth,EqualityGenerated.centralCosineExpression,
    ScalarExpr.eval,boxEnv,sharpData,radicalCoordinates,EqualityParameters.C,EqualityParameters.S,
    c,s,h₁,h₂,y₄,pA,pB,pD,pE,pH,pG,inFrame,x₃,halfAngleCos,halfAngleSin,div_eq_mul_inv,
    Matrix.cons_val,Matrix.cons_val_zero]
  push_cast
  ring_nf

private theorem box_interpretation_1 (p : EqualityParameters) :
    (boxExpressions 1).eval (boxEnv p)=boxData p 1 := by
  simp only [boxExpressions,boxData,rawTiltWidth,EqualityGenerated.centralSineExpression,
    ScalarExpr.eval,boxEnv,sharpData,radicalCoordinates,EqualityParameters.C,EqualityParameters.S,
    c,s,h₁,h₂,y₄,pA,pB,pD,pE,pH,pG,inFrame,x₃,halfAngleCos,halfAngleSin,div_eq_mul_inv,
    Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one]
  push_cast
  ring_nf

private theorem box_interpretation_2 (p : EqualityParameters) :
    (boxExpressions 2).eval (boxEnv p)=boxData p 2 := by
  simp only [boxExpressions,boxData,rawTiltWidth,EqualityGenerated.relativeCosineExpression,
    ScalarExpr.eval,boxEnv,sharpData,radicalCoordinates,EqualityParameters.C,EqualityParameters.S,
    c,s,h₁,h₂,y₄,pA,pB,pD,pE,pH,pG,inFrame,x₃,halfAngleCos,halfAngleSin,div_eq_mul_inv,
    Matrix.cons_val]
  push_cast
  ring_nf

private theorem box_interpretation_3 (p : EqualityParameters) :
    (boxExpressions 3).eval (boxEnv p)=boxData p 3 := by
  simp only [boxExpressions,boxData,rawTiltWidth,EqualityGenerated.relativeSineExpression,
    ScalarExpr.eval,boxEnv,sharpData,radicalCoordinates,EqualityParameters.C,EqualityParameters.S,
    c,s,h₁,h₂,y₄,pA,pB,pD,pE,pH,pG,inFrame,x₃,halfAngleCos,halfAngleSin,div_eq_mul_inv,
    Matrix.cons_val]
  push_cast
  ring_nf

private theorem box_interpretation_4 (p : EqualityParameters) :
    (boxExpressions 4).eval (boxEnv p)=boxData p 4 := by
  simp only [boxExpressions,boxData,rawTiltWidth,EqualityGenerated.coreFirstExpression,
    ScalarExpr.eval,boxEnv,sharpData,radicalCoordinates,EqualityParameters.C,EqualityParameters.S,
    c,s,h₁,h₂,y₄,pA,pB,pD,pE,pH,pG,inFrame,x₃,halfAngleCos,halfAngleSin,div_eq_mul_inv,
    Matrix.cons_val]
  push_cast
  ring_nf

private theorem box_interpretation_5 (p : EqualityParameters) :
    (boxExpressions 5).eval (boxEnv p)=boxData p 5 := by
  simp only [boxExpressions,boxData,rawTiltWidth,EqualityGenerated.coreSecondExpression,
    ScalarExpr.eval,boxEnv,sharpData,radicalCoordinates,EqualityParameters.C,EqualityParameters.S,
    c,s,h₁,h₂,y₄,pA,pB,pD,pE,pH,pG,inFrame,x₃,halfAngleCos,halfAngleSin,div_eq_mul_inv,
    Matrix.cons_val]
  push_cast
  ring_nf

private theorem box_interpretation_6 (p : EqualityParameters) :
    (boxExpressions 6).eval (boxEnv p)=boxData p 6 := by
  simp only [boxExpressions,boxData,rawTiltWidth,EqualityGenerated.AMarginExpression,
    ScalarExpr.eval,boxEnv,sharpData,radicalCoordinates,EqualityParameters.C,EqualityParameters.S,
    c,s,h₁,h₂,y₄,pA,pB,pD,pE,pH,pG,inFrame,x₃,halfAngleCos,halfAngleSin,div_eq_mul_inv,
    Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one]
  push_cast
  ring_nf

private theorem box_interpretation_7 (p : EqualityParameters) :
    (boxExpressions 7).eval (boxEnv p)=boxData p 7 := by
  simp only [boxExpressions,boxData,rawTiltWidth,EqualityGenerated.BMarginExpression,
    ScalarExpr.eval,boxEnv,sharpData,radicalCoordinates,EqualityParameters.C,EqualityParameters.S,
    c,s,h₁,h₂,y₄,pA,pB,pD,pE,pH,pG,inFrame,x₃,halfAngleCos,halfAngleSin,div_eq_mul_inv,
    Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one]
  push_cast
  ring_nf

private theorem box_interpretation_8 (p : EqualityParameters) :
    (boxExpressions 8).eval (boxEnv p)=boxData p 8 := by
  simp only [boxExpressions,boxData,rawTiltWidth,EqualityGenerated.DMarginExpression,
    ScalarExpr.eval,boxEnv,sharpData,radicalCoordinates,EqualityParameters.C,EqualityParameters.S,
    c,s,h₁,h₂,y₄,pA,pB,pD,pE,pH,pG,inFrame,x₃,halfAngleCos,halfAngleSin,div_eq_mul_inv,
    Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one]
  push_cast
  ring_nf

private theorem box_interpretation_9 (p : EqualityParameters) :
    (boxExpressions 9).eval (boxEnv p)=boxData p 9 := by
  simp only [boxExpressions,boxData,rawTiltWidth,EqualityGenerated.EMarginExpression,
    ScalarExpr.eval,boxEnv,sharpData,radicalCoordinates,EqualityParameters.C,EqualityParameters.S,
    c,s,h₁,h₂,y₄,pA,pB,pD,pE,pH,pG,inFrame,x₃,halfAngleCos,halfAngleSin,div_eq_mul_inv,
    Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one]
  push_cast
  ring_nf

private theorem box_interpretation_10 (p : EqualityParameters) :
    (boxExpressions 10).eval (boxEnv p)=boxData p 10 := by
  simp only [boxExpressions,boxData,rawTiltWidth,EqualityGenerated.HMarginExpression,
    ScalarExpr.eval,boxEnv,sharpData,radicalCoordinates,EqualityParameters.C,EqualityParameters.S,
    c,s,h₁,h₂,y₄,pA,pB,pD,pE,pH,pG,inFrame,x₃,halfAngleCos,halfAngleSin,div_eq_mul_inv,
    Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one]
  push_cast
  ring_nf

private theorem box_interpretation_11 (p : EqualityParameters) :
    (boxExpressions 11).eval (boxEnv p)=boxData p 11 := by
  simp only [boxExpressions,boxData,rawTiltWidth,EqualityGenerated.GMarginExpression,
    ScalarExpr.eval,boxEnv,sharpData,radicalCoordinates,EqualityParameters.C,EqualityParameters.S,
    c,s,h₁,h₂,y₄,pA,pB,pD,pE,pH,pG,inFrame,x₃,halfAngleCos,halfAngleSin,div_eq_mul_inv,
    Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one]
  push_cast
  ring_nf

private theorem box_interpretation_12 (p : EqualityParameters) :
    (boxExpressions 12).eval (boxEnv p)=boxData p 12 := by
  simp only [boxExpressions,boxData,rawTiltWidth,EqualityGenerated.TMarginExpression,
    ScalarExpr.eval,boxEnv,sharpData,radicalCoordinates,EqualityParameters.C,EqualityParameters.S,
    c,s,h₁,h₂,y₄,pA,pB,pD,pE,pH,pG,inFrame,x₃,halfAngleCos,halfAngleSin,div_eq_mul_inv,
    Matrix.cons_val]
  push_cast
  ring_nf

private theorem box_interpretation_13 (p : EqualityParameters) :
    (boxExpressions 13).eval (boxEnv p)=boxData p 13 := by
  simp only [boxExpressions,boxData,rawTiltWidth,EqualityGenerated.topDiskReserveExpression,
    ScalarExpr.eval,boxEnv,sharpData,radicalCoordinates,EqualityParameters.C,EqualityParameters.S,
    c,s,h₁,h₂,y₄,pA,pB,pD,pE,pH,pG,inFrame,x₃,halfAngleCos,halfAngleSin,div_eq_mul_inv,
    Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one]
  push_cast
  ring_nf

private theorem box_interpretation_14 (p : EqualityParameters) :
    (boxExpressions 14).eval (boxEnv p)=boxData p 14 := by
  simp only [boxExpressions,boxData,rawTiltWidth,EqualityGenerated.tiltedDiskReserveExpression,
    ScalarExpr.eval,boxEnv,sharpData,radicalCoordinates,EqualityParameters.C,EqualityParameters.S,
    c,s,h₁,h₂,y₄,pA,pB,pD,pE,pH,pG,inFrame,x₃,halfAngleCos,halfAngleSin,div_eq_mul_inv,
    Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one]
  push_cast
  ring_nf

private theorem box_interpretation_15 (p : EqualityParameters) :
    (boxExpressions 15).eval (boxEnv p)=boxData p 15 := by
  simp only [boxExpressions,boxData,rawTiltWidth,EqualityGenerated.topHExpression,
    ScalarExpr.eval,boxEnv,sharpData,radicalCoordinates,EqualityParameters.C,EqualityParameters.S,
    c,s,h₁,h₂,y₄,pA,pB,pD,pE,pH,pG,inFrame,x₃,halfAngleCos,halfAngleSin,div_eq_mul_inv,
    Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one]
  push_cast
  ring_nf

private theorem box_interpretation_16 (p : EqualityParameters) :
    (boxExpressions 16).eval (boxEnv p)=boxData p 16 := by
  simp only [boxExpressions,boxData,rawTiltWidth,EqualityGenerated.topGExpression,
    ScalarExpr.eval,boxEnv,sharpData,radicalCoordinates,EqualityParameters.C,EqualityParameters.S,
    c,s,h₁,h₂,y₄,pA,pB,pD,pE,pH,pG,inFrame,x₃,halfAngleCos,halfAngleSin,div_eq_mul_inv,
    Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one]
  push_cast
  ring_nf

private theorem box_interpretation_17 (p : EqualityParameters) :
    (boxExpressions 17).eval (boxEnv p)=boxData p 17 := by
  simp only [boxExpressions,boxData,rawTiltWidth,EqualityGenerated.leftGExpression,
    ScalarExpr.eval,boxEnv,sharpData,radicalCoordinates,EqualityParameters.C,EqualityParameters.S,
    c,s,h₁,h₂,y₄,pA,pB,pD,pE,pH,pG,inFrame,x₃,halfAngleCos,halfAngleSin,div_eq_mul_inv,
    Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one]
  push_cast
  ring_nf

theorem box_interpretation (p : EqualityParameters) (i : Fin 18) :
    (boxExpressions i).eval (boxEnv p)=boxData p i := by
  fin_cases i
  · exact box_interpretation_0 p
  · exact box_interpretation_1 p
  · exact box_interpretation_2 p
  · exact box_interpretation_3 p
  · exact box_interpretation_4 p
  · exact box_interpretation_5 p
  · exact box_interpretation_6 p
  · exact box_interpretation_7 p
  · exact box_interpretation_8 p
  · exact box_interpretation_9 p
  · exact box_interpretation_10 p
  · exact box_interpretation_11 p
  · exact box_interpretation_12 p
  · exact box_interpretation_13 p
  · exact box_interpretation_14 p
  · exact box_interpretation_15 p
  · exact box_interpretation_16 p
  · exact box_interpretation_17 p

theorem box_data_bounds {p : EqualityParameters} (hp : p.InBox) (i : Fin 18) :
    boxLower i≤boxData p i ∧ boxData p i≤boxUpper i := by
  have he := boxEnv_mem hp
  rw [← box_interpretation p i]
  fin_cases i
  · exact EqualityGenerated.centralCosine_bound _ he
  · exact EqualityGenerated.centralSine_bound _ he
  · exact EqualityGenerated.relativeCosine_bound _ he
  · exact EqualityGenerated.relativeSine_bound _ he
  · exact EqualityGenerated.coreFirst_bound _ he
  · exact EqualityGenerated.coreSecond_bound _ he
  · exact EqualityGenerated.AMargin_bound _ he
  · exact EqualityGenerated.BMargin_bound _ he
  · exact EqualityGenerated.DMargin_bound _ he
  · exact EqualityGenerated.EMargin_bound _ he
  · exact EqualityGenerated.HMargin_bound _ he
  · exact EqualityGenerated.GMargin_bound _ he
  · exact EqualityGenerated.TMargin_bound _ he
  · exact EqualityGenerated.topDiskReserve_bound _ he
  · exact EqualityGenerated.tiltedDiskReserve_bound _ he
  · exact EqualityGenerated.topH_bound _ he
  · exact EqualityGenerated.topG_bound _ he
  · exact EqualityGenerated.leftG_bound _ he

end SquaresInCircles.Eight.Stationary
