module

public import SquaresInCircles.Eight.ExactFamily.EqualityGeometry

/-! Uncompiled interpretation of the eighteen exact equality-box expressions. -/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.ExactFamily
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

theorem box_interpretation (p : EqualityParameters) (i : Fin 18) :
    (boxExpressions i).eval (boxEnv p)=boxData p i := by
  fin_cases i <;>
    norm_num [boxExpressions,boxData,rawTiltWidth,EqualityGenerated.centralCosineExpression, EqualityGenerated.centralSineExpression, EqualityGenerated.relativeCosineExpression, EqualityGenerated.relativeSineExpression, EqualityGenerated.coreFirstExpression, EqualityGenerated.coreSecondExpression, EqualityGenerated.AMarginExpression, EqualityGenerated.BMarginExpression, EqualityGenerated.DMarginExpression, EqualityGenerated.EMarginExpression, EqualityGenerated.HMarginExpression, EqualityGenerated.GMarginExpression, EqualityGenerated.TMarginExpression, EqualityGenerated.topDiskReserveExpression, EqualityGenerated.tiltedDiskReserveExpression, EqualityGenerated.topHExpression, EqualityGenerated.topGExpression, EqualityGenerated.leftGExpression,ScalarExpr.eval,boxEnv,
      sharpData,radicalCoordinates,EqualityParameters.C,EqualityParameters.S,
      c,s,h₁,h₂,y₄,pA,pB,pD,pE,pH,pG,inFrame,x₃,
      halfAngleCos,halfAngleSin,div_eq_mul_inv] <;> ring

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

end SquaresInCircles.Eight.ExactFamily
