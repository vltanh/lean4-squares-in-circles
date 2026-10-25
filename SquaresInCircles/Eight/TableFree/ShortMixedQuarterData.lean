module

public import SquaresInCircles.Eight.TableFree.ShortWordZero
public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreeReferenceAlgebra

/-!
# Literal normalized mixed quarter-one rows of 0010111

Uncompiled transcription of Section 1 of
`SHORT_WRONG_WORD_ALL_MIXED_ONE_HAND_PROOF.md`.
The twenty-four rows in each radial order are the original signed role
coefficients and their exact reflected reversals. They contain no angle
or state subdivision. Both closed core pieces have the same affine label.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortWord.MixedQuarter
open CommonQuarter CorePairGeometry Arithmetic TableFreeWordGeometry WordProblems

abbrev Row := Fin 24
def edge : Row→Vertex := ![2,2,2,2,4,4,4,4,4,4,4,4,5,5,5,5,5,5,5,5,6,6,6,6]
def reversed (r : Row) : Bool := r.val%2=1
def sourcePositive : Row→Bool :=
  ![false,true,false,false,false,true,false,false,true,true,true,false,
    false,true,false,false,true,true,true,false,false,false,true,false]
def targetPositive : Row→Bool :=
  ![false,true,true,true,false,true,true,true,false,false,true,false,
    false,true,true,true,false,false,true,false,true,true,true,false]
def sourceSign (r : Row) : ℝ := WordProblems.sign (sourcePositive r)
def targetSign (r : Row) : ℝ := WordProblems.sign (targetPositive r)

def coC : Row→ℝ := fun r =>
  (![-39186,12917,80483,-6772,-25682,-24510,1449,-25931,-3767,5267,23364,3846,
    19687,21928,21731,20507,21108,-5203,23152,-6624,7651,-21837,9072,-23881] r)/100000
def coP : Row→ℝ := fun r =>
  (![-33147,-9133,51554,-9133,-20967,-19335,0,-19335,-20967,0,0,0,
    18602,20967,21826,20967,18602,0,21826,0,0,-18602,0,-21826] r)/100000
def coQ : Row→ℝ := fun r =>
  (![113360,88074,119909,88074,83048,76744,86884,76744,83048,71553,86884,71553,
    80996,83048,83472,83048,80996,86884,83472,86884,94766,80996,94766,83472] r)/100000
def coG : Row→ℝ := fun r =>
  (![113855,62750,113855,104729,104073,95269,104073,99195,58829,95269,58829,99195,
    95269,99173,95269,95324,99195,99173,99195,95324,99173,108816,95324,108816] r)/100000
def ocC : Row→ℝ := fun r =>
  (![12917,-39186,-6772,80483,-24510,-25682,-25931,1449,5267,-3767,3846,23364,
    21928,19687,20507,21731,-5203,21108,-6624,23152,-21837,7651,-23881,9072] r)/100000
def ocP : Row→ℝ := fun r =>
  (![9133,33147,9133,-51554,19335,20967,19335,0,0,20967,0,0,
    -20967,-18602,-20967,-21826,0,-18602,0,-21826,18602,0,21826,0] r)/100000
def ocQ : Row→ℝ := fun r =>
  (![88074,113360,88074,119909,76744,83048,76744,86884,71553,83048,71553,86884,
    83048,80996,83048,83472,86884,80996,86884,83472,80996,94766,83472,94766] r)/100000
def ocG : Row→ℝ := fun r =>
  (![62750,113855,104729,113855,95269,104073,99195,104073,95269,58829,99195,58829,
    99173,95269,95324,95269,99173,99195,95324,99195,108816,99173,108816,95324] r)/100000

def coreOuterCost (r : Row) (a b A B φ : ℝ) : ℝ :=
  φ+coC r+sourceSign r*coG r*b-coP r*A-targetSign r*coQ r*B
def outerCoreCost (r : Row) (a b A B φ : ℝ) : ℝ :=
  φ+ocC r+ocP r*a+sourceSign r*ocQ r*b-targetSign r*ocG r*B
def sourceSecondary (r : Row) (a b A B φ : ℝ) : Prop :=
  pairWidth φ≤ sourceSign r*b+A*Real.sin φ-targetSign r*B*Real.cos φ
def sourcePrimary (r : Row) (a b A B φ : ℝ) : Prop :=
  pairWidth φ≤a-A*Real.cos φ-targetSign r*B*Real.sin φ

def literalCoreOuter (r : Row) (core : RadialKind) (a b A B φ : ℝ) : ℝ :=
  if reversed r then
    φ+wrongValue .short (edge r) .outer (!targetPositive r) A B-
      wrongValue .short (next (edge r)) core (!sourcePositive r) a b
  else φ+wrongValue .short (edge r) core (sourcePositive r) a b-
    wrongValue .short (next (edge r)) .outer (targetPositive r) A B
def literalOuterCore (r : Row) (core : RadialKind) (a b A B φ : ℝ) : ℝ :=
  if reversed r then
    φ+wrongValue .short (edge r) core (!targetPositive r) A B-
      wrongValue .short (next (edge r)) .outer (!sourcePositive r) a b
  else φ+wrongValue .short (edge r) .outer (sourcePositive r) a b-
    wrongValue .short (next (edge r)) core (targetPositive r) A B

theorem coreOuter_literal (r : Row) (core : RadialKind) (hc : core≠.outer)
    (a b A B φ : ℝ) : coreOuterCost r a b A B φ=literalCoreOuter r core a b A B φ := by
  fin_cases r <;> cases core <;> (try exact absurd rfl hc) <;>
    norm_num [literalCoreOuter,coreOuterCost,edge,reversed,sourcePositive,targetPositive,
      sourceSign,targetSign,coC,coP,coQ,coG,wrongValue,shortCoefficients,radialIndex,
      signIndex,WordProblems.sign,next] <;> ring
theorem outerCore_literal (r : Row) (core : RadialKind) (hc : core≠.outer)
    (a b A B φ : ℝ) : outerCoreCost r a b A B φ=literalOuterCore r core a b A B φ := by
  fin_cases r <;> cases core <;> (try exact absurd rfl hc) <;>
    norm_num [literalOuterCore,outerCoreCost,edge,reversed,sourcePositive,targetPositive,
      sourceSign,targetSign,ocC,ocP,ocQ,ocG,wrongValue,shortCoefficients,radialIndex,
      signIndex,WordProblems.sign,next] <;> ring

def direction (upper : Bool) : ℝ := if upper then 1 else -1
def angle (upper : Bool) (x : ℝ) : ℝ := Real.pi/2+direction upper*x

theorem angle_sin (upper : Bool) (x : ℝ) : Real.sin (angle upper x)=Real.cos x := by
  cases upper <;> simp [angle,direction,Real.sin_add,Real.cos_neg]
theorem angle_cos (upper : Bool) (x : ℝ) : Real.cos (angle upper x)= -direction upper*Real.sin x := by
  cases upper <;> simp [angle,direction,Real.cos_add,Real.sin_neg]
theorem angle_width (upper : Bool) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    pairWidth (angle upper x)=(1+Real.cos x+Real.sin x)/2 := by
  have ht := positive_trig hx
  rw [pairWidth,angle_sin,angle_cos,abs_of_pos (by linarith [ht.1])]
  cases upper <;> simp [direction,abs_of_nonneg ht.2.2.1]

theorem core_circle_lower {a b X Y : ℝ} (hc : CoreState a b) (hY : Y≤0) :
    (X+Y)/2-(1/12)*Real.sqrt (X^2+Y^2)≤X*a+Y*b := by
  rcases hc with ⟨rfl,hb,hbu⟩ | ⟨hb,hab,hcircle⟩
  · have h := full_circle_lower (v:=(1/2:ℝ)) (ρ:=(1/12:ℝ))
      (a:=(7/12:ℝ)) (b:=(1/2:ℝ)) (X:=X) (Y:=Y) (by norm_num) (by norm_num)
    have hy := mul_le_mul_of_nonpos_left hbu hY
    linarith
  · have h := full_circle_lower (v:=(1/2:ℝ)) (ρ:=(1/12:ℝ))
      (X:=X) (Y:=Y) (by norm_num) hcircle
    linarith

theorem core_axial_lower {a b X Y : ℝ} (hc : CoreState a b) (hX : X≤0) (hY : 0≤Y) :
    X*(7/12)≤X*a+Y*b := by
  have hb := CoreAngleEndpoint.state_bounds hc
  have h1 := mul_le_mul_of_nonpos_left hb.2.1 hX
  have h2 := mul_nonneg hY hb.2.2.1
  linarith

theorem outer_axial_lower {a b X Y : ℝ} (hs : OuterState a b) (hX : X≤0) (hY : 0≤Y) :
    X*outerAxial≤X*a+Y*b := by
  have hb := outer_bounds hs
  have h1 := mul_le_mul_of_nonpos_left hb.2.1 hX
  have h2 := mul_nonneg hY hb.2.2.1
  linarith

theorem coefficient_bounds (r : Row) :
    0<coG r ∧ coG r<1139/1000 ∧ 0<coQ r ∧ coQ r<6/5 ∧
    0<ocG r ∧ ocG r<1139/1000 ∧ 0<ocQ r ∧ ocQ r<6/5 ∧
    (129/200)*coG r<coQ r ∧ 0<coP r+(191/250)*coG r ∧
    (129/200)*ocQ r<ocG r := by
  fin_cases r <;> norm_num [coP,coQ,coG,ocP,ocQ,ocG]

theorem targetSign_negative {r : Row} (hr : targetPositive r=false) : targetSign r= -1 := by
  simp [targetSign,WordProblems.sign,hr]
theorem targetSign_positive {r : Row} (hr : targetPositive r=true) : targetSign r=1 := by
  simp [targetSign,WordProblems.sign,hr]

end SquaresInCircles.Eight.TableFree.ShortWord.MixedQuarter
