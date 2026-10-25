module

public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterData
public import SquaresInCircles.Eight.Words.Short.Outer.Zero.PositivePrimary

/-!
# Eight squares: the four literal same-sign edge-five normalizations

Rows 0 and 1 are A₀ and A₁; rows 2 and 3 are B₀ and B₁. The
normalizations are exact reflection/reversals of original owners.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.EdgeFive
open CommonQuarter CorePairGeometry Arithmetic

abbrev Row := Fin 4
abbrev angle := ShortWord.MixedQuarter.angle
abbrev direction := ShortWord.MixedQuarter.direction
def c : Row→ℝ := ![23152/100000,48239/100000,48239/100000,23152/100000]
def p : Row→ℝ := ![0,-18602/100000,-20967/100000,-21826/100000]
def q : Row→ℝ := ![86884/100000,80996/100000,83048/100000,83472/100000]
def P : Row→ℝ := ![21826/100000,20967/100000,18602/100000,0]
def t : Row→ℝ := ![83472/100000,83048/100000,80996/100000,86884/100000]
def positive : Row→Bool := ![true,true,false,false]
def σ (r : Row) : ℝ := WordProblems.sign (positive r)
def ARows (r : Row) : Prop := r=0∨r=1
def BRows (r : Row) : Prop := r=2∨r=3
def width (x : ℝ) : ℝ := (1+Real.cos x+Real.sin x)/2
def cost (r : Row) (upper : Bool) (a b A B x : ℝ) : ℝ :=
  angle upper x+c r+p r*a+σ r*q r*b-P r*A-σ r*t r*B
def Secondary (r : Row) (upper : Bool) (_a b A B x : ℝ) : Prop :=
  width x≤σ r*b+A*Real.cos x+σ r*direction upper*B*Real.sin x
def Primary (r : Row) (upper : Bool) (a _b A B x : ℝ) : Prop :=
  width x≤a+direction upper*A*Real.sin x-σ r*B*Real.cos x

theorem A_sign {r : Row} (hr : ARows r) : σ r=1 := by
  rcases hr with rfl|rfl <;> norm_num [σ,positive,WordProblems.sign]
theorem B_sign {r : Row} (hr : BRows r) : σ r= -1 := by
  rcases hr with rfl|rfl <;> norm_num [σ,positive,WordProblems.sign]
theorem coefficient_bounds (r : Row) :
    p r≤0 ∧ 0≤P r ∧ (809/1000:ℝ)<q r ∧ q r<87/100 ∧
      (809/1000:ℝ)<t r ∧ t r<87/100 := by
  fin_cases r <;> norm_num [p,P,q,t]
theorem A_bounds (r : Row) (hr : ARows r) :
    (209/1000:ℝ)<P r ∧ P r<219/1000 ∧ 83/100<t r ∧ t r≤5217/6250 := by
  rcases hr with rfl|rfl <;> norm_num [P,t]

theorem secondary_support (r : Row) (upper : Bool) {a b A B x lam S T : ℝ}
    (hlam : 0≤lam) (hm : Secondary r upper a b A B x)
    (hs : S≤p r*a+σ r*(q r-lam)*b)
    (ht : T≤(-P r-lam*Real.cos x)*A+σ r*(-direction upper*lam*Real.sin x-t r)*B) :
    angle upper x+c r+lam*width x+S+T≤cost r upper a b A B x := by
  have hh := mul_le_mul_of_nonneg_left hm hlam
  dsimp [Secondary,cost] at *
  nlinarith
theorem primary_support (r : Row) (upper : Bool) {a b A B x lam S T : ℝ}
    (hlam : 0≤lam) (hm : Primary r upper a b A B x)
    (hs : S≤(p r-lam)*a+σ r*q r*b)
    (ht : T≤(-P r-direction upper*lam*Real.sin x)*A+σ r*(lam*Real.cos x-t r)*B) :
    angle upper x+c r+lam*width x+S+T≤cost r upper a b A B x := by
  have hh := mul_le_mul_of_nonneg_left hm hlam
  dsimp [Primary,cost] at *
  nlinarith

theorem outer_endpoint_support {a b X Y : ℝ} (hs : OuterState a b) (hY : 0≤Y) :
    min (X*outerAxial) ((X+Y)*outerDiagonal)≤X*a+Y*b :=
  outer_endpoints_lower hs hY (min_le_left _ _) (min_le_right _ _)

theorem trigonometric_norm (X Y x : ℝ) :
    |X*Real.cos x+Y*Real.sin x|≤Real.sqrt (X^2+Y^2) := by
  have hs := Real.sq_sqrt (show 0≤X^2+Y^2 by positivity)
  have hp := Real.sqrt_nonneg (X^2+Y^2)
  have hid : (X*Real.cos x+Y*Real.sin x)^2+(X*Real.sin x-Y*Real.cos x)^2=X^2+Y^2 := by
    linear_combination (X^2+Y^2)*(Real.sin_sq_add_cos_sq x)
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (X*Real.sin x-Y*Real.cos x)]
theorem axial_norm_bound : Real.sqrt ((1/2:ℝ)^2+(outerAxial-1/2)^2)<1043/1000 := by
  have ha := ShortOuterZero.fine_axial_bounds
  have hs := Real.sq_sqrt (show 0≤(1/2:ℝ)^2+(outerAxial-1/2)^2 by positivity)
  have hp := Real.sqrt_nonneg ((1/2:ℝ)^2+(outerAxial-1/2)^2)
  nlinarith
theorem axial_trig_upper (x : ℝ) :
    (1/2)*Real.cos x+(outerAxial-1/2)*Real.sin x<1043/1000 :=
  (le_abs_self _).trans_lt
    ((trigonometric_norm (1/2) (outerAxial-1/2) x).trans_lt axial_norm_bound)

theorem secondary_margin (r : Row) (upper : Bool) {a b A B x : ℝ} (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 0 a b A B (σ r) (σ r) (angle upper x)) :
    Secondary r upper a b A B x := by
  dsimp [Eight.forwardMargin] at hm
  rw [ShortWord.MixedQuarter.angle_sin,ShortWord.MixedQuarter.angle_cos,
    ShortWord.MixedQuarter.angle_width upper hx] at hm
  dsimp [Secondary,width]
  linarith
theorem primary_margin (r : Row) (upper : Bool) {a b A B x : ℝ} (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 3 a b A B (σ r) (σ r) (angle upper x)) :
    Primary r upper a b A B x := by
  dsimp [Eight.forwardMargin] at hm
  rw [ShortWord.MixedQuarter.angle_sin,ShortWord.MixedQuarter.angle_cos,
    ShortWord.MixedQuarter.angle_width upper hx] at hm
  dsimp [Primary,width]
  linarith

end SquaresInCircles.Eight.ShortOuterOne.EdgeFive
