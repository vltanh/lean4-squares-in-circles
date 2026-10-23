module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneEdgeFiveASecondary

/-!
# The two upper A-primary supports

Uncompiled transcription of Section 6, equations (31)--(32).
The source is the actual axial endpoint and the target uses the stated
whole-circle norm. Its exact perpendicular-square identity supplies the
Cauchy derivative bound on the whole upper angle half.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.EdgeFive.APrimary.Upper
open CommonQuarter CorePairGeometry Arithmetic StationaryPrimitives
open ShortWord.MixedQuarter.Reference

def normA (r : Row) : ℝ := P r^2+t r^2+(4/5:ℝ)^2
def normB (r : Row) : ℝ := -(8/5)*t r
def normC (r : Row) : ℝ := (8/5)*P r
def N (r : Row) (x : ℝ) : ℝ := CircularNorm.norm (normA r) (normB r) (normC r) x
def G (r : Row) (x : ℝ) : ℝ :=
  Real.pi/2+x+c r+(p r-4/5)*outerAxial+(4/5+P r+t r)/2+(4/5)*Real.sin x-radius*N r x
def first (r : Row) (x : ℝ) : ℝ :=
  1+(4/5)*Real.cos x-radius*CircularNorm.d1 (normA r) (normB r) (normC r) x

theorem energy_identity (r : Row) (x : ℝ) :
    CircularNorm.energy (normA r) (normB r) (normC r) x=
      (P r+(4/5)*Real.sin x)^2+(t r-(4/5)*Real.cos x)^2 := by
  dsimp [CircularNorm.energy,normA,normB,normC]
  linear_combination -(16/25:ℝ)*(Real.sin_sq_add_cos_sq x)
theorem energy_positive (r : Row) (hr : ARows r) (x : ℝ) :
    0<CircularNorm.energy (normA r) (normB r) (normC r) x := by
  have ht : 0<t r-(4/5)*Real.cos x := by linarith [(A_bounds r hr).2.2.1,Real.cos_le_one x]
  rw [energy_identity]
  nlinarith [sq_nonneg (P r+(4/5)*Real.sin x)]
theorem norm_positive (r : Row) (hr : ARows r) (x : ℝ) : 0<N r x :=
  CircularNorm.norm_pos (energy_positive r hr x)
theorem norm_sq (r : Row) (hr : ARows r) (x : ℝ) :
    (N r x)^2=(P r+(4/5)*Real.sin x)^2+(t r-(4/5)*Real.cos x)^2 := by
  exact (CircularNorm.norm_sq (energy_positive r hr x).le).trans (energy_identity r x)
theorem norm_hasDerivAt (r : Row) (hr : ARows r) (x : ℝ) :
    HasDerivAt (N r) (CircularNorm.d1 (normA r) (normB r) (normC r) x) x :=
  CircularNorm.norm_hasDerivAt (energy_positive r hr x)
theorem perpendicular_square (r : Row) (hr : ARows r) (x : ℝ) :
    (N r x)^2-(P r*Real.cos x+t r*Real.sin x)^2=
      (P r*Real.sin x-t r*Real.cos x+4/5)^2 := by
  have hn := norm_sq r hr x
  linear_combination hn+((16/25:ℝ)-P r^2-t r^2)*(Real.sin_sq_add_cos_sq x)
theorem cauchy (r : Row) (hr : ARows r) (x : ℝ) :
    |P r*Real.cos x+t r*Real.sin x|≤N r x := by
  have hh := perpendicular_square r hr x
  have hn := norm_positive r hr x
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (P r*Real.sin x-t r*Real.cos x+4/5)]
theorem norm_derivative_upper (r : Row) (hr : ARows r) (x : ℝ) :
    CircularNorm.d1 (normA r) (normB r) (normC r) x≤4/5 := by
  have hn := norm_positive r hr x
  have hh := (le_abs_self _).trans (cauchy r hr x)
  have he : CircularNorm.d1 (normA r) (normB r) (normC r) x=
      ((4/5)*(P r*Real.cos x+t r*Real.sin x))/N r x := by
    dsimp [CircularNorm.d1,CircularNorm.slope,normB,normC]
    change _/(2*N r x)=_
    field_simp [hn.ne']
    ring
  rw [he]
  apply (div_le_iff₀ hn).mpr
  nlinarith
theorem G_hasDerivAt (r : Row) (hr : ARows r) (x : ℝ) :
    HasDerivAt (G r) (first r x) x := by
  convert (((hasDerivAt_id x).const_add
    (Real.pi/2+c r+(p r-4/5)*outerAxial+(4/5+P r+t r)/2)).add
      ((Real.hasDerivAt_sin x).const_mul (4/5))).sub
        ((norm_hasDerivAt r hr x).const_mul radius) using 1 <;> dsimp [G,first] <;> ring
theorem first_positive (r : Row) (hr : ARows r) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    0<first r x := by
  have hh := mul_le_mul_of_nonneg_left (norm_derivative_upper r hr x)
    (show 0≤radius by linarith [radius_bounds.1])
  dsimp [first]
  linarith [(positive_trig hx).1,radius_fine.2]
theorem G_monotone (r : Row) (hr : ARows r) : MonotoneOn (G r) (Icc 0 (7/10)) :=
  monoOn_of_hasDeriv_nonneg
    (fun x _ => (G_hasDerivAt r hr x).continuousAt.continuousWithinAt)
    (fun x _ => G_hasDerivAt r hr x)
    (fun x hx => (first_positive r hr (Ioo_subset_Icc_self hx)).le)

def initialNormBox (r : Row) : Interval (N r 0) := by
  let E := Interval.point (P r^2+(t r-4/5)^2)
  convert rootSix E 1 (by norm_num) (by dsimp [E,Interval.point]; positivity) using 1
  dsimp [N,CircularNorm.norm]
  rw [energy_identity]
  simp
def initialBox (r : Row) : Interval (G r 0) := by
  convert ((((halfPi.add (Interval.point (c r))).add
    ((Interval.point (p r-4/5)).mul axial)).add (Interval.point ((4/5+P r+t r)/2))).sub
      (circleRadius.mul (initialNormBox r))) using 1
  simp [G]
theorem initial (r : Row) (hr : ARows r) : (1449/1250:ℝ)<G r 0 := by
  have hh : (1449/1250:ℝ)<(initialBox r).lo := by
    rcases hr with rfl|rfl <;> dsimp [initialBox,initialNormBox,c,p,P,t] <;> mixed_fixed
  exact hh.trans_le (initialBox r).mem.1
theorem lower (r : Row) (hr : ARows r) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (1449/1250:ℝ)<G r x := (initial r hr).trans_le (G_monotone r hr (by norm_num) hx hx.1)

theorem original (r : Row) (hr : ARows r) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : Primary r true a b A B x) : (1449/1250:ℝ)<cost r true a b A B x := by
  have hcoeff := coefficient_bounds r
  have hsource := ShortWord.MixedQuarter.outer_axial_lower (X:=p r-4/5) (Y:=q r) hs
    (by linarith [hcoeff.1]) (by linarith [hcoeff.2.2.1])
  let X := -P r-(4/5)*Real.sin x
  let Y := (4/5)*Real.cos x-t r
  have he : Real.sqrt (X^2+Y^2)=N r x := by
    dsimp [N,CircularNorm.norm]
    congr 1
    rw [energy_identity]
    dsimp [X,Y]
    ring
  have htarg := outer_circle_lower (X:=X) (Y:=Y) ht
  rw [he] at htarg
  have hh := primary_support r true (λ:=4/5) (by norm_num) hm
    (S:=(p r-4/5)*outerAxial) (T:= -(X+Y)/2-radius*N r x)
    (by rw [A_sign hr]; nlinarith [hsource])
    (by rw [A_sign hr]; exact htarg)
  have hv := lower r hr hx
  dsimp [G,X,Y,width,angle,direction] at *
  nlinarith

end SquaresInCircles.Eight.TableFree.ShortOuterOne.EdgeFive.APrimary.Upper
