module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneEdgeFiveASecondaryData

/-!
# The A-secondary endpoint comparisons

Uncompiled transcription of the fixed comparisons in Section 3.
The lower-half cap retains the strict .8981 reserve. All radicals are
enclosed by positive rational square refinements at the stated endpoints;
these are proof expressions, with no certificate evaluation performed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.EdgeFive.ASecondary.Endpoint
open CommonQuarter Arithmetic StationaryPrimitives
open ShortWord.MixedQuarter.Reference

theorem upper_norm_initial (r : Row) (hr : ARows r) : (63/50:ℝ)<N r true 0 := by
  have hn := norm_positive r hr true (show (0:ℝ)∈Icc 0 (7/10) by norm_num)
  have hs := norm_initial r true
  rcases hr with rfl|rfl <;> norm_num [P,t,weight] at hs <;> nlinarith
theorem lower_norm_initial (r : Row) (hr : ARows r) : N r false 0<343/250 := by
  have hn := norm_positive r hr false (show (0:ℝ)∈Icc 0 (7/10) by norm_num)
  have hs := norm_initial r false
  rcases hr with rfl|rfl <;> norm_num [P,t,q,weight] at hs <;> nlinarith
theorem lower_coef (r : Row) (hr : ARows r) :
    (129/200:ℝ)*(N r false 0)^2<2*weight r false*t r := by
  rw [norm_initial]
  rcases hr with rfl|rfl <;> norm_num [P,t,q,weight]
theorem lower_curvature_reserve (r : Row) (hr : ARows r) :
    radius*N r false 0<4*weight r false := by
  have hR : 0<radius := by linarith [radius_bounds.1]
  have hh := mul_lt_mul_of_pos_left (lower_norm_initial r hr) hR
  have hλ := (lower_weight r hr).1
  nlinarith [radius_fine.2]

def sourceBox (r : Row) (upper : Bool) : Interval (source r upper) := by
  cases upper
  · by_cases h : r=0
    · subst r
      exact Interval.point 0
    · let X := Interval.point (p r^2+(q r-weight r false)^2)
      let S := rootSix X 1 (by norm_num) (by dsimp [X,Interval.point]; positivity)
      convert (Interval.point (-(p r+q r-weight r false)/2)).sub (circleRadius.mul S) using 1
      simp [source,h]
  · exact (Interval.point (p r)).mul axial
def initialNormBox (r : Row) (upper : Bool) : Interval (N r upper 0) := by
  let X := Interval.point ((P r+weight r upper)^2+t r^2)
  convert rootSix X 2 (by norm_num) (by dsimp [X,Interval.point]; positivity) using 1
  dsimp [N,CircularNorm.norm,CircularNorm.energy,normA,normB,normC,X]
  simp only [Real.cos_zero,Real.sin_zero]
  congr 1
  ring
def initialBox (r : Row) (upper : Bool) : Interval (F r upper 0) := by
  convert (((((halfPi.add (Interval.point (c r))).add (sourceBox r upper)).add
    (Interval.point ((weight r upper+P r+t r)/2))).add (Interval.point (weight r upper))).sub
      (circleRadius.mul (initialNormBox r upper))) using 1
  simp [F,angle]
def capNormBox (r : Row) (hr : ARows r) : Interval (N r false (7/10)) := by
  let E := ((Interval.point (normA r false)).add
    ((Interval.point (normB r false)).mul (cosine (by norm_num : (0:ℝ)≤7/10)))).add
      ((Interval.point (normC r false)).mul (sine (by norm_num : (0:ℝ)≤7/10)))
  have hE : 0≤E.lo := by
    rcases hr with rfl|rfl <;> dsimp [E,normA,normB,normC,weight,P,t,q,direction] <;> mixed_fixed
  exact rootSix E 1 (by norm_num) hE
def capBox (r : Row) (hr : ARows r) : Interval (F r false (7/10)) := by
  convert ((((((halfPi.sub (Interval.point (7/10))).add (Interval.point (c r))).add
    (sourceBox r false)).add (Interval.point ((weight r false+P r+t r)/2))).add
      ((Interval.point (weight r false)).mul (cosine (by norm_num : (0:ℝ)≤7/10)))).sub
        (circleRadius.mul (capNormBox r hr))) using 1
  dsimp [F,angle,direction]
  ring

theorem upper_initial (r : Row) (hr : ARows r) : (4619/5000:ℝ)<F r true 0 := by
  have hh : (4619/5000:ℝ)<(initialBox r true).lo := by
    rcases hr with rfl|rfl <;>
      dsimp [initialBox,sourceBox,initialNormBox,weight,c,p,q,P,t] <;> mixed_fixed
  exact hh.trans_le (initialBox r true).mem.1
theorem lower_initial (r : Row) (hr : ARows r) : (4587/5000:ℝ)<F r false 0 := by
  have hh : (4587/5000:ℝ)<(initialBox r false).lo := by
    rcases hr with rfl|rfl <;>
      dsimp [initialBox,sourceBox,initialNormBox,weight,c,p,q,P,t] <;> mixed_fixed
  exact hh.trans_le (initialBox r false).mem.1
theorem lower_terminal (r : Row) (hr : ARows r) : (8981/10000:ℝ)<F r false (7/10) := by
  have hh : (8981/10000:ℝ)<(capBox r hr).lo := by
    rcases hr with rfl|rfl <;>
      dsimp [capBox,sourceBox,capNormBox,normA,normB,normC,weight,c,p,q,P,t,direction] <;> mixed_fixed
  exact hh.trans_le (capBox r hr).mem.1

end SquaresInCircles.Eight.TableFree.ShortOuterOne.EdgeFive.ASecondary.Endpoint
