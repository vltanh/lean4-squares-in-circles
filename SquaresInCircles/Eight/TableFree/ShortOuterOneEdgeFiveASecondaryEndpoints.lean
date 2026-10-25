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
    CommonQuarter.radius*N r false 0<4*weight r false := by
  have hR : 0<CommonQuarter.radius := by linarith [radius_bounds.1]
  have hh := mul_lt_mul_of_pos_left (lower_norm_initial r hr) hR
  have hlam := (lower_weight r hr).1
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
  simp [F,ShortWord.MixedQuarter.angle]
def capNormBox (r : Row) (hr : ARows r) : Interval (N r false (7/10)) := by
  let E := ((Interval.point (normA r false)).add
    ((Interval.point (normB r false)).mul (cosine (by norm_num : (0:ℝ)≤7/10)))).add
      ((Interval.point (normC r false)).mul (sine (by norm_num : (0:ℝ)≤7/10)))
  have hE : 0≤E.lo := by
    rcases hr with rfl|rfl <;> dsimp [E,normA,normB,normC,weight,P,t,q,direction,ShortWord.MixedQuarter.direction] <;> mixed_fixed
  exact rootSix E 1 (by norm_num) hE
def capBox (r : Row) (hr : ARows r) : Interval (F r false (7/10)) := by
  convert ((((((halfPi.sub (Interval.point (7/10))).add (Interval.point (c r))).add
    (sourceBox r false)).add (Interval.point ((weight r false+P r+t r)/2))).add
      ((Interval.point (weight r false)).mul (cosine (by norm_num : (0:ℝ)≤7/10)))).sub
        (circleRadius.mul (capNormBox r hr))) using 1
  simp [F,ShortWord.MixedQuarter.angle,ShortWord.MixedQuarter.direction]
  ring

-- The three endpoint values below evaluate `initialBox` and `capBox`; the radicals are bounded
-- by rational roots checked on their squares.
theorem upper_initial (r : Row) (hr : ARows r) : (4619/5000:ℝ)<F r true 0 := by
  have hn := (norm_positive r hr true (show (0:ℝ)∈Icc 0 (7/10) by norm_num)).le
  have hs := norm_initial r true
  have hR := radius_fine
  have ha := ShortOuterZero.fine_axial_bounds
  have hpi := pi_hand_enclosure
  have hF : F r true 0=Real.pi/2+c r+p r*outerAxial+(3/4+P r+t r)/2+3/4-CommonQuarter.radius*N r true 0 := by
    simp [F,ShortWord.MixedQuarter.angle,source,weight]
  rw [hF]
  rcases hr with rfl|rfl
  · norm_num [P,t,weight] at hs
    norm_num [c,p,P,t]
    have hN : N 0 true 0<1278391531/1000000000 :=
      lt_of_pow_lt_pow_left₀ 2 (by norm_num) (by rw [hs]; norm_num)
    have hRN := mul_le_mul hR.2.le hN.le hn (by norm_num)
    linarith
  · norm_num [P,t,weight] at hs
    norm_num [c,p,P,t]
    have hN : N 1 true 0<1269119199/1000000000 :=
      lt_of_pow_lt_pow_left₀ 2 (by norm_num) (by rw [hs]; norm_num)
    have hRN := mul_le_mul hR.2.le hN.le hn (by norm_num)
    linarith
theorem lower_initial (r : Row) (hr : ARows r) : (4587/5000:ℝ)<F r false 0 := by
  have hn := (norm_positive r hr false (show (0:ℝ)∈Icc 0 (7/10) by norm_num)).le
  have hs := norm_initial r false
  have hR := radius_fine
  have hpi := pi_hand_enclosure
  have hF : F r false 0=Real.pi/2+c r+source r false+(weight r false+P r+t r)/2+
      weight r false-CommonQuarter.radius*N r false 0 := by
    simp [F,ShortWord.MixedQuarter.angle]
  rw [hF]
  rcases hr with rfl|rfl
  · norm_num [P,t,q,weight] at hs
    norm_num [c,P,t,q,weight,source]
    have hN : N 0 false 0<1370599828/1000000000 :=
      lt_of_pow_lt_pow_left₀ 2 (by norm_num) (by rw [hs]; norm_num)
    have hRN := mul_le_mul hR.2.le hN.le hn (by norm_num)
    linarith
  · norm_num [P,t,q,weight] at hs
    have hsrc : source 1 false=-(p 1+q 1-weight 1 false)/2-
        CommonQuarter.radius*Real.sqrt (p 1^2+(q 1-weight 1 false)^2) := by
      simp [source]
    have hq : Real.sqrt (p 1^2+(q 1-weight 1 false)^2)<198072921/1000000000 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num [p,q,weight]
    have hq0 := Real.sqrt_nonneg (p 1^2+(q 1-weight 1 false)^2)
    rw [hsrc]
    generalize Real.sqrt (p 1^2+(q 1-weight 1 false)^2)=S at hq hq0 ⊢
    have hRq := mul_le_mul hR.2.le hq.le hq0 (by norm_num)
    norm_num [c,p,P,t,q,weight]
    have hN : N 1 false 0<1368474721/1000000000 :=
      lt_of_pow_lt_pow_left₀ 2 (by norm_num) (by rw [hs]; norm_num)
    have hRN := mul_le_mul hR.2.le hN.le hn (by norm_num)
    linarith
theorem lower_terminal (r : Row) (hr : ARows r) : (8981/10000:ℝ)<F r false (7/10) := by
  have hx : (7/10:ℝ)∈Icc 0 (7/10) := by norm_num
  have hn := (norm_positive r hr false hx).le
  have hs := norm_sq r hr false hx
  have hR := radius_fine
  have hpi := pi_hand_enclosure
  have tb := trig_taylor_bounds (show (0:ℝ)≤7/10 by norm_num)
  norm_num [sin7,sin9,cos8,cos10] at tb
  have hd : direction false=-1 := by simp [direction,ShortWord.MixedQuarter.direction]
  have hF : F r false (7/10)=Real.pi/2-7/10+c r+source r false+(weight r false+P r+t r)/2+
      weight r false*Real.cos (7/10)-CommonQuarter.radius*N r false (7/10) := by
    simp only [F,angle,ShortWord.MixedQuarter.angle,hd]; ring
  rw [hF]
  simp only [normA,normB,normC,hd] at hs
  rcases hr with rfl|rfl
  · norm_num [P,t,q,weight] at hs
    norm_num [c,P,t,q,weight,source]
    have hN : N 0 false (7/10)<9246267/10000000 :=
      lt_of_pow_lt_pow_left₀ 2 (by norm_num) (by rw [hs]; linarith [tb.1,tb.2.2.2])
    have hRN := mul_le_mul hR.2.le hN.le hn (by norm_num)
    linarith [tb.2.2.1]
  · norm_num [P,t,q,weight] at hs
    have hsrc : source 1 false=-(p 1+q 1-weight 1 false)/2-
        CommonQuarter.radius*Real.sqrt (p 1^2+(q 1-weight 1 false)^2) := by
      simp [source]
    have hq : Real.sqrt (p 1^2+(q 1-weight 1 false)^2)<198072921/1000000000 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num [p,q,weight]
    have hq0 := Real.sqrt_nonneg (p 1^2+(q 1-weight 1 false)^2)
    rw [hsrc]
    generalize Real.sqrt (p 1^2+(q 1-weight 1 false)^2)=S at hq hq0 ⊢
    have hRq := mul_le_mul hR.2.le hq.le hq0 (by norm_num)
    norm_num [c,p,P,t,q,weight]
    have hN : N 1 false (7/10)<9201443/10000000 :=
      lt_of_pow_lt_pow_left₀ 2 (by norm_num) (by rw [hs]; linarith [tb.1,tb.2.2.2])
    have hRN := mul_le_mul hR.2.le hN.le hn (by norm_num)
    linarith [tb.2.2.1]

end SquaresInCircles.Eight.TableFree.ShortOuterOne.EdgeFive.ASecondary.Endpoint
