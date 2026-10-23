module

public import SquaresInCircles.Eight.TableFree.ShortMixedQuarterReferences

/-!
# Every negative outer target on a mixed source-secondary quarter edge

Uncompiled transcription of Section 3.1 of the parent hand proof.
The multiplier is exactly the original core coefficient. Its remainder
vanishes, and the target support is axial. The three fixed coefficient
ranges supply derivative reserves on an entire half, never angle cells.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortWord.MixedQuarter.CoreSecondaryNegative
open CommonQuarter CorePairGeometry Arithmetic StationaryPrimitives Reference

def F (r : Row) (upper : Bool) (x : ℝ) : ℝ :=
  angle upper x+coC r-coP r*outerAxial+coG r/2+
    coG r/2*Real.sin x-coG r*(outerAxial-1/2)*Real.cos x
def Fd (r : Row) (upper : Bool) (x : ℝ) : ℝ :=
  direction upper+coG r/2*Real.cos x+coG r*(outerAxial-1/2)*Real.sin x
def loss (r : Row) : ℝ := if coG r≤477/500 then 0 else if coG r≤1 then 43/1000 else 19/100
def endpointFloor (r : Row) : ℝ :=
  if coG r≤477/500 then 921/1000 else if coG r≤1 then 47/50 else 519/500

theorem F_hasDerivAt (r : Row) (upper : Bool) (x : ℝ) :
    HasDerivAt (F r upper) (Fd r upper x) x := by
  convert (((((hasDerivAt_id x).const_mul (direction upper)).const_add
    (Real.pi/2+coC r-coP r*outerAxial+coG r/2)).add
      ((Real.hasDerivAt_sin x).const_mul (coG r/2))).sub
        ((Real.hasDerivAt_cos x).const_mul (coG r*(outerAxial-1/2)))) using 1 <;>
    dsimp [F,Fd,angle] <;> ring

theorem original_lower (r : Row) (hr : targetPositive r=false) (upper : Bool)
    {a b A B x : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10)) (hm : sourceSecondary r a b A B (angle upper x)) :
    F r upper x≤coreOuterCost r a b A B (angle upper x) := by
  have hb := coefficient_bounds r
  have htr := positive_trig hx
  have hsin : 0<coP r+coG r*Real.cos x := by
    have hp := mul_lt_mul_of_pos_left htr.1 hb.1
    linarith [hb.2.2.2.2.2.2.2.2.2.1]
  have hy : 0≤coQ r+direction upper*coG r*Real.sin x := by
    have hp := mul_lt_mul_of_pos_left htr.2.2.2.1 hb.1
    cases upper <;> dsimp [direction] <;> nlinarith [hb.2.2.2.2.2.2.2.2.1]
  have hsup := MixedQuarter.outer_axial_lower ht (show -(coP r+coG r*Real.cos x)≤0 by linarith) hy
  dsimp [sourceSecondary] at hm
  have hmult := mul_le_mul_of_nonneg_left hm hb.1.le
  rw [angle_width upper hx,angle_sin,angle_cos,targetSign_negative hr] at hmult
  dsimp [F,coreOuterCost]
  rw [targetSign_negative hr]
  nlinarith

theorem derivative_lower_half (r : Row) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    Fd r false x≤loss r := by
  have hg := (coefficient_bounds r).1
  have hgu := (coefficient_bounds r).2.1
  have hA := outer_endpoint_bounds
  have htr := positive_trig hx
  let v := Real.cos x/2+(outerAxial-1/2)*Real.sin x
  have hv : 0≤v := by
    exact add_nonneg (div_nonneg (by linarith [htr.1]) (by norm_num))
      (mul_nonneg (by linarith [hA.1]) htr.2.2.1)
  have hs : v^2≤1/4+(outerAxial-1/2)^2 := by
    have hid : v^2+(Real.sin x/2-(outerAxial-1/2)*Real.cos x)^2=
        1/4+(outerAxial-1/2)^2 := by
      dsimp [v]
      linear_combination (1/4+(outerAxial-1/2)^2)*(Real.sin_sq_add_cos_sq x)
    nlinarith [sq_nonneg (Real.sin x/2-(outerAxial-1/2)*Real.cos x)]
  have hvs : v^2<(43489/40000:ℝ) := by nlinarith [hA.1,hA.2.1]
  have hvu : v<(1043/1000:ℝ) := by nlinarith
  have hgv : 0≤coG r*v := mul_nonneg hg.le hv
  by_cases hsmall : coG r≤477/500
  · have hgs : coG r^2≤(477/500:ℝ)^2 := pow_le_pow_left₀ hg.le hsmall 2
    have hp := mul_lt_mul_of_pos_right hvs (sq_pos_of_pos hg)
    have hq := mul_le_mul_of_nonneg_right hgs (by norm_num : (0:ℝ)≤43489/40000)
    have hbound : coG r*v<1 := by nlinarith
    dsimp [Fd,direction,loss]
    rw [if_pos hsmall]
    dsimp [v] at hbound
    linarith
  · by_cases hmid : coG r≤1
    · have hp := mul_le_mul_of_nonneg_right hmid hv
      dsimp [Fd,direction,loss]
      rw [if_neg hsmall,if_pos hmid]
      dsimp [v] at hp hvu
      linarith
    · have hp := mul_lt_mul_of_pos_left hvu hg
      have hq : (1043/1000:ℝ)*coG r<(1043/1000)*(1139/1000) := by nlinarith
      dsimp [Fd,direction,loss]
      rw [if_neg hsmall,if_neg hmid]
      dsimp [v] at hp
      nlinarith

def endpointBox (r : Row) : Interval (F r false (7/10)) := by
  let s := sine (by norm_num : (0:ℝ)≤7/10)
  let k := cosine (by norm_num : (0:ℝ)≤7/10)
  convert ((((((halfPi.sub (Interval.point (7/10))).add (Interval.point (coC r))).sub
    ((Interval.point (coP r)).mul axial)).add (Interval.point (coG r/2))).add
      ((Interval.point (coG r/2)).mul s)).sub
        (((Interval.point (coG r)).mul (axial.sub (Interval.point (1/2)))).mul k)
    using 1 <;> dsimp [F,angle,direction] <;> ring

theorem endpoint (r : Row) (hr : targetPositive r=false) : endpointFloor r<F r false (7/10) := by
  have hlo : endpointFloor r<(endpointBox r).lo := by
    fin_cases r <;> norm_num [targetPositive] at hr <;>
      dsimp [endpointBox,endpointFloor] <;> mixed_fixed
  exact hlo.trans_le (endpointBox r).mem.1

theorem floor_reserve (r : Row) : (449/500:ℝ)<endpointFloor r-loss r*(7/10) ∧ 0≤loss r := by
  fin_cases r <;> norm_num [endpointFloor,loss,coG]

theorem lower_half (r : Row) (hr : targetPositive r=false) {x : ℝ}
    (hx : x∈Icc 0 (7/10)) : (449/500:ℝ)<F r false x := by
  have h := derivative_reserve (f:=fun z => -F r false z) (df:=fun z => -Fd r false z)
    (k:= -loss r) (fun z _ => (F_hasDerivAt r false z).neg.continuousAt.continuousWithinAt)
    (fun z _ => (F_hasDerivAt r false z).neg)
    (fun z hz => by linarith [derivative_lower_half r (Ioo_subset_Icc_self hz)])
    hx (show (7/10:ℝ)∈Icc 0 (7/10) by norm_num) hx.2
  have hL := mul_nonneg (floor_reserve r).2 hx.1
  linarith [endpoint r hr,(floor_reserve r).1]

theorem upper_increases (r : Row) : MonotoneOn (F r true) (Icc 0 (7/10)) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun x _ => (F_hasDerivAt r true x).continuousAt.continuousWithinAt)
    (fun x _ => F_hasDerivAt r true x)
  intro x hx
  have ht := positive_trig (Ioo_subset_Icc_self hx)
  have hg := (coefficient_bounds r).1
  have hA : 0≤outerAxial-1/2 := by linarith [outer_endpoint_bounds.1]
  dsimp [Fd,direction]
  have h1 := mul_nonneg hg.le (show 0≤Real.cos x by linarith [ht.1])
  have h2 := mul_nonneg (mul_nonneg hg.le hA) ht.2.2.1
  nlinarith

theorem all_angles (r : Row) (hr : targetPositive r=false) (upper : Bool) {x : ℝ}
    (hx : x∈Icc 0 (7/10)) : (449/500:ℝ)<F r upper x := by
  cases upper
  · exact lower_half r hr hx
  · have h0 := lower_half r hr (show (0:ℝ)∈Icc 0 (7/10) by norm_num)
    have hm := upper_increases r (show (0:ℝ)∈Icc 0 (7/10) by norm_num) hx hx.1
    have he : F r true 0=F r false 0 := by simp [F,angle]
    linarith

theorem original (r : Row) (hr : targetPositive r=false) (upper : Bool)
    {a b A B x : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10)) (hm : sourceSecondary r a b A B (angle upper x)) :
    (449/500:ℝ)<coreOuterCost r a b A B (angle upper x) :=
  (all_angles r hr upper hx).trans_le (original_lower r hr upper hs ht hx hm)

end SquaresInCircles.Eight.TableFree.ShortWord.MixedQuarter.CoreSecondaryNegative
