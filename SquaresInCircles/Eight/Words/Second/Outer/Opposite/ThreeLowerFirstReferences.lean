module

public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreeLowerFirstThird

/-!
# Eight squares: named references for the first lower-secondary minimum

Every enclosure here concerns an endpoint of an analytic regime or
the single interior reference of the uniformly convex rectangle.
All quantities retain their actual radical expressions.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree.LowerFirst
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)
open LowerContact LowerGeometry LowerInverse
open StationaryPrimitives (Interval)
open ReferenceAlgebra LowerAlgebra

private lemma r62_mpr_hi {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).hi = S.hi := by subst e; rfl
private lemma r62_mpr_lo {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).lo = S.lo := by subst e; rfl
private lemma r62_shifted_eq {y : ℝ} : U y = Real.sqrt (Q0-(y+1/2)^2) := by dsimp [U,arc]; ring
private lemma r62_shifted_lo {y : ℝ} (Y : Interval y) (s : ℝ) (hs : 0<s)
    (hr : 0≤(radicand Y).lo) :
    (shifted Y s hs hr).lo = (rootThree (radicand Y) s hs hr).lo :=
  r62_mpr_lo r62_shifted_eq (congrArg _ r62_shifted_eq) _
private lemma r62_shifted_hi {y : ℝ} (Y : Interval y) (s : ℝ) (hs : 0<s)
    (hr : 0≤(radicand Y).lo) :
    (shifted Y s hs hr).hi = (rootThree (radicand Y) s hs hr).hi :=
  r62_mpr_hi r62_shifted_eq (congrArg _ r62_shifted_eq) _
private lemma r62_coordinate_eq {y : ℝ} : arc y = U y-1/2 := by dsimp [U]; ring
private lemma r62_coordinate_lo {y : ℝ} (Y : Interval (U y)) :
    (coordinate Y).lo = (Y.sub (Interval.point (1/2))).lo :=
  r62_mpr_lo r62_coordinate_eq (congrArg _ r62_coordinate_eq) _
private lemma r62_coordinate_hi {y : ℝ} (Y : Interval (U y)) :
    (coordinate Y).hi = (Y.sub (Interval.point (1/2))).hi :=
  r62_mpr_hi r62_coordinate_eq (congrArg _ r62_coordinate_eq) _

local macro "lower_reference" : tactic => `(tactic|
  norm_num [freeFirstBox,outerFirstBox,outerSecondBox,inverseFirstBox,inverseSecondBox,
    qBox,factorBox,factorDBox,speedBox,firstBox,secondBox,
    ratioBox,ratioDBox,r62_coordinate_lo,r62_coordinate_hi,r62_shifted_lo,r62_shifted_hi,
    radicand,rootThree,rootStep,
    LowerContact.inner,LowerContact.outer,TLabel,LLabel,Q0,
    Interval.point,Interval.of_bounds,Interval.add,Interval.sub,Interval.neg,
    Interval.mul,Interval.square,Interval.cube,Interval.inv,Interval.div])

def fourU : Interval (U (2/5)) :=
  shifted (Interval.point (2/5)) (9/5) (by norm_num) (by lower_reference)
def halfU : Interval (U (1/2)) :=
  shifted (Interval.point (1/2)) (17/10) (by norm_num) (by lower_reference)
def smallU : Interval (U (1/10)) :=
  shifted (Interval.point (1/10)) (19/10) (by norm_num) (by lower_reference)
def middleU : Interval (U (21/200)) :=
  shifted (Interval.point (21/200)) (19/10) (by norm_num) (by lower_reference)

lemma four_coefficients :
    (16787/50000:ℝ)< -ratio (2/5)*factorD (U (2/5))-LLabel.d2 (2/5) ∧
    (6739/50000:ℝ)<(ratio (2/5))^2/(q (U (2/5)))^2 ∧
    -(10997/100000:ℝ)<3*(ratio (2/5))^2/(q (U (2/5)))^2-ratioD (2/5)/q (U (2/5)) := by
  have hu : 0<fourU.lo := by dsimp [fourU]; lower_reference
  let Q := qBox fourU
  have hq : 0<Q.lo := by dsimp [Q,fourU]; lower_reference
  let R := ratioBox (Interval.point (2/5)) fourU hu
  let D := ratioDBox fourU hu
  let C₀ := ((R.mul (factorDBox fourU Q hu hq)).neg).sub
    (secondBox LLabel (Interval.point (2/5)) fourU hu)
  let C₃ := R.square.div Q.square (Interval.square_lo_pos hq)
  let C₁ := ((Interval.point 3).mul C₃).sub (D.div Q hq)
  have h0 : (16787/50000:ℝ)<C₀.lo := by dsimp [C₀,R,Q,fourU]; lower_reference
  have h3 : (6739/50000:ℝ)<C₃.lo := by dsimp [C₃,R,Q,fourU]; lower_reference
  have h1 : -(10997/100000:ℝ)<C₁.lo := by dsimp [C₁,C₃,R,D,Q,fourU]; lower_reference
  exact ⟨by rw [neg_mul]; exact h0.trans_le C₀.mem.1,h3.trans_le C₃.mem.1,
    by rw [mul_div_assoc]; exact h1.trans_le C₁.mem.1⟩

lemma four_quotient {b : ℝ} (hb : b∈Icc 0 (1/10)) :
    (117/250:ℝ)<quotient (b+1/2) (2/5) ∧ quotient (b+1/2) (2/5)<591/1000 := by
  have hb' : b∈Icc 0 (83/200) := ⟨hb.1,by linarith [hb.2]⟩
  have hB := full_domain (by norm_num : (2/5:ℝ)∈Icc 0 (4/5))
  have hv := (OppositeTwo.PrimaryInverse.data hB (short_shift hb')).2.2.1
  let Q := qBox fourU
  have hqlo : (1391057/1000000:ℝ)<Q.lo := by dsimp [Q,fourU]; lower_reference
  have hqhi : Q.hi<(695529/500000:ℝ) := by dsimp [Q,fourU]; lower_reference
  have hq0 := hqlo.trans_le Q.mem.1
  have hq1 := Q.mem.2.trans_lt hqhi
  have hcircle := (OppositeTwo.PrimaryInverse.data hB (short_shift hb')).2.2.2
  have hzlo : (1/2:ℝ)≤b+1/2 := by linarith [hb.1]
  have hzhi : b+1/2≤(3/5:ℝ) := by linarith [hb.2]
  have hzslo := mul_self_le_mul_self (by norm_num : (0:ℝ)≤1/2) hzlo
  have hzshi := mul_self_le_mul_self (by linarith : 0≤b+1/2) hzhi
  constructor
  · apply (lt_div_iff₀ hv).2
    by_contra hn
    have hp := mul_self_le_mul_self (by linarith : 0≤b+1/2) (le_of_not_gt hn)
    nlinarith
  · exact (quotient_bound hB (short_shift hb') (by norm_num) (by nlinarith)).2

lemma four_curvature {b : ℝ} (hb : b∈Icc 0 (1/10)) :
    (7/25:ℝ)<outerSecond false b (2/5) := by
  have hb' : b∈Icc 0 (83/200) := ⟨hb.1,by linarith [hb.2]⟩
  have hB := full_domain (by norm_num : (2/5:ℝ)∈Icc 0 (4/5))
  have he := second_cubic hB (short_shift hb')
  rcases four_coefficients with ⟨h0,h3,h1⟩
  have ht := four_quotient hb
  have ht0 : 0≤quotient (b+1/2) (2/5) := by linarith [ht.1]
  have ht3 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤117/250) ht.1.le 3
  have hmul3 := mul_lt_mul_of_pos_right h3 (pow_pos (by linarith : 0<quotient (b+1/2) (2/5)) 3)
  have hmul1 := mul_lt_mul_of_pos_right h1 (by linarith : 0<quotient (b+1/2) (2/5))
  dsimp [outerSecond,outer]
  rw [he]
  nlinarith

lemma half_endpoints :
    outerSecond false 0 (1/2)< -(1339/10000:ℝ) ∧
      outerSecond false (arc (1/2)-1) (1/2)< -(111/1000:ℝ) := by
  have hu : 0<halfU.lo := by dsimp [halfU]; lower_reference
  have hq : 0<(qBox halfU).lo := by dsimp [halfU]; lower_reference
  let V₀ := speedBox (Interval.point ((0:ℝ)+1/2)) (qBox halfU) (11/10) (by norm_num)
    (by dsimp [halfU]; lower_reference)
  have hv₀ : 0<V₀.lo := by dsimp [V₀,halfU]; lower_reference
  let C₀ := outerSecondBox false (Interval.point ((0:ℝ)+1/2)) (Interval.point (1/2)) halfU V₀ hu hq hv₀
  have hh₀ : C₀.hi< -(1339/10000:ℝ) := by dsimp [C₀,V₀,halfU]; lower_reference
  have hz : arc (1/2)-1+1/2=U (1/2)-1 := by dsimp [U]; ring
  let Z₁ : Interval (arc (1/2)-1+1/2) :=
    ⟨(halfU.sub (Interval.point 1)).lo,(halfU.sub (Interval.point 1)).hi,
      by rw [hz]; exact (halfU.sub (Interval.point 1)).mem⟩
  have hv : speed (arc (1/2)-1+1/2) (1/2)=1 := by
    have hcircle := UW_circle (outer_domain (full_domain (by norm_num : (1/2:ℝ)∈Icc 0 (4/5))))
    have he : q (U (1/2))-(arc (1/2)-1+1/2)^2=(1:ℝ) := by
      rw [hz]
      norm_num [W,q,NegativeTwo.Inverse.q] at hcircle ⊢
      nlinarith
    change Real.sqrt (q (U (1/2))-(arc (1/2)-1+1/2)^2)=1
    rw [he]
    norm_num
  let V₁ : Interval (speed (arc (1/2)-1+1/2) (1/2)) :=
    ⟨1,1,by rw [hv]; exact (Interval.point (1:ℝ)).mem⟩
  let C₁ := outerSecondBox false Z₁ (Interval.point (1/2)) halfU V₁ hu hq (by dsimp [V₁]; norm_num [Interval.point])
  have hh₁ : C₁.hi< -(111/1000:ℝ) := by dsimp [C₁,V₁,Z₁,halfU]; lower_reference
  exact ⟨C₀.mem.2.trans_lt hh₀,C₁.mem.2.trans_lt hh₁⟩

lemma middle_first_endpoints :
    (61/10000:ℝ)<outerFirst false (21/200) (2/5) ∧
      (19/1250:ℝ)<outerFirst false (21/200) (1/2) := by
  have hu₀ : 0<fourU.lo := by dsimp [fourU]; lower_reference
  have hq₀ : 0<(qBox fourU).lo := by dsimp [fourU]; lower_reference
  have hu₁ : 0<halfU.lo := by dsimp [halfU]; lower_reference
  have hq₁ : 0<(qBox halfU).lo := by dsimp [halfU]; lower_reference
  let V₀ := speedBox (Interval.point ((21/200:ℝ)+1/2)) (qBox fourU) 1 (by norm_num)
    (by dsimp [fourU]; lower_reference)
  let V₁ := speedBox (Interval.point ((21/200:ℝ)+1/2)) (qBox halfU) 1 (by norm_num)
    (by dsimp [halfU]; lower_reference)
  have hv₀ : 0<V₀.lo := by dsimp [V₀,fourU]; lower_reference
  have hv₁ : 0<V₁.lo := by dsimp [V₁,halfU]; lower_reference
  let C₀ := outerFirstBox false (Interval.point ((21/200:ℝ)+1/2)) (Interval.point (2/5)) fourU V₀ hu₀ hq₀ hv₀
  let C₁ := outerFirstBox false (Interval.point ((21/200:ℝ)+1/2)) (Interval.point (1/2)) halfU V₁ hu₁ hq₁ hv₁
  have hh₀ : (61/10000:ℝ)<C₀.lo := by dsimp [C₀,V₀,fourU]; lower_reference
  have hh₁ : (19/1250:ℝ)<C₁.lo := by dsimp [C₁,V₁,halfU]; lower_reference
  exact ⟨hh₀.trans_le C₀.mem.1,hh₁.trans_le C₁.mem.1⟩

lemma free_first_references :
    0<freeFirst false (1/10) (2/5) ∧
      freeFirst false 0 (2/5)<0 ∧
      (7/5000:ℝ)<freeFirst false (21/200) (1/2) := by
  have hu₀ : 0<smallU.lo := by dsimp [smallU]; lower_reference
  have hu₁ : 0<Aligned.zeroU.lo := by dsimp [Aligned.zeroU]; lower_reference
  have hu₂ : 0 < middleU.lo := by dsimp [middleU]; lower_reference
  let V₀ := speedBox (Interval.point ((1/10:ℝ)+1/2)) (qBox fourU) 1 (by norm_num)
    (by dsimp [fourU]; lower_reference)
  let V₁ := speedBox (Interval.point ((0:ℝ)+1/2)) (qBox fourU) 1 (by norm_num)
    (by dsimp [fourU]; lower_reference)
  let V₂ := speedBox (Interval.point ((21/200:ℝ)+1/2)) (qBox halfU) 1 (by norm_num)
    (by dsimp [halfU]; lower_reference)
  have hv₀ : 0<V₀.lo := by dsimp [V₀,fourU]; lower_reference
  have hv₁ : 0<V₁.lo := by dsimp [V₁,fourU]; lower_reference
  have hv₂ : 0<V₂.lo := by dsimp [V₂,halfU]; lower_reference
  let C₀ := freeFirstBox false (Interval.point (1/10)) smallU V₀ hu₀ hv₀
  let C₁ := freeFirstBox false (Interval.point 0) Aligned.zeroU V₁ hu₁ hv₁
  let C₂ := freeFirstBox false (Interval.point (21/200)) middleU V₂ hu₂ hv₂
  have hh₀ : 0<C₀.lo := by dsimp [C₀,V₀,smallU,fourU]; lower_reference
  have hh₁ : C₁.hi<0 := by dsimp [C₁,V₁,Aligned.zeroU,fourU]; lower_reference
  have hh₂ : (7/5000:ℝ)<C₂.lo := by dsimp [C₂,V₂,middleU,halfU]; lower_reference
  exact ⟨hh₀.trans_le C₀.mem.1,C₁.mem.2.trans_lt hh₁,hh₂.trans_le C₂.mem.1⟩

end SquaresInCircles.Eight.SecondWord.OppositeThree.LowerFirst
