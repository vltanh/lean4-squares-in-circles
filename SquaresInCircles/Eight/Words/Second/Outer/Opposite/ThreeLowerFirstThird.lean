module

public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreeLowerLateGeometry

/-!
# Eight squares: decreasing outer curvature on every first lower-contact regime

The inverse phase is differentiated on the full physical radical
domain.  Its third derivative is bounded separately on the convex
rectangle, the single middle comparison curve, and the complete
terminal contact surface.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree.LowerFirst
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)
open LowerContact LowerGeometry LowerInverse
open StationaryPrimitives (Interval)
open ReferenceAlgebra

lemma short_domain {b : ℝ} (hb : b∈Icc 0 (83/200)) : b∈Icc 0 outerDiagonal :=
  ⟨hb.1,by linarith [hb.2,fine_outer_endpoint_bounds.2]⟩

lemma short_shift {b : ℝ} (hb : b∈Icc 0 (83/200)) : b+1/2∈shifts := by
  constructor <;> linarith [hb.1,hb.2]

lemma quotient_bound {z y t : ℝ} (hy : y∈Icc 0 outerDiagonal) (hz : z∈shifts)
    (ht : 0<t) (hquad : z^2<t^2*(speed z y)^2) : 0≤quotient z y ∧ quotient z y<t := by
  have hv := (OppositeTwo.PrimaryInverse.data hy hz).2.2.1
  refine ⟨div_nonneg hz.1 hv.le,?_⟩
  apply (div_lt_iff₀ hv).2
  by_contra hn
  have hh := mul_self_le_mul_self (mul_pos ht hv).le (le_of_not_gt hn)
  nlinarith

lemma early_quotient {b B : ℝ} (hb : b∈Icc 0 (1/10)) (hB : B∈Icc 0 (2/5)) :
    0≤quotient (b+1/2) B ∧ quotient (b+1/2) B<141/200 := by
  have hbf : b∈Icc 0 (83/200) := ⟨hb.1,by linarith [hb.2]⟩
  have hBf := full_domain ⟨hB.1,by linarith [hB.2]⟩
  have hh := OppositeTwo.PrimaryInverse.data hBf (short_shift hbf)
  apply quotient_bound hBf (short_shift hbf) (by norm_num)
  have hz2 : (b+1/2)^2≤(3/5:ℝ)^2 := by nlinarith [hb.1,hb.2]
  have hq := (early_data hB).2.2.2.2.2.1
  nlinarith [hh.2.2.2]

lemma early_third_negative {b B : ℝ} (hb : b∈Icc 0 (1/10)) (hB : B∈Icc 0 (2/5)) :
    outerThird false b B<0 := by
  rcases early_third_terms hB with ⟨hX,hA,hC⟩
  have ht := early_quotient hb hB
  have hd := early_data hB
  have hthird := third_upper hX.le hA.le hC.le (by linarith [hd.1])
    (by linarith [hd.2.2.2.2.2.1]) ht.1 ht.2.le (by norm_num) (by norm_num)
  have hl := Aligned.L_third_lower (full_domain ⟨hB.1,by linarith [hB.2]⟩)
  norm_num at hthird
  dsimp [outerThird,outer]
  linarith

lemma middle_quotient {B : ℝ} (hB : B∈Icc (2/5) (1/2)) :
    0≤quotient (121/200) B ∧ quotient (121/200) B<599/1000 := by
  have hBf := full_domain ⟨by linarith [hB.1],by linarith [hB.2]⟩
  have hz : (121/200:ℝ)∈shifts := by norm_num [shifts,OppositeTwo.PrimaryInverse.shifts]
  have hh := OppositeTwo.PrimaryInverse.data hBf hz
  apply quotient_bound hBf hz (by norm_num)
  have hq := (middle_data hB).2.2.2.2.2.2.1
  nlinarith [hh.2.2.2]

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
private lemma r62_ratioDD_eq {y : ℝ} : ratioDD y = 3*Q0*(y+1/2)/((U y)^3*(U y)^2) := by
  dsimp [ratioDD,U]; ring
private lemma r62_ratioDDBox_lo {y : ℝ} (Y : Interval y) (X : Interval (U y)) (hX : 0<X.lo) :
    (ratioDDBox Y X hX).lo = (((Interval.point (3*Q0)).mul (Y.add (Interval.point (1/2)))).div
      (X.cube.mul X.square)
      (Interval.mul_lo_pos (Interval.cube_lo_pos hX) (Interval.square_lo_pos hX))).lo :=
  r62_mpr_lo r62_ratioDD_eq (congrArg _ r62_ratioDD_eq) _
private lemma r62_ratioDDBox_hi {y : ℝ} (Y : Interval y) (X : Interval (U y)) (hX : 0<X.lo) :
    (ratioDDBox Y X hX).hi = (((Interval.point (3*Q0)).mul (Y.add (Interval.point (1/2)))).div
      (X.cube.mul X.square)
      (Interval.mul_lo_pos (Interval.cube_lo_pos hX) (Interval.square_lo_pos hX))).hi :=
  r62_mpr_hi r62_ratioDD_eq (congrArg _ r62_ratioDD_eq) _

lemma two_fifths_L_third : (9/2:ℝ)<LLabel.d3 (2/5) := by
  let X₀ := shifted (Interval.point (2/5)) (9/5) (by norm_num)
    (by norm_num [radicand,Interval.point,Interval.sub,Interval.add,Interval.square,
      Interval.mul,Q0])
  have hX : 0<X₀.lo := by
    norm_num [X₀,r62_shifted_lo,rootThree,rootStep,radicand,Interval.point,Interval.sub,
      Interval.add,Interval.square,Interval.mul,Q0]
  let Z := thirdBox LLabel (Interval.point (2/5)) X₀ hX
  have hh : (9/2:ℝ)<Z.lo := by
    norm_num [Z,X₀,thirdBox,ratioDBox,r62_ratioDDBox_lo,r62_ratioDDBox_hi,r62_shifted_lo,r62_shifted_hi,
      rootThree,rootStep,
      radicand,Interval.point,Interval.sub,Interval.add,Interval.square,Interval.cube,
      Interval.mul,Interval.div,Interval.inv,LLabel,Q0]
  exact hh.trans_le Z.mem.1

lemma middle_third_negative {B : ℝ} (hB : B∈Icc (2/5) (1/2)) :
    outerThird false (21/200) B<0 := by
  rcases middle_third_terms hB with ⟨hX,hA,hC⟩
  have ht := middle_quotient hB
  have hd := middle_data hB
  have hthird := third_upper hX.le hA.le hC.le (by linarith [hd.1])
    (by linarith [hd.2.2.2.2.2.2.1]) ht.1 ht.2.le (by norm_num) (by norm_num)
  have hBf : B∈Icc 0 outerDiagonal := full_domain ⟨by linarith [hB.1],by linarith [hB.2]⟩
  have hl := L_third_monotone (full_domain (by norm_num : (2/5:ℝ)∈Icc 0 (4/5))) hBf hB.1
  have he : (21/200:ℝ)+1/2=121/200 := by norm_num
  dsimp [outerThird,outer]
  rw [he]
  norm_num at hthird
  linarith [two_fifths_L_third]

lemma late_quotient {b B : ℝ} (hd : Domain b B) (hB : 1/2≤B) :
    0≤quotient (b+1/2) B ∧ quotient (b+1/2) B<709/1000 := by
  have hv := physical_speed hd
  have hw : 1≤W B := by dsimp [W]; linarith
  have hz0 : 0≤b+1/2 := by linarith [hd.1.1]
  have hz1 : b+1/2<(177/250:ℝ) := by
    have hu := (late_U hd hB).2
    dsimp [U] at hu
    linarith [hd.2.2]
  have hp := (OppositeTwo.PrimaryInverse.data hd.2.1 (domain_bounds hd).2.2).2.2.1
  refine ⟨div_nonneg hz0 hp.le,?_⟩
  apply (div_lt_iff₀ hp).2
  linarith

lemma late_third_negative {b B : ℝ} (hd : Domain b B) (hB : 1/2≤B) :
    outerThird false b B<0 := by
  rcases late_third_terms hd hB with ⟨hX,hA,hC⟩
  have ht := late_quotient hd hB
  have hdata := late_data hd hB
  have hthird := third_upper hX.le hA.le hC.le (by linarith [hdata.1])
    (by linarith [hdata.2.2.2.2.2.2.1]) ht.1 ht.2.le (by norm_num) (by norm_num)
  have hl := L_third_monotone (full_domain (by norm_num : (2/5:ℝ)∈Icc 0 (4/5)))
    hd.2.1 (by linarith)
  dsimp [outerThird,outer]
  norm_num at hthird
  linarith [two_fifths_L_third]

end SquaresInCircles.Eight.SecondWord.OppositeThree.LowerFirst
