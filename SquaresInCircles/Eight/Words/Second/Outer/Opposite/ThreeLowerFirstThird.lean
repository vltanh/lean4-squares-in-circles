module

public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreeLowerGeometry

/-!
# Eight squares: decreasing outer curvature on every first lower-contact regime

The inverse phase is differentiated on the full physical radical
domain.  Its third derivative is bounded separately on the convex
rectangle, the single middle comparison curve, and the complete
terminal contact surface.
-/

section
/-!
## The middle and terminal lower-contact derivative regimes

These are uniform analytic substitutions in the exact inverse
derivatives.  The terminal regime retains the physical contact
inequality throughout.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree.LowerGeometry
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)
open StationaryPrimitives (Interval)
open ReferenceAlgebra LowerAlgebra LowerInverse

private lemma r62_mpr_hi {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).hi = S.hi := by subst e; rfl
private lemma r62_mpr_lo {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).lo = S.lo := by subst e; rfl
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

local macro "lower_bounds" : tactic => `(tactic|
  norm_num [ratioBox,ratioDBox,r62_ratioDDBox_lo,r62_ratioDDBox_hi,qBox,factorDBox,factorDDBox,
    A1Box,A3Box,Interval.point,Interval.of_bounds,Interval.add,Interval.sub,
    Interval.neg,Interval.mul,Interval.square,Interval.cube,Interval.inv,
    Interval.div,Q0])

lemma middle_data {y : ℝ} (hy : y∈Icc (2/5) (1/2)) :
    (51/100:ℝ)<ratio y ∧ ratio y<293/500 ∧
    0<ratioD y ∧ ratioD y≤Q0/(1707/1000)^3 ∧
    (31/50:ℝ)<ratioDD y ∧ ratioDD y<2 ∧
    (1737/1250:ℝ)<q (U y) ∧ q (U y)<1877/1250 ∧ 0≤factorD (U y) := by
  let Y : Interval y := Interval.of_bounds hy
  let U₀ : Interval (U y) := Interval.of_bounds ⟨(middle_U hy).1.le,(middle_U hy).2.le⟩
  have hU : 0<U₀.lo := by dsimp only [U₀]; lower_bounds
  let R := ratioBox Y U₀ hU
  let D := ratioDBox U₀ hU
  let DD := ratioDDBox Y U₀ hU
  let Q := qBox U₀
  have hQ : 0<Q.lo := by dsimp only [Q,U₀]; lower_bounds
  let F := factorDBox U₀ Q hU hQ
  have hr0 : (51/100:ℝ)<R.lo := by dsimp only [R,Y,U₀]; lower_bounds
  have hr1 : R.hi<(293/500:ℝ) := by dsimp only [R,Y,U₀]; lower_bounds
  have hd0 : 0<D.lo := by dsimp only [D,U₀]; lower_bounds
  have hd1 : D.hi≤Q0/(1707/1000)^3 := by dsimp only [D,U₀]; lower_bounds
  have hdd0 : (31/50:ℝ)<DD.lo := by dsimp only [DD,Y,U₀]; lower_bounds
  have hdd1 : DD.hi<(2:ℝ) := by dsimp only [DD,Y,U₀]; lower_bounds
  have hf : 0≤F.lo := by dsimp only [F,Q,U₀]; lower_bounds
  have hq0 : (1737/1250:ℝ)<q (U y) := by
    have hu := (middle_U hy).2
    norm_num [q,NegativeTwo.Inverse.q,Q0]
    linarith
  have hq1 : q (U y)<(1877/1250:ℝ) := by
    have hu := (middle_U hy).1
    norm_num [q,NegativeTwo.Inverse.q,Q0]
    linarith
  exact ⟨hr0.trans_le R.mem.1,R.mem.2.trans_lt hr1,
    hd0.trans_le D.mem.1,D.mem.2.trans hd1,hdd0.trans_le DD.mem.1,
    DD.mem.2.trans_lt hdd1,hq0,hq1,hf.trans F.mem.1⟩

lemma middle_third_terms {y : ℝ} (hy : y∈Icc (2/5) (1/2)) :
    X y<(359/500:ℝ) ∧ A1 y<23/20 ∧ A3 y<13/40 := by
  rcases middle_data hy with ⟨hr0,hr1,hd0,hd1,hdd0,hdd1,hq0,hq1,hf⟩
  let R : Interval (ratio y) := Interval.of_bounds ⟨hr0.le,hr1.le⟩
  let D : Interval (ratioD y) := Interval.of_bounds ⟨hd0.le,hd1⟩
  let DD : Interval (ratioDD y) := Interval.of_bounds ⟨hdd0.le,hdd1.le⟩
  let U₀ : Interval (U y) := Interval.of_bounds ⟨(middle_U hy).1.le,(middle_U hy).2.le⟩
  let Q : Interval (q (U y)) := Interval.of_bounds ⟨hq0.le,hq1.le⟩
  have hU : 0<U₀.lo := by dsimp only [U₀]; lower_bounds
  have hQ : 0<Q.lo := by dsimp only [Q]; lower_bounds
  let XX := R.square.mul (factorDDBox U₀ Q hU hQ)
  let AA := A1Box R D DD Q hQ
  let BB := A3Box R D Q hQ
  have hx : XX.hi<(359/500:ℝ) := by dsimp only [XX,R,U₀,Q]; lower_bounds
  have hA : AA.hi<(23/20:ℝ) := by dsimp only [AA,R,D,DD,Q]; lower_bounds
  have hB : BB.hi<(13/40:ℝ) := by dsimp only [BB,R,D,Q]; lower_bounds
  have hxle : X y≤(ratio y)^2*factorDD (U y) := by
    dsimp [X]
    nlinarith [mul_nonneg hd0.le hf]
  exact ⟨hxle.trans_lt (XX.mem.2.trans_lt hx),AA.mem.2.trans_lt hA,BB.mem.2.trans_lt hB⟩

lemma factorD_monotone : MonotoneOn factorD (Icc (3/2:ℝ) (383/200)) := by
  have hp {u : ℝ} (hu : u∈Icc (3/2:ℝ) (383/200)) : 0<u ∧ 0<q u := by
    constructor
    · linarith [hu.1]
    · norm_num [q,NegativeTwo.Inverse.q,Q0]
      linarith [hu.2]
  apply monoOn_of_hasDeriv_nonneg
  · intro u hu
    exact (factorD_hasDerivAt (hp hu).1.ne' (hp hu).2.ne').continuousAt.continuousWithinAt
  · intro u hu
    exact factorD_hasDerivAt (hp (Ioo_subset_Icc_self hu)).1.ne'
      (hp (Ioo_subset_Icc_self hu)).2.ne'
  · intro u hu
    exact (factorDD_positive (hp (Ioo_subset_Icc_self hu)).1
      (hp (Ioo_subset_Icc_self hu)).2).le

lemma late_data {b y : ℝ} (hd : LowerContact.Domain b y) (hy : 1/2≤y) :
    (117/200:ℝ)<ratio y ∧ ratio y<861/1000 ∧
    0<ratioD y ∧ ratioD y≤Q0/(3/2)^3 ∧
    (101/125:ℝ)<ratioDD y ∧ ratioDD y<3 ∧
    (3749/2500:ℝ)<q (U y) ∧ q (U y)≤4789/2500 ∧
    -(31/1000:ℝ)<factorD (U y) := by
  have hu := late_U hd hy
  have hc := Aligned.coordinates ⟨hd.2.1.1,(LowerContact.domain_bounds hd).2.1⟩
  have hw : W y<1291/1000 := hc.2.1
  have hyhi : y≤(791/1000:ℝ) := by dsimp [W] at hw; linarith
  let Y : Interval y := Interval.of_bounds ⟨hy,hyhi⟩
  let U₀ : Interval (U y) := Interval.of_bounds ⟨hu.1,hu.2.le⟩
  have hU : 0<U₀.lo := by dsimp only [U₀]; lower_bounds
  let R := ratioBox Y U₀ hU
  let D := ratioDBox U₀ hU
  let DD := ratioDDBox Y U₀ hU
  have hr0 : (117/200:ℝ)<R.lo := by dsimp only [R,Y,U₀]; lower_bounds
  have hd0 : 0<D.lo := by dsimp only [D,U₀]; lower_bounds
  have hd1 : D.hi≤Q0/(3/2)^3 := by dsimp only [D,U₀]; lower_bounds
  have hdd0 : (101/125:ℝ)<DD.lo := by dsimp only [DD,Y,U₀]; lower_bounds
  have hdd1 : DD.hi<(3:ℝ) := by dsimp only [DD,Y,U₀]; lower_bounds
  have hq0 : (3749/2500:ℝ)<q (U y) := by
    norm_num [q,NegativeTwo.Inverse.q,Q0]
    linarith [hu.2]
  have hq1 : q (U y)≤(4789/2500:ℝ) := by
    norm_num [q,NegativeTwo.Inverse.q,Q0]
    linarith [hu.1]
  have hf := factorD_monotone (by norm_num : (3/2:ℝ)∈Icc (3/2:ℝ) (383/200))
    ⟨hu.1,by linarith [hu.2]⟩ hu.1
  have hf0 : -(31/1000:ℝ)<factorD (3/2) := by
    norm_num [factorD,NegativeTwo.Inverse.factorD,NegativeTwo.Inverse.N,
      q,NegativeTwo.Inverse.q,Q0]
  exact ⟨hr0.trans_le R.mem.1,hc.2.2,hd0.trans_le D.mem.1,D.mem.2.trans hd1,
    hdd0.trans_le DD.mem.1,DD.mem.2.trans_lt hdd1,hq0,hq1,hf0.trans_le hf⟩

lemma late_third_terms {b y : ℝ} (hd : LowerContact.Domain b y) (hy : 1/2≤y) :
    X y<(143/100:ℝ) ∧ A1 y<63/20 ∧ A3 y<1049/1000 := by
  rcases late_data hd hy with ⟨hr0,hr1,hd0,hd1,hdd0,hdd1,hq0,hq1,hf⟩
  let R : Interval (ratio y) := Interval.of_bounds ⟨hr0.le,hr1.le⟩
  let D : Interval (ratioD y) := Interval.of_bounds ⟨hd0.le,hd1⟩
  let DD : Interval (ratioDD y) := Interval.of_bounds ⟨hdd0.le,hdd1.le⟩
  let U₀ : Interval (U y) := Interval.of_bounds ⟨(late_U hd hy).1,(late_U hd hy).2.le⟩
  let Q : Interval (q (U y)) := Interval.of_bounds ⟨hq0.le,hq1⟩
  have hU : 0<U₀.lo := by dsimp only [U₀]; lower_bounds
  have hQ : 0<Q.lo := by dsimp only [Q]; lower_bounds
  let XX := R.square.mul (factorDDBox U₀ Q hU hQ)
  let AA := A1Box R D DD Q hQ
  let BB := A3Box R D Q hQ
  have hx : XX.hi<(697/500:ℝ) := by dsimp only [XX,R,U₀,Q]; lower_bounds
  have hA : AA.hi<(63/20:ℝ) := by dsimp only [AA,R,D,DD,Q]; lower_bounds
  have hB : BB.hi<(1049/1000:ℝ) := by dsimp only [BB,R,D,Q]; lower_bounds
  have hdsmall : ratioD y<(1161/1000:ℝ) := by
    have hn : Q0/(3/2)^3<(1161/1000:ℝ) := by norm_num [Q0]
    exact hd1.trans_lt hn
  have hterm : -ratioD y*factorD (U y)<(9/250:ℝ) := by
    have hp := mul_lt_mul_of_pos_left hf hd0
    nlinarith
  have hxle : X y<(143/100:ℝ) := by
    have hp := XX.mem.2.trans_lt hx
    dsimp [X]
    linarith
  exact ⟨hxle,AA.mem.2.trans_lt hA,BB.mem.2.trans_lt hB⟩

end SquaresInCircles.Eight.SecondWord.OppositeThree.LowerGeometry
end
end
end

section
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
end
end
end
