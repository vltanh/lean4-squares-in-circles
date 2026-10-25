module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreeLowerGeometry

/-!
# The middle and terminal lower-contact derivative regimes

These are uniform analytic substitutions in the exact inverse
derivatives.  The terminal regime retains the physical contact
inequality throughout.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.LowerGeometry
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

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.LowerGeometry
