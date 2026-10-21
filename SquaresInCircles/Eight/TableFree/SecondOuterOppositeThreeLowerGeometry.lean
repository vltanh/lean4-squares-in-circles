module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreeLowerAlgebra

/-!
# Bounds on the three complete lower-contact regimes

The intervals in this file are the three analytic regimes of the
minimum proof.  Every bound is transported from the actual shifted
circle; none is a cell of a coordinate cover.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.LowerGeometry
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)
open StationaryPrimitives (Interval)
open ReferenceAlgebra LowerAlgebra LowerInverse

lemma full_domain {y : ℝ} (hy : y∈Icc 0 (4/5)) : y∈Icc 0 outerDiagonal :=
  ⟨hy.1,by linarith [hy.2,fine_outer_endpoint_bounds.2]⟩

lemma shifted_range {y l h u v : ℝ} (hy : y∈Icc 0 outerDiagonal)
    (hyl : l≤y) (hyh : y≤h) (hl : 0≤l+1/2) (hu : 0≤u) (hv : 0<v)
    (hlo : u^2+(h+1/2)^2<Q0) (hhi : Q0<v^2+(l+1/2)^2) :
    u<U y ∧ U y<v := by
  have hc := UW_circle (outer_domain hy)
  have hp := U_positive (outer_domain hy)
  have hwlo : l+1/2≤W y := by dsimp [W]; linarith
  have hwhi : W y≤h+1/2 := by dsimp [W]; linarith
  have hwslo := mul_self_le_mul_self hl hwlo
  have hwshi := mul_self_le_mul_self (hl.trans hwlo) hwhi
  constructor <;> nlinarith

lemma early_U {y : ℝ} (hy : y∈Icc 0 (2/5)) :
    (881/500:ℝ)<U y ∧ U y<383/200 :=
  shifted_range (full_domain ⟨hy.1,by linarith [hy.2]⟩) hy.1 hy.2
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Q0]) (by norm_num [Q0])

lemma middle_U {y : ℝ} (hy : y∈Icc (2/5) (1/2)) :
    (1707/1000:ℝ)<U y ∧ U y<1763/1000 :=
  shifted_range (full_domain ⟨by linarith [hy.1],by linarith [hy.2]⟩) hy.1 hy.2
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Q0]) (by norm_num [Q0])

lemma late_U {b y : ℝ} (hd : LowerContact.Domain b y) (hy : 1/2≤y) :
    (3/2:ℝ)≤U y ∧ U y<427/250 := by
  have hlo : (3/2:ℝ)≤U y := by dsimp [U]; linarith [hd.1.1,hd.2.2]
  have hc := UW_circle (outer_domain hd.2.1)
  have hw : 1≤W y := by dsimp [W]; linarith
  norm_num [Q0] at hc
  exact ⟨hlo,by nlinarith [mul_self_le_mul_self (by norm_num : (0:ℝ)≤1) hw]⟩

local macro "lower_bounds" : tactic => `(tactic|
  norm_num [ratioBox,ratioDBox,ratioDDBox,qBox,factorDBox,factorDDBox,
    A1Box,A3Box,Interval.point,Interval.of_bounds,Interval.add,Interval.sub,
    Interval.neg,Interval.mul,Interval.square,Interval.cube,Interval.inv,
    Interval.div,Q0])

lemma early_data {y : ℝ} (hy : y∈Icc 0 (2/5)) :
    (261/1000:ℝ)<ratio y ∧ ratio y<511/1000 ∧
    (557/1000:ℝ)<ratioD y ∧ ratioD y<179/250 ∧
    (57/250:ℝ)<ratioDD y ∧ (1357/1250:ℝ)<q (U y) ∧
      q (U y)<3479/2500 ∧ 0≤factorD (U y) := by
  let Y : Interval y := Interval.of_bounds hy
  let X : Interval (U y) := Interval.of_bounds ⟨(early_U hy).1.le,(early_U hy).2.le⟩
  have hX : 0<X.lo := by lower_bounds
  let R := ratioBox Y X hX
  let D := ratioDBox X hX
  let DD := ratioDDBox Y X hX
  let Q := qBox X
  have hQ : 0<Q.lo := by lower_bounds
  let F := factorDBox X Q hX hQ
  have hr0 : (261/1000:ℝ)<R.lo := by lower_bounds
  have hr1 : R.hi<(511/1000:ℝ) := by lower_bounds
  have hd0 : (557/1000:ℝ)<D.lo := by lower_bounds
  have hd1 : D.hi<(179/250:ℝ) := by lower_bounds
  have hdd : (57/250:ℝ)<DD.lo := by lower_bounds
  have hf : 0≤F.lo := by lower_bounds
  have hq0 : (1357/1250:ℝ)<q (U y) := by
    have hu := (early_U hy).2
    norm_num [q,NegativeTwo.Inverse.q,Q0]
    linarith
  have hq1 : q (U y)<(3479/2500:ℝ) := by
    have hu := (early_U hy).1
    norm_num [q,NegativeTwo.Inverse.q,Q0]
    linarith
  exact ⟨hr0.trans_le R.mem.1,R.mem.2.trans_lt hr1,
    hd0.trans_le D.mem.1,D.mem.2.trans_lt hd1,hdd.trans_le DD.mem.1,
    hq0,hq1,hf.trans F.mem.1⟩

lemma third_upper {z y a c e t : ℝ}
    (hx : X y≤a) (hA : A1 y≤c) (hB : A3 y≤e)
    (hr : 0≤ratio y) (hq : 0<q (U y))
    (ht : 0≤quotient z y) (htt : quotient z y≤t) (hc : 0≤c) (he : 0≤e) :
    third z y≤a+c*t+e*t^3 := by
  have ht3 := pow_le_pow_left₀ ht htt 3
  have hct := (mul_le_mul_of_nonneg_right hA ht).trans
    (mul_le_mul_of_nonneg_left htt hc)
  have het := (mul_le_mul_of_nonneg_right hB (pow_nonneg ht 3)).trans
    (mul_le_mul_of_nonneg_left ht3 he)
  have hlast : 0≤3*(ratio y)^3/(q (U y))^3*(quotient z y)^5 := by positivity
  dsimp [third]
  linarith

lemma early_third_terms {y : ℝ} (hy : y∈Icc 0 (2/5)) :
    X y<(209/200:ℝ) ∧ A1 y<633/250 ∧ A3 y<433/500 := by
  have h := early_data hy
  let R : Interval (ratio y) := Interval.of_bounds ⟨h.1.le,h.2.1.le⟩
  let D : Interval (ratioD y) := Interval.of_bounds ⟨h.2.2.1.le,h.2.2.2.1.le⟩
  let U₀ : Interval (U y) := Interval.of_bounds ⟨(early_U hy).1.le,(early_U hy).2.le⟩
  let Q : Interval (q (U y)) := Interval.of_bounds ⟨h.2.2.2.2.2.1.le,h.2.2.2.2.2.2.1.le⟩
  have hU : 0<U₀.lo := by lower_bounds
  have hQ : 0<Q.lo := by lower_bounds
  let DD₀ := ratioDDBox (Interval.of_bounds hy) U₀ hU
  have hDD : DD₀.hi≤(1:ℝ) := by lower_bounds
  let DD : Interval (ratioDD y) :=
    Interval.of_bounds ⟨h.2.2.2.2.1.le,DD₀.mem.2.trans hDD⟩
  let XX := R.square.mul (factorDDBox U₀ Q hU hQ)
  let AA := A1Box R D DD Q hQ
  let BB := A3Box R D Q hQ
  have hx : XX.hi<(209/200:ℝ) := by lower_bounds
  have hA : AA.hi<(633/250:ℝ) := by lower_bounds
  have hB : BB.hi<(433/500:ℝ) := by lower_bounds
  have hxle : X y≤(ratio y)^2*factorDD (U y) := by
    dsimp [X]
    have hp := mul_nonneg h.2.2.1.le h.2.2.2.2.2.2.2
    linarith
  exact ⟨hxle.trans_lt (XX.mem.2.trans_lt hx),AA.mem.2.trans_lt hA,BB.mem.2.trans_lt hB⟩

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.LowerGeometry
