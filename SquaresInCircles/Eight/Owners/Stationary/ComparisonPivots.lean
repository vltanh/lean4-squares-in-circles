module

public import SquaresInCircles.Eight.Owners.Stationary.ComparisonBounds

/-!
# Eight squares: three exact comparison values for the position localization

Each theorem retains the complete original
radius interval.  Positive squaring gives the four successive circle
roots at the one specified comparison position, and ordered-field
arithmetic then bounds the actual position derivative.  These are the
three comparison values in the continuous affine-curve proof, not a
cover or a search for a stationary root.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.StationaryPrimitives
open Stationary.FiveCornerGeometry

theorem upper_pivot {q : ℝ} (hq : q∈Icc (19577/5000:ℝ) (9789/2500)) :
    183/5000<2*positionHalf q (cosine (13/100)) (sine (13/100)) (461/500) := by
  have hu : (461/500:ℝ)∈Icc (461/500) (461/500) := ⟨le_rfl,le_rfl⟩
  obtain ⟨hr,hU,hV,hY,hv,hw⟩ := radical_box hq hu
    (rl:=175080438/100000000) (ru:=175086151/100000000)
    (Ul:=165931190/100000000) (Uu:=165937218/100000000)
    (Yl:=145531969/100000000) (Yu:=145544394/100000000)
    (wl:=190229423/100000000) (wu:=190238238/100000000) (by norm_num)
  have hh : (13/100:ℝ)∈Icc (13/100) (13/100) := ⟨le_rfl,le_rfl⟩
  have hc := cosine_box hh (cl:=99165561/100000000) (cu:=99165563/100000000) (by norm_num)
  have hs : sine (13/100)∈Icc ((13/100:ℝ)*(99165561/100000000))
      ((13/100:ℝ)*(99165563/100000000)) := by
    rw [sine_eq]
    exact product_bounds hh hc (by norm_num) (by norm_num)
  let J := differentialIntervals (Interval.of_bounds hq) (Interval.of_bounds hu)
    (Interval.of_bounds hr) (Interval.of_bounds hU) (Interval.of_bounds hV)
    (Interval.of_bounds hY) (Interval.of_bounds hv) (Interval.of_bounds hw)
    (Interval.of_bounds hc) (Interval.of_bounds hs)
    (by norm_num [Interval.of_bounds]) (by norm_num [Interval.of_bounds])
    (by norm_num [Interval.of_bounds]) (by norm_num [Interval.of_bounds])
    (by norm_num [Interval.of_bounds]) (by norm_num [Interval.of_bounds])
  have hf := J.first.mem
  norm_num [J,differentialIntervals,Interval.of_bounds,Interval.point,Interval.add,
    Interval.sub,Interval.neg,Interval.mul,Interval.div,Interval.inv,Interval.square,Interval.cube] at hf
  linarith [hf.1]

theorem lower_fixed_endpoint {q : ℝ} (hq : q∈Icc (19577/5000:ℝ) (9789/2500)) :
    2*positionHalf q (cosine (41/250)) (sine (41/250)) (179/200)< -11/1000 := by
  have hu : (179/200:ℝ)∈Icc (179/200) (179/200) := ⟨le_rfl,le_rfl⟩
  obtain ⟨hr,hU,hV,hY,hv,hw⟩ := radical_box hq hu
    (rl:=176475918/100000000) (ru:=176481587/100000000)
    (Ul:=164145514/100000000) (Uu:=164151608/100000000)
    (Yl:=143866460/100000000) (Yu:=143879167/100000000)
    (wl:=189744632/100000000) (wu:=189753663/100000000) (by norm_num)
  have hh : (41/250:ℝ)∈Icc (41/250) (41/250) := ⟨le_rfl,le_rfl⟩
  have hc := cosine_box hh (cl:=98681733/100000000) (cu:=98681734/100000000) (by norm_num)
  have hs : sine (41/250)∈Icc ((41/250:ℝ)*(98681733/100000000))
      ((41/250:ℝ)*(98681734/100000000)) := by
    rw [sine_eq]
    exact product_bounds hh hc (by norm_num) (by norm_num)
  let J := differentialIntervals (Interval.of_bounds hq) (Interval.of_bounds hu)
    (Interval.of_bounds hr) (Interval.of_bounds hU) (Interval.of_bounds hV)
    (Interval.of_bounds hY) (Interval.of_bounds hv) (Interval.of_bounds hw)
    (Interval.of_bounds hc) (Interval.of_bounds hs)
    (by norm_num [Interval.of_bounds]) (by norm_num [Interval.of_bounds])
    (by norm_num [Interval.of_bounds]) (by norm_num [Interval.of_bounds])
    (by norm_num [Interval.of_bounds]) (by norm_num [Interval.of_bounds])
  have hf := J.first.mem
  norm_num [J,differentialIntervals,Interval.of_bounds,Interval.point,Interval.add,
    Interval.sub,Interval.neg,Interval.mul,Interval.div,Interval.inv,Interval.square,Interval.cube] at hf
  linarith [hf.2]

theorem lower_affine_pivot {q : ℝ} (hq : q∈Icc (19577/5000:ℝ) (9789/2500)) :
    2*positionHalf q (cosine (3/25)) (sine (3/25)) (229/250)< -27/500 := by
  have hu : (229/250:ℝ)∈Icc (229/250) (229/250) := ⟨le_rfl,le_rfl⟩
  obtain ⟨hr,hU,hV,hY,hv,hw⟩ := radical_box hq hu
    (rl:=175395096/100000000) (ru:=175400799/100000000)
    (Ul:=165539844/100000000) (Uu:=165545885/100000000)
    (Yl:=145170473/100000000) (Yu:=145182958/100000000)
    (wl:=190125545/100000000) (wu:=190134406/100000000) (by norm_num)
  have hh : (3/25:ℝ)∈Icc (3/25) (3/25) := ⟨le_rfl,le_rfl⟩
  have hc := cosine_box hh (cl:=99287683/100000000) (cu:=99287685/100000000) (by norm_num)
  have hs : sine (3/25)∈Icc ((3/25:ℝ)*(99287683/100000000))
      ((3/25:ℝ)*(99287685/100000000)) := by
    rw [sine_eq]
    exact product_bounds hh hc (by norm_num) (by norm_num)
  let J := differentialIntervals (Interval.of_bounds hq) (Interval.of_bounds hu)
    (Interval.of_bounds hr) (Interval.of_bounds hU) (Interval.of_bounds hV)
    (Interval.of_bounds hY) (Interval.of_bounds hv) (Interval.of_bounds hw)
    (Interval.of_bounds hc) (Interval.of_bounds hs)
    (by norm_num [Interval.of_bounds]) (by norm_num [Interval.of_bounds])
    (by norm_num [Interval.of_bounds]) (by norm_num [Interval.of_bounds])
    (by norm_num [Interval.of_bounds]) (by norm_num [Interval.of_bounds])
  have hf := J.first.mem
  norm_num [J,differentialIntervals,Interval.of_bounds,Interval.point,Interval.add,
    Interval.sub,Interval.neg,Interval.mul,Interval.div,Interval.inv,Interval.square,Interval.cube] at hf
  linarith [hf.2]

end SquaresInCircles.Eight.StationaryPrimitives
