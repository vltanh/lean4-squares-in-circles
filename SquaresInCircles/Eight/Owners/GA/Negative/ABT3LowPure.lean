module

public import SquaresInCircles.Eight.Owners.GA.Negative.ABT3Endpoints
public import SquaresInCircles.Eight.Owners.GA.Negative.ABT3LowNegative
public import SquaresInCircles.Eight.Owners.GA.Negative.ABT3Positive
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2LowEqual

/-!
# Eight squares: all pure alternatives on the low quarter interval

The GA equal-angle endpoint pays for AB through
the exact decreasing norm increment in the other coefficient. The
negative H curve is concave in tan(s) on the complete interval [0,z].
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeABT3.LowPure
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open NegativeAPositiveTD.SecantCoordinate NegativeAPositiveTD.SecantBounds

private theorem r69_low_dom {z : ℝ} (hz : z∈Icc 0 (1/4:ℝ)) :
    z∈Icc (Certificate.left .low:ℝ) (Certificate.right .low:ℝ) := by
  norm_num [Certificate.left,Certificate.right,Certificate.split]; exact hz

theorem baseline_comparison {s z : ℝ} (hz : z∈Icc 0 (1/4:ℝ)) (hs : s∈Icc 0 frameCap) :
    baseline true (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s z≤
      baseline false (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s z := by
  have hb := Explicit.positive .low (r69_low_dom hz)
  have hl : 0<Explicit.l .low z := by linarith [hb.2.1]
  have hkm := (Explicit.low_ratios hz).2.2.2.2
  have hh := NegativeAPositiveTD.LowEqual.charge_comparison hb.1 hkm.le hl hs
  rw [Angular.baseline_eq_extension true _ _ _ _ hs,Angular.baseline_eq_extension false _ _ _ _ hs]
  simp only [Angular.extension,Angular.affected,↓reduceIte,Bool.false_eq_true,baseline_zero]
  linarith [hh]

theorem equal_positive (atG : Bool) {z : ℝ} (hz : z∈Icc 0 (1/4:ℝ)) :
    0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) z z := by
  have hh := (low_endpoints hz).2.2.2.2
  cases atG
  · exact hh.trans_le (baseline_comparison hz (Explicit.frame_domain .low (r69_low_dom hz)))
  · exact hh

def scalar (atG : Bool) (z x : ℝ) : ℝ :=
  NegativeAPositiveTD.SecantCoordinate.pure
    (baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) 0 z)
    (Explicit.l .low z)
    (Angular.ratio atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z))
    (Explicit.k .low z) 1 z x

theorem ratio_domain (atG : Bool) {z : ℝ} (hz : z∈Icc 0 (1/4:ℝ)) :
    Angular.ratio atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z)∈Icc 0 (113/100:ℝ) := by
  have hb := Explicit.positive .low (r69_low_dom hz)
  have hl : 0<Explicit.l .low z := by linarith [hb.2.1]
  have hr := Explicit.low_ratios hz
  cases atG
  · exact ⟨div_nonneg hb.2.2.le hl.le,(div_le_iff₀ hl).2 hr.2.2.2.1.le⟩
  · exact ⟨div_nonneg hb.1.le hl.le,(div_le_iff₀ hl).2 (by
      simp only [Angular.affected,↓reduceIte]; linarith [hr.2.1,hl])⟩

theorem scalar_concave (atG : Bool) {z : ℝ} (hz : z∈Icc 0 (1/4:ℝ)) :
    ConcaveOn ℝ (Icc 0 (Real.tan z)) (scalar atG z) := by
  have hb := Explicit.low_ranges hz
  have hzf := Explicit.frame_domain .low (r69_low_dom hz)
  apply pure_concave (by linarith [hb.1.1] : 0<Explicit.k .low z) (by norm_num : (0:ℝ)<1)
    hzf le_rfl hzf.2
  intro x hx
  have hs := arctan_interval hzf hx
  have hxhi : x≤32/125 := by
    have ht := tan_monotone hzf (show (1/4:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hz.2
    linarith [hx.2,tan_GA_cut]
  exact (LowNegative.pure_curvature hb.2.1.1 (ratio_domain atG hz)
    ⟨hb.1.1,by linarith [hb.1.2]⟩ ⟨hx.1,hxhi⟩
    ⟨by linarith [hs.2],by linarith [hs.1,hz.2]⟩).le.trans (by norm_num)

theorem scalar_zero (atG : Bool) {z : ℝ} (hz : z∈Icc 0 (1/4:ℝ)) : 0<scalar atG z 0 := by
  simpa [scalar,NegativeAPositiveTD.SecantCoordinate.pure,baseline_zero] using (low_endpoints hz).1
theorem scalar_equal (atG : Bool) {z : ℝ} (hz : z∈Icc 0 (1/4:ℝ)) : 0<scalar atG z (Real.tan z) := by
  have hl : 0<Explicit.l .low z := by linarith [(Explicit.positive .low (r69_low_dom hz)).2.1]
  have hh := Angular.pure_at_original (k:=Explicit.k .low z) (m:=Explicit.m .low z) (z:=z)
    (p:=Explicit.k .low z) (q:=1) atG hl (Explicit.frame_domain .low (r69_low_dom hz))
  simpa only [scalar,hh,sub_self,V_zero,add_zero] using equal_positive atG hz

theorem H_positive (atG : Bool) {s z : ℝ} (hz : z∈Icc 0 (1/4:ℝ)) (hs : s∈Icc 0 z) :
    0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s z+
      V R (Explicit.k .low z) 1 (z-s) := by
  have hzf := Explicit.frame_domain .low (r69_low_dom hz)
  have hsf : s∈Icc 0 frameCap := ⟨hs.1,hs.2.trans hzf.2⟩
  have hx : Real.tan s∈Icc 0 (Real.tan z) := ⟨tan_nonnegative hsf,tan_monotone hsf hzf hs.2⟩
  have hh := concave_gt_of_endpoints (scalar_concave atG hz) hx (scalar_zero atG hz) (scalar_equal atG hz)
  have hl : 0<Explicit.l .low z := by linarith [(Explicit.positive .low (r69_low_dom hz)).2.1]
  simpa only [scalar,Angular.pure_at_original atG hl hsf] using hh

theorem negative_positive (atG : Bool) {s z : ℝ} (hz : z∈Icc 0 (1/4:ℝ))
    (hs : s∈Icc 0 (Explicit.angleCut atG)) (hsz : s≤z) (i : Fin 4) :
    0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s z+
      V R (Explicit.p .low atG z s i) (Explicit.q .low atG z s i) (z-s) := by
  have hh := H_positive atG hz ⟨hs.1,hsz⟩
  have hc := LowNegative.comparison (t:=z-s) atG hz hs ⟨by linarith,by linarith [hz.2,hs.1]⟩ i
  linarith

theorem original (atG : Bool) {s z : ℝ} (hz : z∈Icc 0 (1/4:ℝ))
    (hs : s∈Icc 0 (Explicit.angleCut atG)) (i j : Fin 4) :
    0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s z+
      Concentration.pure .low (Explicit.p .low atG z s) (Explicit.q .low atG z s) i j s z := by
  by_cases hsz : s≤z
  · simpa only [Concentration.pure,ite_eq_left hsz] using negative_positive atG hz hs hsz j
  · have hp := Positive.reduces_to_equal .low atG (r69_low_dom hz) hs (le_of_not_ge hsz) i
    have he := equal_positive atG hz
    simp only [Concentration.pure,ite_eq_right hsz]
    linarith

end SquaresInCircles.Eight.GlobalGA.NegativeABT3.LowPure
