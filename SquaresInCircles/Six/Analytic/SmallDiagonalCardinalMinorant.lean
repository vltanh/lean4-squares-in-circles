import SquaresInCircles.Six.Analytic.SmallDiagonalStressTools

/-!
# Cardinal W: a radical minorant on the whole small-diagonal rectangle

The C--W, C--D and W--D multipliers are 1, 3/2 and 1. In the W frame the
force norm is sqrt(2+2 sin d), independent of the W tilt v. This identity
makes the vertex minorant separately concave on [0,2/5] x [0,1/2].

The v slice is a positive trigonometric sum. The d slice uses the explicit
radical curvature identity with p=q=2. Four original rectangle corners,
proved with visible Taylor and rational root bounds, complete the argument.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

def cardinalSmallDMinorant (v d : ℝ) : ℝ :=
  3-c0+Real.cos v+(3/4-(3/2)*c0)*(Real.cos d+Real.sin d)+
    Real.cos (v+d)+Real.sin (v+d)-
    R0*Real.sqrt (2+2*Real.sin d)-R0*Real.sqrt (13/4)

lemma cardinalSmallD_concave_v {d : ℝ} (hd : 0≤d ∧ d≤1/2) :
    ConcaveOn ℝ (Set.Icc 0 (2/5)) (fun v => cardinalSmallDMinorant v d) := by
  let A := 1+Real.cos d+Real.sin d
  let B := Real.cos d-Real.sin d
  let C := 3-c0+(3/4-(3/2)*c0)*(Real.cos d+Real.sin d)-
    R0*Real.sqrt (2+2*Real.sin d)-R0*Real.sqrt (13/4)
  have ht := small_secondary_trig ⟨hd.1,by linarith [hd.2]⟩
  have hA : 0≤A := by dsimp [A]; linarith [ht.1,ht.2.1]
  have hB : 0≤B := by
    have hh := Seven.sin_le_cos_of_small ⟨hd.1,by linarith [hd.2,Real.pi_gt_d2]⟩
    dsimp [B]
    linarith
  have hc := signed_trig_concave (A := A) (B := B) (C := C) (l := 0) (u := 2/5) (by
    intro v hv
    have hvtr := small_secondary_trig ⟨hv.1,by linarith [hv.2]⟩
    exact add_nonneg (mul_nonneg hA hvtr.1) (mul_nonneg hB hvtr.2.1))
  apply hc.congr
  intro v _
  dsimp [A,B,C,cardinalSmallDMinorant]
  rw [Real.cos_add,Real.sin_add]
  ring

lemma cardinalSmallD_concave_d {v : ℝ} (hv : 0≤v ∧ v≤2/5) :
    ConcaveOn ℝ (Set.Icc 0 (1/2)) (fun d => cardinalSmallDMinorant v d) := by
  let K := 3/4-(3/2)*c0
  let A := K+Real.cos v+Real.sin v
  let B := K+Real.cos v-Real.sin v
  let C := 3-c0+Real.cos v-R0*Real.sqrt (13/4)
  have hK : 0≤K := by dsimp [K]; linarith [c0_lt_23_200]
  have hroot (d : ℝ) (hd : d∈Set.Icc 0 (1/2)) : 0<2+2*Real.sin d := by
    have hs := (small_secondary_trig ⟨hd.1,by linarith [hd.2]⟩).2.1
    linarith
  have hbound (d : ℝ) (hd : d∈Set.Icc 0 (1/2)) :
      R0*Real.sqrt (2+2*Real.sin d)≤4*(A*Real.cos d+B*Real.sin d) := by
    have hrd := Real.sqrt_le_sqrt (show 2+2*Real.sin d≤(2:ℝ)^2 by linarith [Real.sin_le_one d])
    rw [Real.sqrt_sq (by norm_num)] at hrd
    have hR := mul_le_mul (show R0≤2 by linarith [R0_lt_1689_1000]) hrd
      (Real.sqrt_nonneg _) (by norm_num : (0:ℝ)≤2)
    have hq := small_secondary_trig
      (show 0≤v+d ∧ v+d≤7/6 by constructor <;> linarith [hv.1,hv.2,hd.1,hd.2])
    have hw := one_le_abs_cos_add_abs_sin (v+d)
    rw [abs_of_nonneg hq.1,abs_of_nonneg hq.2.1] at hw
    have hdt := small_secondary_trig ⟨hd.1,by linarith [hd.2]⟩
    have hpositive := mul_nonneg hK (add_nonneg hdt.1 hdt.2.1)
    have hid : A*Real.cos d+B*Real.sin d=
        K*(Real.cos d+Real.sin d)+Real.cos (v+d)+Real.sin (v+d) := by
      dsimp [A,B]
      rw [Real.cos_add,Real.sin_add]
      ring
    rw [hid]
    nlinarith only [hR,hw,hpositive]
  have hr := radicalTrig_concave (A := A) (B := B) (p := 2) (q := 2) (R := R0)
    (l := 0) (u := 1/2) R0_nonneg (by norm_num) hroot hbound
  have hc := (concave_constant C 0 (1/2)).add hr
  apply hc.congr
  intro d _
  dsimp [C,A,B,K,radicalTrig,cardinalSmallDMinorant]
  rw [Real.cos_add,Real.sin_add]
  ring

def cardinalSmallDRationalMinorant (v d L : ℝ) : ℝ :=
  3-5641/50000+Real.cos v+(3/4-(3/2)*(5641/50000))*(Real.cos d+Real.sin d)+
    Real.cos (v+d)+Real.sin (v+d)-(33771/20000)*(L+90139/50000)

lemma cardinalSmallD_above_rational {v d L : ℝ} (hd : 0≤d ∧ d≤1/2)
    (hL : 0≤L) (hnorm : 2+2*Real.sin d≤L^2) :
    cardinalSmallDRationalMinorant v d L≤cardinalSmallDMinorant v d := by
  have hroot := Real.sqrt_le_sqrt hnorm
  rw [Real.sqrt_sq hL] at hroot
  have hDroot := Real.sqrt_le_sqrt (show (13/4:ℝ)≤(90139/50000)^2 by norm_num)
  rw [Real.sqrt_sq (by norm_num)] at hDroot
  have hsum : Real.sqrt (2+2*Real.sin d)+Real.sqrt (13/4)≤L+90139/50000 := by linarith
  have hR := mul_le_mul normalization_radius_upper_sharp.le hsum
    (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (by norm_num : (0:ℝ)≤33771/20000)
  have ht := small_secondary_trig ⟨hd.1,by linarith [hd.2]⟩
  have hC := mul_le_mul_of_nonneg_right normalization_center_upper_sharp.le
    (show 0≤1+(3/2)*(Real.cos d+Real.sin d) by linarith [ht.1,ht.2.1])
  dsimp [cardinalSmallDRationalMinorant,cardinalSmallDMinorant]
  nlinarith only [hR,hC]

private lemma cardinal_root_half : 2+2*Real.sin ((1:ℝ)/2)≤(86007/50000)^2 := by
  have hs := Seven.sin_upper_five (x := (1:ℝ)/2) (by norm_num)
  nlinarith only [hs]

/-- Four positive lower bounds, at the original geometric corners only. -/
private lemma cardinal_rational_endpoints :
    0<cardinalSmallDRationalMinorant 0 0 (70711/50000) ∧
      0<cardinalSmallDRationalMinorant 0 (1/2) (86007/50000) ∧
      0<cardinalSmallDRationalMinorant (2/5) 0 (70711/50000) ∧
      0<cardinalSmallDRationalMinorant (2/5) (1/2) (86007/50000) := by
  refine ⟨?_,?_,?_,?_⟩
  · norm_num [cardinalSmallDRationalMinorant]
  · have hs := Seven.sin_lower_seven (x := (1:ℝ)/2) (by norm_num)
    have hc := Seven.cos_lower_six (x := (1:ℝ)/2) (by norm_num)
    norm_num [cardinalSmallDRationalMinorant]
    nlinarith only [hs,hc]
  · have hs := Seven.sin_lower_seven (x := (2:ℝ)/5) (by norm_num)
    have hc := Seven.cos_lower_six (x := (2:ℝ)/5) (by norm_num)
    norm_num [cardinalSmallDRationalMinorant]
    nlinarith only [hs,hc]
  · have hcv := Seven.cos_lower_six (x := (2:ℝ)/5) (by norm_num)
    have hsd := Seven.sin_lower_seven (x := (1:ℝ)/2) (by norm_num)
    have hcd := Seven.cos_lower_six (x := (1:ℝ)/2) (by norm_num)
    have hsq := Seven.sin_lower_seven (x := (9:ℝ)/10) (by norm_num)
    have hcq := Seven.cos_lower_six (x := (9:ℝ)/10) (by norm_num)
    norm_num [cardinalSmallDRationalMinorant]
    nlinarith only [hcv,hsd,hcd,hsq,hcq]

/-- The complete scalar minorant, with no cell-cover hypothesis. -/
theorem cardinalSmallD_positive {v d : ℝ}
    (hv : 0≤v ∧ v≤2/5) (hd : 0≤d ∧ d≤1/2) : 0<cardinalSmallDMinorant v d := by
  have he := cardinal_rational_endpoints
  have h00 : 0<cardinalSmallDMinorant 0 0 := he.1.trans_le
    (cardinalSmallD_above_rational (by constructor <;> norm_num) (by norm_num) (by norm_num))
  have h01 : 0<cardinalSmallDMinorant 0 (1/2) := he.2.1.trans_le
    (cardinalSmallD_above_rational (by constructor <;> norm_num) (by norm_num) cardinal_root_half)
  have h10 : 0<cardinalSmallDMinorant (2/5) 0 := he.2.2.1.trans_le
    (cardinalSmallD_above_rational (by constructor <;> norm_num) (by norm_num) (by norm_num))
  have h11 : 0<cardinalSmallDMinorant (2/5) (1/2) := he.2.2.2.trans_le
    (cardinalSmallD_above_rational (by constructor <;> norm_num) (by norm_num) cardinal_root_half)
  exact positive_on_separately_concave_rectangle hv hd (fun _ ht => cardinalSmallD_concave_v ht)
    (cardinalSmallD_concave_d (by constructor <;> norm_num))
    (cardinalSmallD_concave_d (by constructor <;> norm_num)) h00 h01 h10 h11

end SquaresInCircles.Six.Analytic
