module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneEdgeFiveData

/-!
# All original positive-to-negative owners on roles five and four

Uncompiled transcription of Sections 2 and 7 of the edge-five complete
note. On the lower half every original projection is bounded by the
same transverse sum. Its scalar has the stated Cauchy derivative bound.
The upper half and the role-four corollary use the original direct labels.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.EdgeFive.PositiveNegative
open CommonQuarter CorePairGeometry Arithmetic TableFreeWordGeometry StationaryPrimitives
open ShortWord.MixedQuarter.Reference

def F (x : ℝ) : ℝ := Real.pi/2-x+21108/100000-(18602/100000)*outerAxial+
  (80996/100000)*(1/2+Real.sin x/2+(1/2-outerAxial)*Real.cos x)
def Fd (x : ℝ) : ℝ := -1+(80996/100000)*
  ((1/2)*Real.cos x+(outerAxial-1/2)*Real.sin x)

theorem half_angle_bound {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    1-Real.cos x≤(3/8)*Real.sin x := by
  have ht := positive_trig hx
  have hden : 0<1+Real.cos x := by linarith [ht.1]
  have hcoef : Real.sin x≤(3/8)*(1+Real.cos x) := by linarith [ht.1,ht.2.2.2.1]
  have hp := mul_le_mul_of_nonneg_right hcoef ht.2.2.1
  have hid : (1-Real.cos x)*(1+Real.cos x)=(Real.sin x)^2 := by
    nlinarith [Real.sin_sq_add_cos_sq x]
  apply (mul_le_mul_iff_of_pos_right hden).mp
  nlinarith
theorem primary_projection_bound {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    outerAxial-outerDiagonal*Real.sin x≤outerAxial*Real.cos x := by
  have ht := positive_trig hx
  have hcoef : (3/8)*outerAxial≤outerDiagonal := by
    linarith [ShortOuterZero.fine_axial_bounds.2,ShortMixedZero.fine_diagonal_bounds.1]
  have hhalf := mul_le_mul_of_nonneg_left (half_angle_bound hx)
    (show 0≤outerAxial by linarith [outer_endpoint_bounds.1])
  have hp := mul_le_mul_of_nonneg_right hcoef ht.2.2.1
  nlinarith

theorem original_transverse (j : Fin 4) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin j a b A B 1 (-1) (angle false x)) :
    width x-outerAxial*Real.cos x≤b+B := by
  have hsb := outer_bounds hs
  have htb := outer_bounds ht
  have tr := positive_trig hx
  have hc : 0≤Real.cos x := by linarith [tr.1]
  have hac := mul_le_mul_of_nonneg_right hsb.2.1 hc
  have hAc := mul_le_mul_of_nonneg_right htb.2.1 hc
  have hads := mul_le_mul_of_nonneg_right hsb.1 tr.2.2.1
  have hAds := mul_le_mul_of_nonneg_right htb.1 tr.2.2.1
  have hbs := mul_le_mul_of_nonneg_left (Real.sin_le_one x) hs.1
  have hBs := mul_le_mul_of_nonneg_left (Real.sin_le_one x) ht.1
  have hbc := mul_le_mul_of_nonneg_left (Real.cos_le_one x) hs.1
  have hBc := mul_le_mul_of_nonneg_left (Real.cos_le_one x) ht.1
  have hprimary := primary_projection_bound hx
  fin_cases j <;> norm_num [Eight.forwardMargin] at hm <;>
    rw [ShortWord.MixedQuarter.angle_sin,ShortWord.MixedQuarter.angle_cos,
      ShortWord.MixedQuarter.angle_width false hx] at hm <;>
    dsimp [direction,width] at * <;> nlinarith

theorem F_hasDerivAt (x : ℝ) : HasDerivAt F (Fd x) x := by
  convert ((((hasDerivAt_id x).neg).const_add
    (Real.pi/2+21108/100000-(18602/100000)*outerAxial)).add
      ((((Real.hasDerivAt_sin x).div_const 2).const_add (1/2)).add
        ((Real.hasDerivAt_cos x).const_mul (1/2-outerAxial))).const_mul (80996/100000))
    using 1 <;> dsimp [F,Fd] <;> ring
theorem Fd_negative (x : ℝ) : Fd x<0 := by
  have hh := axial_trig_upper x
  dsimp [Fd]
  linarith
theorem F_antitone : AntitoneOn F (Icc 0 (7/10)) :=
  antiOn_of_hasDeriv_nonpos
    (fun x _ => (F_hasDerivAt x).continuousAt.continuousWithinAt)
    (fun x _ => F_hasDerivAt x) (fun x _ => (Fd_negative x).le)

def endpointBox : Interval (F (7/10)) := by
  convert ((((halfPi.sub (Interval.point (7/10))).add (Interval.point (21108/100000))).sub
    ((Interval.point (18602/100000)).mul axial)).add
      ((Interval.point (80996/100000)).mul
        (((Interval.point (1/2)).add
          ((sine (by norm_num : (0:ℝ)≤7/10)).div (Interval.point 2) (by norm_num [Interval.point]))).add
            (((Interval.point (1/2)).sub axial).mul (cosine (by norm_num : (0:ℝ)≤7/10))))) using 1
  dsimp [F]
  ring
theorem endpoint : (459/500:ℝ)<F (7/10) := by
  have hh : (459/500:ℝ)<endpointBox.lo := by dsimp [endpointBox]; mixed_fixed
  exact hh.trans_le endpointBox.mem.1

theorem original_five_half (upper : Bool) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (j : Fin 4) (hm : 0≤Eight.forwardMargin j a b A B 1 (-1) (angle upper x)) :
    (459/500:ℝ)<angle upper x+21108/100000+(86884/100000)*b-(18602/100000)*A+(80996/100000)*B := by
  have hA := mul_le_mul_of_nonneg_left (outer_bounds ht).2.1
    (by norm_num : (0:ℝ)≤18602/100000)
  cases upper
  · have hsum := original_transverse j hs ht hx hm
    have hmono := F_antitone hx (show (7/10:ℝ)∈Icc 0 (7/10) by norm_num) hx.2
    have hf : (459/500:ℝ)<F x := endpoint.trans_le hmono
    dsimp [F,angle,direction,width] at *
    nlinarith [hs.1]
  · have ha := ShortOuterZero.fine_axial_bounds.2
    have hp := pi_hand_enclosure.1
    dsimp [angle,direction]
    nlinarith [hx.1,hs.1,ht.1]

theorem original_five {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B 1 (-1) φ) :
    (459/500:ℝ)<φ+wrongValue .short 5 .outer true a b-
      wrongValue .short (next 5) .outer false A B := by
  obtain ⟨upper,x,hx,rfl⟩ := ShortWord.MixedQuarter.angle_cover hφ
  have hh := original_five_half upper hs ht hx j hm
  norm_num [wrongValue,WordProblems.shortCoefficients,WordProblems.radialIndex,
    WordProblems.signIndex,WordProblems.sign,next] at *
  linarith

theorem original_four {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) :
    (1869/2000:ℝ)<φ+wrongValue .short 4 .outer true a b-
      wrongValue .short (next 4) .outer false A B := by
  have htarget := ShortWord.MixedQuarter.outer_increasing_label_lower
    (X:=(20967/100000:ℝ)) (Y:=(83048/100000:ℝ)) ht (by norm_num)
  have ha := ShortOuterZero.fine_axial_bounds.1
  have hangle := (abs_le.mp hφ).1
  have hp := pi_hand_enclosure.1
  norm_num [wrongValue,WordProblems.shortCoefficients,WordProblems.radialIndex,
    WordProblems.signIndex,WordProblems.sign,next]
  nlinarith [hs.1]

end SquaresInCircles.Eight.TableFree.ShortOuterOne.EdgeFive.PositiveNegative
