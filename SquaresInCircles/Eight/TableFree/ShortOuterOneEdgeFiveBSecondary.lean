module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneEdgeFivePositiveNegative

/-!
# Both B tuples on the complete secondary angle halves

Uncompiled transcription of Section 4. The stipulated unit multiplier
gives two exact axial supports. The upper scalar increases; the lower
scalar decreases because its one moving trigonometric term increases
to a value below .973 at the original angle cap.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.EdgeFive.BSecondary
open CommonQuarter CorePairGeometry Arithmetic StationaryPrimitives
open ShortWord.MixedQuarter.Reference

def H (r : Row) (upper : Bool) (x : ℝ) : ℝ :=
  angle upper x+c r+(p r-P r)*outerAxial+1/2+(1/2-outerAxial)*Real.cos x+Real.sin x/2
def sweep (x : ℝ) : ℝ := (outerAxial-1/2)*Real.sin x+Real.cos x/2
def sweepD (x : ℝ) : ℝ := (outerAxial-1/2)*Real.cos x-Real.sin x/2
def Hd (upper : Bool) (x : ℝ) : ℝ := direction upper+sweep x

theorem sweep_hasDerivAt (x : ℝ) : HasDerivAt sweep (sweepD x) x := by
  have h : HasDerivAt sweep ((outerAxial-1/2)*Real.cos x+(-Real.sin x)/2) x :=
    ((Real.hasDerivAt_sin x).const_mul (outerAxial-1/2)).fun_add
      ((Real.hasDerivAt_cos x).div_const 2)
  exact h.congr_deriv (by simp only [sweepD]; ring)
theorem sweepD_positive {x : ℝ} (hx : x∈Icc 0 (7/10)) : 0<sweepD x := by
  have ht := positive_trig hx
  have ha : (91/100:ℝ)<outerAxial-1/2 := by linarith [outer_endpoint_bounds.1]
  have hp := mul_lt_mul_of_pos_right ha (show 0<Real.cos x by linarith [ht.1])
  dsimp [sweepD]
  nlinarith [ht.2.2.2.1]
theorem sweep_monotone : MonotoneOn sweep (Icc 0 (7/10)) :=
  monoOn_of_hasDeriv_nonneg
    (fun x _ => (sweep_hasDerivAt x).continuousAt.continuousWithinAt)
    (fun x _ => sweep_hasDerivAt x)
    (fun x hx => (sweepD_positive (Ioo_subset_Icc_self hx)).le)
theorem sweep_cap : sweep (7/10)<973/1000 := by
  let B := ((axial.sub (Interval.point (1/2))).mul
    (sine (by norm_num : (0:ℝ)≤7/10))).add
      ((cosine (by norm_num : (0:ℝ)≤7/10)).div (Interval.point 2) (by norm_num [Interval.point]))
  have hh : B.hi<(973/1000:ℝ) := by dsimp [B]; mixed_fixed
  exact B.mem.2.trans_lt hh
theorem sweep_bounds {x : ℝ} (hx : x∈Icc 0 (7/10)) : 0≤ sweep x ∧ sweep x<973/1000 := by
  have ht := positive_trig hx
  have hp := mul_nonneg (show 0≤outerAxial-1/2 by linarith [outer_endpoint_bounds.1]) ht.2.2.1
  refine ⟨?_,(sweep_monotone hx (show (7/10:ℝ)∈Icc 0 (7/10) by norm_num) hx.2).trans_lt sweep_cap⟩
  dsimp [sweep]
  linarith [ht.1]
theorem H_hasDerivAt (r : Row) (upper : Bool) (x : ℝ) : HasDerivAt (H r upper) (Hd upper x) x := by
  have h1 : HasDerivAt (fun y => angle upper y+c r+(p r-P r)*outerAxial+1/2)
      (direction upper*1) x :=
    ((((hasDerivAt_id' x).const_mul (direction upper)).const_add (Real.pi/2)).add_const
      (c r)).add_const ((p r-P r)*outerAxial) |>.add_const (1/2)
  have h2 := (h1.fun_add ((Real.hasDerivAt_cos x).const_mul (1/2-outerAxial))).fun_add
    ((Real.hasDerivAt_sin x).div_const 2)
  have h3 : HasDerivAt (H r upper)
      (direction upper*1+(1/2-outerAxial)*(-Real.sin x)+Real.cos x/2) x := h2
  exact h3.congr_deriv (by simp only [Hd,sweep]; ring)
theorem upper_monotone (r : Row) : MonotoneOn (H r true) (Icc 0 (7/10)) :=
  monoOn_of_hasDeriv_nonneg
    (fun x _ => (H_hasDerivAt r true x).continuousAt.continuousWithinAt)
    (fun x _ => H_hasDerivAt r true x)
    (fun x hx => by
      dsimp [Hd,direction,ShortWord.MixedQuarter.direction]
      linarith [(sweep_bounds (Ioo_subset_Icc_self hx)).1])
theorem lower_antitone (r : Row) : AntitoneOn (H r false) (Icc 0 (7/10)) :=
  antiOn_of_hasDeriv_nonpos
    (fun x _ => (H_hasDerivAt r false x).continuousAt.continuousWithinAt)
    (fun x _ => H_hasDerivAt r false x)
    (fun x hx => by
      dsimp [Hd,direction,ShortWord.MixedQuarter.direction]
      linarith [(sweep_bounds (Ioo_subset_Icc_self hx)).2])

def initialBox (r : Row) : Interval (H r true 0) := by
  convert (((halfPi.add (Interval.point (c r))).add
    ((Interval.point (p r-P r)).mul axial)).add (Interval.point 1)).sub axial using 1
  simp [H,ShortWord.MixedQuarter.angle,ShortWord.MixedQuarter.direction]
  ring
def terminalBox (r : Row) : Interval (H r false (7/10)) := by
  convert ((((((halfPi.sub (Interval.point (7/10))).add (Interval.point (c r))).add
    ((Interval.point (p r-P r)).mul axial)).add (Interval.point (1/2))).add
      (((Interval.point (1/2)).sub axial).mul (cosine (by norm_num : (0:ℝ)≤7/10)))).add
        ((sine (by norm_num : (0:ℝ)≤7/10)).div (Interval.point 2) (by norm_num [Interval.point]))) using 1
  simp [H,ShortWord.MixedQuarter.angle,ShortWord.MixedQuarter.direction]
  ring
private theorem r84_initial_of (r : Row)
    (h : (2697/2500:ℝ)<((((halfPi.add (Interval.point (c r))).add
      ((Interval.point (p r-P r)).mul axial)).add (Interval.point 1)).sub axial).lo) :
    (2697/2500:ℝ)<H r true 0 := by
  have h2 := h.trans_le ((((halfPi.add (Interval.point (c r))).add
      ((Interval.point (p r-P r)).mul axial)).add (Interval.point 1)).sub axial).mem.1
  have he : H r true 0=Real.pi/2+c r+(p r-P r)*outerAxial+1-outerAxial := by
    simp [H,ShortWord.MixedQuarter.angle,ShortWord.MixedQuarter.direction]
    ring
  rw [he]
  exact h2
private theorem r84_terminal_of (r : Row)
    (h : (229/250:ℝ)<((((((halfPi.sub (Interval.point (7/10))).add (Interval.point (c r))).add
      ((Interval.point (p r-P r)).mul axial)).add (Interval.point (1/2))).add
        (((Interval.point (1/2)).sub axial).mul
          (ShortWord.MixedQuarter.Reference.cosine (by norm_num : (0:ℝ)≤7/10)))).add
            ((ShortWord.MixedQuarter.Reference.sine (by norm_num : (0:ℝ)≤7/10)).div
              (Interval.point 2) (by norm_num [Interval.point]))).lo) :
    (229/250:ℝ)<H r false (7/10) := by
  have h2 := h.trans_le ((((((halfPi.sub (Interval.point (7/10))).add (Interval.point (c r))).add
      ((Interval.point (p r-P r)).mul axial)).add (Interval.point (1/2))).add
        (((Interval.point (1/2)).sub axial).mul
          (ShortWord.MixedQuarter.Reference.cosine (by norm_num : (0:ℝ)≤7/10)))).add
            ((ShortWord.MixedQuarter.Reference.sine (by norm_num : (0:ℝ)≤7/10)).div
              (Interval.point 2) (by norm_num [Interval.point]))).mem.1
  have he : H r false (7/10)=Real.pi/2-7/10+c r+(p r-P r)*outerAxial+1/2+
      (1/2-outerAxial)*Real.cos (7/10)+Real.sin (7/10)/2 := by
    simp only [H,ShortWord.MixedQuarter.angle,ShortWord.MixedQuarter.direction,
      Bool.false_eq_true,↓reduceIte]
    ring
  rw [he]
  exact h2
theorem initial (r : Row) (hr : BRows r) : (2697/2500:ℝ)<H r true 0 := by
  apply r84_initial_of
  rcases hr with rfl|rfl <;> dsimp [c,p,P] <;> mixed_fixed
theorem terminal (r : Row) (hr : BRows r) : (229/250:ℝ)<H r false (7/10) := by
  apply r84_terminal_of
  rcases hr with rfl|rfl <;> dsimp [c,p,P] <;> mixed_fixed
theorem lower (r : Row) (hr : BRows r) (upper : Bool) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (229/250:ℝ)<H r upper x := by
  cases upper
  · exact (terminal r hr).trans_le (lower_antitone r hx (by norm_num) hx.2)
  · have hh := (initial r hr).trans_le (upper_monotone r (by norm_num) hx hx.1)
    linarith

theorem original_lower (r : Row) (hr : BRows r) (upper : Bool) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : Secondary r upper a b A B x) : H r upper x≤cost r upper a b A B x := by
  have hcoeff := coefficient_bounds r
  have tr := positive_trig hx
  have hsource := ShortWord.MixedQuarter.outer_axial_lower (X:=p r) (Y:=1-q r) hs
    hcoeff.1 (by linarith [hcoeff.2.2.2.1])
  have hX : -P r-Real.cos x≤0 := by linarith [hcoeff.2.1,tr.1]
  have hY : 0≤t r+direction upper*Real.sin x := by
    cases upper <;> dsimp [direction,ShortWord.MixedQuarter.direction] <;>
      linarith [hcoeff.2.2.2.2.1,tr.2.2.1,tr.2.2.2.1]
  have htarget := ShortWord.MixedQuarter.outer_axial_lower
    (X:= -P r-Real.cos x) (Y:=t r+direction upper*Real.sin x) ht hX hY
  have hh := secondary_support r upper (lam:=1) (by norm_num) hm
    (S:=p r*outerAxial) (T:=(-P r-Real.cos x)*outerAxial)
    (by rw [B_sign hr]; nlinarith [hsource]) (by rw [B_sign hr]; nlinarith [htarget])
  dsimp [H,width] at hh ⊢
  linarith
theorem original (r : Row) (hr : BRows r) (upper : Bool) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : Secondary r upper a b A B x) : (229/250:ℝ)<cost r upper a b A B x :=
  (lower r hr upper hx).trans_le (original_lower r hr upper hs ht hx hm)

end SquaresInCircles.Eight.TableFree.ShortOuterOne.EdgeFive.BSecondary
