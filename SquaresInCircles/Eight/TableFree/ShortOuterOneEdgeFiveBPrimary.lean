module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneEdgeFiveBSecondary

/-!
# Both B tuples on the complete primary angle halves

Uncompiled transcription of Section 5 of the edge-five completion
note. The multiplier is exactly four fifths. The lower target keeps
both actual arc endpoints: its axial scalar is concave and its diagonal
scalar increases on the entire original angle half.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.EdgeFive.BPrimary
open CommonQuarter CorePairGeometry Arithmetic StationaryPrimitives
open ShortWord.MixedQuarter.Reference

def source (r : Row) : ℝ :=
  (4/5-p r+q r)/2-CommonQuarter.radius*Real.sqrt ((4/5-p r)^2+q r^2)
def HA (r : Row) (upper : Bool) (x : ℝ) : ℝ :=
  angle upper x+c r+source r-P r*outerAxial+2/5+
    (2/5)*Real.cos x+(4/5)*(1/2-direction upper*outerAxial)*Real.sin x
def HAd (upper : Bool) (x : ℝ) : ℝ :=
  direction upper-(2/5)*Real.sin x+
    (4/5)*(1/2-direction upper*outerAxial)*Real.cos x
def HAdd (upper : Bool) (x : ℝ) : ℝ :=
  -(2/5)*Real.cos x-(4/5)*(1/2-direction upper*outerAxial)*Real.sin x
def HD (r : Row) (x : ℝ) : ℝ :=
  Real.pi/2-x+c r+source r+(t r-P r)*outerDiagonal+2/5+
    (4/5)*(1/2-outerDiagonal)*Real.cos x+(4/5)*(1/2+outerDiagonal)*Real.sin x
def sweep (x : ℝ) : ℝ :=
  (4/5)*((outerDiagonal-1/2)*Real.sin x+(outerDiagonal+1/2)*Real.cos x)
def sweepD (x : ℝ) : ℝ :=
  (4/5)*((outerDiagonal-1/2)*Real.cos x-(outerDiagonal+1/2)*Real.sin x)

theorem HA_hasDerivAt (r : Row) (upper : Bool) (x : ℝ) :
    HasDerivAt (HA r upper) (HAd upper x) x := by
  have h := ((((hasDerivAt_id x).const_mul (direction upper)).const_add
    (Real.pi/2+c r+source r-P r*outerAxial+2/5)).add
      ((Real.hasDerivAt_cos x).const_mul (2/5))).add
        ((Real.hasDerivAt_sin x).const_mul ((4/5)*(1/2-direction upper*outerAxial)))
  convert h using 1
  · funext y
    simp only [HA,angle,ShortWord.MixedQuarter.angle,Pi.add_apply,id_eq]
    ring
  · simp only [HAd]; ring
theorem HAd_hasDerivAt (upper : Bool) (x : ℝ) :
    HasDerivAt (HAd upper) (HAdd upper x) x := by
  have h := (((Real.hasDerivAt_sin x).const_mul (-(2/5:ℝ))).const_add (direction upper)).add
    ((Real.hasDerivAt_cos x).const_mul ((4/5)*(1/2-direction upper*outerAxial)))
  convert h using 1
  · funext y
    simp only [HAd,Pi.add_apply]
    ring
  · simp only [HAdd]; ring
theorem upper_derivative (x : ℝ) : 0<HAd true x := by
  have hn : Real.sqrt ((outerAxial-1/2)^2+(1/2:ℝ)^2)<1043/1000 := by
    rw [show (outerAxial-1/2)^2+(1/2:ℝ)^2=(1/2:ℝ)^2+(outerAxial-1/2)^2 by ring]
    exact axial_norm_bound
  have hh := (le_abs_self _).trans
    ((trigonometric_norm (outerAxial-1/2) (1/2) x).trans_lt hn).le
  have hd : direction true=1 := by simp [direction,ShortWord.MixedQuarter.direction]
  dsimp only [HAd]
  rw [hd]
  linarith
theorem upper_monotone (r : Row) : MonotoneOn (HA r true) (Icc 0 (7/10)) :=
  monoOn_of_hasDeriv_nonneg
    (fun x _ => (HA_hasDerivAt r true x).continuousAt.continuousWithinAt)
    (fun x _ => HA_hasDerivAt r true x)
    (fun x _ => (upper_derivative x).le)
theorem lower_concave (r : Row) : ConcaveOn ℝ (Icc 0 (7/10)) (HA r false) :=
  concave_of_deriv2 (fun x _ => HA_hasDerivAt r false x)
    (fun x _ => HAd_hasDerivAt false x) (fun x hx => by
      have ht := positive_trig hx
      have hh := mul_nonneg (show 0≤1/2+outerAxial by linarith [outer_endpoint_bounds.1]) ht.2.2.1
      have hd : direction false= -1 := by simp [direction,ShortWord.MixedQuarter.direction]
      dsimp only [HAdd]
      rw [hd]
      linarith [ht.1])

theorem sweep_hasDerivAt (x : ℝ) : HasDerivAt sweep (sweepD x) x := by
  have h := (((Real.hasDerivAt_sin x).const_mul (outerDiagonal-1/2)).add
    ((Real.hasDerivAt_cos x).const_mul (outerDiagonal+1/2))).const_mul (4/5)
  convert h using 1
  · funext y; simp only [sweep,Pi.add_apply]
  · simp only [sweepD]; ring
theorem sweepD_hasDerivAt (x : ℝ) : HasDerivAt sweepD (-sweep x) x := by
  have h := (((Real.hasDerivAt_cos x).const_mul (outerDiagonal-1/2)).sub
    ((Real.hasDerivAt_sin x).const_mul (outerDiagonal+1/2))).const_mul (4/5)
  convert h using 1
  · funext y; simp only [sweepD,Pi.sub_apply]
  · simp only [sweep]; ring
theorem sweep_positive {x : ℝ} (hx : x∈Icc 0 (7/10)) : 0<sweep x := by
  have ht := positive_trig hx
  have hs := mul_nonneg (show 0≤outerDiagonal-1/2 by linarith [outer_endpoint_bounds.2.2.1]) ht.2.2.1
  have hc := mul_pos (show 0<outerDiagonal+1/2 by linarith [outer_endpoint_bounds.2.2.1])
    (show 0<Real.cos x by linarith [ht.1])
  dsimp [sweep]
  nlinarith
theorem sweep_concave : ConcaveOn ℝ (Icc 0 (7/10)) sweep :=
  concave_of_deriv2 (fun x _ => sweep_hasDerivAt x)
    (fun x _ => sweepD_hasDerivAt x) (fun x hx => by linarith [sweep_positive hx])
theorem sweep_initial : (53/50:ℝ)<sweep 0 := by
  dsimp [sweep]
  simp only [Real.sin_zero,Real.cos_zero]
  linarith [ShortMixedZero.fine_diagonal_bounds.1]
theorem sweep_terminal : (53/50:ℝ)<sweep (7/10) := by
  let D := (Interval.point (4/5)).mul
    (((diagonal.sub (Interval.point (1/2))).mul (sine (by norm_num : (0:ℝ)≤7/10))).add
      ((diagonal.add (Interval.point (1/2))).mul (cosine (by norm_num : (0:ℝ)≤7/10))))
  have hh : (53/50:ℝ)<D.lo := by dsimp [D]; mixed_fixed
  exact hh.trans_le D.mem.1
theorem sweep_lower {x : ℝ} (hx : x∈Icc 0 (7/10)) : (53/50:ℝ)<sweep x :=
  concave_gt_of_endpoints sweep_concave hx sweep_initial sweep_terminal
theorem HD_hasDerivAt (r : Row) (x : ℝ) : HasDerivAt (HD r) (-1+sweep x) x := by
  have h := ((((hasDerivAt_id x).neg).const_add
    (Real.pi/2+c r+source r+(t r-P r)*outerDiagonal+2/5)).add
      ((Real.hasDerivAt_cos x).const_mul ((4/5)*(1/2-outerDiagonal)))).add
        ((Real.hasDerivAt_sin x).const_mul ((4/5)*(1/2+outerDiagonal)))
  convert h using 1
  · funext y
    simp only [HD,Pi.add_apply,Pi.neg_apply,id_eq]
    ring
  · simp only [sweep]; ring
theorem HD_monotone (r : Row) : MonotoneOn (HD r) (Icc 0 (7/10)) :=
  monoOn_of_hasDeriv_nonneg
    (fun x _ => (HD_hasDerivAt r x).continuousAt.continuousWithinAt)
    (fun x _ => HD_hasDerivAt r x)
    (fun x hx => by linarith [sweep_lower (Ioo_subset_Icc_self hx)])

def sourceBox (r : Row) : Interval (source r) := by
  let X := Interval.point ((4/5-p r)^2+q r^2)
  let N := rootSix X 2 (by norm_num)
    (by dsimp [X,Interval.point]; positivity)
  exact (Interval.point ((4/5-p r+q r)/2)).sub (circleRadius.mul N)
def initialBox (r : Row) : Interval (HA r true 0) := by
  convert ((((halfPi.add (Interval.point (c r))).add (sourceBox r)).sub
    ((Interval.point (P r)).mul axial)).add (Interval.point (4/5))) using 1
  simp [HA,ShortWord.MixedQuarter.angle,ShortWord.MixedQuarter.direction]
  ring
def terminalBox (r : Row) : Interval (HA r false (7/10)) := by
  convert (((((((halfPi.sub (Interval.point (7/10))).add (Interval.point (c r))).add (sourceBox r)).sub
    ((Interval.point (P r)).mul axial)).add (Interval.point (2/5))).add
      ((Interval.point (2/5)).mul (cosine (by norm_num : (0:ℝ)≤7/10)))).add
        (((Interval.point (4/5)).mul ((Interval.point (1/2)).add axial)).mul
          (sine (by norm_num : (0:ℝ)≤7/10)))) using 1
  simp [HA,ShortWord.MixedQuarter.angle,ShortWord.MixedQuarter.direction]
  ring
-- `initial` and `terminal` evaluate `initialBox` and `terminalBox`; the source radical is
-- bounded by a rational root checked on its square.
theorem initial (r : Row) (hr : BRows r) : (9231/10000:ℝ)<HA r true 0 := by
  have hR := radius_fine
  have ha := ShortOuterZero.fine_axial_bounds
  have hpi := pi_hand_enclosure
  have hd : direction true=1 := by simp [direction,ShortWord.MixedQuarter.direction]
  have hH : HA r true 0=Real.pi/2+c r+source r-P r*outerAxial+4/5 := by
    simp only [HA,angle,ShortWord.MixedQuarter.angle,hd,Real.sin_zero,Real.cos_zero]; ring
  rw [hH]
  have hq0 := Real.sqrt_nonneg ((4/5-p r)^2+q r^2)
  dsimp only [source]
  rcases hr with rfl|rfl
  · have hq : Real.sqrt ((4/5-p 2)^2+q 2^2)<1307337195/1000000000 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num [p,q]
    generalize Real.sqrt ((4/5-p 2)^2+q 2^2)=S at hq hq0 ⊢
    have hRq := mul_le_mul hR.2.le hq.le hq0 (by norm_num)
    norm_num [c,p,q,P]
    linarith
  · have hq : Real.sqrt ((4/5-p 3)^2+q 3^2)<1316666589/1000000000 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num [p,q]
    generalize Real.sqrt ((4/5-p 3)^2+q 3^2)=S at hq hq0 ⊢
    have hRq := mul_le_mul hR.2.le hq.le hq0 (by norm_num)
    norm_num [c,p,q,P]
    linarith
theorem terminal (r : Row) (hr : BRows r) : (5579/5000:ℝ)<HA r false (7/10) := by
  have hR := radius_fine
  have ha := ShortOuterZero.fine_axial_bounds
  have hpi := pi_hand_enclosure
  have tb := trig_taylor_bounds (show (0:ℝ)≤7/10 by norm_num)
  norm_num [sin7,sin9,cos8,cos10] at tb
  have has := mul_le_mul ha.1.le tb.1 (by norm_num) (by linarith [ha.1])
  have hd : direction false= -1 := by simp [direction,ShortWord.MixedQuarter.direction]
  have hH : HA r false (7/10)=Real.pi/2-7/10+c r+source r-P r*outerAxial+2/5+
      (2/5)*Real.cos (7/10)+(2/5)*Real.sin (7/10)+(4/5)*(outerAxial*Real.sin (7/10)) := by
    simp only [HA,angle,ShortWord.MixedQuarter.angle,hd]; ring
  rw [hH]
  have hq0 := Real.sqrt_nonneg ((4/5-p r)^2+q r^2)
  dsimp only [source]
  rcases hr with rfl|rfl
  · have hq : Real.sqrt ((4/5-p 2)^2+q 2^2)<1307337195/1000000000 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num [p,q]
    generalize Real.sqrt ((4/5-p 2)^2+q 2^2)=S at hq hq0 ⊢
    have hRq := mul_le_mul hR.2.le hq.le hq0 (by norm_num)
    norm_num [c,p,q,P]
    linarith [tb.1,tb.2.2.1]
  · have hq : Real.sqrt ((4/5-p 3)^2+q 3^2)<1316666589/1000000000 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num [p,q]
    generalize Real.sqrt ((4/5-p 3)^2+q 3^2)=S at hq hq0 ⊢
    have hRq := mul_le_mul hR.2.le hq.le hq0 (by norm_num)
    norm_num [c,p,q,P]
    linarith [tb.1,tb.2.2.1]
theorem initial_eq (r : Row) : HA r false 0=HA r true 0 := by
  simp [HA,ShortWord.MixedQuarter.angle]
theorem diagonal_initial (r : Row) (hr : BRows r) : HA r true 0≤HD r 0 := by
  have hc := coefficient_bounds r
  have hY : 0≤t r-4/5 := by linarith [hc.2.2.2.2.1]
  have hdiff : 0≤outerAxial-outerDiagonal := by
    linarith [outer_endpoint_bounds.1,outer_endpoint_bounds.2.2.2]
  have hp := mul_nonneg hc.2.1 hdiff
  have hy := mul_nonneg hY (show 0≤outerDiagonal by linarith [outer_endpoint_bounds.2.2.1])
  simp only [HA,HD,angle,ShortWord.MixedQuarter.angle,Real.sin_zero,Real.cos_zero,mul_zero,
    add_zero,mul_one,sub_zero]
  linarith
theorem axial_lower (r : Row) (hr : BRows r) (upper : Bool) {x : ℝ}
    (hx : x∈Icc 0 (7/10)) : (9231/10000:ℝ)<HA r upper x := by
  cases upper
  · apply concave_gt_of_endpoints (lower_concave r) hx
    · rw [initial_eq]; exact initial r hr
    · linarith [terminal r hr]
  · exact (initial r hr).trans_le (upper_monotone r (by norm_num) hx hx.1)
theorem diagonal_lower (r : Row) (hr : BRows r) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (9231/10000:ℝ)<HD r x :=
  ((initial r hr).trans_le (diagonal_initial r hr)).trans_le (HD_monotone r (by norm_num) hx hx.1)

theorem original (r : Row) (hr : BRows r) (upper : Bool) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : Primary r upper a b A B x) : (9231/10000:ℝ)<cost r upper a b A B x := by
  have hc := coefficient_bounds r
  have tr := positive_trig hx
  have hsource : source r≤(p r-4/5)*a-q r*b := by
    have hh := outer_circle_lower (X:=p r-4/5) (Y:= -q r) hs
    have he : (p r-4/5)^2+(-q r)^2=(4/5-p r)^2+q r^2 := by ring
    rw [he] at hh
    dsimp only [source]
    linarith
  have hY : 0≤t r-(4/5)*Real.cos x := by linarith [hc.2.2.2.2.1,Real.cos_le_one x]
  cases upper
  · have hd : direction false= -1 := by simp [direction,ShortWord.MixedQuarter.direction]
    have htarget := outer_endpoint_support (X:= -P r+(4/5)*Real.sin x)
      (Y:=t r-(4/5)*Real.cos x) ht hY
    rw [show -P r+(4/5)*Real.sin x+(t r-(4/5)*Real.cos x)=
      -P r+(4/5)*Real.sin x+t r-(4/5)*Real.cos x by ring] at htarget
    have hh := primary_support r false (lam:=4/5) (by norm_num) hm
      (S:=source r) (T:=min ((-P r+(4/5)*Real.sin x)*outerAxial)
        ((-P r+(4/5)*Real.sin x+t r-(4/5)*Real.cos x)*outerDiagonal))
      (by rw [B_sign hr]; linarith [hsource])
      (by rw [B_sign hr,hd]; linarith [htarget])
    have hang : angle false x=Real.pi/2-x := by
      simp only [angle,ShortWord.MixedQuarter.angle,hd]; ring
    rw [hang] at hh
    have hsplit := le_total ((-P r+(4/5)*Real.sin x)*outerAxial)
      ((-P r+(4/5)*Real.sin x+t r-(4/5)*Real.cos x)*outerDiagonal)
    rcases hsplit with hsplit|hsplit
    · rw [min_eq_left hsplit] at hh
      have hv := axial_lower r hr false hx
      simp only [HA,hang,hd,width] at hv hh
      linarith
    · rw [min_eq_right hsplit] at hh
      have hv := diagonal_lower r hr hx
      simp only [HD,width] at hv hh
      linarith
  · have hd : direction true=1 := by simp [direction,ShortWord.MixedQuarter.direction]
    have hX : -P r-(4/5)*Real.sin x≤0 := by linarith [hc.2.1,tr.2.2.1]
    have htarget := ShortWord.MixedQuarter.outer_axial_lower
      (X:= -P r-(4/5)*Real.sin x) (Y:=t r-(4/5)*Real.cos x) ht hX hY
    have hh := primary_support r true (lam:=4/5) (by norm_num) hm
      (S:=source r) (T:=(-P r-(4/5)*Real.sin x)*outerAxial)
      (by rw [B_sign hr]; linarith [hsource])
      (by rw [B_sign hr,hd]; linarith [htarget])
    have hv := axial_lower r hr true hx
    simp only [HA,width,hd] at hv hh
    linarith

end SquaresInCircles.Eight.TableFree.ShortOuterOne.EdgeFive.BPrimary
