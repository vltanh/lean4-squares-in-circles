module

public import SquaresInCircles.Eight.Arithmetic.WholeIntervalPolynomial
public import SquaresInCircles.Eight.Owners.Contact.MinimumDerivatives
public import SquaresInCircles.Eight.Owners.Stationary.TerminalWeights
public import SquaresInCircles.Eight.Stationary.System
public import SquaresInCircles.Eight.Words.Second.Mixed.Edge.ThreeAligned
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.ThreeAligned
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ZeroLReferences
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ZeroAsymmetric
public import SquaresInCircles.Eight.Words.Second.Outer.Same.ZeroCycle
public import SquaresInCircles.Eight.Words.Second.Outer.VBounds
public import SquaresInCircles.Eight.Words.Short.Mixed.Quarter
public import SquaresInCircles.Eight.Words.Short.Outer.One.OppositePrimaryUpperOneDiagonal
public import SquaresInCircles.Eight.Words.Short.Outer.One.OppositePrimaryUpperZero
public import SquaresInCircles.Eight.Words.Short.Outer.One.OppositeFiveLowerPrimaryReference
public import SquaresInCircles.Eight.Words.Short.Outer.One.SameSecondaryNegativeFirst
public import SquaresInCircles.Eight.Words.Short.Outer.One.SamePrimary
public import SquaresInCircles.Eight.Words.Short.Outer.One.OppositePrimaryNegativeGeometry
public import SquaresInCircles.Eight.Words.Short.WordZero

/-!
# Eight squares: all six opposite-primary owners of the short word

Each original primary axis is kept, including simultaneous owners (`original_owner`). Reflection
and reversal recover the axis-two owners with the exact label rule `(p,q,P,t) ↦ (-P,t,-p,q)`.
Both angle halves and the distinct edge-two threshold are preserved (`normalized`,
`actual_owner`).
-/

section
/-!
## All original positive-to-negative owners on roles five and four

On the lower half every original projection is bounded by the
same transverse sum. Its scalar has the stated Cauchy derivative bound.
The upper half and the role-four corollary use the original direct labels.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.EdgeFive.PositiveNegative
open CommonQuarter CorePairGeometry Arithmetic QuarterWordGeometry StationaryPrimitives
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
    dsimp [direction,ShortWord.MixedQuarter.direction,width] at hm ⊢ <;>
    norm_num at hm <;> linarith

theorem F_hasDerivAt (x : ℝ) : HasDerivAt F (Fd x) x := by
  have h1 : HasDerivAt (fun y => Real.pi/2-y+21108/100000-(18602/100000)*outerAxial) (-1) x :=
    (((hasDerivAt_id' x).const_sub (Real.pi/2)).add_const (21108/100000)).sub_const
      ((18602/100000)*outerAxial)
  have h2 : HasDerivAt (fun y => 1/2+Real.sin y/2+(1/2-outerAxial)*Real.cos y)
      (Real.cos x/2+(1/2-outerAxial)*(-Real.sin x)) x :=
    (((Real.hasDerivAt_sin x).div_const 2).const_add (1/2)).fun_add
      ((Real.hasDerivAt_cos x).const_mul (1/2-outerAxial))
  have h3 : HasDerivAt F
      (-1+80996/100000*(Real.cos x/2+(1/2-outerAxial)*(-Real.sin x))) x :=
    h1.fun_add (h2.const_mul (80996/100000))
  exact h3.congr_deriv (by simp only [Fd]; ring)
theorem Fd_negative (x : ℝ) : Fd x<0 := by
  have hh := axial_trig_upper x
  dsimp [Fd]
  linarith
theorem F_antitone : AntitoneOn F (Icc 0 (7/10)) :=
  antiOn_of_hasDeriv_nonpos
    (fun x _ => (F_hasDerivAt x).continuousAt.continuousWithinAt)
    (fun x _ => F_hasDerivAt x) (fun x _ => (Fd_negative x).le)

theorem endpoint : (459/500:ℝ)<F (7/10) := by
  let W := ((((halfPi.sub (Interval.point (7/10))).add (Interval.point (21108/100000))).sub
    ((Interval.point (18602/100000)).mul axial)).add
      ((Interval.point (80996/100000)).mul
        (((Interval.point (1/2)).add
          ((ShortWord.MixedQuarter.Reference.sine (by norm_num : (0:ℝ)≤7/10)).div
            (Interval.point 2) (by norm_num [Interval.point]))).add
            (((Interval.point (1/2)).sub axial).mul
              (ShortWord.MixedQuarter.Reference.cosine (by norm_num : (0:ℝ)≤7/10))))))
  have hh : (459/500:ℝ)<W.lo := by dsimp [W]; mixed_fixed
  exact hh.trans_le W.mem.1

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
    dsimp [F,width] at hf hsum
    dsimp [angle,direction,ShortWord.MixedQuarter.angle,ShortWord.MixedQuarter.direction]
    norm_num
    linarith [hs.1]
  · have ha := ShortOuterZero.fine_axial_bounds.2
    have hp := pi_hand_enclosure.1
    dsimp [angle,direction,ShortWord.MixedQuarter.angle,ShortWord.MixedQuarter.direction]
    norm_num
    linarith [hx.1,hs.1,ht.1]

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

end SquaresInCircles.Eight.ShortOuterOne.EdgeFive.PositiveNegative
end
end
end

section
/-!
## Both B tuples on the secondary angle halves

The unit multiplier gives two exact axial supports. The upper scalar increases
(`upper_monotone`); the lower scalar decreases (`lower_antitone`) because its one moving
trigonometric term `sweep` increases to a value below `.973` at the original angle cap
(`sweep_bounds`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.EdgeFive.BSecondary
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
    (fun _ hx => (sweepD_positive (Ioo_subset_Icc_self hx)).le)
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

end SquaresInCircles.Eight.ShortOuterOne.EdgeFive.BSecondary
end
end
end

section
/-!
## Both B tuples on the complete primary angle halves

The multiplier is exactly four fifths. The lower target keeps
both actual arc endpoints: its axial scalar is concave and its diagonal
scalar increases on the entire original angle half.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.EdgeFive.BPrimary
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
theorem diagonal_initial (r : Row) (_hr : BRows r) : HA r true 0≤HD r 0 := by
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

end SquaresInCircles.Eight.ShortOuterOne.EdgeFive.BPrimary
end
end
end

section
/-!
## Every original owner in the edge-five complement

The original ++ and -- owners are recovered by exact reversals of the adjacent states
(`same_original`); the +- owners and the role-four corollary keep their labels
(`complement_original`). Every weak separating-axis tie is included (`actual_owner`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.EdgeFive
open CommonQuarter CorePairGeometry Arithmetic QuarterWordGeometry

theorem secondary (r : Row) (upper : Bool) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : Secondary r upper a b A B x) : (8981/10000:ℝ)<cost r upper a b A B x := by
  have hr : ARows r∨BRows r := by fin_cases r <;> norm_num [ARows,BRows]
  rcases hr with hr|hr
  · exact ASecondary.original r hr upper hs ht hx hm
  · linarith [BSecondary.original r hr upper hs ht hx hm]
theorem primary (r : Row) (upper : Bool) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : Primary r upper a b A B x) : (8981/10000:ℝ)<cost r upper a b A B x := by
  have hr : ARows r∨BRows r := by fin_cases r <;> norm_num [ARows,BRows]
  rcases hr with hr|hr
  · linarith [APrimary.original r hr upper hs ht hx hm]
  · linarith [BPrimary.original r hr upper hs ht hx hm]
theorem normalized (r : Row) {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hφ : |φ-Real.pi/2|≤7/10)
    (j : Fin 4) (hj : j=0∨j=3)
    (hm : 0≤Eight.forwardMargin j a b A B (σ r) (σ r) φ) :
    (8981/10000:ℝ)<φ+c r+p r*a+σ r*q r*b-P r*A-σ r*t r*B := by
  obtain ⟨upper,x,hx,rfl⟩ := ShortWord.MixedQuarter.angle_cover hφ
  rcases hj with rfl|rfl
  · exact secondary r upper hs ht hx (secondary_margin r upper hx hm)
  · exact primary r upper hs ht hx (primary_margin r upper hx hm)

macro "short_edge_five_literal" : tactic => `(tactic|
  norm_num [wrongValue,WordProblems.shortCoefficients,WordProblems.radialIndex,
    WordProblems.signIndex,WordProblems.sign,next,c,p,q,P,t,σ,positive] at * <;> linarith)

theorem same_original (sgn : Bool) (j : Fin 4) {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hφ : |φ-Real.pi/2|≤7/10)
    (hm : 0≤Eight.forwardMargin j a b A B (WordProblems.sign sgn) (WordProblems.sign sgn) φ) :
    (8981/10000:ℝ)<φ+wrongValue .short 5 .outer sgn a b-
      wrongValue .short (next 5) .outer sgn A B := by
  cases sgn
  · fin_cases j
    · have hh := normalized 2 hs ht hφ 0 (Or.inl rfl)
        (by simpa [σ,positive,WordProblems.sign] using hm)
      short_edge_five_literal
    · have hh := normalized 1 ht hs hφ 3 (Or.inr rfl)
        (by simp [σ,positive,WordProblems.sign,Eight.forwardMargin] at hm ⊢; linarith)
      short_edge_five_literal
    · have hh := normalized 1 ht hs hφ 0 (Or.inl rfl)
        (by simp [σ,positive,WordProblems.sign,Eight.forwardMargin] at hm ⊢; linarith)
      short_edge_five_literal
    · have hh := normalized 2 hs ht hφ 3 (Or.inr rfl)
        (by simpa [σ,positive,WordProblems.sign] using hm)
      short_edge_five_literal
  · fin_cases j
    · have hh := normalized 0 hs ht hφ 0 (Or.inl rfl)
        (by simpa [σ,positive,WordProblems.sign] using hm)
      short_edge_five_literal
    · have hh := normalized 3 ht hs hφ 3 (Or.inr rfl)
        (by simp [σ,positive,WordProblems.sign,Eight.forwardMargin] at hm ⊢; linarith)
      short_edge_five_literal
    · have hh := normalized 3 ht hs hφ 0 (Or.inl rfl)
        (by simp [σ,positive,WordProblems.sign,Eight.forwardMargin] at hm ⊢; linarith)
      short_edge_five_literal
    · have hh := normalized 0 hs ht hφ 3 (Or.inr rfl)
        (by simpa [σ,positive,WordProblems.sign] using hm)
      short_edge_five_literal

def Complement (i : Vertex) (sgn target : Bool) : Prop :=
  (i=5 ∧ (sgn=target∨(sgn=true∧target=false)))∨(i=4∧sgn=true∧target=false)
theorem complement_original (i : Vertex) (sgn target : Bool)
    (hcase : Complement i sgn target) (j : Fin 4) {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hφ : |φ-Real.pi/2|≤7/10)
    (hm : 0≤Eight.forwardMargin j a b A B (WordProblems.sign sgn) (WordProblems.sign target) φ) :
    (8981/10000:ℝ)<φ+wrongValue .short i .outer sgn a b-
      wrongValue .short (next i) .outer target A B := by
  rcases hcase with ⟨rfl,hcase⟩|⟨rfl,rfl,rfl⟩
  · rcases hcase with rfl|⟨rfl,rfl⟩
    · exact same_original _ j hs ht hφ hm
    · have hh := PositiveNegative.original_five hs ht hφ j (by simpa [WordProblems.sign] using hm)
      linarith
  · linarith [PositiveNegative.original_four hs ht hφ]

theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (_hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .short)
    (i : Vertex) (hi : F.word hgap pi_lt_22_over_7 i=1)
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer)
    (hcase : Complement i (positiveOf C i) (positiveOf C (next i)))
    (j : Fin 4) (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    WordProblems.wrongGamma .short i<phaseValue F hgap i+wrongMarker C .short i-
      wrongMarker C .short (next i) := by
  have hφ : |phaseValue F hgap i-Real.pi/2|≤7/10 := by
    simpa [phaseValue,hi] using (difference_small F i).le
  have hsource : OuterState (C.a i) (C.b i) := by
    simpa only [State,hs,↓reduceIte] using actual_state C i
  have htarget : OuterState (C.a (next i)) (C.b (next i)) := by
    simpa only [State,ht,↓reduceIte] using actual_state C (next i)
  have hh := complement_original i (positiveOf C i) (positiveOf C (next i)) hcase j
    hsource htarget hφ (original_margin C F hgap i j howner)
  have hv : (8981/10000:ℝ)<phaseValue F hgap i+wrongMarker C .short i-
      wrongMarker C .short (next i) := by
    simpa only [wrongMarker,hs,ht] using hh
  have hΓ := ShortWord.Zero.threshold_le i
  linarith

end SquaresInCircles.Eight.ShortOuterOne.EdgeFive
end
end
end

section
/-!
## Every original lower-half opposite primary contact

Five
intrinsic rows use the two concave target endpoints. The sixth retains
its negative primary coefficient and proves the original axial support
criterion on the whole separator-forced angle interval. The result
keeps the actual original source and target states and weak owner.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.Opposite.Primary.Negative
open CommonQuarter CorePairGeometry Arithmetic WrongWordCircleSupport

theorem original_circle_support (r : Row) {a b : ℝ} (hs : OuterState a b) :
    S r≤(p r-weight r)*a-q r*b := by
  have hh := outer_circle_lower (X:=p r-weight r) (Y:=-(q r)) hs
  rw [show (-(q r))^2=(q r)^2 by ring] at hh
  dsimp [S]
  linarith

theorem positive_primary_axial {x : ℝ} (hx : x∈Icc 0 cap) :
    X 1 x<0 ∧ 0<(outerAxial+1/2)*Y 1 x-X 1 x/2 := by
  have tr := small_trig hx
  have hX : X 1 x<0 := by norm_num [X,P,weight]; linarith [tr.2.2]
  have hpos : 0<P 1-weight 1*Real.sin x := by dsimp [X] at hX; linarith
  have hr := mul_lt_mul_of_pos_right rho_bounds.1 hpos
  have hpositive : 0<Y 1 x-rho*X 1 x := by
    norm_num [X,Y,P,t,weight] at hr ⊢
    nlinarith [tr.1,tr.2.2]
  have hh := mul_pos
    (show 0<outerAxial+1/2 by linarith [outer_endpoint_bounds.1]) hpositive
  have hid : (outerAxial+1/2)*(Y 1 x-rho*X 1 x)=
      (outerAxial+1/2)*Y 1 x-X 1 x/2 := by
    calc
      (outerAxial+1/2)*(Y 1 x-rho*X 1 x)=
        (outerAxial+1/2)*Y 1 x-((outerAxial+1/2)*rho)*X 1 x := by ring
      _=(outerAxial+1/2)*Y 1 x-X 1 x/2 := by rw [rho_identity]; ring
  exact ⟨hX,hid ▸ hh⟩

theorem original (r : Row) {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10)) (hm : width x≤a-A*Real.sin x-B*Real.cos x) :
    threshold r<cost r false a b A B x := by
  have hx' : x∈Icc 0 cap := ⟨hx.1,(forced_cap hs ht hx hm).le⟩
  have hsource := original_circle_support r hs
  have hp := mul_le_mul_of_nonneg_left hm (weight_positive r).le
  by_cases hr : r=1
  · subst r
    have ha := positive_primary_axial hx'
    have htarget := outer_axial_lower ht ha.1.le ha.2.le
    have hv := axial_lower 1 hx'
    dsimp [X,Y,axialValue,width,cost,Unit.angle,Unit.direction] at htarget hp hv ⊢
    nlinarith only [hsource,hp,htarget,hv]
  have hX : 0≤X r x := by
    have hh := mul_nonneg (weight_positive r).le (small_trig hx').2.1
    dsimp [X]
    linarith [P_nonpositive r hr]
  by_cases hmin : X r x*outerAxial≤(X r x+Y r x)*outerDiagonal
  · have htarget := outer_concave_lower ht hX le_rfl hmin
    have hv := axial_lower r hx'
    dsimp [X,Y,axialValue,width,cost,Unit.angle,Unit.direction] at htarget hp hv ⊢
    nlinarith only [hsource,hp,htarget,hv]
  · have htarget := outer_concave_lower ht hX (lt_of_not_ge hmin).le le_rfl
    have hv := diagonal_lower r hr hx'
    dsimp [X,Y,diagonalValue,width,cost,Unit.angle,Unit.direction] at htarget hp hv ⊢
    nlinarith only [hsource,hp,htarget,hv]

end SquaresInCircles.Eight.ShortOuterOne.Opposite.Primary.Negative
end
end
end

section
/-!
## The exceptional upper primary owner's early contact minimum

The complete physical region before the unique stationary-angle event
is compact. Axial, initial-angle and terminal-angle boundaries have
their proved values; the source-axis boundary has a feasible descending
direction. An interior minimum would have a zero target derivative and
a strictly positive angle derivative, which is impossible.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace SquaresInCircles.Eight.ShortOuterOne.Opposite.Primary.Upper.Minimum
open CommonQuarter CorePairGeometry Arithmetic
open SameContact (arc ratio)

theorem source_strict_lower {B e x : ℝ} (he : Upper.IsEvent e)
    (hB : B∈Icc 0 outerDiagonal) (hx : x∈Icc 0 e) (hxe : x<e) :
    outerDiagonal<contact B x := by
  have hx' := (before_domain he hx).2.1
  have hh := ShortOuterZero.Same.Event.zero_decrease hx' (event_bounds he).2.2 hx.2
  have hh' : (69/100)*(e-x)≤contact 0 x-contact 0 e := by
    simpa [ShortOuterZero.Same.contact] using hh
  have he2 : contact 0 e=outerDiagonal := he.2
  rw [he2] at hh'
  have hmono := (contact_strictMono hx').monotoneOn zero_mem hB hB.1
  have hp : 0<(69/100:ℝ)*(e-x) := mul_pos (by norm_num) (sub_pos.mpr hxe)
  linarith

theorem target_diagonal_infeasible {e x : ℝ} (he : Upper.IsEvent e) (hx : x∈Icc 0 e) :
    outerAxial<contact outerDiagonal x := by
  have hc := early_cos he hx
  have hs := axial_bounds he hx
  have hd := ShortMixedZero.fine_diagonal_bounds
  have hp := mul_lt_mul''
    (show (1399/1000:ℝ)<outerDiagonal+1/2 by linarith) hc (by norm_num) (by norm_num)
  have hm := mul_le_mul
    (show outerDiagonal-1/2≤(2/5:ℝ) by linarith) hs.2.2.2.2.2.2.2.le
      hs.2.2.2.2.2.2.1 (by norm_num)
  dsimp [contact,SecondWord.SameZero.b]
  rw [SameContact.arc_diagonal]
  linarith [ShortOuterZero.fine_axial_bounds.2]

theorem target_strict {B e x : ℝ} (he : Upper.IsEvent e) (hd : Domain B x) (hx : x≤e) :
    B<outerDiagonal := by
  apply lt_of_le_of_ne hd.1.2
  intro heq
  subst B
  exact (not_lt_of_ge hd.2.2.2) (target_diagonal_infeasible he ⟨hd.2.1.1,hx⟩)

theorem source_axial_first {B e x : ℝ} (he : Upper.IsEvent e) (hd : Domain B x)
    (hx : x≤e) (ha : contact B x=outerAxial) : 0<first 1 B x := by
  have hL : (173/50:ℝ)<sourceD 1 (contact B x) := by
    rw [ha,sourceD,ratio,SameContact.arc_axial]
    norm_num [p,q]
    linarith [ShortOuterZero.fine_axial_bounds.1]
  have hc := early_cos he ⟨hd.2.1.1,hx⟩
  have hk := stateSpeed_lower hd.1 hd.2.1
  have hp := mul_lt_mul'' hL (hc.trans_le hk) (by norm_num) (by norm_num)
  have hr : 0≤ratio B := (SameContact.ratio_pos (SameContact.outer_domain hd.1)).le
  norm_num [first,P,t]
  nlinarith

theorem minimum_not_source_axial {B e s x : ℝ} (he : Upper.IsEvent e)
    (hs : Stationary.IsEvent s) (hd : Domain B x) (hx : x≤ s) (hB : 0<B)
    (ha : contact B x=outerAxial)
    (hmin : ∀D y,Domain D y → y≤ s → value 1 B x≤value 1 D y) : False := by
  have hxe : x≤e := by linarith [hs.1.2,(event_bounds he).1]
  have hzero := before_domain he ⟨hd.2.1.1,hxe⟩
  have hdom {D : ℝ} (hD : D∈Icc 0 B) : Domain D x := between_domain hzero hd hD
  have hnecessary := ContactMinimumDerivatives.right_endpoint hB
    (first_target_hasDerivAt 1 hd).continuousAt
    (fun D hD => value_target_hasDerivAt 1 (hdom hD))
    (fun D hD => hmin D x (hdom hD) hx)
  exact (not_lt_of_ge hnecessary) (source_axial_first he hd hxe ha)

theorem interior_not_minimum {B e s x : ℝ} (he : Upper.IsEvent e)
    (hs : Stationary.IsEvent s) (hd : Domain B x)
    (hB : B∈Ioo 0 outerDiagonal) (hx : x∈Ioo 0 s)
    (ha : contact B x∈Ioo outerDiagonal outerAxial)
    (hmin : ∀D y,Domain D y → y≤ s → value 1 B x≤value 1 D y) : False := by
  let OT : Set ℝ := Ioo 0 outerDiagonal ∩ (fun D => contact D x) ⁻¹' Ioo outerDiagonal outerAxial
  have hCT : Continuous (fun D => contact D x) := by
    dsimp [contact,SecondWord.SameZero.b,arc]
    fun_prop
  have hOT : IsOpen OT := isOpen_Ioo.inter (isOpen_Ioo.preimage hCT)
  have hmemT : B∈OT := ⟨hB,ha⟩
  have hlocalT : IsLocalMin (fun D => value 1 D x) B := by
    filter_upwards [hOT.mem_nhds hmemT] with D hD
    exact hmin D x ⟨Ioo_subset_Icc_self hD.1,hd.2.1,Ioo_subset_Icc_self hD.2⟩ hx.2.le
  have htarget : first 1 B x=0 := hlocalT.hasDerivAt_eq_zero (value_target_hasDerivAt 1 hd)
  let OA : Set ℝ := Ioo 0 s ∩ (contact B) ⁻¹' Ioo outerDiagonal outerAxial
  have hCA : Continuous (contact B) := continuous_iff_continuousAt.2
    fun y => (SecondWord.SameZero.b_angle_hasDerivAt B y).continuousAt
  have hOA : IsOpen OA := isOpen_Ioo.inter (isOpen_Ioo.preimage hCA)
  have hmemA : x∈OA := ⟨hx,ha⟩
  have hlocalA : IsLocalMin (value 1 B) x := by
    filter_upwards [hOA.mem_nhds hmemA] with y hy
    have hy' : y∈Icc 0 (7/10) := ⟨hy.1.1.le,by linarith [hy.1.2,hs.1.2]⟩
    exact hmin B y ⟨hd.1,hy',Ioo_subset_Icc_self hy.2⟩ hy.1.2.le
  have hangle : angleFirst 1 B x=0 := hlocalA.hasDerivAt_eq_zero (value_angle_hasDerivAt 1 hd)
  have hlower := Stationary.stationary_angle_lower he hd
    (show x≤e by linarith [hx.2,hs.1.2,(event_bounds he).1]) htarget
  have hpositive := Stationary.positive_before hs hx.1.le hx.2
  linarith

theorem minimum_lower {B e s x : ℝ} (he : Upper.IsEvent e) (hs : Stationary.IsEvent s)
    (hd : Domain B x) (hx : x≤ s)
    (hmin : ∀D y,Domain D y → y≤ s → value 1 B x≤value 1 D y) :
    (4489/5000:ℝ)<value 1 B x := by
  have hxe : x<e := by linarith [hx,hs.1.2,(event_bounds he).1]
  have hxearly : x∈Icc 0 e := ⟨hd.2.1.1,hxe.le⟩
  by_cases hfinal : x=s
  · subst x
    exact before_one_after_nine he hd ⟨hs.1.1.le,by linarith [hs.1.2,(event_bounds he).1]⟩
  by_cases hzero : B=0
  · subst B
    exact F_one_lower he hxearly
  have hB : 0<B := lt_of_le_of_ne hd.1.1 (Ne.symm hzero)
  by_cases hinitial : x=0
  · subst x
    have hD := before_domain he (show (0:ℝ)∈Icc 0 e from
      ⟨le_rfl,by linarith [(event_bounds he).1]⟩)
    have hm := endpoint_minimum 1 hD hd hd.1.1
      ((show (0:ℝ)<1/20 by norm_num).trans Reference.initial_H_one).le
    have hf := F_one_lower he (show (0:ℝ)∈Icc 0 e from
      ⟨le_rfl,by linarith [(event_bounds he).1]⟩)
    exact hf.trans_le hm
  by_cases haxis : contact B x=outerAxial
  · exact (minimum_not_source_axial he hs hd hx hB haxis hmin).elim
  have hsource : contact B x∈Ioo outerDiagonal outerAxial :=
    ⟨source_strict_lower he hd.1 hxearly hxe,lt_of_le_of_ne hd.2.2.2 haxis⟩
  have htarget : B∈Ioo 0 outerDiagonal := ⟨hB,target_strict he hd hxe.le⟩
  have hangle : x∈Ioo 0 s :=
    ⟨lt_of_le_of_ne hd.2.1.1 (Ne.symm hinitial),lt_of_le_of_ne hx hfinal⟩
  exact (interior_not_minimum he hs hd htarget hangle hsource hmin).elim

theorem early_contact {B e s x : ℝ} (he : Upper.IsEvent e) (hs : Stationary.IsEvent s)
    (hd : Domain B x) (hx : x≤ s) : (4489/5000:ℝ)<value 1 B x := by
  let guard : ℝ×ℝ→ℝ := fun p => outerAxial-contact p.1 p.2
  let objective : ℝ×ℝ→ℝ := fun p => value 1 p.1 p.2
  have hg : Continuous guard := by dsimp [guard,contact,SecondWord.SameZero.b,arc]; fun_prop
  have hf : Continuous objective := by
    dsimp [objective,value,source,target,contact,SecondWord.SameZero.b,arc]
    fun_prop
  obtain ⟨m,hm,hbetter,hmin⟩ := contact_region_minimum hg hf
    (p₀:=(B,x)) ⟨hd.1,⟨hd.2.1.1,hx⟩,sub_nonneg.mpr hd.2.2.2⟩
  have hme : m.2<e := by linarith [hm.2.1.2,hs.1.2,(event_bounds he).1]
  have hmd : Domain m.1 m.2 :=
    ⟨hm.1,⟨hm.2.1.1,by linarith [hm.2.1.2,hs.1.2]⟩,
      (source_strict_lower he hm.1 ⟨hm.2.1.1,hme.le⟩ hme).le,sub_nonneg.mp hm.2.2⟩
  have hlower := minimum_lower he hs hmd hm.2.1.2
    (fun D y hDy hy => hmin (D,y) hDy.1 ⟨hDy.2.1.1,hy⟩ (sub_nonneg.mpr hDy.2.2.2))
  exact hlower.trans_le hbetter

theorem one_contact {B x : ℝ} (hd : Domain B x) : (4489/5000:ℝ)<value 1 B x := by
  obtain ⟨e,he⟩ := Upper.exists_event
  obtain ⟨s,hs⟩ := Stationary.exists_event
  by_cases hafter : e≤x
  · exact OneDiagonal.after_contact he hd hafter
  by_cases hearly : x≤ s
  · exact early_contact he hs hd hearly
  · exact before_one_after_nine he hd
      ⟨by linarith [hs.1.1],(lt_of_not_ge hafter).le⟩

end SquaresInCircles.Eight.ShortOuterOne.Opposite.Primary.Upper.Minimum
end
end
end

section
/-!
## All six original opposite-primary upper angle halves

The full contact region, its axial/diagonal junction and its possible
interior state minimum are covered before the original weak separator
is restored. No state or angle boundary hypothesis remains.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.Opposite.Primary.Upper
open CommonQuarter CorePairGeometry Arithmetic

theorem contact_lower (r : Row) {B x : ℝ} (hd : Domain B x) :
    (4489/5000:ℝ)<value r B x := by
  fin_cases r
  · have hh := zero_contact hd
    exact lt_trans (by norm_num) hh
  · exact Minimum.one_contact hd
  · exact simple_contact 2 (Or.inl rfl) hd
  · exact simple_contact 3 (Or.inr (Or.inl rfl)) hd
  · exact simple_contact 4 (Or.inr (Or.inr (Or.inl rfl))) hd
  · exact simple_contact 5 (Or.inr (Or.inr (Or.inr rfl))) hd

theorem original (r : Row) {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10)) (hm : width x≤a+A*Real.sin x-B*Real.cos x) :
    threshold r<cost r true a b A B x := by
  obtain ⟨D,hD,hbetter⟩ := original_to_contact r hs ht hx hm
  have hh := (contact_lower r hD).trans_le hbetter
  have hthreshold : threshold r<(4489/5000:ℝ) := by
    fin_cases r <;> norm_num [threshold]
  exact hthreshold.trans hh

end SquaresInCircles.Eight.ShortOuterOne.Opposite.Primary.Upper
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.Opposite.Primary
open CommonQuarter CorePairGeometry Arithmetic QuarterWordGeometry

theorem normalized (r : Row) {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (hm : 0≤Eight.forwardMargin 3 a b A B (-1) 1 φ) :
    threshold r<φ+c r+p r*a-q r*b-P r*A-t r*B := by
  obtain ⟨high,x,hx,rfl⟩ := Unit.angle_cover hφ
  have hm' := normalized_margin high hx hm
  cases high
  · have hh := Negative.original r hs ht hx (by
      simp only [Unit.direction,Bool.false_eq_true,ite_false] at hm'
      linarith)
    simpa [cost] using hh
  · have hh := Upper.original r hs ht hx (by simpa [Unit.direction] using hm')
    simpa [cost] using hh

def OriginalOwner (i : Vertex) (j : Fin 4) : Prop :=
  (i=2∨i=4∨i=6) ∧ (j=1∨j=3)

theorem original_owner (i : Vertex) (j : Fin 4) (hrole : OriginalOwner i j)
    {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (hm : 0≤Eight.forwardMargin j a b A B (-1) 1 φ) :
    (WordProblems.wrongGamma .short i:ℝ)<φ+wrongValue .short i .outer false a b-
      wrongValue .short (next i) .outer true A B := by
  rcases hrole with ⟨hi,hj⟩
  rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl
  · have hh := normalized 0 ht hs hφ (by simpa [Eight.forwardMargin,
      sub_eq_add_neg,add_comm,add_left_comm,add_assoc] using hm)
    norm_num [wrongValue,WordProblems.shortCoefficients,WordProblems.radialIndex,
      WordProblems.signIndex,WordProblems.sign,WordProblems.wrongGamma,next,
      threshold,c,p,q,P,t] at *
    linarith
  · have hh := normalized 1 hs ht hφ hm
    norm_num [wrongValue,WordProblems.shortCoefficients,WordProblems.radialIndex,
      WordProblems.signIndex,WordProblems.sign,WordProblems.wrongGamma,next,
      threshold,c,p,q,P,t] at *
    linarith
  · have hh := normalized 2 ht hs hφ (by simpa [Eight.forwardMargin,
      sub_eq_add_neg,add_comm,add_left_comm,add_assoc] using hm)
    norm_num [wrongValue,WordProblems.shortCoefficients,WordProblems.radialIndex,
      WordProblems.signIndex,WordProblems.sign,WordProblems.wrongGamma,next,
      threshold,c,p,q,P,t] at *
    linarith
  · have hh := normalized 3 hs ht hφ hm
    norm_num [wrongValue,WordProblems.shortCoefficients,WordProblems.radialIndex,
      WordProblems.signIndex,WordProblems.sign,WordProblems.wrongGamma,next,
      threshold,c,p,q,P,t] at *
    linarith
  · have hh := normalized 4 ht hs hφ (by simpa [Eight.forwardMargin,
      sub_eq_add_neg,add_comm,add_left_comm,add_assoc] using hm)
    norm_num [wrongValue,WordProblems.shortCoefficients,WordProblems.radialIndex,
      WordProblems.signIndex,WordProblems.sign,WordProblems.wrongGamma,next,
      threshold,c,p,q,P,t] at *
    linarith
  · have hh := normalized 5 hs ht hφ hm
    norm_num [wrongValue,WordProblems.shortCoefficients,WordProblems.radialIndex,
      WordProblems.signIndex,WordProblems.sign,WordProblems.wrongGamma,next,
      threshold,c,p,q,P,t] at *
    linarith

theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (_hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .short)
    (i : Vertex) (hi : F.word hgap pi_lt_22_over_7 i=1)
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer)
    (hσ : positiveOf C i=false) (hτ : positiveOf C (next i)=true) (j : Fin 4)
    (hrole : OriginalOwner i j)
    (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    WordProblems.wrongGamma .short i<phaseValue F hgap i+wrongMarker C .short i-
      wrongMarker C .short (next i) := by
  have he : phaseValue F hgap i-Real.pi/2=difference F i := by
    simp [phaseValue,hi]
  have hφ : |phaseValue F hgap i-Real.pi/2|≤7/10 := by
    rw [he]
    exact (difference_small F i).le
  have hsource : OuterState (C.a i) (C.b i) := by
    simpa [State,hs] using actual_state C i
  have htarget : OuterState (C.a (next i)) (C.b (next i)) := by
    simpa [State,ht] using actual_state C (next i)
  have hm := original_margin C F hgap i j howner
  simp only [hσ,hτ,WordProblems.sign,Bool.false_eq_true,ite_false,ite_true,
    Rat.cast_neg,Rat.cast_one] at hm
  have hh := original_owner i j hrole hsource htarget hφ hm
  simpa only [wrongMarker,hs,ht,hσ,hτ] using hh

end SquaresInCircles.Eight.ShortOuterOne.Opposite.Primary
end
end
end
