module

public import SquaresInCircles.Eight.Words.Common.QuarterState
public import SquaresInCircles.Eight.Owners.Zero.LowScalar

/-!
# Eight squares: full-interval scalar reserves for the high-EH/low-GA path

The negative rotated endpoint is controlled directly by positive
squaring.  Its degree-twelve reserve has a positive constant and a
positive linear remainder after all negative higher powers are charged
on the whole interval.  The remaining error costs have explicit linear
minorants, obtained from their global concavity and intrinsic endpoints.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalEH

abbrev lam : ℝ := 13/10
abbrev eta : ℝ := 2/5
abbrev mass : ℝ := 111/100
abbrev primaryLower : ℝ := 447/800
abbrev endpointCap : ℝ := 20467/10000
abbrev pathBase : ℝ := 294819/100000
abbrev axialLower : ℝ := 141457/100000

def rotatedNorm (z : ℝ) : ℝ :=
  Real.sqrt ((eta+lam*Real.cos z)^2+(mass-lam*Real.sin z)^2)

def rotatedThreshold (z : ℝ) : ℝ :=
  endpointCap+eta*axialLower+(eta+mass)/2-lam/2+lam*Real.cos z-(109/100)*z

def thresholdLower (z : ℝ) : ℝ :=
  endpointCap+eta*axialLower+(eta+mass)/2-lam/2+
    lam*(1-z^2/2+z^4/24-z^6/720)-(109/100)*z

def normUpperSquare (z : ℝ) : ℝ :=
  eta^2+mass^2+lam^2+
    2*lam*(eta*(1-z^2/2+z^4/24)-mass*(z-z^3/6+z^5/120-z^7/5040))

def rotatedReserve (z : ℝ) : ℝ := (thresholdLower z)^2-Q0*normUpperSquare z

theorem rotatedReserve_identity (z : ℝ) :
    rotatedReserve z=
      8904/244140625+(993051/390625)*z-(1249109/625000)*z^2-
      (1166009/2500000)*z^3+(3440281/5000000)*z^4-
      (3586973/150000000)*z^5-(12738661/150000000)*z^6+
      (10671973/6300000000)*z^7+(169/32000)*z^8-
      (169/864000)*z^10+(169/51840000)*z^12 := by
  dsimp [rotatedReserve,thresholdLower,normUpperSquare,endpointCap,eta,axialLower,
    mass,lam,Q0]
  ring

theorem rotatedReserve_positive {z : ℝ} (hz : z∈Icc 0 frameCap) :
    0<rotatedReserve z := by
  have hp (n : ℕ) : z^(n+1)≤(7/10:ℝ)^n*z := by
    have hh := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hz.1 (show z≤7/10 from hz.2) n) hz.1
    simpa only [pow_succ] using hh
  have h2 := hp 1
  have h3 := hp 2
  have h5 := hp 4
  have h6 := hp 5
  have h10 := hp 9
  norm_num at h2 h3 h5 h6 h10
  rw [rotatedReserve_identity]
  nlinarith only [h2,h3,h5,h6,h10,pow_nonneg hz.1 4,pow_nonneg hz.1 7,
    pow_nonneg hz.1 8,pow_nonneg hz.1 12,hz.1]

theorem rotatedNorm_sq (z : ℝ) :
    (rotatedNorm z)^2=eta^2+mass^2+lam^2+
      2*lam*(eta*Real.cos z-mass*Real.sin z) := by
  have hh := Real.sq_sqrt (show 0≤(eta+lam*Real.cos z)^2+
    (mass-lam*Real.sin z)^2 by positivity)
  dsimp [rotatedNorm]
  nlinarith [congrArg (fun r : ℝ => lam^2*r) (Real.sin_sq_add_cos_sq z)]

theorem thresholdLower_positive {z : ℝ} (hz : z∈Icc 0 frameCap) :
    0<thresholdLower z := by
  have hc := GlobalZeroLow.cosine6_nonneg hz
  change 0≤1-z^2/2+z^4/24-z^6/720 at hc
  dsimp [thresholdLower,endpointCap,eta,axialLower,mass,lam]
  dsimp [frameCap] at hz
  linarith [hz.2]

/-- This is the complete `.09` negative-rotation deletion estimate,
including zero and the full endpoint `7/10`. -/
theorem rotated_radical_bound {z : ℝ} (hz : z∈Icc 0 frameCap) :
    CommonQuarter.radius*rotatedNorm z<rotatedThreshold z := by
  have hc6 := cos_lower_six hz.1
  have hc4 := cos_upper_four hz.1
  have hs7 := sin_lower_seven hz.1
  have hnorm := rotatedNorm_sq z
  have hupper : (rotatedNorm z)^2≤normUpperSquare z := by
    dsimp [normUpperSquare,eta,mass,lam] at *
    linarith
  have hthreshold : thresholdLower z≤rotatedThreshold z := by
    dsimp [thresholdLower,rotatedThreshold,lam]
    linarith
  have hreserve := rotatedReserve_positive hz
  have hR := CommonQuarter.radius_sq
  have hQ : 0≤Q0 := by norm_num [Q0]
  have hproduct := mul_le_mul_of_nonneg_left hupper hQ
  have hsq : (CommonQuarter.radius*rotatedNorm z)^2=
      Q0*(rotatedNorm z)^2 := by rw [mul_pow,hR]
  have hsmall : CommonQuarter.radius*rotatedNorm z<thresholdLower z := by
    have hpositive := thresholdLower_positive hz
    dsimp [rotatedReserve] at hreserve
    nlinarith
  exact hsmall.trans_le hthreshold

def positiveCost (x : ℝ) : ℝ :=
  x+lam*Real.sin x-2*lam*CommonQuarter.radius*Real.sin (x/2)

def negativeCost (x : ℝ) : ℝ :=
  -x+lam*((primaryLower+1/2)*Real.sin x-(1/2)*(1-Real.cos x))

def positiveDerivative (x : ℝ) : ℝ :=
  1+lam*Real.cos x-lam*CommonQuarter.radius*Real.cos (x/2)

def positiveSecond (x : ℝ) : ℝ :=
  -lam*Real.sin x+(lam*CommonQuarter.radius/2)*Real.sin (x/2)

def negativeDerivative (x : ℝ) : ℝ :=
  -1+lam*((primaryLower+1/2)*Real.cos x-(1/2)*Real.sin x)

def negativeSecond (x : ℝ) : ℝ :=
  -lam*((primaryLower+1/2)*Real.sin x+(1/2)*Real.cos x)

theorem positiveCost_derivative (x : ℝ) : HasDerivAt positiveCost (positiveDerivative x) x := by
  convert (((hasDerivAt_id x).add ((Real.hasDerivAt_sin x).const_mul lam)).sub
    ((((hasDerivAt_id x).div_const 2).sin).const_mul
      (2*lam*CommonQuarter.radius))) using 1
  · rfl
  · dsimp [positiveDerivative]
    ring

theorem positiveCost_second (x : ℝ) : HasDerivAt positiveDerivative (positiveSecond x) x := by
  convert (((hasDerivAt_const x 1).add ((Real.hasDerivAt_cos x).const_mul lam)).sub
    ((((hasDerivAt_id x).div_const 2).cos).const_mul
      (lam*CommonQuarter.radius))) using 1
  · rfl
  · dsimp [positiveSecond]
    ring

theorem negativeCost_derivative (x : ℝ) : HasDerivAt negativeCost (negativeDerivative x) x := by
  convert (hasDerivAt_id x).neg.add
    ((((Real.hasDerivAt_sin x).const_mul (primaryLower+1/2)).sub
      (((hasDerivAt_const x 1).sub (Real.hasDerivAt_cos x)).const_mul (1/2))).const_mul lam)
    using 1
  · rfl
  · dsimp [negativeDerivative]
    ring

theorem negativeCost_second (x : ℝ) : HasDerivAt negativeDerivative (negativeSecond x) x := by
  convert (hasDerivAt_const x (-1)).add
    ((((Real.hasDerivAt_cos x).const_mul (primaryLower+1/2)).sub
      ((Real.hasDerivAt_sin x).const_mul (1/2))).const_mul lam) using 1
  · rfl
  · dsimp [negativeSecond]
    ring

theorem positiveCost_concave : ConcaveOn ℝ (Icc 0 frameCap) positiveCost := by
  apply concave_of_deriv2 (fun x _ => positiveCost_derivative x)
    (fun x _ => positiveCost_second x)
  intro x hx
  have hh : x/2∈Icc 0 frameCap := by
    simp only [frameCap,mem_Icc] at hx ⊢
    constructor <;> linarith [hx.1,hx.2]
  have tr := transport_trig hh
  have hcoef : CommonQuarter.radius/2-2*Real.cos (x/2)≤0 := by
    linarith [CommonQuarter.radius_bounds.2,tr.1]
  have hp := mul_nonpos_of_nonneg_of_nonpos tr.2.2.1 hcoef
  have hs : Real.sin x=2*Real.sin (x/2)*Real.cos (x/2) := by
    have hh := Real.sin_two_mul (x/2)
    rwa [show 2*(x/2)=x by ring] at hh
  dsimp [positiveSecond,lam]
  rw [hs]
  nlinarith only [hp]

theorem negativeCost_concave : ConcaveOn ℝ (Icc 0 frameCap) negativeCost := by
  apply concave_of_deriv2 (fun x _ => negativeCost_derivative x)
    (fun x _ => negativeCost_second x)
  intro x hx
  have tr := transport_trig hx
  dsimp [negativeSecond,lam,primaryLower]
  linarith [tr.1,tr.2.2.1]

private theorem concave_linear_lower {f : ℝ→ℝ} {c : ℝ}
    (hf : ConcaveOn ℝ (Icc 0 frameCap) f) (hzero : f 0=0)
    (hend : c*frameCap<f frameCap) {x : ℝ} (hx : x∈Icc 0 frameCap) : c*x≤f x := by
  have hcap : 0<frameCap := by norm_num [frameCap]
  let t := x/frameCap
  have ht0 : 0≤t := div_nonneg hx.1 hcap.le
  have ht1 : t≤1 := (div_le_one hcap).2 hx.2
  have hid : t*frameCap=x := by
    dsimp [t]
    field_simp
  have hh := hf.2 (show (0:ℝ)∈Icc 0 frameCap by exact ⟨le_rfl,hcap.le⟩)
    (show frameCap∈Icc 0 frameCap by exact ⟨hcap.le,le_rfl⟩)
    (sub_nonneg.mpr ht1) ht0 (by ring)
  simp only [smul_eq_mul,hzero,mul_zero,zero_add,hid] at hh
  have hp := mul_le_mul_of_nonneg_left hend.le ht0
  have ht : t*(c*frameCap)=c*x := by
    rw [← hid]
    ring
  rw [ht] at hp
  exact hp.trans hh

theorem positiveCost_lower {x : ℝ} (hx : x∈Icc 0 frameCap) :
    -(327/1000)*x≤positiveCost x := by
  apply concave_linear_lower positiveCost_concave (by norm_num [positiveCost]) _ hx
  have hs := sin_lower_seven (show 0≤frameCap by norm_num [frameCap])
  have hh := sin_upper_five (show 0≤frameCap/2 by norm_num [frameCap])
  have ht := transport_trig (show frameCap/2∈Icc 0 frameCap by norm_num [frameCap])
  have hp := mul_le_mul CommonQuarter.radius_bounds.2.le hh ht.2.2.1
    (by norm_num : (0:ℝ)≤1979/1000)
  dsimp [positiveCost,frameCap,lam]
  norm_num [frameCap] at hs hp
  linarith

theorem negativeCost_lower {x : ℝ} (hx : x∈Icc 0 frameCap) :
    (47/1000)*x≤negativeCost x := by
  apply concave_linear_lower negativeCost_concave (by norm_num [negativeCost]) _ hx
  have hs := sin_lower_seven (show 0≤frameCap by norm_num [frameCap])
  have hc := cos_lower_six (show 0≤frameCap by norm_num [frameCap])
  dsimp [negativeCost,frameCap,lam,primaryLower]
  norm_num [frameCap] at hs hc
  linarith

theorem augmentation_lower {x : ℝ} (hx : x∈Icc 0 frameCap) :
    (52/1000)*x≤(9/50)*frameCost x := by
  have hc : ConcaveOn ℝ (Icc 0 frameCap) (fun x => (9/50)*frameCost x) := by
    apply concave_of_deriv2
      (f' := fun x => (9/100)*(Real.cos x-Real.sin x))
      (f'' := fun x => -(9/100)*(Real.sin x+Real.cos x))
    · intro x _
      have h := ((((Real.hasDerivAt_cos x).fun_add (Real.hasDerivAt_sin x)).sub_const 1).div_const
        2).const_mul (9/50:ℝ)
      unfold frameCost
      exact h.congr_deriv (by ring)
    · intro x _
      have h := ((Real.hasDerivAt_cos x).fun_sub (Real.hasDerivAt_sin x)).const_mul (9/100:ℝ)
      exact h.congr_deriv (by ring)
    · intro x hx
      have hh := transport_trig hx
      linarith [hh.1,hh.2.2.1]
  apply concave_linear_lower hc (by norm_num [frameCost]) _ hx
  have hs := sin_lower_seven (show 0≤frameCap by norm_num [frameCap])
  have hcos := cos_lower_six (show 0≤frameCap by norm_num [frameCap])
  show (52/1000:ℝ)*frameCap<9/50*frameCost frameCap
  simp only [frameCost,frameCap] at hs hcos ⊢
  norm_num at hs hcos
  linarith

theorem two_cost_reserve {x z : ℝ} (hx : x∈Icc 0 frameCap) (hz : z∈Icc 0 frameCap) :
    11/4<pathBase+positiveCost x+negativeCost z+(9/50)*frameCost |x-z| := by
  have hdiff : |x-z|∈Icc 0 frameCap :=
    ⟨abs_nonneg _,abs_le.2 ⟨by linarith [hx.1,hz.2],by linarith [hx.2,hz.1]⟩⟩
  have hf := positiveCost_lower hx
  have hd := negativeCost_lower hz
  have hh := augmentation_lower hdiff
  by_cases hxz : z≤x
  · rw [abs_of_nonneg (sub_nonneg.mpr hxz)] at hh ⊢
    dsimp [pathBase,frameCap] at *
    linarith [hx.1,hx.2,hz.1,hz.2]
  · rw [abs_of_neg (sub_neg.mpr (lt_of_not_ge hxz))] at hh ⊢
    dsimp [pathBase,frameCap] at *
    linarith [hx.1,hx.2,hz.1,hz.2]

end SquaresInCircles.Eight.GlobalEH
