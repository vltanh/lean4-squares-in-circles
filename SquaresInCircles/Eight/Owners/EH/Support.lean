module

public import SquaresInCircles.Eight.Owners.Zero.LowDomain
public import SquaresInCircles.Eight.Words.Common.QuarterState

/-!
# Eight squares: endpoint and error supports on the EH–HG–GA path

Every support uses the shifted corner disk and the common marker: the endpoint support
`unsigned s + lam * s.a < endpointCap` (`endpoint_support`), the base of the path (`path_base`),
and the costs of the primary and zero errors (`primaryError_positive`, `zeroError_positive`).
Outer rotated endpoints and a negative primary on the flat core are told apart by their feasible
axes; a weak witness of a low owner gives a `LowReduction` (`low_reduction`).
-/

section
/-!
## Full-interval scalar reserves for the high-EH/low-GA path

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
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalEH

open FramePair ZeroPrimary GlobalZeroSign GlobalQuarterSign GlobalOuterAnchor

theorem endpoint_support (s : State) : unsigned s+lam*s.a<endpointCap := by
  by_cases hcore : s.branch.type=0
  · have ha := (core_bounds s hcore).1
    have hb := s.canonical.trans ha
    have hlo := primary_lower s
    have hb0 : 0≤ s.b := (coordinates s).2.2.1
    have hmarker : unsigned s≤8*(7/12-s.a)+(11/10)*s.b := by
      cases hbr : s.branch <;> simp [hbr,Branch.type] at hcore
      all_goals
        dsimp [unsigned]
        rw [hbr]
        dsimp [FramePair.label]
        nlinarith [s.b_nonneg]
    have hc := s.canonical
    simp only [lam,endpointCap]
    linarith
  · have hm := (outer_marker_bounds s hcore).2
    obtain ⟨n,hndef⟩ : ∃ n, n=Real.sqrt ((lam+eta)^2+mass^2) := ⟨_,rfl⟩
    have hs : (lam+eta)*s.a+mass*s.b≤CommonQuarter.radius*n-(lam+eta+mass)/2 := by
      rw [hndef]; exact state_support s (lam+eta) mass
    have hn : n^2=(lam+eta)^2+mass^2 := by rw [hndef]; exact Real.sq_sqrt (by positivity)
    have hR := CommonQuarter.radius_sq
    have hprod : (CommonQuarter.radius*n)^2=Q0*((lam+eta)^2+mass^2) := by
      rw [mul_pow,hR,hn]
    have hn0 : 0≤n := by rw [hndef]; exact Real.sqrt_nonneg _
    have hR0 : 0≤CommonQuarter.radius := Real.sqrt_nonneg _
    have hstrict : CommonQuarter.radius*n<
        endpointCap+(lam+eta+mass)/2+eta*axialLower := by
      have hRn : 0≤CommonQuarter.radius*n := mul_nonneg hR0 hn0
      simp only [endpointCap,lam,eta,mass,axialLower,Q0] at hprod ⊢
      nlinarith
    have ha := FrameLowArc.a0_bounds.1
    simp only [lam,eta,mass,endpointCap,axialLower] at hs hstrict hm ⊢
    linarith

theorem path_base : pathBase<Real.pi+3*lam-2*endpointCap := by
  have hh := Arithmetic.pi_hand_enclosure.1
  dsimp [pathBase,lam,endpointCap]
  linarith

def primaryError (s : State) (d : ℝ) : ℝ :=
  d+lam*(GlobalOuterAnchor.width d-1-s.a*Real.sin d-s.b*(1-Real.cos d))

def zeroError (s : State) (d : ℝ) : ℝ :=
  d+lam*(GlobalOuterAnchor.width d-1-s.a*Real.sin d+s.b*(1-Real.cos d))

def rotatedCost (s : State) (d : ℝ) : ℝ :=
  d+lam*(GlobalOuterAnchor.width d-1)-unsigned s-lam*(s.a*Real.cos d+s.b*Real.sin d)

def lowCost (s t : State) (primary : Bool) (d : ℝ) : ℝ :=
  if primary then -unsigned t-lam*t.a+primaryError s d else rotatedCost t d

@[simp] theorem primaryError_zero (s : State) : primaryError s 0=0 := by
  norm_num [primaryError,GlobalOuterAnchor.width]

@[simp] theorem zeroError_zero (s : State) : zeroError s 0=0 := by
  norm_num [zeroError,GlobalOuterAnchor.width]

theorem rotated_positive_delete (s : State) {x : ℝ} (hx : x∈Icc 0 frameCap) :
    -endpointCap+(9/100)*x<rotatedCost s x := by
  have tr := transport_trig hx
  have hsin := Real.sin_le hx.1
  have hcos := sub_nonneg.mpr tr.2.1
  have ha := (coordinates s).1
  have hb := (coordinates s).2.2.2.2
  have hp1 := mul_nonneg (show 0≤ s.a-1/2 by linarith) hcos
  have hp2 := mul_nonneg (show 0≤9/10-s.b by linarith) tr.2.2.1
  have he := endpoint_support s
  simp only [rotatedCost,GlobalOuterAnchor.width,lam,endpointCap] at *
  rw [abs_of_nonneg tr.2.2.1]
  nlinarith

theorem rotated_negative_delete (s : State) (houter : s.branch.type≠0)
    {z : ℝ} (hz : z∈Icc 0 frameCap) :
    -endpointCap+(9/100)*z<rotatedCost s (-z) := by
  have tr := transport_trig hz
  have hm := (outer_marker_bounds s houter).2
  have hs : (eta+lam*Real.cos z)*s.a+(mass-lam*Real.sin z)*s.b≤
      CommonQuarter.radius*rotatedNorm z-
        (eta+lam*Real.cos z+(mass-lam*Real.sin z))/2 :=
    state_support s (eta+lam*Real.cos z) (mass-lam*Real.sin z)
  have hr := rotated_radical_bound hz
  have ha := FrameLowArc.a0_bounds.1
  simp only [rotatedCost,GlobalOuterAnchor.width,rotatedThreshold,lam,eta,mass,
    endpointCap,axialLower] at *
  rw [Real.sin_neg,Real.cos_neg,abs_neg,abs_of_nonneg tr.2.2.1]
  linarith

theorem rotated_delete (s : State) (houter : s.branch.type≠0)
    {d : ℝ} (hd : |d|≤frameCap) :
    -endpointCap+(9/100)*|d|<rotatedCost s d := by
  by_cases hp : 0≤d
  · rw [abs_of_nonneg hp]
    exact rotated_positive_delete s ⟨hp,(le_abs_self d).trans hd⟩
  · have hz : -d∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs d).trans hd⟩
    have hh := rotated_negative_delete s houter hz
    simpa only [neg_neg,abs_of_neg (lt_of_not_ge hp)] using hh

theorem half_angle_norm {x : ℝ} (hx : x∈Icc 0 frameCap) :
    Real.sqrt ((Real.sin x)^2+(1-Real.cos x)^2)=2*Real.sin (x/2) := by
  have hx' : x/2∈Icc 0 frameCap := by
    have h1 := hx.1
    have h2 := hx.2
    simp only [frameCap] at h2 ⊢
    constructor <;> linarith
  have ht := transport_trig hx'
  have hhalf := Real.sin_sq_add_cos_sq (x/2)
  have hunit := Real.sin_sq_add_cos_sq x
  have hc : Real.cos x=2*(Real.cos (x/2))^2-1 := by
    rw [← Real.cos_two_mul]; ring_nf
  have hid : (Real.sin x)^2+(1-Real.cos x)^2=(2*Real.sin (x/2))^2 := by
    linear_combination hunit-2*hc-4*hhalf
  have hp : 0≤2*Real.sin (x/2) := mul_nonneg (by norm_num) ht.2.2.1
  rw [hid,Real.sqrt_sq_eq_abs,abs_of_nonneg hp]

theorem primaryError_positive (s : State) {x : ℝ} (hx : x∈Icc 0 frameCap) :
    positiveCost x≤primaryError s x := by
  have tr := transport_trig hx
  have hs := state_support s (Real.sin x) (1-Real.cos x)
  rw [half_angle_norm hx] at hs
  dsimp [primaryError,positiveCost,GlobalOuterAnchor.width,lam]
  rw [abs_of_nonneg tr.2.2.1]
  nlinarith

theorem zeroError_positive (s : State) {x : ℝ} (hx : x∈Icc 0 frameCap) :
    positiveCost x≤zeroError s x := by
  have hh := primaryError_positive s hx
  have hp := mul_nonneg s.b_nonneg (sub_nonneg.mpr (Real.cos_le_one x))
  dsimp [primaryError,zeroError,lam] at *
  linarith

def lowOwner (primary : Bool) : Fin 4 := if primary then 1 else 0

/-- A reduction of a quarter edge: a feasible low axis at the error `d` itself, and a scalar stress
parameter `error ∈ {0, d}` with the cost bound `cost_gain`. -/
structure LowReduction (s t : State) (d : ℝ) where
  primary : Bool
  feasible : s.Feasible t (lowOwner primary) (Real.pi/2+d)
  error : ℝ
  error_nonneg : 0≤error
  error_eq : error=0 ∨ error=d
  cost_gain : -endpointCap+primaryError s error+(9/100)*|d-error|<lowCost s t primary d

theorem low_reduction (s t : State) {d : ℝ} (hd : |d|≤frameCap)
    (hs : transverse s≤0) (ht : 0≤transverse t)
    (j : Fin 4) (hj : j=0 ∨ j=1)
    (hf : s.Feasible t j (Real.pi/2+d)) : Nonempty (LowReduction s t d) := by
  have hsecondary (hm : s.Feasible t 0 (Real.pi/2+d)) : Nonempty (LowReduction s t d) := by
    have ho := GlobalZeroLow.secondary_target_outer s t hd hs ht hm
    refine ⟨⟨false,hm,0,le_rfl,Or.inl rfl,?_⟩⟩
    simpa [lowCost] using rotated_delete t ho hd
  rcases hj with rfl | rfl
  · exact hsecondary hf
  · by_cases hdpos : 0≤d
    · refine ⟨⟨true,hf,d,hdpos,Or.inr rfl,?_⟩⟩
      have he := endpoint_support t
      simp only [lowCost,ite_true,sub_self,abs_zero,mul_zero,add_zero]
      simp only [lam,endpointCap] at he ⊢
      linarith
    · by_cases hsecondaryAxis : s.Feasible t 0 (Real.pi/2+d)
      · exact hsecondary hsecondaryAxis
      · have hz : -d∈Ioc 0 frameCap := ⟨by linarith,(neg_le_abs d).trans hd⟩
        have hg := GlobalQuarterNegativePrimary.exceptional_gain s t hz hs ht
          (by simpa using hf) (by simpa using hsecondaryAxis)
        have tr := transport_trig (show -d∈Icc 0 frameCap from ⟨hz.1.le,hz.2⟩)
        have he := endpoint_support t
        have hcost : (9/100)*(-d)<primaryError s d := by
          dsimp [primaryError,GlobalOuterAnchor.width,lam]
          have hsin : Real.sin d≤0 := by
            simpa only [Real.sin_neg,neg_nonneg] using tr.2.2.1
          rw [abs_of_nonpos hsin]
          simp only [Real.sin_neg,Real.cos_neg] at hg
          nlinarith
        refine ⟨⟨true,hf,0,le_rfl,Or.inl rfl,?_⟩⟩
        simp only [lowCost,ite_true,primaryError_zero,add_zero,sub_zero,
          abs_of_neg (lt_of_not_ge hdpos)]
        simp only [lam,endpointCap] at he hcost ⊢
        linarith

end SquaresInCircles.Eight.GlobalEH
end
end
end
