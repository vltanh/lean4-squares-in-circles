module

public import SquaresInCircles.Eight.Owners.All.HighCycleComponents
public import SquaresInCircles.Eight.Owners.BT.CoreDE3Polynomial
public import SquaresInCircles.Eight.Owners.EH.Support
public import SquaresInCircles.Eight.Owners.Outer.AnchorDomain
public import SquaresInCircles.Eight.Owners.Zero.SourceOuter

/-!
# Eight squares: pointwise comparisons of the AB, BT and TD dual terms

These statements compare weighted necessary inequalities at two errors on the same states; they
say nothing about feasibility after an error changes. A positive error can be deleted from the
dual term (`positive_zero_delete`, `positive_BT0_delete`, `positive_DE2_delete`,
`positive_DE3_delete`), a negative error of a zero edge leaves the reserve
`(9/2000) z` (`negative_zero_delete`), and the AB term with weight `ABweight` is at least
`kappa * (1 - transverse s + transverse t)` (`AB_delete`). Both signs of the transverse
coordinates and both zero owners are allowed.
-/

section
/-!
## The positive-zero and negative-AB error gains

The positive-zero gain `positiveZeroGain lambda z = z + lambda sin z - 2 lambda R sin (z/2)` is
concave on the whole frame interval and nonnegative there (`positive_zero_gain`). The
negative-AB gain uses one polynomial `P` of degree six whose positive quadratic part dominates its
higher coefficients on `[0, 7/10]` (`reserves`, `positive`), which gives the reserve `9z/2000`
(`negative_AB_gain_scaled`).
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT

open Polynomial FrameCircleArc

def positiveZeroGain (lambda z : ℝ) : ℝ := z+lambda*Real.sin z-2*lambda*R*Real.sin (z/2)
def positiveZeroGainD (lambda z : ℝ) : ℝ := 1+lambda*Real.cos z-lambda*R*Real.cos (z/2)
def positiveZeroGainDD (lambda z : ℝ) : ℝ := -lambda*Real.sin z+(lambda*R/2)*Real.sin (z/2)

theorem positiveZeroGain_deriv (lambda z : ℝ) :
    HasDerivAt (positiveZeroGain lambda) (positiveZeroGainD lambda z) z := by
  have hh : HasDerivAt (fun y => Real.sin (y/2)) (Real.cos (z/2)*(1/2)) z := by
    have h := (Real.hasDerivAt_sin (z/2)).comp z ((hasDerivAt_id' z).div_const 2)
    exact h
  have h : HasDerivAt (fun y => y+lambda*Real.sin y-2*lambda*R*Real.sin (y/2))
      (1+lambda*Real.cos z-2*lambda*R*(Real.cos (z/2)*(1/2))) z :=
    ((hasDerivAt_id' z).fun_add ((Real.hasDerivAt_sin z).const_mul lambda)).fun_sub
      (hh.const_mul (2*lambda*R))
  unfold positiveZeroGain positiveZeroGainD
  exact h.congr_deriv (by ring)

theorem positiveZeroGainD_deriv (lambda z : ℝ) :
    HasDerivAt (positiveZeroGainD lambda) (positiveZeroGainDD lambda z) z := by
  have hh : HasDerivAt (fun y => Real.cos (y/2)) (-Real.sin (z/2)*(1/2)) z := by
    have h := (Real.hasDerivAt_cos (z/2)).comp z ((hasDerivAt_id' z).div_const 2)
    exact h
  have h : HasDerivAt (fun y => 1+lambda*Real.cos y-lambda*R*Real.cos (y/2))
      (lambda*(-Real.sin z)-lambda*R*(-Real.sin (z/2)*(1/2))) z :=
    (((Real.hasDerivAt_cos z).const_mul lambda).const_add 1).fun_sub (hh.const_mul (lambda*R))
  unfold positiveZeroGainD positiveZeroGainDD
  exact h.congr_deriv (by ring)

theorem sine_half_identity (z : ℝ) : Real.sin z=2*Real.sin (z/2)*Real.cos (z/2) := by
  have h := Real.sin_two_mul (z/2)
  rwa [show 2*(z/2)=z by ring] at h

theorem positiveZeroGain_concave :
    ConcaveOn ℝ (Icc 0 frameCap) (positiveZeroGain kappa) := by
  apply concave_of_deriv2 (fun z _ => positiveZeroGain_deriv kappa z)
    (fun z _ => positiveZeroGainD_deriv kappa z)
  intro z hz
  have hhalf : z/2∈Icc 0 frameCap := by
    simp only [frameCap,mem_Icc] at hz ⊢
    constructor <;> linarith [hz.1,hz.2]
  have tr := transport_trig hhalf
  have hr : R<2 := by
    have hh := FrameHighArc.radius_bound
    dsimp [FrameHighArc.radiusUpper] at hh
    linarith
  have hcoeff : R/2-2*Real.cos (z/2)≤0 := by linarith [tr.1]
  have hp := mul_nonpos_of_nonneg_of_nonpos tr.2.2.1 hcoeff
  rw [positiveZeroGainDD,sine_half_identity z]
  dsimp [kappa]
  nlinarith only [hp]

theorem positiveZeroGain_last : 0<positiveZeroGain kappa frameCap := by
  have hs := sin_lower_seven (by norm_num : (0:ℝ)≤7/10)
  have hu := sin_upper_five (by norm_num : (0:ℝ)≤7/20)
  have hhalf : 0≤Real.sin (7/20:ℝ) :=
    (transport_trig (by norm_num [frameCap] : (7/20:ℝ)∈Icc 0 frameCap)).2.2.1
  have hR : R<1979/1000 := by
    have hh := FrameHighArc.radius_bound
    dsimp [FrameHighArc.radiusUpper] at hh
    linarith
  have hp := mul_le_mul hR.le hu hhalf (by norm_num : (0:ℝ)≤1979/1000)
  dsimp [positiveZeroGain,kappa,frameCap]
  norm_num at hs hu hp ⊢
  linarith

theorem positive_zero_gain {lambda z : ℝ} (_hl : 0≤lambda) (hlu : lambda≤kappa)
    (hz : z∈Icc 0 frameCap) : 0≤positiveZeroGain lambda z := by
  have hbase := positiveZeroGain_concave.min_le_of_mem_Icc
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) hz
  have hzero : positiveZeroGain kappa 0=0 := by simp [positiveZeroGain]
  rw [hzero,min_eq_left positiveZeroGain_last.le] at hbase
  have hhalf : z/2∈Icc 0 frameCap := by
    simp only [frameCap,mem_Icc] at hz ⊢
    constructor <;> linarith [hz.1,hz.2]
  have hsn := (transport_trig hhalf).2.2.1
  have hR : 1<R := by
    have hh := R_sq
    have hp := R_pos
    norm_num [Q0] at hh
    nlinarith
  have hchange : Real.sin z-2*R*Real.sin (z/2)≤0 := by
    rw [sine_half_identity z]
    nlinarith [mul_nonneg hsn (show 0≤R-Real.cos (z/2) by linarith [Real.cos_le_one (z/2)])]
  have hm := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hlu) hchange
  dsimp [positiveZeroGain] at hbase ⊢
  nlinarith only [hbase,hm]

namespace NegativeABPolynomial

def P : ℚ[X] :=
  C ((49/50)*(847/800)-2009/2000)-C ((49/50)/5)*X+
    C ((2009/2000)/2-(49/50)*(847/800)/6)*X^2+C ((49/50)/60)*X^3+
    C ((49/50)*(847/800)/120-(2009/2000)/24)*X^4-
    C ((49/50)/1800)*X^5-C ((49/50)*(847/800)/5040)*X^6

private theorem coeffs : P.coeff 0=(49/50)*(847/800)-2009/2000 ∧ P.coeff 1=-((49/50)/5) ∧
    P.coeff 2=(2009/2000)/2-(49/50)*(847/800)/6 ∧ P.coeff 3=(49/50)/60 ∧
    P.coeff 4=(49/50)*(847/800)/120-(2009/2000)/24 ∧ P.coeff 5=-((49/50)/1800) ∧
    P.coeff 6=-((49/50)*(847/800)/5040) ∧ ∀ n, 7≤n → P.coeff n=0 := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,fun n hn => ?_⟩ <;>
    simp only [P,coeff_add,coeff_sub,coeff_C_mul,coeff_X_pow,coeff_X,coeff_C] <;>
    norm_num
  rw [ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_right (by omega),
    ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_right (by omega),
    ite_eq_right (by omega)]
  norm_num

theorem identity : P=C (P.coeff 0)+C (P.coeff 1)*X+C (P.coeff 2)*X^2+
    PowerTailBounds.tail P 3 4 := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ := coeffs
  ext n
  simp only [PowerTailBounds.tail,Fin.sum_univ_four,coeff_add,coeff_C_mul,
    coeff_X_pow,coeff_X,coeff_C]
  rcases n with _|_|_|_|_|_|_|n <;> simp [h0,h1,h2,h3,h4,h5,h6]
  exact h7 _ (by omega)

theorem reserves : 0<P.coeff 2-DirectedPowerBounds.negativeNorm P 3 4 (7/10) ∧
    (P.coeff 1)^2<4*(P.coeff 0)*(P.coeff 2-DirectedPowerBounds.negativeNorm P 3 4 (7/10)) := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,-⟩ := coeffs
  have hn : DirectedPowerBounds.negativeNorm P 3 4 (7/10)=
      max (-P.coeff 3) 0*(7/10)+max (-P.coeff 4) 0*(7/10)^2+max (-P.coeff 5) 0*(7/10)^3+
        max (-P.coeff 6) 0*(7/10)^4 := by
    simp [DirectedPowerBounds.negativeNorm,Fin.sum_univ_four]
  rw [hn,h0,h1,h2,h3,h4,h5,h6]
  norm_num

theorem positive {z : ℝ} (hz : z∈Icc 0 frameCap) : 0<aeval z P := by
  have hz' : z∈Icc 0 ((7/10:ℚ):ℝ) := by
    simp only [frameCap] at hz
    push_cast
    exact hz
  have hh := DirectedPowerBounds.quadratic_lower identity hz'
  have ha : 0<(P.coeff 2:ℝ)-(DirectedPowerBounds.negativeNorm P 3 4 (7/10):ℝ) := by
    exact_mod_cast reserves.1
  have hd : (P.coeff 1:ℝ)^2<4*
      ((P.coeff 2:ℝ)-(DirectedPowerBounds.negativeNorm P 3 4 (7/10):ℝ))*(P.coeff 0:ℝ) := by
    have h := reserves.2
    exact_mod_cast (by linarith [h] : (P.coeff 1)^2<4*
      (P.coeff 2-DirectedPowerBounds.negativeNorm P 3 4 (7/10))*(P.coeff 0))
  have hp := TailPolynomial.strict_quadratic (x := z) ha hd
  linarith

theorem identity_eval (z : ℝ) : z*aeval z P=
    kappa*((847/800)*(z-z^3/6+z^5/120-z^7/5040)+
      (2/5)*(1-z^2/2+z^4/24-z^6/720)-2/5)-
        (2009/2000)*z*(1-z^2/2+z^4/24) := by
  simp [P,kappa]
  ring

end NegativeABPolynomial

/-- The negative-AB comparison multiplied by the positive `cos z`. Its reserve `9/2000` holds for
either zero owner. -/
theorem negative_AB_gain_scaled {z : ℝ} (hz : z∈Icc 0 frameCap) :
    (2009/2000)*z*Real.cos z≤
      kappa*((847/800)*Real.sin z-(2/5)*(1-Real.cos z)) := by
  have hp := mul_nonneg hz.1 (NegativeABPolynomial.positive hz).le
  rw [NegativeABPolynomial.identity_eval] at hp
  have hs := mul_le_mul_of_nonneg_left (sin_lower_seven hz.1)
    (show 0≤kappa*(847/800) by norm_num [kappa])
  have hc := mul_le_mul_of_nonneg_left (cos_lower_six hz.1)
    (show 0≤kappa*(2/5) by norm_num [kappa])
  have hu := mul_le_mul_of_nonneg_left (cos_upper_four hz.1)
    (mul_nonneg (by norm_num : (0:ℝ)≤2009/2000) hz.1)
  linarith only [hp,hs,hc,hu]

end SquaresInCircles.Eight.GlobalBT
end
end
end

section
/-!
## All-original-axis nominal bounds on the short return path

Each original projection rotates exactly one actual center.  Its
center norm bounds the full signed rotation increment, and the same
error's square width recovers the nominal inequality.  The three
actual return projections then constrain A without any H/G sign or
quarter-owner assumption.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT

open FramePair FrameCircleArc GlobalOuterAnchor GlobalZeroSign GlobalQuarterSign

def projection (quarter : Bool) (s t : State) (d : ℝ) : Fin 4→ℝ :=
  if quarter then
    ![transverse s+t.a*Real.cos d+transverse t*Real.sin d,
      t.a+s.a*Real.sin d+transverse s*Real.cos d,
      s.a*Real.cos d-transverse s*Real.sin d-transverse t,
      s.a+t.a*Real.sin d-transverse t*Real.cos d]
  else
    ![transverse s+t.a*Real.sin d-transverse t*Real.cos d,
      t.a-s.a*Real.cos d+transverse s*Real.sin d,
      s.a*Real.sin d+transverse s*Real.cos d-transverse t,
      s.a-t.a*Real.cos d-transverse t*Real.sin d]

def nominal (quarter : Bool) (s t : State) (j : Fin 4) : ℝ := projection quarter s t 0 j

theorem projection_feasible (quarter : Bool) (s t : State) (j : Fin 4) {d : ℝ}
    (hd : |d|≤frameCap) :
    s.Feasible t j ((if quarter then Real.pi/2 else 0)+d) ↔
      GlobalOuterAnchor.width d≤projection quarter s t d j := by
  cases quarter <;> fin_cases j <;>
    simp [State.Feasible,forwardMargin,projection,transverse,
      Real.sin_add,Real.cos_add,GlobalOuterAnchor.width,
      CommonQuarter.signed_width (by simpa only [frameCap] using hd),
      CommonQuarter.quarter_width (by simpa only [frameCap] using hd)]
  constructor <;> intro hh <;> linarith

theorem transverse_sq (s : State) : (transverse s)^2=s.b^2 := by
  cases hp : s.positive <;> simp [transverse,FramePair.sign,hp]

theorem transverse_bounds (s : State) : -s.b≤transverse s ∧ transverse s≤ s.b := by
  cases hp : s.positive <;> simp [transverse,FramePair.sign,hp] <;> linarith [s.b_nonneg]

theorem state_sum_sharp (s : State) : s.a+s.b≤2*c0 := by
  have hc := state_circle s
  have hh := c0_circle
  have ha := s.a_pos
  have hb := s.b_nonneg
  have hd := c0_bounds.1
  by_contra! hn
  have hm := mul_pos (show 0<s.a+s.b-2*c0 by linarith)
    (show 0<s.a+s.b+2*c0+2 by linarith)
  nlinarith [sq_nonneg (s.a-s.b)]

/-- The complete signed rotation increment, for arbitrary real force
components, uses the one original center norm. -/
theorem rotation_increment {a b d : ℝ} (hn : a^2+b^2≤(283/200:ℝ)^2) :
    a*(Real.cos d-1)+b*Real.sin d≤(283/200)*|d| := by
  have hc := Real.one_sub_sq_div_two_le_cos (x := d)
  have hunit := Real.sin_sq_add_cos_sq d
  have hdelta : (Real.cos d-1)^2+(Real.sin d)^2≤d^2 := by linarith
  have hforce : 0≤a^2+b^2 := by positivity
  have h1 := mul_le_mul_of_nonneg_left hdelta hforce
  have h2 := mul_le_mul_of_nonneg_right hn (sq_nonneg d)
  have hid : (a^2+b^2)*((Real.cos d-1)^2+(Real.sin d)^2)-
      (a*(Real.cos d-1)+b*Real.sin d)^2=
      (a*Real.sin d-b*(Real.cos d-1))^2 := by ring
  have hsq : (a*(Real.cos d-1)+b*Real.sin d)^2≤((283/200)*|d|)^2 := by
    rw [mul_pow,sq_abs]
    linarith only [h1,h2,hid,sq_nonneg (a*Real.sin d-b*(Real.cos d-1))]
  have hp : 0≤(283/200:ℝ)*|d| := mul_nonneg (by norm_num) (abs_nonneg d)
  exact (abs_le_of_sq_le_sq' hsq hp).2

theorem projection_increment (quarter : Bool) (s t : State) (j : Fin 4) (d : ℝ) :
    projection quarter s t d j-nominal quarter s t j≤(283/200)*|d| := by
  have hs : (transverse s)^2+s.a^2≤(283/200:ℝ)^2 := by
    rw [transverse_sq]; linarith [state_norm_sq s]
  have ht : (transverse t)^2+t.a^2≤(283/200:ℝ)^2 := by
    rw [transverse_sq]; linarith [state_norm_sq t]
  cases quarter with
  | false =>
      fin_cases j
      · have hh := rotation_increment (a := -transverse t) (b := t.a) (d := d) (by linarith)
        simp [projection,nominal]
        linarith
      · have hh := rotation_increment (a := -s.a) (b := transverse s) (d := d) (by linarith)
        simp [projection,nominal]
        linarith
      · have hh := rotation_increment (a := transverse s) (b := s.a) (d := d) (by linarith)
        simp [projection,nominal]
        linarith
      · have hh := rotation_increment (a := -t.a) (b := -transverse t) (d := d) (by linarith)
        simp [projection,nominal]
        linarith
  | true =>
      fin_cases j
      · have hh := rotation_increment (a := t.a) (b := transverse t) (d := d) (by linarith)
        simp [projection,nominal]
        linarith
      · have hh := rotation_increment (a := transverse s) (b := s.a) (d := d) (by linarith)
        simp [projection,nominal]
        linarith
      · have hh := rotation_increment (a := s.a) (b := -transverse s) (d := d) (by linarith)
        simp [projection,nominal]
        linarith
      · have hh := rotation_increment (a := -transverse t) (b := t.a) (d := d) (by linarith)
        simp [projection,nominal]
        linarith

theorem width_abs (d : ℝ) : GlobalOuterAnchor.width d=GlobalOuterAnchor.width |d| := by
  by_cases hp : 0≤d
  · rw [abs_of_nonneg hp]
  · rw [abs_of_nonpos (by linarith : d≤0)]
    simp [GlobalOuterAnchor.width,Real.cos_neg,Real.sin_neg,abs_neg]

theorem short_width_reserve {d : ℝ} (hd : |d|≤(3/10:ℝ)) :
    1-|d|≤GlobalOuterAnchor.width d-(283/200)*|d| := by
  have hz : |d|∈Icc 0 (3/10:ℝ) := ⟨abs_nonneg d,hd⟩
  have hc := Real.one_sub_sq_div_two_le_cos (x := |d|)
  have hs := Real.sin_ge_sub_cube hz.1
  have hs0 := (transport_trig (show |d|∈Icc 0 (7/10:ℝ) from
    ⟨hz.1,by linarith [hz.2]⟩)).2.2.1
  rw [width_abs,GlobalOuterAnchor.width,abs_of_nonneg hs0]
  generalize |d| = z at *
  have h2 : z^2≤(3/10)*z := by nlinarith [mul_nonneg hz.1 (sub_nonneg.mpr hz.2)]
  have h3 := mul_le_mul_of_nonneg_right h2 hz.1
  have h4 := mul_le_mul_of_nonneg_left h2 (by norm_num : (0:ℝ)≤3/10)
  nlinarith

/-- All four original axes, both signs and both zero/quarter words. -/
theorem original_nominal_lower (quarter : Bool) (s t : State) (j : Fin 4) {d : ℝ}
    (hd : |d|≤(3/10:ℝ))
    (hm : s.Feasible t j ((if quarter then Real.pi/2 else 0)+d)) :
    1-|d|≤nominal quarter s t j := by
  have hf := (projection_feasible quarter s t j
    (by change |d|≤(7/10:ℝ); linarith [hd])).1 hm
  linarith [projection_increment quarter s t j d,short_width_reserve hd]

theorem three_nominal_upper (e h g a : State) (jE jH jG : Fin 4)
    (he : transverse e≤0) (ha : 0≤transverse a) (hH : jH=0 ∨ jH=2) :
    nominal true e h jE+nominal false h g jH+nominal true g a jG≤4*c0-a.b := by
  have heq := transverse_nonpos_eq e he
  have haq := transverse_of_nonneg a ha
  have hHsum := state_sum_sharp h
  have hGsum := state_sum_sharp g
  have hAsum := state_sum_sharp a
  have hEsum := state_sum_sharp e
  have hHy := transverse_bounds h
  have hGy := transverse_bounds g
  change transverse e= -e.b at heq
  have hHv : nominal false h g jH=transverse h-transverse g := by
    rcases hH with rfl | rfl <;> simp [nominal,projection]
  have hEv : nominal true e h jE=h.a-e.b ∨ nominal true e h jE=e.a-transverse h := by
    fin_cases jE <;> simp [nominal,projection,heq]
    all_goals (left; ring)
  have hGv : nominal true g a jG=transverse g+a.a ∨ nominal true g a jG=g.a-a.b := by
    fin_cases jG <;> simp [nominal,projection,haq]
    all_goals (left; ring)
  rw [hHv]
  rcases hEv with hE | hE <;> rcases hGv with hG | hG <;> rw [hE,hG] <;>
    linarith [e.b_nonneg,a.b_nonneg,hHy.2,hGy.1]

theorem short_return_endpoint (e h g a : State) (jE jH jG : Fin 4) {r v t : ℝ}
    (he : transverse e≤0) (ha : 0≤transverse a) (hH : jH=0 ∨ jH=2)
    (hshort : |r|+|v|+|t|≤(3/10:ℝ))
    (hEH : e.Feasible h jE (Real.pi/2+r))
    (hHG : h.Feasible g jH v) (hGA : g.Feasible a jG (Real.pi/2+t)) :
    a.b≤4*c0-3+(|r|+|v|+|t|) := by
  have hr : |r|≤(3/10:ℝ) := by linarith [abs_nonneg v,abs_nonneg t]
  have hv : |v|≤(3/10:ℝ) := by linarith [abs_nonneg r,abs_nonneg t]
  have ht : |t|≤(3/10:ℝ) := by linarith [abs_nonneg r,abs_nonneg v]
  have hpE := original_nominal_lower true e h jE hr hEH
  have hpH := original_nominal_lower false h g jH hv (by simpa using hHG)
  have hpG := original_nominal_lower true g a jG ht hGA
  linarith [three_nominal_upper e h g a jE jH jG he ha hH]

end SquaresInCircles.Eight.GlobalBT
end
end
end

section
/-!
## Actual source data under either forbidden low BT owner

Every stored sign, radial fact, owner and projection is derived from
the unchanged physical cycle.  This record introduces no source
hypothesis and retains a feasible original witness for each edge.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT

open Candidate FramePair GlobalOuterAnchor

theorem frame_zero_projection {C : BoundaryCycle Q0} (F : Candidate.Frame C)
    (i : Vertex) (hi : word i=0) (j : Fin 4)
    (hj : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    GlobalOuterAnchor.width (delta F.theta i)≤projection false (stateOf C i) (stateOf C (next i))
      (delta F.theta i) j := by
  have hd : |delta F.theta i|≤frameCap := by simpa only [frameCap] using (F.delta_small i).le
  apply (projection_feasible false _ _ _ hd).1
  simpa [Candidate.phi,hi] using GlobalAllHigh.frame_state_feasible F i j hj

theorem frame_quarter_projection {C : BoundaryCycle Q0} (F : Candidate.Frame C)
    (i : Vertex) (hi : word i=1) (j : Fin 4)
    (hj : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    GlobalOuterAnchor.width (delta F.theta i)≤projection true (stateOf C i) (stateOf C (next i))
      (delta F.theta i) j := by
  have hd : |delta F.theta i|≤frameCap := by simpa only [frameCap] using (F.delta_small i).le
  apply (projection_feasible true _ _ _ hd).1
  simpa [Candidate.phi,hi] using GlobalAllHigh.frame_state_feasible F i j hj

structure LowSource (C : BoundaryCycle Q0) (F : Candidate.Frame C) (j : Fin 4) where
  AB : Bool
  TD : Bool
  DE : Fin 4
  A_tangent : 0<C.tangent A
  A_positive : 0≤transverse (stateOf C A)
  T_positive : 0≤transverse (stateOf C T)
  D_negative : transverse (stateOf C D)≤0
  E_negative : transverse (stateOf C E)≤0
  T_outer : (stateOf C T).branch.type≠0
  DE_owner : DE=2 ∨ DE=3
  AB_projection : GlobalOuterAnchor.width (delta F.theta A)≤
    projection false (stateOf C A) (stateOf C B) (delta F.theta A) (leftOwner AB)
  BT_projection : GlobalOuterAnchor.width (delta F.theta B)≤
    projection true (stateOf C B) (stateOf C T) (delta F.theta B) j
  TD_projection : GlobalOuterAnchor.width (delta F.theta T)≤
    projection false (stateOf C T) (stateOf C D) (delta F.theta T) (leftOwner TD)
  DE_projection : GlobalOuterAnchor.width (delta F.theta D)≤
    projection true (stateOf C D) (stateOf C E) (delta F.theta D) DE

theorem lowSource {C : BoundaryCycle Q0} (F : Candidate.Frame C) (hE : C.tangent E≤0)
    (j : Fin 4) (hj : j=0 ∨ j=1)
    (hBT : (forwardAxis j).Feasible (C.square B) (C.square T)) : Nonempty (LowSource C F j) := by
  have hq : Q0∈Icc (5/2:ℝ) Q0 := by norm_num [Q0]
  have hA := GlobalZeroLow.frame_BT_low_A_positive F hq j hj hBT
  have hTOuter := GlobalQuarterOuter.frame_low_outer F hq B (by norm_num [word,B]) j hj
    (by simpa [B,T,next] using hBT)
  have hT : 0<C.tangent T := by
    rcases GlobalQuarterSign.of_frame F hq B (by norm_num [word,B]) j
      (by simpa [B,T,next] using hBT) with ⟨_,hh⟩ | ⟨hh,_⟩
    · simpa [B,T,next] using hh
    · rcases hj with rfl | rfl <;> rcases hh with hh | hh <;> norm_num at hh
  have hD := GlobalQuarterSign.frame_DE F hq hE
  have hex (i : Vertex) :
      ∃ k : Fin 4,(forwardAxis k).Feasible (C.square i) (C.square (next i)) := by
    obtain ⟨k,hk⟩ := F.forward_complete i (C.selected i) (C.feasible i)
    exact ⟨k,hk ▸ C.feasible i⟩
  choose owner hf using hex
  have hABowner : owner A=0 ∨ owner A=2 := by
    rcases GlobalZeroSign.of_frame F hq A (by norm_num [word,A]) (owner A) (hf A) with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hTDowner : owner T=0 ∨ owner T=2 := by
    rcases GlobalZeroSign.of_frame F hq T (by norm_num [word,T]) (owner T) (hf T) with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  obtain ⟨ab,hab⟩ : ∃ab : Bool,leftOwner ab=owner A := by
    rcases hABowner with hh | hh
    · exact ⟨false,by simpa [leftOwner] using hh.symm⟩
    · exact ⟨true,by simpa [leftOwner] using hh.symm⟩
  obtain ⟨td,htd⟩ : ∃td : Bool,leftOwner td=owner T := by
    rcases hTDowner with hh | hh
    · exact ⟨false,by simpa [leftOwner] using hh.symm⟩
    · exact ⟨true,by simpa [leftOwner] using hh.symm⟩
  refine ⟨{
    AB := ab, TD := td, DE := owner D,
    A_tangent := hA,
    A_positive := (GlobalAllHigh.state_positive_of_tangent C A hA).le,
    T_positive := (GlobalAllHigh.state_positive_of_tangent C T hT).le,
    D_negative := (GlobalAllHigh.state_negative_of_tangent C D hD.1).le,
    E_negative := ?_, T_outer := ?_, DE_owner := ?_,
    AB_projection := ?_, BT_projection := ?_, TD_projection := ?_, DE_projection := ?_ }⟩
  · rw [GlobalAllHigh.state_transverse_eq]
    exact mul_nonpos_of_nonneg_of_nonpos (C.a_pos E).le hE
  · exact GlobalAllHigh.state_outer_of_kind C T (by simpa [B,T,next] using hTOuter)
  · exact hD.2 (owner D) (by simpa [D,E,next] using hf D)
  · simpa [A,B,next,hab] using frame_zero_projection F A (by norm_num [word,A]) (owner A) (hf A)
  · simpa [B,T,next] using frame_quarter_projection F B (by norm_num [word,B]) j
      (by simpa [B,T,next] using hBT)
  · simpa [T,D,next,htd] using frame_zero_projection F T (by norm_num [word,T]) (owner T) (hf T)
  · simpa [D,E,next] using frame_quarter_projection F D (by norm_num [word,D]) (owner D) (hf D)

end SquaresInCircles.Eight.GlobalBT
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT

open FramePair FrameCircleArc GlobalOuterAnchor GlobalZeroSign

def zeroDual (primary : Bool) (s t : State) (d lambda : ℝ) : ℝ :=
  d+lambda*(GlobalOuterAnchor.width d-projection false s t d (leftOwner primary))
def ABweight (d : ℝ) : ℝ := if 0≤d then kappa else kappa/Real.cos d
def retainedNegative (d : ℝ) : ℝ := -max (-d) 0

theorem width_positive {z : ℝ} (hz : z∈Icc 0 frameCap) :
    GlobalOuterAnchor.width z=(1+Real.cos z+Real.sin z)/2 := by
  rw [GlobalOuterAnchor.width,abs_of_nonneg (transport_trig hz).2.2.1]

theorem width_negative {z : ℝ} (hz : z∈Icc 0 frameCap) :
    GlobalOuterAnchor.width (-z)=(1+Real.cos z+Real.sin z)/2 := by
  rw [GlobalOuterAnchor.width,Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg (transport_trig hz).2.2.1]

theorem folded_positive_gain (s : State) {lambda z : ℝ}
    (hl : 0≤lambda) (hlu : lambda≤kappa) (hz : z∈Icc 0 frameCap) :
    0≤z+lambda*(GlobalOuterAnchor.width z-1-s.a*Real.sin z-s.b*(1-Real.cos z)) := by
  have hs := state_support s (Real.sin z) (1-Real.cos z)
  rw [GlobalEH.half_angle_norm hz,show CommonQuarter.radius=R from rfl] at hs
  have hs' : s.a*Real.sin z+s.b*(1-Real.cos z)≤
      2*R*Real.sin (z/2)-(Real.sin z+1-Real.cos z)/2 := by
    linarith
  have hm := mul_le_mul_of_nonneg_left hs' hl
  have hg := positive_zero_gain hl hlu hz
  rw [width_positive hz]
  dsimp [positiveZeroGain] at hg
  nlinarith only [hm,hg]

theorem positive_zero_delete (s t : State) (primary : Bool) {lambda z : ℝ}
    (hl : 0≤lambda) (hlu : lambda≤kappa) (hz : z∈Icc 0 frameCap) :
    lambda*(1-transverse s+transverse t)≤zeroDual primary s t z lambda := by
  have hcos : 0≤1-Real.cos z := sub_nonneg.mpr (Real.cos_le_one z)
  cases primary with
  | false =>
      have hgain := folded_positive_gain t hl hlu hz
      have hy := (transverse_bounds t).2
      have hp := mul_nonneg (sub_nonneg.mpr hy) hcos
      have hm := mul_nonneg hl hp
      dsimp [zeroDual,leftOwner,projection]
      nlinarith only [hgain,hm]
  | true =>
      have hgain := folded_positive_gain s hl hlu hz
      have hy := (transverse_bounds s).1
      have hp := mul_nonneg (show 0≤ s.b+transverse s by linarith) hcos
      have hm := mul_nonneg hl hp
      dsimp [zeroDual,leftOwner,projection]
      nlinarith only [hgain,hm]

theorem negative_zero_difference (s t : State) (primary : Bool) {z : ℝ}
    (hz : z∈Icc 0 frameCap) :
    (zeroDual primary s t (-z) (kappa/Real.cos z)-
      kappa*(1-transverse s+transverse t)-(9/2000)*z)*Real.cos z=
      kappa*((if primary then s.a+1/2 else t.a+1/2)*Real.sin z+
        (if primary then transverse t+1/2 else 1/2-transverse s)*(1-Real.cos z))-
          (2009/2000)*z*Real.cos z := by
  have hc : Real.cos z≠0 := ne_of_gt (by linarith [(transport_trig hz).1])
  cases primary <;>
    simp only [zeroDual,leftOwner,projection,Bool.false_eq_true,↓reduceIte,
      Matrix.cons_val_zero,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,
      width_negative hz,Real.cos_neg,Real.sin_neg]
  all_goals field_simp [hc]; ring

theorem negative_zero_delete (s t : State) (primary : Bool) {z : ℝ}
    (hz : z∈Icc 0 frameCap) :
    kappa*(1-transverse s+transverse t)+(9/2000)*z≤
      zeroDual primary s t (-z) (kappa/Real.cos z) := by
  have htr := transport_trig hz
  have hcos : 0<Real.cos z := by linarith [htr.1]
  have hdiff := negative_zero_difference s t primary hz
  have hg := negative_AB_gain_scaled hz
  have h1 : 0≤1-Real.cos z := sub_nonneg.mpr (Real.cos_le_one z)
  have hsA := (ZeroPrimary.primary_lower s).le
  have htA := (ZeroPrimary.primary_lower t).le
  have hsY : transverse s≤9/10 := (transverse_bounds s).2.trans s.b_upper
  have htY : -(9/10:ℝ)≤transverse t := by
    linarith [(transverse_bounds t).1,t.b_upper]
  cases primary with
  | false =>
      have hpa := mul_nonneg (show 0≤ t.a-447/800 by linarith) htr.2.2.1
      have hpy := mul_nonneg (show 0≤9/10-transverse s by linarith) h1
      simp only [Bool.false_eq_true,↓reduceIte] at hdiff
      have hscaled : 0≤(zeroDual false s t (-z) (kappa/Real.cos z)-
          kappa*(1-transverse s+transverse t)-(9/2000)*z)*Real.cos z := by
        dsimp [kappa] at hg hdiff ⊢
        nlinarith only [hdiff,hg,hpa,hpy]
      nlinarith only [hscaled,hcos]
  | true =>
      have hpa := mul_nonneg (show 0≤ s.a-447/800 by linarith) htr.2.2.1
      have hpy := mul_nonneg (show 0≤transverse t+9/10 by linarith) h1
      simp only [↓reduceIte] at hdiff
      have hscaled : 0≤(zeroDual true s t (-z) (kappa/Real.cos z)-
          kappa*(1-transverse s+transverse t)-(9/2000)*z)*Real.cos z := by
        dsimp [kappa] at hg hdiff ⊢
        nlinarith only [hdiff,hg,hpa,hpy]
      nlinarith only [hscaled,hcos]

theorem ABweight_positive {d : ℝ} (hd : |d|≤frameCap) : 0<ABweight d := by
  have hc : 0<Real.cos d := by
    linarith [(CommonQuarter.signed_cos (by simpa only [frameCap] using hd)).1]
  by_cases hp : 0≤d
  · simp [ABweight,hp,kappa]
  · rw [ABweight,ite_eq_right hp]
    exact div_pos (by norm_num [kappa]) hc

/-- For both owners of AB and either sign of B, the AB dual term with weight `ABweight d` is at
least `kappa * (1 - transverse s + transverse t)`. -/
theorem AB_delete (s t : State) (primary : Bool) {d : ℝ} (hd : |d|≤frameCap) :
    kappa*(1-transverse s+transverse t)≤zeroDual primary s t d (ABweight d) := by
  by_cases hp : 0≤d
  · rw [ABweight,ite_eq_left hp]
    exact positive_zero_delete s t primary (by norm_num [kappa]) le_rfl
      ⟨hp,(le_abs_self d).trans hd⟩
  · have hz : -d∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs d).trans hd⟩
    have hh := negative_zero_delete s t primary hz
    rw [ABweight,ite_eq_right hp]
    simp only [neg_neg,Real.cos_neg] at hh
    linarith [hz.1]

theorem rotated_positive_gain (s : State) {y lambda z : ℝ}
    (hy : y≤9/10) (hl : 0≤lambda) (hlu : lambda≤kappa)
    (hz : z∈Icc 0 frameCap) :
    0≤z+lambda*(GlobalOuterAnchor.width z-1-s.a*(Real.cos z-1)-y*Real.sin z) := by
  have ht := transport_trig hz
  have ha := ZeroPrimary.primary_lower s
  have hc := mul_nonneg (show 0≤ s.a-1/2 by linarith)
    (sub_nonneg.mpr (Real.cos_le_one z))
  have hsin := Real.sin_le hz.1
  have hyprod := mul_nonneg (show 0≤9/10-y by linarith) ht.2.2.1
  have hbase : -(2/5)*z≤GlobalOuterAnchor.width z-1-s.a*(Real.cos z-1)-y*Real.sin z := by
    rw [width_positive hz]
    nlinarith only [hc,hyprod,hsin]
  have hm := mul_le_mul_of_nonneg_left hbase hl
  have hcoef : 0≤1-(2/5)*lambda := by dsimp [kappa] at hlu; linarith
  nlinarith only [hm,mul_nonneg hcoef hz.1]

theorem positive_BT0_delete (s t : State) {lambda z : ℝ}
    (hl : 0≤lambda) (hlu : lambda≤kappa) (hz : z∈Icc 0 frameCap) :
    lambda*(1-projection true s t 0 0)≤
      z+lambda*(GlobalOuterAnchor.width z-projection true s t z 0) := by
  have hh := rotated_positive_gain t ((transverse_bounds t).2.trans t.b_upper) hl hlu hz
  simp only [projection,↓reduceIte,Matrix.cons_val_zero,
    Real.cos_zero,Real.sin_zero,mul_one,mul_zero,add_zero]
  linarith

theorem positive_DE2_delete (s t : State) {lambda z : ℝ}
    (hl : 0≤lambda) (hlu : lambda≤kappa) (hz : z∈Icc 0 frameCap) :
    lambda*(1-projection true s t 0 2)≤
      z+lambda*(GlobalOuterAnchor.width z-projection true s t z 2) := by
  have hy : -transverse s≤9/10 := by linarith [(transverse_bounds s).1,s.b_upper]
  have hh := rotated_positive_gain s hy hl hlu hz
  simp only [projection,↓reduceIte,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,
    Real.cos_zero,Real.sin_zero,mul_one,mul_zero,sub_zero]
  linarith

theorem positive_DE3_delete (s t : State) {lambda z : ℝ}
    (hl : 0≤lambda) (hlu : lambda≤kappa) (hz : z∈Icc 0 frameCap) :
    lambda*(1-projection true s t 0 2)≤
      z+lambda*(GlobalOuterAnchor.width z-projection true s t z 3) := by
  have hh := positive_zero_delete s t false hl hlu hz
  dsimp [zeroDual,leftOwner,projection] at hh
  simp only [projection,↓reduceIte,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.head_cons,Matrix.tail_cons,Real.cos_zero,Real.sin_zero,mul_one,mul_zero,sub_zero]
  linarith

end SquaresInCircles.Eight.GlobalBT
end
end
end
