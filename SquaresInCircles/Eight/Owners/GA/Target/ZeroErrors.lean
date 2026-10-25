module

public import SquaresInCircles.Eight.Owners.EH.Path
public import SquaresInCircles.Eight.Owners.GA.Target.Markers

/-!
# Eight squares: the zero errors pay for the return-charge variation

Each positive error is bounded using its rotating endpoint (`positive_lower`). Negative outer
errors use the two endpoints of the whole arc (`negative_outer_lower`). The only core exception
keeps the assumed large target coordinate and the lower bound of the core primary
(`large_target_lower`). No zero owner or marker is reselected (`return_allowance`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.Target
open FramePair ZeroPrimary FrameCircleArc GlobalZeroSign GlobalOuterAnchor
open Arithmetic

def zeroError (s : State) (d : ℝ) : ℝ :=
  d+m*(GlobalOuterAnchor.width d-1-s.a*Real.sin d-s.b*(Real.cos d-1))
def zeroPositive (s : State) (d : ℝ) : ℝ :=
  d+m*((Real.sin d+Real.cos d-1)/2-s.a*Real.sin d+s.b*(1-Real.cos d))
def zeroDerivative (s : State) (d : ℝ) : ℝ :=
  1+m*((s.b-1/2)*Real.sin d+(1/2-s.a)*Real.cos d)

lemma positive_identity (s : State) {d : ℝ} (hd : d∈Icc 0 frameCap) :
    zeroError s d=zeroPositive s d := by
  have ht := transport_trig hd
  dsimp [zeroError,zeroPositive,GlobalOuterAnchor.width]
  rw [abs_of_nonneg ht.2.2.1]
  ring

lemma negative_identity (s : State) {z : ℝ} (hz : z∈Icc 0 frameCap) :
    zeroError s (-z)=-z+m*((s.a+1/2)*Real.sin z+(s.b-1/2)*(1-Real.cos z)) := by
  have ht := transport_trig hz
  dsimp [zeroError,GlobalOuterAnchor.width]
  rw [Real.sin_neg,Real.cos_neg,abs_neg,abs_of_nonneg ht.2.2.1]
  ring

lemma positive_hasDerivAt (s : State) (d : ℝ) :
    HasDerivAt (zeroPositive s) (zeroDerivative s d) d := by
  have h1 : HasDerivAt (fun x => (Real.sin x+Real.cos x-1)/2)
      ((Real.cos d+-Real.sin d)/2) d :=
    (((Real.hasDerivAt_sin d).fun_add (Real.hasDerivAt_cos d)).sub_const 1).div_const 2
  have h2 : HasDerivAt (fun x => (Real.sin x+Real.cos x-1)/2-s.a*Real.sin x)
      ((Real.cos d+-Real.sin d)/2-s.a*Real.cos d) d :=
    h1.fun_sub ((Real.hasDerivAt_sin d).const_mul s.a)
  have h3 : HasDerivAt (fun x => s.b*(1-Real.cos x)) (s.b*(-(-Real.sin d))) d :=
    ((Real.hasDerivAt_cos d).const_sub 1).const_mul s.b
  have h4 : HasDerivAt
      (fun x => x+m*((Real.sin x+Real.cos x-1)/2-s.a*Real.sin x+s.b*(1-Real.cos x)))
      (1+m*((Real.cos d+-Real.sin d)/2-s.a*Real.cos d+s.b*(-(-Real.sin d)))) d :=
    (hasDerivAt_id' d).fun_add ((h2.fun_add h3).const_mul m)
  exact h4.congr_deriv (by dsimp [zeroDerivative]; ring)

lemma positive_derivative_lower (s : State) {d : ℝ} (hd : d∈Icc 0 frameCap) :
    (9/100:ℝ)<zeroDerivative s d := by
  have ht := transport_trig hd
  have hp := FrameCoreArc.projection_lt (a:=(1/2:ℝ)) (b:=(183/200:ℝ))
    (by norm_num : (0:ℝ)<1043/1000) (by norm_num) d
  have hA := mul_le_mul_of_nonneg_right (coordinates s).2.1.le
    (show 0≤Real.cos d by linarith [ht.1])
  have hB := mul_nonneg s.b_nonneg ht.2.2.1
  dsimp [zeroDerivative,m]
  nlinarith only [hp,hA,hB]

lemma positive_lower (s : State) {d : ℝ} (hd : d∈Icc 0 frameCap) :
    (9/100)*d≤zeroError s d := by
  have hm : MonotoneOn (fun z => zeroPositive s z-(9/100)*z) (Icc 0 frameCap) :=
    monoOn_of_hasDeriv_nonneg
      (fun z _ => ((positive_hasDerivAt s z).sub ((hasDerivAt_id z).const_mul (9/100:ℝ))).continuousAt.continuousWithinAt)
      (fun z _ => (positive_hasDerivAt s z).sub ((hasDerivAt_id z).const_mul (9/100:ℝ)))
      (fun z hz => by linarith [positive_derivative_lower s (Ioo_subset_Icc_self hz)])
  have hh := hm (by norm_num [frameCap] : (0:ℝ)∈Icc 0 frameCap) hd hd.1
  rw [positive_identity s hd]
  norm_num [zeroPositive] at hh
  dsimp only [zeroPositive]
  linarith

lemma sine_linear {z : ℝ} (hz : z∈Icc 0 frameCap) : (23/25)*z≤Real.sin z := by
  have hcap : (23/25)*frameCap<Real.sin frameCap := by
    have hs := HighOrderTaylor.S15_le_sin (by norm_num [frameCap] : 0≤frameCap)
    have hnum : (23/25)*frameCap<HighOrderTaylor.S15 frameCap := by
      norm_num [frameCap,HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,sin9,sin7]
    exact hnum.trans_le hs
  have hc : ConcaveOn ℝ (Icc 0 frameCap) (fun x : ℝ => Real.sin x-(23/25)*x) := by
    apply concave_of_deriv2 (f':=fun x => Real.cos x-23/25) (f'':=fun x => -Real.sin x)
    · intro x hx
      have h := (Real.hasDerivAt_sin x).fun_sub ((hasDerivAt_id' x).const_mul (23/25:ℝ))
      exact h.congr_deriv (by ring)
    · intro x hx
      exact (Real.hasDerivAt_cos x).sub_const (23/25)
    · intro x hx
      linarith [(transport_trig hx).2.2.1]
  have hh := hc.min_le_of_mem_Icc (by norm_num [frameCap] : (0:ℝ)∈Icc 0 frameCap)
    (by norm_num [frameCap] : frameCap∈Icc 0 frameCap) hz
  have hlo : (0:ℝ)≤ min (Real.sin 0-(23/25)*0) (Real.sin frameCap-(23/25)*frameCap) :=
    le_min (by norm_num) (by linarith)
  linarith

lemma cosine_loss_linear {z : ℝ} (hz : z∈Icc 0 frameCap) :
    0≤1-Real.cos z ∧ 1-Real.cos z≤(7/20)*z := by
  have hc := Real.one_sub_sq_div_two_le_cos (x:=z)
  have hsq := mul_nonneg hz.1 (sub_nonneg.mpr hz.2)
  dsimp [frameCap] at hsq
  exact ⟨sub_nonneg.mpr (Real.cos_le_one z),by nlinarith⟩

lemma negative_outer_lower (s : State) (hs : s.branch.type≠0) {z : ℝ}
    (hz : z∈Icc 0 frameCap) : (9/100)*z≤zeroError s (-z) := by
  have hchart := state_outer_chart s hs
  have ht := transport_trig hz
  have hsin := sine_linear hz
  have hcos := cosine_loss_linear hz
  have he := linear_endpoint_lower (p:=Real.sin z) (q:=1-Real.cos z)
    ht.2.2.1 (by norm_num : (0:ℝ)≤0) le_rfl hchart.2
  have hax : (9/100)*z≤-z+m*(linear (Real.sin z) (1-Real.cos z) 0+
      Real.sin z/2-(1-Real.cos z)/2) := by
    have ha : (19/10:ℝ)≤a0+1/2 := by linarith [FrameLowArc.a0_bounds.1]
    have hp := mul_le_mul ha hsin (by linarith [hz.1] : 0≤(23/25)*z) (by linarith [FrameLowArc.a0_bounds.1])
    rw [linear,A_zero]
    dsimp [m]
    nlinarith
  have hdiag : (9/100)*z≤-z+m*(linear (Real.sin z) (1-Real.cos z) c0+
      Real.sin z/2-(1-Real.cos z)/2) := by
    have ha : (1399/1000:ℝ)≤c0+1/2 := by linarith [c0_bounds.1]
    have hp := mul_le_mul ha hsin (by linarith [hz.1] : 0≤(23/25)*z) (by linarith [c0_bounds.1])
    have hdrop := mul_nonneg (show 0≤c0-1/2 by linarith [c0_bounds.1]) hcos.1
    rw [linear,A_c0]
    dsimp [m]
    nlinarith
  rw [negative_identity s hz,hchart.1]
  rcases le_total (linear (Real.sin z) (1-Real.cos z) 0)
    (linear (Real.sin z) (1-Real.cos z) c0) with h | h
  · rw [min_eq_left h] at he
    have hh := mul_le_mul_of_nonneg_left he (by norm_num [m] : 0≤ m)
    dsimp [linear] at hh hax
    nlinarith
  · rw [min_eq_right h] at he
    have hh := mul_le_mul_of_nonneg_left he (by norm_num [m] : 0≤ m)
    dsimp [linear] at hh hdiag
    nlinarith

theorem outer_lower (s : State) (hs : s.branch.type≠0) {d : ℝ} (hd : |d|≤frameCap) :
    (9/100)*|d|≤zeroError s d := by
  rcases le_total 0 d with hp | hn
  · simpa [abs_of_nonneg hp] using positive_lower s ⟨hp,(le_abs_self d).trans hd⟩
  · have hz : -d∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs d).trans hd⟩
    simpa [abs_of_nonpos hn] using negative_outer_lower s hs hz

lemma negative_large_target (s : State) (hb : (1/2:ℝ)≤ s.b) {z : ℝ}
    (hz : z∈Icc 0 frameCap) : -(4/25)*z≤zeroError s (-z) := by
  have ht := transport_trig hz
  have hsin := sine_linear hz
  have hcos := cosine_loss_linear hz
  have hA : (847/800:ℝ)≤ s.a+1/2 := by linarith [primary_lower s]
  have hp := mul_le_mul hA hsin (by linarith [hz.1] : 0≤(23/25)*z) (by linarith [primary_lower s])
  have hdrop := mul_nonneg (sub_nonneg.mpr hb) hcos.1
  rw [negative_identity s hz]
  dsimp [m]
  nlinarith

theorem large_target_lower (s : State) (hb : (1/2:ℝ)≤ s.b) {d : ℝ}
    (hd : |d|≤frameCap) : -(4/25)*|d|≤zeroError s d := by
  rcases le_total 0 d with hp | hn
  · have hh := positive_lower s ⟨hp,(le_abs_self d).trans hd⟩
    rw [abs_of_nonneg hp]
    linarith
  · have hz : -d∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs d).trans hd⟩
    simpa [abs_of_nonpos hn] using negative_large_target s hb hz

theorem return_allowance {v u w : ℝ} (hu : u∈Icc 0 frameCap)
    (hspan : |v+u+w|≤frameCap) :
    (9/50)*frameCost u-(9/100)*(|v|+|w|)≤(9/50)*frameCost |v+u+w| := by
  have hh := GlobalEH.frameCost_increment
    (show |u|≤frameCap by simpa [abs_of_nonneg hu.1] using hu.2) hspan
  rw [abs_of_nonneg hu.1] at hh
  have he : u-(v+u+w)=-(v+w) := by ring
  rw [he,abs_neg] at hh
  have htri := abs_add_le v w
  linarith

end SquaresInCircles.Eight.GlobalGA.Target
