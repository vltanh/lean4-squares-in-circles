module

public import SquaresInCircles.Eight.Owners.EH.HighRestriction
public import SquaresInCircles.Eight.Owners.GA.Target.OuterSupport

/-!
# Eight squares: the complete original high-GA three-edge path with a large target

Both original zero owners, every error sign, both target
radial kinds, and all original chart markers remain in the statement.
-/

section
/-!
## The zero errors pay for the return-charge variation

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
end
end
end

section
/-!
## The high GA axis and the three-edge force collection

The two zero projections keep their owner and rotating endpoint. The assumption that the target is
large rules out GA2 and a nonpositive GA3 directly, before any support reduction
(`original_GA_domain`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.Target
open FramePair ZeroPrimary FrameCircleArc GlobalZeroSign GlobalOuterAnchor

def pathCharge (h b : State) (v u w : ℝ) : ℝ :=
  Real.pi/2+v+u+w+unsigned h+unsigned b

theorem original_GA_domain (g a : State) (p : Bool) {u : ℝ}
    (hu : |u|≤frameCap) (hg : transverse g≤0) (ha : (1/2:ℝ)≤transverse a)
    (hGA : g.Feasible a (rightOwner p) (Real.pi/2+u)) :
    p=true ∧ 0<u ∧ GlobalOuterAnchor.width u≤g.a+a.a*Real.sin u-a.b*Real.cos u := by
  have hay : transverse a=a.b := transverse_of_nonneg a (by linarith)
  have hab : (1/2:ℝ)≤a.b := by simpa only [hay] using ha
  have hm := (right_margin g a p hu hg).1 hGA
  have hp : p=true := by
    cases hp : p
    · have hnorm := GlobalQuarterSign.state_norm_sq g
      have hproj := FrameCoreArc.projection_lt (a:=g.b) (b:=g.a)
        (by norm_num : (0:ℝ)<283/200) (by nlinarith) u
      simp only [rightProjection,hp,Bool.false_eq_true,ite_false,hay] at hm
      have hw := width_ge_one hu
      linarith
    · rfl
  rw [hp] at hm
  simp only [rightProjection,ite_true,hay] at hm
  have hpos : 0<u := by
    by_contra! hn
    have hz : -u∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs u).trans hu⟩
    have ht := CommonQuarter.positive_trig (x:=-u) (by simpa only [frameCap] using hz)
    have hcos : 0≤Real.cos (-u) := by linarith [ht.1]
    have hA : 1≤a.a+1/2 := by linarith [primary_lower a]
    have hB : 1≤a.b+1/2 := by linarith
    have hsine := mul_le_mul_of_nonneg_right hA ht.2.2.1
    have hcosine := mul_le_mul_of_nonneg_right hB hcos
    have he : GlobalOuterAnchor.width u=(1+Real.cos (-u)+Real.sin (-u))/2 := by
      have heq : u=-(-u) := by ring
      conv_lhs => rw [heq]
      rw [GlobalOuterAnchor.width,Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg ht.2.2.1]
    have hsin : Real.sin u=-Real.sin (-u) := by simp
    have hcos' : Real.cos u=Real.cos (-u) := by simp
    rw [he,hsin,hcos'] at hm
    have hsum := ht.2.2.2.2.2
    have hga := (coordinates g).2.1
    nlinarith
  exact ⟨hp,hpos,hm⟩

theorem zero_error_separator (h g : State) (p : Bool) {v : ℝ}
    (hHG : GlobalOuterAnchor.width v≤GlobalEH.zeroProjection h g p v) :
    zeroError (if p then h else g) v≤v+m*(h.b+g.b-1) := by
  cases p <;> dsimp [GlobalEH.zeroProjection,zeroError,m] at * <;> nlinarith

theorem path_floor (h g a b : State) (p r : Bool) {v u w : ℝ}
    (hh : h.branch.type≠0) (hb : b.branch.type≠0)
    (hHG : GlobalOuterAnchor.width v≤GlobalEH.zeroProjection h g p v)
    (hAB : GlobalOuterAnchor.width w≤GlobalEH.zeroProjection a b r w) :
    Real.pi/2+u+2*m-m*g.b-m*a.b+
      zeroError (if p then h else g) v+zeroError (if r then a else b) w≤
        pathCharge h b v u w := by
  have hH := marker_floor h hh
  have hB := marker_floor b hb
  have hzH := zero_error_separator h g p hHG
  have hzA := zero_error_separator a b r hAB
  dsimp [pathCharge]
  linarith

theorem outer_domain (g a : State) (hg : g.branch.type≠0) (ha : a.branch.type≠0)
    (hb : (1/2:ℝ)≤a.b) {u : ℝ} (hu : u∈Icc 0 frameCap)
    (hGA : GlobalOuterAnchor.width u≤g.a+a.a*Real.sin u-a.b*Real.cos u) : Outer.Domain u := by
  have hchartA := state_outer_chart a ha
  have hchartG := state_outer_chart g hg
  have hhalf : (1/2:ℝ)∈Icc 0 c0 := ⟨by norm_num,by linarith [c0_bounds.1]⟩
  have haA := A_antitone hhalf hchartA.2 hb
  rw [Outer.A_half,←hchartA.1] at haA
  have hgA := (A_bounds hchartG.2).2
  rw [←hchartG.1] at hgA
  have ht := transport_trig hu
  have hA := mul_le_mul_of_nonneg_right haA ht.2.2.1
  have hB := mul_le_mul_of_nonneg_right hb (by linarith [ht.1] : 0≤Real.cos u)
  dsimp [GlobalOuterAnchor.width] at hGA
  rw [abs_of_nonneg ht.2.2.1] at hGA
  refine ⟨hu,?_⟩
  dsimp [Outer.K,Outer.P]
  nlinarith

theorem outer_force (h g a b : State) (p r : Bool) {v u w : ℝ}
    (hh : h.branch.type≠0) (hg : g.branch.type≠0)
    (ha : a.branch.type≠0) (hb : b.branch.type≠0) (haB : (1/2:ℝ)≤a.b)
    (hu : u∈Icc 0 frameCap)
    (hHG : GlobalOuterAnchor.width v≤GlobalEH.zeroProjection h g p v)
    (hGA : GlobalOuterAnchor.width u≤g.a+a.a*Real.sin u-a.b*Real.cos u)
    (hAB : GlobalOuterAnchor.width w≤GlobalEH.zeroProjection a b r w) :
    Real.pi/2+u+m*(2-Outer.Y u)+
      zeroError (if p then h else g) v+zeroError (if r then a else b) w≤
        pathCharge h b v u w := by
  have hd := outer_domain g a hg ha haB hu hGA
  have hp := Outer.weight_pos hd
  have hfloor := path_floor (u:=u) h g a b p r hh hb hHG hAB
  have hG := state_support g (Outer.weight u) m
  have hA := Outer.target_support a ha haB hd
  have hsep := mul_le_mul_of_nonneg_left hGA hp.le
  have hopt := Outer.optimizing_identity hd
  have ht := transport_trig hu
  have hw : GlobalOuterAnchor.width u=(1+Real.cos u+Real.sin u)/2 := by
    simp only [GlobalOuterAnchor.width,abs_of_nonneg ht.2.2.1]
  have hcollect : Outer.weight u*GlobalOuterAnchor.width u+(Outer.weight u+m)/2-
      (Outer.weight u*(Outer.S-1/2)*Real.sin u+(m-Outer.weight u*Real.cos u)/2)=
        Outer.weight u*Outer.K u := by
    rw [hw]
    dsimp [Outer.K,Outer.P]
    ring
  nlinarith only [hfloor,hG,hA,hsep,hopt,hcollect]

theorem core_force (h g a b : State) (p r : Bool) {v u w : ℝ}
    (hh : h.branch.type≠0) (hb : b.branch.type≠0) (haB : (1/2:ℝ)≤a.b)
    (hu : u∈Icc 0 frameCap)
    (hHG : GlobalOuterAnchor.width v≤GlobalEH.zeroProjection h g p v)
    (hGA : GlobalOuterAnchor.width u≤g.a+a.a*Real.sin u-a.b*Real.cos u)
    (hAB : GlobalOuterAnchor.width w≤GlobalEH.zeroProjection a b r w) :
    Real.pi/2+Core.base+Core.error a u+
      zeroError (if p then h else g) v+zeroError (if r then a else b) w≤
        pathCharge h b v u w := by
  have hfloor := path_floor (u:=u) h g a b p r hh hb hHG hAB
  have hsep := Core.error_separator g a hu hGA
  have hG := state_support g Core.weight m
  have hB := mul_le_mul_of_nonneg_left haB
    (by norm_num [Core.weight,m] : 0≤Core.weight-m)
  dsimp [Core.base,Core.weight,m] at *
  linarith

end SquaresInCircles.Eight.GlobalGA.Target
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.Target
open FramePair ZeroPrimary GlobalOuterAnchor

theorem outer_path (h g a b : State) (p r : Bool) {v u w : ℝ}
    (hh : h.branch.type≠0) (hg : g.branch.type≠0)
    (ha : a.branch.type≠0) (hb : b.branch.type≠0) (haB : (1/2:ℝ)≤a.b)
    (hv : |v|≤frameCap) (hu : u∈Icc 0 frameCap) (hw : |w|≤frameCap)
    (hspan : |v+u+w|≤frameCap)
    (hHG : GlobalOuterAnchor.width v≤GlobalEH.zeroProjection h g p v)
    (hGA : GlobalOuterAnchor.width u≤g.a+a.a*Real.sin u-a.b*Real.cos u)
    (hAB : GlobalOuterAnchor.width w≤GlobalEH.zeroProjection a b r w) :
    (11/4:ℝ)<pathCharge h b v u w+(9/50)*frameCost |v+u+w| := by
  have hforce := outer_force h g a b p r hh hg ha hb haB hu hHG hGA hAB
  have hzH : (9/100)*|v|≤zeroError (if p then h else g) v := by
    cases p
    · exact outer_lower g hg hv
    · exact outer_lower h hh hv
  have hzA : (9/100)*|w|≤zeroError (if r then a else b) w := by
    cases r
    · exact outer_lower b hb hw
    · exact outer_lower a ha hw
  have hallow := return_allowance hu hspan
  have hj := Outer.scalar_lower (outer_domain g a hg ha haB hu hGA)
  have hpi := Arithmetic.pi_hand_enclosure.1
  dsimp [Outer.J,frameCost] at *
  linarith

theorem core_path (h g a b : State) (p r : Bool) {v u w : ℝ}
    (hh : h.branch.type≠0) (hg : g.branch.type≠0)
    (ha : a.branch.type=0) (hb : b.branch.type≠0) (haB : (1/2:ℝ)≤a.b)
    (hv : |v|≤frameCap) (hu : u∈Icc 0 frameCap) (hw : |w|≤frameCap)
    (hspan : |v+u+w|≤frameCap)
    (hHG : GlobalOuterAnchor.width v≤GlobalEH.zeroProjection h g p v)
    (hGA : GlobalOuterAnchor.width u≤g.a+a.a*Real.sin u-a.b*Real.cos u)
    (hAB : GlobalOuterAnchor.width w≤GlobalEH.zeroProjection a b r w) :
    (11/4:ℝ)<pathCharge h b v u w+(9/50)*frameCost |v+u+w| := by
  have hul := Core.angle_lower g a ha haB hu hGA
  have herror := Core.error_lower a ha ⟨hul.le,hu.2⟩
  have hforce := core_force h g a b p r hh hb haB hu hHG hGA hAB
  have hzH : (9/100)*|v|≤zeroError (if p then h else g) v := by
    cases p
    · exact outer_lower g hg hv
    · exact outer_lower h hh hv
  have hzA : -(4/25)*|w|≤zeroError (if r then a else b) w := by
    cases r
    · exact (show -(4/25)*|w|≤(9/100)*|w| by linarith [abs_nonneg w]).trans
        (outer_lower b hb hw)
    · exact large_target_lower a haB hw
  have hallow := return_allowance hu hspan
  have hcost : 0≤frameCost u := frameCost_nonneg
    ⟨hu.1,by dsimp [frameCap] at hu; linarith [hu.2,Real.pi_gt_three]⟩
  have hbase := Core.base_lower
  have hpi := Arithmetic.pi_hand_enclosure.1
  dsimp [frameCap] at hw
  linarith

theorem original_path (h g a b : State) {v u w : ℝ}
    (hhOuter : h.branch.type≠0) (hgOuter : g.branch.type≠0) (hbOuter : b.branch.type≠0)
    (hh : 0≤transverse h) (hg : transverse g≤0)
    (ha : (1/2:ℝ)≤transverse a) (hb : transverse b≤0)
    (hv : |v|≤frameCap) (hu : |u|≤frameCap) (hw : |w|≤frameCap)
    (hspan : |v+u+w|≤frameCap)
    (jH jG jA : Fin 4) (hHowner : jH=0 ∨ jH=2)
    (hGowner : jG=2 ∨ jG=3) (hAowner : jA=0 ∨ jA=2)
    (hHG : h.Feasible g jH v)
    (hGA : g.Feasible a jG (Real.pi/2+u))
    (hAB : a.Feasible b jA w) :
    (11/4:ℝ)<pathCharge h b v u w+(9/50)*frameCost |v+u+w| := by
  obtain ⟨p,hp⟩ : ∃p : Bool,rightOwner p=jG := by
    rcases hGowner with rfl | rfl
    · exact ⟨false,rfl⟩
    · exact ⟨true,rfl⟩
  have hd := original_GA_domain g a p hu hg ha (by simpa [hp] using hGA)
  have hup : u∈Icc 0 frameCap := ⟨hd.2.1.le,(le_abs_self u).trans hu⟩
  have hay : transverse a=a.b := transverse_of_nonneg a (by linarith)
  have hab : (1/2:ℝ)≤a.b := by simpa only [hay] using ha
  obtain ⟨z,hz⟩ : ∃z : Bool,GlobalEH.zeroOwner z=jH := by
    rcases hHowner with rfl | rfl
    · exact ⟨false,rfl⟩
    · exact ⟨true,rfl⟩
  obtain ⟨r,hr⟩ : ∃r : Bool,GlobalEH.zeroOwner r=jA := by
    rcases hAowner with rfl | rfl
    · exact ⟨false,rfl⟩
    · exact ⟨true,rfl⟩
  have hHG' := (GlobalEH.zeroProjection_margin h g z hv hh hg).1 (by simpa [hz] using hHG)
  have hAB' := (GlobalEH.zeroProjection_margin a b r hw (by linarith) hb).1 (by simpa [hr] using hAB)
  by_cases hcore : a.branch.type=0
  · exact core_path h g a b z r hhOuter hgOuter hcore hbOuter hab hv hup hw hspan
      hHG' hd.2.2 hAB'
  · exact outer_path h g a b z r hhOuter hgOuter hcore hbOuter hab hv hup hw hspan
      hHG' hd.2.2 hAB'

end SquaresInCircles.Eight.GlobalGA.Target
end
end
end
