module

public import SquaresInCircles.Eight.Owners.All.HighSecondary
public import SquaresInCircles.Eight.Owners.All.HighNegativeOuter
public import SquaresInCircles.Eight.Owners.All.HighPositiveTransfer
public import SquaresInCircles.Eight.Owners.All.HighZeroPositive

/-!
# Eight squares: the complete common charge of every original high quarter

Both original high owners, every original error sign, every outer
target, and both positive-core target pieces are covered.  Equality
recovers zero error, the original high marker, and the original tight
axis projection.  No charge bound on another edge is assumed.
-/

section
/-!
## No long outer bridge from a high source

With the single multiplier `longLambda = 79/100` the source expression of the marker charge
increases across the whole high arc (`longSource_monotone`, `high_source_long`). A circle support
for a high target and concavity at the endpoints for a middle target (`high_target_long`,
`middle_target_long`) bound the marker charge `augmentedUnsigned` from below on the whole interval
`1/2 ≤ z ≤ 7/10` (`high_source_long_old`), so the cycle cap fails there
(`high_source_long_false`).
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalAllHigh.Bridge

open FramePair ZeroPrimary GlobalOuterAnchor GlobalZeroSign FrameCircleArc FrameLowArc FrameMidArc

def longLambda : ℝ := 79/100
def longScalar (z : ℝ) : ℝ := 733/500-z-(37/80)*Real.cos z+(891/1000)*Real.sin z
def longScalarD (z : ℝ) : ℝ := -1+(37/80)*Real.sin z+(891/1000)*Real.cos z
def longSource (z b : ℝ) : ℝ :=
  (FrameHighArc.u-longLambda*Real.cos z)*A b+
    (longLambda*Real.sin z-FrameHighArc.v)*b

theorem long_trig {z : ℝ} (hz : z∈Icc (1/2:ℝ) frameCap) :
    (479/1000:ℝ)<Real.sin z ∧ Real.cos z<439/500 := by
  have hz2 : z≤7/10 := by have h := hz.2; simp only [frameCap] at h; exact h
  have hp : z≤Real.pi/2 := by linarith [Real.pi_gt_three]
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos] : -(Real.pi/2)≤(1/2:ℝ)) hp hz.1
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi
    (by norm_num : (0:ℝ)≤1/2) (by linarith [Real.pi_gt_three]) hz.1
  have hsl := Real.sin_ge_sub_cube (show (0:ℝ)≤1/2 by norm_num)
  have hcu := cos_upper_four (show (0:ℝ)≤1/2 by norm_num)
  norm_num at hsl hcu
  constructor <;> linarith

theorem longScalar_deriv (z : ℝ) : HasDerivAt longScalar (longScalarD z) z := by
  have h1 : HasDerivAt (fun x : ℝ => 733/500-x) (-1) z := (hasDerivAt_id' z).const_sub _
  have h2 : HasDerivAt (fun x => 733/500-x-(37/80)*Real.cos x) (-1-(37/80)*(-Real.sin z)) z :=
    h1.fun_sub ((Real.hasDerivAt_cos z).const_mul (37/80))
  have h3 : HasDerivAt (fun x => 733/500-x-(37/80)*Real.cos x+(891/1000)*Real.sin x)
      (-1-(37/80)*(-Real.sin z)+(891/1000)*Real.cos z) z :=
    h2.fun_add ((Real.hasDerivAt_sin z).const_mul (891/1000))
  exact h3.congr_deriv (by dsimp [longScalarD]; ring)

theorem longScalar_concave : ConcaveOn ℝ (Icc (1/2:ℝ) frameCap) longScalar := by
  apply concave_of_deriv2 (fun z _ => longScalar_deriv z)
    (f' := longScalarD)
    (f'' := fun z => (37/80)*Real.cos z-(891/1000)*Real.sin z)
  · intro z hz
    have h1 : HasDerivAt (fun x : ℝ => -1+(37/80)*Real.sin x) ((37/80)*Real.cos z) z :=
      ((Real.hasDerivAt_sin z).const_mul (37/80)).const_add (-1)
    have h2 : HasDerivAt (fun x : ℝ => -1+(37/80)*Real.sin x+(891/1000)*Real.cos x)
        ((37/80)*Real.cos z+(891/1000)*(-Real.sin z)) z :=
      h1.fun_add ((Real.hasDerivAt_cos z).const_mul (891/1000))
    exact h2.congr_deriv (by ring)
  · intro z hz
    have ht := long_trig hz
    linarith

theorem longScalar_endpoints :
    (197/200:ℝ)<longScalar (1/2) ∧ (197/200:ℝ)<longScalar frameCap := by
  have hs0 := sin_lower_seven (show (0:ℝ)≤1/2 by norm_num)
  have hc0 := Arithmetic.cos_le_cos8 (show (0:ℝ)≤1/2 by norm_num)
  have hs1 := sin_lower_seven (show (0:ℝ)≤frameCap by norm_num [frameCap])
  have hc1 := Arithmetic.cos_le_cos8 (show (0:ℝ)≤frameCap by norm_num [frameCap])
  norm_num [Arithmetic.cos8,frameCap] at hs0 hc0 hs1 hc1
  constructor <;> dsimp [longScalar,frameCap] <;> linarith

theorem longScalar_lower {z : ℝ} (hz : z∈Icc (1/2:ℝ) frameCap) :
    (197/200:ℝ)<longScalar z :=
  concave_gt_of_endpoints longScalar_concave hz longScalar_endpoints.1 longScalar_endpoints.2

theorem longSource_monotone {z : ℝ} (hz : z∈Icc (1/2:ℝ) frameCap) :
    MonotoneOn (longSource z) (Icc b2 c0) := by
  have ht := transport_trig (show z∈Icc 0 frameCap from ⟨by linarith [hz.1],hz.2⟩)
  have hs := (long_trig hz).1
  have hcoef : 0≤longLambda*Real.cos z-FrameHighArc.u := by
    dsimp [longLambda,FrameHighArc.u]
    linarith [ht.1]
  apply monoOn_of_hasDeriv_nonneg
  · intro b hb
    exact (linear_hasDerivAt ⟨b2_mem.1.trans hb.1,hb.2⟩
      (FrameHighArc.u-longLambda*Real.cos z)
      (longLambda*Real.sin z-FrameHighArc.v)).continuousAt.continuousWithinAt
  · intro b hb
    exact linear_hasDerivAt ⟨b2_mem.1.trans hb.1.le,hb.2.le⟩
      (FrameHighArc.u-longLambda*Real.cos z)
      (longLambda*Real.sin z-FrameHighArc.v)
  · intro b hb
    have hr := FrameHighArc.slope_high_bounds (Ioo_subset_Icc_self hb)
    have hprod := mul_nonneg hcoef (show 0 ≤ slope b-(149/250:ℝ) by linarith)
    have hAd : Ad b=-FrameLowArc.slope b := by
      simp only [Ad,FrameLowArc.slope]; ring
    rw [hAd]
    dsimp [longLambda,FrameHighArc.u,FrameHighArc.v] at *
    nlinarith only [hprod,ht.1,hs]

theorem high_source_long (s : State) (hs : s.branch=.high)
    {z : ℝ} (hz : z∈Icc (1/2:ℝ) frameCap) :
    -FrameHighArc.k+(FrameHighArc.u-longLambda*Real.cos z)*a2+
      (longLambda*Real.sin z-FrameHighArc.v)*b2≤
    -unsigned s-longLambda*s.a*Real.cos z+longLambda*s.b*Real.sin z := by
  have hchart := FrameHighArc.state_high_chart s hs
  have hm := longSource_monotone hz ⟨le_rfl,b2_mem.2⟩ hchart.2 hchart.2.1
  rw [unsigned_arc s (by simp [hs,Branch.type]),hs,arcMarker_high,hchart.1]
  dsimp [longSource,FrameHighArc.H] at hm ⊢
  rw [A_b2] at hm
  linarith

theorem middle_target_long (t : State) (ht : t.branch=.middle) :
    (6/125:ℝ)<unsigned t-longLambda*t.b := by
  have hchart := state_mid_chart t ht
  have hh := linear_endpoint_lower (p := FrameMidArc.p) (q := FrameMidArc.q-longLambda)
    (by norm_num [FrameMidArc.p]) b1_mem.1 b2_mem.2 hchart.2
  have he0 : (6/125:ℝ)<FrameMidArc.M b1-longLambda*b1 := by
    rw [FrameMidArc.M_b1]
    dsimp [longLambda]
    linarith [FrameMidArc.M_endpoints.1,b1_precise.2]
  have he1 : (6/125:ℝ)<FrameMidArc.M b2-longLambda*b2 := by
    rw [FrameMidArc.M_b2]
    dsimp [longLambda]
    linarith [FrameMidArc.M_endpoints.2.2.1,b2_precise.2]
  rw [unsigned_arc t (by simp [ht,Branch.type]),ht,arcMarker_middle]
  dsimp [FrameMidArc.M] at he0 he1 ⊢
  rcases le_total (linear FrameMidArc.p (FrameMidArc.q-longLambda) b1)
      (linear FrameMidArc.p (FrameMidArc.q-longLambda) b2) with hmin | hmin
  · rw [min_eq_left hmin] at hh
    dsimp [linear] at hh
    linarith
  · rw [min_eq_right hmin] at hh
    dsimp [linear] at hh
    linarith

theorem high_target_long (t : State) (ht : t.branch=.high) :
    FrameHighArc.k+(FrameHighArc.u+longLambda-FrameHighArc.v)/2-
      137607/100000<unsigned t-longLambda*t.b := by
  have hh := circle_product_support t
    (f := FrameHighArc.u) (g := longLambda-FrameHighArc.v)
    (K := 137607/100000) (by norm_num)
    (by norm_num [Q0,FrameHighArc.u,FrameHighArc.v,longLambda])
  have hstrict : FrameHighArc.u*t.a+(longLambda-FrameHighArc.v)*t.b<
      137607/100000-(FrameHighArc.u+longLambda-FrameHighArc.v)/2 := by
    have hh' := circle_product_support t
      (f := FrameHighArc.u) (g := longLambda-FrameHighArc.v)
      (K := 688031/500000) (by norm_num)
      (by norm_num [Q0,FrameHighArc.u,FrameHighArc.v,longLambda])
    linarith
  rw [unsigned_arc t (by simp [ht,Branch.type]),ht,arcMarker_high]
  rw [(FrameHighArc.state_high_chart t ht).1] at hstrict
  dsimp [FrameHighArc.H]
  linarith

theorem long_dual_coefficients :
    (733/500:ℝ)<Real.pi/2+(longLambda-9/50)/2+
      FrameHighArc.u*a2-FrameHighArc.v*b2+
      (FrameHighArc.u+longLambda-FrameHighArc.v)/2-137607/100000 ∧
    (1459/1000:ℝ)<Real.pi/2+(longLambda-9/50)/2+
      FrameHighArc.u*a2-FrameHighArc.v*b2-473/500+6/125 ∧
    -(37/80:ℝ)≤(longLambda+9/50)/2-longLambda*a2 ∧
    (891/1000:ℝ)≤(longLambda+9/50)/2+longLambda*b2 := by
  have hp := Arithmetic.pi_hand_enclosure.1
  have ha := a2_bounds
  have hb := b2_precise
  dsimp [longLambda,FrameHighArc.u,FrameHighArc.v]
  refine ⟨?_,?_,?_,?_⟩ <;> linarith

theorem high_source_long_old (s t : State) (hs : s.branch=.high)
    {z : ℝ} (hz : z∈Icc (1/2:ℝ) frameCap)
    (hm : GlobalOuterAnchor.width (-z)≤ s.a*Real.cos z-s.b*Real.sin z+t.b) :
    (t.branch=.high → (197/200:ℝ)<augmentedUnsigned s t (-z)) ∧
    (t.branch=.middle → (489/500:ℝ)<augmentedUnsigned s t (-z)) := by
  have tr := transport_trig (show z∈Icc 0 frameCap from ⟨by linarith [hz.1],hz.2⟩)
  have hp := mul_le_mul_of_nonneg_left hm (show 0≤longLambda by norm_num [longLambda])
  have hsource := high_source_long s hs hz
  have hcos := mul_le_mul_of_nonneg_right long_dual_coefficients.2.2.1
    (show 0≤Real.cos z by linarith [tr.1])
  have hsin := mul_le_mul_of_nonneg_right long_dual_coefficients.2.2.2 tr.2.2.1
  have hscalar := longScalar_lower hz
  rw [GlobalOuterAnchor.width,Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg tr.2.2.1] at hp
  constructor
  · intro ht
    have htarget := high_target_long t ht
    have hconstant := long_dual_coefficients.1
    dsimp [augmentedUnsigned,unsignedCharge,frameCost,longScalar] at *
    rw [abs_neg,abs_of_nonneg (show 0≤z by linarith [hz.1])]
    nlinarith only [hp,hsource,htarget,hcos,hsin,hscalar,hconstant]
  · intro ht
    have htarget := middle_target_long t ht
    have hk := FrameHighArc.k_bounds.2.1
    have hconstant := long_dual_coefficients.2.1
    dsimp [augmentedUnsigned,unsignedCharge,frameCost,longScalar] at *
    rw [abs_neg,abs_of_nonneg (show 0≤z by linarith [hz.1])]
    nlinarith only [hp,hsource,htarget,hcos,hsin,hscalar,hconstant,hk]

/-- On the long interval `1/2 ≤ z ≤ frameCap`, a high source and a middle or high target do not
satisfy both the weak projection and the cycle cap. -/
theorem high_source_long_false (s t : State) (hs : s.branch=.high)
    (ht : t.branch=.middle ∨ t.branch=.high)
    {z : ℝ} (hz : z∈Icc (1/2:ℝ) frameCap)
    (hm : GlobalOuterAnchor.width (-z)≤ s.a*Real.cos z-s.b*Real.sin z+t.b)
    (hc : augmentedUnsigned s t (-z)<cap-bonus s.branch.type t.branch.type) : False := by
  have hh := high_source_long_old s t hs hz hm
  rcases ht with ht | ht
  · have hm := hh.2 ht
    norm_num [hs,ht,Branch.type,cap,bonus,tau] at hc
    linarith
  · have hm := hh.1 ht
    norm_num [hs,ht,Branch.type,cap,bonus,tau] at hc
    linarith

end SquaresInCircles.Eight.GlobalAllHigh.Bridge
end
end
end

section
/-!
## A core target with positive transverse coordinate

A negative primary projection onto a core target with positive transverse coordinate puts the
target on its flat side, `t.a = 7/12`, at an angle below `1/2` (`negative_core_domain`). For
angles at least `3/10` the same projection puts the outer source below the transverse coordinate
`33/100` (`negative_core_small_source`), where its marker correction pays the uniform scalar loss;
so the quarter charge exceeds `kappa` (`negative_primary_core`).
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalAllHigh

open FramePair ZeroPrimary FrameCircleArc FrameLowArc GlobalZeroSign
open GlobalOuterAnchor GlobalQuarterSign

theorem negative_core_domain (s t : State) (htCore : t.branch.type=0)
    (ht : 0<transverse t) {z : ℝ} (hz : z∈Icc 0 frameCap)
    (hm : GlobalOuterAnchor.width (-z)≤ s.a+t.a*Real.sin (-z)-transverse t*Real.cos (-z)) :
    t.a=7/12 ∧ z<1/2 := by
  have hy := transverse_of_nonneg t ht.le
  have tr := transport_trig hz
  have hm' : (1+Real.cos z+Real.sin z)/2≤ s.a-t.a*Real.sin z-t.b*Real.cos z := by
    simp only [GlobalOuterAnchor.width,Real.sin_neg,Real.cos_neg,abs_neg,
      abs_of_nonneg tr.2.2.1,hy,mul_neg] at hm
    linarith
  have hd := one_negative_negative_domain t s hz hm'
  exact ⟨(CommonQuarter.core_small_side (FrameCoreArc.state_core_chart t htCore) hd.1).1,hd.2⟩

def coreSourceThreshold (z : ℝ) : ℝ :=
  1/2+(1/2)*Real.cos z+(13/12)*Real.sin z

theorem coreSourceThreshold_monotone :
    MonotoneOn coreSourceThreshold (Icc 0 frameCap) := by
  have hd (z : ℝ) : HasDerivAt coreSourceThreshold
      (-(1/2)*Real.sin z+(13/12)*Real.cos z) z := by
    have h := ((hasDerivAt_const z (1/2:ℝ)).add
      ((Real.hasDerivAt_cos z).const_mul (1/2))).add
      ((Real.hasDerivAt_sin z).const_mul (13/12))
    convert h using 1
    · funext y
      simp only [coreSourceThreshold,Pi.add_apply]
    · ring
  apply monoOn_of_hasDeriv_nonneg
  · exact fun z _ => (hd z).continuousAt.continuousWithinAt
  · exact fun z _ => hd z
  · intro z hz
    have tr := transport_trig (Ioo_subset_Icc_self hz)
    linarith [tr.1,tr.2.2.2.1]

theorem negative_core_small_source (s t : State) (hs : s.branch.type≠0)
    (ht : 0<transverse t) (hflat : t.a=7/12)
    {z : ℝ} (hz : z∈Icc (3/10:ℝ) frameCap)
    (hm : GlobalOuterAnchor.width (-z)≤ s.a+t.a*Real.sin (-z)-transverse t*Real.cos (-z)) :
    s.b<33/100 := by
  have hz' : z∈Icc 0 frameCap := ⟨by linarith [hz.1],hz.2⟩
  have tr := transport_trig hz'
  have hyprod := mul_pos ht (show 0<Real.cos z by linarith [tr.1])
  have hmargin : coreSourceThreshold z<s.a := by
    simp only [GlobalOuterAnchor.width,Real.sin_neg,Real.cos_neg,abs_neg,
      abs_of_nonneg tr.2.2.1,hflat,mul_neg] at hm
    dsimp [coreSourceThreshold]
    linarith
  have hmono := coreSourceThreshold_monotone
    (by norm_num [frameCap] : (3/10:ℝ)∈Icc 0 frameCap) hz' hz.1
  have hsin := Real.sin_ge_sub_cube (show (0:ℝ)≤3/10 by norm_num)
  have hcos := Real.one_sub_sq_div_two_le_cos (x := (3/10:ℝ))
  have ha : (10381/8000:ℝ)<s.a := by
    dsimp [coreSourceThreshold] at hmono hmargin
    norm_num at hsin hcos
    linarith
  have hc := s.outer_eq hs
  by_contra! hb
  have hsource : (14381/8000:ℝ)^2<(s.a+1/2)^2 := by
    nlinarith [s.a_pos]
  have htangent : (83/100:ℝ)^2≤(s.b+1/2)^2 := by
    nlinarith [s.b_nonneg]
  norm_num [Q0] at hc hsource htangent
  linarith

theorem negative_primary_core (s t : State) (hs : s.branch.type≠0)
    (htCore : t.branch.type=0) (ht : 0<transverse t)
    {z : ℝ} (hz : z∈Ioc 0 frameCap)
    (hm : GlobalOuterAnchor.width (-z)≤ s.a+t.a*Real.sin (-z)-transverse t*Real.cos (-z)) :
    kappa<quarterCharge s (transverse t) (-z) := by
  have hd := negative_core_domain s t htCore ht (Ioc_subset_Icc_self hz) hm
  have hmFlat : GlobalOuterAnchor.width (-z)≤ s.a+(7/12)*Real.sin (-z)-transverse t*Real.cos (-z) := by
    simpa only [hd.1] using hm
  have htransfer := core_primary_scaled_transfer s hs ⟨hz.1.le,hd.2.le⟩ hmFlat
  have hc : 0<Real.cos z := by linarith [(transport_trig (Ioc_subset_Icc_self hz)).1]
  have hscalar : 0<coreL z+rho*J s := by
    by_cases hsmall : z≤3/10
    · have hL := coreL_positive_short ⟨hz.1,hsmall⟩
      have hJ := mul_nonneg (show 0≤rho by norm_num [rho]) (J_nonnegative s hs)
      linarith
    · have hsource := negative_core_small_source s t hs ht hd.1
        ⟨(lt_of_not_ge hsmall).le,hz.2⟩ hm
      have hJ := J_small_transverse s hs hsource.le
      have hL := coreL_lower ⟨hz.1.le,hd.2.le⟩
      dsimp [rho]
      linarith
  have hpositive := (mul_pos hscalar hc).trans_le htransfer
  have hgap := (mul_pos_iff_of_pos_right hc).1 hpositive
  linarith

end SquaresInCircles.Eight.GlobalAllHigh
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalAllHigh

open FramePair GlobalOuterAnchor

theorem primary_charge (s t : State) (hs : s.branch.type≠0)
    (ht : t.branch.type≠0 ∨ 0<transverse t) {d : ℝ}
    (hd : |d|≤frameCap)
    (hm : GlobalOuterAnchor.width d≤ s.a+t.a*Real.sin d-transverse t*Real.cos d) :
    kappa≤quarterCharge s (transverse t) d ∧
      (d≠0 → kappa<quarterCharge s (transverse t) d) := by
  by_cases hd0 : 0≤d
  · have hp := positive_primary_charge s t hs
      ⟨hd0,(le_abs_self d).trans hd⟩ hm
    exact ⟨hp.1,fun hne => hp.2 (lt_of_le_of_ne hd0 (Ne.symm hne))⟩
  · have hz : -d∈Ioc 0 frameCap := ⟨by linarith,(neg_le_abs d).trans hd⟩
    have hm' : GlobalOuterAnchor.width (-(-d))≤ s.a+t.a*Real.sin (-(-d))-
        transverse t*Real.cos (-(-d)) := by simpa only [neg_neg] using hm
    have hstrict : kappa<quarterCharge s (transverse t) d := by
      by_cases htCore : t.branch.type=0
      · have htpos : 0<transverse t := ht.resolve_left (fun hne => hne htCore)
        simpa only [neg_neg] using negative_primary_core s t hs htCore htpos hz hm'
      · simpa only [neg_neg] using negative_primary_outer s t hs htCore hz hm'
    exact ⟨hstrict.le,fun _ => hstrict⟩

/-- A high original owner has the common augmented primary charge.
The target disjunction is exactly what the all-high radial classifier
provides at H, A, and T. -/
theorem high_quarter_charge (s t : State) (hs : s.branch.type≠0)
    (hsy : transverse s≤0) (ht : t.branch.type≠0 ∨ 0<transverse t)
    {j : Fin 4} {d : ℝ} (hj : j=2 ∨ j=3) (hd : |d|≤frameCap)
    (hm : s.Feasible t j (Real.pi/2+d)) :
    kappa≤quarterCharge s (transverse t) d ∧
      (d≠0 → kappa<quarterCharge s (transverse t) d) := by
  rcases hj with rfl | rfl
  · have hmargin := (right_margin s t false hd hsy).1 (by
      simpa only [rightOwner,Bool.false_eq_true,ite_false] using hm)
    change GlobalOuterAnchor.width d≤ s.a*Real.cos d+s.b*Real.sin d-transverse t at hmargin
    exact secondary_charge s hs hd hmargin
  · have hmargin := (right_margin s t true hd hsy).1 (by
      simpa only [rightOwner,ite_true] using hm)
    change GlobalOuterAnchor.width d≤ s.a+t.a*Real.sin d-transverse t*Real.cos d at hmargin
    exact primary_charge s t hs ht hd hmargin

end SquaresInCircles.Eight.GlobalAllHigh
end
end
end
