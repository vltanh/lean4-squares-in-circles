module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneOppositePrimaryUpperAxial

/-!
# The exact angular-stationarity event of the exceptional upper owner

Uncompiled transcription of equations (44)--(46) in the three-family
note. At a stationary target coordinate the angular derivative is
bounded below by the displayed axial expression Omega. Its unique
zero is obtained from its two named rational endpoint signs.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.Opposite.Primary.Upper.Stationary
open CommonQuarter CorePairGeometry Arithmetic StationaryPrimitives
open SameContact (arc ratio)
open ShortWord.MixedQuarter.Reference

def targetU (B : ℝ) : ℝ := arc B+1/2
def targetV (B : ℝ) : ℝ := B+1/2
def targetProjection (B x : ℝ) : ℝ := targetU B*Real.cos x+targetV B*Real.sin x
def targetCharge (B : ℝ) : ℝ := t 1*targetU B-P 1*targetV B
def axisProjection (x : ℝ) : ℝ := (outerAxial+1/2)*Real.cos x+Real.sin x/2
def axisCharge : ℝ := t 1*(outerAxial+1/2)-P 1/2
def Omega (x : ℝ) : ℝ := 1-axisCharge*(1-Real.cos x/axisProjection x)
def Omega1 (x : ℝ) : ℝ := -axisCharge/(2*(axisProjection x)^2)
def IsEvent (s : ℝ) : Prop := s∈Ioo (9/100:ℝ) (134/1250) ∧ Omega s=0

theorem axisCharge_positive : 0<axisCharge := by
  norm_num [axisCharge,t,P]
  linarith [ShortOuterZero.fine_axial_bounds.1]

theorem projection_positive {B x : ℝ} (hB : B∈Icc 0 outerDiagonal) (hx : x∈Icc 0 (7/10)) :
    0<targetProjection B x ∧ Real.cos x<targetProjection B x := by
  have hh := SecondWord.SameZero.v_positive hB hx
  have he : targetProjection B x-Real.cos x=angleSpeed B x := by
    dsimp [targetProjection,targetU,targetV,angleSpeed,SecondWord.SameZero.v]
    ring
  have hc : 0<Real.cos x := by linarith [(positive_trig hx).1]
  exact ⟨by linarith,by linarith⟩

theorem axisProjection_positive {x : ℝ} (hx : x∈Icc 0 (7/10)) : 0<axisProjection x := by
  have hh := (projection_positive zero_mem hx).1
  simpa [targetProjection,targetU,targetV,axisProjection,SameContact.arc_zero] using hh

theorem axisProjection_hasDerivAt (x : ℝ) :
    HasDerivAt axisProjection (-(outerAxial+1/2)*Real.sin x+Real.cos x/2) x := by
  convert ((Real.hasDerivAt_cos x).const_mul (outerAxial+1/2)).add
    ((Real.hasDerivAt_sin x).div_const 2) using 1 <;> dsimp [axisProjection] <;> ring

theorem Omega_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    HasDerivAt Omega (Omega1 x) x := by
  have hp := axisProjection_positive hx
  convert ((((Real.hasDerivAt_cos x).div (axisProjection_hasDerivAt x) hp.ne').
    const_sub 1).const_mul axisCharge).const_sub 1 using 1
  · rfl
  · dsimp [Omega1]
    field_simp [hp.ne']
    dsimp [axisProjection]
    nlinarith [Real.sin_sq_add_cos_sq x]

theorem Omega_strictAnti : StrictAntiOn Omega (Icc (0:ℝ) (7/10)) := by
  have hm : StrictMonoOn (fun x => -Omega x) (Icc (0:ℝ) (7/10)) := by
    apply strictMonoOn_of_hasDeriv_pos
      (fun x hx => (Omega_hasDerivAt hx).neg.continuousAt.continuousWithinAt)
      (fun x hx => (Omega_hasDerivAt (Ioo_subset_Icc_self hx)).neg)
    intro x hx
    have hp := axisProjection_positive (Ioo_subset_Icc_self hx)
    have hh := div_pos axisCharge_positive
      (mul_pos (by norm_num : (0:ℝ)<2) (sq_pos_of_pos hp))
    simpa only [Omega1,neg_div,neg_neg] using hh
  intro x hx y hy hxy
  have hh := hm hx hy hxy
  linarith

def axisProjectionBox (x : ℝ) (hx : 0≤x) : Interval (axisProjection x) := by
  convert ((axial.add (Interval.point (1/2))).mul (cosine hx)).add
    ((sine hx).div (Interval.point 2) (by norm_num [Interval.point])) using 1
  rfl
def axisChargeBox : Interval axisCharge := by
  convert ((Interval.point (t 1)).mul (axial.add (Interval.point (1/2)))).sub
    (Interval.point (P 1/2)) using 1
  rfl
def OmegaBox (x : ℝ) (hx : 0≤x) (hD : 0<(axisProjectionBox x hx).lo) : Interval (Omega x) :=
  (Interval.point 1).sub (axisChargeBox.mul
    ((Interval.point 1).sub ((cosine hx).div (axisProjectionBox x hx) hD)))

theorem endpoint_signs : (49/25000:ℝ)<Omega (9/100) ∧ Omega (134/1250)<-(131/50000:ℝ) := by
  have hD0 : 0<(axisProjectionBox (9/100) (by norm_num)).lo := by
    dsimp [axisProjectionBox]
    mixed_fixed
  have hD1 : 0<(axisProjectionBox (134/1250) (by norm_num)).lo := by
    dsimp [axisProjectionBox]
    mixed_fixed
  have h0 : (49/25000:ℝ)<(OmegaBox (9/100) (by norm_num) hD0).lo := by
    dsimp [OmegaBox,axisProjectionBox,axisChargeBox,t,P]
    mixed_fixed
  have h1 : (OmegaBox (134/1250) (by norm_num) hD1).hi<-(131/50000:ℝ) := by
    dsimp [OmegaBox,axisProjectionBox,axisChargeBox,t,P]
    mixed_fixed
  exact ⟨h0.trans_le (OmegaBox (9/100) (by norm_num) hD0).mem.1,
    (OmegaBox (134/1250) (by norm_num) hD1).mem.2.trans_lt h1⟩

theorem exists_event : ∃s,IsEvent s := by
  have hc : ContinuousOn (fun x => -Omega x) (Icc (9/100:ℝ) (134/1250)) := by
    intro x hx
    exact (Omega_hasDerivAt (show x∈Icc 0 (7/10) from
      ⟨by linarith [hx.1],by linarith [hx.2]⟩)).neg.continuousAt.continuousWithinAt
  obtain ⟨s,hs,hse⟩ := intermediate_value_Icc (by norm_num : (9/100:ℝ)≤134/1250) hc
    (show (0:ℝ)∈Icc (-Omega (9/100)) (-Omega (134/1250)) from
      ⟨by linarith [endpoint_signs.1],by linarith [endpoint_signs.2]⟩)
  have he : Omega s=0 := by linarith
  refine ⟨s,⟨?_,?_⟩,he⟩
  · apply lt_of_le_of_ne hs.1
    intro h
    rw [←h] at he
    linarith [endpoint_signs.1]
  · apply lt_of_le_of_ne hs.2
    intro h
    rw [h] at he
    linarith [endpoint_signs.2]

theorem positive_before {s x : ℝ} (hs : IsEvent s) (hx : 0≤x) (hxs : x<s) : 0<Omega x := by
  have hh := Omega_strictAnti
    (show x∈Icc 0 (7/10) from ⟨hx,by linarith [hs.1.2]⟩)
    (show s∈Icc 0 (7/10) from ⟨by linarith [hs.1.1],by linarith [hs.1.2]⟩) hxs
  rw [hs.2] at hh
  exact hh

theorem projection_target_hasDerivAt {B : ℝ} (hB : B∈Icc 0 outerDiagonal) (x : ℝ) :
    HasDerivAt (fun D => targetProjection D x) (Real.sin x-Real.cos x*ratio B) B := by
  convert (((SameContact.arc_hasDerivAt (SameContact.outer_domain hB)).add_const (1/2)).
    mul_const (Real.cos x)).add (((hasDerivAt_id B).add_const (1/2)).mul_const (Real.sin x)) using 1 <;>
      dsimp [targetProjection,targetU,targetV] <;> ring

theorem projection_le_axis {B e x : ℝ} (he : Upper.IsEvent e)
    (hB : B∈Icc 0 outerDiagonal) (hx : x∈Icc 0 e) : targetProjection B x≤axisProjection x := by
  have hm : AntitoneOn (fun D => targetProjection D x) (Icc 0 outerDiagonal) := by
    apply antiOn_of_hasDeriv_nonpos
      (fun D hD => (projection_target_hasDerivAt hD x).continuousAt.continuousWithinAt)
      (fun D hD => projection_target_hasDerivAt (Ioo_subset_Icc_self hD) x)
    intro D hD
    have hr := (target_ratio (Ioo_subset_Icc_self hD)).1
    have hc := early_cos he hx
    have hs := (axial_bounds he hx).2.2.2.2.2.2.2
    have hp := mul_le_mul hc.le (rho_bounds.1.le.trans hr)
      (by norm_num) (by linarith [hc] : 0≤Real.cos x)
    linarith
  have hh := hm zero_mem hB hB.1
  simpa [targetProjection,targetU,targetV,axisProjection,SameContact.arc_zero] using hh

theorem targetCharge_bounds {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    0<targetCharge B ∧ targetCharge B≤axisCharge := by
  have hs := SameContact.arc_state hB
  have hb := outer_bounds hs
  have hU : 0<targetU B := by dsimp [targetU]; linarith [(target_root_bounds hB).1]
  have hUV : targetV B≤targetU B := by dsimp [targetV,targetU]; linarith [hs.2.1]
  dsimp [targetCharge,axisCharge,targetU,targetV] at *
  norm_num [P,t]
  constructor <;> nlinarith [hb.2.1,hB.1]

theorem stationary_identity {B x : ℝ} (hd : Domain B x) (hf : first 1 B x=0) :
    angleFirst 1 B x=1-targetCharge B*(1-Real.cos x/targetProjection B x) := by
  have hU : 0<targetU B := by dsimp [targetU]; linarith [(target_root_bounds hd.1).1]
  have hD := (projection_positive hd.1 hd.2.1).1
  have hL : sourceD 1 (contact B x)*targetProjection B x=targetCharge B := by
    dsimp [first,stateSpeed,SecondWord.SameZero.k,ratio] at hf
    change sourceD 1 (contact B x)*(Real.cos x+targetV B/targetU B*Real.sin x)+
      P 1*(targetV B/targetU B)-t 1=0 at hf
    field_simp [hU.ne'] at hf
    dsimp [targetProjection,targetCharge]
    nlinarith
  have hs : angleSpeed B x=targetProjection B x-Real.cos x := by
    dsimp [angleSpeed,SecondWord.SameZero.v,targetProjection,targetU,targetV]
    ring
  rw [angleFirst,hs]
  calc
    1-sourceD 1 (contact B x)*(targetProjection B x-Real.cos x)=
      1-(sourceD 1 (contact B x)*targetProjection B x)*(1-Real.cos x/targetProjection B x) := by
        field_simp [hD.ne']
        ring
    _ = _ := by rw [hL]

theorem stationary_angle_lower {B e x : ℝ} (he : Upper.IsEvent e)
    (hd : Domain B x) (hx : x≤e) (hf : first 1 B x=0) : Omega x≤angleFirst 1 B x := by
  have hD := projection_positive hd.1 hd.2.1
  have hA := axisProjection_positive hd.2.1
  have hDA := projection_le_axis he hd.1 ⟨hd.2.1.1,hx⟩
  have hcharge := targetCharge_bounds hd.1
  have hcos : 0<Real.cos x := by linarith [(positive_trig hd.2.1).1]
  have hfactor : 0≤1-Real.cos x/targetProjection B x := by
    have hh := (div_lt_one hD.1).2 hD.2
    linarith
  have hfactor' : 1-Real.cos x/targetProjection B x≤1-Real.cos x/axisProjection x := by
    have hh := div_le_div_of_nonneg_left hcos.le hD.1 hDA
    linarith
  have hp := mul_le_mul hcharge.2 hfactor' hfactor axisCharge_positive.le
  rw [stationary_identity hd hf]
  dsimp [Omega]
  linarith

end SquaresInCircles.Eight.TableFree.ShortOuterOne.Opposite.Primary.Upper.Stationary
