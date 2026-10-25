module

public import SquaresInCircles.Eight.Owners.Positive.SmallScalar
public import SquaresInCircles.Eight.Owners.Small.PositiveZeroEndpoint

/-!
# Eight squares: A small wrong sign reaches an impossible actual zero endpoint

The middle primary is lifted only to its
actual q-circle, keeping its original tangent.  The wrong intermediate
is optimized on that same circle.  Its intrinsic cap either already
allows tangent zero or reaches zero by the proved monotone demand.
The unchanged source H/D/E/T budget excludes that concrete endpoint.
No conclusion about equality of lifted and original points is used.
-/

section
/-!
## A monotone circle cap for a small wrong intermediate tangent

Lifting the middle to its circle at the radius `q` gives the optimized demand of a wrong G in
closed form (`demand`). The sign capture at one tenth restricts the cap to `0.4 ≤ V ≤ 0.5`; on
that whole interval two lower bounds of roots and one cubic show that the demand increases with
the outer angle (`root_bounds`, `coefficient_lt_one`, `demandD_pos`, `demand_monotone`). So the
contact `V = 1/2` is reached at a positive angle before the original wrong-sign state
(`zero_contact`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SmallWrongScalar
open PositiveSmallScalar

def W (q P Y z : ℝ) : ℝ := Real.sqrt (q-(1-V P Y z)^2)
def demand (q P Y Θ h : ℝ) : ℝ :=
  1/2+(1-V P Y (Θ+h))*Real.cos h-(W q P Y (Θ+h)-1)*Real.sin h
def demandD (q P Y Θ h : ℝ) : ℝ :=
  Real.cos h-(W q P Y (Θ+h)-U P Y (Θ+h))*
    (Real.cos h+(1-V P Y (Θ+h))/W q P Y (Θ+h)*Real.sin h)

theorem W_hasDerivAt {q P Y z : ℝ} (hr : 0<q-(1-V P Y z)^2) :
    HasDerivAt (W q P Y)
      (-(1-V P Y z)*U P Y z/W q P Y z) z := by
  have hz := (hasDerivAt_const z (1:ℝ)).sub (V_hasDerivAt P Y z)
  have hd := ((hasDerivAt_const z q).sub (hz.pow 2)).sqrt hr.ne'
  convert hd using 1
  · rfl
  · dsimp [W]
    field_simp [(Real.sqrt_pos.2 hr).ne']
    ring

theorem demand_hasDerivAt {q P Y Θ h : ℝ}
    (hr : 0<q-(1-V P Y (Θ+h))^2) :
    HasDerivAt (demand q P Y Θ) (demandD q P Y Θ h) h := by
  have hw0 : 0<W q P Y (Θ+h) := Real.sqrt_pos.2 hr
  have hv := (V_hasDerivAt P Y (Θ+h)).comp h ((hasDerivAt_id h).const_add Θ)
  have hw := (W_hasDerivAt hr).comp h ((hasDerivAt_id h).const_add Θ)
  have hz := (hasDerivAt_const h (1:ℝ)).sub hv
  have hd := (((hz.mul (Real.hasDerivAt_cos h)).const_add (1/2)).sub
    ((hw.sub_const 1).mul (Real.hasDerivAt_sin h)))
  convert hd using 1
  · rfl
  · dsimp [demandD]
    field_simp
    ring

/-- The coefficient is below one on the whole interval `2/5 ≤ v ≤ 1/2`, by one cubic whose
expansion at the upper endpoint has a positive linear reserve. -/
theorem coefficient_lt_one {v : ℝ} (hv : v∈Icc (2/5 : ℝ) (1/2)) :
    (2*(397/500+v)/(72/25))*
      (1+(1-v)*(397/500-v)/((167/200)*(47/25)))<1 := by
  obtain ⟨x,hx_def⟩ : ∃ x, x=1/2-v := ⟨_,rfl⟩
  have hx : x∈Icc (0:ℝ) (1/10) := by
    rw [hx_def]; constructor <;> linarith [hv.1,hv.2]
  have hx2 : x^2≤x/10 := by
    linarith [mul_nonneg hx.1 (show 0≤1/10-x by linarith [hx.2])]
  have hid : ((72/25)-2*(397/500+v))*((167/200)*(47/25))-
      2*(397/500+v)*(1-v)*(397/500-v)=
      12179/156250+(172341/125000)*x-x^2+2*x^3 := by
    rw [hx_def]
    ring
  have hp : 0<((72/25)-2*(397/500+v))*((167/200)*(47/25))-
      2*(397/500+v)*(1-v)*(397/500-v) := by
    rw [hid]
    linarith [pow_nonneg hx.1 3,hx.1]
  have e : 2*(397/500+v)/(72/25)*(1+(1-v)*(397/500-v)/((167/200)*(47/25)))=
      (2*(397/500+v)*((167/200)*(47/25))+2*(397/500+v)*(1-v)*(397/500-v))/
        ((72/25)*((167/200)*(47/25))) := by
    field_simp
  rw [e,div_lt_one (by norm_num)]
  linarith

theorem root_bounds {q P Y z : ℝ} (S : CapData q P Y)
    (hqL : qLow≤q) (hcircle : (P+1)^2+Y^2=q)
    (hz : z∈Icc 0 frameCap) (hv : V P Y z∈Icc (2/5 : ℝ) (1/2)) :
    0<q-(1-V P Y z)^2 ∧ 47/25<W q P Y z ∧ 1<U P Y z ∧
      0<W q P Y z-U P Y z ∧
      (W q P Y z-U P Y z)*(W q P Y z+U P Y z)=2*(P+V P Y z) := by
  have hr : (47/25 : ℝ)^2<q-(1-V P Y z)^2 := by
    have hs := pow_le_pow_left₀ (show 0≤1-V P Y z by linarith [hv.2])
      (show 1-V P Y z≤3/5 by linarith [hv.1]) 2
    dsimp [qLow] at hqL
    linarith
  have hr0 : 0<q-(1-V P Y z)^2 := by
    have : (0:ℝ)≤(47/25)^2 := by positivity
    linarith
  have hw0 : 0<W q P Y z := Real.sqrt_pos.2 hr0
  have hw2 : (W q P Y z)^2=q-(1-V P Y z)^2 := Real.sq_sqrt hr0.le
  have hw : 47/25<W q P Y z := by
    by_contra! hle
    have := pow_le_pow_left₀ hw0.le hle 2
    linarith
  have htr := transport_trig hz
  have hu0 : 0<U P Y z := by
    have hPsin := mul_nonneg (show 0≤P by linarith [S.P_mem.1]) htr.2.2.1
    have hYcos := mul_pos (show 0<Y by linarith [S.Y_mem.1]) (by linarith [htr.1] : 0<Real.cos z)
    dsimp [U]
    linarith
  have hrot := rotation_identity P Y z
  have hu2 : (U P Y z)^2=q-2*P-1-(V P Y z)^2 := by
    rw [← hcircle]
    linear_combination hrot
  have hvsq := pow_le_pow_left₀ (show 0≤V P Y z by linarith [hv.1]) hv.2 2
  have hu : 1<U P Y z := by
    have hPu := S.P_mem.2
    dsimp [qLow] at hqL
    by_contra! hle
    have := mul_le_mul hle hle hu0.le (by norm_num)
    linarith
  have hid : (W q P Y z-U P Y z)*(W q P Y z+U P Y z)=2*(P+V P Y z) := by
    linear_combination hw2-hu2
  have ht : 0<W q P Y z-U P Y z := by
    have hh : 0<2*(P+V P Y z) := by linarith [S.P_mem.1,hv.1]
    have hsum : 0<W q P Y z+U P Y z := by linarith
    exact pos_of_mul_pos_right (by rw [mul_comm,hid]; exact hh) hsum.le
  exact ⟨hr0,hw,hu,ht,hid⟩

/-- The slope comparison, cleared of tangent denominators, for `0 ≤ h ≤ z`. -/
theorem intrinsic_sine_bound {q P Y z h : ℝ} (S : CapData q P Y)
    (hz : z∈Icc 0 frameCap) (hh : h∈Icc 0 z) (hv : 0≤V P Y z) :
    (167/200)*Real.sin h≤(397/500-V P Y z)*Real.cos h := by
  have hi : h∈Icc 0 frameCap := ⟨hh.1,hh.2.trans hz.2⟩
  have tz := transport_trig hz
  have th := transport_trig hi
  have hs := CorrelatedSameBlock.sin_mono hi hz hh.2
  have hc := CorrelatedSameBlock.cos_anti hi hz hh.2
  have hcross : Real.sin h*Real.cos z≤Real.sin z*Real.cos h :=
    mul_le_mul hs hc (by linarith [tz.1]) tz.2.2.1
  have hbase : Y*Real.sin z≤(P-V P Y z)*Real.cos z := by
    have hvcos := mul_le_mul_of_nonneg_left tz.2.1 hv
    dsimp [V] at hvcos ⊢
    linarith
  have hYcross := mul_le_mul_of_nonneg_left hcross (show 0≤Y by linarith [S.Y_mem.1])
  have hbase' := mul_le_mul_of_nonneg_right hbase (show 0≤Real.cos h by linarith [th.1])
  have hcancel : (Y*Real.sin h)*Real.cos z≤
      ((P-V P Y z)*Real.cos h)*Real.cos z := by linarith
  have hlocal := le_of_mul_le_mul_right hcancel (show 0<Real.cos z by linarith [tz.1])
  have hY := mul_le_mul_of_nonneg_right S.Y_mem.1 th.2.2.1
  have hP := mul_le_mul_of_nonneg_right S.P_mem.2 (show 0≤Real.cos h by linarith [th.1])
  linarith

theorem demandD_pos {q P Y Θ h : ℝ} (S : CapData q P Y)
    (hqL : qLow≤q) (hcircle : (P+1)^2+Y^2=q)
    (hΘ : 0≤Θ) (hh : 0≤h) (hz : Θ+h∈Icc 0 frameCap)
    (hv : V P Y (Θ+h)∈Icc (2/5 : ℝ) (1/2)) :
    0<demandD q P Y Θ h := by
  let v := V P Y (Θ+h)
  let w := W q P Y (Θ+h)
  let u := U P Y (Θ+h)
  let a := 2*(397/500+v)/(72/25)
  let b := 1+(1-v)*(397/500-v)/((167/200)*(47/25))
  obtain ⟨hr,hw,hu,ht,hid⟩ := root_bounds S hqL hcircle hz hv
  have hi : h∈Icc 0 frameCap := ⟨hh,by linarith [hz.2]⟩
  have htr := transport_trig hi
  have hc : 0<Real.cos h := by linarith [htr.1]
  have hs := intrinsic_sine_bound S hz (show h∈Icc 0 (Θ+h) from ⟨hh,by linarith⟩)
    (by linarith [hv.1])
  have hslope : Real.sin h≤((397/500-v)/(167/200))*Real.cos h := by
    dsimp [v]
    linarith
  have hT : w-u≤a := by
    have hsum : 72/25≤w+u := by dsimp [w,u]; linarith
    have hmul := mul_le_mul_of_nonneg_left hsum ht.le
    dsimp [w,u,a,v] at *
    nlinarith [S.P_mem.2]
  have hw0 : 0<w := by dsimp [w]; linarith
  have hz0 : 0≤1-v := by dsimp [v]; linarith [hv.2]
  have hratio : (1-v)/w≤(1-v)/(47/25) :=
    (div_le_div_iff₀ hw0 (by norm_num)).2 (by dsimp [w,v]; nlinarith [hv.2])
  have hterm : ((1-v)/w)*Real.sin h≤
      ((1-v)*(397/500-v)/((167/200)*(47/25)))*Real.cos h := by
    have hm := mul_le_mul hratio hslope htr.2.2.1
      (show 0≤(1-v)/(47/25) by positivity)
    convert hm using 1
    ring
  have hinside : Real.cos h+((1-v)/w)*Real.sin h≤b*Real.cos h := by
    dsimp [b]
    linarith
  have ha0 : 0≤a := by dsimp [a,v]; linarith [hv.1]
  have hinside0 : 0≤Real.cos h+((1-v)/w)*Real.sin h :=
    add_nonneg hc.le (mul_nonneg (div_nonneg hz0 hw0.le) htr.2.2.1)
  have hproduct := mul_le_mul hT hinside hinside0 ha0
  have hcoeff : a*b<1 := coefficient_lt_one hv
  have hstrict := mul_lt_mul_of_pos_right hcoeff hc
  dsimp [demandD]
  change 0<Real.cos h-(w-u)*(Real.cos h+((1-v)/w)*Real.sin h)
  nlinarith

theorem demand_monotone {q P Y Θ l r : ℝ} (S : CapData q P Y)
    (hqL : qLow≤q) (hcircle : (P+1)^2+Y^2=q) (hΘ : 0≤Θ)
    (hdom : ∀s∈Icc l r,0≤ s ∧ Θ+s∈Icc 0 frameCap ∧
      V P Y (Θ+s)∈Icc (2/5 : ℝ) (1/2)) :
    MonotoneOn (demand q P Y Θ) (Icc l r) := by
  have hm : StrictMonoOn (demand q P Y Θ) (Icc l r) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc l r)
    · intro s hs
      have hd := hdom s hs
      exact (demand_hasDerivAt (root_bounds S hqL hcircle hd.2.1 hd.2.2).1).continuousAt.continuousWithinAt
    · intro s hs
      have hd := hdom s (interior_subset hs)
      rw [(demand_hasDerivAt (root_bounds S hqL hcircle hd.2.1 hd.2.2).1).deriv]
      exact demandD_pos S hqL hcircle hΘ hd.1 hd.2.1 hd.2.2
  exact hm.monotoneOn

/-- A feasible wrong-sign cap reaches its contact at zero tangent, `V = 1/2`, at a positive outer
angle `s ≤ e`, with no increase of the required tangent of H. -/
theorem zero_contact {q P Y Θ e bH : ℝ} (S : CapData q P Y)
    (hqL : qLow≤q) (hcircle : (P+1)^2+Y^2=q)
    (hΘ : 0≤Θ) (he : 0<e) (hz : Θ+e∈Icc 0 frameCap)
    (hv : V P Y (Θ+e)∈Ioo (2/5 : ℝ) (1/2))
    (hH : bH<9/10) (hfeas : demand q P Y Θ e≤bH) :
    ∃ s, s∈Ioc 0 e ∧ V P Y (Θ+s)=1/2 ∧ demand q P Y Θ s≤bH := by
  have hΘi : Θ∈Icc 0 frameCap := ⟨hΘ,by linarith [hz.2,he]⟩
  have hleft : 1/2<V P Y Θ := by
    by_contra! hbad
    have hm := demand_monotone S hqL hcircle hΘ (l := 0) (r := e) (by
      intro s hs
      have hsi : Θ+s∈Icc 0 frameCap := ⟨by linarith [hs.1],by linarith [hs.2,hz.2]⟩
      have hlo := V_antitone S hsi hz (by linarith [hs.2])
      have hhi := V_antitone S hΘi hsi (by linarith [hs.1])
      exact ⟨hs.1,hsi,⟨by linarith [hv.1],by linarith⟩⟩)
    have hh := hm (show (0:ℝ)∈Icc 0 e from ⟨le_rfl,he.le⟩)
      (show e∈Icc 0 e from ⟨he.le,le_rfl⟩) he.le
    have h0 : demand q P Y Θ 0=1/2+(1-V P Y Θ) := by simp [demand]
    rw [h0] at hh
    linarith
  obtain ⟨Z,hZ,hZE⟩ := intermediate_value_Icc (show Θ≤Θ+e by linarith)
    (show ContinuousOn (fun z => -V P Y z) (Icc Θ (Θ+e)) by unfold V; fun_prop)
    (show -(1/2 : ℝ)∈Icc (-V P Y Θ) (-V P Y (Θ+e)) by
      constructor <;> linarith [hv.2])
  have hcontact : V P Y Z=1/2 := by linarith
  have hZstrict : Θ<Z := by
    apply lt_of_le_of_ne hZ.1
    intro heq
    rw [←heq] at hcontact
    linarith
  obtain ⟨s,hs_def⟩ : ∃ s, s=Z-Θ := ⟨_,rfl⟩
  have hs : s∈Ioc 0 e := by rw [hs_def]; exact ⟨sub_pos.mpr hZstrict,by linarith [hZ.2]⟩
  have hsi : Θ+s=Z := by rw [hs_def]; ring
  have hZi : Z∈Icc 0 frameCap := ⟨hΘ.trans hZ.1,hZ.2.trans hz.2⟩
  have hm := demand_monotone S hqL hcircle hΘ (l := s) (r := e) (by
    intro t ht
    have hti : Θ+t∈Icc 0 frameCap := ⟨by linarith [ht.1,hs.1],by linarith [ht.2,hz.2]⟩
    have hlo := V_antitone S hti hz (by linarith [ht.2])
    have hhi := V_antitone S hZi hti (by rw [←hsi]; linarith [ht.1])
    exact ⟨by linarith [ht.1,hs.1],hti,⟨by linarith [hv.1],by linarith⟩⟩)
  exact ⟨s,hs,by rw [hsi]; exact hcontact,
    (hm ⟨le_rfl,hs.2⟩ ⟨hs.2,le_rfl⟩ hs.2).trans hfeas⟩

end SquaresInCircles.Eight.SmallWrongScalar
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate
namespace SignedCycle

theorem HardOuterGeometry.small_wrong_G_impossible {q : ℝ}
    (I : HardOuterGeometry q) (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hsmall : (I.cycle.point A).y∈Icc (67/200 : ℝ) (1/2))
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAH : I.cycle.theta A≤I.cycle.theta H)
    (hTy : 0≤(I.cycle.point T).y)
    (hGy : 0≤(I.cycle.point G).y) (hGsmall : (I.cycle.point G).y<1/10) : False := by
  have hHupper : (I.cycle.point H).y<9/10 :=
    (le_abs_self _).trans_lt (SignedPoint.coordinate_bounds
      (I.necessary.sorted H) (I.necessary.core H) (I.necessary.contained H) hq).2.2
  have hcharge := (signed_outer_charges hq I.necessary I.anchors_normal
    I.witnesses I.zero_signs).1
  have hHGorder : I.cycle.theta H<I.cycle.theta G := by
    simp only [EndpointRotationPenalty.charge] at hcharge
    linarith only [hcharge,hHupper,hGy]
  have hHG : I.cycle.Feasible H 0 := by
    have ho : I.witnesses.owner H=0 ∨ I.witnesses.owner H=2 := by
      simpa [normalOwners,H] using I.witnesses.allowed H
    rcases ho with ho | ho
    · simpa [ho] using I.witnesses.feasible H
    · exact False.elim (not_lt_of_ge hGy (I.zero_signs.HG_canceling ho))
  obtain ⟨Θ,hΘ_def⟩ : ∃ Θ, Θ=I.cycle.theta H-I.cycle.theta A := ⟨_,rfl⟩
  obtain ⟨e,he_def⟩ : ∃ e, e=I.cycle.theta G-I.cycle.theta H := ⟨_,rfl⟩
  have hΘ : 0≤Θ := by rw [hΘ_def]; exact sub_nonneg.mpr hAH
  have he : 0<e := by rw [he_def]; exact sub_pos.mpr hHGorder
  have hz : Θ+e∈Icc 0 frameCap := by
    refine ⟨by linarith only [hΘ,he],?_⟩
    have hspread := (le_abs_self _).trans (I.necessary.spread G A)
    rw [hΘ_def,he_def]
    linarith only [hspread]
  have hei : e∈Icc 0 frameCap := ⟨he.le,by linarith only [hz.2,hΘ]⟩
  obtain ⟨hPs,hPo,hPc⟩ := SignedPoint.outerAt_spec hqL
    (SignedPoint.contained_minor_le_diagonal (I.necessary.sorted A) (I.necessary.contained A))
  obtain ⟨P,hP⟩ : ∃ P, P=SignedPoint.outerAt q (I.cycle.point A).y := ⟨_,rfl⟩
  rw [← hP] at hPs hPo hPc
  have hPy : P.y=(I.cycle.point A).y := by rw [hP]; rfl
  have hAy0 := I.anchors_normal.A_nonneg
  have hPcirc : (P.a+1/2)^2+((I.cycle.point A).y+1/2)^2=q := by
    have h : P.circle=q := hPo
    simp only [SignedPoint.circle,hPy,abs_of_nonneg hAy0] at h
    exact h
  have hPa : (I.cycle.point A).a≤P.a := by
    have hAc : (I.cycle.point A).circle≤q := I.necessary.contained A
    simp only [SignedPoint.circle,abs_of_nonneg hAy0] at hAc
    by_contra! hlt
    have h2 := pow_lt_pow_left₀ (show P.a+1/2<(I.cycle.point A).a+1/2 by linarith only [hlt])
      (show 0≤P.a+1/2 by linarith only [hPs.1]) (by decide : (2:ℕ)≠0)
    linarith only [h2,hAc,hPcirc]
  obtain ⟨p,hp_def⟩ : ∃ p, p=P.a-1/2 := ⟨_,rfl⟩
  obtain ⟨Y,hY_def⟩ : ∃ Y, Y=(I.cycle.point A).y+1/2 := ⟨_,rfl⟩
  have hY : Y∈Icc (167/200 : ℝ) 1 := by
    rw [hY_def]
    constructor <;> linarith only [hsmall.1,hsmall.2]
  have hcircle : (p+1)^2+Y^2=q := by
    rw [hp_def,hY_def]
    linear_combination hPcirc
  have hp : p∈Icc (1/2 : ℝ) (397/500) := by
    have hqL' := hqL
    have hq' := hq
    simp only [qLow,qCap] at hqL' hq'
    have hp1 : 0<p+1 := by
      have := SignedPoint.primary_gt_half hPs hPc
      rw [hp_def]
      linarith only [this]
    constructor
    · have hYsq := pow_le_pow_left₀ (show 0≤Y by linarith only [hY.1]) hY.2 2
      by_contra! hlt
      have := pow_lt_pow_left₀ (show p+1<3/2 by linarith only [hlt]) hp1.le
        (by decide : (2:ℕ)≠0)
      linarith only [this,hYsq,hcircle,hqL']
    · have hYsq := pow_le_pow_left₀ (show (0:ℝ)≤167/200 by norm_num) hY.1 2
      by_contra! hlt
      have := pow_lt_pow_left₀ (show (397/500:ℝ)+1<p+1 by linarith only [hlt])
        (by norm_num) (by decide : (2:ℕ)≠0)
      linarith only [this,hYsq,hcircle,hq']
  have S : PositiveSmallScalar.CapData q p Y := {
    P_mem := hp
    Y_mem := hY
    circle := hcircle.le
    ceiling := hq }
  have hGA : -(I.cycle.point G).y+1/2≤PositiveSmallScalar.V p Y (Θ+e) := by
    have hf : edgeWidth (I.cycle.theta A-I.cycle.theta G)≤
        quarterProjection (I.cycle.point G) (I.cycle.point A)
          (I.cycle.theta A-I.cycle.theta G) 0 := by
      simpa [Feasible,slack,edge,word,delta,next,G,A,sub_nonneg] using I.GA_hard
    have hd : I.cycle.theta A-I.cycle.theta G= -(Θ+e) := by rw [hΘ_def,he_def]; ring
    rw [hd,edgeWidth_negative_formula hz] at hf
    simp only [quarterProjection,Matrix.cons_val_zero,Real.cos_neg,Real.sin_neg] at hf
    have hmul := mul_le_mul_of_nonneg_right hPa (show 0≤Real.cos (Θ+e) by
      linarith [(transport_trig hz).1])
    simp only [PositiveSmallScalar.V]
    rw [hp_def,hY_def]
    linarith only [hf,hmul]
  have hVlower : 2/5<PositiveSmallScalar.V p Y (Θ+e) := by linarith only [hGA,hGsmall]
  have hHG' : zeroFeasible (I.cycle.point H) (I.cycle.point G) e 0 := by
    rw [he_def]
    simpa [Feasible,slack,edge,word,delta,next,H,G,zeroFeasible,sub_nonneg] using hHG
  have hQbound : |(0:ℝ)|≤diagonalCoordinate q := by
    rw [abs_zero]
    linarith only [(uniform_circle_reserves hqL hq).1]
  obtain ⟨hQs,hQo,hQc⟩ := SignedPoint.outerAt_spec hqL hQbound
  obtain ⟨Q,hQ⟩ : ∃ Q, Q=SignedPoint.outerAt q 0 := ⟨_,rfl⟩
  rw [← hQ] at hQs hQo hQc
  have hQy : Q.y=0 := by rw [hQ]; rfl
  have hQa : Q.a=Real.sqrt (q-1/4)-1/2 := by
    rw [hQ]
    simp only [SignedPoint.outerAt,abs_zero,zero_add]
    norm_num
  have hGAzero {s : ℝ} (hs : s∈Ioc 0 e)
      (hV : 1/2≤PositiveSmallScalar.V p Y (Θ+s)) :
      quarterFeasible Q P (-(Θ+s)) 0 := by
    have hi : Θ+s∈Icc 0 frameCap :=
      ⟨by linarith only [hs.1,hΘ],by linarith only [hs.2,hz.2]⟩
    rw [quarterFeasible,edgeWidth_negative_formula hi]
    simp only [quarterProjection,Matrix.cons_val_zero,Real.cos_neg,Real.sin_neg,hQy,hPy]
    simp only [PositiveSmallScalar.V] at hV
    rw [hp_def,hY_def] at hV
    linarith only [hV]
  have hcandidate : ∃s,s∈Ioc 0 e ∧
      zeroFeasible (I.cycle.point H) Q s 0 ∧ quarterFeasible Q P (-(Θ+s)) 0 := by
    by_cases hcap : 1/2≤PositiveSmallScalar.V p Y (Θ+e)
    · have hQa' : (I.cycle.point G).a≤Q.a := by
        have hGc : (I.cycle.point G).circle≤q := I.necessary.contained G
        have hQcircle : Q.circle=q := hQo
        simp only [SignedPoint.circle,abs_of_nonneg hGy,hQy,abs_zero] at hGc hQcircle
        by_contra! hlt
        have h2 := pow_lt_pow_left₀ (show Q.a+1/2<(I.cycle.point G).a+1/2 by linarith only [hlt])
          (show 0≤Q.a+1/2 by linarith only [hQs.1]) (by decide : (2:ℕ)≠0)
        have h3 : (1/2:ℝ)^2≤((I.cycle.point G).y+1/2)^2 :=
          pow_le_pow_left₀ (by norm_num) (by linarith only [hGy]) 2
        linarith only [h2,h3,hGc,hQcircle]
      have hg : zeroFeasible (I.cycle.point H) Q e 0 := by
        have hh := hHG'
        rw [zeroFeasible,edgeWidth_positive_formula hei] at hh ⊢
        simp only [zeroProjection,Matrix.cons_val_zero,hQy,zero_mul,sub_zero] at hh ⊢
        have ha := mul_le_mul_of_nonneg_right hQa' (transport_trig hei).2.2.1
        have hy := mul_nonneg hGy (show 0≤Real.cos e by linarith [(transport_trig hei).1])
        linarith only [hh,ha,hy]
      exact ⟨e,⟨he,le_rfl⟩,hg,hGAzero ⟨he,le_rfl⟩ hcap⟩
    · have hv : PositiveSmallScalar.V p Y (Θ+e)∈Ioo (2/5 : ℝ) (1/2) :=
        ⟨hVlower,lt_of_not_ge hcap⟩
      have hb := SmallWrongScalar.root_bounds S hqL hcircle hz ⟨hv.1.le,hv.2.le⟩
      have hW2 : (SmallWrongScalar.W q p Y (Θ+e))^2=
          q-(1-PositiveSmallScalar.V p Y (Θ+e))^2 := Real.sq_sqrt hb.1.le
      have hGa : (I.cycle.point G).a≤SmallWrongScalar.W q p Y (Θ+e)-1/2 := by
        have hGc : (I.cycle.point G).circle≤q := I.necessary.contained G
        simp only [SignedPoint.circle,abs_of_nonneg hGy] at hGc
        have hy2 := pow_le_pow_left₀
          (show 0≤1-PositiveSmallScalar.V p Y (Θ+e) by linarith only [hv.2])
          (show 1-PositiveSmallScalar.V p Y (Θ+e)≤(I.cycle.point G).y+1/2 by
            linarith only [hGA]) 2
        by_contra! hlt
        have h2 := pow_lt_pow_left₀
          (show SmallWrongScalar.W q p Y (Θ+e)<(I.cycle.point G).a+1/2 by linarith only [hlt])
          (show 0≤SmallWrongScalar.W q p Y (Θ+e) by linarith only [hb.2.1])
          (by decide : (2:ℕ)≠0)
        linarith only [h2,hy2,hGc,hW2]
      have hsource : SmallWrongScalar.demand q p Y Θ e≤(I.cycle.point H).y := by
        have hh := hHG'
        rw [zeroFeasible,edgeWidth_positive_formula hei] at hh
        simp only [zeroProjection,Matrix.cons_val_zero] at hh
        have ha := mul_le_mul_of_nonneg_right hGa (transport_trig hei).2.2.1
        have hy := mul_le_mul_of_nonneg_right
          (show 1/2-PositiveSmallScalar.V p Y (Θ+e)≤(I.cycle.point G).y by linarith only [hGA])
          (show 0≤Real.cos e by linarith [(transport_trig hei).1])
        simp only [SmallWrongScalar.demand]
        linarith only [hh,ha,hy]
      obtain ⟨s,hs,hzero,hdemand⟩ := SmallWrongScalar.zero_contact S hqL hcircle
        hΘ he hz hv hHupper hsource
      have hi : s∈Icc 0 frameCap := ⟨hs.1.le,hs.2.trans hei.2⟩
      have hW : SmallWrongScalar.W q p Y (Θ+s)=Real.sqrt (q-1/4) := by
        simp only [SmallWrongScalar.W,hzero]
        norm_num
      have hg : zeroFeasible (I.cycle.point H) Q s 0 := by
        simp only [SmallWrongScalar.demand] at hdemand
        rw [hzero,hW] at hdemand
        rw [zeroFeasible,edgeWidth_positive_formula hi]
        simp only [zeroProjection,Matrix.cons_val_zero,hQy,zero_mul,sub_zero,hQa]
        linarith only [hdemand]
      exact ⟨s,hs,hg,hGAzero hs hzero.ge⟩
  obtain ⟨s,hs,hHGQ,hGAQ⟩ := hcandidate
  apply I.small_positive_G_zero_impossible (θ := I.cycle.theta H+s)
    hq hAB hnorm hsmall hTA hAH hTy P Q hPs hPc hPo.le hPy hQo.le hQy
    (by linarith only [hs.1])
    (by linarith only [hs.2,hz.2,hΘ_def])
  · rw [show I.cycle.theta H+s-I.cycle.theta H=s by ring]
    exact hHGQ
  · rw [show I.cycle.theta A-(I.cycle.theta H+s)= -(Θ+s) by rw [hΘ_def]; ring]
    exact hGAQ

end SignedCycle
end SquaresInCircles.Eight
end
end
end
