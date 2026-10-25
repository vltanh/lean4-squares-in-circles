module

public import SquaresInCircles.Eight.TableFree.PositiveSmallScalar

/-!
# A monotone circle cap for a small wrong intermediate tangent

Uncompiled source draft.  The actual-q middle-circle lift makes the
optimized wrong-G demand explicit.  The global one-tenth sign capture
restricts its intrinsic cap to .4 ≤ V ≤ .5.  On that whole interval,
two elementary root lower bounds and one cubic prove that the demand
increases with the outer angle.  The contact V=.5 is consequently
reached at a positive angle before the original wrong-sign state.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SmallWrongScalar
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

/-- The complete intrinsic interval is covered by one explicit cubic.
Its expansion at the upper endpoint has a positive linear reserve. -/
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

/-- The intrinsic slope comparison is cleared of tangent denominators.
It uses the true order 0 ≤ h ≤ z rather than a fixed angular mesh. -/
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

/-- A feasible wrong-sign cap reaches its actual zero-tangent contact at
a positive outer angle, with no increase in the required H tangent. -/
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

end SquaresInCircles.Eight.TableFree.SmallWrongScalar
