module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Owners.Small.WrongScalar

/-!
# Eight squares: the small wrong-sign cap

The lift of the A circle at the same q is kept in all identities. Chord bounds for the two
positive square roots cover every middle tangent between `.28` and `.5`. They give one increasing
wrong-sign demand (`demand_monotone`) and a zero-tangent contact between `.195` and `.4`
(`contact`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CrossedSmallWrongScalar
open PositiveSmallScalar

structure CapData (q P Y : ℝ) : Prop where
  P_mem : P∈Icc (1/2 : ℝ) (819/1000)
  Y_mem : Y∈Icc (39/50 : ℝ) 1
  circle : (P+1)^2+Y^2=q
  floor : qLow≤q
  ceiling : q≤qCap

theorem U_pos {q P Y z : ℝ} (S : CapData q P Y)
    (hz : z∈Icc 0 frameCap) : 0<U P Y z := by
  have ht := transport_trig hz
  have hp := mul_nonneg (show 0≤P by linarith [S.P_mem.1]) ht.2.2.1
  have hy := mul_pos (show 0<Y by linarith [S.Y_mem.1])
    (show 0<Real.cos z by linarith [ht.1])
  dsimp [U]
  linarith

theorem V_antitone {q P Y : ℝ} (S : CapData q P Y) :
    AntitoneOn (V P Y) (Icc 0 frameCap) := by
  intro x hx y hy hxy
  have hc := mul_le_mul_of_nonneg_left (CorrelatedSameBlock.cos_anti hx hy hxy)
    (show 0≤P by linarith [S.P_mem.1])
  have hs := mul_le_mul_of_nonneg_left (CorrelatedSameBlock.sin_mono hx hy hxy)
    (show 0≤Y by linarith [S.Y_mem.1])
  dsimp [V]
  linarith

theorem V_strictAnti {q P Y : ℝ} (S : CapData q P Y) :
    StrictAntiOn (V P Y) (Icc 0 frameCap) := by
  have hm : StrictMonoOn (fun z => -V P Y z) (Icc 0 frameCap) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 frameCap)
    · unfold V
      fun_prop
    · intro z hz
      have hd : HasDerivAt (fun z => -V P Y z) (-(-U P Y z)) z := (V_hasDerivAt P Y z).neg
      rw [hd.deriv,neg_neg]
      exact U_pos S (interior_subset hz)
  intro x hx y hy hxy
  exact neg_lt_neg_iff.mp (hm hx hy hxy)

theorem contact_lower_test {q P Y : ℝ} (S : CapData q P Y) :
    1/2<V P Y (39/200) := by
  have hP : 3537/5000<P := by
    have hYsq := pow_le_pow_left₀ (show 0≤Y by linarith [S.Y_mem.1]) S.Y_mem.2 2
    have hq := S.floor
    dsimp [qLow] at hq
    nlinarith [S.circle,S.P_mem.1]
  have hs0 := (transport_trig (show (39/200 : ℝ)∈Icc 0 frameCap by
    norm_num [frameCap])).2.2.1
  have hc := cos_lower_six (show (0:ℝ)≤39/200 by norm_num)
  have hs := sin_upper_five (show (0:ℝ)≤39/200 by norm_num)
  have hpc := mul_le_mul_of_nonneg_right hP.le
    (show 0≤Real.cos (39/200 : ℝ) by linarith)
  have hcl := mul_le_mul_of_nonneg_left hc (show (0:ℝ)≤3537/5000 by norm_num)
  have hys := mul_le_mul_of_nonneg_right S.Y_mem.2 hs0
  dsimp [V]
  norm_num at hc hs hpc hcl hys ⊢
  linarith

theorem contact_upper_test {q P Y : ℝ} (S : CapData q P Y) :
    V P Y (2/5)<1/2 := by
  have ht := transport_trig (show (2/5 : ℝ)∈Icc 0 frameCap by norm_num [frameCap])
  have hc := cos_upper_four (show (0:ℝ)≤2/5 by norm_num)
  have hs := Real.sin_ge_sub_cube (show (0:ℝ)≤2/5 by norm_num)
  have hp := mul_le_mul_of_nonneg_right S.P_mem.2 (show 0≤Real.cos (2/5 : ℝ) by
    linarith [ht.1])
  have hpc := mul_le_mul_of_nonneg_left hc (show (0:ℝ)≤819/1000 by norm_num)
  have hy := mul_le_mul_of_nonneg_right S.Y_mem.1 ht.2.2.1
  have hys := mul_le_mul_of_nonneg_left hs (show (0:ℝ)≤39/50 by norm_num)
  dsimp [V]
  norm_num at hp hpc hy hys ⊢
  linarith

/-- The root is intrinsic to the lifted circle at the same q. The comparison range `.4` is only
a scalar interval, not a spread of the configuration. -/
theorem contact {q P Y : ℝ} (S : CapData q P Y) :
    ∃ Z, Z∈Ioo (39/200 : ℝ) (2/5) ∧ V P Y Z=1/2 := by
  have hleft := contact_lower_test S
  have hright := contact_upper_test S
  obtain ⟨Z,hZ,heq⟩ := intermediate_value_Icc (show (39/200 : ℝ)≤2/5 by norm_num)
    (show ContinuousOn (fun z => -V P Y z) (Icc (39/200) (2/5)) by
      unfold V
      fun_prop)
    (show -(1/2 : ℝ)∈Icc (-V P Y (39/200)) (-V P Y (2/5)) by
      constructor <;> linarith)
  have hZE : V P Y Z=1/2 := by linarith
  refine ⟨Z,⟨?_,?_⟩,hZE⟩
  · apply lt_of_le_of_ne hZ.1
    intro h
    rw [←h] at hZE
    linarith
  · apply lt_of_le_of_ne hZ.2
    intro h
    rw [h] at hZE
    linarith

theorem coefficient_lt_one {v : ℝ} (hv : v∈Icc (2/5 : ℝ) (1/2)) :
    (2*(819/1000+v)/(7319/2500))*
      (1+(1-v)*(819/1000-v)/((39/50)*(1769/1000+(29/100)*v)))<1 := by
  let x := 1/2-v
  have hx : x∈Icc (0:ℝ) (1/10) := by dsimp [x]; constructor <;> linarith [hv.1,hv.2]
  have hx2 : x^2≤x/10 := by
    nlinarith [mul_nonneg hx.1 (show 0≤1/10-x by linarith [hx.2])]
  have hid : ((7319/2500)-2*(819/1000+v))*((39/50)*(1769/1000+(29/100)*v))-
      2*(819/1000+v)*(1-v)*(819/1000-v)=
      1448579/125000000+(13485131/12500000)*x-(3631/2500)*x^2+2*x^3 := by
    dsimp [x]
    ring
  have hp : 0<((7319/2500)-2*(819/1000+v))*((39/50)*(1769/1000+(29/100)*v))-
      2*(819/1000+v)*(1-v)*(819/1000-v) := by
    rw [hid]
    nlinarith [pow_nonneg hx.1 3]
  have hw : 0<1769/1000+(29/100)*v := by linarith [hv.1]
  have hid' : (2*(819/1000+v)/(7319/2500))*
      (1+(1-v)*(819/1000-v)/((39/50)*(1769/1000+(29/100)*v)))=
      (2*(819/1000+v)*((39/50)*(1769/1000+(29/100)*v)+(1-v)*(819/1000-v)))/
        ((7319/2500)*((39/50)*(1769/1000+(29/100)*v))) := by
    rw [one_add_div (mul_pos (by norm_num) hw).ne',div_mul_div_comm]
  rw [hid']
  apply (div_lt_iff₀ (show 0<(7319/2500)*((39/50)*(1769/1000+(29/100)*v)) by positivity)).2
  nlinarith

theorem root_bounds {q P Y z : ℝ} (S : CapData q P Y)
    (hz : z∈Icc 0 frameCap) (hv : V P Y z∈Icc (2/5 : ℝ) (1/2)) :
    0<q-(1-V P Y z)^2 ∧
      1769/1000+(29/100)*V P Y z<SmallWrongScalar.W q P Y z ∧
      6153/5000-(217/500)*V P Y z<U P Y z ∧
      7319/2500<SmallWrongScalar.W q P Y z+U P Y z ∧
      0<SmallWrongScalar.W q P Y z-U P Y z ∧
      (SmallWrongScalar.W q P Y z-U P Y z)*
        (SmallWrongScalar.W q P Y z+U P Y z)=2*(P+V P Y z) := by
  let v := V P Y z
  let x := v-2/5
  have hx : x∈Icc (0:ℝ) (1/10) := by dsimp [x,v]; constructor <;> linarith [hv.1,hv.2]
  have hx2 : x^2≤x/10 := by
    linarith [mul_nonneg hx.1 (show 0≤1/10-x by linarith [hx.2])]
  have hq := S.floor
  dsimp [qLow] at hq
  have hwline : (1769/1000+(29/100)*v)^2<q-(1-v)^2 := by
    have hid : q-(1-v)^2-(1769/1000+(29/100)*v)^2=
        q-19577/5000+87/40000+(1067/10000)*x-(10841/10000)*x^2 := by
      dsimp [x]
      ring
    linarith [hx.1,hx.2]
  have hwline0 : 0<1769/1000+(29/100)*v := by dsimp [v]; linarith [hv.1]
  have hr : 0<q-(1-v)^2 := by linarith [sq_nonneg (1769/1000+(29/100)*v)]
  have hw0 : 0<SmallWrongScalar.W q P Y z := Real.sqrt_pos.2 hr
  have hw2 : (SmallWrongScalar.W q P Y z)^2=q-(1-v)^2 := Real.sq_sqrt hr.le
  have hw : 1769/1000+(29/100)*v<SmallWrongScalar.W q P Y z :=
    lt_of_pow_lt_pow_left₀ 2 hw0.le (by rw [hw2]; exact hwline)
  have hu0 := U_pos S hz
  have hrot := rotation_identity P Y z
  have hu2 : (U P Y z)^2=q-2*P-1-v^2 := by dsimp [v]; linarith [S.circle]
  have huline : (6153/5000-(217/500)*v)^2<(U P Y z)^2 := by
    have hid : q-2*P-1-v^2-(6153/5000-(217/500)*v)^2=
        q-19577/5000+2*(819/1000-P)+151/1000000+
          (29369/250000)*x-(297089/250000)*x^2 := by
      dsimp [x]
      ring
    linarith [S.P_mem.2,hx.1,hx.2]
  have hul0 : 0<6153/5000-(217/500)*v := by dsimp [v]; linarith [hv.2]
  have hu : 6153/5000-(217/500)*v<U P Y z := lt_of_pow_lt_pow_left₀ 2 hu0.le huline
  have hsum : 7319/2500<SmallWrongScalar.W q P Y z+U P Y z := by
    dsimp [v] at hw hu
    linarith [hv.2]
  have hid : (SmallWrongScalar.W q P Y z-U P Y z)*
      (SmallWrongScalar.W q P Y z+U P Y z)=2*(P+V P Y z) := by
    dsimp [v] at hw2 hu2
    linear_combination hw2-hu2
  have ht : 0<SmallWrongScalar.W q P Y z-U P Y z := by
    exact pos_of_mul_pos_right (by rw [mul_comm,hid]; linarith [S.P_mem.1,hv.1])
      (by linarith : 0≤SmallWrongScalar.W q P Y z+U P Y z)
  exact ⟨hr,hw,hu,hsum,ht,hid⟩

theorem intrinsic_sine_bound {q P Y z h : ℝ} (S : CapData q P Y)
    (hz : z∈Icc 0 frameCap) (hh : h∈Icc 0 z) (hv : 0≤V P Y z) :
    (39/50)*Real.sin h≤(819/1000-V P Y z)*Real.cos h := by
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
    nlinarith
  have hYcross := mul_le_mul_of_nonneg_left hcross (show 0≤Y by linarith [S.Y_mem.1])
  have hbase' := mul_le_mul_of_nonneg_right hbase (show 0≤Real.cos h by linarith [th.1])
  have hcancel : (Y*Real.sin h)*Real.cos z≤
      ((P-V P Y z)*Real.cos h)*Real.cos z := by nlinarith
  have hlocal := le_of_mul_le_mul_right hcancel (show 0<Real.cos z by linarith [tz.1])
  have hY := mul_le_mul_of_nonneg_right S.Y_mem.1 th.2.2.1
  have hP := mul_le_mul_of_nonneg_right S.P_mem.2 (show 0≤Real.cos h by linarith [th.1])
  nlinarith

theorem demandD_pos {q P Y Θ h : ℝ} (S : CapData q P Y)
    (hΘ : 0≤Θ) (hh : 0≤h) (hz : Θ+h∈Icc 0 frameCap)
    (hv : V P Y (Θ+h)∈Icc (2/5 : ℝ) (1/2)) :
    0<SmallWrongScalar.demandD q P Y Θ h := by
  let v := V P Y (Θ+h)
  let w := SmallWrongScalar.W q P Y (Θ+h)
  let u := U P Y (Θ+h)
  let w0 := 1769/1000+(29/100)*v
  let a := 2*(819/1000+v)/(7319/2500)
  let b := 1+(1-v)*(819/1000-v)/((39/50)*w0)
  obtain ⟨hr,hw,hu,hsum,ht,hid⟩ := root_bounds S hz hv
  have hi : h∈Icc 0 frameCap := ⟨hh,by linarith [hz.2]⟩
  have htr := transport_trig hi
  have hc : 0<Real.cos h := by linarith [htr.1]
  have hs := intrinsic_sine_bound S hz (show h∈Icc 0 (Θ+h) from ⟨hh,by linarith⟩)
    (by linarith [hv.1])
  have hslope : Real.sin h≤((819/1000-v)/(39/50))*Real.cos h := by dsimp [v]; linarith
  have hT : w-u≤a := by
    have hmul := mul_le_mul_of_nonneg_left hsum.le ht.le
    dsimp [w,u,a,v] at *
    nlinarith [S.P_mem.2]
  have hw00 : 0<w0 := by dsimp [w0,v]; linarith [hv.1]
  have hw0 : 0<w := by dsimp [w,w0,v] at *; linarith
  have hz0 : 0≤1-v := by dsimp [v]; linarith [hv.2]
  have hratio : (1-v)/w≤(1-v)/w0 :=
    (div_le_div_iff₀ hw0 hw00).2 (by dsimp [w,w0,v]; nlinarith [hv.2])
  have hterm : ((1-v)/w)*Real.sin h≤
      ((1-v)*(819/1000-v)/((39/50)*w0))*Real.cos h := by
    have hm := mul_le_mul hratio hslope htr.2.2.1 (div_nonneg hz0 hw00.le)
    convert hm using 1 <;> ring
  have hinside : Real.cos h+((1-v)/w)*Real.sin h≤b*Real.cos h := by dsimp [b]; linarith
  have ha0 : 0≤a := by dsimp [a,v]; linarith [hv.1]
  have hinside0 : 0≤Real.cos h+((1-v)/w)*Real.sin h :=
    add_nonneg hc.le (mul_nonneg (div_nonneg hz0 hw0.le) htr.2.2.1)
  have hproduct := mul_le_mul hT hinside hinside0 ha0
  have hcoeff : a*b<1 := coefficient_lt_one hv
  have hstrict := mul_lt_mul_of_pos_right hcoeff hc
  change 0<Real.cos h-(w-u)*(Real.cos h+((1-v)/w)*Real.sin h)
  nlinarith

theorem demand_monotone {q P Y Θ l r : ℝ} (S : CapData q P Y)
    (hΘ : 0≤Θ)
    (hdom : ∀s∈Icc l r,0≤ s ∧ Θ+s∈Icc 0 frameCap ∧
      V P Y (Θ+s)∈Icc (2/5 : ℝ) (1/2)) :
    MonotoneOn (SmallWrongScalar.demand q P Y Θ) (Icc l r) := by
  have hm : StrictMonoOn (SmallWrongScalar.demand q P Y Θ) (Icc l r) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc l r)
    · intro s hs
      have hd := hdom s hs
      exact (SmallWrongScalar.demand_hasDerivAt
        (root_bounds S hd.2.1 hd.2.2).1).continuousAt.continuousWithinAt
    · intro s hs
      have hd := hdom s (interior_subset hs)
      rw [(SmallWrongScalar.demand_hasDerivAt (root_bounds S hd.2.1 hd.2.2).1).deriv]
      exact demandD_pos S hΘ hd.1 hd.2.1 hd.2.2
  exact hm.monotoneOn

/-- A feasible wrong-sign cap reaches its zero-tangent contact at a positive outer angle, with
no increase in the required H tangent. -/
theorem zero_contact {q P Y Θ e bH : ℝ} (S : CapData q P Y)
    (hΘ : 0≤Θ) (he : 0<e) (hz : Θ+e∈Icc 0 frameCap)
    (hv : V P Y (Θ+e)∈Ioo (2/5 : ℝ) (1/2))
    (hH : bH<9/10) (hfeas : SmallWrongScalar.demand q P Y Θ e≤bH) :
    ∃ s, s∈Ioc 0 e ∧ V P Y (Θ+s)=1/2 ∧ SmallWrongScalar.demand q P Y Θ s≤bH := by
  have hΘi : Θ∈Icc 0 frameCap := ⟨hΘ,by linarith [hz.2]⟩
  have hleft : 1/2<V P Y Θ := by
    by_contra! hbad
    have hm := demand_monotone S hΘ (l := 0) (r := e) (by
      intro s hs
      have hsi : Θ+s∈Icc 0 frameCap := ⟨by linarith [hs.1],by linarith [hs.2,hz.2]⟩
      have hlo := V_antitone S hsi hz (by linarith [hs.2])
      have hhi := V_antitone S hΘi hsi (by linarith [hs.1])
      exact ⟨hs.1,hsi,⟨by linarith [hv.1],by linarith⟩⟩)
    have hh := hm (show (0:ℝ)∈Icc 0 e from ⟨le_rfl,he.le⟩)
      (show e∈Icc 0 e from ⟨he.le,le_rfl⟩) he.le
    have h0 : SmallWrongScalar.demand q P Y Θ 0=3/2-V P Y Θ := by
      simp only [SmallWrongScalar.demand,add_zero,Real.cos_zero,Real.sin_zero,mul_one,mul_zero,
        sub_zero]
      ring
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
  let s := Z-Θ
  have hs : s∈Ioc 0 e := by dsimp [s]; exact ⟨sub_pos.mpr hZstrict,by linarith [hZ.2]⟩
  have hsi : Θ+s=Z := by dsimp [s]; ring
  have hZi : Z∈Icc 0 frameCap := ⟨hΘ.trans hZ.1,hZ.2.trans hz.2⟩
  have hm := demand_monotone S hΘ (l := s) (r := e) (by
    intro t ht
    have hti : Θ+t∈Icc 0 frameCap := ⟨by linarith [ht.1,hs.1],by linarith [ht.2,hz.2]⟩
    have hlo := V_antitone S hti hz (by linarith [ht.2])
    have hhi := V_antitone S hZi hti (by rw [←hsi]; linarith [ht.1])
    exact ⟨by linarith [ht.1,hs.1],hti,⟨by linarith [hv.1],by linarith⟩⟩)
  exact ⟨s,hs,by rw [hsi]; exact hcontact,
    (hm ⟨le_rfl,hs.2⟩ ⟨hs.2,le_rfl⟩ hs.2).trans hfeas⟩

end SquaresInCircles.Eight.CrossedSmallWrongScalar
