module

public import SquaresInCircles.Eight.TableFree.CrossedSmallWrongScalar
public import SquaresInCircles.Eight.TableFree.CrossedZeroReserve
public import SquaresInCircles.Eight.TableFree.SecondOuterMinimumCalculus

/-!
# The two intrinsic crossed wrong-sign endpoints

Uncompiled source draft.  For each wrong-sign circle cap, the charged
HG demand has its minimum at the two actual ends of the HG-angle
interval.  The far endpoint has curvature at least 2/3 in the intrinsic
GA angle.  At the zero-tangent contact its slope is at least -.075.
These bounds give the exact loss 27/6400 by one completed square.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.CrossedWrongEndpointCalculus
open PositiveSmallScalar CrossedSmallWrongScalar EndpointRotationPenalty

def zeroDemand (q h : ℝ) : ℝ :=
  1/2+Real.cos h/2-(Real.sqrt (q-1/4)-1)*Real.sin h

def chargedDemand (q P Y z h : ℝ) : ℝ :=
  1/2+(1-V P Y z)*Real.cos h-(SmallWrongScalar.W q P Y z-1)*Real.sin h+
    charge*(h-z)

def K (q P Y z : ℝ) : ℝ := chargedDemand q P Y z frameCap

def K1 (q P Y z : ℝ) : ℝ :=
  U P Y z*(Real.cos frameCap+
    (1-V P Y z)/SmallWrongScalar.W q P Y z*Real.sin frameCap)-charge

def K2 (q P Y z : ℝ) : ℝ :=
  V P Y z*(Real.cos frameCap+
    (1-V P Y z)/SmallWrongScalar.W q P Y z*Real.sin frameCap)+
      q*(U P Y z)^2/(SmallWrongScalar.W q P Y z)^3*Real.sin frameCap

theorem fixed_trig : (478/625 : ℝ)≤Real.cos frameCap ∧
    (3221/5000 : ℝ)≤Real.sin frameCap := by
  have hc := cos_lower_six (show (0:ℝ)≤7/10 by norm_num)
  have hs := sin_lower_seven (show (0:ℝ)≤7/10 by norm_num)
  dsimp [frameCap]
  constructor <;> norm_num at * <;> linarith

theorem zeroDemand_antitone {q : ℝ} (hq : qLow≤q) :
    AntitoneOn (zeroDemand q) (Icc (0:ℝ) (11/10)) := by
  have hr : 0≤q-1/4 := by dsimp [qLow] at hq; linarith
  have hw := Real.sq_sqrt hr
  have hs := Real.sqrt_nonneg (q-1/4)
  have hk : 0≤Real.sqrt (q-1/4)-1 := by dsimp [qLow] at hq; nlinarith
  apply antiOn_of_hasDeriv_nonpos (d := fun h =>
    -Real.sin h/2-(Real.sqrt (q-1/4)-1)*Real.cos h)
  · unfold zeroDemand
    fun_prop
  · intro h hh
    have hd : HasDerivAt (fun x => 1/2+Real.cos x/2-(Real.sqrt (q-1/4)-1)*Real.sin x)
        (-Real.sin h/2-(Real.sqrt (q-1/4)-1)*Real.cos h) h := by
      have h' := (((Real.hasDerivAt_cos h).div_const 2).const_add (1/2)).fun_sub
        ((Real.hasDerivAt_sin h).const_mul (Real.sqrt (q-1/4)-1))
      convert h' using 1
    exact hd
  · intro h hh
    have hsin := CrossedZeroReserve.sin_nonneg (Ioo_subset_Icc_self hh)
    have hsq := pow_le_pow_left₀ hh.1.le hh.2.le 2
    have hcos : 0≤Real.cos h := by linarith [Real.one_sub_sq_div_two_le_cos (x := h)]
    have hm := mul_nonneg hk hcos
    linarith

theorem zeroDemand_reserve {q h : ℝ} (hqL : qLow≤q) (hq : q≤qCap)
    (hh : h∈Icc (39/200 : ℝ) (11/10)) :
    1+7/1000<zeroDemand q h+charge*h := by
  have hr : 0≤q-1/4 := by dsimp [qLow] at hqL; linarith
  have hw := Real.sq_sqrt hr
  have hs := Real.sqrt_nonneg (q-1/4)
  have hk : Real.sqrt (q-1/4)-1≤183/200 := by dsimp [qCap] at hq; nlinarith
  have hf := CrossedZeroReserve.strict hk hh
  dsimp [zeroDemand]
  linarith

theorem K_hasDerivAt {q P Y z : ℝ} (hr : 0<q-(1-V P Y z)^2) :
    HasDerivAt (K q P Y) (K1 q P Y z) z := by
  have hv := (hasDerivAt_const z (1:ℝ)).sub (V_hasDerivAt P Y z)
  have hw := SmallWrongScalar.W_hasDerivAt hr
  have hd := (((hv.mul_const (Real.cos frameCap)).const_add (1/2)).sub
    ((hw.sub_const 1).mul_const (Real.sin frameCap))).add
      (((hasDerivAt_id z).const_sub frameCap).const_mul charge)
  convert hd using 1
  · rfl
  · dsimp [K1]
    ring

theorem ratio_hasDerivAt {q P Y z : ℝ} (hr : 0<q-(1-V P Y z)^2) :
    HasDerivAt (fun z => (1-V P Y z)/SmallWrongScalar.W q P Y z)
      (q*U P Y z/(SmallWrongScalar.W q P Y z)^3) z := by
  have hw : SmallWrongScalar.W q P Y z≠0 := (Real.sqrt_pos.2 hr).ne'
  have hw2 : (SmallWrongScalar.W q P Y z)^2=q-(1-V P Y z)^2 := Real.sq_sqrt hr.le
  have hd := ((hasDerivAt_const z (1:ℝ)).sub (V_hasDerivAt P Y z)).div
    (SmallWrongScalar.W_hasDerivAt hr) hw
  convert hd using 1
  simp only [Pi.sub_apply]
  obtain ⟨w,hwdef⟩ : ∃ w,w=SmallWrongScalar.W q P Y z := ⟨_,rfl⟩
  rw [←hwdef] at hw hw2 ⊢
  rw [show q=w^2+(1-V P Y z)^2 by linarith]
  field_simp
  ring

theorem K1_hasDerivAt {q P Y z : ℝ} (hr : 0<q-(1-V P Y z)^2) :
    HasDerivAt (K1 q P Y) (K2 q P Y z) z := by
  have hd := ((U_hasDerivAt P Y z).mul
    (((ratio_hasDerivAt hr).mul_const (Real.sin frameCap)).const_add
      (Real.cos frameCap))).sub_const charge
  convert hd using 1
  · rfl
  · dsimp [K2]
    ring

theorem root_uniform_bounds {q P Y z : ℝ} (S : CrossedSmallWrongScalar.CapData q P Y)
    (hz : z∈Icc 0 frameCap) (hv : V P Y z∈Icc (2/5 : ℝ) (1/2)) :
    0<SmallWrongScalar.W q P Y z ∧ SmallWrongScalar.W q P Y z<383/200 ∧
      1267/1250<U P Y z := by
  have hb := CrossedSmallWrongScalar.root_bounds S hz hv
  have hw0 : 0<SmallWrongScalar.W q P Y z := Real.sqrt_pos.2 hb.1
  have hw2 : (SmallWrongScalar.W q P Y z)^2=q-(1-V P Y z)^2 :=
    Real.sq_sqrt hb.1.le
  have hC2 := pow_le_pow_left₀ (show (0:ℝ)≤1/2 by norm_num)
    (show 1/2≤1-V P Y z by linarith [hv.2]) 2
  have hw : SmallWrongScalar.W q P Y z<383/200 := by
    have hq := S.ceiling
    dsimp [qCap] at hq
    nlinarith
  have hu : 1267/1250<U P Y z := by linarith [hb.2.2.1,hv.2]
  exact ⟨hw0,hw,hu⟩

theorem K1_contact_lower {q P Y z : ℝ} (S : CrossedSmallWrongScalar.CapData q P Y)
    (hz : z∈Icc 0 frameCap) (hv : V P Y z=1/2) :
    -(3/40 : ℝ)≤K1 q P Y z := by
  obtain ⟨hw0,hw,hu⟩ := root_uniform_bounds S hz (by rw [hv]; norm_num)
  have hc := fixed_trig.1
  have hs := fixed_trig.2
  have hs0 : 0≤Real.sin frameCap := by linarith
  have hr : (1/2 : ℝ)/(383/200)≤(1/2)/SmallWrongScalar.W q P Y z :=
    (div_le_div_iff₀ (by norm_num) hw0).2 (by linarith)
  have hm := mul_le_mul hr hs (by norm_num : (0:ℝ)≤3221/5000)
    (div_nonneg (by norm_num) hw0.le)
  have hi : 478/625+((1/2)/(383/200))*(3221/5000)≤
      Real.cos frameCap+((1/2)/SmallWrongScalar.W q P Y z)*Real.sin frameCap := by
    linarith
  have hp := mul_le_mul hu.le hi (by norm_num :
      (0:ℝ)≤478/625+((1/2)/(383/200))*(3221/5000)) (by linarith : 0≤U P Y z)
  dsimp [K1,charge]
  rw [hv]
  norm_num at hp ⊢
  linarith

theorem K2_lower {q P Y z : ℝ} (S : CrossedSmallWrongScalar.CapData q P Y)
    (hz : z∈Icc 0 frameCap) (hv : V P Y z∈Icc (2/5 : ℝ) (1/2)) :
    2/3≤K2 q P Y z := by
  obtain ⟨hw0,hw,hu⟩ := root_uniform_bounds S hz hv
  have hc := fixed_trig.1
  have hs := fixed_trig.2
  have hs0 : 0≤Real.sin frameCap := by linarith
  have hu0 : 0≤U P Y z := by linarith
  have hu2 := pow_le_pow_left₀ (show (0:ℝ)≤1267/1250 by norm_num) hu.le 2
  have hw3 := pow_le_pow_left₀ hw0.le hw.le 3
  have hq0 : 0≤q := by have hh := S.floor; dsimp [qLow] at hh; linarith
  have hn1 := mul_le_mul S.floor hu2 (by norm_num [qLow] : (0:ℝ)≤(1267/1250)^2) hq0
  have hn := mul_le_mul hn1 hs (by norm_num : (0:ℝ)≤3221/5000)
    (mul_nonneg hq0 (sq_nonneg (U P Y z)))
  let n0 : ℝ := qLow*(1267/1250)^2*(3221/5000)
  have hn0 : 0≤n0 := by norm_num [n0,qLow]
  have hcross1 := mul_le_mul_of_nonneg_left hw3 hn0
  have hcross2 := mul_le_mul_of_nonneg_right hn
    (show (0:ℝ)≤(383/200)^3 by norm_num)
  have hquot : n0/(383/200)^3≤
      (q*(U P Y z)^2*Real.sin frameCap)/(SmallWrongScalar.W q P Y z)^3 := by
    apply (div_le_div_iff₀ (by norm_num) (pow_pos hw0 3)).2
    exact hcross1.trans hcross2
  have hfirst := mul_le_mul hv.1 hc (by norm_num : (0:ℝ)≤478/625)
    (by linarith [hv.1] : 0≤V P Y z)
  have hextra : 0≤V P Y z*((1-V P Y z)/SmallWrongScalar.W q P Y z*
      Real.sin frameCap) := by
    exact mul_nonneg (by linarith [hv.1])
      (mul_nonneg (div_nonneg (by linarith [hv.2]) hw0.le) hs0)
  dsimp [K2]
  have hid : q*(U P Y z)^2/(SmallWrongScalar.W q P Y z)^3*Real.sin frameCap=
      (q*(U P Y z)^2*Real.sin frameCap)/(SmallWrongScalar.W q P Y z)^3 := by ring
  rw [hid]
  norm_num [n0,qLow] at hquot
  nlinarith

theorem K_contact_loss {q P Y Z z : ℝ} (S : CrossedSmallWrongScalar.CapData q P Y)
    (hZ : Z∈Icc 0 frameCap) (hz : z∈Icc 0 frameCap) (hZz : Z≤z)
    (hcontact : V P Y Z=1/2) (hv : V P Y z∈Icc (2/5 : ℝ) (1/2)) :
    K q P Y Z-27/6400≤K q P Y z := by
  have hdom {t : ℝ} (ht : t∈Icc Z z) :
      t∈Icc 0 frameCap ∧ V P Y t∈Icc (2/5 : ℝ) (1/2) := by
    have hi : t∈Icc 0 frameCap := ⟨hZ.1.trans ht.1,ht.2.trans hz.2⟩
    have hlo := CrossedSmallWrongScalar.V_antitone S hi hz ht.2
    have hhi := CrossedSmallWrongScalar.V_antitone S hZ hi ht.1
    exact ⟨hi,⟨hv.1.trans hlo,by linarith⟩⟩
  have htan := curvature_tangent (κ := (2/3 : ℝ))
    (show z∈Icc Z z from ⟨hZz,le_rfl⟩) (show Z∈Icc Z z from ⟨le_rfl,hZz⟩)
    (fun t ht => K_hasDerivAt (CrossedSmallWrongScalar.root_bounds S
      (hdom ht).1 (hdom ht).2).1)
    (fun t ht => K1_hasDerivAt (CrossedSmallWrongScalar.root_bounds S
      (hdom ht).1 (hdom ht).2).1)
    (fun t ht => K2_lower S (hdom ht).1 (hdom ht).2)
  have hslope := K1_contact_lower S hZ hcontact
  have hm := mul_le_mul_of_nonneg_right hslope (sub_nonneg.mpr hZz)
  nlinarith [sq_nonneg (z-Z-9/80)]

/-- The right HG-angle endpoint has negative first derivative uniformly
over the intrinsic wrong-sign cap. -/
theorem fixed_right_negative {q C w : ℝ} (hq : qLow≤q)
    (hC : C∈Icc (1/2 : ℝ) (3/5)) (hw : 0<w) (hw2 : w^2=q-C^2) :
    -C*Real.sin frameCap-(w-1)*Real.cos frameCap+charge<0 := by
  let x := C-1/2
  have hx : x∈Icc (0:ℝ) (1/10) := by dsimp [x]; constructor <;> linarith [hC.1,hC.2]
  have hx2 : x^2≤x/10 := by
    nlinarith [mul_nonneg hx.1 (show 0≤1/10-x by linarith [hx.2])]
  have hline : 3829/2000-(3/10)*x<w := by
    have hid : q-C^2-(3829/2000-(3/10)*x)^2=
        q-19577/5000+359/4000000+(1487/10000)*x-(109/100)*x^2 := by
      dsimp [x]
      ring
    have hline0 : 0<3829/2000-(3/10)*x := by linarith [hx.2]
    have hq' := hq
    dsimp [qLow] at hq'
    nlinarith
  have hw1 : 0≤w-1 := by linarith [hx.2]
  have hcs := mul_le_mul_of_nonneg_left fixed_trig.2 (by linarith [hC.1] : 0≤C)
  have hwc := mul_le_mul_of_nonneg_left fixed_trig.1 hw1
  have hlin := mul_le_mul_of_nonneg_right hline.le (show (0:ℝ)≤478/625 by norm_num)
  dsimp [x,charge] at *
  nlinarith

theorem chargedDemand_endpoint_lower {q P Y z h L : ℝ}
    (S : CrossedSmallWrongScalar.CapData q P Y)
    (hz : z∈Icc 0 frameCap) (hv : V P Y z∈Icc (2/5 : ℝ) (1/2))
    (hh : h∈Icc z frameCap)
    (hleft : L≤SmallWrongScalar.demand q P Y 0 z) (hright : L≤K q P Y z) :
    L≤chargedDemand q P Y z h := by
  let C := 1-V P Y z
  let w := SmallWrongScalar.W q P Y z
  let f := fun s : ℝ => C*Real.cos s-(w-1)*Real.sin s+charge*s
  let d := fun s : ℝ => -C*Real.sin s-(w-1)*Real.cos s+charge
  let dd := fun s : ℝ => -C*Real.cos s+(w-1)*Real.sin s
  let ddd := fun s : ℝ => C*Real.sin s+(w-1)*Real.cos s
  have hb := CrossedSmallWrongScalar.root_bounds S hz hv
  have hC : C∈Icc (1/2 : ℝ) (3/5) := by dsimp [C]; constructor <;> linarith [hv.1,hv.2]
  have hw0 : 0<w := Real.sqrt_pos.2 hb.1
  have hw2 : w^2=q-C^2 := Real.sq_sqrt hb.1.le
  have hw1 : 0≤w-1 := by dsimp [w]; linarith [hb.2.1,hv.1]
  have hf (s : ℝ) : HasDerivAt f (d s) s := by
    have h := (((Real.hasDerivAt_cos s).const_mul C).fun_sub
      ((Real.hasDerivAt_sin s).const_mul (w-1))).fun_add
        ((hasDerivAt_id' s).const_mul charge)
    convert h using 1
    simp only [d]; ring
  have hd (s : ℝ) : HasDerivAt d (dd s) s := by
    have h := (((Real.hasDerivAt_sin s).const_mul (-C)).fun_sub
      ((Real.hasDerivAt_cos s).const_mul (w-1))).add_const charge
    convert h using 1
    simp only [dd]; ring
  have hdd (s : ℝ) : HasDerivAt dd (ddd s) s := by
    have h := ((Real.hasDerivAt_cos s).const_mul (-C)).fun_add
      ((Real.hasDerivAt_sin s).const_mul (w-1))
    convert h using 1
    simp only [ddd]; ring
  have hm := SecondWord.MinimumCalculus.endpoint_minimum hh
    (fun s _ => hf s) (fun s _ => hd s) (fun s _ => hdd s)
    (by
      intro s hs
      have ht := transport_trig (show s∈Icc 0 frameCap from ⟨hz.1.trans hs.1,hs.2⟩)
      exact add_nonneg (mul_nonneg (by linarith [hC.1]) ht.2.2.1)
        (mul_nonneg hw1 (by linarith [ht.1])))
    (fixed_right_negative S.floor hC hw0 hw2)
  have hl : L-1/2+charge*z≤f z := by
    dsimp [SmallWrongScalar.demand,f,C,w] at hleft ⊢
    simp only [zero_add] at hleft
    linarith
  have hr : L-1/2+charge*z≤f frameCap := by
    dsimp [K,chargedDemand,f,C,w] at hright ⊢
    linarith
  have hmin := le_min hl hr
  dsimp [chargedDemand,f,C,w] at *
  linarith

end SquaresInCircles.Eight.TableFree.CrossedWrongEndpointCalculus
