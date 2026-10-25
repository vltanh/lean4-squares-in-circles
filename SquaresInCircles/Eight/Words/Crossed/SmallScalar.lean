module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TotallySplit
public import SquaresInCircles.Eight.Frames.Signed.OppositeHardSigns
public import SquaresInCircles.Eight.Owners.Positive.SmallScalar
public import SquaresInCircles.Eight.Words.Crossed.SmallWrongScalar
public import SquaresInCircles.Eight.Words.Crossed.ClampBudget

/-!
# Eight squares: the small normal crossed cap

Exact-circle identities strengthen the positive-small cap bounds of `PositiveSmallScalar` to
`T < 1` (`T_lt_one`). They give strict concavity of the required H tangent on the whole
intrinsic GA interval, including scalar comparison angles up to `1.1` (`curvature_lower`). Once
the source budget captures `Y > 48/49` and `r < .01`, the whole interval has a GA-alignment gain
of `z/100` (`alignment_gain`).
-/

section
/-!
## The large-side circle cap and its two intrinsic endpoints

The scalar keeps the circle q (`CapData`). Its hard-contact interval ends at the unique
zero-transverse contact (`contact_endpoint`). The required H tangent `demand` is strictly concave
on that whole interval, also on the enlarged comparison angles up to `.9` (`curvature_lower`).
After the crossed-frame capture its derivative has a uniform positive reserve toward GA
alignment (`alignment_gain`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CrossedLargeScalar
open PositiveSmallScalar EndpointRotationPenalty

structure CapData (q P Y : ℝ) : Prop where
  P_mem : P∈Icc (1/2 : ℝ) (177/250)
  Y_mem : Y∈Icc (1 : ℝ) (13/10)
  circle : (P+1)^2+Y^2=q
  ceiling : q≤qCap

def demand (q P Y r z : ℝ) : ℝ :=
  1/2+(1-V P Y z)*Real.cos (r+z)-(W q P Y z-1)*Real.sin (r+z)

def demandD (q P Y r z : ℝ) : ℝ := -F1 q P Y (-r) (r+z)
def demandDD (q P Y r z : ℝ) : ℝ := -F2 q P Y (-r) (r+z)

theorem CapData.floor {q P Y : ℝ} (I : CapData q P Y) : (13/4 : ℝ)≤q := by
  nlinarith [I.circle,I.P_mem.1,I.Y_mem.1]

theorem CapData.tangent_range {q P Y : ℝ} (I : CapData q P Y) :
    Y-1/2∈Icc (1/2 : ℝ) SignedOppositeHardEnvelope.pivot := by
  constructor
  · linarith [I.Y_mem.1]
  · have hq := I.ceiling
    dsimp [qCap,SignedOppositeHardEnvelope.pivot] at *
    nlinarith [I.circle,I.P_mem.1,I.Y_mem.1]

theorem V_upper {q P Y z : ℝ} (I : CapData q P Y)
    (hz : z∈Icc 0 frameCap) : V P Y z≤P := by
  have hc := mul_le_mul_of_nonneg_left (Real.cos_le_one z)
    (show 0≤P by linarith [I.P_mem.1])
  have hs := mul_nonneg (show 0≤Y by linarith [I.Y_mem.1]) (transport_trig hz).2.2.1
  dsimp [V]
  linarith

theorem V_antitone {q P Y : ℝ} (I : CapData q P Y) :
    AntitoneOn (V P Y) (Icc 0 frameCap) := by
  intro x hx z hz hxz
  have hc := CorrelatedSameBlock.cos_anti hx hz hxz
  have hs := CorrelatedSameBlock.sin_mono hx hz hxz
  have hp := mul_le_mul_of_nonneg_left hc (show 0≤P by linarith [I.P_mem.1])
  have hY := mul_le_mul_of_nonneg_left hs (show 0≤Y by linarith [I.Y_mem.1])
  dsimp [V]
  linarith

theorem contact_angle_short {q P Y z : ℝ} (I : CapData q P Y)
    (hz : z∈Icc 0 frameCap) (hV : 1/2≤V P Y z) : z<1/5 := by
  have hi : (1/5:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have ht := transport_trig hi
  have hcap : V P Y (1/5)≤(177/250)*Real.cos (1/5)-Real.sin (1/5) := by
    have hp := mul_le_mul_of_nonneg_right I.P_mem.2 (show 0≤Real.cos (1/5) by linarith [ht.1])
    have hy := mul_le_mul_of_nonneg_right I.Y_mem.1 ht.2.2.1
    dsimp [V]
    linarith
  have hright : V P Y (1/5)<1/2 := by
    have hc := cos_upper_four (show (0:ℝ)≤1/5 by norm_num)
    have hs := Real.sin_ge_sub_cube (show (0:ℝ)≤1/5 by norm_num)
    nlinarith
  by_contra! hnot
  have hm := V_antitone I hi hz hnot
  linarith

theorem contact_endpoint {q P Y z : ℝ} (I : CapData q P Y)
    (hz : z∈Icc 0 frameCap) (hV : 1/2≤V P Y z) :
    ∃ Z,z≤Z ∧ Z<1/5 ∧ V P Y Z=1/2 ∧
      ∀ x∈Icc 0 Z,1/2≤V P Y x := by
  have hshort := contact_angle_short I hz hV
  have hright : V P Y (1/5)<1/2 := by
    by_contra! hbad
    exact (lt_irrefl (1/5:ℝ)) (contact_angle_short I (by norm_num [frameCap]) hbad)
  obtain ⟨Z,hZ,heq⟩ := intermediate_value_Icc hshort.le
    (show ContinuousOn (fun x => -V P Y x) (Icc z (1/5)) by unfold V; fun_prop)
    (show -(1/2:ℝ)∈Icc (-V P Y z) (-V P Y (1/5)) by constructor <;> linarith)
  have hZE : V P Y Z=1/2 := by linarith
  have hZu : Z<1/5 := by
    apply lt_of_le_of_ne hZ.2
    intro he
    rw [he] at hZE
    linarith
  refine ⟨Z,hZ.1,hZu,hZE,?_⟩
  intro x hx
  have hZi : Z∈Icc 0 frameCap := by
    dsimp [frameCap]
    exact ⟨by linarith [hz.1,hZ.1],by linarith⟩
  simpa only [hZE] using V_antitone I ⟨hx.1,hx.2.trans hZi.2⟩ hZi hx.2

structure PointBounds (q P Y z : ℝ) : Prop where
  radicand : 0<q-(V P Y z)^2
  V_mem : V P Y z∈Icc (1/2 : ℝ) (177/250)
  W_mem : W q P Y z∈Ioo (33/20 : ℝ) (383/200)
  U_lower : 1≤U P Y z
  T_mem : T q P Y z∈Ioo (0:ℝ) (183/200)
  difference : (T q P Y z)^2+2*T q P Y z*U P Y z=2*P+1

theorem point_bounds {q P Y z : ℝ} (I : CapData q P Y)
    (hz : z∈Icc 0 frameCap) (hV : 1/2≤V P Y z) : PointBounds q P Y z := by
  have hvU := V_upper I hz
  have hv : V P Y z∈Icc (1/2 : ℝ) (177/250) := ⟨hV,hvU.trans I.P_mem.2⟩
  have hv2 := pow_le_pow_left₀ (show 0≤V P Y z by linarith) hv.2 2
  have hr : (33/20 : ℝ)^2<q-(V P Y z)^2 := by linarith [I.floor]
  have hr0 : 0<q-(V P Y z)^2 := by linarith
  have hw0 : 0≤W q P Y z := Real.sqrt_nonneg _
  have hw2 : (W q P Y z)^2=q-(V P Y z)^2 := Real.sq_sqrt hr0.le
  have hw : W q P Y z∈Ioo (33/20 : ℝ) (383/200) := by
    constructor
    · exact lt_of_pow_lt_pow_left₀ 2 hw0 (by rw [hw2]; exact hr)
    · have hq : q≤9789/2500 := I.ceiling
      have hv1 := pow_le_pow_left₀ (by norm_num) hv.1 2
      exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) (by rw [hw2]; linarith)
  have htr := transport_trig hz
  have hu0 : 0≤U P Y z := by
    have hp := mul_nonneg (show 0≤P by linarith [I.P_mem.1]) htr.2.2.1
    have hy := mul_nonneg (show 0≤Y by linarith [I.Y_mem.1]) (show 0≤Real.cos z by linarith [htr.1])
    dsimp [U]
    linarith
  have hrot := rotation_identity P Y z
  have hvP2 := pow_le_pow_left₀ (show 0≤V P Y z by linarith) hvU 2
  have hu : 1≤U P Y z := by
    have hY2 := pow_le_pow_left₀ (by norm_num) I.Y_mem.1 2
    exact le_of_pow_le_pow_left₀ two_ne_zero hu0 (by linarith)
  have hdiff : (T q P Y z)^2+2*T q P Y z*U P Y z=2*P+1 := by
    dsimp [T]
    linear_combination hw2-hrot-I.circle
  have ht0 : 0<T q P Y z := by
    have hws : (U P Y z)^2<(W q P Y z)^2 := by linarith [I.circle,I.P_mem.1]
    have h := lt_of_pow_lt_pow_left₀ 2 hw0 hws
    dsimp [T]
    linarith
  have htU : T q P Y z<183/200 := by dsimp [T]; linarith [hw.2]
  exact ⟨hr0,hv,hw,hu,⟨ht0,htU⟩,hdiff⟩

theorem curvature_lower {q P Y r z : ℝ} (I : CapData q P Y)
    (hz : z∈Icc 0 frameCap) (hV : 1/2≤V P Y z)
    (hh : r+z∈Icc 0 (9/10 : ℝ)) :
    1/10≤F2 q P Y (-r) (r+z) := by
  have B := point_bounds I hz hV
  have hw : 0<W q P Y z := by linarith [B.W_mem.1]
  have hVT := mul_le_mul B.V_mem.2 B.T_mem.2.le B.T_mem.1.le
    (by norm_num : (0:ℝ)≤177/250)
  have hcoef : 1/5≤1+2*T1 q P Y z := by
    have hid : (1+2*T1 q P Y z)*W q P Y z=
        W q P Y z-2*V P Y z*T q P Y z := by
      dsimp [T1]
      field_simp [hw.ne']
      ring
    have hb : (1/5)*W q P Y z≤(1+2*T1 q P Y z)*W q P Y z := by
      rw [hid]
      nlinarith [B.W_mem.1]
    exact le_of_mul_le_mul_right hb hw
  have hT2 : 0≤T2 q P Y z := by
    dsimp [T2]
    have hq0 : 0≤q := by linarith [I.floor]
    exact div_nonneg (mul_nonneg B.T_mem.1.le
      (add_nonneg (mul_nonneg hq0 (by linarith [B.U_lower]))
        (mul_nonneg (sq_nonneg (V P Y z)) hw.le))) (pow_nonneg hw.le 3)
  have hs : 0≤Real.sin (r+z) := Real.sin_nonneg_of_nonneg_of_le_pi hh.1
    (by linarith [hh.2,Real.pi_gt_three])
  have hc : 1/2≤Real.cos (r+z) := by
    have h2 := pow_le_pow_left₀ hh.1 hh.2 2
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := r+z)]
  have hfirst := mul_le_mul hc hcoef (by norm_num : (0:ℝ)≤1/5)
    (by linarith : 0≤Real.cos (r+z))
  have hsecond := mul_nonneg hs (show 0≤1-T q P Y z+T2 q P Y z by linarith [B.T_mem.2])
  dsimp [F2]
  rw [show -r+(r+z)=z by ring]
  nlinarith

theorem demand_identity (q P Y r z : ℝ) :
    demand q P Y r z=3/2-V P Y (-r)-F q P Y (-r) (r+z) := by
  have hi := inverse_identity P Y (-r) (r+z)
  rw [show -r+(r+z)=z by ring] at hi
  dsimp [demand,F,T]
  rw [show -r+(r+z)=z by ring]
  nlinarith

theorem demand_hasDerivAt {q P Y r z : ℝ}
    (hr : 0<q-(V P Y z)^2) :
    HasDerivAt (demand q P Y r) (demandD q P Y r z) z := by
  have hd := (F_hasDerivAt (q := q) (P := P) (Y := Y) (Θ := -r) (h := r+z)
    (by simpa only [show -r+(r+z)=z by ring] using hr)).comp z
    ((hasDerivAt_id z).const_add r)
  have he : demand q P Y r=(fun x => 3/2-V P Y (-r)-F q P Y (-r) (r+x)) :=
    funext (demand_identity q P Y r)
  rw [he]
  convert hd.const_sub (3/2-V P Y (-r)) using 1 <;> dsimp [demandD]
  ring

theorem demandD_hasDerivAt {q P Y r z : ℝ}
    (hr : 0<q-(V P Y z)^2) :
    HasDerivAt (demandD q P Y r) (demandDD q P Y r z) z := by
  have hd := (F1_hasDerivAt (q := q) (P := P) (Y := Y) (Θ := -r) (h := r+z)
    (by simpa only [show -r+(r+z)=z by ring] using hr)).comp z
    ((hasDerivAt_id z).const_add r)
  have hd2 := hd.neg
  rw [mul_one] at hd2
  exact hd2

theorem endpoint_minimum {q P Y r Z z : ℝ} (I : CapData q P Y)
    (hr : r∈Icc 0 frameCap) (hZ : Z∈Icc 0 (1/5 : ℝ))
    (hV : ∀x∈Icc 0 Z,1/2≤V P Y x) (hz : z∈Icc 0 Z) :
    min (demand q P Y r 0) (demand q P Y r Z)≤demand q P Y r z := by
  have hconc : ConcaveOn ℝ (Icc 0 Z) (demand q P Y r) := by
    apply concave_of_deriv2 (f' := demandD q P Y r) (f'' := demandDD q P Y r)
    · intro x hx
      have hxi : x∈Icc 0 frameCap := ⟨hx.1,by dsimp [frameCap]; linarith [hx.2,hZ.2]⟩
      exact demand_hasDerivAt (point_bounds I hxi (hV x hx)).radicand
    · intro x hx
      have hxi : x∈Icc 0 frameCap := ⟨hx.1,by dsimp [frameCap]; linarith [hx.2,hZ.2]⟩
      exact demandD_hasDerivAt (point_bounds I hxi (hV x hx)).radicand
    · intro x hx
      have hxi : x∈Icc 0 frameCap := ⟨hx.1,by dsimp [frameCap]; linarith [hx.2,hZ.2]⟩
      have hhi : r+x∈Icc 0 (9/10 : ℝ) := by
        dsimp [frameCap] at hr
        constructor <;> linarith [hr.1,hr.2,hx.1,hx.2,hZ.2]
      have hc := curvature_lower I hxi (hV x hx) hhi
      dsimp [demandDD]
      linarith
  have hh := concave_endpoint_reserve (k := 0) (by norm_num) hz
    (show ConcaveOn ℝ (Icc 0 Z) (fun x => demand q P Y r x+(0:ℝ)/2*x^2) by simpa using hconc)
  simpa using hh

theorem zero_T_upper {q P Y Z : ℝ} (I : CapData q P Y)
    (hZ : Z∈Icc 0 frameCap) (heq : V P Y Z=1/2) :
    T q P Y Z<797/1000 := by
  have B := point_bounds I hZ heq.ge
  have hU2 : P^2+3/4≤(U P Y Z)^2 := by
    have hr := rotation_identity P Y Z
    rw [heq] at hr
    nlinarith [I.Y_mem.1]
  have hP2 := pow_le_pow_left₀ (show 0≤P by linarith [I.P_mem.1]) I.P_mem.2 2
  by_contra! hT
  have hT2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤797/1000) hT 2
  have hTU := mul_le_mul_of_nonneg_right hT (show 0≤U P Y Z by linarith [B.U_lower])
  have hbound : 2*(797/1000)*U P Y Z≤2*P+1-(797/1000 : ℝ)^2 := by
    nlinarith [B.difference]
  have hbound2 := pow_le_pow_left₀ (show 0≤2*(797/1000)*U P Y Z by linarith [B.U_lower]) hbound 2
  nlinarith [I.P_mem.2]

theorem endpoint_slope {q P Y r Z : ℝ} (I : CapData q P Y)
    (hr : r∈Icc 0 (1/25 : ℝ)) (hZ : Z∈Icc 0 (1/5 : ℝ))
    (heq : V P Y Z=1/2) : F1 q P Y (-r) (r+Z)< -(1/150) := by
  have hZi : Z∈Icc 0 frameCap := ⟨hZ.1,by dsimp [frameCap]; linarith [hZ.2]⟩
  have B := point_bounds I hZi heq.ge
  have hT := zero_T_upper I hZi heq
  have hh : r+Z∈Icc 0 (6/25 : ℝ) := by
    constructor <;> linarith [hr.1,hr.2,hZ.1,hZ.2]
  have hs : Real.sin (r+Z)≤6/25 := (Real.sin_le hh.1).trans hh.2
  have hs0 : 0≤Real.sin (r+Z) := Real.sin_nonneg_of_nonneg_of_le_pi hh.1
    (by linarith [hh.2,Real.pi_gt_three])
  have hc : 607/625≤Real.cos (r+Z) := by
    have h2 := pow_le_pow_left₀ hh.1 hh.2 2
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := r+Z)]
  have hw : 0<W q P Y Z := by linarith [B.W_mem.1]
  have hdiv : T q P Y Z/(383/100)≤T q P Y Z/(2*W q P Y Z) := by
    apply (div_le_div_iff₀ (by norm_num) (by positivity)).2
    nlinarith [mul_nonneg B.T_mem.1.le (show 0≤383/200-W q P Y Z by linarith [B.W_mem.2])]
  have hdivmul := mul_le_mul_of_nonneg_left hdiv hs0
  have hcoef : 0≤Real.cos (r+Z)-Real.sin (r+Z)/(383/100) := by
    nlinarith
  have htmul := mul_le_mul_of_nonneg_right hT.le hcoef
  have hid : F1 q P Y (-r) (r+Z)=
      Real.cos (r+Z)*(T q P Y Z-1)+
        Real.sin (r+Z)*(1-T q P Y Z/(2*W q P Y Z)) := by
    dsimp [F1,T1]
    rw [show -r+(r+Z)=Z by ring,heq]
    field_simp [hw.ne']
    ring
  rw [hid]
  nlinarith

/-- At the captured crossing, GA alignment strictly decreases the
required H tangent, with a fixed gain per unit of G-frame motion. -/
theorem alignment_gain {q P Y r Z z : ℝ} (I : CapData q P Y)
    (hr : r∈Icc 0 (1/25 : ℝ)) (hZ : Z∈Icc 0 (1/5 : ℝ))
    (heq : V P Y Z=1/2) (hV : ∀x∈Icc 0 Z,1/2≤V P Y x)
    (hz : z∈Icc 0 Z) :
    z/150≤demand q P Y r z-demand q P Y r 0 := by
  have hmono : MonotoneOn (fun x => F1 q P Y (-r) (r+x)) (Icc 0 Z) := by
    apply monoOn_of_hasDeriv_nonneg (d := fun x => F2 q P Y (-r) (r+x))
    · intro x hx
      have hxi : x∈Icc 0 frameCap := ⟨hx.1,by dsimp [frameCap]; linarith [hx.2,hZ.2]⟩
      have hb := point_bounds I hxi (hV x hx)
      have hd := (F1_hasDerivAt (q := q) (P := P) (Y := Y) (Θ := -r) (h := r+x)
        (by simpa only [show -r+(r+x)=x by ring] using hb.radicand)).comp x
        ((hasDerivAt_id x).const_add r)
      exact hd.continuousAt.continuousWithinAt
    · intro x hx
      have hxi : x∈Icc 0 frameCap := ⟨hx.1.le,by dsimp [frameCap]; linarith [hx.2,hZ.2]⟩
      have hb := point_bounds I hxi (hV x (Ioo_subset_Icc_self hx))
      have hd := (F1_hasDerivAt (q := q) (P := P) (Y := Y) (Θ := -r) (h := r+x)
        (by simpa only [show -r+(r+x)=x by ring] using hb.radicand)).comp x
        ((hasDerivAt_id x).const_add r)
      rw [mul_one] at hd
      exact hd
    · intro x hx
      have hxi : x∈Icc 0 frameCap := ⟨hx.1.le,by dsimp [frameCap]; linarith [hx.2,hZ.2]⟩
      have hhi : r+x∈Icc 0 (9/10 : ℝ) := by
        constructor <;> linarith [hr.1,hr.2,hx.1,hx.2,hZ.2]
      exact (by norm_num : (0:ℝ)≤1/10).trans
        (curvature_lower I hxi (hV x (Ioo_subset_Icc_self hx)) hhi)
  have hend := endpoint_slope I hr hZ heq
  have hd : ∀x∈Icc 0 Z,HasDerivAt (demand q P Y r) (demandD q P Y r x) x := by
    intro x hx
    have hxi : x∈Icc 0 frameCap := ⟨hx.1,by dsimp [frameCap]; linarith [hx.2,hZ.2]⟩
    exact demand_hasDerivAt (point_bounds I hxi (hV x hx)).radicand
  have hk : ∀x∈Ioo 0 Z,(1/150 : ℝ)≤demandD q P Y r x := by
    intro x hx
    have hm := hmono (Ioo_subset_Icc_self hx) (right_mem_Icc.mpr hZ.1) hx.2.le
    dsimp [demandD]
    linarith
  have hh := derivative_reserve
    (show ContinuousOn (demand q P Y r) (Icc 0 Z) from
      fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => hd x (Ioo_subset_Icc_self hx)) hk
    (left_mem_Icc.mpr hZ.1) hz hz.1
  linarith

end SquaresInCircles.Eight.CrossedLargeScalar
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CrossedSmallScalar
open PositiveSmallScalar CrossedLargeScalar EndpointRotationPenalty

structure CapData (q P Y : ℝ) : Prop where
  P_mem : P∈Icc (1/2 : ℝ) (397/500)
  Y_mem : Y∈Icc (167/200 : ℝ) 1
  circle : (P+1)^2+Y^2=q
  floor : qLow≤q
  ceiling : q≤qCap

theorem CapData.positive {q P Y : ℝ} (S : CapData q P Y) : PositiveSmallScalar.CapData q P Y :=
  ⟨S.P_mem,S.Y_mem,S.circle.le,S.ceiling⟩

theorem CapData.wide {q P Y : ℝ} (S : CapData q P Y) : CrossedSmallWrongScalar.CapData q P Y :=
  ⟨⟨S.P_mem.1,by linarith [S.P_mem.2]⟩,
    ⟨by linarith [S.Y_mem.1],S.Y_mem.2⟩,S.circle,S.floor,S.ceiling⟩

theorem primary_lower {q P Y : ℝ} (S : CapData q P Y) : 3537/5000<P := by
  have hy2 := pow_le_pow_left₀ (show 0≤Y by linarith [S.Y_mem.1]) S.Y_mem.2 2
  have hq := S.floor
  dsimp [qLow] at hq
  nlinarith [S.circle,S.P_mem.1]

theorem T_lt_one {q P Y z : ℝ} (S : CapData q P Y)
    (hz : z∈Icc 0 frameCap) (hv : 1/2≤V P Y z) : T q P Y z<1 := by
  have B := PositiveSmallScalar.point_bounds S.positive hz hv
  have hVupper := PositiveSmallScalar.V_upper S.positive hz
  have hV2 := pow_le_pow_left₀ (show 0≤V P Y z by linarith) hVupper 2
  have hu0 := (CrossedSmallWrongScalar.U_pos S.wide hz).le
  have hrot := rotation_identity P Y z
  have hu : Y≤U P Y z := by nlinarith [S.Y_mem.1]
  have hw2 : (W q P Y z)^2=q-(V P Y z)^2 := Real.sq_sqrt B.radicand_pos.le
  have hUP : P<U P Y z := by linarith [S.P_mem.2,S.Y_mem.1]
  by_contra! ht
  have hw : U P Y z+1≤W q P Y z := by dsimp [T] at ht; linarith
  have hwSq := pow_le_pow_left₀ (show 0≤U P Y z+1 by linarith) hw 2
  nlinarith [S.circle]

theorem curvature_lower {q P Y r z : ℝ} (S : CapData q P Y)
    (hz : z∈Icc 0 frameCap) (hv : 1/2≤V P Y z)
    (hh : r+z∈Icc (0:ℝ) (11/10)) :
    1/25≤F2 q P Y (-r) (r+z) := by
  have B := PositiveSmallScalar.point_bounds S.positive hz hv
  have hT := T_lt_one S hz hv
  have hs := CrossedZeroReserve.sin_nonneg hh
  have hc : 79/200≤Real.cos (r+z) := by
    have hsq := pow_le_pow_left₀ hh.1 hh.2 2
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := r+z)]
  have hfirst := mul_le_mul hc B.coefficient_lower
    (by norm_num : (0:ℝ)≤4999/47875) (by linarith : 0≤Real.cos (r+z))
  have hsecond := mul_nonneg hs (show 0≤1-T q P Y z+T2 q P Y z by
    linarith [B.T2_nonneg])
  dsimp [F2]
  rw [show -r+(r+z)=z by ring]
  nlinarith

theorem contact_endpoint {q P Y z : ℝ} (S : CapData q P Y)
    (hz : z∈Icc 0 frameCap) (hv : 1/2≤V P Y z) :
    ∃ Z,z≤Z ∧ Z∈Ioo (39/200 : ℝ) (2/5) ∧ V P Y Z=1/2 ∧
      ∀x∈Icc 0 Z,1/2≤V P Y x := by
  obtain ⟨Z,hzZ,hZu,hZE,hall⟩ := PositiveSmallScalar.contact_endpoint S.positive hz hv
  have hZi : Z∈Icc 0 frameCap := ⟨by linarith [hz.1],by dsimp [frameCap]; linarith⟩
  have hZl : 39/200<Z := by
    by_contra! hbad
    have hm := CrossedSmallWrongScalar.V_antitone S.wide hZi
      (show (39/200 : ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hbad
    have hl := CrossedSmallWrongScalar.contact_lower_test S.wide
    rw [hZE] at hm
    linarith
  exact ⟨Z,hzZ,⟨hZl,hZu⟩,hZE,hall⟩

theorem endpoint_minimum {q P Y r Z z : ℝ} (S : CapData q P Y)
    (hr : r∈Icc 0 frameCap) (hZ : Z∈Icc (0:ℝ) (2/5))
    (hV : ∀x∈Icc 0 Z,1/2≤V P Y x) (hz : z∈Icc 0 Z) :
    min (demand q P Y r 0) (demand q P Y r Z)≤demand q P Y r z := by
  have hconc : ConcaveOn ℝ (Icc 0 Z) (demand q P Y r) := by
    apply concave_of_deriv2 (f' := demandD q P Y r) (f'' := demandDD q P Y r)
    · intro x hx
      have hi : x∈Icc 0 frameCap := ⟨hx.1,by dsimp [frameCap]; linarith [hx.2,hZ.2]⟩
      exact CrossedLargeScalar.demand_hasDerivAt
        (PositiveSmallScalar.point_bounds S.positive hi (hV x hx)).radicand_pos
    · intro x hx
      have hi : x∈Icc 0 frameCap := ⟨hx.1,by dsimp [frameCap]; linarith [hx.2,hZ.2]⟩
      exact CrossedLargeScalar.demandD_hasDerivAt
        (PositiveSmallScalar.point_bounds S.positive hi (hV x hx)).radicand_pos
    · intro x hx
      have hi : x∈Icc 0 frameCap := ⟨hx.1,by dsimp [frameCap]; linarith [hx.2,hZ.2]⟩
      have hh : r+x∈Icc (0:ℝ) (11/10) := by
        dsimp [frameCap] at hr
        constructor <;> linarith [hr.1,hr.2,hx.1,hx.2,hZ.2]
      have hc := curvature_lower S hi (hV x hx) hh
      dsimp [demandDD]
      linarith
  exact hconc.min_le_of_mem_Icc (left_mem_Icc.mpr hZ.1)
    (right_mem_Icc.mpr hZ.1) hz

theorem aligned_root_bounds {q P Y : ℝ} (S : CapData q P Y) :
    1<W q P Y 0 ∧ W q P Y 0<37/20 ∧
      (1-P)^2+(W q P Y 0-1)^2<(9/10 : ℝ)^2 := by
  have B := PositiveSmallScalar.point_bounds S.positive
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) (by simpa [V] using S.P_mem.1)
  have hw2 : (W q P Y 0)^2=q-P^2 := by
    have h : (W q P Y 0)^2=q-(V P Y 0)^2 := Real.sq_sqrt B.radicand_pos.le
    rw [h,show V P Y 0=P by simp [V]]
  have hw0 := B.W_pos
  have hP := primary_lower S
  have hqL := S.floor
  have hq := S.ceiling
  dsimp [qLow,qCap] at hqL hq
  have hw1 : 1<W q P Y 0 := by
    have hp2 := pow_le_pow_left₀ (show 0≤P by linarith [S.P_mem.1]) S.P_mem.2 2
    nlinarith
  have hwu : W q P Y 0<37/20 := by
    have hp2 := pow_le_pow_left₀ (show (0:ℝ)≤3537/5000 by norm_num) hP.le 2
    nlinarith
  have hpsq := pow_le_pow_left₀ (show 0≤1-P by linarith [S.P_mem.2])
    (show 1-P≤1463/5000 by linarith) 2
  have hwsq := pow_le_pow_left₀ (show 0≤W q P Y 0-1 by linarith)
    (show W q P Y 0-1≤17/20 by linarith) 2
  exact ⟨hw1,hwu,by nlinarith⟩

/-- The charged aligned endpoint grows by at least (p-.9)r.  The .9
support bound follows from a single strict squared-radius comparison. -/
theorem aligned_growth {q P Y r : ℝ} (S : CapData q P Y)
    (hr : r∈Icc 0 frameCap) :
    3/2-P+(charge-9/10)*r≤demand q P Y r 0+charge*r := by
  let f := fun x : ℝ => demand q P Y x 0+charge*x
  let d := fun x : ℝ => -(1-P)*Real.sin x-(W q P Y 0-1)*Real.cos x+charge
  have hd (x : ℝ) : HasDerivAt f (d x) x := by
    have hh := ((((Real.hasDerivAt_cos x).const_mul (1-P)).const_add (1/2)).sub
      ((Real.hasDerivAt_sin x).const_mul (W q P Y 0-1))).add
        ((hasDerivAt_id x).const_mul charge)
    have hf : f=fun x => 1/2+(1-P)*Real.cos x-(W q P Y 0-1)*Real.sin x+charge*id x := by
      funext y
      simp only [f,demand,V,add_zero,Real.cos_zero,Real.sin_zero,mul_one,mul_zero,sub_zero,id]
    rw [hf]
    convert hh using 1
    simp only [d]
    ring
  have hk (x : ℝ) : charge-9/10≤d x := by
    have hrad := (aligned_root_bounds S).2.2
    have hrot := rotation_identity (W q P Y 0-1) (-(1-P)) x
    have hother := sq_nonneg (U (W q P Y 0-1) (-(1-P)) x)
    have hbound : (1-P)*Real.sin x+(W q P Y 0-1)*Real.cos x<9/10 := by
      dsimp [V,U] at hrot hother
      nlinarith
    dsimp [d]
    linarith
  have hh := derivative_reserve
    (show ContinuousOn f (Icc 0 frameCap) from fun x _ => (hd x).continuousAt.continuousWithinAt)
    (fun x _ => hd x) (fun x _ => hk x)
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hr hr.1
  have h0 : demand q P Y 0 0=3/2-P := by
    simp only [demand,V,add_zero,Real.cos_zero,Real.sin_zero,mul_one,mul_zero,sub_zero]
    ring
  simp only [f] at hh
  linarith

theorem tight_primary {q P Y : ℝ} (S : CapData q P Y) (hY : 48/49≤Y) :
    P<1439/2000 := by
  have hysq := pow_le_pow_left₀ (show (0:ℝ)≤48/49 by norm_num) hY 2
  have hq := S.ceiling
  dsimp [qCap] at hq
  nlinarith [S.circle,S.P_mem.1]

theorem tight_contact_angle {q P Y Z : ℝ} (S : CapData q P Y) (hY : 48/49≤Y)
    (hZ : Z∈Icc 0 frameCap) (hV : 1/2≤V P Y Z) : Z<21/100 := by
  have hi : (21/100 : ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have ht := transport_trig hi
  have hP := tight_primary S hY
  have hp := mul_le_mul_of_nonneg_right hP.le (show 0≤Real.cos (21/100 : ℝ) by linarith [ht.1])
  have hy := mul_le_mul_of_nonneg_right hY ht.2.2.1
  have hc := cos_upper_four (show (0:ℝ)≤21/100 by norm_num)
  have hs := Real.sin_ge_sub_cube (show (0:ℝ)≤21/100 by norm_num)
  have hright : V P Y (21/100)<1/2 := by
    dsimp [V]
    nlinarith
  by_contra! hbad
  have hm := PositiveSmallScalar.V_antitone S.positive hi hZ hbad
  linarith

theorem tight_zero_T {q P Y Z : ℝ} (S : CapData q P Y) (hY : 48/49≤Y)
    (hZ : Z∈Icc 0 frameCap) (hV : V P Y Z=1/2) : T q P Y Z<101/125 := by
  have B := PositiveSmallScalar.point_bounds S.positive hZ hV.ge
  have hP := tight_primary S hY
  have hrot := rotation_identity P Y Z
  rw [hV] at hrot
  have hu0 := (CrossedSmallWrongScalar.U_pos S.wide hZ).le
  have hu2 : (U P Y Z)^2=q-2*P-5/4 := by nlinarith [S.circle]
  have hu : 1107/1000<U P Y Z := by
    have hq := S.floor
    dsimp [qLow] at hq
    nlinarith
  have hw2 : (W q P Y Z)^2=q-1/4 := by
    have h : (W q P Y Z)^2=q-(V P Y Z)^2 := Real.sq_sqrt B.radicand_pos.le
    rw [h,hV]; norm_num
  have hw : W q P Y Z<383/200 := by
    have hq := S.ceiling
    dsimp [qCap] at hq
    nlinarith [B.W_pos]
  dsimp [T]
  linarith

theorem endpoint_slope {q P Y r Z : ℝ} (S : CapData q P Y) (hY : 48/49≤Y)
    (hr : r∈Icc 0 (1/100 : ℝ)) (hZ : Z∈Icc 0 (21/100 : ℝ))
    (hV : V P Y Z=1/2) : F1 q P Y (-r) (r+Z)< -(1/100) := by
  have hZi : Z∈Icc 0 frameCap := ⟨hZ.1,by dsimp [frameCap]; linarith [hZ.2]⟩
  have B := PositiveSmallScalar.point_bounds S.positive hZi hV.ge
  have hT := tight_zero_T S hY hZi hV
  have hh : r+Z∈Icc 0 (11/50 : ℝ) := by
    constructor <;> linarith [hr.1,hr.2,hZ.1,hZ.2]
  have hs := (Real.sin_le hh.1).trans hh.2
  have hs0 := CrossedZeroReserve.sin_nonneg
    (show r+Z∈Icc (0:ℝ) (11/10) from ⟨hh.1,by linarith [hh.2]⟩)
  have hc : 4879/5000≤Real.cos (r+Z) := by
    have hsq := pow_le_pow_left₀ hh.1 hh.2 2
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := r+Z)]
  have hw := B.W_pos
  have hw2 : (W q P Y Z)^2=q-1/4 := by
    have h : (W q P Y Z)^2=q-(V P Y Z)^2 := Real.sq_sqrt B.radicand_pos.le
    rw [h,hV]; norm_num
  have hwu : W q P Y Z<383/200 := by
    have hq := S.ceiling
    dsimp [qCap] at hq
    nlinarith
  have hdiv : T q P Y Z/(383/100)≤T q P Y Z/(2*W q P Y Z) := by
    apply (div_le_div_iff₀ (by norm_num) (by positivity)).2
    nlinarith [mul_nonneg B.T_pos.le (show 0≤383/200-W q P Y Z by linarith)]
  have hdivmul := mul_le_mul_of_nonneg_left hdiv hs0
  have hcoef : 0≤Real.cos (r+Z)-Real.sin (r+Z)/(383/100) := by nlinarith
  have htmul := mul_le_mul_of_nonneg_right hT.le hcoef
  have hid : F1 q P Y (-r) (r+Z)=Real.cos (r+Z)*(T q P Y Z-1)+
      Real.sin (r+Z)*(1-T q P Y Z/(2*W q P Y Z)) := by
    dsimp [F1,T1]
    rw [show -r+(r+Z)=Z by ring,hV]
    field_simp [hw.ne']
    ring
  rw [hid]
  nlinarith

theorem alignment_gain {q P Y r Z z : ℝ} (S : CapData q P Y) (hY : 48/49≤Y)
    (hr : r∈Icc 0 (1/100 : ℝ)) (hZ : Z∈Icc 0 (21/100 : ℝ))
    (hcontact : V P Y Z=1/2) (hV : ∀x∈Icc 0 Z,1/2≤V P Y x)
    (hz : z∈Icc 0 Z) : z/100≤demand q P Y r z-demand q P Y r 0 := by
  have hmono : MonotoneOn (fun x => F1 q P Y (-r) (r+x)) (Icc 0 Z) := by
    apply monoOn_of_hasDeriv_nonneg (d := fun x => F2 q P Y (-r) (r+x))
    · intro x hx
      have hi : x∈Icc 0 frameCap := ⟨hx.1,by dsimp [frameCap]; linarith [hx.2,hZ.2]⟩
      have hb := PositiveSmallScalar.point_bounds S.positive hi (hV x hx)
      have hd := (F1_hasDerivAt (q := q) (P := P) (Y := Y) (Θ := -r) (h := r+x)
        (by simpa only [show -r+(r+x)=x by ring] using hb.radicand_pos)).comp x
        ((hasDerivAt_id x).const_add r)
      exact hd.continuousAt.continuousWithinAt
    · intro x hx
      have hi : x∈Icc 0 frameCap := ⟨hx.1.le,by dsimp [frameCap]; linarith [hx.2,hZ.2]⟩
      have hb := PositiveSmallScalar.point_bounds S.positive hi (hV x (Ioo_subset_Icc_self hx))
      have hd := (F1_hasDerivAt (q := q) (P := P) (Y := Y) (Θ := -r) (h := r+x)
        (by simpa only [show -r+(r+x)=x by ring] using hb.radicand_pos)).comp x
        ((hasDerivAt_id x).const_add r)
      rw [mul_one] at hd
      exact hd
    · intro x hx
      have hi : x∈Icc 0 frameCap := ⟨hx.1.le,by dsimp [frameCap]; linarith [hx.2,hZ.2]⟩
      have hh : r+x∈Icc (0:ℝ) (11/10) := by
        constructor <;> linarith [hr.1,hr.2,hx.1,hx.2,hZ.2]
      exact (by norm_num : (0:ℝ)≤1/25).trans
        (curvature_lower S hi (hV x (Ioo_subset_Icc_self hx)) hh)
  have hend := endpoint_slope S hY hr hZ hcontact
  have hd : ∀x∈Icc 0 Z,HasDerivAt (demand q P Y r) (demandD q P Y r x) x := by
    intro x hx
    have hi : x∈Icc 0 frameCap := ⟨hx.1,by dsimp [frameCap]; linarith [hx.2,hZ.2]⟩
    exact CrossedLargeScalar.demand_hasDerivAt
      (PositiveSmallScalar.point_bounds S.positive hi (hV x hx)).radicand_pos
  have hk : ∀x∈Ioo 0 Z,(1/100 : ℝ)≤demandD q P Y r x := by
    intro x hx
    have hm := hmono (Ioo_subset_Icc_self hx) (right_mem_Icc.mpr hZ.1) hx.2.le
    dsimp [demandD]
    linarith
  have hh := derivative_reserve
    (show ContinuousOn (demand q P Y r) (Icc 0 Z) from
      fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => hd x (Ioo_subset_Icc_self hx)) hk
    (left_mem_Icc.mpr hZ.1) hz hz.1
  linarith

end SquaresInCircles.Eight.CrossedSmallScalar
end
end
end
