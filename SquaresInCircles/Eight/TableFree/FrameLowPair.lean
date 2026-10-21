module

public import SquaresInCircles.Eight.TableFree.FrameLowScalars

/-!
# The full original low/low frame-pair inequality

Uncompiled source draft.  All points on the closed low outer arc, both
signed tangents and every weak feasible forward axis are retained.
The two secondary-axis supports use the circle and the actual arc
endpoints.  The primary-axis supports use monotonicity on that same arc
and concavity on one whole angular interval.  No frame-window premise,
coefficient table, interval cover or axis re-selection occurs here.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameLowPair
open FramePair FrameCircleArc FrameLowArc FrameLowScalars

def width (x : ℝ) : ℝ := (1+Real.sin x+Real.cos x)/2
def cost (i k : Bool) (b B x : ℝ) : ℝ :=
  x-(9/100)*(Real.cos x+Real.sin x-1)+sign i*L b-sign k*L B
def secondary (i k : Bool) (b B x : ℝ) : ℝ :=
  sign i*b+A B*Real.sin x-sign k*B*Real.cos x-width x
def primary (k : Bool) (b B x : ℝ) : ℝ :=
  A b-A B*Real.cos x-sign k*B*Real.sin x-width x

theorem quadrant {x : ℝ} (hx : x∈Icc 0 (Real.pi/2)) :
    0≤Real.sin x ∧ Real.sin x≤1 ∧ 0≤Real.cos x ∧ Real.cos x≤1 := by
  exact ⟨Real.sin_nonneg_of_nonneg_of_le_pi hx.1
    (by linarith [hx.2,Real.pi_pos]),Real.sin_le_one x,
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hx.1,Real.pi_pos],hx.2⟩,
    Real.cos_le_one x⟩

theorem pairWidth_eq {x : ℝ} (hx : x∈Icc 0 (Real.pi/2)) : pairWidth x=width x := by
  have hh := quadrant hx
  simp [pairWidth,width,abs_of_nonneg hh.1,abs_of_nonneg hh.2.2.1]

theorem pi_lower : (157/50:ℝ)<Real.pi := by
  linarith [Arithmetic.pi_hand_enclosure.1]

theorem signed_label_bounds (i : Bool) {b : ℝ} (hb : b∈Icc 0 b1) :
    -L1≤sign i*L b ∧ sign i*L b≤L1 := by
  have hh := L_bounds hb
  cases i <;> norm_num [sign] <;> constructor <;> linarith [L1_bounds.1]

theorem minus_label_le (i : Bool) {b : ℝ} (hb : b∈Icc 0 b1) :
    -L b≤sign i*L b := by
  have hh := (L_bounds hb).1
  cases i <;> norm_num [sign] <;> linarith

theorem source_loss (i : Bool) {b : ℝ} (hb : b∈Icc 0 b1) :
    -epsilon i≤sign i*(L b-lambda i*b) := by
  cases i with
  | false =>
      have hh := (L_bounds hb).2.1
      norm_num [epsilon,sign,lambda]
      linarith
  | true =>
      have he : -(1/50000:ℝ)≤L1-(189/200)*b1 := by
        linarith [L1_bounds.1,b1_bounds.2]
      simpa [epsilon,sign,lambda] using
        label_loss_lower hb (by norm_num : (0:ℝ)≤1/50000) he

theorem source_loss_negative (i : Bool) {b : ℝ} (hb : b∈Icc 0 b1) :
    -(13/1000:ℝ)≤sign i*(L b-(24/25)*b) := by
  cases i with
  | false =>
      have hh := (L_bounds hb).2.1
      have hbU := hb.2.trans b1_bounds.2.le
      norm_num [sign]
      linarith
  | true =>
      have he : -(13/1000:ℝ)≤L1-(24/25)*b1 := by
        linarith [L1_bounds.1,b1_bounds.2]
      simpa [sign] using
        label_loss_lower hb (by norm_num : (0:ℝ)≤13/1000) he

/-! ## The positive-target secondary axis -/

theorem full_circle_support (i : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc 0 b1)
    (hm : 0≤secondary i true b B x) : G i x≤cost i true b B x := by
  have hλ : 0≤lambda i := by linarith [(parameters i).1]
  have hscaled := mul_nonneg hλ hm
  have hsource := source_loss i hb
  have hc := circle_linear_lower
    (A_circle ⟨hB.1,hB.2.trans b1_mem.2⟩)
    (-u-lambda i*Real.sin x) (lambda i*Real.cos x-v)
  have hn : Real.sqrt ((-u-lambda i*Real.sin x)^2+
      (lambda i*Real.cos x-v)^2)=N i x := by
    unfold N
    congr 1
    ring
  rw [hn] at hc
  dsimp [secondary,cost,width,G,L] at *
  simp only [sign,ite_true,one_mul] at *
  nlinarith

def tailSlope (x : ℝ) : ℝ := (23/50)*Real.sin x+Real.cos x

theorem tailSlope_deriv (x : ℝ) :
    HasDerivAt tailSlope ((23/50)*Real.cos x-Real.sin x) x := by
  convert ((Real.hasDerivAt_sin x).const_mul (23/50)).add
    (Real.hasDerivAt_cos x) using 1 <;> dsimp [tailSlope] <;> ring

theorem tailSlope_antitone (i : Bool) :
    AntitoneOn tailSlope (Icc (cut i) (Real.pi/2)) := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun x _ => (tailSlope_deriv x).continuousAt.continuousWithinAt
  · exact fun x _ => tailSlope_deriv x
  · intro x hx
    have hz : 0≤cut i := by linarith [(parameters i).2.2.2.2.1]
    have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos] : -(Real.pi/2)≤cut i) hx.2.le hx.1.le
    have hc := Real.cos_le_cos_of_nonneg_of_le_pi hz
      (by linarith [hx.2,Real.pi_pos]) hx.1.le
    have ht := cut_trig i
    have hnum : (23/50)*cosHi i-sinLo i<0 := by
      cases i <;> norm_num [cosHi,sinLo]
    linarith [ht.1,ht.2.2.2]

theorem target_positive_antitone (i : Bool) {x : ℝ}
    (hx : x∈Icc (cut i) (Real.pi/2)) :
    AntitoneOn (linear (-u-lambda i*Real.sin x) (lambda i*Real.cos x-v))
      (Icc 0 b1) := by
  have hx0 : 0≤x := by linarith [hx.1,(parameters i).2.2.2.2.1]
  have hq := quadrant ⟨hx0,hx.2⟩
  have hλ : 0≤lambda i := by linarith [(parameters i).1]
  have hcoef : 0≤u+lambda i*Real.sin x := by
    exact add_nonneg (by norm_num [u]) (mul_nonneg hλ hq.1)
  have ht := tailSlope_antitone i ⟨le_rfl,hx.1.trans hx.2⟩ hx hx.1
  have htrig := cut_trig i
  have htail : tailSlope x≤(23/50)*sinHi i+cosHi i := by
    dsimp [tailSlope] at ht ⊢
    linarith [htrig.2.1,htrig.2.2.2]
  have hscaled := mul_le_mul_of_nonneg_left htail hλ
  have hnum : (23/50)*u+lambda i*((23/50)*sinHi i+cosHi i)-v<0 := by
    cases i <;> norm_num [u,v,lambda,sinHi,cosHi]
  apply antiOn_of_hasDeriv_nonpos
  · intro B hB
    exact (linear_hasDerivAt ⟨hB.1,hB.2.trans b1_mem.2⟩ _ _).continuousAt.continuousWithinAt
  · intro B hB
    exact linear_hasDerivAt ⟨hB.1.le,hB.2.le.trans b1_mem.2⟩ _ _
  · intro B hB
    have hb := slope_bounds (Ioo_subset_Icc_self hB)
    have hmul := mul_le_mul_of_nonneg_left hb.2.le hcoef
    dsimp [Ad,slope,tailSlope] at hmul hscaled ⊢
    nlinarith

theorem endpoint_support (i : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc 0 b1)
    (hx : x∈Icc (cut i) (Real.pi/2))
    (hm : 0≤secondary i true b B x) : E i x≤cost i true b B x := by
  have hλ : 0≤lambda i := by linarith [(parameters i).1]
  have hscaled := mul_nonneg hλ hm
  have hsource := source_loss i hb
  have htarget := target_positive_antitone i hx hB ⟨b1_mem.1,le_rfl⟩ hB.2
  dsimp [linear] at htarget
  rw [A_b1] at htarget
  dsimp [secondary,cost,width,E,pCoeff,nCoeff,L,L1] at *
  simp only [sign,ite_true,one_mul] at *
  nlinarith

theorem secondary_positive (i : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc 0 b1)
    (hx : x∈Icc 0 (Real.pi/2)) (hm : 0≤secondary i true b B x) :
    (91/100:ℝ)<cost i true b B x := by
  by_cases hcut : x≤cut i
  · exact (full_circle_lower i ⟨hx.1,hcut⟩).trans_le
      (full_circle_support i hb hB hm)
  · exact (endpoint_continuation i ⟨(lt_of_not_ge hcut).le,hx.2⟩).trans_le
      (endpoint_support i hb hB ⟨(lt_of_not_ge hcut).le,hx.2⟩ hm)

/-! ## The negative-target secondary axis -/

theorem negative_target_endpoint {B x : ℝ} (hB : B∈Icc 0 b1)
    (hx : x∈Icc 0 (Real.pi/2)) :
    min (linear (u-(24/25)*Real.sin x) (v-(24/25)*Real.cos x) 0)
      (linear (u-(24/25)*Real.sin x) (v-(24/25)*Real.cos x) b1)≤
        linear (u-(24/25)*Real.sin x) (v-(24/25)*Real.cos x) B := by
  by_cases hp : 0≤u-(24/25)*Real.sin x
  · exact linear_endpoint_lower hp (by norm_num) b1_mem.2 hB
  · have hq : 0≤v-(24/25)*Real.cos x := by
      have hc := (quadrant hx).2.2.2
      dsimp [v]
      linarith
    exact (min_le_left _ _).trans
      (linear_monotone (le_of_not_ge hp) hq
        ⟨le_rfl,b1_mem.1.trans b1_mem.2⟩
        ⟨hB.1,hB.2.trans b1_mem.2⟩ hB.1)

def negativeEndpoint (x : ℝ) : ℝ :=
  x-13/1000+L1+57/100+(39/100-(24/25)*b1)*Real.cos x+
    (39/100-(24/25)*a1)*Real.sin x

theorem negativeEndpoint_deriv (x : ℝ) :
    HasDerivAt negativeEndpoint
      (1-(39/100-(24/25)*b1)*Real.sin x-
        ((24/25)*a1-39/100)*Real.cos x) x := by
  convert (((((hasDerivAt_id x).sub_const (13/1000)).add_const L1).add_const
    (57/100)).add ((Real.hasDerivAt_cos x).const_mul
      (39/100-(24/25)*b1))).add ((Real.hasDerivAt_sin x).const_mul
        (39/100-(24/25)*a1)) using 1 <;> dsimp [negativeEndpoint] <;> ring

theorem negativeEndpoint_lower {x : ℝ} (hx : x∈Icc 0 (Real.pi/2)) :
    (91/100:ℝ)<negativeEndpoint x := by
  have hp : 0≤39/100-(24/25)*b1 := by linarith [b1_bounds.2]
  have hn : 0≤(24/25)*a1-39/100 := by linarith [a1_bounds.1]
  have hm : MonotoneOn negativeEndpoint (Icc 0 (Real.pi/2)) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun y _ => (negativeEndpoint_deriv y).continuousAt.continuousWithinAt
    · exact fun y _ => negativeEndpoint_deriv y
    · intro y hy
      have hq := quadrant (Ioo_subset_Icc_self hy)
      have hps := mul_le_mul_of_nonneg_left hq.2.1 hp
      have hnc := mul_le_mul_of_nonneg_left hq.2.2.2 hn
      have he : a1=4*b1 := by dsimp [b1]; ring
      nlinarith [a1_bounds.2,b1_bounds.1]
  have h0 : (91/100:ℝ)<negativeEndpoint 0 := by
    simp only [negativeEndpoint,Real.cos_zero,Real.sin_zero,mul_one,mul_zero,
      zero_sub,add_zero]
    linarith [L1_bounds.1,b1_bounds.2]
  exact h0.trans_le (hm ⟨le_rfl,by positivity⟩ hx hx.1)

theorem secondary_negative (i : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc 0 b1)
    (hx : x∈Icc 0 (Real.pi/2)) (hm : 0≤secondary i false b B x) :
    (91/100:ℝ)<cost i false b B x := by
  have hscaled := mul_nonneg (show (0:ℝ)≤24/25 by norm_num) hm
  have hsource := source_loss_negative i hb
  have htarget := negative_target_endpoint hB hx
  have haxial := axial_lower
    (show (24/25)*a0-39/100≤969/1000 by linarith [a0_bounds.2]) hx
  have hend := negativeEndpoint_lower hx
  have hh : min
      (557/1000+x+(39/100)*Real.cos x-((24/25)*a0-39/100)*Real.sin x)
      (negativeEndpoint x)≤cost i false b B x := by
    have hzero : linear (u-(24/25)*Real.sin x) (v-(24/25)*Real.cos x) 0=
        (u-(24/25)*Real.sin x)*a0 := by simp [linear]
    have hlast : linear (u-(24/25)*Real.sin x) (v-(24/25)*Real.cos x) b1=
        (u-(24/25)*Real.sin x)*a1+(v-(24/25)*Real.cos x)*b1 := by
      simp [linear,A_b1]
    rw [hzero,hlast] at htarget
    rcases le_total ((u-(24/25)*Real.sin x)*a0)
      ((u-(24/25)*Real.sin x)*a1+(v-(24/25)*Real.cos x)*b1) with h | h
    · rw [min_eq_left h] at htarget
      apply (min_le_left _ _).trans
      dsimp [secondary,cost,width,L,linear] at *
      simp only [sign,ite_false,neg_one_mul] at *
      nlinarith
    · rw [min_eq_right h] at htarget
      apply (min_le_right _ _).trans
      dsimp [secondary,cost,width,L,linear,negativeEndpoint,L1] at *
      simp only [sign,ite_false,neg_one_mul] at *
      nlinarith
  exact (lt_min haxial hend).trans_le hh

/-! ## The two primary-axis signs -/

theorem trig_thirteen_tenths :
    (93/100:ℝ)<Real.sin (13/10:ℝ) ∧ (13/50:ℝ)<Real.cos (13/10:ℝ) := by
  have hs := Real.sin_ge_sub_cube (show (0:ℝ)≤13/10 by norm_num)
  have hc := cos_lower_six (show (0:ℝ)≤13/10 by norm_num)
  norm_num at hs hc
  constructor <;> linarith

theorem primary_positive_cut {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc 0 b1)
    (hx : x∈Icc 0 (Real.pi/2)) (hm : 0≤primary true b B x) :
    (13/10:ℝ)<x := by
  by_contra! hxU
  have ha := A_low_bounds hb
  have hA := A_low_bounds hB
  have hq := quadrant hx
  have hAc := mul_le_mul_of_nonneg_right hA.1 hq.2.2.1
  have hBs := mul_nonneg hB.1 hq.1
  have hsupport : 0<1/2-a0+(a1+1/2)*Real.cos x+(1/2)*Real.sin x := by
    apply harmonic_pos_of_endpoints
      (show 0≤a1+1/2 by linarith [a1_bounds.1]) (by norm_num) (by norm_num)
      (by linarith [pi_lower] : (13/10:ℝ)≤Real.pi/2) ⟨hx.1,hxU⟩
    · simp only [Real.cos_zero,Real.sin_zero,mul_one,mul_zero,add_zero]
      linarith [a0_bounds.2,a1_bounds.1]
    · have hp := mul_lt_mul_of_pos_left trig_thirteen_tenths.2
        (show 0<a1+1/2 by linarith [a1_bounds.1])
      nlinarith [trig_thirteen_tenths.1,a0_bounds.2,a1_bounds.1]
  dsimp [primary,width,sign] at hm
  norm_num at hm
  nlinarith

theorem primary_source_endpoint {λ b : ℝ} (hb : b∈Icc 0 b1)
    (hλ : 0≤λ) (hλU : λ≤5/4) :
    linear (-(u+λ)) (-v) b1≤linear (-(u+λ)) (-v) b := by
  have hcoef : 0≤u+λ := by dsimp [u]; linarith
  have hm : AntitoneOn (linear (-(u+λ)) (-v)) (Icc 0 b1) := by
    apply antiOn_of_hasDeriv_nonpos
    · intro z hz
      exact (linear_hasDerivAt ⟨hz.1,hz.2.trans b1_mem.2⟩ _ _).continuousAt.continuousWithinAt
    · intro z hz
      exact linear_hasDerivAt ⟨hz.1.le,hz.2.le.trans b1_mem.2⟩ _ _
    · intro z hz
      have hs := (slope_bounds (Ioo_subset_Icc_self hz)).2
      have hh := mul_le_mul_of_nonneg_left hs.le hcoef
      dsimp [Ad,slope,u,v] at *
      nlinarith
  exact hm hb ⟨b1_mem.1,le_rfl⟩ hb.2

theorem primary_positive_target_endpoint {B x : ℝ} (hB : B∈Icc 0 b1)
    (hx : x∈Icc 0 (Real.pi/2)) :
    linear (-u+(9/10)*Real.cos x) ((9/10)*Real.sin x-v) b1≤
      linear (-u+(9/10)*Real.cos x) ((9/10)*Real.sin x-v) B := by
  have hq := quadrant hx
  have hm : AntitoneOn (linear (-u+(9/10)*Real.cos x)
      ((9/10)*Real.sin x-v)) (Icc 0 b1) := by
    apply antiOn_of_hasDeriv_nonpos
    · intro z hz
      exact (linear_hasDerivAt ⟨hz.1,hz.2.trans b1_mem.2⟩ _ _).continuousAt.continuousWithinAt
    · intro z hz
      exact linear_hasDerivAt ⟨hz.1.le,hz.2.le.trans b1_mem.2⟩ _ _
    · intro z hz
      have hs := slope_bounds (Ioo_subset_Icc_self hz)
      have hh := mul_nonneg hq.2.2.1 (show 0≤slope z by linarith [hs.1])
      have hu := mul_le_mul_of_nonneg_left hs.2.le (show 0≤u by norm_num [u])
      dsimp [Ad,slope,u,v] at *
      nlinarith
  exact hm hB ⟨b1_mem.1,le_rfl⟩ hB.2

def primaryPositiveEndpoint (x : ℝ) : ℝ :=
  x-2*L1+27/50-(9/10)*a1+
    (9/25+(9/10)*a1)*Real.cos x+(9/25+(9/10)*b1)*Real.sin x

theorem primaryPositiveEndpoint_lower {x : ℝ}
    (hx : x∈Icc (13/10:ℝ) (Real.pi/2)) :
    (91/100:ℝ)<primaryPositiveEndpoint x := by
  have hA : 0≤9/25+(9/10)*b1 := by linarith [b1_bounds.1]
  have hB : 0≤9/25+(9/10)*a1 := by linarith [a1_bounds.1]
  have hs := mul_le_mul_of_nonneg_left trig_thirteen_tenths.1.le hA
  have hc := mul_le_mul_of_nonneg_left trig_thirteen_tenths.2.le hB
  have hh := trig_concave_gt (α := 1)
    (m := 91/100+2*L1-27/50+(9/10)*a1)
    hA hB (by norm_num) le_rfl hx
    (by nlinarith [L1_bounds.2,a1_bounds.1,a1_bounds.2,b1_bounds.1])
    (by simp only [Real.sin_pi_div_two,Real.cos_pi_div_two,mul_one,mul_zero,add_zero];
        linarith [pi_lower,L1_bounds.2,a1_bounds.2,b1_bounds.1])
  dsimp [primaryPositiveEndpoint]
  nlinarith

theorem primary_positive (i : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc 0 b1)
    (hx : x∈Icc 0 (Real.pi/2)) (hm : 0≤primary true b B x) :
    (91/100:ℝ)<cost i true b B x := by
  have hcut := primary_positive_cut hb hB hx hm
  have hscalar := primaryPositiveEndpoint_lower ⟨hcut.le,hx.2⟩
  have hsrc := primary_source_endpoint hb
    (by norm_num : (0:ℝ)≤9/10) (by norm_num : (9/10:ℝ)≤5/4)
  have htgt := primary_positive_target_endpoint hB hx
  have hsign := minus_label_le i hb
  have hscaled := mul_nonneg (show (0:ℝ)≤9/10 by norm_num) hm
  dsimp [linear] at hsrc htgt
  rw [A_b1] at hsrc htgt
  dsimp [cost,primary,width,primaryPositiveEndpoint,L,L1] at *
  simp only [sign,ite_true,one_mul] at *
  nlinarith

def primaryNegativeZero (x : ℝ) : ℝ :=
  x-L1+143/200-(5/4)*a1+(107/200+(5/4)*a0)*Real.cos x+
    (107/200)*Real.sin x
def primaryNegativeLast (x : ℝ) : ℝ :=
  x+143/200-(5/4)*a1+(107/200+(5/4)*a1)*Real.cos x+
    (107/200-(5/4)*b1)*Real.sin x

theorem primaryNegativeZero_lower {x : ℝ} (hx : x∈Icc 0 (13/10:ℝ)) :
    (91/100:ℝ)<primaryNegativeZero x := by
  have hB : 0≤107/200+(5/4)*a0 := by linarith [a0_bounds.1]
  have hs := mul_le_mul_of_nonneg_left trig_thirteen_tenths.1.le
    (show (0:ℝ)≤107/200 by norm_num)
  have hc := mul_le_mul_of_nonneg_left trig_thirteen_tenths.2.le hB
  have hh := trig_concave_gt (α := 1)
    (m := 91/100+L1-143/200+(5/4)*a1)
    (by norm_num : (0:ℝ)≤107/200) hB (by norm_num)
    (by linarith [pi_lower] : (13/10:ℝ)≤Real.pi/2) hx
    (by simp only [Real.sin_zero,Real.cos_zero,mul_zero,mul_one,zero_add];
        linarith [L1_bounds.2,a1_bounds.2,a0_bounds.1])
    (by nlinarith [L1_bounds.2,a1_bounds.2,a0_bounds.1])
  dsimp [primaryNegativeZero]
  nlinarith

theorem primaryNegativeLast_lower {x : ℝ} (hx : x∈Icc 0 (13/10:ℝ)) :
    (91/100:ℝ)<primaryNegativeLast x := by
  have hA : 0≤107/200-(5/4)*b1 := by linarith [b1_bounds.2]
  have hB : 0≤107/200+(5/4)*a1 := by linarith [a1_bounds.1]
  have hs := mul_le_mul_of_nonneg_left trig_thirteen_tenths.1.le hA
  have hc := mul_le_mul_of_nonneg_left trig_thirteen_tenths.2.le hB
  have hh := trig_concave_gt (α := 1)
    (m := 91/100-143/200+(5/4)*a1)
    hA hB (by norm_num) (by linarith [pi_lower] : (13/10:ℝ)≤Real.pi/2) hx
    (by simp only [Real.sin_zero,Real.cos_zero,mul_zero,mul_one,zero_add]; linarith)
    (by nlinarith [a1_bounds.1,a1_bounds.2,b1_bounds.2])
  dsimp [primaryNegativeLast]
  nlinarith

theorem primary_negative_short (i : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc 0 b1)
    (hx : x∈Icc 0 (13/10:ℝ)) (hm : 0≤primary false b B x) :
    (91/100:ℝ)<cost i false b B x := by
  have hxq : x∈Icc 0 (Real.pi/2) :=
    ⟨hx.1,by linarith [hx.2,pi_lower]⟩
  have hq := quadrant hxq
  have hp : 0≤u+(5/4)*Real.cos x := by dsimp [u]; linarith [hq.2.2.1]
  have hsrc := primary_source_endpoint hb (by norm_num : (0:ℝ)≤5/4) le_rfl
  have htgt := linear_endpoint_lower (q := v-(5/4)*Real.sin x) hp
    (by norm_num : (0:ℝ)≤0) b1_mem.2 hB
  have hsign := minus_label_le i hb
  have hscaled := mul_nonneg (show (0:ℝ)≤5/4 by norm_num) hm
  have hzero := primaryNegativeZero_lower hx
  have hlast := primaryNegativeLast_lower hx
  have hh : min (primaryNegativeZero x) (primaryNegativeLast x)≤cost i false b B x := by
    dsimp [linear] at hsrc htgt
    rw [A_b1] at hsrc
    rw [A_zero,A_b1,mul_zero,add_zero] at htgt
    rcases le_total ((u+(5/4)*Real.cos x)*a0)
      ((u+(5/4)*Real.cos x)*a1+(v-(5/4)*Real.sin x)*b1) with h | h
    · rw [min_eq_left h] at htgt
      apply (min_le_left _ _).trans
      dsimp [cost,primary,width,primaryNegativeZero,L,L1] at *
      simp only [sign,ite_false,neg_one_mul] at *
      nlinarith
    · rw [min_eq_right h] at htgt
      apply (min_le_right _ _).trans
      dsimp [cost,primary,width,primaryNegativeLast,L,L1] at *
      simp only [sign,ite_false,neg_one_mul] at *
      nlinarith
  exact (lt_min hzero hlast).trans_le hh

theorem primary_negative (i : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc 0 b1)
    (hx : x∈Icc 0 (Real.pi/2)) (hm : 0≤primary false b B x) :
    (91/100:ℝ)<cost i false b B x := by
  by_cases hcut : x≤13/10
  · exact primary_negative_short i hb hB ⟨hx.1,hcut⟩ hm
  · have hsrc := (signed_label_bounds i hb).1
    have htgt := (L_bounds hB).1
    have hc := CorePairGeometry.charge_upper x
    rw [periodic_cost_quadrant hx] at hc
    have he : cost i false b B x=
        x-(9/100)*(Real.cos x+Real.sin x-1)+sign i*L b+L B := by
      simp [cost,sign]
    rw [he]
    nlinarith [L1_bounds.2]

/-! ## Original signed states and every weak axis -/

theorem state_cost_quadrant (s t : FramePair.State)
    (hs : s.branch=.low) (ht : t.branch=.low) {x : ℝ}
    (hx : x∈Icc 0 (Real.pi/2)) :
    s.cost t x=cost s.positive t.positive s.b t.b x := by
  rw [State.cost,periodic_cost_quadrant hx,state_low_label s hs,state_low_label t ht]
  dsimp [cost]
  ring

theorem state_secondary_quadrant (s t : FramePair.State)
    (hs : s.branch=.low) (ht : t.branch=.low) {x : ℝ}
    (hx : x∈Icc 0 (Real.pi/2)) :
    s.Feasible t 0 x ↔ 0≤secondary s.positive t.positive s.b t.b x := by
  simp only [State.Feasible,forwardMargin,Matrix.cons_val_zero,
    (state_low_chart s hs).1,(state_low_chart t ht).1,pairWidth_eq hx]
  rfl

theorem state_primary_quadrant (s t : FramePair.State)
    (hs : s.branch=.low) (ht : t.branch=.low) {x : ℝ}
    (hx : x∈Icc 0 (Real.pi/2)) :
    s.Feasible t 3 x ↔ 0≤primary t.positive s.b t.b x := by
  simp only [State.Feasible,forwardMargin,Matrix.cons_val_succ,Matrix.cons_val_zero,
    (state_low_chart s hs).1,(state_low_chart t ht).1,pairWidth_eq hx]
  rfl

theorem angle_pos (s t : FramePair.State) (hs : s.branch=.low) (ht : t.branch=.low)
    {x : ℝ} (hgap : (19/25:ℝ)≤s.gap t x) : 0<x := by
  have hso := low_offset_bounds s hs
  have hto := low_offset_bounds t ht
  dsimp [State.gap] at hgap
  linarith

theorem beyond_quadrant (s t : FramePair.State) (hs : s.branch=.low) (ht : t.branch=.low)
    {x : ℝ} (hx : Real.pi/2≤x) : (91/100:ℝ)<s.cost t x := by
  have hsrc := (signed_label_bounds s.positive (state_low_chart s hs).2).1
  have htgt := (signed_label_bounds t.positive (state_low_chart t ht).2).2
  have hc := CorePairGeometry.charge_upper x
  rw [State.cost,state_low_label s hs,state_low_label t ht]
  linarith [L1_bounds.2,pi_lower]

theorem source_secondary (s t : FramePair.State) (hs : s.branch=.low) (ht : t.branch=.low)
    {x : ℝ} (hgap : (19/25:ℝ)≤s.gap t x) (hm : s.Feasible t 0 x) :
    (91/100:ℝ)<s.cost t x := by
  by_cases hxU : x≤Real.pi/2
  · have hx : x∈Icc 0 (Real.pi/2) := ⟨(angle_pos s t hs ht hgap).le,hxU⟩
    rw [state_cost_quadrant s t hs ht hx]
    have hh := (state_secondary_quadrant s t hs ht hx).mp hm
    have hb := (state_low_chart s hs).2
    have hB := (state_low_chart t ht).2
    cases hk : t.positive with
    | false => rw [hk] at hh ⊢; exact secondary_negative s.positive hb hB hx hh
    | true => rw [hk] at hh ⊢; exact secondary_positive s.positive hb hB hx hh
  · exact beyond_quadrant s t hs ht (le_of_not_ge hxU)

theorem source_primary (s t : FramePair.State) (hs : s.branch=.low) (ht : t.branch=.low)
    {x : ℝ} (hgap : (19/25:ℝ)≤s.gap t x) (hm : s.Feasible t 3 x) :
    (91/100:ℝ)<s.cost t x := by
  by_cases hxU : x≤Real.pi/2
  · have hx : x∈Icc 0 (Real.pi/2) := ⟨(angle_pos s t hs ht hgap).le,hxU⟩
    rw [state_cost_quadrant s t hs ht hx]
    have hh := (state_primary_quadrant s t hs ht hx).mp hm
    have hb := (state_low_chart s hs).2
    have hB := (state_low_chart t ht).2
    cases hk : t.positive with
    | false => rw [hk] at hh ⊢; exact primary_negative s.positive hb hB hx hh
    | true => rw [hk] at hh ⊢; exact primary_positive s.positive hb hB hx hh
  · exact beyond_quadrant s t hs ht (le_of_not_ge hxU)

/-- The complete low/low theorem: no sign, endpoint, tie or feasible
forward axis is removed from the original state. -/
theorem low_pair (s t : FramePair.State) (hs : s.branch=.low) (ht : t.branch=.low)
    (j : Fin 4) {x : ℝ} (hgap : (19/25:ℝ)≤s.gap t x) (hm : s.Feasible t j x) :
    handGamma s.branch.type t.branch.type<s.cost t x := by
  have hnum : handGamma s.branch.type t.branch.type=(91/100:ℝ) := by
    norm_num [hs,ht,Branch.type,handGamma,handGammaNumerator]
  rw [hnum]
  fin_cases j
  · exact source_secondary s t hs ht hgap hm
  · have hh := source_primary t.flip s.flip
      (by simpa [State.flip] using ht) (by simpa [State.flip] using hs)
      (by simpa using hgap) ((s.target_primary_reverse t x).mp hm)
    simpa using hh
  · have hh := source_secondary t.flip s.flip
      (by simpa [State.flip] using ht) (by simpa [State.flip] using hs)
      (by simpa using hgap) ((s.target_secondary_reverse t x).mp hm)
    simpa using hh
  · exact source_primary s t hs ht hgap hm

/-- Every original weak forward witness on a physical low/low edge
inherits the strict continuous bound before any frame concentration. -/
theorem low_cycle_pair (C : BoundaryCycle Q0) (i : Vertex)
    (hi : branchOf C i=.low) (hj : branchOf C (next i)=.low)
    (j : Fin 4) (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    handGamma (branchOf C i).type (branchOf C (next i)).type<
      (stateOf C i).cost (stateOf C (next i)) (pairAngle C i) := by
  exact low_pair (stateOf C i) (stateOf C (next i)) hi hj j
    (stateOf_gap_bounds C i).1.le (stateOf_feasible C i j haxis)

end SquaresInCircles.Eight.TableFree.FrameLowPair
