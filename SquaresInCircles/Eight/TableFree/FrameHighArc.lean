module

public import SquaresInCircles.Eight.TableFree.FrameCoreArc

/-!
# The original high arc and its exact frame marker

The whole high circle arc is parameterized by its original transverse
coordinate.  The diagonal and the common middle/high cut are retained.
All marker and derivative bounds follow from those exact endpoints.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameHighArc
open FramePair FrameCircleArc
open FrameLowArc (slope)
open FrameMidArc (a2 b2 A_b2 upper_circle b2_mem a2_bounds b2_bounds)

def u : ℝ := 8898/15625
def v : ℝ := 195443/500000
def k : ℝ := Real.pi/4+(u-v)*c0
def H (b : ℝ) : ℝ := k-u*A b+v*b
def H2 : ℝ := k-u*a2+v*b2
def Hd (b : ℝ) : ℝ := u*slope b+v
def kUpper : ℝ := 355/452+(u-v)*(179843/200000)
def radiusUpper : ℝ := 494697/250000

theorem radius_bound : R<radiusUpper := by
  have hh := R_sq
  have hp := R_pos
  norm_num [Q0,radiusUpper] at hh ⊢
  nlinarith

theorem diagonal_bounds : (449607/500000:ℝ)<c0 ∧ c0<179843/200000 := by
  have hc := c0_circle
  have hp := c0_bounds.1
  norm_num [Q0] at hc
  constructor <;> by_contra! hbad <;> nlinarith

theorem k_bounds : (189/200:ℝ)<k ∧ k<473/500 ∧ k<kUpper := by
  have hd := diagonal_bounds
  have hp := Arithmetic.pi_hand_enclosure
  have hup : Real.pi<(355/113:ℝ) := by linarith
  dsimp [k,kUpper,u,v]
  repeat' constructor <;> linarith

theorem A_high_bounds {b : ℝ} (hb : b∈Icc b2 c0) : c0≤A b ∧ A b≤a2 := by
  have hl := A_antitone ⟨b2_mem.1.trans hb.1,hb.2⟩
    ⟨b2_mem.1.trans b2_mem.2,le_rfl⟩ hb.2
  have hu := A_antitone b2_mem ⟨b2_mem.1.trans hb.1,hb.2⟩ hb.1
  rw [A_c0] at hl
  rw [A_b2] at hu
  exact ⟨hl,hu⟩

theorem high_bounds {b : ℝ} (hb : b∈Icc b2 c0) :
    (5139/10000:ℝ)<b ∧ b<(9/10:ℝ) ∧
      (449607/500000:ℝ)<A b ∧ A b<(6/5:ℝ) := by
  have ha := A_high_bounds hb
  exact ⟨by linarith [hb.1,b2_bounds.1],by linarith [hb.2,diagonal_bounds.2],
    by linarith [ha.1,diagonal_bounds.1],by linarith [ha.2,a2_bounds.2]⟩

theorem slope_high_bounds {b : ℝ} (hb : b∈Icc b2 c0) :
    (149/250:ℝ)<slope b ∧ slope b≤1 := by
  have ha := A_high_bounds hb
  have hn := high_bounds hb
  have hp := A_shift_pos ⟨b2_mem.1.trans hb.1,hb.2⟩
  dsimp [slope]
  constructor
  · apply (lt_div_iff₀ hp).2
    linarith [hn.1,hn.2.2.2]
  · apply (div_le_iff₀ hp).2
    linarith [hb.2,ha.1]

@[simp] theorem H_b2 : H b2=H2 := by simp [H,H2,A_b2]
@[simp] theorem H_c0 : H c0=Real.pi/4 := by
  rw [H,A_c0]
  dsimp [k]
  ring

theorem H2_bounds : (4639/10000:ℝ)<H2 ∧ H2<(58/125:ℝ) := by
  have hd := diagonal_bounds
  have ha := a2_bounds
  have hp := Arithmetic.pi_hand_enclosure
  dsimp [H2,k,u,v,FrameMidArc.b2]
  constructor <;> linarith

theorem H_deriv {b : ℝ} (hb : b∈Icc b2 c0) : HasDerivAt H (Hd b) b := by
  have hh := (((A_hasDerivAt ⟨b2_mem.1.trans hb.1,hb.2⟩).const_mul (-u)).const_add k).
    add ((hasDerivAt_id b).const_mul v)
  convert hh using 1 <;> dsimp [H,Hd,slope,Ad] <;> ring

theorem Hd_bounds {b : ℝ} (hb : b∈Icc b2 c0) : 0<Hd b ∧ Hd b≤u+v := by
  have hr := slope_high_bounds hb
  have hu := mul_le_mul_of_nonneg_left hr.2 (show 0≤u by norm_num [u])
  dsimp [Hd,u,v] at *
  constructor <;> linarith

theorem H_monotone : MonotoneOn H (Icc b2 c0) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun b hb => (H_deriv hb).continuousAt.continuousWithinAt
  · exact fun b hb => H_deriv (Ioo_subset_Icc_self hb)
  · exact fun b hb => (Hd_bounds (Ioo_subset_Icc_self hb)).1.le

theorem H_bounds {b : ℝ} (hb : b∈Icc b2 c0) : H2≤H b ∧ H b≤Real.pi/4 := by
  have hl := H_monotone ⟨le_rfl,b2_mem.2⟩ hb hb.1
  have hu := H_monotone hb ⟨b2_mem.2,le_rfl⟩ hb.2
  simpa only [H_b2,H_c0] using And.intro hl hu

theorem loss_antitone {lambda : ℝ} (hλ : u+v≤lambda) :
    AntitoneOn (fun b => H b-lambda*b) (Icc b2 c0) := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun b hb => ((H_deriv hb).sub ((hasDerivAt_id b).const_mul lambda)).
      continuousAt.continuousWithinAt
  · exact fun b hb => (H_deriv (Ioo_subset_Icc_self hb)).sub
      ((hasDerivAt_id b).const_mul lambda)
  · intro b hb
    linarith [(Hd_bounds (Ioo_subset_Icc_self hb)).2]

theorem high_norm_sq {b : ℝ} (hb : b∈Icc b2 c0) :
    (1:ℝ)<(A b)^2+b^2 ∧ (A b)^2+b^2<(4/3:ℝ)^2 := by
  have ha := A_high_bounds hb
  have hc := A_circle ⟨b2_mem.1.trans hb.1,hb.2⟩
  have hmin := linear_endpoint_lower (p := (1:ℝ)) (q := (1:ℝ))
    (by norm_num) b2_mem.1 le_rfl hb
  simp only [linear,A_b2,A_c0,one_mul] at hmin
  have hend : a2+b2≤c0+c0 := by
    dsimp [FrameMidArc.b2]
    linarith [a2_bounds.2,diagonal_bounds.1]
  rw [min_eq_left hend] at hmin
  have hsum : A b+b≤2*c0 := by
    have hc0 := c0_circle
    have hp := high_bounds hb
    nlinarith [sq_nonneg (A b-b)]
  have hd := diagonal_bounds
  have he := a2_bounds
  dsimp [FrameMidArc.b2] at hmin
  norm_num [Q0] at hc
  constructor <;> nlinarith

theorem signed_label_bounds (i : Bool) {b : ℝ} (hb : b∈Icc b2 c0) :
    -(Real.pi/4)≤sign i*H b ∧ sign i*H b≤Real.pi/4 := by
  have hh := H_bounds hb
  have hp : 0≤H b := by linarith [H2_bounds.1]
  cases i <;> norm_num [sign] <;> constructor <;> linarith

theorem minus_label_le (i : Bool) {b : ℝ} (hb : b∈Icc b2 c0) : -H b≤sign i*H b := by
  have hp : 0≤H b := by linarith [(H_bounds hb).1,H2_bounds.1]
  cases i <;> norm_num [sign] <;> linarith

theorem state_high_chart (s : FramePair.State) (hs : s.branch=.high) :
    s.a=A s.b ∧ s.b∈Icc b2 c0 := by
  have hn : s.branch.type≠0 := by simp [hs,Branch.type]
  have hh := state_outer_chart s hn
  have hc := s.outer_eq hn
  have ht : 3*s.a≤7*s.b := by simpa [hs,TypeMem] using s.type_mem
  have he : a2=(7/3)*b2 := by dsimp [FrameMidArc.b2]; ring
  have hec := upper_circle
  rw [he] at hec
  have hsq := pow_le_pow_left₀ (show 0≤s.a+1/2 by linarith [s.a_pos])
    (show s.a+1/2≤(7/3)*s.b+1/2 by linarith) 2
  have hlo : b2≤s.b := by
    by_contra! hbad
    have hp := mul_pos (sub_pos.mpr hbad)
      (show 0<b2+s.b by linarith [b2_bounds.1,s.b_nonneg])
    nlinarith
  exact ⟨hh.1,⟨hlo,hh.2.2⟩⟩

theorem state_high_label (s : FramePair.State) (hs : s.branch=.high) :
    s.signedLabel=sign s.positive*H s.b := by
  rw [State.signedLabel,hs]
  simp only [label]
  rw [(state_high_chart s hs).1]
  dsimp [H,k,u,v]
  ring

end SquaresInCircles.Eight.TableFree.FrameHighArc
