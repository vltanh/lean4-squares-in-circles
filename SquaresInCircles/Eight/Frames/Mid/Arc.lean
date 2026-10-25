module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Frames.Low.Arc

/-!
# Eight squares: the complete middle outer arc and its exact frame marker

The two endpoints are the actual intersections with `a = 4b` and
`3a = 7b`.  Every middle state lies on the closed arc between them.
Marker bounds, derivatives, coordinate supports and the center-radius
bound are derived from that circle, before any frame concentration.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameMidArc
open FramePair FrameCircleArc FrameLowArc

def p : ℝ := 1489593/1000000
def q : ℝ := 1580219/1000000
def cM : ℝ := -85723/40000
def g : ℝ := 269343/250000
def K : ℝ := 7506931/1000000
def a2 : ℝ := (Real.sqrt (11368*Q0-784)-70)/116
def b2 : ℝ := (3/7)*a2
def M (b : ℝ) : ℝ := cM+p*A b+q*b
def M1 : ℝ := cM+p*a1+q*b1
def M2 : ℝ := cM+p*a2+q*b2
def Md (b : ℝ) : ℝ := q-p*slope b

theorem a1_precise :
    (1298747247/1000000000:ℝ)<a1 ∧ a1<1298747249/1000000000 := by
  have hs := Real.sq_sqrt (show 0≤272*Q0-36 by norm_num [Q0])
  have hn := Real.sqrt_nonneg (272*Q0-36)
  dsimp [a1,Q0] at *
  constructor <;> nlinarith

theorem a2_bounds :
    (59962803/50000000:ℝ)<a2 ∧ a2<599628031/500000000 := by
  have hs := Real.sq_sqrt (show 0≤11368*Q0-784 by norm_num [Q0])
  have hn := Real.sqrt_nonneg (11368*Q0-784)
  dsimp [a2,Q0] at *
  constructor <;> nlinarith

theorem b2_bounds : (5139/10000:ℝ)<b2 ∧ b2<257/500 := by
  dsimp [b2]
  constructor <;> linarith [a2_bounds.1,a2_bounds.2]

theorem upper_circle : (a2+1/2)^2+(b2+1/2)^2=Q0 := by
  have hs := Real.sq_sqrt (show 0≤11368*Q0-784 by norm_num [Q0])
  have he : Real.sqrt (11368*Q0-784)=116*a2+70 := by dsimp [a2]; ring
  rw [he] at hs
  dsimp [b2]
  nlinarith only [hs]

theorem b1_lt_b2 : b1<b2 := by linarith [b1_bounds.2,b2_bounds.1]
theorem b2_mem : b2∈Icc 0 c0 :=
  ⟨by linarith [b2_bounds.1],by linarith [b2_bounds.2,c0_bounds.1]⟩

theorem A_b2 : A b2=a2 := by
  dsimp [A]
  rw [show Q0-(b2+1/2)^2=(a2+1/2)^2 by linarith [upper_circle],
    Real.sqrt_sq (by linarith [a2_bounds.1])]
  ring

theorem A_mid_bounds {b : ℝ} (hb : b∈Icc b1 b2) : a2≤A b ∧ A b≤a1 := by
  have hb' : b∈Icc 0 c0 := ⟨b1_mem.1.trans hb.1,hb.2.trans b2_mem.2⟩
  have hlo := A_antitone hb' b2_mem hb.2
  have hhi := A_antitone b1_mem hb' hb.1
  simpa only [A_b1,A_b2] using And.intro hlo hhi

theorem slope_mid_bounds {b : ℝ} (hb : b∈Icc b1 b2) :
    (229/500:ℝ)<slope b ∧ slope b<597/1000 := by
  have ha := A_mid_bounds hb
  have hden := A_shift_pos ⟨b1_mem.1.trans hb.1,hb.2.trans b2_mem.2⟩
  unfold FrameLowArc.slope
  constructor
  · apply (lt_div_iff₀ hden).2
    linarith [hb.1,b1_bounds.1,ha.2,a1_precise.2]
  · apply (div_lt_iff₀ hden).2
    linarith [hb.2,b2_bounds.2,ha.1,a2_bounds.1]

theorem M_endpoints :
    (1523/5000:ℝ)<M1 ∧ M1<30461/100000 ∧
      (911/2000:ℝ)<M2 ∧ M2<455511/1000000 := by
  have ha1 := a1_precise
  have ha2 := a2_bounds
  dsimp [M1,M2,b1,b2,p,q,cM]
  refine ⟨?_,?_,?_,?_⟩ <;> linarith

@[simp] theorem M_b1 : M b1=M1 := by simp [M,M1,A_b1]
@[simp] theorem M_b2 : M b2=M2 := by simp [M,M2,A_b2]

theorem M_deriv {b : ℝ} (hb : b∈Icc b1 b2) : HasDerivAt M (Md b) b := by
  have hd := (((A_hasDerivAt ⟨b1_mem.1.trans hb.1,hb.2.trans b2_mem.2⟩).const_mul p).const_add
    cM).fun_add ((hasDerivAt_id' b).const_mul q)
  unfold M
  convert hd using 1
  simp only [Md,Ad,FrameLowArc.slope]
  ring

theorem Md_bounds {b : ℝ} (hb : b∈Icc b1 b2) : 0<Md b ∧ Md b<449/500 := by
  have hh := slope_mid_bounds hb
  dsimp [Md,p,q]
  constructor <;> linarith

theorem M_monotone : MonotoneOn M (Icc b1 b2) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun b hb => (M_deriv hb).continuousAt.continuousWithinAt
  · exact fun b hb => M_deriv (Ioo_subset_Icc_self hb)
  · exact fun b hb => (Md_bounds (Ioo_subset_Icc_self hb)).1.le

theorem M_bounds {b : ℝ} (hb : b∈Icc b1 b2) : M1≤M b ∧ M b≤M2 := by
  have hlo := M_monotone ⟨le_rfl,b1_lt_b2.le⟩ hb hb.1
  have hhi := M_monotone hb ⟨b1_lt_b2.le,le_rfl⟩ hb.2
  simpa only [M_b1,M_b2] using And.intro hlo hhi

theorem loss_antitone {lam : ℝ} (hlam : (449/500:ℝ)≤lam) :
    AntitoneOn (fun b => M b-lam*b) (Icc b1 b2) := by
  apply antiOn_of_hasDeriv_nonpos
  · intro b hb
    exact ((M_deriv hb).sub ((hasDerivAt_id b).const_mul lam)).continuousAt.continuousWithinAt
  · intro b hb
    exact (M_deriv (Ioo_subset_Icc_self hb)).sub ((hasDerivAt_id b).const_mul lam)
  · intro b hb
    linarith [(Md_bounds (Ioo_subset_Icc_self hb)).2]

theorem state_mid_chart (s : FramePair.State) (hs : s.branch=.middle) :
    s.a=A s.b ∧ s.b∈Icc b1 b2 := by
  have hn : s.branch.type≠0 := by simp [hs,Branch.type]
  have hh := state_outer_chart s hn
  have hc := s.outer_eq hn
  have ht : s.a≤4*s.b ∧ 7*s.b≤3*s.a := by simpa [hs,TypeMem] using s.type_mem
  have he1 : a1=4*b1 := by dsimp [b1]; ring
  have he2 : a2=(7/3)*b2 := by dsimp [b2]; ring
  have h1 := endpoint_circle
  have h2 := upper_circle
  rw [he1] at h1
  rw [he2] at h2
  have hsq1 := pow_le_pow_left₀ (show 0≤ s.a+1/2 by linarith [s.a_pos])
    (show s.a+1/2≤4*s.b+1/2 by linarith [ht.1]) 2
  have hsq2 := pow_le_pow_left₀ (show 0≤(7/3)*s.b+1/2 by linarith [s.b_nonneg])
    (show (7/3)*s.b+1/2≤ s.a+1/2 by linarith [ht.2]) 2
  have hlo : b1≤ s.b := by
    by_contra! hbad
    have hp := mul_pos (sub_pos.mpr hbad)
      (show 0<b1+s.b by linarith [b1_bounds.1,s.b_nonneg])
    nlinarith
  have hhi : s.b≤b2 := by
    by_contra! hbad
    have hp := mul_pos (sub_pos.mpr hbad)
      (show 0<s.b+b2 by linarith [b2_bounds.1,s.b_nonneg])
    nlinarith
  exact ⟨hh.1,⟨hlo,hhi⟩⟩

theorem state_mid_label (s : FramePair.State) (hs : s.branch=.middle) :
    s.signedLabel=sign s.positive*M s.b := by
  rw [State.signedLabel,hs]
  simp only [label]
  rw [(state_mid_chart s hs).1]
  rfl

theorem middle_offset_bounds (s : FramePair.State) (hs : s.branch=.middle) :
    -(81/200:ℝ)<s.offset ∧ s.offset<81/200 := by
  have htm : s.a≤4*s.b ∧ 7*s.b≤3*s.a := by simpa [hs,TypeMem] using s.type_mem
  have ht := htm.2
  have hr : s.b/s.a≤3/7 := (div_le_iff₀ s.a_pos).2 (by linarith)
  have h0 : 0≤Real.arctan (s.b/s.a) :=
    Real.arctan_nonneg.2 (div_nonneg s.b_nonneg s.a_pos.le)
  have hupper := Arithmetic.arctan_le_atanUpper (show (0:ℝ)≤3/7 by norm_num)
  have hnum : Arithmetic.atanUpper (3/7:ℝ)<81/200 := by norm_num [Arithmetic.atanUpper]
  have hangle : Real.arctan (s.b/s.a)<81/200 :=
    (Real.arctan_mono hr).trans_lt (hupper.trans_lt hnum)
  rcases sign_cases s.positive with he | he <;>
    simp only [State.offset,he,one_mul,neg_one_mul] <;> constructor <;> linarith

/-- The norm decreases along the canonical outer arc, so the middle
source is controlled by its lower intrinsic endpoint. -/
theorem middle_norm_sq {b : ℝ} (hb : b∈Icc b1 b2) :
    (A b)^2+b^2<(67/50:ℝ)^2 := by
  have ha := A_mid_bounds hb
  have hc := A_circle ⟨b1_mem.1.trans hb.1,hb.2.trans b2_mem.2⟩
  have hconc := linear_endpoint_lower (p := (1:ℝ)) (q := (1:ℝ))
    (by norm_num) b1_mem.1 b2_mem.2 hb
  simp only [linear,A_b1,A_b2,one_mul] at hconc
  have hsum : a1+b1≤A b+b := by
    have hh : a1+b1≤a2+b2 := by
      dsimp [b1,b2]
      linarith [a1_precise.2,a2_bounds.1]
    simpa only [min_eq_left hh] using hconc
  have hbase : a1^2+b1^2<(67/50:ℝ)^2 := by
    have ha0 : 0≤a1 := by linarith [a1_precise.1]
    have hsq := pow_le_pow_left₀ ha0 a1_precise.2.le 2
    dsimp [b1]
    nlinarith
  nlinarith [endpoint_circle]

end SquaresInCircles.Eight.FrameMidArc
