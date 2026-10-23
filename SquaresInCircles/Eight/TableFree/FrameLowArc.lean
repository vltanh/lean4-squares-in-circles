module

public import SquaresInCircles.Eight.TableFree.FrameCircleArc

/-!
# The complete low outer arc and its frame marker

Uncompiled source draft.  The endpoints are exact positive roots of the
outer-circle equation.  Every low state lies on this one closed arc.
The marker bounds and all source-loss bounds follow from monotonicity
or endpoint concavity on the full arc.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameLowArc
open FramePair FrameCircleArc

def u : ℝ := 3231/8000
def v : ℝ := 217813/200000
def a1 : ℝ := (Real.sqrt (272*Q0-36)-10)/17
def b1 : ℝ := a1/4
def L (b : ℝ) : ℝ := u*(A b-a0)+v*b
def L1 : ℝ := u*(a1-a0)+v*b1
def slope (b : ℝ) : ℝ := (b+1/2)/(A b+1/2)
def Ld (b : ℝ) : ℝ := v-u*slope b

theorem a0_bounds : (141457/100000:ℝ)<a0 ∧ a0<70729/50000 := by
  have hs := Real.sq_sqrt (show 0≤Q0-1/4 by norm_num [Q0])
  have hn := Real.sqrt_nonneg (Q0-1/4)
  dsimp [a0,Q0] at *
  constructor <;> nlinarith

theorem a1_bounds : (64937/50000:ℝ)<a1 ∧ a1<1039/800 := by
  have hs := Real.sq_sqrt (show 0≤272*Q0-36 by norm_num [Q0])
  have hn := Real.sqrt_nonneg (272*Q0-36)
  dsimp [a1,Q0] at *
  constructor <;> nlinarith

theorem b1_bounds : (64937/200000:ℝ)<b1 ∧ b1<1039/3200 := by
  dsimp [b1]
  constructor <;> linarith [a1_bounds.1,a1_bounds.2]

theorem endpoint_circle : (a1+1/2)^2+(b1+1/2)^2=Q0 := by
  have hs := Real.sq_sqrt (show 0≤272*Q0-36 by norm_num [Q0])
  have he : Real.sqrt (272*Q0-36)=17*a1+10 := by dsimp [a1]; ring
  rw [he] at hs
  dsimp [b1]
  nlinarith only [hs]

theorem b1_mem : b1∈Icc 0 c0 :=
  ⟨by linarith [b1_bounds.1],by linarith [b1_bounds.2,c0_bounds.1]⟩

theorem A_b1 : A b1=a1 := by
  dsimp [A]
  rw [show Q0-(b1+1/2)^2=(a1+1/2)^2 by linarith [endpoint_circle],
    Real.sqrt_sq (by linarith [a1_bounds.1])]
  ring

theorem A_low_bounds {b : ℝ} (hb : b∈Icc 0 b1) : a1≤A b ∧ A b≤a0 := by
  have hb' : b∈Icc 0 c0 := ⟨hb.1,hb.2.trans b1_mem.2⟩
  have hh := A_antitone hb' b1_mem hb.2
  rw [A_b1] at hh
  exact ⟨hh,(A_bounds hb').2⟩

theorem L1_bounds : (30681/100000:ℝ)<L1 ∧ L1<30683/100000 := by
  have ha0 := a0_bounds
  have ha1 := a1_bounds
  have hb1 := b1_bounds
  dsimp [L1,u,v]
  constructor <;> linarith

@[simp] theorem L_zero : L 0=0 := by simp [L,A_zero]
@[simp] theorem L_b1 : L b1=L1 := by simp [L,L1,A_b1]

theorem slope_bounds {b : ℝ} (hb : b∈Icc 0 b1) :
    (13/50:ℝ)<slope b ∧ slope b<23/50 := by
  have ha := A_low_bounds hb
  have hden := A_shift_pos (show b∈Icc 0 c0 from ⟨hb.1,hb.2.trans b1_mem.2⟩)
  dsimp [slope]
  constructor
  · apply (lt_div_iff₀ hden).2
    linarith [hb.1,ha.2,a0_bounds.2]
  · apply (div_lt_iff₀ hden).2
    linarith [hb.2,ha.1,a1_bounds.1,b1_bounds.2]

theorem L_hasDerivAt {b : ℝ} (hb : b∈Icc 0 b1) : HasDerivAt L (Ld b) b := by
  have hh := (((A_hasDerivAt ⟨hb.1,hb.2.trans b1_mem.2⟩).sub_const a0).const_mul u).add
    ((hasDerivAt_id b).const_mul v)
  convert hh using 1
  · rfl
  · dsimp [Ld,Ad,slope]
    ring

theorem Ld_bounds {b : ℝ} (hb : b∈Icc 0 b1) : 0<Ld b ∧ Ld b<1 := by
  have hh := slope_bounds hb
  dsimp [Ld,u,v]
  constructor <;> linarith

theorem L_monotone : MonotoneOn L (Icc 0 b1) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun b hb => (L_hasDerivAt hb).continuousAt.continuousWithinAt
  · exact fun b hb => L_hasDerivAt (Ioo_subset_Icc_self hb)
  · exact fun b hb => (Ld_bounds (Ioo_subset_Icc_self hb)).1.le

theorem loss_monotone : MonotoneOn (fun b => b-L b) (Icc 0 b1) := by
  apply monoOn_of_hasDeriv_nonneg
  · intro b hb
    exact ((hasDerivAt_id b).sub (L_hasDerivAt hb)).continuousAt.continuousWithinAt
  · intro b hb
    exact (hasDerivAt_id b).sub (L_hasDerivAt (Ioo_subset_Icc_self hb))
  · intro b hb
    linarith [(Ld_bounds (Ioo_subset_Icc_self hb)).2]

theorem L_bounds {b : ℝ} (hb : b∈Icc 0 b1) : 0≤L b ∧ L b≤b ∧ L b≤L1 := by
  have hb0 : (0:ℝ)∈Icc 0 b1 := ⟨le_rfl,b1_mem.1⟩
  have hb1 : b1∈Icc 0 b1 := ⟨b1_mem.1,le_rfl⟩
  have hlo := L_monotone hb0 hb hb.1
  have hhi := L_monotone hb hb1 hb.2
  have hloss := loss_monotone hb0 hb hb.1
  simp only [L_zero,L_b1,sub_zero] at hlo hhi hloss
  exact ⟨hlo,by linarith,hhi⟩

theorem label_loss_lower {b lambda epsilon : ℝ} (hb : b∈Icc 0 b1)
    (he : 0≤epsilon) (hend : -epsilon≤L1-lambda*b1) :
    -epsilon≤L b-lambda*b := by
  have hh := linear_endpoint_lower (p := u) (q := v-lambda)
    (by norm_num [u]) (by norm_num : (0:ℝ)≤0) b1_mem.2 hb
  have hzero : u*a0-epsilon≤linear u (v-lambda) 0 := by
    simp only [linear,A_zero,mul_zero,add_zero]
    linarith
  have hlast : u*a0-epsilon≤linear u (v-lambda) b1 := by
    dsimp [linear]
    rw [A_b1]
    dsimp [L1] at hend
    nlinarith
  have hlo := (le_min hzero hlast).trans hh
  dsimp [linear,L] at *
  nlinarith

theorem state_low_chart (s : FramePair.State) (hs : s.branch=.low) :
    s.a=A s.b ∧ s.b∈Icc 0 b1 := by
  have hn : s.branch.type≠0 := by simp [hs,Branch.type]
  have hh := state_outer_chart s hn
  have hc := s.outer_eq hn
  have hb := s.b_nonneg
  have hcut : 4*s.b≤s.a := by simpa [hs,TypeMem] using s.type_mem
  have hsq := pow_le_pow_left₀ (show 0≤4*s.b+1/2 by linarith)
    (show 4*s.b+1/2≤s.a+1/2 by linarith) 2
  have hlast := endpoint_circle
  have ha1 : a1=4*b1 := by dsimp [b1]; ring
  rw [ha1] at hlast
  have hbU : s.b≤b1 := by
    by_contra! hbad
    have hprod := mul_pos (by linarith : 0<s.b-b1)
      (by linarith [b1_mem.1] : 0<s.b+b1)
    nlinarith
  exact ⟨hh.1,⟨hb,hbU⟩⟩

theorem state_low_label (s : FramePair.State) (hs : s.branch=.low) :
    s.signedLabel=sign s.positive*L s.b := by
  rw [State.signedLabel,hs]
  simp only [label]
  rw [(state_low_chart s hs).1]
  rfl

theorem low_offset_bounds (s : FramePair.State) (hs : s.branch=.low) :
    -(1/4:ℝ)<s.offset ∧ s.offset<1/4 := by
  have hcut : 4*s.b≤s.a := by simpa [hs,TypeMem] using s.type_mem
  have hr : 0≤s.b/s.a ∧ s.b/s.a≤1/4 :=
    ⟨div_nonneg s.b_nonneg s.a_pos.le,(div_le_iff₀ s.a_pos).2 (by linarith)⟩
  have hangle0 : 0≤Real.arctan (s.b/s.a) := by
    simpa using Real.arctan_le_arctan hr.1
  have hangle : Real.arctan (s.b/s.a)<1/4 := by
    exact (Real.arctan_le_arctan hr.2).trans
      (Real.arctan_lt_self (by norm_num : (0:ℝ)<1/4))
  rcases sign_cases s.positive with he | he <;>
    simp only [State.offset,he,one_mul,neg_one_mul] <;> constructor <;> linarith

end SquaresInCircles.Eight.TableFree.FrameLowArc
