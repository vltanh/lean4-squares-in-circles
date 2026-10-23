module

public import SquaresInCircles.Eight.TableFree.FrameDiagonalArc

/-!
# The unchanged frame potentials in diagonal coordinates

Both folded markers are exact complements of the original markers.
The identities include the intrinsic endpoints; they do not choose a
new side of a tie.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameDiagonalLabels
open FramePair FrameDiagonalArc

def u : ℝ := 89293/1000000
def v : ℝ := 480179/1000000
def k : ℝ := 767453/500000
def q : ℝ := 45313/1000000
def cM : ℝ := Real.pi/4+85723/40000
def H (b : ℝ) : ℝ := u*(A b-a0)+v*b
def M (b : ℝ) : ℝ := cM-k*A b+q*b
def H1 : ℝ := H b1
def M1 : ℝ := M b1
def M2 : ℝ := M b2
def Hd (b : ℝ) : ℝ := v-u*slope b
def Md (b : ℝ) : ℝ := k*slope b+q

/-- `true` denotes the folded middle arc; `false` the folded high arc. -/
def arc (middle : Bool) : Set ℝ := if middle then Icc b1 b2 else Icc 0 b1
def marker (middle : Bool) (b : ℝ) : ℝ := if middle then M b else H b
def constant (middle : Bool) : ℝ := if middle then cM else -u*a0
def primary (middle : Bool) : ℝ := if middle then -k else u
def transverse (middle : Bool) : ℝ := if middle then q else v

theorem marker_affine (middle : Bool) (b : ℝ) :
    marker middle b=constant middle+primary middle*A b+transverse middle*b := by
  cases middle <;> dsimp [marker,constant,primary,transverse,H,M] <;> ring

theorem arc_subset {middle : Bool} {b : ℝ} (hb : b∈arc middle) : b∈Icc 0 b2 := by
  cases middle
  · exact high_subset hb
  · exact mid_subset hb

theorem H_deriv {b : ℝ} (hb : b∈Icc 0 b1) : HasDerivAt H (Hd b) b := by
  have hd := (((A_hasDerivAt (high_subset hb)).sub_const a0).const_mul u).
    add ((hasDerivAt_id b).const_mul v)
  convert hd using 1 <;> dsimp [H,Hd,Ad,slope] <;> ring

theorem Hd_deriv {b : ℝ} (hb : b∈Icc 0 b1) :
    HasDerivAt Hd (-u*slopeD b) b := by
  convert ((slope_hasDerivAt (high_subset hb)).const_mul (-u)).const_add v using 1 <;>
    dsimp [Hd] <;> ring

theorem M_deriv {b : ℝ} (hb : b∈Icc b1 b2) : HasDerivAt M (Md b) b := by
  have hd := (((A_hasDerivAt (mid_subset hb)).const_mul (-k)).const_add cM).
    add ((hasDerivAt_id b).const_mul q)
  convert hd using 1 <;> dsimp [M,Md,Ad,slope] <;> ring

theorem Md_deriv {b : ℝ} (hb : b∈Icc b1 b2) :
    HasDerivAt Md (k*slopeD b) b := by
  simpa [Md] using ((slope_hasDerivAt (mid_subset hb)).const_mul k).add_const q

theorem Hd_positive {b : ℝ} (hb : b∈Icc 0 b1) : 0<Hd b := by
  have hr := slope_high_bounds hb
  dsimp [Hd,u,v]
  linarith

theorem Md_positive {b : ℝ} (hb : b∈Icc b1 b2) : 0<Md b := by
  have hr := slope_mid_bounds hb
  dsimp [Md,k,q]
  linarith

theorem H_monotone : MonotoneOn H (Icc 0 b1) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun b hb => (H_deriv hb).continuousAt.continuousWithinAt
  · exact fun b hb => H_deriv (Ioo_subset_Icc_self hb)
  · exact fun b hb => (Hd_positive (Ioo_subset_Icc_self hb)).le

theorem M_monotone : MonotoneOn M (Icc b1 b2) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun b hb => (M_deriv hb).continuousAt.continuousWithinAt
  · exact fun b hb => M_deriv (Ioo_subset_Icc_self hb)
  · exact fun b hb => (Md_positive (Ioo_subset_Icc_self hb)).le

@[simp] theorem H_zero : H 0=0 := by simp [H]

theorem H1_bounds : (0:ℝ)<H1 ∧ H1<160727/500000 := by
  have ha := a1_precise
  have h0 := a0_precise
  dsimp [H1,H]
  rw [A_b1,b1_eq]
  dsimp [u,v]
  constructor <;> linarith

theorem M_endpoints :
    (8247/25000:ℝ)<M1 ∧ M2<601/1250 := by
  have ha1 := a1_precise
  have ha2 := a2_precise
  have hp := Arithmetic.pi_hand_enclosure
  dsimp [M1,M2,M]
  rw [A_b1,A_b2,b1_eq,b2_eq]
  dsimp [cM,k,q]
  constructor <;> linarith

theorem H_bounds {b : ℝ} (hb : b∈Icc 0 b1) :
    0≤H b ∧ H b<(160727/500000:ℝ) := by
  have h0 := H_monotone ⟨le_rfl,by linarith [b1_bounds.1]⟩ hb hb.1
  have h1 := H_monotone hb ⟨by linarith [b1_bounds.1],le_rfl⟩ hb.2
  rw [H_zero] at h0
  exact ⟨h0,h1.trans_lt H1_bounds.2⟩

theorem M_bounds {b : ℝ} (hb : b∈Icc b1 b2) :
    (8247/25000:ℝ)<M b ∧ M b<(601/1250:ℝ) := by
  have h1 := M_monotone ⟨le_rfl,b1_lt_b2.le⟩ hb hb.1
  have h2 := M_monotone hb ⟨b1_lt_b2.le,le_rfl⟩ hb.2
  exact ⟨M_endpoints.1.trans_le h1,h2.trans_lt M_endpoints.2⟩

theorem H_concave : ConcaveOn ℝ (Icc 0 b1) H := by
  apply concave_of_deriv2 (fun b hb => H_deriv hb) (fun b hb => Hd_deriv hb)
  intro b hb
  have hp : 0<slopeD b := by
    exact div_pos (by norm_num [Q0]) (pow_pos (A_shift_pos (high_subset hb)) 3)
  exact (mul_neg_of_neg_of_pos (by norm_num [u]) hp).le

theorem M_convex : ConvexOn ℝ (Icc b1 b2) M := by
  have hn : ConcaveOn ℝ (Icc b1 b2) (fun b => -M b) := by
    apply concave_of_deriv2
      (f' := fun b => -Md b) (f'' := fun b => -k*slopeD b)
    · exact fun b hb => (M_deriv hb).neg
    · intro b hb
      convert (Md_deriv hb).neg using 1 <;> ring
    · intro b hb
      have hp : 0<slopeD b :=
        div_pos (by norm_num [Q0]) (pow_pos (A_shift_pos (mid_subset hb)) 3)
      exact (mul_neg_of_neg_of_pos (by norm_num [k]) hp).le
  simpa only [neg_neg] using hn.neg

theorem H_fold {b : ℝ} (hb : b∈Icc FrameMidArc.b2 c0) :
    H (foldTrans b)=Real.pi/4-FrameHighArc.H b := by
  rw [H,(old_high_fold hb).2,a0_eq_diagonal]
  dsimp [foldTrans,FrameHighArc.H,FrameHighArc.k,
    FrameHighArc.u,FrameHighArc.v,u,v]
  ring

theorem M_fold {b : ℝ} (hb : b∈Icc FrameLowArc.b1 FrameMidArc.b2) :
    M (foldTrans b)=Real.pi/4-FrameMidArc.M b := by
  rw [M,(old_mid_fold hb).2]
  dsimp [foldTrans,FrameMidArc.M,FrameMidArc.cM,FrameMidArc.p,FrameMidArc.q,cM,k,q]
  ring

theorem state_high_label (s : FramePair.State) (hs : s.branch=.high) :
    sign (!s.positive)*H (s.a-s.b)=s.signedLabel-sign s.positive*(Real.pi/4) := by
  have hc := FrameHighArc.state_high_chart s hs
  have he := H_fold hc.2
  rw [foldTrans,← hc.1] at he
  rw [FrameHighArc.state_high_label s hs,he,sign_not]
  ring

theorem state_mid_label (s : FramePair.State) (hs : s.branch=.middle) :
    sign (!s.positive)*M (s.a-s.b)=s.signedLabel-sign s.positive*(Real.pi/4) := by
  have hc := FrameMidArc.state_mid_chart s hs
  have he := M_fold hc.2
  rw [foldTrans,← hc.1] at he
  rw [FrameMidArc.state_mid_label s hs,he,sign_not]
  ring

end SquaresInCircles.Eight.TableFree.FrameDiagonalLabels
