module

public import SquaresInCircles.Eight.TableFree.SecondOuterJBounds
public import SquaresInCircles.Eight.TableFree.SecondOuterKBounds
public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeTwoInverse

/-!
# The original same-sign zero-quarter contact

Uncompiled source draft.  The source transverse coordinate is solved
directly from its original weak secondary separator.  The contact
increases with the original target coordinate and decreases with the
angle.  Its exact circle speed and projection identities are shared by
the P/J and L/K costs, without any contact-location premise.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.SameZero
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)

def b (B x : ℝ) : ℝ :=
  1/2+(B+1/2)*Real.cos x-(arc B-1/2)*Real.sin x
def v (B x : ℝ) : ℝ :=
  (arc B-1/2)*Real.cos x+(B+1/2)*Real.sin x
def k (B x : ℝ) : ℝ := Real.cos x+ratio B*Real.sin x
def Domain (B x : ℝ) : Prop :=
  B∈Icc 0 outerDiagonal ∧ x∈Icc 0 (7/10) ∧ b B x∈Icc 0 outerDiagonal

def value (F G : RoleLabel) (B x : ℝ) : ℝ := x+F.outer (b B x)-G.outer B
def angleFirst (F : RoleLabel) (B x : ℝ) : ℝ := 1-F.d1 (b B x)*v B x
def targetFirst (F G : RoleLabel) (B x : ℝ) : ℝ := F.d1 (b B x)*k B x-G.d1 B

lemma b_angle_hasDerivAt (B x : ℝ) : HasDerivAt (b B) (-v B x) x :=
  ((((Real.hasDerivAt_cos x).const_mul (B+1/2)).const_add (1/2)).fun_sub
    ((Real.hasDerivAt_sin x).const_mul (arc B-1/2))).congr_deriv (by dsimp [v]; ring)

lemma v_angle_hasDerivAt (B x : ℝ) : HasDerivAt (v B) (b B x-1/2) x :=
  (((Real.hasDerivAt_cos x).const_mul (arc B-1/2)).fun_add
    ((Real.hasDerivAt_sin x).const_mul (B+1/2))).congr_deriv (by dsimp [b]; ring)

lemma b_target_hasDerivAt {B : ℝ} (hB : B∈Icc 0 outerDiagonal) (x : ℝ) :
    HasDerivAt (fun t => b t x) (k B x) B := by
  have hh := ((((hasDerivAt_id' B).add_const (1/2)).mul_const
    (Real.cos x)).const_add (1/2)).fun_sub
      (((ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hB)).sub_const
        (1/2)).mul_const (Real.sin x))
  exact hh.congr_deriv (by dsimp [k]; ring)

lemma v_positive {B x : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) : 0<v B x := by
  have ht := positive_trig hx
  have hU := UW_bounds hB
  have hp := mul_pos (show 0<arc B-1/2 by dsimp [U] at hU; linarith [hU.1])
    (show 0<Real.cos x by linarith [ht.1])
  have hs := mul_nonneg (show 0≤B+1/2 by linarith [hB.1]) ht.2.2.1
  dsimp [v]
  linarith

lemma k_positive {B x : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) : 0<k B x := by
  have ht := positive_trig hx
  have hp := mul_nonneg (ShortOuterOne.SameContact.ratio_pos (outer_domain hB)).le
    ht.2.2.1
  dsimp [k]
  linarith [ht.1]

lemma b_angle_antitone {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    AntitoneOn (b B) (Icc 0 (7/10)) :=
  antiOn_of_hasDeriv_nonpos
    (fun x _ => (b_angle_hasDerivAt B x).continuousAt.continuousWithinAt)
    (fun x _ => b_angle_hasDerivAt B x)
    (fun x hx => neg_nonpos.mpr (v_positive hB (Ioo_subset_Icc_self hx)).le)

lemma b_target_monotone {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    MonotoneOn (fun B => b B x) (Icc 0 outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun B hB => (b_target_hasDerivAt hB x).continuousAt.continuousWithinAt)
    (fun B hB => b_target_hasDerivAt (Ioo_subset_Icc_self hB) x)
    (fun B hB => (k_positive (Ioo_subset_Icc_self hB) hx).le)

lemma zero_final_lower : (293/1000:ℝ)<b 0 (7/10) := by
  have ht := cap_trig
  have ha := ShortOuterZero.fine_axial_bounds
  have hs := mul_lt_mul_of_pos_left ht.2.1
    (show 0<outerAxial-1/2 by linarith [ha.1])
  have hu := mul_lt_mul_of_pos_right
    (show outerAxial-1/2<(114321959/125000000:ℝ) by linarith [ha.2])
    (by norm_num : (0:ℝ)<16106/25000)
  norm_num [b,ShortOuterOne.SameContact.arc_zero]
  linarith [ht.2.2.1]

lemma b_lower {B x : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) : (293/1000:ℝ)<b B x := by
  have hangle := b_angle_antitone outer_zero_mem hx (by norm_num) hx.2
  have htarget := b_target_monotone hx outer_zero_mem hB hB.1
  exact zero_final_lower.trans_le (hangle.trans htarget)

lemma norm_identity {B : ℝ} (hB : B∈Icc 0 outerDiagonal) (x : ℝ) :
    (b B x-1/2)^2+(v B x)^2=NegativeTwo.Inverse.q (U B) := by
  have hc := UW_circle (outer_domain hB)
  have ht := Real.sin_sq_add_cos_sq x
  dsimp [b,v,NegativeTwo.Inverse.q,U,W] at *
  linear_combination hc+((arc B-1/2)^2+(B+1/2)^2)*ht

lemma v_upper {B x : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) : v B x<(243/200:ℝ) := by
  have hc := UW_circle (outer_domain hB)
  have ht := Real.sin_sq_add_cos_sq x
  have hrot : (U B*Real.cos x+W B*Real.sin x)^2+
      (W B*Real.cos x-U B*Real.sin x)^2=Q0 := by
    linear_combination hc+((U B)^2+(W B)^2)*ht
  have hY : U B*Real.cos x+W B*Real.sin x<(1979/1000:ℝ) := by
    norm_num [Q0] at hrot
    nlinarith [sq_nonneg (W B*Real.cos x-U B*Real.sin x)]
  have he : v B x=U B*Real.cos x+W B*Real.sin x-Real.cos x := by
    dsimp [v,U,W]
    ring
  rw [he]
  linarith [(positive_trig hx).1]

lemma projection_identity {B x : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) :
    k B x/v B x=NegativeTwo.Inverse.factor (U B)+
      W B*(b B x-1/2)/(U B*NegativeTwo.Inverse.q (U B)*v B x) := by
  have hu := U_positive (outer_domain hB)
  have hq : 0<NegativeTwo.Inverse.q (U B) := by
    linarith [NegativeTwo.Inverse.actual_q_positive hB]
  have hv := v_positive hB hx
  have hc := UW_circle (outer_domain hB)
  have hk : k B x*U B=U B*Real.cos x+W B*Real.sin x := by
    have hr : ratio B=W B/U B := rfl
    rw [k,hr]
    field_simp
  have hvv : v B x=(U B-1)*Real.cos x+W B*Real.sin x := by dsimp [v,U,W]; ring
  have hbb : b B x-1/2=W B*Real.cos x-(U B-1)*Real.sin x := by dsimp [b,U,W]; ring
  have key : k B x*U B*NegativeTwo.Inverse.q (U B)=
      (Q0-U B)*v B x+W B*(b B x-1/2) := by
    rw [hk,hvv,hbb,NegativeTwo.Inverse.q]
    linear_combination (-Real.cos x)*hc
  rw [NegativeTwo.Inverse.factor,div_add_div _ _ (by positivity) (by positivity),
    div_eq_div_iff hv.ne' (by positivity)]
  linear_combination (U B*NegativeTwo.Inverse.q (U B)*v B x)*key

lemma value_angle_hasDerivAt (F G : RoleLabel) {B x : ℝ} (hd : Domain B x) :
    HasDerivAt (value F G B) (angleFirst F B x) x := by
  have hh := ((hasDerivAt_id' x).fun_add
    ((F.outer_hasDerivAt (outer_domain hd.2.2)).comp x (b_angle_hasDerivAt B x))).sub_const
      (G.outer B)
  exact hh.congr_deriv (by dsimp [angleFirst]; ring)

lemma value_target_hasDerivAt (F G : RoleLabel) {B x : ℝ} (hd : Domain B x) :
    HasDerivAt (fun t => value F G t x) (targetFirst F G B x) B := by
  have hh := (((F.outer_hasDerivAt (outer_domain hd.2.2)).comp B
    (b_target_hasDerivAt hd.1 x)).const_add x).fun_sub (G.outer_hasDerivAt (outer_domain hd.1))
  exact hh

lemma original_contact {a b₀ A B x : ℝ} (hs : OuterState a b₀) (ht : OuterState A B)
    (hx : |x|≤7/10) (hm : 0≤Eight.forwardMargin 0 a b₀ A B 1 1 x) :
    Domain B x ∧ b B x≤b₀ := by
  have hp := ShortOuterZero.positive_original_angle hs ht hx hm
  have hxi : x∈Icc 0 (7/10) := ⟨by linarith,(abs_le.mp hx).2⟩
  have hB : B∈Icc 0 outerDiagonal := ⟨ht.1,(outer_bounds ht).2.2.2.1⟩
  have hwidth : pairWidth x=(1+Real.sin x+Real.cos x)/2 := by
    rw [signed_width hx,abs_of_nonneg (positive_trig hxi).2.2.1]
    ring
  have hcut : b B x≤b₀ := by
    norm_num [forwardMargin] at hm
    rw [hwidth] at hm
    dsimp [b]
    rw [(ShortOuterOne.SameContact.actual_arc ht).1]
    linarith
  exact ⟨⟨hB,hxi,⟨by linarith [b_lower hB hxi],
    hcut.trans (outer_bounds hs).2.2.2.1⟩⟩,hcut⟩

end SquaresInCircles.Eight.TableFree.SecondWord.SameZero
