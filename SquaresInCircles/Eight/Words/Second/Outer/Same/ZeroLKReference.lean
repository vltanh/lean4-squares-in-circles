module

public import SquaresInCircles.Eight.Words.Second.Outer.PointProducts
public import SquaresInCircles.Eight.Words.Second.Outer.VBounds
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.ThreeData
public import SquaresInCircles.Eight.Words.Short.Outer.Zero.PositivePrimary

/-!
# Eight squares: the single target-zero reference for the L/K row

The displayed rational angle determines its
actual source coordinate and circle radical.  Taylor bounds and exact
circle squares prove the reference value and slope; no independently
chosen contact coordinate is substituted for the original one.
-/

section
/-!
## The original same-sign zero-quarter contact

The source transverse coordinate is solved
directly from its original weak secondary separator.  The contact
increases with the original target coordinate and decreases with the
angle.  Its exact circle speed and projection identities are shared by
the P/J and L/K costs, without any contact-location premise.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.SameZero
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
    (fun _ hx => neg_nonpos.mpr (v_positive hB (Ioo_subset_Icc_self hx)).le)

lemma b_target_monotone {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    MonotoneOn (fun B => b B x) (Icc 0 outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun _ hB => (b_target_hasDerivAt hB x).continuousAt.continuousWithinAt)
    (fun _ hB => b_target_hasDerivAt (Ioo_subset_Icc_self hB) x)
    (fun _ hB => (k_positive (Ioo_subset_Icc_self hB) hx).le)

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

end SquaresInCircles.Eight.SecondWord.SameZero
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.SameZero.LK
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

def reference : ℝ := 15781/100000
def bLo : ℝ := 4250280203/5000000000
def bHi : ℝ := 1700112083/2000000000
def vLo : ℝ := 4908944453/5000000000
def vHi : ℝ := 9817888921/10000000000
def uLo : ℝ := 14467026939/10000000000
def uHi : ℝ := 14467026949/10000000000

lemma reference_trig :
    (314311597/2000000000:ℝ)<Real.sin reference ∧
      Real.sin reference<1571557991/10000000000 ∧
      (395029529/400000000:ℝ)<Real.cos reference ∧
      Real.cos reference<4937869113/5000000000 := by
  rw [show reference=15781/100000 from rfl]
  have hs := sin_lower_seven (x := 15781/100000) (by norm_num)
  have hu := sin_upper_five (x := 15781/100000) (by norm_num)
  have hc := cos_lower_six (x := 15781/100000) (by norm_num)
  have hk := cos_le_cos8 (x := 15781/100000) (by norm_num)
  norm_num [cos8] at hs hu hc hk
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma reference_coordinates : b 0 reference∈Icc bLo bHi ∧ v 0 reference∈Icc vLo vHi := by
  have ht := reference_trig
  have ha := ShortOuterZero.fine_axial_bounds
  have has0 : 0≤outerAxial-1/2 := by linarith [ha.1]
  have hslo := mul_le_mul
    (show (914575671/1000000000:ℝ)≤outerAxial-1/2 by linarith [ha.1]) ht.1.le
    (by norm_num : (0:ℝ)≤314311597/2000000000) has0
  have hshi := mul_le_mul
    (show outerAxial-1/2≤(114321959/125000000:ℝ) by linarith [ha.2]) ht.2.1.le
    (show 0≤Real.sin reference by linarith [ht.1]) (by norm_num : (0:ℝ)≤114321959/125000000)
  have hclo := mul_le_mul
    (show (914575671/1000000000:ℝ)≤outerAxial-1/2 by linarith [ha.1]) ht.2.2.1.le
    (by norm_num : (0:ℝ)≤395029529/400000000) has0
  have hchi := mul_le_mul
    (show outerAxial-1/2≤(114321959/125000000:ℝ) by linarith [ha.2]) ht.2.2.2.le
    (show 0≤Real.cos reference by linarith [ht.2.2.1]) (by norm_num : (0:ℝ)≤114321959/125000000)
  norm_num [b,v,ShortOuterOne.SameContact.arc_zero,bLo,bHi,vLo,vHi]
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩ <;> linarith

lemma reference_domain : Domain 0 reference ∧ (151/200:ℝ)<b 0 reference := by
  have hb := reference_coordinates.1
  refine ⟨⟨outer_zero_mem,by norm_num [reference],⟨?_,?_⟩⟩,?_⟩
  · norm_num [bLo] at hb
    linarith
  · norm_num [bHi] at hb
    linarith [fine_outer_endpoint_bounds.2]
  · norm_num [bLo] at hb
    linarith

lemma reference_radical : U (b 0 reference)∈Icc uLo uHi := by
  have hb := reference_coordinates.1
  have hc := UW_circle (outer_domain reference_domain.1.2.2)
  have hu := U_positive (outer_domain reference_domain.1.2.2)
  have hb2lo := pow_le_pow_left₀ (by norm_num [bLo] : (0:ℝ)≤bLo+1/2)
    (show bLo+1/2≤b 0 reference+1/2 by linarith [hb.1]) 2
  have hb2hi := pow_le_pow_left₀ (show 0≤b 0 reference+1/2 by
    linarith [reference_domain.1.2.2.1])
    (show b 0 reference+1/2≤bHi+1/2 by linarith [hb.2]) 2
  have hW : W (b 0 reference)=b 0 reference+1/2 := rfl
  rw [hW] at hc
  constructor
  · apply le_of_pow_le_pow_left₀ (n := 2) (by norm_num) hu.le
    norm_num [bHi,uLo,Q0] at hb2hi hc ⊢
    linarith
  · apply le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (by norm_num [uHi])
    norm_num [bLo,uHi,Q0] at hb2lo hc ⊢
    linarith

theorem reference_value :
    (8977797/10000000:ℝ)<value LLabel KLabel 0 reference ∧
      |angleFirst LLabel 0 reference|<(3/1000000:ℝ) := by
  have hh := GeneralReference.label LLabel reference_domain.1.2.2
    reference_coordinates.1 reference_radical
    (by norm_num [bLo] : (0:ℝ)≤bLo) (by norm_num [uLo] : (1/2:ℝ)<uLo)
  have hv := reference_coordinates.2
  have hvl : (7100939225198/10000000000000:ℝ)≤
      GeneralReference.valueLo LLabel bLo bHi uLo uHi := by
    norm_num [GeneralReference.valueLo,GeneralReference.lo,LLabel,bLo,bHi,uLo,uHi]
  have hfl : (1018546847/1000000000:ℝ)≤GeneralReference.firstLo LLabel bLo bHi uLo uHi := by
    norm_num [GeneralReference.firstLo,GeneralReference.lo,GeneralReference.rlo,
      GeneralReference.rhi,LLabel,bLo,bHi,uLo,uHi]
  have hfh : GeneralReference.firstHi LLabel bLo bHi uLo uHi≤(1018546856/1000000000:ℝ) := by
    norm_num [GeneralReference.firstHi,GeneralReference.hi,GeneralReference.rlo,
      GeneralReference.rhi,LLabel,bLo,bHi,uLo,uHi]
  have hp := mul_le_mul (hfl.trans hh.2.2.1) hv.1 (by norm_num [vLo] : (0:ℝ)≤vLo)
    (show 0≤LLabel.d1 (b 0 reference) by linarith [hfl.trans hh.2.2.1])
  have hq := mul_le_mul (hh.2.2.2.1.trans hfh) hv.2
    (v_positive outer_zero_mem reference_domain.1.2.1).le (by norm_num)
  have hK := K_zero
  have ha := ShortOuterZero.fine_axial_bounds
  dsimp [K] at hK
  norm_num [vLo,vHi] at hp hq
  constructor
  · have hL := hvl.trans hh.1
    dsimp only [value]
    rw [hK]
    linarith [show reference=15781/100000 from rfl,ha.1]
  · rw [abs_lt]
    dsimp only [angleFirst]
    constructor <;> linarith

end SquaresInCircles.Eight.SecondWord.SameZero.LK
end
end
end
