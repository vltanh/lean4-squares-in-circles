module

public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreeUpperDiagonalData

/-!
# Eight squares: one target concavity bound on the entire primary rectangle

The middle numerator of the third derivative is negative everywhere.
The two remaining positive terms are bounded on the complete rectangle,
and the literal `L'''` endpoint exceeds their sum.  The fixed left
target curvature is negative, hence so is every later target curvature.
-/

section
/-!
## Target derivatives on the complete remaining primary rectangle

The source is held fixed while the physical target primary height is
inserted into the explicit inverse rotation.  All target derivatives
are derived from that actual composition; their radical stays positive
on the enlarged rectangle `[0,.1] × [.664,d]`.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree.UpperTarget
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)

def z (B : ℝ) : ℝ := arc B-1/2
def speed (b B : ℝ) : ℝ := UpperInverse.speed (z B) b
def cost (b B : ℝ) : ℝ := Real.pi/2+UpperInverse.X (z B) b-T b-L B
def first (b B : ℝ) : ℝ := ratio B/speed b B-LLabel.d1 B
def second (b B : ℝ) : ℝ :=
  ratioD B/speed b B-z B*(ratio B)^2/(speed b B)^3-LLabel.d2 B
def third (b B : ℝ) : ℝ :=
  ratioDD B/speed b B+
    ratio B*((ratio B)^2-3*z B*ratioD B)/(speed b B)^3+
    3*(z B)^2*(ratio B)^3/(speed b B)^5-LLabel.d3 B

lemma target_start_mem : (83/125:ℝ)∈Icc 0 outerDiagonal := by
  constructor <;> linarith [fine_outer_endpoint_bounds.2]

lemma target_domain {B : ℝ} (hB : B∈Icc (83/125) outerDiagonal) :
    B∈Icc 0 outerDiagonal := ⟨by linarith [hB.1],hB.2⟩

lemma shift_mem {B : ℝ} (hB : B∈Icc 0 outerDiagonal) : z B∈UpperInverse.shifts :=
  UpperInverse.primary_shift (ShortOuterOne.SameContact.arc_state hB)

lemma speed_data {b B : ℝ} (hb : b∈Icc 0 outerDiagonal) (hB : B∈Icc 0 outerDiagonal) :
    0<speed b B ∧ (z B)^2+(speed b B)^2=NegativeTwo.Inverse.q (U b) := by
  have hh := OppositeTwo.PrimaryInverse.data hb (shift_mem hB)
  exact ⟨hh.2.2.1,hh.2.2.2⟩

lemma z_hasDerivAt {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    HasDerivAt z (-ratio B) B :=
  (ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hB)).sub_const (1/2)

lemma speed_hasDerivAt {b B : ℝ} (hb : b∈Icc 0 outerDiagonal) (hB : B∈Icc 0 outerDiagonal) :
    HasDerivAt (speed b) (z B*ratio B/speed b B) B := by
  have hh := speed_data hb hB
  have hrad : NegativeTwo.Inverse.q (U b)-(z B)^2≠0 := by
    nlinarith [hh.1,hh.2]
  have hd := (((z_hasDerivAt hB).pow 2).const_sub (NegativeTwo.Inverse.q (U b))).sqrt hrad
  convert hd using 1
  · rfl
  · dsimp [speed,UpperInverse.speed,OppositeTwo.PrimaryInverse.speed,
      NegativeTwo.ContactInverse.speed]
    field_simp [show Real.sqrt (NegativeTwo.Inverse.q (U b)-(z B)^2)≠0 from hh.1.ne']

lemma cost_hasDerivAt {b B : ℝ} (hb : b∈Icc 0 outerDiagonal) (hB : B∈Icc 0 outerDiagonal) :
    HasDerivAt (cost b) (first b B) B := by
  have hd := (OppositeTwo.PrimaryInverse.X_shift_hasDerivAt hb (shift_mem hB)).comp B
    (z_hasDerivAt hB)
  convert ((hd.const_add (Real.pi/2)).sub_const (T b)).sub
    (LLabel.outer_hasDerivAt (outer_domain hB)) using 1
  · funext x
    simp only [cost,L,Function.comp_apply,Pi.sub_apply]
  · dsimp [first,speed]
    ring

lemma first_hasDerivAt {b B : ℝ} (hb : b∈Icc 0 outerDiagonal) (hB : B∈Icc 0 outerDiagonal) :
    HasDerivAt (first b) (second b B) B := by
  have hv := (speed_data hb hB).1
  have hd := ((ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hB)).div
    (speed_hasDerivAt hb hB) hv.ne').sub (LLabel.d1_hasDerivAt (outer_domain hB))
  convert hd using 1
  · rfl
  · dsimp [second]
    field_simp [hv.ne']

lemma second_hasDerivAt {b B : ℝ} (hb : b∈Icc 0 outerDiagonal) (hB : B∈Icc 0 outerDiagonal) :
    HasDerivAt (second b) (third b B) B := by
  have hv := (speed_data hb hB).1
  have hd := (((ShortOuterOne.SameContact.ratioD_hasDerivAt (outer_domain hB)).div
    (speed_hasDerivAt hb hB) hv.ne').sub
      (((z_hasDerivAt hB).mul
        ((ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hB)).pow 2)).div
          ((speed_hasDerivAt hb hB).pow 3) (pow_ne_zero 3 hv.ne'))).sub
            (LLabel.d2_hasDerivAt (outer_domain hB))
  convert hd using 1
  · rfl
  · dsimp [third]
    field_simp [hv.ne']
    ring

lemma target_start_U : (160021/100000:ℝ)<U (83/125) ∧ U (83/125)<160023/100000 :=
  shifted_chart_reference (outer_domain target_start_mem)
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])

lemma rectangle_geometry {b B : ℝ} (hb : b∈Icc 0 (1/10))
    (hB : B∈Icc (83/125) outerDiagonal) :
    (1399/1000:ℝ)<U B ∧ U B<1601/1000 ∧
      (399/1000:ℝ)<z B ∧ z B<601/1000 ∧ (17/20:ℝ)<speed b B := by
  have hbf := UpperDiagonal.early_domain hb
  have hBf := target_domain hB
  have hUlo := (UW_bounds hBf).1
  have hmono := ShortOuterOne.SameContact.arc_antitone
    (outer_domain target_start_mem) (outer_domain hBf) hB.1
  have hUhi : U B<(1601/1000:ℝ) := by
    have hh := target_start_U.2
    dsimp [U] at hh ⊢
    linarith
  have hzlo : (399/1000:ℝ)<z B := by dsimp [z]; dsimp [U] at hUlo; linarith
  have hzhi : z B<(601/1000:ℝ) := by dsimp [z]; dsimp [U] at hUhi; linarith
  have hv := speed_data hbf hBf
  have hq := NegativeTwo.Inverse.actual_q_positive hbf
  have hvlo : (17/20:ℝ)<speed b B := by nlinarith [hv.1,hv.2]
  exact ⟨hUlo,hUhi,hzlo,hzhi,hvlo⟩

lemma target_start_second : (963/1000:ℝ)<LLabel.d2 (83/125) := by
  have hh := LLabel.second_chart_reference (outer_domain target_start_mem)
    (l := (160021/100000:ℝ)) (u := (160023/100000:ℝ))
    (dlo := (963/1000:ℝ)) (dhi := (1:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [LLabel,W,Q0]) (by norm_num [LLabel,W,Q0])
  exact hh.1

lemma target_start_third : (353/50:ℝ)<LLabel.d3 (83/125) := by
  have hh := LLabel.third_numerator (outer_domain target_start_mem)
  have hu := U_positive (outer_domain target_start_mem)
  have hp := pow_le_pow_left₀ hu.le target_start_U.2.le 5
  have hp0 := pow_pos hu 5
  have hval : -3*Q0*(LLabel.s*Q0+(LLabel.p-LLabel.s/2)*W (83/125))=
      (11591225586369/156250000000:ℝ) := by
    norm_num [LLabel,Q0,W]
  rw [hval] at hh
  norm_num at hp
  nlinarith

lemma target_start_speed {b : ℝ} (hb : b∈Icc 0 (1/10)) :
    speed b (83/125)<(443/500:ℝ) := by
  have hbf := UpperDiagonal.early_domain hb
  have hm := ShortOuterOne.SameContact.arc_antitone
    (outer_domain hbf) (outer_domain tenth_mem) hb.2
  have hu : (94281/50000:ℝ)<U b := by
    have hh := UpperDiagonal.tenth_U.1
    dsimp [U] at hh ⊢
    linarith
  have hq : NegativeTwo.Inverse.q (U b)<(28609/25000:ℝ) := by
    norm_num [NegativeTwo.Inverse.q,Q0]
    linarith
  have hz : (60021/100000:ℝ)<z (83/125) := by
    have hh := target_start_U.1
    dsimp [z,U] at *
    linarith
  have hv := speed_data hbf target_start_mem
  nlinarith [hv.1,hv.2]

end SquaresInCircles.Eight.SecondWord.OppositeThree.UpperTarget
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree.UpperTarget
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)

lemma third_negative {b B : ℝ} (hb : b∈Icc 0 (1/10))
    (hB : B∈Icc (83/125) outerDiagonal) : third b B<0 := by
  have hg := rectangle_geometry hb hB
  have hBf := target_domain hB
  have hu := U_positive (outer_domain hBf)
  have hv : 0<speed b B := by linarith [hg.2.2.2.2]
  have hr := outer_ratio_bounds hBf
  have hr0 : 0<ratio B := by linarith [hr.1]
  have hz0 : 0<z B := by linarith [hg.2.2.1]
  have hU3 := pow_lt_pow_left₀ hg.2.1 hu.le (by norm_num : (3:ℕ)≠0)
  have hD : (19/20:ℝ)<ratioD B := by
    change (19/20:ℝ)<Q0/(U B)^3
    apply (lt_div_iff₀ (pow_pos hu 3)).2
    norm_num [Q0] at *
    nlinarith
  have hmiddleNum : (ratio B)^2-3*z B*ratioD B<0 := by
    have hp := mul_lt_mul'' hg.2.2.1 hD (by norm_num) (by norm_num)
    nlinarith [hr.2.1]
  have hmiddle : ratio B*((ratio B)^2-3*z B*ratioD B)/(speed b B)^3<0 :=
    div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hr0 hmiddleNum) (pow_pos hv 3)
  have hU5 := pow_lt_pow_left₀ hg.1 (by norm_num : (0:ℝ)≤1399/1000)
    (by norm_num : (5:ℕ)≠0)
  have hden := mul_lt_mul'' hU5 hg.2.2.2.2 (by norm_num) (by norm_num)
  have hW : W B<(7/5:ℝ) := by
    dsimp [W]
    linarith [hB.2,outer_endpoint_bounds.2.2.2]
  have hfirst : ratioDD B/speed b B<(37/10:ℝ) := by
    change (3*Q0*W B/(U B)^5)/speed b B<(37/10:ℝ)
    rw [div_div]
    apply (div_lt_iff₀ (mul_pos (pow_pos hu 5) hv)).2
    norm_num [Q0] at *
    nlinarith
  have hv5 := pow_lt_pow_left₀ hg.2.2.2.2 (by norm_num : (0:ℝ)≤17/20)
    (by norm_num : (5:ℕ)≠0)
  have hz2 : (z B)^2<(601/1000:ℝ)^2 := by nlinarith [hg.2.2.2.1]
  have hr3 : (ratio B)^3≤1 := by
    have hh := pow_le_pow_left₀ hr0.le hr.2.1 3
    simpa using hh
  have hprod := mul_le_mul hz2.le hr3 (pow_nonneg hr0.le 3) (by norm_num)
  have hlast : 3*(z B)^2*(ratio B)^3/(speed b B)^5<(5/2:ℝ) := by
    apply (div_lt_iff₀ (pow_pos hv 5)).2
    norm_num at hprod hv5
    nlinarith
  have hL := target_start_third.trans_le
    (L_third_monotone target_start_mem hBf hB.1)
  dsimp [third]
  linarith

lemma target_start_ratio : (72739/100000:ℝ)<ratio (83/125) := by
  have hu := U_positive (outer_domain target_start_mem)
  change (72739/100000:ℝ)<(83/125+1/2)/U (83/125)
  apply (lt_div_iff₀ hu).2
  nlinarith [target_start_U.2]

lemma target_start_ratioD : ratioD (83/125)<(239/250:ℝ) := by
  have hu := U_positive (outer_domain target_start_mem)
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤160021/100000)
    target_start_U.1.le 3
  change Q0/(U (83/125))^3<(239/250:ℝ)
  apply (div_lt_iff₀ (pow_pos hu 3)).2
  norm_num [Q0] at *
  nlinarith

lemma target_start_product : (127/400:ℝ)<z (83/125)*(ratio (83/125))^2 := by
  have hz : (60021/100000:ℝ)<z (83/125) := by
    have hh := target_start_U.1
    dsimp [z,U] at *
    linarith
  have hr := target_start_ratio
  have hs : (72739/100000:ℝ)^2<(ratio (83/125))^2 := by nlinarith
  have hp := mul_lt_mul'' hz hs (by norm_num) (by norm_num)
  norm_num at hp
  linarith

lemma second_at_start {b : ℝ} (hb : b∈Icc 0 (1/10)) :
    second b (83/125)<(-(7/25):ℝ) := by
  have hstart : (83/125:ℝ)∈Icc (83/125) outerDiagonal := ⟨le_rfl,target_start_mem.2⟩
  have hg := rectangle_geometry hb hstart
  have hv : 0<speed b (83/125) := by linarith [hg.2.2.2.2]
  have hfirst : ratioD (83/125)/speed b (83/125)<(9/8:ℝ) := by
    apply (div_lt_iff₀ hv).2
    nlinarith [target_start_ratioD]
  have hvhi := target_start_speed hb
  have hv3 := pow_lt_pow_left₀ hvhi hv.le (by norm_num : (3:ℕ)≠0)
  have hsecond : (9/20:ℝ)<z (83/125)*(ratio (83/125))^2/(speed b (83/125))^3 := by
    apply (lt_div_iff₀ (pow_pos hv 3)).2
    norm_num at hv3
    nlinarith [target_start_product]
  dsimp [second]
  linarith [target_start_second]

lemma second_negative {b B : ℝ} (hb : b∈Icc 0 (1/10))
    (hB : B∈Icc (83/125) outerDiagonal) : second b B<0 := by
  have hbf := UpperDiagonal.early_domain hb
  have hanti : AntitoneOn (second b) (Icc (83/125) outerDiagonal) :=
    antiOn_of_hasDeriv_nonpos
      (fun t ht => (second_hasDerivAt hbf (target_domain ht)).continuousAt.continuousWithinAt)
      (fun t ht => second_hasDerivAt hbf (target_domain (Ioo_subset_Icc_self ht)))
      (fun t ht => (third_negative hb (Ioo_subset_Icc_self ht)).le)
  have hh := hanti ⟨le_rfl,target_start_mem.2⟩ hB hB.1
  linarith [second_at_start hb]

theorem concave {b : ℝ} (hb : b∈Icc 0 (1/10)) :
    ConcaveOn ℝ (Icc (83/125) outerDiagonal) (cost b) :=
  concave_of_deriv2
    (fun _ ht => cost_hasDerivAt (UpperDiagonal.early_domain hb) (target_domain ht))
    (fun _ ht => first_hasDerivAt (UpperDiagonal.early_domain hb) (target_domain ht))
    (fun _ ht => (second_negative hb ht).le)

end SquaresInCircles.Eight.SecondWord.OppositeThree.UpperTarget
end
end
end
