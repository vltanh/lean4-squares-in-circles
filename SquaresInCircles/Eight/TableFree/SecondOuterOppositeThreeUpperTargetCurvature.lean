module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreeUpperDiagonal

/-!
# Target derivatives on the complete remaining primary rectangle

The source is held fixed while the physical target primary height is
inserted into the explicit inverse rotation.  All target derivatives
are derived from that actual composition; their radical stays positive
on the enlarged rectangle `[0,.1] × [.664,d]`.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.UpperTarget
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
    ring

lemma cost_hasDerivAt {b B : ℝ} (hb : b∈Icc 0 outerDiagonal) (hB : B∈Icc 0 outerDiagonal) :
    HasDerivAt (cost b) (first b B) B := by
  have hd := (OppositeTwo.PrimaryInverse.X_shift_hasDerivAt hb (shift_mem hB)).comp B
    (z_hasDerivAt hB)
  convert ((hd.const_add (Real.pi/2)).sub_const (T b)).sub
    (LLabel.outer_hasDerivAt (outer_domain hB)) using 1 <;>
    dsimp [cost,first,speed] <;> ring

lemma first_hasDerivAt {b B : ℝ} (hb : b∈Icc 0 outerDiagonal) (hB : B∈Icc 0 outerDiagonal) :
    HasDerivAt (first b) (second b B) B := by
  have hv := (speed_data hb hB).1
  have hd := ((ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hB)).div
    (speed_hasDerivAt hb hB) hv.ne').sub (LLabel.d1_hasDerivAt (outer_domain hB))
  convert hd using 1
  · rfl
  · dsimp [second]
    field_simp [hv.ne']
    ring

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
  norm_num [LLabel,Q0,W] at hh hp
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

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.UpperTarget
