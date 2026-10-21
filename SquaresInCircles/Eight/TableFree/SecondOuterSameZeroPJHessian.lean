module

public import SquaresInCircles.Eight.TableFree.SecondOuterSameZeroPJCriticalBounds

/-!
# The uniform negative P/J Hessian direction

Uncompiled source draft.  This is the single whole-domain estimate in
Section 3 of the same-sign hand proof.  The explicit inverse-contact
second derivative is below -.05 on the critical coordinate range.
Together with the proved E and mixed-derivative bounds, the Hessian
is negative on the fixed direction (1,-.7).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.SameZero.PJ
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (ratio)
open NegativeTwo.Inverse (q N factorD brace)

def qLower : ℝ := 3029/2500
def qUpper : ℝ := 3289/2500
def factorLower : ℝ := N (9/5)/((9/5)*qUpper)^2
def braceUpper : ℝ := Q0/(9/5)^3-3*(189/500)^2/qUpper

lemma inverse_target_upper {u r z w : ℝ}
    (hu : u∈Icc (9/5:ℝ) (463/250)) (hr : (189/500:ℝ)<r)
    (hz : z∈Icc (0:ℝ) (2/5)) (hw : 0<w) (hn : z^2+w^2=q u) :
    PJCritical.inverseTarget u r z w< -(1/20:ℝ) := by
  have hu0 : 0<u := by linarith [hu.1]
  have hq : q u∈Icc qLower qUpper := by
    dsimp [q,NegativeTwo.Inverse.q,qLower,qUpper]
    norm_num [Q0]
    constructor <;> linarith [hu.1,hu.2]
  have hq0 : 0<q u := by linarith [hq.1,show (0:ℝ)<qLower by norm_num [qLower]]
  have hN : N (9/5)≤N u := by
    have hp := mul_nonneg (sub_nonneg.mpr hu.1)
      (show 0≤4*Q0-2*(u+9/5) by norm_num [Q0]; linarith [hu.2])
    dsimp [N,NegativeTwo.Inverse.N]
    nlinarith
  have hmass : u*q u≤(9/5)*qUpper := by
    have hp := mul_nonneg (sub_nonneg.mpr hu.1)
      (show 0≤2*u+18/5-(Q0+1) by norm_num [Q0]; linarith [hu.1])
    norm_num [q,NegativeTwo.Inverse.q,qUpper,Q0] at *
    nlinarith
  have hf0 : 0<factorLower := by norm_num [factorLower,N,NegativeTwo.Inverse.N,qUpper,Q0]
  have hf : factorLower≤factorD u := by
    apply (le_div_iff₀ (mul_pos (sq_pos_of_pos hu0) (sq_pos_of_pos hq0))).2
    have hh := pow_le_pow_left₀ (mul_pos hu0 hq0).le hmass 2
    have hm := mul_le_mul_of_nonneg_left hh hf0.le
    have he : factorLower*((9/5)*qUpper)^2=N (9/5) := by
      norm_num [factorLower,qUpper]
    rw [he] at hm
    nlinarith
  have hr0 : 0<r := by linarith
  have hr2 : (189/500:ℝ)^2≤r^2 :=
    pow_le_pow_left₀ (by norm_num) hr.le 2
  have hu3 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤9/5) hu.1 3
  have hfirst : Q0/u^3≤Q0/(9/5)^3 := by
    apply (div_le_iff₀ (pow_pos hu0 3)).2
    norm_num [Q0]
    nlinarith
  have hsecond : (189/500:ℝ)^2/qUpper≤r^2/q u := by
    apply (le_div_iff₀ hq0).2
    have hh := mul_le_mul_of_nonneg_left hq.2
      (by norm_num [qUpper] : (0:ℝ)≤(189/500)^2/qUpper)
    norm_num [qUpper] at hh
    nlinarith
  have hw2 : w^2≤qUpper := by nlinarith [sq_nonneg z]
  have hthird : (189/500:ℝ)^2/qUpper≤r^2/w^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hw)).2
    have hh := mul_le_mul_of_nonneg_left hw2
      (by norm_num [qUpper] : (0:ℝ)≤(189/500)^2/qUpper)
    norm_num [qUpper] at hh
    nlinarith
  have hb : brace u r w≤braceUpper := by
    dsimp [brace,NegativeTwo.Inverse.brace,braceUpper]
    linarith
  have hb0 : 0≤braceUpper := by norm_num [braceUpper,qUpper,Q0]
  have hz2 := pow_le_pow_left₀ hz.1 hz.2 2
  have hwl : (41/40:ℝ)<w := by
    have hh := hq.1
    norm_num [qLower] at hh
    nlinarith
  have hden := mul_le_mul hq.1 hwl.le
    (by norm_num : (0:ℝ)≤41/40) hq0.le
  have hweight : z/(q u*w)≤(2/5)/(qLower*(41/40)) := by
    apply (div_le_iff₀ (mul_pos hq0 hw)).2
    have hh := mul_le_mul_of_nonneg_left hden
      (by norm_num [qLower] : (0:ℝ)≤(2/5)/(qLower*(41/40)))
    norm_num [qLower] at hh
    linarith [hz.2]
  have hmiddle := (mul_le_mul_of_nonneg_left hb
    (div_nonneg hz.1 (mul_pos hq0 hw).le)).trans
      (mul_le_mul_of_nonneg_right hweight hb0)
  have hprod := mul_le_mul hr.le hf hf0.le hr0.le
  have href : -(189/500)*factorLower+
      ((2/5)/(qLower*(41/40)))*braceUpper< -(1/20:ℝ) := by
    norm_num [factorLower,braceUpper,N,NegativeTwo.Inverse.N,qLower,qUpper,Q0]
  dsimp [PJCritical.inverseTarget,PJCritical.heightFactorD]
  linarith

lemma stationary_actual {B x : ℝ} (hd : Domain B x)
    (hstat : angleFirst PLabel B x=0) :
    b B x∈sourceInterval ∧ criticalU (b B x)=U B ∧
      criticalV (b B x)=W B ∧ criticalRatio (b B x)=ratio B ∧
      B∈Ioo (1/5:ℝ) (8/25) := by
  have hs : b B x∈sourceInterval := ⟨(stationary_source hd hstat).le,hd.2.2.2⟩
  have he := stationary_coordinate hd hstat
  have hc := critical_data hs
  have hcircle := UW_circle (outer_domain hd.1)
  have hW : 0<W B := by dsimp [W]; linarith [hd.1.1]
  have hV : criticalV (b B x)=W B := by
    rw [he] at hc
    nlinarith [hc.2.2.1,hc.2.2.2.1]
  have hr : criticalRatio (b B x)=ratio B := by
    dsimp [criticalRatio,ratio,U,W]
    rw [show criticalV (b B x)=B+1/2 from hV,
      show criticalU (b B x)=ShortOuterOne.SameContact.arc B+1/2 from he]
  have hB : B∈Ioo (1/5:ℝ) (8/25) := by
    have hlo := hc.2.2.2.2.1
    have hhi := hc.2.2.2.2.2.1
    rw [hV] at hlo hhi
    dsimp [W] at hlo hhi
    constructor <;> linarith
  exact ⟨hs,he,hV,hr,hB⟩

theorem hessian_direction_negative {B x : ℝ} (hd : Domain B x)
    (hstat : angleFirst PLabel B x=0) :
    E (b B x)-(7/5)*ratio B*(p (b B x))^3+
      (49/100)*(PJCritical.inverseTarget (U B) (ratio B)
        (b B x-1/2) (v B x)-JLabel.d2 B)< -(1/200:ℝ) := by
  obtain ⟨hs,he,hV,hr,hB⟩ := stationary_actual hd hstat
  have hc := critical_data hs
  have hu := criticalU_bounds hs
  rw [he] at hu
  have hu' : U B∈Icc (9/5:ℝ) (463/250) := ⟨by linarith,by linarith⟩
  have hr' : (189/500:ℝ)<ratio B := by
    have hh := hc.2.2.2.2.2.2
    rwa [hr] at hh
  have hz : b B x-1/2∈Icc (0:ℝ) (2/5) := by
    constructor <;> linarith [hs.1,hd.2.2.2,outer_endpoint_bounds.2.2.2]
  have hinverse := inverse_target_upper hu' hr' hz (v_positive hd.1 hd.2.1)
    (norm_identity hd.1 x)
  have hJ := J_second_antitone hd.1
    (Asymmetric.rational_outer_mem (by norm_num : (8/25:ℝ)∈Icc 0 (899/1000))) hB.2.le
  have hcross := critical_mixed_lower hs
  rw [hr] at hcross
  have hE := (E_bounds hs).2
  nlinarith [J_eight_twentyfifths_second]

end SquaresInCircles.Eight.TableFree.SecondWord.SameZero.PJ
