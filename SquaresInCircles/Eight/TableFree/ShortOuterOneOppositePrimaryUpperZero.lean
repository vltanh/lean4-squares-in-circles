module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneOppositePrimaryUpperSimple

/-!
# The remaining reflected edge-2 upper primary owner

Uncompiled transcription of Sections 5--6 of the complementary note.
The diagonal endpoint derivative is bounded in the three intrinsic
sign cases of its displayed factors. The same global state curvature
then covers its possible interior contact minimum.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.Opposite.Primary.Upper
open CommonQuarter CorePairGeometry Arithmetic

def zeroDiagonalLower (s : ℝ) : ℝ :=
  (p 0+q 0)-t 0+P 0*(499/1250)/(969/500)+
  ((p 0+q 0)*(499/1250)/(969/500)+P 0*(1-1/(969/500)))*s+
  (p 0+q 0)*(1-1/(969/500)-1/(441/250))*s^2

theorem zeroDiagonalLower_bound {s : ℝ} (hs : s∈Icc (499/1250:ℝ) (129/200)) :
    -(187/1000:ℝ)<zeroDiagonalLower s := by
  have hc : ConcaveOn ℝ (Icc (499/1250:ℝ) (129/200)) zeroDiagonalLower := by
    apply concave_of_deriv2
      (f':=fun u => ((p 0+q 0)*(499/1250)/(969/500)+P 0*(1-1/(969/500)))+
        2*(p 0+q 0)*(1-1/(969/500)-1/(441/250))*u)
      (f'':=fun _ => 2*(p 0+q 0)*(1-1/(969/500)-1/(441/250)))
    · intro u _
      dsimp [zeroDiagonalLower]
      convert (((hasDerivAt_id u).const_mul
        ((p 0+q 0)*(499/1250)/(969/500)+P 0*(1-1/(969/500)))).const_add
          ((p 0+q 0)-t 0+P 0*(499/1250)/(969/500))).add
            (((hasDerivAt_id u).pow 2).const_mul
              ((p 0+q 0)*(1-1/(969/500)-1/(441/250)))) using 1 <;> ring
    · intro u _
      convert ((hasDerivAt_id u).const_mul
        (2*(p 0+q 0)*(1-1/(969/500)-1/(441/250)))).const_add
          ((p 0+q 0)*(499/1250)/(969/500)+P 0*(1-1/(969/500))) using 1 <;> ring
    · intro u _
      norm_num [p,q]
  exact concave_gt_of_endpoints hc hs
    (by norm_num [zeroDiagonalLower,p,q,P,t]) (by norm_num [zeroDiagonalLower,p,q,P,t])

theorem negative_z_ratio_lower {x : ℝ} (hx : DiagonalDomain x) (hz : z x<0) :
    Real.sin x+(499/1250-Real.sin x)/(969/500)≤V x/U x := by
  have hn := negative_z_data hx hz
  have hr := diagonal_radical hx
  have ht := positive_trig (SecondWord.SameZero.PJ.Diagonal.angle_mem hx.1)
  have hU := (diagonal_coordinate_bounds hx).1
  have hzl : (499/1250:ℝ)-Real.sin x≤z x := by
    dsimp [z,SecondWord.SameZero.PJ.Diagonal.Z,SecondWord.SameZero.PJ.Diagonal.z₀]
    linarith [ShortMixedZero.fine_diagonal_bounds.1]
  have hkz := mul_le_mul_of_nonpos_right ht.2.1 hz.le
  have hcut := mul_le_mul_of_nonpos_left hr.1.le
    (show (499/1250-Real.sin x)/(969/500:ℝ)≤0 by linarith [hn.1])
  have hlower0 : 0≤Real.sin x+(499/1250-Real.sin x)/(969/500:ℝ) := by linarith [hn.1]
  have hUT := mul_le_mul_of_nonneg_left (diagonal_U_le_T hx) hlower0
  apply (le_div_iff₀ (by linarith : 0<U x)).2
  dsimp [V,SecondWord.SameZero.PJ.Diagonal.vertical]
  nlinarith

theorem J_zero_lower {e x : ℝ} (he : IsEvent e) (hx : x∈Icc e (7/10)) :
    -(27/125:ℝ)<J 0 x := by
  have hd := after_diagonal_domain he hx
  have ht := positive_trig (SecondWord.SameZero.PJ.Diagonal.angle_mem hd.1)
  have hc := diagonal_coordinate_bounds hd
  have hcos := cosine_lower_square (SecondWord.SameZero.PJ.Diagonal.angle_mem hd.1)
  have hs0 : (10679/100000:ℝ)<Real.sin x := by
    exact (event_trig he).1.trans_le
      (sin_mono (event_bounds he).2.2 (SecondWord.SameZero.PJ.Diagonal.angle_mem hd.1) hx.1)
  by_cases hfactor : (p 0+q 0)*Real.sin x+P 0<0
  · have hs : Real.sin x<(67/500:ℝ) := by norm_num [p,q,P] at hfactor; linarith
    have hcos' : (9909/10000:ℝ)<Real.cos x := by
      nlinarith [Real.sin_sq_add_cos_sq x,ht.1,ht.2.2.1]
    have hp := mul_le_mul_of_nonpos_left hc.2.2.2.2.2.le hfactor.le
    norm_num [J,p,q,P,t] at hp ⊢
    nlinarith
  · have hf := le_of_not_gt hfactor
    by_cases hz : 0≤z x
    · have hr := (nonnegative_z_geometry hd hz).2.2
      have hp := mul_le_mul_of_nonneg_left hr hf
      have hs := sq_nonneg (2*(433/1000)*(68355/100000)*Real.sin x-9133/100000)
      have hsquare := sq_nonneg (Real.sin x)
      norm_num [p,q,P] at hp hf
      norm_num [J,p,q,P,t]
      nlinarith
    · have hzn := lt_of_not_ge hz
      have hn := negative_z_data hd hzn
      have hratio := negative_z_ratio_lower hd hzn
      have hp := mul_le_mul_of_nonneg_left hratio hf
      have hvalue := zeroDiagonalLower_bound
        (show Real.sin x∈Icc (499/1250:ℝ) (129/200) from ⟨hn.1.le,ht.2.2.2.1.le⟩)
      norm_num [p,q,P] at hp hf
      dsimp [zeroDiagonalLower] at hvalue
      norm_num [J,p,q,P,t] at hvalue ⊢
      nlinarith

theorem G_zero_lower {e x : ℝ} (he : IsEvent e) (hx : x∈Icc e (7/10)) :
    (1159/1250:ℝ)<G 0 x := by
  have hmono := G_simple_increasing 0 (Or.inl rfl) he
    ⟨le_rfl,(event_bounds he).2.2.2⟩ hx hx.1
  rw [G_at_event 0 he] at hmono
  have hF := F_zero_increasing he
    (show (134/1250:ℝ)∈Icc 0 e from ⟨by norm_num,(event_bounds he).1.le⟩)
    ⟨by linarith [(event_bounds he).1],le_rfl⟩ (event_bounds he).1.le
  exact Reference.zero_value_at_event_lower.trans_le (hF.trans hmono)

theorem after_zero {B e x : ℝ} (he : IsEvent e) (hd : Domain B x) (hx : e≤x) :
    (449/500:ℝ)<value 0 B x := by
  have hx' : x∈Icc e (7/10) := ⟨hx,hd.2.1.2⟩
  have hxD := after_diagonal_domain he hx'
  have hD := diagonal_contact_domain hxD
  have hJ := J_zero_lower he hx'
  rw [J_first 0 hxD] at hJ
  have hh := contact_remainder 0 hD hd (diagonal_lower_target hd hxD)
    (by norm_num : (0:ℝ)<43/50) (by norm_num : (0:ℝ)≤27/125) hJ.le
    (fun E hE => by simpa [curvatureFloor] using
      (curvature 0 (between_domain hD hd hE)).le)
  have hG := G_zero_lower he hx'
  rw [G_value 0 hxD] at hG
  norm_num at hh
  linarith

theorem zero_contact {B x : ℝ} (hd : Domain B x) : (449/500:ℝ)<value 0 B x := by
  obtain ⟨e,he⟩ := exists_event
  rcases le_total x e with hx | hx
  · exact before_zero he hd hx
  · exact after_zero he hd hx

end SquaresInCircles.Eight.TableFree.ShortOuterOne.Opposite.Primary.Upper
