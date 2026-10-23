module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneOppositePrimaryUpperDiagonalData

/-!
# The four upper primary owners whose minimum is at the lower contact

Uncompiled transcription of Section 4 of the complementary note and
Section 2 of the three-family note. Convexity in the state coordinate
and positivity of the actual lower-endpoint derivative reduce every
original contact to its axial or diagonal reference curve.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.Opposite.Primary.Upper
open CommonQuarter CorePairGeometry Arithmetic
open SameContact (arc ratio)

theorem projection_whole {x : ℝ} (hx : x∈Icc 0 (7/10)) : (233/250:ℝ)<projection x := by
  have hconcave : ConcaveOn ℝ (Icc (0:ℝ) (7/10)) projection := by
    apply concave_of_deriv2 (fun y _ => projection_hasDerivAt y)
      (f'':=fun y => -projection y)
    · intro y _
      convert (Real.hasDerivAt_sin y).neg.add ((Real.hasDerivAt_cos y).const_mul rho) using 1 <;>
        dsimp [projectionD,projection] <;> ring
    · intro y hy
      have ht := positive_trig hy
      have hp := mul_nonneg (by linarith [rho_bounds.1] : 0≤rho) ht.2.2.1
      dsimp [projection]
      linarith [ht.1]
  apply concave_gt_of_endpoints hconcave hx
  · norm_num [projection]
  · have hs := RoleFour.fine_cap_trig
    have hp := mul_le_mul rho_bounds.1.le
      (show (161/250:ℝ)≤Real.sin (7/10) by linarith [hs.1]) (by norm_num)
      (by linarith [rho_bounds.1] : 0≤rho)
    dsimp [projection]
    linarith [hs.2.2.1]

theorem diagonal_support (r : Row) {x : ℝ} (hx : DiagonalDomain x) :
    -radius*Real.sqrt ((P r)^2+(t r)^2)≤P r*V x-t r*U x := by
  have hs := Real.sq_sqrt (show 0≤(P r)^2+(t r)^2 by positivity)
  have hn := Real.sqrt_nonneg ((P r)^2+(t r)^2)
  have hR := radius_bounds
  have hnorm : (radius*Real.sqrt ((P r)^2+(t r)^2))^2=Q0*((P r)^2+(t r)^2) := by
    rw [mul_pow,radius_sq,hs]
  have hidentity : (P r*V x-t r*U x)^2+(P r*U x+t r*V x)^2=
      ((P r)^2+(t r)^2)*Q0 := by
    nlinarith [diagonal_circle hx]
  have hp : 0≤radius*Real.sqrt ((P r)^2+(t r)^2) := mul_nonneg (by linarith) hn
  nlinarith [sq_nonneg (P r*U x+t r*V x)]

theorem simple_norm_reserve (r : Row) (hr : r=2∨r=5) :
    radius*Real.sqrt ((P r)^2+(t r)^2)+(1/20:ℝ)<(p r+q r)*(969/500:ℝ) := by
  have hs := Real.sq_sqrt (show 0≤(P r)^2+(t r)^2 by positivity)
  have hn := Real.sqrt_nonneg ((P r)^2+(t r)^2)
  have hnorm : (radius*Real.sqrt ((P r)^2+(t r)^2))^2=Q0*((P r)^2+(t r)^2) := by
    rw [mul_pow,radius_sq,hs]
  have hp : 0≤radius*Real.sqrt ((P r)^2+(t r)^2) :=
    mul_nonneg (by linarith [radius_bounds.1]) hn
  rcases hr with rfl | rfl <;> norm_num [p,q,P,t,Q0] at hnorm ⊢ <;> nlinarith

theorem J_norm_positive (r : Row) (hr : r=2∨r=5) {x : ℝ} (hx : DiagonalDomain x) :
    0<J r x := by
  have hc := diagonal_coordinate_bounds hx
  have hrT := diagonal_radical hx
  have hU : 0<U x := by linarith [hc.1]
  have he : J r x*U x=(p r+q r)*T x+P r*V x-t r*U x := by
    dsimp [J]
    field_simp [hU.ne']
    nlinarith [(diagonal_projection hx).1]
  have hL : 0<p r+q r := by linarith [(coefficients r).2.2.1]
  have hprod := mul_lt_mul_of_pos_left hrT.1 hL
  have hs := diagonal_support r hx
  have hn := simple_norm_reserve r hr
  have hpositive : 0<J r x*U x := by linarith
  exact (mul_pos_iff_of_pos_right hU).1 hpositive

theorem J_three_positive {x : ℝ} (hx : DiagonalDomain x) : 0<J 3 x := by
  have ht := positive_trig (SecondWord.SameZero.PJ.Diagonal.angle_mem hx.1)
  have hp := mul_le_mul_of_nonneg_left (diagonal_ratio hx).2 ht.2.2.1
  have hg := projection_whole (SecondWord.SameZero.PJ.Diagonal.angle_mem hx.1)
  dsimp [projection] at hg
  norm_num [J,p,q,P,t]
  nlinarith

theorem diagonal_small_sine_ratio {x : ℝ} (hx : DiagonalDomain x)
    (hs : Real.sin x<(197/1000:ℝ)) : V x/U x<(11/25:ℝ) := by
  have ht := positive_trig (SecondWord.SameZero.PJ.Diagonal.angle_mem hx.1)
  have hr := diagonal_radical hx
  have hc := diagonal_coordinate_bounds hx
  have hz0 : 0<z x ∧ z x<(2/5:ℝ) := by
    dsimp [z,SecondWord.SameZero.PJ.Diagonal.Z,SecondWord.SameZero.PJ.Diagonal.z₀]
    constructor <;> linarith [ShortMixedZero.fine_diagonal_bounds.1,
      ShortMixedZero.fine_diagonal_bounds.2,ht.2.2.1]
  have hfirst := mul_le_mul hs.le
    (hr.2.1.trans ShortWord.MixedQuarter.Reference.radius_fine.2.le)
    (by linarith [hr.1] : 0≤T x) (by norm_num)
  have hsecond := mul_le_mul_of_nonneg_left ht.2.1 hz0.1.le
  have hV : V x<(79/100:ℝ) := by
    dsimp [V,SecondWord.SameZero.PJ.Diagonal.vertical]
    nlinarith
  have hU : (181/100:ℝ)<U x := by
    have hcircle := diagonal_circle hx
    norm_num [Q0] at hcircle
    nlinarith [hc.1,hc.2.2.1]
  apply (div_lt_iff₀ (by linarith : 0<U x)).2
  linarith

theorem J_four_positive {x : ℝ} (hx : DiagonalDomain x) : 0<J 4 x := by
  have ht := positive_trig (SecondWord.SameZero.PJ.Diagonal.angle_mem hx.1)
  have hc := diagonal_coordinate_bounds hx
  have hrho := (diagonal_ratio hx).2
  by_cases hsign : 0≤q 4*Real.sin x+P 4
  · have hh := mul_le_mul_of_nonneg_left hrho hsign
    have hg := projection_whole (SecondWord.SameZero.PJ.Diagonal.angle_mem hx.1)
    dsimp [projection] at hg
    norm_num [J,p,q,P,t] at hsign hh ⊢
    nlinarith [rho_bounds.2]
  · have hs : Real.sin x<(197/1000:ℝ) := by
      norm_num [q,P] at hsign
      linarith
    have hcos : (49/50:ℝ)<Real.cos x := by
      nlinarith [Real.sin_sq_add_cos_sq x,ht.1,ht.2.2.1]
    have hratio := diagonal_small_sine_ratio hx hs
    have hh := mul_le_mul_of_nonpos_left hratio.le (le_of_lt (lt_of_not_ge hsign))
    norm_num [J,p,q,P,t] at hh ⊢
    nlinarith [ht.2.2.1]

theorem J_simple_positive (r : Row) (hr : r=2∨r=3∨r=4∨r=5)
    {x : ℝ} (hx : DiagonalDomain x) : 0<J r x := by
  rcases hr with rfl | rfl | rfl | rfl
  · exact J_norm_positive 2 (Or.inl rfl) hx
  · exact J_three_positive hx
  · exact J_four_positive hx
  · exact J_norm_positive 5 (Or.inr rfl) hx

theorem after_simple (r : Row) (hr : r=2∨r=3∨r=4∨r=5)
    {B e x : ℝ} (he : IsEvent e) (hd : Domain B x) (hx : e≤x) :
    (4489/5000:ℝ)<value r B x := by
  have hxD := after_diagonal_domain he ⟨hx,hd.2.1.2⟩
  have hD := diagonal_contact_domain hxD
  have hJ := J_simple_positive r hr hxD
  rw [J_first r hxD] at hJ
  have hminimum := endpoint_minimum r hD hd (diagonal_lower_target hd hxD) hJ.le
  have hinc := G_simple_increasing r (Or.inr hr) he
    ⟨le_rfl,(event_bounds he).2.2.2⟩ ⟨hx,hd.2.1.2⟩ hx
  rw [G_at_event r he,G_value r hxD] at hinc
  have hF : (4489/5000:ℝ)<F r e := by
    by_cases hpair : r=3∨r=4
    · exact F_pair_lower r hpair he ⟨by linarith [(event_bounds he).1],le_rfl⟩
    · have hs : r=2∨r=5 := by rcases hr with h | h | h | h <;> tauto
      have hh := F_simple_lower r hs he ⟨by linarith [(event_bounds he).1],le_rfl⟩
      linarith
  exact hF.trans_le (hinc.trans hminimum)

theorem simple_contact (r : Row) (hr : r=2∨r=3∨r=4∨r=5)
    {B x : ℝ} (hd : Domain B x) : (4489/5000:ℝ)<value r B x := by
  obtain ⟨e,he⟩ := exists_event
  rcases le_total x e with hx | hx
  · exact before_simple r hr he hd hx
  · exact after_simple r hr he hd hx

end SquaresInCircles.Eight.TableFree.ShortOuterOne.Opposite.Primary.Upper
