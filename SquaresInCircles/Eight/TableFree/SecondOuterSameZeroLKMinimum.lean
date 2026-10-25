module

public import SquaresInCircles.Eight.TableFree.SecondOuterSameZeroLKBoundary
public import SquaresInCircles.Eight.TableFree.ContactArcMinimum
public import SquaresInCircles.Eight.TableFree.ContactContinuation

/-!
# The complete L/K same-sign contact minimum

Uncompiled source draft.  Compactness is applied to the whole physical
contact rectangle.  A minimum with positive target coordinate would
have nonpositive target derivative.  The exact derivative implication
then makes its angular derivative positive; the source diagonal and
the feasible left angular direction both contradict this.  Thus the
minimum is on the already bounded target-zero boundary.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.SameZero.LK
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

lemma diagonal_angle_negative {B x : ℝ} (hd : Domain B x)
    (hb : b B x=outerDiagonal) : angleFirst LLabel B x<0 := by
  have hL : (23/20:ℝ)<LLabel.d1 outerDiagonal := by
    rw [L_first_diagonal]
    linarith [outer_endpoint_bounds.2.2.2]
  have hz : outerDiagonal-1/2∈Icc (0:ℝ) (2/5) := by
    constructor <;> linarith [fine_outer_endpoint_bounds.2,
      outer_endpoint_bounds.2.2.2]
  have hn := norm_identity hd.1 x
  rw [hb] at hn
  have hv := v_positive hd.1 hd.2.1
  have hvlo : (24/25:ℝ)<v B x := by
    have hsq := pow_le_pow_left₀ hz.1 hz.2 2
    have hq := NegativeTwo.Inverse.actual_q_positive hd.1
    nlinarith
  have hp := mul_lt_mul hL hvlo.le (by norm_num : (0:ℝ)<24/25)
    (show 0≤LLabel.d1 outerDiagonal by linarith)
  dsimp [angleFirst]
  rw [hb]
  norm_num at hp
  linarith

lemma domain_angle_positive {B x : ℝ} (hd : Domain B x) : 0<x := by
  by_contra! hn
  have he : x=0 := le_antisymm hn hd.2.1.1
  have hcut := hd.2.2.2
  rw [he] at hcut
  norm_num [b] at hcut
  linarith [hd.1.1,outer_endpoint_bounds.2.2.2]

theorem minimum_target_zero {B x : ℝ} (hd : Domain B x)
    (hmin : ∀C y,Domain C y →
      value LLabel KLabel B x≤value LLabel KLabel C y) : B=0 := by
  by_contra hne
  have hB : 0<B := lt_of_le_of_ne hd.1.1 (Ne.symm hne)
  have htarget : targetFirst LLabel KLabel B x≤0 := by
    have hmax : IsMaxOn (fun C => -value LLabel KLabel C x) (Icc 0 B) B := by
      intro C hC
      have hCi : C∈Icc 0 outerDiagonal := ⟨hC.1,hC.2.trans hd.1.2⟩
      have hbhi : b C x≤b B x := b_target_monotone hd.2.1 hCi hd.1 hC.2
      have hCd : Domain C x := ⟨hCi,hd.2.1,
        ⟨by linarith [b_lower hCi hd.2.1],hbhi.trans hd.2.2.2⟩⟩
      have hh := hmin C x hCd
      change -value LLabel KLabel C x≤ -value LLabel KLabel B x
      linarith
    have hh := not_negative_at_rightward_maximum
      (show B∈Icc 0 B from ⟨hd.1.1,le_rfl⟩) hB hmax
      (value_target_hasDerivAt LLabel KLabel hd).fun_neg
    linarith
  have hangle : 0<angleFirst LLabel B x := by
    by_contra! hn
    have hh := angular_nonpos_target_pos hd hn
    linarith
  have hbstrict : b B x<outerDiagonal := by
    rcases lt_or_eq_of_le hd.2.2.2 with hh | hh
    · exact hh
    · have hn := diagonal_angle_negative hd hh
      linarith
  have hx := domain_angle_positive hd
  let O : Set ℝ := {t | 0<t ∧ b B t<outerDiagonal}
  have hbcont : Continuous (b B) :=
    continuous_iff_continuousAt.2 fun t => (b_angle_hasDerivAt B t).continuousAt
  have hO : IsOpen O := by
    change IsOpen ({t : ℝ | 0<t} ∩ {t : ℝ | b B t<outerDiagonal})
    exact (isOpen_lt continuous_const continuous_id).inter
      (isOpen_lt hbcont continuous_const)
  obtain ⟨ε,hε,hsub⟩ := exists_closed_interval_in_open hO
    (show x∈O from ⟨hx,hbstrict⟩)
  have hmax : IsMaxOn (fun t => -value LLabel KLabel B t) (Icc (x-ε) x) x := by
    intro y hy
    have hyO := hsub (show y∈Icc (x-ε) (x+ε) from
      ⟨hy.1,by linarith [hy.2]⟩)
    have hyi : y∈Icc 0 (7/10) := ⟨hyO.1.le,hy.2.trans hd.2.1.2⟩
    have hyd : Domain B y := ⟨hd.1,hyi,
      ⟨by linarith [b_lower hd.1 hyi],hyO.2.le⟩⟩
    have hh := hmin B y hyd
    change -value LLabel KLabel B y≤ -value LLabel KLabel B x
    linarith
  have hh := not_negative_at_rightward_maximum
    (show x∈Icc (x-ε) x by constructor <;> linarith) (by linarith : x-ε<x)
    hmax (value_angle_hasDerivAt LLabel KLabel hd).fun_neg
  linarith

theorem whole_contact_lower {B x : ℝ} (hd : Domain B x) :
    (89777/100000:ℝ)<value LLabel KLabel B x := by
  let contact : ℝ×ℝ → ℝ := fun p => outerDiagonal-b p.1 p.2
  let cost : ℝ×ℝ → ℝ := fun p => value LLabel KLabel p.1 p.2
  have hc : Continuous contact := by
    dsimp [contact,b,arc]
    fun_prop
  have hf : Continuous cost := by
    dsimp [cost,value,RoleLabel.outer,RoleLabel.eval,b,arc]
    fun_prop
  obtain ⟨p,hp,hsmall,hmin⟩ := contact_region_minimum hc hf
    (p₀ := (B,x)) (show B∈Icc 0 outerDiagonal ∧ x∈Icc 0 (7/10) ∧
      0≤contact (B,x) from ⟨hd.1,hd.2.1,sub_nonneg.mpr hd.2.2.2⟩)
  have hpd : Domain p.1 p.2 := ⟨hp.1,hp.2.1,
    ⟨by linarith [b_lower hp.1 hp.2.1],sub_nonneg.mp hp.2.2⟩⟩
  have hzero := minimum_target_zero hpd (fun C y hCy =>
    hmin (C,y) hCy.1 hCy.2.1 (sub_nonneg.mpr hCy.2.2.2))
  have hl := zero_boundary_lower (show Domain 0 p.2 by simpa [hzero] using hpd)
  change value LLabel KLabel p.1 p.2≤value LLabel KLabel B x at hsmall
  rw [hzero] at hsmall
  exact hl.trans_le hsmall

/-- The literal original source-secondary weak separator pays the L/K
row.  The only replacement is the proved cost-lowering contact. -/
theorem original_primary {a b₀ A B x : ℝ} (hs : OuterState a b₀)
    (ht : OuterState A B) (hx : |x|≤7/10)
    (hm : 0≤Eight.forwardMargin 0 a b₀ A B 1 1 x) :
    (89777/100000:ℝ)<x+LLabel.eval a b₀-KLabel.eval A B := by
  obtain ⟨hd,hcut⟩ := original_contact hs ht hx hm
  have hsource := L_monotone hd.2.2
    (show b₀∈Icc 0 outerDiagonal from ⟨hs.1,(outer_bounds hs).2.2.2.1⟩) hcut
  change LLabel.outer (b B x)≤LLabel.outer b₀ at hsource
  dsimp [RoleLabel.outer] at hsource
  rw [(ShortOuterOne.SameContact.actual_arc hs).1] at hsource
  have hh := whole_contact_lower hd
  dsimp [value,RoleLabel.outer] at hh
  rw [(ShortOuterOne.SameContact.actual_arc ht).1] at hh
  linarith

end SquaresInCircles.Eight.TableFree.SecondWord.SameZero.LK
