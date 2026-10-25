module

public import SquaresInCircles.Eight.TableFree.SecondOuterSameZeroPJDiagonalGeometry

/-!
# The complete P/J source-diagonal boundary

Uncompiled source draft.  The polynomial estimate bounds B''/(B')²
by 1/4 on the whole physical branch.  The original J bounds give
curvature greater than 1/30, so the one rational reference supplies
the asserted strict reserve everywhere on the branch.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.SameZero.PJ.Diagonal
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (ratio)

lemma acceleration_bound {x : ℝ} (hx : Domain x) :
    acceleration x<(speed x)^2/4 := by
  let u := U (height x)
  let r := ratio (height x)
  let w := v (height x) x
  have hd := contact_domain hx
  have hu : u∈Icc (33/20:ℝ) (383/200) := by
    dsimp [u]
    rw [(actual_coordinates hx).1]
    exact ⟨(whole_bounds hx.1).1.le,(whole_bounds hx.1).2.1.le⟩
  have hup : 0<u := U_positive (outer_domain hd.1)
  have hrp : 0<r := ShortOuterOne.SameContact.ratio_pos (outer_domain hd.1)
  have hw : 0<w := v_positive hd.1 hd.2.1
  have hq : 0<NegativeTwo.Inverse.q u := by
    linarith [NegativeTwo.Inverse.actual_q_positive hd.1]
  have hz : z₀∈Icc (0:ℝ) (2/5) := by
    dsimp [z₀]
    constructor <;> linarith [diagonal_fine.1,diagonal_fine.2]
  have hrc : r^2*u^2=Q0-u^2 := by
    have hh := UW_circle (outer_domain hd.1)
    have hru : r*u=W (height x) := by
      have h0 : U (height x)≠0 := hup.ne'
      dsimp only [r,u]
      rw [show ratio (height x)=W (height x)/U (height x) from rfl]
      field_simp
    have hsq : r^2*u^2=(r*u)^2 := by ring
    rw [hsq,hru]
    dsimp only [u]
    linarith
  have hn : z₀^2+w^2=NegativeTwo.Inverse.q u := by
    have hh := norm_identity hd.1 x
    rw [contact hx] at hh
    exact hh
  have hbrace := inverse_brace_positive hu hrc hz hw hn
  have hlog := logarithmic_height_bound hu hrp.le hrc
  have hfac : 0<NegativeTwo.Inverse.factor u := by
    dsimp [NegativeTwo.Inverse.factor]
    apply div_pos _ (mul_pos hup hq)
    norm_num [Q0]
    linarith [hu.2]
  have hfirst : NegativeTwo.Inverse.factor u < inverseFirst x := by
    dsimp [inverseFirst]
    have hz0 : 0<z₀ := by dsimp [z₀]; linarith [diagonal_fine.1]
    have hp := div_pos (mul_pos hz0 hrp) (mul_pos hq hw)
    linarith
  have hsecond : -r*NegativeTwo.Inverse.factorD u < inverseSecond x := by
    have hz0 : 0<z₀ := by dsimp [z₀]; linarith [diagonal_fine.1]
    have hp := mul_pos (div_pos hz0 (mul_pos hq hw)) hbrace
    dsimp [inverseSecond,PJCritical.inverseTarget,PJCritical.heightFactorD]
    linarith
  have hif : 0 < inverseFirst x := hfac.trans hfirst
  have hratio : -inverseFirst x/4 < inverseSecond x := by linarith
  have hs : 0<speed x := by linarith [(whole_bounds hx.1).2.2.1]
  have hm := mul_lt_mul_of_pos_right hratio (sq_pos_of_pos hs)
  have hid := inverse_second_identity hx
  have hproduct : inverseFirst x*(acceleration x-(speed x)^2/4)<0 := by nlinarith
  exact lt_of_sub_neg (neg_of_mul_neg_right hproduct hif.le)

lemma curvature {x : ℝ} (hx : Domain x) : (1/30:ℝ)<second x := by
  have htarget := target_mem hx
  have hJ := J_first_bounds htarget
  have hJ2 := J_second_upper htarget
  have hspeed := (whole_bounds hx.1).2.2.1
  have hp : 0<JLabel.d1 (height x) := by linarith [hJ.1]
  have h1 := mul_lt_mul_of_pos_left (acceleration_bound hx) hp
  have h2 := mul_le_mul_of_nonneg_right hJ.2.le
    (div_nonneg (sq_nonneg (speed x)) (by norm_num : (0:ℝ)≤4))
  have h3 := mul_lt_mul_of_pos_right hJ2 (sq_pos_of_pos (by linarith : 0<speed x))
  dsimp [second]
  nlinarith

lemma cost_hasDerivAt {x : ℝ} (hx : Domain x) : HasDerivAt cost (first x) x := by
  have hd : HasDerivAt (fun t => t+PLabel.outer outerDiagonal-JLabel.outer (height t))
      (1-JLabel.d1 (height x)*speed x) x :=
    (((hasDerivAt_id x).add_const (PLabel.outer outerDiagonal)).sub
      ((JLabel.outer_hasDerivAt (outer_domain (target_mem hx))).comp x
        (height_hasDerivAt hx.1))).congr_deriv (by simp)
  exact hd

lemma first_hasDerivAt {x : ℝ} (hx : Domain x) : HasDerivAt first (second x) x := by
  have hd : HasDerivAt (fun t => 1-JLabel.d1 (height t)*speed t)
      (-(JLabel.d2 (height x)*speed x*speed x+JLabel.d1 (height x)*acceleration x)) x :=
    (((JLabel.d1_hasDerivAt (outer_domain (target_mem hx))).comp x
      (height_hasDerivAt hx.1)).fun_mul (speed_hasDerivAt hx.1)).const_sub 1
  exact hd.congr_deriv (by simp only [second]; ring)

theorem lower {x : ℝ} (hx : Domain x) : (89777/100000:ℝ)<cost x := by
  let r := Reference.diagonalReference
  let l := min x r
  let u := max x r
  have hr := Reference.diagonal_reference
  have hX : x∈Icc l u := ⟨min_le_left _ _,le_max_left _ _⟩
  have hR : r∈Icc l u := ⟨min_le_right _ _,le_max_right _ _⟩
  have hdom : ∀t∈Icc l u,Domain t := by
    intro t ht
    have hti : t∈Icc start (7/10) :=
      ⟨(le_min hx.1.1 hr.1.1.1).trans ht.1,ht.2.trans (max_le hx.1.2 hr.1.1.2)⟩
    refine ⟨hti,?_⟩
    rcases le_total x r with he | he
    · have hxt : x≤t := by simpa [l,min_eq_left he] using ht.1
      exact hx.2.trans (height_monotone hx.1 hti hxt)
    · have hrt : r≤t := by simpa [l,min_eq_right he] using ht.1
      exact hr.1.2.trans (height_monotone hr.1.1 hti hrt)
  have hh := curvature_tangent (f := cost) (d := first) (dd := second)
    (κ := (1/30:ℝ)) hX hR
    (fun t ht => cost_hasDerivAt (hdom t ht))
    (fun t ht => first_hasDerivAt (hdom t ht))
    (fun t ht => (curvature (hdom t ht)).le)
  have hs := abs_lt.mp hr.2.2
  have hsquare := sq_nonneg ((x-r)/30+first r)
  have hsmall : (first r)^2<(1/1000000:ℝ)^2 := by nlinarith
  nlinarith [hr.2.1]

theorem original_lower {B x : ℝ} (hd : SameZero.Domain B x)
    (he : b B x=outerDiagonal) : (89777/100000:ℝ)<value PLabel JLabel B x := by
  obtain ⟨hx,hB⟩ := original_coordinates hd he
  have hh := lower hx
  dsimp [cost] at hh
  rw [hB] at hh
  simpa [value,he] using hh

end SquaresInCircles.Eight.TableFree.SecondWord.SameZero.PJ.Diagonal
