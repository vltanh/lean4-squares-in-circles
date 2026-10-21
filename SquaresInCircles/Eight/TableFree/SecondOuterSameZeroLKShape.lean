module

public import SquaresInCircles.Eight.TableFree.SecondOuterSameZeroContact

/-!
# A single endpoint-forcing direction for the L/K contact

Uncompiled source draft.  If the angular derivative can fail to be
positive, the original source lies above .755.  Its exact projection
ratio then exceeds the target label slope on the whole target arc.
Every nonpositive angular derivative therefore has a strictly positive
target derivative.  The split at .2 compares two analytic bounds on
the same circle; no box or sampled contact is a hypothesis.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.SameZero.LK
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)

lemma first_left : LLabel.d1 (293/1000)<(817/1000:ℝ) := by
  have hh := LLabel.first_chart_reference
    (outer_domain (Asymmetric.rational_outer_mem (by norm_num : (293/1000:ℝ)∈Icc 0 (899/1000))))
    (l := (18129398776/10000000000:ℝ)) (u := (18129398777/10000000000:ℝ))
    (dlo := (0:ℝ)) (dhi := (817/1000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [LLabel,W,Q0]) (by norm_num [LLabel,W,Q0])
  exact hh.2

lemma first_right : LLabel.d1 (151/200)<(817/1000:ℝ) := by
  have hh := LLabel.first_chart_reference
    (outer_domain (Asymmetric.rational_outer_mem (by norm_num : (151/200:ℝ)∈Icc 0 (899/1000))))
    (l := (15298937871/10000000000:ℝ)) (u := (15298937872/10000000000:ℝ))
    (dlo := (0:ℝ)) (dhi := (817/1000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [LLabel,W,Q0]) (by norm_num [LLabel,W,Q0])
  exact hh.2

lemma second_right : (167/100:ℝ)<LLabel.d2 (151/200) := by
  have hh := LLabel.second_chart_reference
    (outer_domain (Asymmetric.rational_outer_mem (by norm_num : (151/200:ℝ)∈Icc 0 (899/1000))))
    (l := (15298937871/10000000000:ℝ)) (u := (15298937872/10000000000:ℝ))
    (dlo := (167/100:ℝ)) (dhi := (2:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [LLabel,W,Q0]) (by norm_num [LLabel,W,Q0])
  exact hh.1

lemma target_fifth_first : KLabel.d1 (1/5)<(869/1000:ℝ) := by
  have hh := KLabel.first_chart_reference
    (outer_domain (Asymmetric.rational_outer_mem (by norm_num : (1/5:ℝ)∈Icc 0 (899/1000))))
    (l := (18508376482/10000000000:ℝ)) (u := (18508376483/10000000000:ℝ))
    (dlo := (0:ℝ)) (dhi := (869/1000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [KLabel,W,Q0]) (by norm_num [KLabel,W,Q0])
  exact hh.2

lemma first_middle {y : ℝ} (hy : y∈Icc (293/1000:ℝ) (151/200)) :
    LLabel.d1 y<(817/1000:ℝ) := by
  have hdom : Icc (293/1000:ℝ) (151/200)⊆Icc 0 outerDiagonal := by
    intro z hz
    exact ⟨by linarith [hz.1],by linarith [hz.2,fine_outer_endpoint_bounds.2]⟩
  have hc : ConcaveOn ℝ (Icc (293/1000:ℝ) (151/200)) (fun y => -LLabel.d1 y) :=
    concave_of_deriv2
      (fun z hz => (LLabel.d1_hasDerivAt (outer_domain (hdom hz))).neg)
      (fun z hz => (LLabel.d2_hasDerivAt (outer_domain (hdom hz))).neg)
      (fun z hz => neg_nonpos.mpr (L_third_positive (hdom hz)).le)
  have hh := concave_gt_of_endpoints hc hy
    (show -(817/1000:ℝ)< -LLabel.d1 (293/1000) by linarith [first_left])
    (show -(817/1000:ℝ)< -LLabel.d1 (151/200) by linarith [first_right])
  linarith

lemma angular_nonpos_large {B x : ℝ} (hd : Domain B x)
    (hangle : angleFirst LLabel B x≤0) : (151/200:ℝ)<b B x := by
  by_contra! hsmall
  have hp := first_middle ⟨(b_lower hd.1 hd.2.1).le,hsmall⟩
  have hv := v_upper hd.1 hd.2.1
  have hprod := mul_lt_mul hp hv (v_positive hd.1 hd.2.1)
    (by norm_num : (0:ℝ)≤817/1000)
  dsimp [angleFirst] at hangle
  norm_num at hprod
  linarith

lemma factor_lower {u : ℝ} (hu : 0<u) (hq : 0<NegativeTwo.Inverse.q u) :
    (21/25:ℝ)<NegativeTwo.Inverse.factor u := by
  apply (lt_div_iff₀ (mul_pos hu hq)).2
  have he : Q0-u-(21/25)*u*NegativeTwo.Inverse.q u=
      (42/25)*(u-320569/210000)^2+20016239/26250000000 := by
    norm_num [Q0,NegativeTwo.Inverse.q]
    ring
  nlinarith [sq_nonneg (u-320569/210000)]

lemma projection_early {B x : ℝ} (hd : Domain B x) (hB : B≤1/5)
    (hb : (151/200:ℝ)<b B x) : (116/125:ℝ)<k B x/v B x := by
  have hu := U_positive (outer_domain hd.1)
  have hq : 0<NegativeTwo.Inverse.q (U B) := by
    linarith [NegativeTwo.Inverse.actual_q_positive hd.1]
  have hv := v_positive hd.1 hd.2.1
  have hU : (37/20:ℝ)<U B := by
    have hc := UW_circle (outer_domain hd.1)
    have hw : (W B)^2≤(7/10:ℝ)^2 := by dsimp [W]; nlinarith [hd.1.1]
    norm_num [Q0] at hc
    nlinarith
  have hUhi := (UW_bounds hd.1).2.1
  have hqhi : NegativeTwo.Inverse.q (U B)<(3039/2500:ℝ) := by
    norm_num [NegativeTwo.Inverse.q,Q0]
    linarith
  have hden : U B*NegativeTwo.Inverse.q (U B)≤(37/20)*(3039/2500) := by
    have hh := mul_nonneg (show 0≤U B-37/20 by linarith)
      (show 0≤2*U B+37/10-(Q0+1) by norm_num [Q0]; linarith)
    norm_num [NegativeTwo.Inverse.q,Q0] at *
    nlinarith
  have hfirst : (889/1000:ℝ)<NegativeTwo.Inverse.factor (U B) := by
    apply (lt_div_iff₀ (mul_pos hu hq)).2
    norm_num [Q0] at hden ⊢
    nlinarith
  have hvhi : v B x<(1103/1000:ℝ) := by
    have hn := norm_identity hd.1 x
    nlinarith [sq_nonneg (b B x-1/2)]
  have hden2 := mul_lt_mul
    (mul_lt_mul hUhi hqhi hq (by norm_num : (0:ℝ)≤383/200)) hvhi hv
    (by norm_num : (0:ℝ)≤(383/200)*(3039/2500))
  have hnum : (1/2)*(51/200)<W B*(b B x-1/2) := by
    have hh := mul_nonneg (show 0≤W B-1/2 by dsimp [W]; linarith [hd.1.1])
      (show 0≤b B x-1/2 by linarith)
    nlinarith
  have hsecond : (39/1000:ℝ)<W B*(b B x-1/2)/
      (U B*NegativeTwo.Inverse.q (U B)*v B x) := by
    apply (lt_div_iff₀ (mul_pos (mul_pos hu hq) hv)).2
    nlinarith
  rw [projection_identity hd.1 hd.2.1]
  linarith

lemma projection_late {B x : ℝ} (hd : Domain B x) (hB : 1/5≤B)
    (hb : (151/200:ℝ)<b B x) : (869/1000:ℝ)<k B x/v B x := by
  have hu := U_positive (outer_domain hd.1)
  have hq : 0<NegativeTwo.Inverse.q (U B) := by
    linarith [NegativeTwo.Inverse.actual_q_positive hd.1]
  have hv := v_positive hd.1 hd.2.1
  have hUhi := (UW_bounds hd.1).2.1
  have hqhi : NegativeTwo.Inverse.q (U B)<(1059/500:ℝ) := by
    have hu := (UW_bounds hd.1).1
    norm_num [NegativeTwo.Inverse.q,Q0]
    linarith
  have hvhi := v_upper hd.1 hd.2.1
  have hden := mul_lt_mul
    (mul_lt_mul hUhi hqhi hq (by norm_num : (0:ℝ)≤383/200)) hvhi hv
    (by norm_num : (0:ℝ)≤(383/200)*(1059/500))
  have hnum : (7/10)*(51/200)<W B*(b B x-1/2) := by
    have hh := mul_nonneg (show 0≤W B-7/10 by dsimp [W]; linarith)
      (show 0≤b B x-1/2 by linarith)
    nlinarith
  have hsecond : (29/1000:ℝ)<W B*(b B x-1/2)/
      (U B*NegativeTwo.Inverse.q (U B)*v B x) := by
    apply (lt_div_iff₀ (mul_pos (mul_pos hu hq) hv)).2
    nlinarith
  rw [projection_identity hd.1 hd.2.1]
  linarith [factor_lower hu hq]

theorem angular_nonpos_target_pos {B x : ℝ} (hd : Domain B x)
    (hangle : angleFirst LLabel B x≤0) : 0<targetFirst LLabel KLabel B x := by
  have hb := angular_nonpos_large hd hangle
  have hv := v_positive hd.1 hd.2.1
  have hk := k_positive hd.1 hd.2.1
  have hpaid : k B x/v B x≤LLabel.d1 (b B x)*k B x := by
    apply (div_le_iff₀ hv).2
    have hh := mul_nonneg hk.le (show 0≤LLabel.d1 (b B x)*v B x-1 by
      dsimp [angleFirst] at hangle; linarith)
    nlinarith
  have hgap : KLabel.d1 B<k B x/v B x := by
    rcases le_total B (1/5) with he | hl
    · exact (K_first_bounds hd.1).2.trans (projection_early hd he hb)
    · have hf := K_first_antitone (Asymmetric.rational_outer_mem
        (by norm_num : (1/5:ℝ)∈Icc 0 (899/1000))) hd.1 hl
      exact (hf.trans_lt target_fifth_first).trans (projection_late hd hl hb)
  dsimp [targetFirst]
  linarith

end SquaresInCircles.Eight.TableFree.SecondWord.SameZero.LK
