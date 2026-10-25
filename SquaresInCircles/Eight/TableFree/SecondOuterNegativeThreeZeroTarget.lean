module

public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeThreeZeroAngle

/-!
# The whole zero-target contact bound

A single strong-concavity reference bounds `T(b)-.72*b` on the first
half of the physical arc.  Convexity of the label derivative and its
actual endpoint values show that the same expression decreases on the
rest.  The affine angle bound then proves a reserve above `.9` for
every original zero-target contact.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.NegativeThree.ZeroTarget

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)

lemma half_mem : (1/2:ℝ)∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem (by norm_num)

lemma half_second : TLabel.d2 (1/2)<(-42/125:ℝ) := by
  have hh := TLabel.second_chart_reference (outer_domain half_mem)
    (l := (683/400:ℝ)) (u := (4269/2500:ℝ))
    (dlo := (-1:ℝ)) (dhi := (-42/125:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [TLabel,W,Q0]) (by norm_num [TLabel,W,Q0])
  exact hh.2

lemma half_first : TLabel.d1 (1/2)<(18/25:ℝ) := by
  have hh := TLabel.first_chart_reference (outer_domain half_mem)
    (l := (683/400:ℝ)) (u := (4269/2500:ℝ))
    (dlo := (0:ℝ)) (dhi := (18/25:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [TLabel,W,Q0]) (by norm_num [TLabel,W,Q0])
  exact hh.2

lemma third_references :
    T (1/3)-(18/25)*(1/3)<(69177/1000000:ℝ) ∧
      |TLabel.d1 (1/3)-18/25|<1/6250 := by
  have hm : (1/3:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  have hu := shifted_chart_reference (outer_domain hm)
    (l := (1794757798577723/1000000000000000:ℝ))
    (u := (448689449644431/250000000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  have hh := FixedReference.target hm ⟨le_rfl,le_rfl⟩ ⟨hu.1.le,hu.2.le⟩
    (by norm_num) (by norm_num)
  norm_num [FixedReference.valueLo,FixedReference.valueHi,FixedReference.firstLo,
    FixedReference.firstHi,FixedReference.secondLo,FixedReference.secondHi,Q0] at hh
  constructor
  · linarith
  · rw [abs_lt]
    constructor <;> linarith

lemma early_label {b : ℝ} (hb : b∈Icc 0 (1/2)) :
    T b-(18/25)*b<(3459/50000:ℝ) := by
  have hdom (t : ℝ) (ht : t∈Icc 0 (1/2)) : t∈Icc 0 outerDiagonal :=
    ⟨ht.1,ht.2.trans half_mem.2⟩
  have hsec (t : ℝ) (ht : t∈Icc 0 (1/2)) : (42/125:ℝ)≤ -TLabel.d2 t := by
    have hm := T_second_monotone (hdom t ht) half_mem ht.2
    linarith [half_second]
  have hval : (18/25-TLabel.d1 (1/3))^2<
      2*(42/125)*(3459/50000-T (1/3)+(18/25)*(1/3)) := by
    have hd := (abs_lt.mp third_references.2)
    have hs : (18/25-TLabel.d1 (1/3))^2<(1/6250:ℝ)^2 := by nlinarith
    nlinarith [third_references.1]
  have hh := positive_of_curvature (f := fun t => 3459/50000-T t+(18/25)*t)
    (d := fun t => 18/25-TLabel.d1 t) (dd := fun t => -TLabel.d2 t)
    (κ := (42/125:ℝ)) (by norm_num) hb
    (show (1/3:ℝ)∈Icc 0 (1/2) by norm_num)
    (fun t ht => (((TLabel.outer_hasDerivAt (outer_domain (hdom t ht))).const_sub
        (3459/50000)).fun_add ((hasDerivAt_id' t).const_mul (18/25))).congr_deriv
        (by ring))
    (fun t ht => (TLabel.d1_hasDerivAt (outer_domain (hdom t ht))).const_sub (18/25))
    hsec hval
  linarith

lemma endpoint_first : TLabel.d1 ZeroAngle.endpoint<(18/25:ℝ) := by
  have hs := ShortOuterOne.SameContact.primary_state primary_one_mem
  have he := primary_first_exchange hs
  change TPrimaryLabel.d1 1*ratio ZeroAngle.endpoint=TLabel.d1 ZeroAngle.endpoint at he
  have hr : ratio ZeroAngle.endpoint<(1291/1500:ℝ) := by
    change W ZeroAngle.endpoint/U ZeroAngle.endpoint<_
    rw [ZeroAngle.endpoint_circle]
    dsimp [W]
    linarith [ZeroAngle.endpoint_bounds.2]
  have hr0 : 0≤ratio ZeroAngle.endpoint :=
    (ShortOuterOne.SameContact.ratio_pos (outer_domain ZeroAngle.endpoint_mem)).le
  have hm := primary_one_references
  have hp := mul_le_mul hm.2.1.le hr.le hr0 (by norm_num : (0:ℝ)≤38723/50000)
  rw [he] at hp
  norm_num at hp
  linarith

lemma late_first {b : ℝ} (hb : b∈Icc (1/2) ZeroAngle.endpoint) :
    TLabel.d1 b<(18/25:ℝ) := by
  have hdom (t : ℝ) (ht : t∈Icc (1/2) ZeroAngle.endpoint) : t∈Icc 0 outerDiagonal :=
    ⟨by linarith [ht.1],ht.2.trans ZeroAngle.endpoint_mem.2⟩
  have hh := positive_of_second_nonpos
    (f := fun t => 18/25-TLabel.d1 t)
    (d := fun t => -TLabel.d2 t) (dd := fun t => -TLabel.d3 t) hb
    (fun t ht => (TLabel.d1_hasDerivAt (outer_domain (hdom t ht))).const_sub (18/25))
    (fun t ht => (TLabel.d2_hasDerivAt (outer_domain (hdom t ht))).neg)
    (fun t ht => by linarith [T_third_lower (hdom t ht)])
    (by linarith [half_first]) (by linarith [endpoint_first])
  linarith

theorem label_bound {b : ℝ} (hb : b∈Icc 0 ZeroAngle.endpoint) :
    T b-(18/25)*b<(3459/50000:ℝ) := by
  rcases le_total b (1/2) with h | h
  · exact early_label ⟨hb.1,h⟩
  · have hdom (t : ℝ) (ht : t∈Icc (1/2) ZeroAngle.endpoint) : t∈Icc 0 outerDiagonal :=
      ⟨by linarith [ht.1],ht.2.trans ZeroAngle.endpoint_mem.2⟩
    have hanti : AntitoneOn (fun t => T t-(18/25)*t) (Icc (1/2) ZeroAngle.endpoint) :=
      antiOn_of_hasDeriv_nonpos
        (fun t ht => ((TLabel.outer_hasDerivAt (outer_domain (hdom t ht))).sub
          ((hasDerivAt_id t).const_mul (18/25))).continuousAt.continuousWithinAt)
        (fun t ht => (TLabel.outer_hasDerivAt (outer_domain (hdom t (Ioo_subset_Icc_self ht)))).sub
          ((hasDerivAt_id t).const_mul (18/25)))
        (fun t ht => by linarith [late_first (Ioo_subset_Icc_self ht)])
    have hm := hanti (show (1/2:ℝ)∈Icc (1/2) ZeroAngle.endpoint from
      ⟨le_rfl,by linarith [ZeroAngle.endpoint_bounds.1]⟩) ⟨h,hb.2⟩ h
    exact hm.trans_lt (early_label (by norm_num))

theorem original_contact {b x : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) (hc : NegativeTwo.TargetContact.B b x=0) :
    (9/10:ℝ)<value b 0 (Real.pi/2-x) := by
  have hr := ZeroAngle.original_source_range hb hx hc
  have ha := ZeroAngle.original_angle hb hx hc
  have hl := label_bound hr
  dsimp [value]
  linarith [pi_hand_enclosure.1,K_zero_bounds.1]

end SquaresInCircles.Eight.TableFree.SecondWord.NegativeThree.ZeroTarget
