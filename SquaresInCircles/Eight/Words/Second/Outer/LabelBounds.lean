module

public import Mathlib.Tactic
public import SquaresInCircles.Common.Analysis
public import SquaresInCircles.Eight.Words.Second.WordData
public import SquaresInCircles.Eight.Words.Short.Outer.Zero.PositivePrimary

/-!
# Eight squares: whole-arc derivative bounds for the edge-two outer labels

The source label is convex and has increasing curvature.  The target
label is increasing and strictly concave, with decreasing curvature.
Every bound follows on the entire physical outer arc from its circle
equation and the two circle endpoints.
-/

section
/-!
## Endpoint minima from an increasing second derivative

If the first derivative is convex and negative at the right endpoint,
the value cannot have an interior minimum below both endpoint values.
The proof splits on the actual derivative at the queried point and
uses monotonicity on the resulting two subintervals.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.MinimumCalculus

theorem endpoint_minimum {f d dd ddd : ℝ→ℝ} {l u x : ℝ}
    (hx : x∈Icc l u)
    (hf : ∀ t∈Icc l u, HasDerivAt f (d t) t)
    (hd : ∀ t∈Icc l u, HasDerivAt d (dd t) t)
    (hdd : ∀ t∈Icc l u, HasDerivAt dd (ddd t) t)
    (hthird : ∀ t∈Icc l u, 0≤ddd t)
    (hright : d u<0) : min (f l) (f u)≤f x := by
  have hmono : MonotoneOn dd (Icc l u) := monoOn_of_hasDeriv_nonneg
    (fun t ht => (hdd t ht).continuousAt.continuousWithinAt)
    (fun t ht => hdd t (Ioo_subset_Icc_self ht))
    (fun t ht => hthird t (Ioo_subset_Icc_self ht))
  have hconcave : ConcaveOn ℝ (Icc l u) (fun t => -d t) :=
    concave_of_deriv2
      (fun t ht => (hd t ht).neg)
      (fun t ht => (hdd t ht).neg)
      (fun t ht => neg_nonpos.mpr (hthird t ht))
  by_cases hdx : d x≤0
  · have hdom {t : ℝ} (ht : t∈Icc x u) : t∈Icc l u :=
      ⟨hx.1.trans ht.1,ht.2⟩
    have hdnegative {t : ℝ} (ht : t∈Icc x u) : d t≤0 := by
      have hm := hconcave.min_le_of_mem_Icc hx ⟨hx.1.trans hx.2,le_rfl⟩ ht
      have hmin : 0≤min (-d x) (-d u) := by
        exact le_min (neg_nonneg.mpr hdx) (neg_nonneg.mpr hright.le)
      linarith
    have hanti : AntitoneOn f (Icc x u) := antiOn_of_hasDeriv_nonpos
      (fun t ht => (hf t (hdom ht)).continuousAt.continuousWithinAt)
      (fun t ht => hf t (hdom (Ioo_subset_Icc_self ht)))
      (fun t ht => hdnegative (Ioo_subset_Icc_self ht))
    exact (min_le_right _ _).trans
      (hanti ⟨le_rfl,hx.2⟩ ⟨hx.2,le_rfl⟩ hx.2)
  · have hdpositive : 0<d x := lt_of_not_ge hdx
    have hddnegative : dd x<0 := by
      by_contra hbad
      have hnonneg : 0≤dd x := le_of_not_gt hbad
      have hdom {t : ℝ} (ht : t∈Icc x u) : t∈Icc l u :=
        ⟨hx.1.trans ht.1,ht.2⟩
      have hM : MonotoneOn d (Icc x u) := monoOn_of_hasDeriv_nonneg
        (fun t ht => (hd t (hdom ht)).continuousAt.continuousWithinAt)
        (fun t ht => hd t (hdom (Ioo_subset_Icc_self ht)))
        (fun t ht => hnonneg.trans (hmono hx (hdom (Ioo_subset_Icc_self ht)) ht.1.le))
      have hh := hM ⟨le_rfl,hx.2⟩ ⟨hx.2,le_rfl⟩ hx.2
      linarith
    have hdom {t : ℝ} (ht : t∈Icc l x) : t∈Icc l u :=
      ⟨ht.1,ht.2.trans hx.2⟩
    have hanti : AntitoneOn d (Icc l x) := antiOn_of_hasDeriv_nonpos
      (fun t ht => (hd t (hdom ht)).continuousAt.continuousWithinAt)
      (fun t ht => hd t (hdom (Ioo_subset_Icc_self ht)))
      (fun t ht => (hmono (hdom (Ioo_subset_Icc_self ht)) hx ht.2.le).trans hddnegative.le)
    have hM : MonotoneOn f (Icc l x) := monoOn_of_hasDeriv_nonneg
      (fun t ht => (hf t (hdom ht)).continuousAt.continuousWithinAt)
      (fun t ht => hf t (hdom (Ioo_subset_Icc_self ht)))
      (fun t ht => hdpositive.le.trans
        (hanti (Ioo_subset_Icc_self ht) ⟨hx.1,le_rfl⟩ ht.2.le))
    exact (min_le_left _ _).trans
      (hM ⟨le_rfl,hx.1⟩ ⟨hx.1,le_rfl⟩ hx.1)

end SquaresInCircles.Eight.SecondWord.MinimumCalculus
end
end
end

section
/-!
## Endpoint minima from a concave first derivative

Reflection of the increasing-curvature endpoint lemma proves the dual
statement: a concave first derivative that is positive at the left
endpoint permits no value below both endpoint values.  The derivatives
of the reflected function are supplied explicitly.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.MinimumCalculus

theorem endpoint_minimum_of_third_nonpos {f d dd ddd : ℝ→ℝ} {l u x : ℝ}
    (hx : x∈Icc l u)
    (hf : ∀ t∈Icc l u, HasDerivAt f (d t) t)
    (hd : ∀ t∈Icc l u, HasDerivAt d (dd t) t)
    (hdd : ∀ t∈Icc l u, HasDerivAt dd (ddd t) t)
    (hthird : ∀ t∈Icc l u, ddd t≤0)
    (hleft : 0<d l) : min (f l) (f u)≤f x := by
  have hdom (t : ℝ) (ht : t∈Icc (-u) (-l)) : -t∈Icc l u := by
    constructor <;> linarith [ht.1,ht.2]
  have hfr (t : ℝ) (ht : t∈Icc (-u) (-l)) :
      HasDerivAt (fun s => f (-s)) (-d (-t)) t := by
    have h : HasDerivAt (fun s => f (-s)) (d (-t)*(-1)) t :=
      (hf (-t) (hdom t ht)).comp t (hasDerivAt_neg t)
    convert h using 1
    ring
  have hdr (t : ℝ) (ht : t∈Icc (-u) (-l)) :
      HasDerivAt (fun s => -d (-s)) (dd (-t)) t := by
    have h : HasDerivAt (fun s => -d (-s)) (-(dd (-t)*(-1))) t :=
      ((hd (-t) (hdom t ht)).comp t (hasDerivAt_neg t)).neg
    convert h using 1
    ring
  have hddr (t : ℝ) (ht : t∈Icc (-u) (-l)) :
      HasDerivAt (fun s => dd (-s)) (-ddd (-t)) t := by
    have h : HasDerivAt (fun s => dd (-s)) (ddd (-t)*(-1)) t :=
      (hdd (-t) (hdom t ht)).comp t (hasDerivAt_neg t)
    convert h using 1
    ring
  have hh := endpoint_minimum (show -x∈Icc (-u) (-l) by
      constructor <;> linarith [hx.1,hx.2]) hfr hdr hddr
    (fun t ht => neg_nonneg.mpr (hthird (-t) (hdom t ht)))
    (show -d (-(-l))<0 by simpa only [neg_neg] using neg_neg_of_pos hleft)
  simpa only [neg_neg,min_comm] using hh

end SquaresInCircles.Eight.SecondWord.MinimumCalculus
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)

lemma ratioDD_positive {b : ℝ} (hb : b∈Icc 0 outerDiagonal) : 0<ratioDD b := by
  have hu := U_positive (outer_domain hb)
  change 0<3*Q0*W b/(U b)^5
  exact div_pos (mul_pos (by norm_num [Q0])
    (by dsimp [W]; linarith [hb.1])) (pow_pos hu 5)

lemma ratioDD_formula {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    ratioDD b=(3*W b/(U b)^2)*ratioD b := by
  have hu := U_positive (outer_domain hb)
  have hu0 : U b≠0 := hu.ne'
  rw [show ratioDD b=3*Q0*(W b)/(U b)^5 from rfl,show ratioD b=Q0/(U b)^3 from rfl]
  field_simp

lemma ratioDD_upper {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    ratioDD b<3*ratioD b := by
  have hu := U_positive (outer_domain hb)
  have hd := ShortOuterOne.SameContact.ratioD_pos (outer_domain hb)
  have hbounds := UW_bounds hb
  have hquot : 3*W b/(U b)^2<3 := by
    apply (div_lt_iff₀ (sq_pos_of_pos hu)).2
    nlinarith [hbounds.1,hbounds.2.2.2]
  rw [ratioDD_formula hb]
  exact mul_lt_mul_of_pos_right hquot hd

lemma P_second_positive {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    0<PLabel.d2 b := by
  have hr := ShortOuterOne.SameContact.ratio_pos (outer_domain hb)
  have hd := ShortOuterOne.SameContact.ratioD_pos (outer_domain hb)
  have hm := mul_nonneg hb.1 hd.le
  norm_num [RoleLabel.d2,PLabel]
  nlinarith

lemma P_third_positive {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    0<PLabel.d3 b := by
  have hd := ShortOuterOne.SameContact.ratioD_pos (outer_domain hb)
  have hh := ratioDD_positive hb
  have hm := mul_nonneg hb.1 hh.le
  norm_num [RoleLabel.d3,PLabel]
  nlinarith

lemma P_second_monotone : MonotoneOn PLabel.d2 (Icc 0 outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun _ hb => (PLabel.d2_hasDerivAt (outer_domain hb)).continuousAt.continuousWithinAt)
    (fun _ hb => PLabel.d2_hasDerivAt (outer_domain (Ioo_subset_Icc_self hb)))
    (fun _ hb => (P_third_positive (Ioo_subset_Icc_self hb)).le)

lemma P_first_monotone : MonotoneOn PLabel.d1 (Icc 0 outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun _ hb => (PLabel.d1_hasDerivAt (outer_domain hb)).continuousAt.continuousWithinAt)
    (fun _ hb => PLabel.d1_hasDerivAt (outer_domain (Ioo_subset_Icc_self hb)))
    (fun _ hb => (P_second_positive (Ioo_subset_Icc_self hb)).le)

lemma P_first_zero_bounds : (773/1000:ℝ)<PLabel.d1 0 ∧ PLabel.d1 0<387/500 := by
  norm_num [RoleLabel.d1,PLabel,ShortOuterOne.SameContact.arc_zero]
  constructor <;> linarith [outer_endpoint_bounds.2.1,ShortOuterZero.fine_axial_bounds.1]

lemma ratio_diagonal : ratio outerDiagonal=1 := by
  have hp : outerDiagonal+1/2≠0 := by linarith [outer_endpoint_bounds.2.2.1]
  rw [show ratio outerDiagonal=(outerDiagonal+1/2)/(arc outerDiagonal+1/2) from rfl,
    ShortOuterOne.SameContact.arc_diagonal]
  exact div_self hp

lemma P_first_diagonal : PLabel.d1 outerDiagonal=
    18603/20000+(2363/50000)*outerDiagonal := by
  rw [RoleLabel.d1,ShortOuterOne.SameContact.arc_diagonal,ratio_diagonal]
  simp only [PLabel]
  ring

lemma P_first_bounds {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    (773/1000:ℝ)<PLabel.d1 b ∧ PLabel.d1 b<973/1000 := by
  have hlo := P_first_monotone outer_zero_mem hb hb.1
  have hhi := P_first_monotone hb
    (show outerDiagonal∈Icc 0 outerDiagonal from ⟨outer_zero_mem.2,le_rfl⟩) hb.2
  rw [P_first_diagonal] at hhi
  exact ⟨P_first_zero_bounds.1.trans_le hlo,
    by linarith [hhi,outer_endpoint_bounds.2.2.2]⟩

lemma P_monotone : MonotoneOn P (Icc 0 outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun b hb => (PLabel.outer_hasDerivAt (outer_domain hb)).continuousAt.continuousWithinAt)
    (fun b hb => PLabel.outer_hasDerivAt (outer_domain (Ioo_subset_Icc_self hb)))
    (fun b hb => by linarith [(P_first_bounds (Ioo_subset_Icc_self hb)).1])

lemma V_third_negative {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    VLabel.d3 b<0 := by
  have hd := ShortOuterOne.SameContact.ratioD_pos (outer_domain hb)
  have hp := ratioDD_positive hb
  have hu := ratioDD_upper hb
  have hm := mul_nonneg hb.1 hp.le
  norm_num [RoleLabel.d3,VLabel]
  nlinarith

lemma V_second_antitone : AntitoneOn VLabel.d2 (Icc 0 outerDiagonal) :=
  antiOn_of_hasDeriv_nonpos
    (fun _ hb => (VLabel.d2_hasDerivAt (outer_domain hb)).continuousAt.continuousWithinAt)
    (fun _ hb => VLabel.d2_hasDerivAt (outer_domain (Ioo_subset_Icc_self hb)))
    (fun _ hb => (V_third_negative (Ioo_subset_Icc_self hb)).le)

lemma zero_ratio_upper : ratio 0<131/500 := by
  have hu := U_positive (outer_domain outer_zero_mem)
  change (0+1/2:ℝ)/U 0<131/500
  apply (div_lt_iff₀ hu).2
  norm_num [U,ShortOuterOne.SameContact.arc_zero]
  linarith [ShortOuterZero.fine_axial_bounds.1]

lemma zero_ratioD_upper : ratioD 0<14/25 := by
  have hu := U_positive (outer_domain outer_zero_mem)
  have hlo : (1914/1000:ℝ)<U 0 := by
    norm_num [U,ShortOuterOne.SameContact.arc_zero]
    linarith [ShortOuterZero.fine_axial_bounds.1]
  have hcube := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1914/1000) hlo.le 3
  change Q0/(U 0)^3<14/25
  apply (div_lt_iff₀ (pow_pos hu 3)).2
  norm_num [Q0]
  nlinarith

lemma V_second_zero : VLabel.d2 0< -(13/40:ℝ) := by
  have hr := (outer_ratio_bounds outer_zero_mem).1
  have hd := zero_ratioD_upper
  norm_num [RoleLabel.d2,VLabel]
  linarith

lemma V_second_upper {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    VLabel.d2 b< -(13/40:ℝ) :=
  (V_second_antitone outer_zero_mem hb hb.1).trans_lt V_second_zero

lemma V_first_antitone : AntitoneOn VLabel.d1 (Icc 0 outerDiagonal) :=
  antiOn_of_hasDeriv_nonpos
    (fun b hb => (VLabel.d1_hasDerivAt (outer_domain hb)).continuousAt.continuousWithinAt)
    (fun b hb => VLabel.d1_hasDerivAt (outer_domain (Ioo_subset_Icc_self hb)))
    (fun b hb => by linarith [V_second_upper (Ioo_subset_Icc_self hb)])

lemma V_first_diagonal : VLabel.d1 outerDiagonal=(1066/6250:ℝ) := by
  rw [RoleLabel.d1,ShortOuterOne.SameContact.arc_diagonal,ratio_diagonal]
  simp only [VLabel]
  ring

lemma V_first_zero : VLabel.d1 0<1061/1000 := by
  have ha := outer_endpoint_bounds.2.1
  have hr := zero_ratio_upper
  norm_num [RoleLabel.d1,VLabel,ShortOuterOne.SameContact.arc_zero]
  linarith

lemma V_first_bounds {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    (1066/6250:ℝ)≤VLabel.d1 b ∧ VLabel.d1 b<1061/1000 := by
  have hlo := V_first_antitone hb
    (show outerDiagonal∈Icc 0 outerDiagonal from ⟨outer_zero_mem.2,le_rfl⟩) hb.2
  rw [V_first_diagonal] at hlo
  exact ⟨hlo,(V_first_antitone outer_zero_mem hb hb.1).trans_lt V_first_zero⟩

lemma V_first_upper {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    VLabel.d1 b<1061/1000 := (V_first_bounds hb).2

lemma V_monotone : MonotoneOn V (Icc 0 outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun b hb => (VLabel.outer_hasDerivAt (outer_domain hb)).continuousAt.continuousWithinAt)
    (fun b hb => VLabel.outer_hasDerivAt (outer_domain (Ioo_subset_Icc_self hb)))
    (fun b hb => by linarith [(V_first_bounds (Ioo_subset_Icc_self hb)).1])

end SquaresInCircles.Eight.SecondWord
end
end
end
