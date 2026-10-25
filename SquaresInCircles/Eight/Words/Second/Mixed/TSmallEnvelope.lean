module

public import SquaresInCircles.Eight.Words.Second.Mixed.TEnvelope

/-!
# Eight squares: the sharper T envelope on the whole initial physical arc

One tangent parabola at .53362 proves the line through .6.  On the
remaining entire interval to .7, the derivative shape reduces the
minimum of the affine difference to its two endpoints.  The two
additional tangents are also global on the whole concave arc to .6.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedTSmall
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

def q : ℝ := 31/50
abbrev k := MixedTEnvelope.k
def reference : ℝ := 26681/50000
def difference (b : ℝ) : ℝ := q*b-T b

lemma reference_mem : reference∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem (by norm_num [reference])

lemma reference_bounds : T reference<(441739/1000000:ℝ) ∧
    |TLabel.d1 reference-q|<(1/100000:ℝ) := by
  have hr := shifted_chart_reference (outer_domain reference_mem)
    (l := (16873736087/10000000000:ℝ)) (u := (2109217011/1250000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [reference,W,Q0]) (by norm_num [reference,W,Q0])
  have hd := TLabel.first_chart_reference (outer_domain reference_mem)
    (l := (16873736087/10000000000:ℝ)) (u := (2109217011/1250000000:ℝ))
    (dlo := (61999/100000:ℝ)) (dhi := (62001/100000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [reference,W,Q0]) (by norm_num [reference,W,Q0])
    (by norm_num [reference,TLabel,W,Q0]) (by norm_num [reference,TLabel,W,Q0])
  constructor
  · dsimp [T,RoleLabel.outer,RoleLabel.eval,TLabel,reference]
    dsimp [U,reference] at hr
    nlinarith [hr.1]
  · rw [abs_lt]
    norm_num [q]
    constructor <;> linarith [hd.1,hd.2]

lemma difference_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt difference (q-TLabel.d1 b) b :=
  TLabel.affine_difference_hasDerivAt q (outer_domain hb)

lemma early {b : ℝ} (hb : b∈Icc (0:ℝ) (3/5)) : -k<difference b := by
  have hdom (x : ℝ) (hx : x∈Icc (0:ℝ) (3/5)) : x∈Icc 0 outerDiagonal :=
    ⟨hx.1,hx.2.trans T_six_mem.2⟩
  have ht := curvature_tangent (f := difference) (d := fun x => q-TLabel.d1 x)
    (dd := fun x => -TLabel.d2 x) (κ := (6/125:ℝ)) hb
    (show reference∈Icc (0:ℝ) (3/5) by norm_num [reference])
    (fun x hx => difference_hasDerivAt (hdom x hx))
    (fun x hx => (TLabel.d1_hasDerivAt (outer_domain (hdom x hx))).const_sub q)
    (fun x hx => by
      have hm := T_second_monotone (hdom x hx) T_six_mem hx.2
      linarith [T_six_second.2])
  have hd := abs_lt.mp reference_bounds.2
  have hs : (q-TLabel.d1 reference)^2<(1/100000:ℝ)^2 := by nlinarith
  have hp := sq_nonneg ((6/125)*(b-reference)+(q-TLabel.d1 reference))
  have hT := reference_bounds.1
  dsimp [difference,q,k,MixedTEnvelope.k,reference] at *
  nlinarith

lemma seven_mem : (7/10:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)

lemma seven_value : T (7/10)<(27191/50000:ℝ) := by
  have hh := shifted_chart_reference (outer_domain seven_mem)
    (l := (7867/5000:ℝ)) (u := (3147/2000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  dsimp [U] at hh
  norm_num [T,RoleLabel.outer,RoleLabel.eval,TLabel]
  nlinarith [hh.1]

theorem upper {b : ℝ} (hb : b∈Icc (0:ℝ) (7/10)) : T b<k+q*b := by
  have hdom (x : ℝ) (hx : x∈Icc (3/5:ℝ) (7/10)) : x∈Icc 0 outerDiagonal :=
    ⟨by linarith [hx.1],hx.2.trans seven_mem.2⟩
  have hh : -k<difference b := by
    by_cases he : b≤3/5
    · exact early ⟨hb.1,he⟩
    · have hm := MinimumCalculus.endpoint_minimum_of_third_nonpos
        (f := difference) (d := fun x => q-TLabel.d1 x)
        (dd := fun x => -TLabel.d2 x) (ddd := fun x => -TLabel.d3 x)
        (show b∈Icc (3/5:ℝ) (7/10) from ⟨by linarith,hb.2⟩)
        (fun x hx => difference_hasDerivAt (hdom x hx))
        (fun x hx => (TLabel.d1_hasDerivAt (outer_domain (hdom x hx))).const_sub q)
        (fun x hx => (TLabel.d2_hasDerivAt (outer_domain (hdom x hx))).neg)
        (fun x hx => by linarith [T_third_lower (hdom x hx)])
        (by norm_num [q]; linarith [T_six_first.2])
      have hl := early (show (3/5:ℝ)∈Icc (0:ℝ) (3/5) by norm_num)
      have hr : -k<difference (7/10) := by
        dsimp [difference,q,k,MixedTEnvelope.k]
        linarith [seven_value]
      exact (lt_min hl hr).trans_le hm
  dsimp [difference] at hh
  linarith

lemma concave_second {b : ℝ} (hb : b∈Icc (0:ℝ) (3/5)) : TLabel.d2 b<0 := by
  have hh := T_second_monotone ⟨hb.1,hb.2.trans T_six_mem.2⟩ T_six_mem hb.2
  linarith [T_six_second.2]

lemma first_tangent_reference :
    (1947/2500:ℝ)<TLabel.d1 (13/50) ∧ TLabel.d1 (13/50)<(779/1000:ℝ) ∧
      T (13/50)<(63573/250000:ℝ) := by
  have hd : (13/50:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  have hr := shifted_chart_reference (outer_domain hd)
    (l := (182701943/100000000:ℝ)) (u := (45675486/25000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  have hh := TLabel.first_chart_reference (outer_domain hd)
    (l := (182701943/100000000:ℝ)) (u := (45675486/25000000:ℝ))
    (dlo := (1947/2500:ℝ)) (dhi := (779/1000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [TLabel,W,Q0]) (by norm_num [TLabel,W,Q0])
  refine ⟨hh.1,hh.2,?_⟩
  dsimp [U] at hr
  norm_num [T,RoleLabel.outer,RoleLabel.eval,TLabel]
  nlinarith [hr.1]

theorem first_tangent {b : ℝ} (hb : b∈Icc (0:ℝ) (3/5)) :
    T b≤13/250+(779/1000)*b := by
  have hh := TLabel.tangent_upper
    (fun x hx => outer_domain (show x∈Icc 0 outerDiagonal from ⟨hx.1,hx.2.trans T_six_mem.2⟩))
    hb (show (13/50:ℝ)∈Icc 0 (3/5) by norm_num) (fun _ hx => (concave_second hx).le)
  change T b≤T (13/50)+TLabel.d1 (13/50)*(b-13/50) at hh
  have hp := mul_le_mul_of_nonneg_right first_tangent_reference.2.1.le hb.1
  nlinarith [first_tangent_reference.1,first_tangent_reference.2.2]

lemma second_tangent_reference :
    (70115079/100000000:ℝ)<TLabel.d1 (9/25) ∧ TLabel.d1 (9/25)<(701151/1000000:ℝ) ∧
      T (9/25)<(328119843/1000000000:ℝ) := by
  have hd : (9/25:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  have hr := shifted_chart_reference (outer_domain hd)
    (l := (178213355279/100000000000:ℝ)) (u := (2227666941/1250000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  have hh := TLabel.first_chart_reference (outer_domain hd)
    (l := (178213355279/100000000000:ℝ)) (u := (2227666941/1250000000:ℝ))
    (dlo := (70115079/100000000:ℝ)) (dhi := (701151/1000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [TLabel,W,Q0]) (by norm_num [TLabel,W,Q0])
  refine ⟨hh.1,hh.2,?_⟩
  dsimp [U] at hr
  norm_num [T,RoleLabel.outer,RoleLabel.eval,TLabel]
  nlinarith [hr.1]

theorem second_tangent {b : ℝ} (hb : b∈Icc (0:ℝ) (3/5)) :
    T b≤37853/500000+(701151/1000000)*b := by
  have hh := TLabel.tangent_upper
    (fun x hx => outer_domain (show x∈Icc 0 outerDiagonal from ⟨hx.1,hx.2.trans T_six_mem.2⟩))
    hb (show (9/25:ℝ)∈Icc 0 (3/5) by norm_num) (fun _ hx => (concave_second hx).le)
  change T b≤T (9/25)+TLabel.d1 (9/25)*(b-9/25) at hh
  have hp := mul_le_mul_of_nonneg_right second_tangent_reference.2.1.le hb.1
  nlinarith [second_tangent_reference.1,second_tangent_reference.2.2]

end SquaresInCircles.Eight.SecondWord.MixedTSmall
