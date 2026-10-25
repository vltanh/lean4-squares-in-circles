module

public import SquaresInCircles.Eight.Words.Short.Outer.One.EdgeFiveASecondaryEndpoints

/-!
# Eight squares: the four complete A-secondary angle halves

The upper numerator decreases
while its norm increases. On the lower half, the exact norm defect
retains the cosine factor; the circle-norm curvature identity then gives
concavity on the complete interval. No angle subdivision is introduced.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.EdgeFive.ASecondary
open CommonQuarter CorePairGeometry Arithmetic

def numerator (r : Row) (x : ℝ) : ℝ := t r*Real.cos x-P r*Real.sin x
def numeratorD (r : Row) (x : ℝ) : ℝ := -t r*Real.sin x-P r*Real.cos x
theorem numerator_hasDerivAt (r : Row) (x : ℝ) :
    HasDerivAt (numerator r) (numeratorD r x) x := by
  have h := ((Real.hasDerivAt_cos x).const_mul (t r)).sub
    ((Real.hasDerivAt_sin x).const_mul (P r))
  convert h using 1
  · funext y; simp only [numerator,Pi.sub_apply]
  · simp only [numeratorD]; ring
theorem numerator_positive (r : Row) (hr : ARows r) {x : ℝ}
    (hx : x∈Icc 0 (7/10)) : 0<numerator r x := by
  have hc := A_bounds r hr
  have tr := positive_trig hx
  have ht : 0<t r := by linarith [hc.2.2.1]
  have htc := mul_lt_mul_of_pos_left tr.1 ht
  have htt := mul_lt_mul_of_pos_right hc.2.2.1 (by norm_num : (0:ℝ)<191/250)
  have hPs := mul_le_mul hc.2.1.le tr.2.2.2.1.le tr.2.2.1 (by norm_num : (0:ℝ)≤219/1000)
  dsimp [numerator]
  nlinarith
theorem numerator_antitone (r : Row) (hr : ARows r) :
    AntitoneOn (numerator r) (Icc 0 (7/10)) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun x _ => (numerator_hasDerivAt r x).continuousAt.continuousWithinAt)
    (fun x _ => numerator_hasDerivAt r x)
  intro x hx
  have tr := positive_trig (Ioo_subset_Icc_self hx)
  have hp := mul_nonneg (show 0≤P r by linarith [(A_bounds r hr).1])
    (show 0≤Real.cos x by linarith [tr.1])
  have ht := mul_nonneg (show 0≤t r by linarith [(A_bounds r hr).2.2.1]) tr.2.2.1
  dsimp [numeratorD]
  linarith
theorem upper_norm_monotone (r : Row) (hr : ARows r) :
    MonotoneOn (N r true) (Icc 0 (7/10)) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun x hx => (norm_hasDerivAt r hr true hx).continuousAt.continuousWithinAt)
    (fun x hx => norm_hasDerivAt r hr true (Ioo_subset_Icc_self hx))
  intro x hx
  have hxc := Ioo_subset_Icc_self hx
  rw [norm_first r hr true hxc]
  have hp := numerator_positive r hr hxc
  have hn := norm_positive r hr true hxc
  have hd : direction true=1 := by simp [direction,ShortWord.MixedQuarter.direction]
  have hw : weight r true=3/4 := by simp [weight]
  rw [hd,hw]
  apply div_nonneg
  · dsimp [numerator] at hp
    linarith
  · exact hn.le
theorem upper_ratio (r : Row) (hr : ARows r) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    numerator r x/N r true x<663/1000 := by
  have h0 : (0:ℝ)∈Icc 0 (7/10) := by norm_num
  have hm := numerator_antitone r hr h0 hx hx.1
  have hN := (Endpoint.upper_norm_initial r hr).trans_le (upper_norm_monotone r hr h0 hx hx.1)
  have ht := (A_bounds r hr).2.2.2
  have hn0 : numerator r 0=t r := by simp [numerator]
  rw [hn0] at hm
  apply (div_lt_iff₀ (norm_positive r hr true hx)).mpr
  linarith
theorem upper_first (r : Row) (hr : ARows r) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (1/10:ℝ)<first r true x := by
  have hd : direction true=1 := by simp [direction,ShortWord.MixedQuarter.direction]
  have hw : weight r true=3/4 := by simp [weight]
  have he : CircularNorm.d1 (normA r true) (normB r true) (normC r true) x=
      (3/4)*(numerator r x/N r true x) := by
    rw [norm_first r hr true hx,hd,hw]
    dsimp only [numerator]
    ring
  have hd' := mul_lt_mul_of_pos_left (upper_ratio r hr hx) (by norm_num : (0:ℝ)<3/4)
  have hR : 0<CommonQuarter.radius := by linarith [radius_bounds.1]
  have hh := mul_lt_mul_of_pos_left hd' hR
  have tr := positive_trig hx
  dsimp only [first]
  rw [he,hd,hw]
  linarith [ShortWord.MixedQuarter.Reference.radius_fine.2,tr.1,tr.2.2.2.1]
theorem upper_monotone (r : Row) (hr : ARows r) : MonotoneOn (F r true) (Icc 0 (7/10)) :=
  monoOn_of_hasDeriv_nonneg
    (fun x hx => (F_hasDerivAt r hr true hx).continuousAt.continuousWithinAt)
    (fun x hx => F_hasDerivAt r hr true (Ioo_subset_Icc_self hx))
    (fun x hx => by linarith [upper_first r hr (Ioo_subset_Icc_self hx)])
theorem upper_lower (r : Row) (hr : ARows r) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (4619/5000:ℝ)<F r true x :=
  (Endpoint.upper_initial r hr).trans_le (upper_monotone r hr (by norm_num) hx hx.1)

theorem lower_norm_defect (r : Row) (hr : ARows r) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (N r false x)^2-(N r false 0)^2*(Real.cos x)^2=
      (N r false 0)^2*(Real.sin x)^2-2*weight r false*P r*(1-Real.cos x)-
        2*weight r false*t r*Real.sin x := by
  have hn := norm_sq r hr false hx
  have h0 := norm_initial r false
  have hd : direction false= -1 := by simp [direction,ShortWord.MixedQuarter.direction]
  simp only [normA,normB,normC,hd] at hn
  linear_combination hn-h0-(N r false 0)^2*(Real.sin_sq_add_cos_sq x)
theorem lower_norm_cos (r : Row) (hr : ARows r) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    N r false x≤N r false 0*Real.cos x := by
  have tr := positive_trig hx
  have hcoef := Endpoint.lower_coef r hr
  have hDs := mul_le_mul_of_nonneg_left tr.2.2.2.1.le (sq_nonneg (N r false 0))
  have hin : (N r false 0)^2*Real.sin x-2*weight r false*t r≤0 := by nlinarith
  have hlast := mul_nonpos_of_nonneg_of_nonpos tr.2.2.1 hin
  have hdef := lower_norm_defect r hr hx
  have hP : 0≤P r := by linarith [(A_bounds r hr).1]
  have hw := (weight_positive r hr false).le
  have hdrop := mul_nonneg (mul_nonneg hw hP) (show 0≤1-Real.cos x by linarith [Real.cos_le_one x])
  have hN := norm_positive r hr false hx
  have hN0 := norm_positive r hr false (show (0:ℝ)∈Icc 0 (7/10) by norm_num)
  have hright := mul_pos hN0 (show 0<Real.cos x by linarith [tr.1])
  nlinarith
theorem lower_second (r : Row) (hr : ARows r) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    second r false x<0 := by
  have hd : direction false= -1 := by simp [direction,ShortWord.MixedQuarter.direction]
  have hcoef : (normB r false)^2+(normC r false)^2≤(normA r false)^2 := by
    rcases hr with rfl|rfl <;> norm_num [normA,normB,normC,weight,P,t,q,hd]
  have hc := CircularNorm.curvature_lower (energy_positive r hr false hx) hcoef
  have hR : 0≤CommonQuarter.radius := by linarith [radius_bounds.1]
  have hm := mul_le_mul_of_nonneg_left hc hR
  have hn := mul_le_mul_of_nonneg_left (lower_norm_cos r hr hx) hR
  have hreserve := Endpoint.lower_curvature_reserve r hr
  have hcos : 0<Real.cos x := by linarith [(positive_trig hx).1]
  have hnegative := mul_neg_of_pos_of_neg hcos
    (show -weight r false+CommonQuarter.radius*N r false 0/4<0 by linarith)
  dsimp only [second]
  rw [hd]
  change CommonQuarter.radius*(-N r false x/4)≤_ at hm
  linarith only [hm,hn,hnegative]
theorem lower_concave (r : Row) (hr : ARows r) : ConcaveOn ℝ (Icc 0 (7/10)) (F r false) :=
  concave_of_deriv2 (fun x hx => F_hasDerivAt r hr false hx)
    (fun x hx => first_hasDerivAt r hr false hx) (fun x hx => (lower_second r hr hx).le)
theorem lower_lower (r : Row) (hr : ARows r) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (8981/10000:ℝ)<F r false x := by
  apply concave_gt_of_endpoints (lower_concave r hr) hx
  · linarith [Endpoint.lower_initial r hr]
  · exact Endpoint.lower_terminal r hr

theorem original (r : Row) (hr : ARows r) (upper : Bool) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : Secondary r upper a b A B x) : (8981/10000:ℝ)<cost r upper a b A B x := by
  have hh := original_lower r hr upper hs ht hx hm
  cases upper
  · exact (lower_lower r hr hx).trans_le hh
  · linarith [upper_lower r hr hx]

end SquaresInCircles.Eight.ShortOuterOne.EdgeFive.ASecondary
