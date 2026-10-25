module

public import SquaresInCircles.Eight.TableFree.SecondOuterSameZeroPJInverse
public import SquaresInCircles.Eight.TableFree.ContactArcMinimum

/-!
# The P/J stationary point is not an interior contact minimum

Uncompiled source draft.  The explicit inverse angle gives a genuine
open interval of feasible contacts through the putative minimum.  The
fixed direction (1,-.7) has uniformly negative second derivative on a
neighborhood, contradicting the one-variable minimum theorem.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace SquaresInCircles.Eight.TableFree.SecondWord.SameZero.PJ
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)

lemma lineSecond_continuousAt {s B t : ℝ}
    (hs : s+t∈Icc 0 outerDiagonal) (hB : B-(7/10)*t∈Icc 0 outerDiagonal) :
    ContinuousAt (lineSecond s B) t := by
  have hz := inverse_data hs hB
  have hd := NegativeTwo.ContactInverse.data hB hz
  have hq0 : NegativeTwo.Inverse.q (U (B-(7/10)*t))≠0 := by
    linarith [NegativeTwo.Inverse.actual_q_positive hB]
  have hu0 : U (B-(7/10)*t)≠0 := hd.1.ne'
  have hv0 : NegativeTwo.ContactInverse.speed (s+t-1/2) (B-(7/10)*t)≠0 :=
    hd.2.2.2.2.1.ne'
  have hS : ContinuousAt (fun y : ℝ => s+y) t := by fun_prop
  have hT : ContinuousAt (fun y : ℝ => B-(7/10)*y) t := by fun_prop
  have hZ : ContinuousAt (fun y : ℝ => s+y-1/2) t := by fun_prop
  have hP0 := ContinuousAt.comp (x := t) (PLabel.d2_hasDerivAt (outer_domain hs)).continuousAt hS
  have hP : ContinuousAt (fun y => PLabel.d2 (s+y)) t := hP0
  have hJ0 := ContinuousAt.comp (x := t) (JLabel.d2_hasDerivAt (outer_domain hB)).continuousAt hT
  have hJ : ContinuousAt (fun y => JLabel.d2 (B-(7/10)*y)) t := hJ0
  have hU0 := ContinuousAt.comp (x := t) ((ShortOuterOne.SameContact.arc_hasDerivAt
    (outer_domain hB)).add_const (1/2)).continuousAt hT
  have hU : ContinuousAt (fun y => U (B-(7/10)*y)) t := hU0
  have hR0 := ContinuousAt.comp (x := t)
    (ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hB)).continuousAt hT
  have hR : ContinuousAt (fun y => ratio (B-(7/10)*y)) t := hR0
  have hQ : ContinuousAt (fun y => NegativeTwo.Inverse.q (U (B-(7/10)*y))) t :=
    continuousAt_const.sub (continuousAt_const.mul hU)
  have hV : ContinuousAt
      (fun y => NegativeTwo.ContactInverse.speed (s+y-1/2) (B-(7/10)*y)) t :=
    (hQ.sub (hZ.pow 2)).sqrt
  have hN : ContinuousAt (fun y => NegativeTwo.Inverse.N (U (B-(7/10)*y))) t :=
    ((continuousAt_const.mul hU).sub (continuousAt_const.mul (hU.pow 2))).sub
      continuousAt_const
  have hFD : ContinuousAt (fun y => NegativeTwo.Inverse.factorD (U (B-(7/10)*y))) t :=
    hN.div ((hU.pow 2).mul (hQ.pow 2)) (mul_ne_zero (pow_ne_zero 2 hu0) (pow_ne_zero 2 hq0))
  have hbrace : ContinuousAt (fun y => NegativeTwo.Inverse.brace (U (B-(7/10)*y))
      (ratio (B-(7/10)*y)) (NegativeTwo.ContactInverse.speed (s+y-1/2) (B-(7/10)*y))) t :=
    ((continuousAt_const.div (hU.pow 3) (pow_ne_zero 3 hu0)).sub
      ((continuousAt_const.mul (hR.pow 2)).div hQ hq0)).sub
        ((hR.pow 2).div (hV.pow 2) (pow_ne_zero 2 hv0))
  have hIT : ContinuousAt (fun y => PJCritical.inverseTarget (U (B-(7/10)*y))
      (ratio (B-(7/10)*y)) (s+y-1/2)
        (NegativeTwo.ContactInverse.speed (s+y-1/2) (B-(7/10)*y))) t :=
    (hR.neg.mul hFD).add ((hZ.div (hQ.mul hV) (mul_ne_zero hq0 hv0)).mul hbrace)
  have hIDS : ContinuousAt (fun y => inverseDirectionSecond (s+y) (B-(7/10)*y)) t :=
    ((hZ.add (continuousAt_const.mul hR)).neg.div (hV.pow 3) (pow_ne_zero 3 hv0)).add
      (continuousAt_const.mul hIT)
  exact (hIDS.add hP).sub (continuousAt_const.mul hJ)

theorem interior_not_minimum {B x : ℝ}
    (hB : B∈Ioo 0 outerDiagonal) (hx : x∈Ioo 0 (7/10))
    (hs : b B x∈Ioo 0 outerDiagonal)
    (hmin : ∀C y, Domain C y → value PLabel JLabel B x≤value PLabel JLabel C y) : False := by
  have hd : Domain B x :=
    ⟨Ioo_subset_Icc_self hB,Ioo_subset_Icc_self hx,Ioo_subset_Icc_self hs⟩
  have hbcont : Continuous (b B) :=
    continuous_iff_continuousAt.2 fun t => (b_angle_hasDerivAt B t).continuousAt
  let O : Set ℝ := Ioo 0 (7/10) ∩ (b B) ⁻¹' Ioo 0 outerDiagonal
  have hO : IsOpen O := isOpen_Ioo.inter (isOpen_Ioo.preimage hbcont)
  have hlocal : IsLocalMin (value PLabel JLabel B) x := by
    filter_upwards [hO.mem_nhds (show x∈O from ⟨hx,hs⟩)] with y hy
    exact hmin B y ⟨hd.1,Ioo_subset_Icc_self hy.1,Ioo_subset_Icc_self hy.2⟩
  have hstat : angleFirst PLabel B x=0 :=
    hlocal.hasDerivAt_eq_zero (value_angle_hasDerivAt PLabel JLabel hd)
  have hnegative := stationary_line_negative hd hstat
  let s := b B x
  let κ := -lineSecond s B 0/2
  have hk : 0<κ := by dsimp [κ,s]; linarith
  have hS : ContinuousAt (fun t : ℝ => s+t) 0 := by fun_prop
  have hT : ContinuousAt (fun t : ℝ => B-(7/10)*t) 0 := by fun_prop
  have hs0 : s+0∈Icc 0 outerDiagonal := by rw [add_zero]; exact hd.2.2
  have hB0 : B-(7/10)*0∈Icc 0 outerDiagonal := by rw [mul_zero,sub_zero]; exact hd.1
  have hI := (inverse_line_hasDerivAt (s := s) (B := B) (t := 0) hs0 hB0).continuousAt
  have hSecond := lineSecond_continuousAt (s := s) (B := B) (t := 0) hs0 hB0
  have hi0 : inverseAngle (s+0) (B-(7/10)*0)=x := by
    rw [add_zero,mul_zero,sub_zero]
    exact inverse_original hd
  have hSource : ∀ᶠ t in 𝓝 (0:ℝ), s+t∈Ioo 0 outerDiagonal :=
    hS.tendsto.eventually (isOpen_Ioo.mem_nhds (by rw [add_zero]; exact hs))
  have hTarget : ∀ᶠ t in 𝓝 (0:ℝ), B-(7/10)*t∈Ioo 0 outerDiagonal :=
    hT.tendsto.eventually (isOpen_Ioo.mem_nhds (by rw [mul_zero,sub_zero]; exact hB))
  have hAngle : ∀ᶠ t in 𝓝 (0:ℝ), inverseAngle (s+t) (B-(7/10)*t)∈Ioo 0 (7/10) :=
    hI.tendsto.eventually (isOpen_Ioo.mem_nhds (by rw [hi0]; exact hx))
  have hCurvature : ∀ᶠ t in 𝓝 (0:ℝ), lineSecond s B t< -κ :=
    hSecond.tendsto.eventually (eventually_lt_nhds (by dsimp [κ,s]; linarith))
  have hN : {t | s+t∈Ioo 0 outerDiagonal ∧ B-(7/10)*t∈Ioo 0 outerDiagonal ∧
      inverseAngle (s+t) (B-(7/10)*t)∈Ioo 0 (7/10) ∧ lineSecond s B t< -κ}∈𝓝 (0:ℝ) := by
    filter_upwards [hSource,hTarget,hAngle,hCurvature] with t ht hu hv hw
    exact ⟨ht,hu,hv,hw⟩
  obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhds_iff.mp hN
  apply not_minimum_on_strictly_concave_curve
    (s := {p : ℝ×ℝ | Domain p.1 p.2})
    (cost := fun p : ℝ×ℝ => value PLabel JLabel p.1 p.2)
    (p := (B,x)) (fun p hp => hmin p.1 p.2 hp)
    (curve := fun t : ℝ => (B-(7/10)*t,inverseAngle (s+t) (B-(7/10)*t)))
    (value := lineValue s B) (dvalue := lineFirst s B) (ddvalue := lineSecond s B)
    (O := Metric.ball 0 ε) Metric.isOpen_ball
    (show (0:ℝ)∈Metric.ball 0 ε by simpa using hε) hk
  · show (B-(7/10)*0,inverseAngle (s+0) (B-(7/10)*0))=(B,x)
    rw [hi0,mul_zero,sub_zero]
  · intro t ht
    have hh := hsub ht
    refine ⟨Ioo_subset_Icc_self hh.2.1,Ioo_subset_Icc_self hh.2.2.1,?_⟩
    show b (B-(7/10)*t) (inverseAngle (s+t) (B-(7/10)*t))∈Icc 0 outerDiagonal
    rw [inverse_contact (Ioo_subset_Icc_self hh.1) (Ioo_subset_Icc_self hh.2.1)]
    exact Ioo_subset_Icc_self hh.1
  · intro t ht
    have hh := hsub ht
    show value PLabel JLabel (B-(7/10)*t) (inverseAngle (s+t) (B-(7/10)*t))=_
    dsimp only [lineValue,inverseValue,value]
    rw [inverse_contact (Ioo_subset_Icc_self hh.1) (Ioo_subset_Icc_self hh.2.1)]
  · intro t ht
    exact lineValue_hasDerivAt (Ioo_subset_Icc_self (hsub ht).1)
      (Ioo_subset_Icc_self (hsub ht).2.1)
  · intro t ht
    exact lineFirst_hasDerivAt (Ioo_subset_Icc_self (hsub ht).1)
      (Ioo_subset_Icc_self (hsub ht).2.1)
  · intro t ht
    exact (hsub ht).2.2.2.le

end SquaresInCircles.Eight.TableFree.SecondWord.SameZero.PJ
