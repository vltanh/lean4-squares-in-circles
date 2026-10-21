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
  have hsource : HasDerivAt (fun y : ℝ => s+y) 1 t := by
    convert (hasDerivAt_id t).const_add s using 1 <;> ring
  have htarget : HasDerivAt (fun y : ℝ => B-(7/10)*y) (-(7/10)) t := by
    convert ((hasDerivAt_id t).const_mul (7/10)).const_sub B using 1 <;> ring
  have hP := (PLabel.d2_hasDerivAt (outer_domain hs)).continuousAt.comp t hsource.continuousAt
  have hJ := (JLabel.d2_hasDerivAt (outer_domain hB)).continuousAt.comp t htarget.continuousAt
  have hU := ((ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hB)).add_const
    (1/2)).continuousAt.comp t htarget.continuousAt
  have hR := (ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hB)).continuousAt.comp t
    htarget.continuousAt
  have hd := NegativeTwo.ContactInverse.data hB (inverse_data hs hB)
  have hQ : ContinuousAt (fun y => NegativeTwo.Inverse.q (U (B-(7/10)*y))) t := by
    exact (continuousAt_const.sub (hU.const_mul 2))
  have hV : ContinuousAt (fun y => NegativeTwo.ContactInverse.speed
      (s+y-1/2) (B-(7/10)*y)) t :=
    (hQ.sub ((hsource.continuousAt.sub continuousAt_const).pow 2)).sqrt
  have hu : U (B-(7/10)*t)≠0 := hd.1.ne'
  have hq : NegativeTwo.Inverse.q (U (B-(7/10)*t))≠0 := by
    linarith [NegativeTwo.Inverse.actual_q_positive hB]
  have hv : NegativeTwo.ContactInverse.speed (s+t-1/2) (B-(7/10)*t)≠0 :=
    hd.2.2.2.2.1.ne'
  dsimp [lineSecond,inverseDirectionSecond,PJCritical.inverseTarget,
    PJCritical.heightFactorD,NegativeTwo.Inverse.factorD,NegativeTwo.Inverse.N,
    NegativeTwo.Inverse.brace]
  fun_prop (disch := first | assumption | positivity)

theorem interior_not_minimum {B x : ℝ}
    (hB : B∈Ioo 0 outerDiagonal) (hx : x∈Ioo 0 (7/10))
    (hs : b B x∈Ioo 0 outerDiagonal)
    (hmin : ∀C y, Domain C y → value PLabel JLabel B x≤value PLabel JLabel C y) : False := by
  have hd : Domain B x :=
    ⟨Ioo_subset_Icc_self hB,Ioo_subset_Icc_self hx,Ioo_subset_Icc_self hs⟩
  have hbcont : Continuous (b B) := by dsimp [b]; fun_prop
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
  have hI := (inverse_line_hasDerivAt
    (s := s) (B := B) (t := 0) (by simpa using hd.2.2)
    (by simpa using hd.1)).continuousAt
  have hSecond := lineSecond_continuousAt
    (s := s) (B := B) (t := 0) (by simpa using hd.2.2) (by simpa using hd.1)
  have hi0 : inverseAngle (s+0) (B-(7/10)*0)=x := by
    simpa [s] using inverse_original hd
  have hSource : ∀ᶠ t in 𝓝 (0:ℝ), s+t∈Ioo 0 outerDiagonal :=
    hS.tendsto.eventually (isOpen_Ioo.mem_nhds (by simpa [s] using hs))
  have hTarget : ∀ᶠ t in 𝓝 (0:ℝ), B-(7/10)*t∈Ioo 0 outerDiagonal :=
    hT.tendsto.eventually (isOpen_Ioo.mem_nhds (by simpa using hB))
  have hAngle : ∀ᶠ t in 𝓝 (0:ℝ), inverseAngle (s+t) (B-(7/10)*t)∈Ioo 0 (7/10) :=
    hI.tendsto.eventually (isOpen_Ioo.mem_nhds (by rwa [hi0]))
  have hCurvature : ∀ᶠ t in 𝓝 (0:ℝ), lineSecond s B t< -κ := by
    apply hSecond.tendsto.eventually
    apply gt_mem_nhds
    dsimp [κ]
    linarith
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
  · simp [hi0]
  · intro t ht
    have hh := hsub ht
    refine ⟨Ioo_subset_Icc_self hh.2.1,Ioo_subset_Icc_self hh.2.2.1,?_⟩
    rw [inverse_contact (Ioo_subset_Icc_self hh.1) (Ioo_subset_Icc_self hh.2.1)]
    exact Ioo_subset_Icc_self hh.1
  · intro t ht
    have hh := hsub ht
    dsimp [lineValue,inverseValue,value]
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
