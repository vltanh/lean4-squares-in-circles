module

public import SquaresInCircles.Eight.Owners.Contact.ArcMinimum
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ZeroAlignedL
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ZeroLNegativeRatio
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ZeroNegativePJ

/-!
# Eight squares: boundary completeness for the symmetric negative-angle contact

A compact minimum with positive angle has a nonpositive one-sided angular derivative. The
location lemmas then put its source strictly inside the physical arc, and the positive target
derivative gives a feasible left descent, also at the closed target diagonal. Thus every minimum
is aligned (`minimum_aligned`), which gives the lower bound `minus_lower`.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace SquaresInCircles.Eight.SecondWord.OppositeZero.Symmetric
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)

/-- A differentiable minimum at the right end of a nondegenerate left interval
has nonpositive derivative. The proof uses a local linear minorant. -/
private lemma right_minimum_derivative {f d : ℝ→ℝ} {l x : ℝ}
    (hlx : l<x) (hc : ContinuousAt d x)
    (hd : ∀t∈Icc l x, HasDerivAt f (d t) t)
    (hmin : ∀t∈Icc l x, f x≤f t) : d x≤0 := by
  by_contra! hpos
  have hN : {t : ℝ | l<t ∧ d x/2<d t}∈𝓝 x := by
    filter_upwards [eventually_gt_nhds hlx,
      hc.tendsto.eventually (eventually_gt_nhds (half_lt_self hpos))] with t ht hu
    exact ⟨ht,hu⟩
  obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhds_iff.mp hN
  let y := x-ε/2
  have hyx : y<x := by dsimp [y]; linarith
  have hball {t : ℝ} (ht : t∈Icc y x) : t∈Metric.ball x ε := by
    change dist t x<ε
    rw [Real.dist_eq]
    apply abs_lt.mpr
    dsimp [y] at ht
    constructor <;> linarith [ht.1,ht.2]
  have hy : l<y := (hsub (hball ⟨le_rfl,hyx.le⟩)).1
  have hdom {t : ℝ} (ht : t∈Icc y x) : t∈Icc l x :=
    ⟨hy.le.trans ht.1,ht.2⟩
  have hm : MonotoneOn (fun t => f t-(d x/2)*t) (Icc y x) :=
    monoOn_of_hasDeriv_nonneg
      (fun t ht => ((hd t (hdom ht)).sub
        ((hasDerivAt_id t).const_mul (d x/2))).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (hdom (Ioo_subset_Icc_self ht))).sub
        ((hasDerivAt_id t).const_mul (d x/2)))
      (fun t ht => by linarith [(hsub (hball (Ioo_subset_Icc_self ht))).2])
  have hh := hm ⟨le_rfl,hyx.le⟩ ⟨hyx.le,le_rfl⟩ hyx.le
  have hl := hmin y ⟨hy.le,hyx.le⟩
  nlinarith [mul_pos (half_pos hpos) (sub_pos.mpr hyx)]

lemma targetFirst_continuousAt {B x : ℝ} (hd : MinusDomain B x) :
    ContinuousAt (fun C => minusTarget LLabel LLabel C x) B := by
  have hsource := ((LLabel.d1_hasDerivAt (outer_domain hd.2.2)).comp B
    (minus_target_hasDerivAt hd.1 x)).continuousAt
  have htarget := (LLabel.d1_hasDerivAt (outer_domain hd.1)).continuousAt
  have hratio := (ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hd.1)).continuousAt
  have hK : ContinuousAt (fun C => minusK C x) B :=
    continuousAt_const.add (hratio.mul continuousAt_const)
  exact htarget.sub (hsource.mul hK)

lemma minimum_aligned {B x : ℝ} (hd : MinusDomain B x)
    (hmin : ∀C y, MinusDomain C y → minusCost LLabel LLabel B x≤ minusCost LLabel LLabel C y) :
    x=0 := by
  by_contra hxne
  have hx : 0<x := lt_of_le_of_ne hd.2.1.1 (Ne.symm hxne)
  have hdx : minusFirst LLabel B x≤0 :=
    right_minimum_derivative hx (minusFirst_hasDerivAt LLabel hd).continuousAt
      (fun t ht => minusCost_hasDerivAt LLabel LLabel (NegativePJ.domain_before hd ht))
      (fun t ht => hmin B t (NegativePJ.domain_before hd ht))
  have hloc := nonpositive_angular_location hd hdx
  have hsource : minus B x∈Ioo 0 outerDiagonal :=
    ⟨by linarith [minus_aligned_le hd.1 hd.2.1,hd.1.2,outer_endpoint_bounds.2.2.2],
      by linarith [hloc.2.1,fine_outer_endpoint_bounds.2]⟩
  let O : Set ℝ := Ioi 0 ∩ (fun C => minus C x) ⁻¹' Ioo 0 outerDiagonal
  have hcont : Continuous (fun C => minus C x) := by dsimp [minus,arc]; fun_prop
  have hO : IsOpen O := isOpen_Ioi.inter (isOpen_Ioo.preimage hcont)
  have hmem : B∈O := ⟨show (0:ℝ)<B by linarith [hloc.1],hsource⟩
  obtain ⟨ε,hε,hsub⟩ := exists_closed_interval_in_open hO hmem
  have hdom {C : ℝ} (hC : C∈Icc (B-ε) B) : MinusDomain C x := by
    have hh := hsub (show C∈Icc (B-ε) (B+ε) from ⟨hC.1,by linarith [hC.2]⟩)
    exact ⟨⟨hh.1.le,hC.2.trans hd.1.2⟩,hd.2.1,Ioo_subset_Icc_self hh.2⟩
  have hBder : minusTarget LLabel LLabel B x≤0 :=
    right_minimum_derivative (f := fun C => minusCost LLabel LLabel C x)
      (d := fun C => minusTarget LLabel LLabel C x) (by linarith : B-ε<B)
      (targetFirst_continuousAt hd)
      (fun C hC => minusCost_target_hasDerivAt LLabel LLabel (hdom hC))
      (fun C hC => hmin C x (hdom hC))
  exact (not_lt_of_ge hBder) (target_derivative_positive hd hdx)

/-- The whole negative-angle symmetric physical contact, with both diagonals. -/
theorem minus_lower {B x : ℝ} (hd : MinusDomain B x) :
    (89777/100000:ℝ)< minusCost LLabel LLabel B x := by
  let guard : ℝ×ℝ→ℝ := fun p => outerDiagonal-minus p.1 p.2
  let cost : ℝ×ℝ→ℝ := fun p => minusCost LLabel LLabel p.1 p.2
  have hg : Continuous guard := by dsimp [guard,minus,arc]; fun_prop
  have hc : Continuous cost := by
    dsimp [cost,minusCost,RoleLabel.outer,RoleLabel.eval,minus,arc]
    fun_prop
  obtain ⟨p,hp,hbetter,hmin⟩ := contact_region_minimum hg hc
    (p₀ := (B,x)) ⟨hd.1,hd.2.1,sub_nonneg.mpr hd.2.2.2⟩
  have hpd : MinusDomain p.1 p.2 :=
    ⟨hp.1,hp.2.1,⟨by
      linarith [minus_aligned_le hp.1 hp.2.1,hp.1.2,outer_endpoint_bounds.2.2.2],
      sub_nonneg.mp hp.2.2⟩⟩
  have haligned : p.2=0 := minimum_aligned hpd (fun C y hCy =>
    hmin (C,y) hCy.1 hCy.2.1 (sub_nonneg.mpr hCy.2.2.2))
  have hsource := hpd.2.2
  rw [haligned] at hsource
  norm_num [minus] at hsource
  have hl := AlignedL.original hsource hpd.1 (by ring)
  have hcost : (89777/100000:ℝ)< minusCost LLabel LLabel p.1 p.2 := by
    simpa [minusCost,minus,haligned] using hl
  exact hcost.trans_le hbetter

end SquaresInCircles.Eight.SecondWord.OppositeZero.Symmetric
