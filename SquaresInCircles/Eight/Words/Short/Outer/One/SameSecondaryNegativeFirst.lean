module

public import SquaresInCircles.Eight.Owners.Contact.MinimumDerivatives
public import SquaresInCircles.Eight.Words.Short.Outer.One.SameSecondaryFirstNormBound
public import SquaresInCircles.Eight.Words.Short.Outer.One.SameSecondaryFirstZero

/-!
# Eight squares: the first negative secondary owner

Compactness on the initial strip leaves alignment, the moving zero-source boundary or the
diagonal target (`original_strip`). The stationary angular derivative excludes every other
minimum, including at the final angle. The single multiplier support covers all later angles
(`original`).
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace SquaresInCircles.Eight.ShortOuterOne.Same.Secondary.Negative.FirstStrip
open CommonQuarter CorePairGeometry Arithmetic
open SameContact (arc)

lemma diagonal_lower {x : ℝ} (hx : x∈Icc 0 strip) :
    (8981/10000:ℝ)<Negative.cost 0 outerDiagonal x := by
  have hdiag : outerDiagonal∈Icc 0 outerDiagonal :=
    ⟨by linarith [outer_endpoint_bounds.2.2.1],le_rfl⟩
  have hdom : ∀y∈Icc 0 strip,Domain outerDiagonal y :=
    fun y hy => ⟨hdiag,hy,(contact_target_diagonal hy).1.le⟩
  have hm : MonotoneOn (Negative.cost 0 outerDiagonal) (Icc 0 strip) := monoOn_of_hasDeriv_nonneg
    (fun y hy => (cost_angle_hasDerivAt 0 (wide_domain (hdom y hy))).continuousAt.continuousWithinAt)
    (fun y hy => cost_angle_hasDerivAt 0 (wide_domain (hdom y (Ioo_subset_Icc_self hy))))
    (fun y hy => (diagonal_first_positive (Ioo_subset_Icc_self hy)).le)
  have h0 : (0:ℝ)∈Icc 0 strip := by norm_num [strip]
  exact (initial_lower (hdom 0 h0)).trans_le (hm h0 hx hx.1)

lemma interior_not_minimum {B x : ℝ} (hd : Domain B x)
    (hx : 0<x) (hB : B<outerDiagonal) (hb : 0<contact B x)
    (hmin : ∀C y,Domain C y→Negative.cost 0 B x≤Negative.cost 0 C y) : False := by
  let T : Set ℝ := Ioo 0 outerDiagonal ∩ (fun C => contact C x) ⁻¹' Ioi 0
  have hcontactT : Continuous (fun C => contact C x) := by dsimp [contact,arc]; fun_prop
  have hT : IsOpen T := isOpen_Ioo.inter (isOpen_Ioi.preimage hcontactT)
  have hmemT : B∈T := ⟨⟨by linarith [target_lower hd],hB⟩,hb⟩
  have hlocalT : IsLocalMin (fun C => Negative.cost 0 C x) B := by
    filter_upwards [hT.mem_nhds hmemT] with C hC
    exact hmin C x ⟨Ioo_subset_Icc_self hC.1,hd.2.1,hC.2.le⟩
  have hstat : targetFirst 0 B x=0 :=
    hlocalT.hasDerivAt_eq_zero (cost_target_hasDerivAt 0 (wide_domain hd))
  have hfirst : 0<Negative.first 0 B x := by
    rw [stationary_first hd hstat]
    exact transport_positive hd
  let O : Set ℝ := Ioi 0 ∩ (contact B) ⁻¹' Ioi 0
  have hcontactO : Continuous (contact B) := by unfold contact; fun_prop
  have hO : IsOpen O := isOpen_Ioi.inter (isOpen_Ioi.preimage hcontactO)
  have hmemO : x∈O := ⟨hx,hb⟩
  obtain ⟨ε,hε,hsub⟩ := exists_closed_interval_in_open hO hmemO
  have hdom {y : ℝ} (hy : y∈Icc (x-ε) x) : Domain B y := by
    have hh := hsub (show y∈Icc (x-ε) (x+ε) from ⟨hy.1,by linarith [hy.2]⟩)
    exact ⟨hd.1,⟨hh.1.le,hy.2.trans hd.2.1.2⟩,hh.2.le⟩
  have hn := ContactMinimumDerivatives.right_endpoint (show x-ε<x by linarith)
    (first_continuousAt hd) (fun y hy => cost_angle_hasDerivAt 0 (wide_domain (hdom hy)))
    (fun y hy => hmin B y (hdom hy))
  linarith

lemma minimum_lower {B x : ℝ} (hd : Domain B x)
    (hmin : ∀C y,Domain C y→Negative.cost 0 B x≤Negative.cost 0 C y) :
    (8981/10000:ℝ)<Negative.cost 0 B x := by
  by_cases hx : x=0
  · subst x
    exact initial_lower hd
  by_cases hb : contact B x=0
  · exact Zero.original_lower hd hb
  by_cases hB : B=outerDiagonal
  · subst B
    exact diagonal_lower hd.2.1
  exact (interior_not_minimum hd (lt_of_le_of_ne hd.2.1.1 (Ne.symm hx))
    (lt_of_le_of_ne hd.1.2 hB) (lt_of_le_of_ne hd.2.2 (Ne.symm hb)) hmin).elim

theorem contact_lower {B x : ℝ} (hd : Domain B x) :
    (8981/10000:ℝ)<Negative.cost 0 B x := by
  let guard : ℝ×ℝ→ℝ := fun z => contact z.1 z.2
  let objective : ℝ×ℝ→ℝ := fun z => Negative.cost 0 z.1 z.2
  have hg : Continuous guard := by dsimp [guard,contact,arc]; fun_prop
  have hf : Continuous objective := by dsimp [objective,Negative.cost,target,targetCost,contact,arc]; fun_prop
  obtain ⟨z,hz,hbetter,hmin⟩ := contact_region_minimum hg hf
    (p₀:=(B,x)) ⟨hd.1,hd.2.1,hd.2.2⟩
  have hzd : Domain z.1 z.2 := ⟨hz.1,hz.2.1,hz.2.2⟩
  have hh := minimum_lower hzd (fun C y hCy => hmin (C,y) hCy.1 hCy.2.1 hCy.2.2)
  exact hh.trans_le hbetter

theorem original_strip {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 strip)
    (hm : (1+Real.cos x+Real.sin x)/2≤b+A*Real.cos x-B*Real.sin x) :
    (8981/10000:ℝ)<Real.pi/2-x+c 0-P 0*a+t 0*b+p 0*A-q 0*B := by
  have hb : b∈Icc 0 outerDiagonal := ⟨hs.1,(outer_bounds hs).2.2.2.1⟩
  have hB : B∈Icc 0 outerDiagonal := ⟨ht.1,(outer_bounds ht).2.2.2.1⟩
  have hrequired : contact B x≤b := by
    dsimp [contact]
    rw [(SameContact.actual_arc ht).1]
    linarith
  have hcost : Real.pi/2-x+c 0+target 0 b+targetCost 0 B=
      Real.pi/2-x+c 0-P 0*a+t 0*b+p 0*A-q 0*B := by
    have hh := Secondary.original_cost 0 hs ht
    linarith
  rw [←hcost]
  by_cases hactive : 0≤contact B x
  · have hd : Domain B x := ⟨hB,hx,hactive⟩
    have hsource := target_monotone 0 (source_mem hd) hb hrequired
    have hh := contact_lower hd
    dsimp [Negative.cost] at hh
    linarith
  · have hdiag : outerDiagonal∈Icc 0 outerDiagonal :=
      ⟨by linarith [outer_endpoint_bounds.2.2.1],le_rfl⟩
    have hc : Continuous (fun D => contact D x) := by dsimp [contact,arc]; fun_prop
    obtain ⟨D,hD,he⟩ := intermediate_value_Icc hB.2 hc.continuousOn
      (show (0:ℝ)∈Icc (contact B x) (contact outerDiagonal x) from
        ⟨by linarith,(contact_target_diagonal hx).1.le⟩)
    beta_reduce at he
    have hDouter : D∈Icc 0 outerDiagonal := ⟨hB.1.trans hD.1,hD.2⟩
    have htarget := targetCost_antitone 0 hB hDouter hD.1
    have hsource := target_monotone 0 (show (0:ℝ)∈Icc 0 outerDiagonal from
      ⟨le_rfl,hdiag.1⟩) hb hb.1
    have hh := contact_lower (show Domain D x from ⟨hDouter,hx,he.ge⟩)
    dsimp [Negative.cost] at hh
    rw [he] at hh
    linarith

theorem original {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.cos x+Real.sin x)/2≤b+A*Real.cos x-B*Real.sin x) :
    (449/500:ℝ)<Real.pi/2-x+c 0-P 0*a+t 0*b+p 0*A-q 0*B := by
  by_cases hsmall : x≤ strip
  · linarith [original_strip hs ht ⟨hx.1,hsmall⟩ hm]
  · have hh := FirstNorm.original_later hs ht
      (show x∈Icc (3/100:ℝ) (7/10) from ⟨by dsimp [strip] at hsmall; linarith,hx.2⟩) hm
    linarith

end SquaresInCircles.Eight.ShortOuterOne.Same.Secondary.Negative.FirstStrip
