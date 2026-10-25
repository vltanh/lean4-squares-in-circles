module

public import SquaresInCircles.Eight.TableFree.EndpointPrinciples
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Minima on intrinsic contact arcs

Uncompiled source draft. This module provides the compactness and local-curve
argument used to replace a feasible pair by an alignment, a sign junction,
or a diagonal. There is no discretization of the contact parameter.

A strict negative curvature excludes an interior minimum along an actual
feasible contact curve. Compactness is used only on one closed rectangle.
The curvature and geometric feasibility of each curve are supplied by the
explicit formula theorems in the paired-primary modules.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree

/-- An open real neighborhood contains a two-sided closed interval. -/
theorem exists_closed_interval_in_open {s : Set ℝ} (hs : IsOpen s)
    {x : ℝ} (hx : x∈s) :
    ∃ ε : ℝ, 0<ε ∧ Icc (x-ε) (x+ε)⊆s := by
  obtain ⟨δ,hδ,hsub⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds hx)
  refine ⟨δ/2,half_pos hδ,?_⟩
  intro y hy
  apply hsub
  change dist y x<δ
  rw [Real.dist_eq]
  apply abs_lt.mpr
  constructor <;> linarith [hy.1,hy.2]

/-- A minimum over arbitrary geometric states is not an interior point of
any actual feasible strongly concave contact curve. -/
theorem not_minimum_on_strictly_concave_curve
    {X : Type*} {s : Set X} {cost : X → ℝ} {p : X}
    (hp : ∀ z∈s, cost p≤cost z)
    {curve : ℝ → X} {value dvalue ddvalue : ℝ → ℝ}
    {O : Set ℝ} (hO : IsOpen O) {x k : ℝ}
    (hx : x∈O) (hk : 0<k)
    (he : curve x=p)
    (hfeasible : ∀ y∈O, curve y∈s)
    (hvalue : ∀ y∈O, cost (curve y)=value y)
    (hd : ∀ y∈O, HasDerivAt value (dvalue y) y)
    (hdd : ∀ y∈O, HasDerivAt dvalue (ddvalue y) y)
    (hcurv : ∀ y∈O, ddvalue y≤-k) : False := by
  obtain ⟨ε,hε,hsub⟩ := exists_closed_interval_in_open hO hx
  have hmid : x∈Ioo (x-ε) (x+ε) := by constructor <;> linarith
  have hend := strict_endpoint_of_second_derivative hk hmid
    (fun y hy => hd y (hsub hy)) (fun y hy => hdd y (hsub hy))
    (fun y hy => hcurv y (hsub hy))
  have hlo : x-ε∈O := hsub ⟨le_rfl,by linarith⟩
  have hhi : x+ε∈O := hsub ⟨by linarith,le_rfl⟩
  have hl := hp (curve (x-ε)) (hfeasible _ hlo)
  have hu := hp (curve (x+ε)) (hfeasible _ hhi)
  rw [← he,hvalue x hx,hvalue _ hlo] at hl
  rw [← he,hvalue x hx,hvalue _ hhi] at hu
  rcases hend with h | h <;> linarith

/-- A continuous nonnegative-contact region of a closed rectangle is compact. -/
theorem compact_contact_region {l u a b : ℝ} {contact : ℝ × ℝ → ℝ}
    (hc : Continuous contact) :
    IsCompact {p : ℝ × ℝ | p.1∈Icc l u ∧ p.2∈Icc a b ∧ 0≤contact p} := by
  have hbox : IsCompact (Icc l u ×ˢ Icc a b) := isCompact_Icc.prod isCompact_Icc
  have hclosed : IsClosed {p : ℝ × ℝ | 0≤contact p} :=
    isClosed_le continuous_const hc
  convert hbox.inter_right hclosed using 1
  ext p
  simp only [Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_prod,and_assoc]

theorem contact_region_minimum {l u a b : ℝ} {contact cost : ℝ × ℝ → ℝ}
    (hc : Continuous contact) (hf : Continuous cost)
    {p₀ : ℝ × ℝ} (hp₀ : p₀.1∈Icc l u ∧ p₀.2∈Icc a b ∧ 0≤contact p₀) :
    ∃ p : ℝ × ℝ,
      (p.1∈Icc l u ∧ p.2∈Icc a b ∧ 0≤contact p) ∧
      cost p≤cost p₀ ∧
      ∀ z : ℝ × ℝ, z.1∈Icc l u → z.2∈Icc a b → 0≤contact z → cost p≤cost z := by
  obtain ⟨p,hp,hm⟩ := (compact_contact_region hc).exists_isMinOn ⟨p₀,hp₀⟩
    hf.continuousOn
  exact ⟨p,hp,hm hp₀,fun z hz₁ hz₂ hz₃ => hm ⟨hz₁,hz₂,hz₃⟩⟩

/-- At a minimum whose cost strictly improves as y increases, the upper side
or the actual contact must be reached. The proof uses IVT, including a
nondifferentiable sign junction of the underlying outer circle. -/
theorem upper_or_contact_at_minimum
    {l u a b x y : ℝ} {contact cost : ℝ × ℝ → ℝ}
    (hxy : x∈Icc l u ∧ y∈Icc a b ∧ 0≤contact (x,y))
    (hmin : ∀ z : ℝ × ℝ, z.1∈Icc l u → z.2∈Icc a b → 0≤contact z →
      cost (x,y)≤cost z)
    (hc : Continuous (fun z : ℝ => contact (x,z)))
    (hcost : StrictAntiOn (fun z : ℝ => cost (x,z)) (Icc a b)) :
    y=b ∨ contact (x,y)=0 := by
  by_cases hy : y=b
  · exact Or.inl hy
  right
  by_contra hnot
  have hyb : y<b := lt_of_le_of_ne hxy.2.1.2 hy
  have hpos : 0<contact (x,y) := lt_of_le_of_ne hxy.2.2 (Ne.symm hnot)
  by_cases hb : 0≤contact (x,b)
  · have hf := hmin (x,b) hxy.1 ⟨by linarith [hxy.2.1.1],le_rfl⟩ hb
    have hlt := hcost hxy.2.1 ⟨by linarith [hxy.2.1.1],le_rfl⟩ hyb
    exact (not_lt_of_ge hf) hlt
  · have hbneg : contact (x,b)<0 := lt_of_not_ge hb
    have himage : 0∈(fun z : ℝ => -contact (x,z)) '' Icc y b := by
      apply intermediate_value_Icc hyb.le hc.neg.continuousOn
      constructor <;> simp only [Pi.neg_apply] <;> linarith
    obtain ⟨z,hz,hzval⟩ := himage
    have hz0 : contact (x,z)=0 := by simp only at hzval; linarith
    have hyz : y<z := by
      by_contra! h
      have he : z=y := le_antisymm h hz.1
      rw [he] at hz0
      linarith
    have hzab : z∈Icc a b := ⟨hxy.2.1.1.trans hz.1,hz.2⟩
    have hf := hmin (x,z) hxy.1 hzab hz0.ge
    have hlt := hcost hxy.2.1 hzab hyz
    exact (not_lt_of_ge hf) hlt

end SquaresInCircles.Eight.TableFree