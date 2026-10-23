module

public import SquaresInCircles.Eight.TableFree.ContactContinuation

/-!
# Continuation from the derivative at an active boundary only

Uncompiled source draft.  No derivative sign away from the boundary is
assumed.  A first bad point in a compact interval would be a minimum
from the left, incompatible with a positive boundary derivative.  If
the initial point is itself on the boundary, either an interior point
is already strict or the initial point is a maximum from the right.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree

theorem not_positive_at_leftward_maximum {f : ℝ → ℝ} {a b m d : ℝ}
    (hm : m∈Icc a b) (hmb : m<b)
    (hmax : IsMaxOn f (Icc a b) m) (hd : HasDerivAt f d m) : d≤0 := by
  have hb : b∈Icc a b := ⟨hm.1.trans hm.2,le_rfl⟩
  have hsegment : segment ℝ m b ⊆ Icc a b :=
    (convex_Icc a b).segment_subset hm hb
  have hcone := sub_mem_posTangentConeAt_of_segment_subset hsegment
  have hlocal : IsLocalMaxOn f (Icc a b) m := hmax.isLocalMaxOn
  have hh := hlocal.hasFDerivWithinAt_nonpos hd.hasFDerivAt.hasFDerivWithinAt hcone
  have hp : d*(b-m)≤0 := by simpa [mul_comm] using hh
  nlinarith

theorem strict_boundary_of_strict_start {f df : ℝ → ℝ} {l u b : ℝ}
    (hlu : l≤u) (hc : Continuous f)
    (hd : ∀x∈Icc l u,HasDerivAt f (df x) x)
    (hboundary : ∀x∈Icc l u,f x=b → 0<df x) (hl : b<f l) : b<f u := by
  by_contra! hu
  let K := Icc l u ∩ f ⁻¹' Iic b
  have hK : IsCompact K := isCompact_Icc.inter_right (isClosed_Iic.preimage hc)
  have hne : K.Nonempty := ⟨u,⟨⟨hlu,le_rfl⟩,hu⟩⟩
  obtain ⟨m,hm,hmin⟩ := hK.exists_isMinOn hne continuous_id.continuousOn
  have hmi : m∈Icc l u := hm.1
  have hfm : f m≤b := hm.2
  have hlm : l<m := by
    apply lt_of_le_of_ne hmi.1
    intro he
    rw [←he] at hfm
    linarith
  obtain ⟨v,hv,hveq⟩ := intermediate_value_Icc hmi.1 hc.neg.continuousOn
    (show -b∈Icc (-f l) (-f m) by constructor <;> linarith)
  have hfv : f v=b := by linarith
  have hvK : v∈K := ⟨⟨hv.1,hv.2.trans hmi.2⟩,hfv.le⟩
  have hmv : m≤v := hmin hvK
  have hvm : v=m := le_antisymm hv.2 hmv
  have hfeq : f m=b := by simpa only [hvm] using hfv
  have hmax : IsMaxOn (fun x => -f x) (Icc l m) m := by
    intro y hy
    by_cases hfy : f y≤b
    · have hyK : y∈K := ⟨⟨hy.1,hy.2.trans hmi.2⟩,hfy⟩
      have hmy : m≤y := hmin hyK
      have hym : y=m := le_antisymm hy.2 hmy
      simp only [hym]
    · linarith
  have hn := not_negative_at_rightward_maximum
    (show m∈Icc l m from ⟨hmi.1,le_rfl⟩) hlm hmax (hd m hmi).neg
  have hp := hboundary m hmi hfeq
  linarith

/-- A cap sum that starts feasible is strictly feasible after every
positive motion, provided its derivative points inward at every exact
boundary.  Both interval endpoints are included in the derivative data. -/
theorem strict_boundary_continuation {f df : ℝ → ℝ} {l u b : ℝ}
    (hc : Continuous f)
    (hd : ∀x∈Icc l u,HasDerivAt f (df x) x)
    (hboundary : ∀x∈Icc l u,f x=b → 0<df x) (hl : b≤f l) :
    ∀x∈Ioc l u,b<f x := by
  intro x hx
  by_contra! hbad
  by_cases hex : ∃y∈Icc l x,b<f y
  · obtain ⟨y,hy,hfy⟩ := hex
    have hsub : Icc y x ⊆ Icc l u := Icc_subset_Icc hy.1 hx.2
    have hh := strict_boundary_of_strict_start hy.2 hc
      (fun z hz => hd z (hsub hz))
      (fun z hz => hboundary z (hsub hz)) hfy
    linarith
  · have hbound (y : ℝ) (hy : y∈Icc l x) : f y≤b := by
      by_contra! hn
      exact hex ⟨y,hy,hn⟩
    have hli : l∈Icc l u := ⟨le_rfl,hx.1.le.trans hx.2⟩
    have hfeq : f l=b := le_antisymm (hbound l ⟨le_rfl,hx.1.le⟩) hl
    have hmax : IsMaxOn f (Icc l x) l := by
      intro y hy
      exact (hbound y hy).trans hl
    have hn := not_positive_at_leftward_maximum
      (show l∈Icc l x from ⟨le_rfl,hx.1.le⟩) hx.1 hmax (hd l hli)
    have hp := hboundary l hli hfeq
    linarith

end SquaresInCircles.Eight.TableFree
