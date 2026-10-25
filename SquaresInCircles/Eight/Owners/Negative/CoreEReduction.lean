module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Rat.Star
public import SquaresInCircles.Eight.Boundary.ActualSortedSupport
public import SquaresInCircles.Eight.Frames.Pair.TransportAssembly
public import SquaresInCircles.Eight.Owners.Negative.CoreEEntry
public import SquaresInCircles.Eight.Owners.Negative.TEntry
public import SquaresInCircles.Eight.Owners.PowerTailBounds
public import SquaresInCircles.Eight.Owners.TD0Span

/-!
# Eight squares: a negative E-primary total has a geometric reduction

From a normalized boundary cycle with E on the core and negative E total, a move of E gives a
`Reduction`: its E total is nonnegative, or E is on the flat core with both primary errors
nonpositive (`reduce_negative_total`). Every witness not incident to E and all the data of G, A,
B, T stay unchanged.
-/

section
/-!
## The growing flat-core interval for positive DE and negative EH

The two primary separators bound the tangent of E from below and from above (`lowerGap`,
`upperGap`). Both bounds move inward with the frame of E, and their gap grows on the whole short
interval (`rates`, `growing_gap`). The endpoint uses the same D and H and stays in the circle of
`q` (`NegativeEHEndpoint`, `negative_EH_endpoint`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.NegativeCoreE

def lowerGap (a t : ℝ) : ℝ :=
  1/2-(a-1/2)/Real.cos t-(1/12)*(Real.sin t/Real.cos t)

def upperGap (a t : ℝ) : ℝ :=
  -1/2+(a-1/2)/Real.cos t-(13/12)*(Real.sin t/Real.cos t)

def lowerRate (a t : ℝ) : ℝ :=
  ((a-1/2)*Real.sin t+1/12)/(Real.cos t)^2

def upperRate (a t : ℝ) : ℝ :=
  (13/12-(a-1/2)*Real.sin t)/(Real.cos t)^2

theorem short_trig {t : ℝ} (ht : t∈Icc 0 (1/4 : ℝ)) :
    31/32≤Real.cos t ∧ (Real.cos t)^2≤1 ∧
      93/100<(Real.cos t)^2 ∧ 0≤Real.sin t ∧ Real.sin t≤1/4 := by
  have hc := Real.one_sub_sq_div_two_le_cos (x := t)
  have htu := pow_le_pow_left₀ ht.1 ht.2 2
  have hcL : 31/32≤Real.cos t := by norm_num at htu; linarith
  have hcu := Real.cos_le_one t
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi ht.1
    (by linarith [ht.2,Real.pi_gt_three])
  refine ⟨hcL,?_,?_,hs0,(Real.sin_le ht.1).trans ht.2⟩ <;> nlinarith

theorem lowerGap_derivative {a t : ℝ} (ht : t∈Icc 0 (1/4 : ℝ)) :
    HasDerivAt (lowerGap a) (-lowerRate a t) t := by
  have hc : Real.cos t≠0 := ne_of_gt (by linarith [(short_trig ht).1])
  have hd := (((hasDerivAt_const t (1/2 : ℝ)).sub
    ((hasDerivAt_const t (a-1/2)).div (Real.hasDerivAt_cos t) hc)).sub
    (((Real.hasDerivAt_sin t).div (Real.hasDerivAt_cos t) hc).const_mul (1/12 : ℝ)))
  convert hd using 1
  · rfl
  · dsimp [lowerRate]
    field_simp [hc]
    nlinarith [Real.sin_sq_add_cos_sq t]

theorem upperGap_derivative {a t : ℝ} (ht : t∈Icc 0 (1/4 : ℝ)) :
    HasDerivAt (upperGap a) (-upperRate a t) t := by
  have hc : Real.cos t≠0 := ne_of_gt (by linarith [(short_trig ht).1])
  have hd := (((hasDerivAt_const t (-1/2 : ℝ)).add
    ((hasDerivAt_const t (a-1/2)).div (Real.hasDerivAt_cos t) hc)).sub
    (((Real.hasDerivAt_sin t).div (Real.hasDerivAt_cos t) hc).const_mul (13/12 : ℝ)))
  convert hd using 1
  · rfl
  · dsimp [upperRate]
    field_simp [hc]
    nlinarith [Real.sin_sq_add_cos_sq t]

/-- Rational bounds on the two rates, for every contained anchor with `1/2 < a < 283/200`; no
anchor is replaced by a diagonal or by the circle of the upper radius. -/
theorem rates {a t : ℝ} (ha : 1/2<a ∧ a<283/200)
    (ht : t∈Icc 0 (1/4 : ℝ)) :
    0<lowerRate a t ∧ lowerRate a t<17/50 ∧ 17/20<upperRate a t := by
  obtain ⟨hc,hc2U,hc2L,hs0,hsU⟩ := short_trig ht
  have hcos2 : 0<(Real.cos t)^2 := by linarith
  have hprod0 := mul_nonneg (show 0≤a-1/2 by linarith [ha.1]) hs0
  have hprodU : (a-1/2)*Real.sin t≤183/800 := by
    have hh := mul_le_mul (show a-1/2≤183/200 by linarith [ha.2]) hsU
      hs0 (by norm_num : (0:ℝ)≤183/200)
    norm_num at hh
    exact hh
  refine ⟨div_pos (by linarith) hcos2,?_,?_⟩
  · apply (div_lt_iff₀ hcos2).2
    nlinarith
  · apply (lt_div_iff₀ hcos2).2
    nlinarith

theorem growing_gap {aD aH p n : ℝ}
    (hD : 1/2<aD ∧ aD<283/200) (hH : 1/2<aH ∧ aH<283/200)
    (hp : 0≤p ∧ p≤n) (hn : n≤1/4) :
    MonotoneOn (fun τ : ℝ => upperGap aH (n-τ)) (Icc 0 p) ∧
      MonotoneOn (fun τ : ℝ => upperGap aH (n-τ)-lowerGap aD (p-τ)) (Icc 0 p) := by
  have hparams {τ : ℝ} (hτ : τ∈Icc 0 p) :
      n-τ∈Icc 0 (1/4 : ℝ) ∧ p-τ∈Icc 0 (1/4 : ℝ) := by
    constructor <;> constructor <;> linarith [hτ.1,hτ.2,hp.1,hp.2]
  have hupper {τ : ℝ} (hτ : τ∈Icc 0 p) :
      HasDerivAt (fun x => upperGap aH (n-x)) (upperRate aH (n-τ)) τ := by
    have hd := (upperGap_derivative (a := aH) (hparams hτ).1).comp τ
      ((hasDerivAt_id τ).const_sub n)
    exact hd.congr_deriv (by ring)
  have hgap {τ : ℝ} (hτ : τ∈Icc 0 p) :
      HasDerivAt (fun x => upperGap aH (n-x)-lowerGap aD (p-x))
        (upperRate aH (n-τ)-lowerRate aD (p-τ)) τ := by
    have hd := (lowerGap_derivative (a := aD) (hparams hτ).2).comp τ
      ((hasDerivAt_id τ).const_sub p)
    exact ((hupper hτ).sub hd).congr_deriv (by ring)
  constructor
  · apply StrictMonoOn.monotoneOn
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 p)
    · intro τ hτ
      exact (hupper hτ).continuousAt.continuousWithinAt
    · intro τ hτ
      rw [(hupper (interior_subset hτ)).deriv]
      have hr := (rates hH (hparams (interior_subset hτ)).1).2.2
      linarith
  · apply StrictMonoOn.monotoneOn
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 p)
    · intro τ hτ
      exact (hgap hτ).continuousAt.continuousWithinAt
    · intro τ hτ
      rw [(hgap (interior_subset hτ)).deriv]
      have hru := (rates hH (hparams (interior_subset hτ)).1).2.2
      have hrl := (rates hD (hparams (interior_subset hτ)).2).2.1
      linarith

theorem DE_margin {p b : ℝ} (D : SignedPoint) (hp : p∈Icc 0 (1/4 : ℝ)) :
    quarterProjection D (SignedPoint.flat (-b)) p 3-edgeWidth p=
      (b-lowerGap D.a p)*Real.cos p := by
  have hc : Real.cos p≠0 := ne_of_gt (by linarith [(short_trig hp).1])
  rw [edgeWidth_positive_formula ⟨hp.1,by linarith [hp.2]⟩]
  simp [quarterProjection,SignedPoint.flat]
  dsimp [lowerGap]
  field_simp [hc]
  ring

theorem EH_margin {n b : ℝ} (H : SignedPoint) (hn : n∈Icc 0 (1/4 : ℝ)) :
    quarterProjection (SignedPoint.flat (-b)) H (-n) 1-edgeWidth (-n)=
      (upperGap H.a n-b)*Real.cos n := by
  have hc : Real.cos n≠0 := ne_of_gt (by linarith [(short_trig hn).1])
  rw [edgeWidth_negative_formula ⟨hn.1,by linarith [hn.2]⟩]
  simp only [quarterProjection,Matrix.cons_val_one,SignedPoint.flat,Real.sin_neg,Real.cos_neg]
  dsimp [upperGap]
  field_simp [hc]
  ring

structure NegativeEHEndpoint (q : ℝ) (D E H : SignedPoint) (p n : ℝ) where
  point : SignedPoint
  sorted : point.Sorted
  nonpos : point.y≤0
  core : point.Core
  contained : point.Contained q
  flat : point.a=7/12
  tangent_bound : -point.y<39/250
  negative_remaining : 0<n-p
  DE3 : quarterFeasible D point 0 3
  DE2 : quarterFeasible D point 0 2
  EH1 : quarterFeasible point H (-(n-p)) 1

/-- The endpoint has the frame of D, and its tangent is the larger of the tangent of E and the
aligned DE lower bound; the gap estimate on the whole interval gives EH1 there. Only containment in
the circle of `q` is needed. -/
theorem negative_EH_endpoint {q p n : ℝ} {D E H : SignedPoint}
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hDs : D.Sorted) (hDcore : D.AvoidsCore) (hDo : D.Outer q)
    (hHs : H.Sorted) (hHcore : H.AvoidsCore) (hHy : 0≤H.y) (hHc : H.Contained q)
    (hEs : E.Sorted) (hEy : E.y≤0) (hEc : E.Core)
    (hn : n∈Ioc 0 frameCap) (hp : 0<p ∧ p<n)
    (hDE : quarterFeasible D E p 3) (hEH : quarterFeasible E H (-n) 1)
    (hnot : ¬quarterFeasible E H (-n) 0) :
    Nonempty (NegativeEHEndpoint q D E H p n) := by
  obtain ⟨hflat,hbU,hnU⟩ := genuine_negative_flat hEs hEy hEc hHs hHy hHc hqU hn hEH hnot
  let b := -E.y
  have hb0 : 0≤b := neg_nonneg.mpr hEy
  have hEeq : E=SignedPoint.flat (-b) := by
    apply SignedPoint.ext <;> simp [SignedPoint.flat,b,hflat]
  have hp' : p∈Icc 0 (1/4 : ℝ) := ⟨hp.1.le,hp.2.le.trans hnU.le⟩
  have hn' : n∈Icc 0 (1/4 : ℝ) := ⟨hn.1.le,hnU.le⟩
  have hD : 1/2<D.a ∧ D.a<283/200 :=
    ⟨SignedPoint.primary_gt_half hDs hDcore,
      (SignedPoint.coordinate_bounds hDs hDcore hDo.le hqU).2.1⟩
  have hH : 1/2<H.a ∧ H.a<283/200 :=
    ⟨SignedPoint.primary_gt_half hHs hHcore,
      (SignedPoint.coordinate_bounds hHs hHcore hHc hqU).2.1⟩
  have hL : lowerGap D.a p≤b := by
    have hm := sub_nonneg.mpr (show edgeWidth p≤quarterProjection D (SignedPoint.flat (-b)) p 3 by
      rw [← hEeq]; exact hDE)
    rw [DE_margin D hp'] at hm
    have hc : 0<Real.cos p := by linarith [(short_trig hp').1]
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_right hc).1 hm)
  have hU : b≤upperGap H.a n := by
    have hm := sub_nonneg.mpr (show edgeWidth (-n)≤quarterProjection (SignedPoint.flat (-b)) H (-n) 1 by
      rw [← hEeq]; exact hEH)
    rw [EH_margin H hn'] at hm
    have hc : 0<Real.cos n := by linarith [(short_trig hn').1]
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_right hc).1 hm)
  have hmono := growing_gap hD hH ⟨hp.1.le,hp.2.le⟩ hnU.le
  have hz : (0:ℝ)∈Icc 0 p := ⟨le_rfl,hp.1.le⟩
  have hpI : p∈Icc 0 p := ⟨hp.1.le,le_rfl⟩
  have hUmono : upperGap H.a n≤upperGap H.a (n-p) := by
    simpa using hmono.1 hz hpI hp.1.le
  have hgap : upperGap H.a n-lowerGap D.a p≤
      upperGap H.a (n-p)-lowerGap D.a 0 := by
    simpa using hmono.2 hz hpI hp.1.le
  let b' := max b (lowerGap D.a 0)
  have hb'0 : 0≤b' := hb0.trans (le_max_left _ _)
  have hb'U : b'≤upperGap H.a (n-p) := by
    apply max_le
    · exact hU.trans hUmono
    · linarith
  have hL0 : lowerGap D.a 0=1-D.a := by norm_num [lowerGap]; ring
  have hDlower := (uniform_circle_reserves hqL hqU).1.trans_le
    (SignedPoint.outer_bounds hDs hDo).1
  have hb'cut : b'<39/250 := by
    apply max_lt_iff.mpr
    exact ⟨hbU,by rw [hL0]; linarith⟩
  have habs : |-b'|≤1/2 := by rw [abs_neg,abs_of_nonneg hb'0]; linarith
  have hDEnew : quarterFeasible D (SignedPoint.flat (-b')) 0 3 ∧
      quarterFeasible D (SignedPoint.flat (-b')) 0 2 := by
    have hl : 1-D.a≤b' := by rw [← hL0]; exact le_max_right _ _
    constructor <;>
      simp [quarterFeasible,quarterProjection,SignedPoint.flat,edgeWidth,pairWidth] <;> linarith
  have hEHnew : quarterFeasible (SignedPoint.flat (-b')) H (-(n-p)) 1 := by
    apply sub_nonneg.mp
    rw [EH_margin H (show n-p∈Icc 0 (1/4 : ℝ) by constructor <;> linarith [hnU,hp.1,hp.2])]
    exact mul_nonneg (sub_nonneg.mpr hb'U)
      (by linarith [(short_trig (show n-p∈Icc 0 (1/4 : ℝ) by
        constructor <;> linarith [hnU,hp.1,hp.2])).1])
  exact ⟨{
    point := SignedPoint.flat (-b')
    sorted := SignedPoint.flat_sorted habs
    nonpos := neg_nonpos.mpr hb'0
    core := SignedPoint.flat_on_core habs
    contained := SignedPoint.flat_contained hqL habs
    flat := rfl
    tangent_bound := by simpa [SignedPoint.flat] using hb'cut
    negative_remaining := sub_pos.mpr hp.2
    DE3 := hDEnew.1
    DE2 := hDEnew.2
    EH1 := hEHnew }⟩

end SquaresInCircles.Eight.NegativeCoreE
end
end
end

section
/-!
## Inserting the negative core-E reductions into the seven-cycle

A `CycleMove` changes only E: the frames of D and H and every other point, owner and error stay.
The loss of positive variation is computed before the new normalized boundary input at the same
`q` is built (`boundaryInput`), and the equality of the two variations gives the negative budget
as well. Both local endpoints are such moves (`NegativeDEEndpoint.toCycle`,
`NegativeEHEndpoint.toCycle`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate
namespace NegativeCoreE

structure CycleMove (q : ℝ) (C : SignedCycle) where
  point : SignedPoint
  theta : ℝ
  sorted : point.Sorted
  contained : point.Contained q
  core : point.Core
  nonpos : point.y≤0
  frame_range : theta∈Icc (min (C.theta E) (C.theta D)) (max (C.theta E) (C.theta D))
  de : Fin 4
  eh : Fin 4
  de_allowed : de=2 ∨ de=3
  eh_allowed : eh=0 ∨ eh=1
  DE : quarterFeasible (C.point D) point (theta-C.theta D) de
  EH : quarterFeasible point (C.point H) (C.theta H-theta) eh
  positive_nonincrease : positiveVariation (Function.update C.theta E theta)≤positiveVariation C.theta

namespace CycleMove
variable {q : ℝ} {C : SignedCycle}

def cycle (O : CycleMove q C) : SignedCycle := replacePoint C E O.point O.theta

theorem unchanged (O : CycleMove q C) (i : Vertex) (hi : i≠E) :
    O.cycle.point i=C.point i ∧ O.cycle.theta i=C.theta i := by
  simp [cycle,replacePoint,hi]

theorem other_delta (O : CycleMove q C) (i : Vertex) (hiD : i≠D) (hiE : i≠E) :
    delta O.cycle.theta i=delta C.theta i := by
  have hn : next i≠E := (by decide : ∀ j : Vertex,j≠D → next j≠E) i hiD
  simp [delta,(O.unchanged i hiE).2,(O.unchanged (next i) hn).2]

theorem DE_actual (O : CycleMove q C) : O.cycle.Feasible D O.de := by
  simpa [cycle,replacePoint,SignedCycle.Feasible,SignedCycle.slack,
    SignedCycle.edge,word,delta,next,D,E,quarterFeasible,sub_nonneg] using O.DE

theorem EH_actual (O : CycleMove q C) : O.cycle.Feasible E O.eh := by
  simpa [cycle,replacePoint,SignedCycle.Feasible,SignedCycle.slack,
    SignedCycle.edge,word,delta,next,H,E,quarterFeasible,sub_nonneg] using O.EH

theorem other_feasible (O : CycleMove q C) (i : Vertex) (hiD : i≠D) (hiE : i≠E)
    (j : Fin 4) : O.cycle.Feasible i j ↔ C.Feasible i j := by
  have hn : next i≠E := (by decide : ∀ j : Vertex,j≠D → next j≠E) i hiD
  exact SignedCycle.replacePoint_other_feasible hiE hn

theorem necessary (O : CycleMove q C) (hn : C.Necessary q) : O.cycle.Necessary q :=
  SignedCycle.necessary_replace_clamped (v := E) (a := E) (b := D)
    hn O.sorted O.contained O.core.ge (Or.inr O.frame_range)

theorem normal (O : CycleMove q C) (hn : C.NormalAnchors) : O.cycle.NormalAnchors := by
  constructor
  · rw [(O.unchanged H (by decide)).1]; exact hn.H_nonneg
  · rw [(O.unchanged A (by decide)).1]; exact hn.A_nonneg
  · rw [(O.unchanged B (by decide)).1]; exact hn.B_nonpos
  · rw [(O.unchanged D (by decide)).1]; exact hn.D_nonpos

def witnesses (O : CycleMove q C) (w : C.Witnesses) : O.cycle.Witnesses where
  owner := Function.update (Function.update w.owner D O.de) E O.eh
  feasible i := by
    by_cases hiE : i=E
    · subst i; simpa using O.EH_actual
    · by_cases hiD : i=D
      · subst i; simpa [D,E] using O.DE_actual
      · simpa [Function.update_of_ne hiE,Function.update_of_ne hiD] using
          (O.other_feasible i hiD hiE (w.owner i)).2 (w.feasible i)
  allowed i := by
    by_cases hiE : i=E
    · subst i
      simpa [SignedCycle.normalOwners,E] using O.eh_allowed
    · by_cases hiD : i=D
      · subst i
        simpa [SignedCycle.normalOwners,D,E] using O.de_allowed
      · simpa [Function.update_of_ne hiE,Function.update_of_ne hiD] using w.allowed i

theorem other_owner (O : CycleMove q C) (w : C.Witnesses) (i : Vertex)
    (hiD : i≠D) (hiE : i≠E) : (O.witnesses w).owner i=w.owner i := by
  simp [witnesses,hiD,hiE]

theorem zero_signs (O : CycleMove q C) (w : C.Witnesses)
    (hz : C.ZeroSignImplications w) : O.cycle.ZeroSignImplications (O.witnesses w) := by
  constructor
  · intro hj
    rw [(O.unchanged G (by decide)).1]
    apply hz.HG_canceling
    simpa [witnesses,H,D,E] using hj
  · intro hj
    rw [(O.unchanged T (by decide)).1]
    apply hz.TD_canceling
    simpa [witnesses,T,D,E] using hj

theorem negative_nonincrease (O : CycleMove q C) :
    negativeVariation O.cycle.theta≤negativeVariation C.theta := by
  rw [← variations_equal O.cycle.theta,← variations_equal C.theta]
  exact O.positive_nonincrease

def boundaryInput (I : SignedCycle.NormalizedBoundaryInput q) (hq : q≤qCap)
    (O : CycleMove q I.cycle) : SignedCycle.NormalizedBoundaryInput q where
  cycle := O.cycle
  necessary := O.necessary I.necessary
  ordered := SignedCycle.normal_necessary_ordered (O.necessary I.necessary) hq
    (O.normal I.anchors_normal) (O.witnesses I.witnesses) (O.zero_signs I.witnesses I.zero_signs)
  strict_spread := SignedCycle.strictSpread_replace_clamped (v := E) (a := E) (b := D)
    (p := O.point) I.strict_spread (Or.inr O.frame_range)
  positive_variation := lt_of_le_of_lt O.positive_nonincrease I.positive_variation
  negative_variation := lt_of_le_of_lt O.negative_nonincrease I.negative_variation
  radial := by
    intro i
    by_cases hi : i=E
    · subst i; exact Or.inr O.core
    · rw [(O.unchanged i hi).1]; exact I.radial i
  anchors_outer := by
    intro i hi
    have hiE : i≠E := (by decide : ∀ j∈({H,A,B,D} : Finset Vertex),j≠E) i hi
    rw [(O.unchanged i hiE).1]
    exact I.anchors_outer i hi
  anchors_normal := O.normal I.anchors_normal
  witnesses := O.witnesses I.witnesses
  zero_signs := O.zero_signs I.witnesses I.zero_signs
  E_nonpos := O.nonpos

end CycleMove

def NegativeDEEndpoint.toCycle {q : ℝ} {C : SignedCycle}
    (O : NegativeDEEndpoint q (C.point D) (C.point E) (C.point H)
      (C.theta D-C.theta E) (C.theta H-C.theta E)) : CycleMove q C where
  point := O.point
  theta := C.theta E+O.movement
  sorted := O.sorted
  contained := O.contained
  core := O.core
  nonpos := O.nonpos
  frame_range := by
    have hED : C.theta E≤C.theta D := by linarith [O.negative_remaining,O.movement_nonneg]
    rw [min_eq_left hED,max_eq_right hED]
    constructor <;> linarith [O.negative_remaining,O.movement_nonneg]
  de := 3
  eh := 0
  de_allowed := Or.inr rfl
  eh_allowed := Or.inl rfl
  DE := by convert O.DE3 using 1; ring
  EH := by convert O.EH0 using 1; ring
  positive_nonincrease := by
    have hDEold : positivePart (C.theta E-C.theta D)=0 :=
      max_eq_right (by linarith [O.movement_nonneg,O.negative_remaining])
    have hDEnew : positivePart (C.theta E+O.movement-C.theta D)=0 :=
      max_eq_right (by linarith [O.negative_remaining])
    have hEHold : positivePart (C.theta H-C.theta E)=C.theta H-C.theta E :=
      max_eq_left (by linarith [O.movement_nonneg,O.movement_le_p])
    have hEHnew : positivePart (C.theta H-(C.theta E+O.movement))=
        C.theta H-(C.theta E+O.movement) := max_eq_left (by linarith [O.movement_le_p])
    have heq : positiveVariation C.theta-
        positiveVariation (Function.update C.theta E (C.theta E+O.movement))=O.movement := by
      have hV : ∀ θ : Vertex → ℝ, positiveVariation θ=
          positivePart (θ G-θ H)+positivePart (θ A-θ G)+positivePart (θ B-θ A)+
          positivePart (θ T-θ B)+positivePart (θ D-θ T)+positivePart (θ E-θ D)+
          positivePart (θ H-θ E) := fun θ => by
        simp only [positiveVariation,Fin.sum_univ_seven,delta,next]; rfl
      rw [hV,hV]
      simp only [Function.update_self,Function.update_of_ne (show H≠E by decide),
        Function.update_of_ne (show G≠E by decide),Function.update_of_ne (show A≠E by decide),
        Function.update_of_ne (show B≠E by decide),Function.update_of_ne (show T≠E by decide),
        Function.update_of_ne (show D≠E by decide)]
      rw [hDEold,hDEnew,hEHold,hEHnew]
      ring
    linarith [O.movement_nonneg]

def NegativeEHEndpoint.toCycle {q : ℝ} {C : SignedCycle}
    (O : NegativeEHEndpoint q (C.point D) (C.point E) (C.point H)
      (C.theta E-C.theta D) (C.theta E-C.theta H))
    (hDEpos : C.theta D<C.theta E) : CycleMove q C where
  point := O.point
  theta := C.theta D
  sorted := O.sorted
  contained := O.contained
  core := O.core
  nonpos := O.nonpos
  frame_range := ⟨min_le_right _ _,le_max_right _ _⟩
  de := 2
  eh := 1
  de_allowed := Or.inl rfl
  eh_allowed := Or.inr rfl
  DE := by simpa using O.DE2
  EH := by convert O.EH1 using 1; ring
  positive_nonincrease := by
    have hDEold : positivePart (C.theta E-C.theta D)=C.theta E-C.theta D :=
      max_eq_left (sub_nonneg.mpr hDEpos.le)
    have hDEnew : positivePart (C.theta D-C.theta D)=0 := by simp
    have hEHold : positivePart (C.theta H-C.theta E)=0 :=
      max_eq_right (by linarith [O.negative_remaining])
    have hEHnew : positivePart (C.theta H-C.theta D)=0 :=
      max_eq_right (by linarith [O.negative_remaining])
    have heq : positiveVariation C.theta-
        positiveVariation (Function.update C.theta E (C.theta D))=C.theta E-C.theta D := by
      have hV : ∀ θ : Vertex → ℝ, positiveVariation θ=
          positivePart (θ G-θ H)+positivePart (θ A-θ G)+positivePart (θ B-θ A)+
          positivePart (θ T-θ B)+positivePart (θ D-θ T)+positivePart (θ E-θ D)+
          positivePart (θ H-θ E) := fun θ => by
        simp only [positiveVariation,Fin.sum_univ_seven,delta,next]; rfl
      rw [hV,hV]
      simp only [Function.update_self,Function.update_of_ne (show H≠E by decide),
        Function.update_of_ne (show G≠E by decide),Function.update_of_ne (show A≠E by decide),
        Function.update_of_ne (show B≠E by decide),Function.update_of_ne (show T≠E by decide),
        Function.update_of_ne (show D≠E by decide)]
      rw [hDEold,hDEnew,hEHold,hEHnew]
      ring
    linarith

/-- Selecting a secondary owner again at the same state is also a move at the same radius. -/
def identityMove {q : ℝ} (I : SignedCycle.NormalizedBoundaryInput q)
    (hc : (I.cycle.point E).Core) (de eh : Fin 4)
    (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hDE : I.cycle.Feasible D de) (hEH : I.cycle.Feasible E eh) : CycleMove q I.cycle where
  point := I.cycle.point E
  theta := I.cycle.theta E
  sorted := I.necessary.sorted E
  contained := I.necessary.contained E
  core := hc
  nonpos := I.E_nonpos
  frame_range := ⟨min_le_left _ _,le_max_left _ _⟩
  de := de
  eh := eh
  de_allowed := hde
  eh_allowed := heh
  DE := by
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,
      delta,next,D,E,quarterFeasible,sub_nonneg] using hDE
  EH := by
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,
      delta,next,H,E,quarterFeasible,sub_nonneg] using hEH
  positive_nonincrease := by simp

end NegativeCoreE
end SquaresInCircles.Eight
end
end
end

section
/-!
## The negative-TD charge dominates the middle norm

The trigonometric charge `J z = (13/12) sin z - (2/5)(1 - cos z)` dominates the middle norm
`V TD0Span.lambda z` on `[0, 3/10]`, strictly at nonzero angle (`charge_lower`, `charge_strict`).
A comparison of positive squares reduces this to one rational polynomial on `[0, 3/10]`, a positive
combination of products of `z` and `3/10 - z` (`polynomial_positive`). The bounds on the
coordinates of T come from BT2, TD2 and the avoidance of the core (`actual_negative_cuts`).
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.NegativeTDSpanCharge
open Polynomial SpanNormBounds TD0Span

def J (z : ℝ) : ℝ := (13/12)*Real.sin z-(2/5)*(1-Real.cos z)

def S5 : ℚ[X] := X-C (1/6)*X^3+C (1/120)*X^5
def S7 : ℚ[X] := S5-C (1/5040)*X^7
def lowerA : ℚ[X] := C (13/12)*S7+C (3/5)*(C (1/2)*X^2-C (1/24)*X^4)
def upperA : ℚ[X] := C (13/12)*S5+C (3/10)*X^2
def numerator : ℚ[X] :=
  C (2*(1978787/1000000)*(596343/500000))*lowerA-
    C (2*(9789/2500)*(13/20))*S5-upperA^2

/-- `numerator` vanishes at `0`, and `numerator / z` has positive Bernstein coefficients of
degree nine on `[0, 3/10]`: `numerator` is a positive combination of `z` and the products
`z^(i+1) (3/10 - z)^(9-i)`, which `linarith` finds. -/
theorem polynomial_positive {z : ℝ} (hz : z∈Ioc 0 (3/10:ℝ)) :
    0<aeval z numerator := by
  have h0 := hz.1.le
  have h1 : 0≤3/10-z := sub_nonneg.2 hz.2
  simp only [numerator,lowerA,upperA,S7,S5,map_sub,map_add,map_mul,map_pow,aeval_C,aeval_X,
    eq_ratCast]
  push_cast
  linarith [hz.1,mul_nonneg h0 (pow_nonneg h1 9),mul_nonneg (pow_nonneg h0 2) (pow_nonneg h1 8),
    mul_nonneg (pow_nonneg h0 3) (pow_nonneg h1 7),mul_nonneg (pow_nonneg h0 4) (pow_nonneg h1 6),
    mul_nonneg (pow_nonneg h0 5) (pow_nonneg h1 5),mul_nonneg (pow_nonneg h0 6) (pow_nonneg h1 4),
    mul_nonneg (pow_nonneg h0 7) (pow_nonneg h1 3),mul_nonneg (pow_nonneg h0 8) (pow_nonneg h1 2),
    mul_nonneg (pow_nonneg h0 9) h1,pow_nonneg h0 10]

theorem lowerA_nonneg {z : ℝ} (hz : z∈Icc 0 (3/10:ℝ)) :
    0≤aeval z lowerA := by
  have hz2 := pow_le_pow_left₀ hz.1 hz.2 2
  have hz6 := pow_le_pow_left₀ hz.1 hz.2 6
  have hp : 0≤(13/12)*(1-z^2/6+z^4/120-z^6/5040)+
      (3/5)*z*(1/2-z^2/24) := by
    have hm := mul_nonneg hz.1 (show 0≤1/2-z^2/24 by nlinarith)
    nlinarith [pow_nonneg hz.1 4]
  have he : aeval z lowerA=z*((13/12)*(1-z^2/6+z^4/120-z^6/5040)+
      (3/5)*z*(1/2-z^2/24)) := by simp [lowerA,S7,S5]; ring
  rw [he]
  exact mul_nonneg hz.1 hp

/-- At every angle `0 < z ≤ 3/10` the trigonometric charge strictly exceeds the middle norm. -/
theorem charge_strict {z : ℝ} (hz : z∈Ioc 0 (3/10:ℝ)) :
    V TD0Span.lambda z<J z := by
  obtain ⟨a,ha⟩ : ∃ a : ℝ,a=(13/12)*Real.sin z+(3/5)*(1-Real.cos z) := ⟨_,rfl⟩
  have hzi : z∈Icc 0 frameCap := ⟨hz.1.le,by simp only [frameCap]; linarith [hz.2]⟩
  have hsi := (transport_trig hzi).2.2.1
  have hcos1 := Real.cos_le_one z
  have ha0 : 0≤a := by rw [ha]; nlinarith
  have hlow : aeval z lowerA≤a := by
    have hs := sin_lower_seven hz.1.le
    have hc := cos_upper_four hz.1.le
    have he : aeval z lowerA=(13/12)*(z-z^3/6+z^5/120-z^7/5040)+
        (3/5)*(z^2/2-z^4/24) := by simp [lowerA,S7,S5]; ring
    rw [he,ha]
    linarith
  have hupp : a≤aeval z upperA := by
    have hs := sin_upper_five hz.1.le
    have hc := Real.one_sub_sq_div_two_le_cos (x := z)
    have he : aeval z upperA=(13/12)*(z-z^3/6+z^5/120)+(3/10)*z^2 := by
      simp [upperA,S5]; ring
    rw [he,ha]
    linarith
  have halow0 := lowerA_nonneg ⟨hz.1.le,hz.2⟩
  have hs5 : Real.sin z≤aeval z S5 := by
    have he : aeval z S5=z-z^3/6+z^5/120 := by simp [S5]; ring
    rw [he]
    exact sin_upper_five hz.1.le
  have hN0 := fixed_norm_bounds.1
  have hR0 : 0<R := by linarith [radius_bounds.1]
  have hcoeff : (2*(1978787/1000000)*(596343/500000):ℝ)≤
      2*R*N TD0Span.lambda 0 := by
    have hmul := mul_le_mul radius_bounds.1.le hN0.le (by norm_num) hR0.le
    simp only [TD0Span.lambda]
    linarith
  have hmain := mul_le_mul hcoeff hlow halow0 (by positivity : 0≤2*R*N TD0Span.lambda 0)
  have hsin := mul_le_mul_of_nonneg_left hs5
    (show 0≤2*qCap*TD0Span.lambda by norm_num [qCap,TD0Span.lambda])
  have hasq := pow_le_pow_left₀ ha0 hupp 2
  have hp := polynomial_positive hz
  have hpos : 0<2*R*N TD0Span.lambda 0*a-
      2*qCap*TD0Span.lambda*Real.sin z-a^2 := by
    simp only [numerator,map_sub,map_mul,map_pow,aeval_C,eq_ratCast] at hp
    push_cast at hp
    simp only [qCap,TD0Span.lambda] at hsin ⊢
    linarith
  have hzabs : |-z|≤frameCap := by rw [abs_neg,abs_of_pos hz.1]; exact hzi.2
  have hNsq := N_sq (show (0:ℝ)<TD0Span.lambda by norm_num [TD0Span.lambda]) hzabs
  have hN0sq := N_sq (show (0:ℝ)<TD0Span.lambda by norm_num [TD0Span.lambda])
    (show |(0:ℝ)|≤frameCap by norm_num [frameCap])
  have hR2 : R^2=qCap := Real.sq_sqrt (by norm_num [qCap])
  have hn2 : (R*N TD0Span.lambda (-z))^2=
      qCap*(1+TD0Span.lambda^2-2*TD0Span.lambda*Real.sin z) := by
    rw [mul_pow,hR2,hNsq,Real.sin_neg]
    ring
  have hn02 : (R*N TD0Span.lambda 0)^2=qCap*(1+TD0Span.lambda^2) := by
    rw [mul_pow,hR2,hN0sq,Real.sin_zero]
    ring
  have hnonneg : 0≤R*N TD0Span.lambda (-z) := mul_nonneg hR0.le (Real.sqrt_nonneg _)
  have hgain : R*N TD0Span.lambda 0-a<R*N TD0Span.lambda (-z) := by
    by_contra! hbad
    have hsquare := pow_le_pow_left₀ hnonneg hbad 2
    have hexp : (R*N TD0Span.lambda 0-a)^2=
        (R*N TD0Span.lambda 0)^2-2*R*N TD0Span.lambda 0*a+a^2 := by ring
    linarith
  have hV : V TD0Span.lambda z=(Real.cos z-1)-
      (R*N TD0Span.lambda (-z)-R*N TD0Span.lambda 0) := by
    simp only [SpanNormBounds.V,OrdinaryAngleConcavity.V,SpanNormBounds.N]
    ring
  rw [hV,J]
  linarith

theorem charge_lower {z : ℝ} (hz : z∈Icc 0 (3/10:ℝ)) :
    V TD0Span.lambda z≤J z := by
  rcases eq_or_lt_of_le hz.1 with hz0 | hz0
  · simp [← hz0,J,SpanNormBounds.V,OrdinaryAngleConcavity.V]
  · exact (charge_strict ⟨hz0,hz.2⟩).le

/-- BT2 and TD2 give `1/10 < T.y < 83/200`, `7/12 ≤ T.a` and `z < 3/10`; T need not lie on the
boundary. -/
theorem actual_negative_cuts {q z v : ℝ} {B T D : SignedPoint}
    (hBs : B.Sorted) (hTs : T.Sorted) (hDs : D.Sorted)
    (hBc : B.Contained q) (hDc : D.Contained q)
    (hTc : T.AvoidsCore) (hDc0 : D.AvoidsCore) (hq : q≤qCap)
    (hyD : D.y≤0) (hz : z∈Ioc 0 frameCap)
    (hBT : quarterFeasible B T v 2) (hTD : zeroFeasible T D (-z) 2) :
    1/10<T.y ∧ T.y<83/200 ∧ 7/12≤T.a ∧ z<3/10 := by
  obtain ⟨hy,hyu,hsum,hyD'⟩ := NegativeTEntry.negative_TD_signs
    hBs hTs hDs hBc hDc hDc0 hq hyD hz hBT hTD
  have hDu := (SignedPoint.coordinate_bounds hDs hDc0 hDc hq).2.2
  rw [abs_of_nonpos hyD] at hDu
  have hyl : 1/10<T.y := by linarith
  have haHalf := SignedPoint.primary_gt_half hTs hTc
  have hcore := hTc
  simp only [SignedPoint.AvoidsCore,SignedPoint.coreDistance,abs_of_pos hy,
    max_eq_left (by linarith : 0≤T.a-1/2),max_eq_right (by linarith : T.y-1/2≤0)] at hcore
  have ha : 7/12≤T.a := by nlinarith
  have hzi : z∈Icc 0 frameCap := ⟨hz.1.le,hz.2⟩
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hzi
  have h1 := mul_le_mul_of_nonneg_right ha hs0
  have h2 := mul_lt_mul_of_pos_right hyu (show 0<Real.cos z by linarith)
  have hh : edgeWidth (-z)≤T.a*Real.sin (-z)+T.y*Real.cos (-z)-D.y := hTD
  rw [edgeWidth_negative_formula hzi,Real.sin_neg,Real.cos_neg] at hh
  have hmargin : (17/200)*Real.cos z+(13/12)*Real.sin z<2/5 := by linarith
  have hshort : z<3/10 := by
    by_contra! hbad
    have hm := NegativeTEntry.TD_short_harmonic_mono.monotoneOn
      (⟨by norm_num,by norm_num [frameCap]⟩ : (3/10:ℝ)∈Icc 0 frameCap) hzi hbad
    have hc3 := cos_lower_six (show (0:ℝ)≤3/10 by norm_num)
    have hs3 := sin_lower_seven (show (0:ℝ)≤3/10 by norm_num)
    norm_num at hc3 hs3 hm
    linarith
  exact ⟨hyl,hyu,ha,hshort⟩

end SquaresInCircles.Eight.NegativeTDSpanCharge
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate ActualCoreEBlocks
namespace NegativeCoreE

theorem CycleMove.primary_DE {q : ℝ} {C : SignedCycle} (O : CycleMove q C) :
    primaryDE O.cycle O.de=if O.de=3 then O.theta-C.theta D else 0 := by
  simp [primaryDE,CycleMove.cycle,replacePoint,delta,next,D,E]

theorem CycleMove.primary_EH {q : ℝ} {C : SignedCycle} (O : CycleMove q C) :
    primaryEH O.cycle O.eh=if O.eh=1 then C.theta H-O.theta else 0 := by
  simp [primaryEH,CycleMove.cycle,replacePoint,delta,next,H,E]

theorem CycleMove.total {q : ℝ} {C : SignedCycle} (O : CycleMove q C) :
    eTotal O.cycle O.de O.eh=
      (if O.de=3 then O.theta-C.theta D else 0)+
      (if O.eh=1 then C.theta H-O.theta else 0) := by
  rw [eTotal,O.primary_DE,O.primary_EH]

structure Reduction (q : ℝ) (I : SignedCycle.NormalizedBoundaryInput q) where
  move : CycleMove q I.cycle
  normal_form : 0≤eTotal move.cycle move.de move.eh ∨
    (move.point.a=7/12 ∧ primaryDE move.cycle move.de≤0 ∧ primaryEH move.cycle move.eh≤0)

/-- With an EH0 witness at E, selecting it again at the same state gives a reduction; the DE error
then decides which stress family applies. -/
theorem reduce_with_secondary {q : ℝ} (I : SignedCycle.NormalizedBoundaryInput q)
    (hq : q≤qCap) (hc : (I.cycle.point E).Core)
    (hEH : I.cycle.Feasible E 0) : Nonempty (Reduction q I) := by
  let de := I.witnesses.owner D
  have hde : de=2 ∨ de=3 := by
    simpa [de,SignedCycle.normalOwners,D] using I.witnesses.allowed D
  let O := identityMove I hc de 0 hde (Or.inl rfl) (I.witnesses.feasible D) hEH
  have hEH' : quarterFeasible (I.cycle.point E) (I.cycle.point H)
      (I.cycle.theta H-I.cycle.theta E) 0 := by
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,
      delta,next,H,E,quarterFeasible,sub_nonneg] using hEH
  have hf := (secondary_flat (I.necessary.sorted E) I.E_nonpos hc
    (I.necessary.sorted H) (I.necessary.contained H) hq hEH').1
  refine ⟨⟨O,?_⟩⟩
  by_cases hpos : 0≤primaryDE O.cycle O.de
  · left
    rw [eTotal,O.primary_EH]
    simpa [O,identityMove] using hpos
  · right
    refine ⟨hf,le_of_lt (lt_of_not_ge hpos),?_⟩
    rw [O.primary_EH]
    norm_num [O,identityMove]

/-- Every negative E-primary total has a reduction at the same `q`, by the owners and signs at E;
the two mixed cases use the endpoint on the core arc and the endpoint of the flat gap. -/
theorem reduce_negative_total {q : ℝ} (I : SignedCycle.NormalizedBoundaryInput q)
    (hqL : qLow≤q) (hqU : q≤qCap) (hc : (I.cycle.point E).Core)
    (hneg : eTotal I.cycle (I.witnesses.owner D) (I.witnesses.owner E)<0) :
    Nonempty (Reduction q I) := by
  by_cases hEH0 : I.cycle.Feasible E 0
  · exact reduce_with_secondary I hqU hc hEH0
  let C := I.cycle
  have hnE : next E=H := by decide
  have hnD : next D=E := by decide
  have heh : I.witnesses.owner E=1 := by
    have hh : I.witnesses.owner E=0 ∨ I.witnesses.owner E=1 := by
      simpa [SignedCycle.normalOwners,E] using I.witnesses.allowed E
    rcases hh with hh | hh
    · exact False.elim (hEH0 (by simpa [hh] using I.witnesses.feasible E))
    · exact hh
  have hde : I.witnesses.owner D=2 ∨ I.witnesses.owner D=3 := by
    simpa [SignedCycle.normalOwners,D] using I.witnesses.allowed D
  have hEH : quarterFeasible (C.point E) (C.point H) (C.theta H-C.theta E) 1 := by
    have hh : C.Feasible E 1 := by simpa [C,heh] using I.witnesses.feasible E
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,
      delta,next,H,E,quarterFeasible,sub_nonneg] using hh
  have hnot : ¬quarterFeasible (C.point E) (C.point H) (C.theta H-C.theta E) 0 := by
    intro hh
    apply hEH0
    simpa [C,SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,
      delta,next,H,E,quarterFeasible,sub_nonneg] using hh
  have hsmall (i : Vertex) : |delta C.theta i|≤frameCap := I.necessary.spread (next i) i
  have hflat {n : ℝ} (hn : n∈Ioc 0 frameCap)
      (heq : C.theta H-C.theta E= -n) : (C.point E).a=7/12 :=
    (genuine_negative_flat (I.necessary.sorted E) I.E_nonpos hc
      (I.necessary.sorted H) I.anchors_normal.H_nonneg (I.necessary.contained H)
      hqU hn (by simpa only [heq] using hEH)
      (by simpa only [heq] using hnot)).1
  rcases hde with hde | hde
  · have hr : C.theta H-C.theta E<0 := by
      have hh := hneg
      simp only [eTotal,primaryDE,primaryEH,hde,heh] at hh
      norm_num at hh
      simpa only [delta,hnE] using hh
    have hn : C.theta E-C.theta H∈Ioc 0 frameCap :=
      ⟨by linarith,(le_abs_self _).trans (I.necessary.spread E H)⟩
    have hf := hflat hn (by ring)
    let O := identityMove I hc 2 1 (Or.inl rfl) (Or.inr rfl)
      (by simpa [hde] using I.witnesses.feasible D)
      (by simpa [heh] using I.witnesses.feasible E)
    refine ⟨⟨O,Or.inr ⟨hf,?_,?_⟩⟩⟩
    · rw [O.primary_DE]; norm_num [O,identityMove]
    · rw [O.primary_EH]; simpa [O,identityMove,C] using hr.le
  · have hsum : C.theta H-C.theta D<0 := by
      have hh := hneg
      simp only [eTotal,primaryDE,primaryEH,hde,heh] at hh
      norm_num at hh
      simp only [delta,hnE,hnD] at hh
      linarith
    have hDE : quarterFeasible (C.point D) (C.point E) (C.theta E-C.theta D) 3 := by
      have hh : C.Feasible D 3 := by simpa [C,hde] using I.witnesses.feasible D
      simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,
        delta,next,D,E,quarterFeasible,sub_nonneg] using hh
    by_cases hEHneg : C.theta H<C.theta E
    · have hn : C.theta E-C.theta H∈Ioc 0 frameCap :=
        ⟨sub_pos.mpr hEHneg,(le_abs_self _).trans (I.necessary.spread E H)⟩
      have hf := hflat hn (by ring)
      by_cases hDEpos : C.theta D<C.theta E
      · obtain ⟨P⟩ := negative_EH_endpoint hqL hqU
          (I.necessary.sorted D) (I.necessary.core D) (I.anchors_outer D (by simp))
          (I.necessary.sorted H) (I.necessary.core H) I.anchors_normal.H_nonneg
          (I.necessary.contained H) (I.necessary.sorted E) I.E_nonpos hc hn
          ⟨sub_pos.mpr hDEpos,by linarith⟩ hDE
          (by simpa only [neg_sub] using hEH) (by simpa only [neg_sub] using hnot)
        let O := P.toCycle hDEpos
        refine ⟨⟨O,Or.inr ⟨P.flat,?_,?_⟩⟩⟩
        · rw [O.primary_DE]; norm_num [O,NegativeEHEndpoint.toCycle]
        · rw [O.primary_EH]
          simpa [O,NegativeEHEndpoint.toCycle] using hsum.le
      · let O := identityMove I hc 3 1 (Or.inr rfl) (Or.inr rfl)
          (by simpa [hde] using I.witnesses.feasible D)
          (by simpa [heh] using I.witnesses.feasible E)
        refine ⟨⟨O,Or.inr ⟨hf,?_,?_⟩⟩⟩
        · rw [O.primary_DE]
          simpa [O,identityMove,C] using sub_nonpos.mpr (le_of_not_gt hDEpos)
        · rw [O.primary_EH]
          simpa [O,identityMove,C] using (sub_neg.mpr hEHneg).le
    · have hp : 0<C.theta H-C.theta E := by
        have hr0 : 0≤C.theta H-C.theta E := sub_nonneg.mpr (le_of_not_gt hEHneg)
        apply lt_of_le_of_ne hr0
        intro heq
        apply hnot
        rw [← heq] at hEH ⊢
        simp only [quarterFeasible,quarterProjection,Real.cos_zero,Real.sin_zero] at hEH ⊢
        norm_num at hEH ⊢
        linarith
      have hn : C.theta D-C.theta E∈Ioc 0 frameCap :=
        ⟨by linarith,(le_abs_self _).trans (I.necessary.spread D E)⟩
      obtain ⟨P⟩ := negative_DE_endpoint hqL hqU (I.necessary.sorted H)
        I.anchors_normal.H_nonneg (I.anchors_outer H (by simp))
        (I.necessary.sorted E) I.E_nonpos hc hn ⟨hp,by linarith⟩
        (by simpa only [neg_sub] using hDE) hEH
      let O := P.toCycle
      refine ⟨⟨O,Or.inr ⟨P.flat,?_,?_⟩⟩⟩
      · rw [O.primary_DE]
        simp only [O,NegativeDEEndpoint.toCycle,ite_true]
        linarith [P.negative_remaining]
      · rw [O.primary_EH]; norm_num [O,NegativeDEEndpoint.toCycle]


end NegativeCoreE
end SquaresInCircles.Eight
end
end
end
