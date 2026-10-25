module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Boundary.SourceEquality
public import SquaresInCircles.Eight.Owners.ScalarRadicalTransfer
public import SquaresInCircles.Eight.Owners.Hard.ZeroEReflection
public import SquaresInCircles.Eight.Owners.Nonpositive.DE2PrimaryBound
public import SquaresInCircles.Eight.Owners.Nonpositive.MixedE

/-!
# Eight squares: strict original E-circle loss after the rotated DE2 descent

At the actual E=D contact, the primary
decreases by an explicit amount bounded by its sorting margin and the
strict actual EH reserve.  DE remains exact.  The resulting same-q
hard cycle keeps all non-E points and frames literal, and its E circle
is strictly smaller than the original source E circle.
-/

section
/-!
## A primary E below D reaches D with two strict margins

When the frame of E is below that of D, a first move on the circle creates a positive common
reserve, and minimizing over a compact set keeps that reserve on the original circle of E. At each
state on the floor of the tangent the necessary seven-cycle is built again and the exclusion of E
at zero applies. So the least frame reaches D, where both primary margins stay strictly positive
(`HardInput.nonpositive_below_primary_state`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SignedCycle
open Candidate

theorem HardInput.nonpositive_below_primary_state {q : ℝ}
    (I : HardInput q) (hqL : qLow≤q) (hq : q≤qTrial)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hHG : I.cycle.Feasible H 0) (hTD : I.cycle.Feasible T 2)
    (hED : I.cycle.theta E<I.cycle.theta D)
    (hDE3 : I.cycle.Feasible D 3) :
    ∃P : EInteriorGeometry.State,
      EInteriorGeometry.Feasible (I.cycle.point H).a (I.cycle.point D).a
        (I.cycle.theta H-I.cycle.theta D) q P ∧
      P.2.2=0 ∧ EInteriorGeometry.corner P=(I.cycle.point E).circle ∧
      P.2.1∈Ioc 0 (-(I.cycle.point E).y) ∧
      EInteriorGeometry.W P.2.2<EInteriorGeometry.deValue (I.cycle.point D).a P ∧
      EInteriorGeometry.W (I.cycle.theta H-I.cycle.theta D-P.2.2)<
        EInteriorGeometry.ehValue (I.cycle.point H).a (I.cycle.theta H-I.cycle.theta D) P := by
  have hcap : q≤qCap := hq.trans (by norm_num [qTrial,qCap])
  have hbounds := I.nonpositive_composite_bounds hcap hAB hAG hGH hDT hTB hHG hTD
  have hrad := I.nonpositive_E_radial hcap hAB hAG hGH hDT hTB hHG hTD
  have hsource_negative := I.nonpositive_E_strict_negative hqL hq hAB hnorm
    hAG hGH hDT hTB hHG hTD
  have hEHorder : I.cycle.theta E≤I.cycle.theta H :=
    hED.le.trans (sub_nonneg.mp hbounds.span_nonneg)
  have hEH1 := I.nonpositive_EH_primary_of_nonneg hcap hAB hAG hGH hDT hTB hHG hTD hEHorder
  let α := I.cycle.theta H-I.cycle.theta D
  let p₀ := I.cycle.theta H-I.cycle.theta E
  let b₀ := -(I.cycle.point E).y
  let f := OriginalECircle.eh (I.cycle.point E) (I.cycle.point H)
  let g := OriginalECircle.de (I.cycle.point E) (I.cycle.point D) α
  have hα : 0≤α := hbounds.span_nonneg
  have hp₀ : α<p₀ := by dsimp [α,p₀]; linarith
  have hp₀u : p₀≤7/10 := (le_abs_self _).trans (I.necessary.spread H E)
  have hb₀ : 0<b₀ := neg_pos.mpr hsource_negative
  have hEHraw : quarterFeasible (I.cycle.point E) (I.cycle.point H) p₀ 1 := by
    simpa [p₀,Feasible,slack,edge,word,delta,next,E,H,quarterFeasible,sub_nonneg] using hEH1
  have hDEraw : quarterFeasible (I.cycle.point D) (I.cycle.point E) (-(p₀-α)) 3 := by
    have heq : -(p₀-α)=I.cycle.theta E-I.cycle.theta D := by dsimp [p₀,α]; ring
    simpa [heq,Feasible,slack,edge,word,delta,next,D,E,quarterFeasible,sub_nonneg] using hDE3
  have hf₀ : 0≤f p₀ b₀ := by
    dsimp [f,b₀]
    rw [OriginalECircle.eh_actual _ _ _ ⟨by linarith,hp₀u⟩,
      OriginalECircle.initial (I.necessary.sorted E) I.E_nonpos]
    exact sub_nonneg.mpr hEHraw
  have hg₀ : 0≤g p₀ b₀ := by
    dsimp [g,b₀]
    rw [OriginalECircle.de_actual _ _ _ _ ⟨by linarith,by linarith⟩,
      OriginalECircle.initial (I.necessary.sorted E) I.E_nonpos]
    exact sub_nonneg.mpr hDEraw
  obtain ⟨p₁,b₁,hp₁,hb₁,hf₁,hg₁⟩ := OriginalECircle.improving_shift
    (I.necessary.sorted E) I.E_nonpos hrad.1 hα hp₀ hp₀u
    ⟨hb₀,le_rfl⟩ hf₀ hg₀
  let η : ℝ := min (f p₁ b₁) (g p₁ b₁)/2
  have hη : 0<η := div_pos (lt_min hf₁ hg₁) (by norm_num)
  have hηf : η≤f p₁ b₁ := by
    have hh := min_le_left (f p₁ b₁) (g p₁ b₁)
    dsimp [η]
    linarith
  have hηg : η≤g p₁ b₁ := by
    have hh := min_le_right (f p₁ b₁) (g p₁ b₁)
    dsimp [η]
    linarith
  have hprimary := OriginalECircle.continuous_primary (I.cycle.point E)
  have hcf : Continuous (fun z : ℝ×ℝ => f z.1 z.2) := by
    dsimp [f,OriginalECircle.eh]
    fun_prop
  have hcg : Continuous (fun z : ℝ×ℝ => g z.1 z.2) := by
    dsimp [g,OriginalECircle.de]
    fun_prop
  let S : Set (ℝ×ℝ) :=
    ((Icc α p₁ ×ˢ Icc 0 b₀) ∩ {z | η≤f z.1 z.2}) ∩ {z | η≤g z.1 z.2}
  have hcompact : IsCompact S :=
    ((isCompact_Icc.prod isCompact_Icc).inter_right
      (isClosed_le continuous_const hcf)).inter_right
      (isClosed_le continuous_const hcg)
  have hstart : (p₁,b₁)∈S :=
    ⟨⟨⟨⟨hp₁.1.le,le_rfl⟩,⟨hb₁.1.le,hb₁.2⟩⟩,hηf⟩,hηg⟩
  obtain ⟨z,hz,hmin⟩ := hcompact.exists_isMinOn ⟨(p₁,b₁),hstart⟩
    continuous_fst.continuousOn
  let m := z.1
  let b := z.2
  have hm : m∈Icc α p₁ := hz.1.1.1
  have hb : b∈Icc 0 b₀ := hz.1.1.2
  have hf : η≤f m b := hz.1.2
  have hg : η≤g m b := hz.2
  have hmp₀ : m≤p₀ := hm.2.trans hp₁.2.le
  have hmpositive : m∈Icc 0 (7/10:ℝ) := ⟨hα.trans hm.1,hmp₀.trans hp₀u⟩
  have hmn : m-α∈Icc 0 (7/10:ℝ) := ⟨by linarith [hm.1],by linarith [hmpositive.2]⟩
  have hgeom := OriginalECircle.geometry (I.necessary.sorted E) I.E_nonpos hrad.1 hb
  have hbpositive : 0<b := by
    by_contra! hbad
    have hbzero : b=0 := le_antisymm hbad hb.1
    let p := OriginalECircle.point (I.cycle.point E) b
    let θ := I.cycle.theta H-m
    have hpq : p.Contained q := hgeom.2.2.1.trans_le (I.necessary.contained E)
    have hpnonpos : p.y≤0 := neg_nonpos.mpr hb.1
    have hprad : max |(I.cycle.point H).y| |(I.cycle.point D).y|≤p.a :=
      hrad.2.trans hgeom.2.2.2
    have hθ : θ∈Icc (I.cycle.theta E) (I.cycle.theta D) := by
      dsimp [θ]
      have hleft : m≤I.cycle.theta H-I.cycle.theta E := hmp₀
      have hright : I.cycle.theta H-I.cycle.theta D≤ m := hm.1
      constructor <;> linarith
    have hDE : quarterFeasible (I.cycle.point D) p (θ-I.cycle.theta D) 3 := by
      have hh : 0≤OriginalECircle.de (I.cycle.point E) (I.cycle.point D) α m b :=
        hη.le.trans hg
      rw [OriginalECircle.de_actual _ _ _ _ hmn] at hh
      have heq : θ-I.cycle.theta D= -(m-α) := by dsimp [θ,α]; ring
      rw [heq]
      exact sub_nonneg.mp hh
    have hEH : quarterFeasible p (I.cycle.point H) (I.cycle.theta H-θ) 1 := by
      have hh : 0≤OriginalECircle.eh (I.cycle.point E) (I.cycle.point H) m b := hη.le.trans hf
      rw [OriginalECircle.eh_actual _ _ _ hmpositive] at hh
      have heq : I.cycle.theta H-θ=m := by dsimp [θ]; ring
      rw [heq]
      exact sub_nonneg.mp hh
    let J := I.fromBelowEPrimary hgeom.1 hpq hgeom.2.1 hpnonpos hprad hθ hDE hEH
    have hfixed (i : Vertex) (hi : i≠E) :
        J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i :=
      belowEPrimaryCycle_unchanged I.cycle p θ i hi
    have hH := hfixed H (by decide)
    have hG := hfixed G (by decide)
    have hA := hfixed A (by decide)
    have hB := hfixed B (by decide)
    have hT := hfixed T (by decide)
    have hD := hfixed D (by decide)
    have hJHG : J.cycle.Feasible H 0 :=
      (replacePoint_other_feasible (v := E) (by decide : H≠E) (by decide : next H≠E)).2 hHG
    have hJTD : J.cycle.Feasible T 2 :=
      (replacePoint_other_feasible (v := E) (by decide : T≠E) (by decide : next T≠E)).2 hTD
    have hJnegative := J.nonpositive_E_strict_negative hqL hq
      (by rw [hA.2,hB.2]; exact hAB)
      (by rw [hA.1,hB.1]; exact hnorm)
      (by rw [hA.2,hG.2]; exact hAG)
      (by rw [hG.2,hH.2]; exact hGH)
      (by rw [hD.2,hT.2]; exact hDT)
      (by rw [hT.2,hB.2]; exact hTB) hJHG hJTD
    change -b<0 at hJnegative
    linarith
  have hmα : m=α := by
    apply le_antisymm _ hm.1
    by_contra! hαm
    obtain ⟨p',b',hp',hb',hf',hg'⟩ := OriginalECircle.improving_shift
      (I.necessary.sorted E) I.E_nonpos hrad.1 hα hαm hmpositive.2
      ⟨hbpositive,hb.2⟩ hf hg
    have hz' : (p',b')∈S :=
      ⟨⟨⟨⟨hp'.1.le,hp'.2.le.trans hm.2⟩,⟨hb'.1.le,hb'.2⟩⟩,hf'.le⟩,hg'.le⟩
    have hh : m≤p' := hmin hz'
    exact (not_le_of_gt hp'.2) hh
  let P : EInteriorGeometry.State := (OriginalECircle.primary (I.cycle.point E) b,b,0)
  have hPcircle : EInteriorGeometry.corner P=(I.cycle.point E).circle := by
    have hh := hgeom.2.2.1
    simpa [P,EInteriorGeometry.corner,OriginalECircle.point,SignedPoint.circle,
      abs_neg,abs_of_nonneg hb.1] using hh
  have hPDE : EInteriorGeometry.W P.2.2<EInteriorGeometry.deValue (I.cycle.point D).a P := by
    have hh : 0<g α b := hη.trans_le (by simpa only [hmα] using hg)
    dsimp [g,OriginalECircle.de] at hh
    dsimp [P,EInteriorGeometry.W,EInteriorGeometry.deValue]
    simp only [sub_self,Real.sin_zero,Real.cos_zero,mul_zero,mul_one,sub_zero,add_zero] at *
    linarith
  have hPEH : EInteriorGeometry.W (α-P.2.2)<EInteriorGeometry.ehValue (I.cycle.point H).a α P := by
    have hh : 0<f α b := hη.trans_le (by simpa only [hmα] using hf)
    dsimp [f,OriginalECircle.eh,P,EInteriorGeometry.W,EInteriorGeometry.ehValue] at *
    simp only [sub_zero,Real.sin_zero,Real.cos_zero] at *
    linarith
  refine ⟨P,?_,rfl,hPcircle,⟨hbpositive,hb.2⟩,hPDE,hPEH⟩
  exact {
    b_nonneg := hb.1
    sorted := by simpa [P,OriginalECircle.point,abs_neg,abs_of_nonneg hb.1] using hgeom.1.2
    angle := ⟨le_rfl,hα⟩
    circle := hPcircle.trans_le (I.necessary.contained E)
    DE := hPDE.le
    EH := hPEH.le }

end SquaresInCircles.Eight.SignedCycle
end
end
end

section
/-!
## Strict original-circle loss for an E below D with primary DE3

The original-circle descent reaches D with
strict actual DE slack.  An explicit positive tangent decrease keeps
that frame, improves EH, and strictly reduces E's original circle.
The resulting necessary cycle retains H,A,B,D and all intermediate
points and frames literally, so every earlier anchor loss survives.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace EInteriorGeometry

theorem lower_tangent_at_D {h d α q : ℝ} {P : State}
    (hα : α≤7/10) (hp : Feasible h d α q P) (hPangle : P.2.2=0)
    (hb : 0<P.2.1) (hDE : W P.2.2<deValue d P) :
    ∃Q : State, Feasible h d α q Q ∧ Q.2.2=0 ∧ Q.1=P.1 ∧
      0<Q.2.1 ∧ Q.2.1<P.2.1 ∧ corner Q<corner P := by
  have hslack : 0<d+P.2.1-1 := by
    simp [W,deValue,hPangle] at hDE
    linarith
  let ε : ℝ := min (P.2.1/2) ((d+P.2.1-1)/2)
  have hε : 0<ε := lt_min (by linarith) (by linarith)
  have hεb : ε≤P.2.1/2 := min_le_left _ _
  have hεDE : ε≤(d+P.2.1-1)/2 := min_le_right _ _
  let Q : State := (P.1,P.2.1-ε,0)
  have hbQ : 0<Q.2.1 := by dsimp [Q]; linarith
  have hangle : α∈Icc 0 (7/10:ℝ) :=
    ⟨by simpa [hPangle] using hp.angle.2,hα⟩
  have hcos : 0≤Real.cos α := by linarith [(transport_trig hangle).1]
  have hgain := mul_nonneg hε.le hcos
  have hdrop : corner Q<corner P := by
    have hh := mul_pos hε (show 0<2*P.2.1+1-ε by linarith)
    dsimp [corner,Q]
    nlinarith
  refine ⟨Q,?_,rfl,rfl,hbQ,by dsimp [Q]; linarith,hdrop⟩
  refine {
    b_nonneg := hbQ.le
    sorted := by dsimp [Q]; linarith [hp.sorted]
    angle := ⟨le_rfl,hangle.1⟩
    circle := hdrop.le.trans hp.circle
    DE := ?_
    EH := ?_ }
  · simp [Q,W,deValue]
    linarith
  · have hh := hp.EH
    dsimp only [ehValue] at hh
    simp only [hPangle,sub_zero] at hh
    dsimp only [Q,ehValue]
    simp only [sub_zero]
    linarith

end EInteriorGeometry

namespace SignedCycle
open Candidate

/-- The strict loss is on the original E circle.  No common-circle
lift is used at any stage of this primary outside branch. -/
theorem HardInput.reduce_nonpositive_below_primary {q : ℝ}
    (I : HardInput q) (hqL : qLow≤q) (hq : q≤qTrial)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hHG : I.cycle.Feasible H 0) (hTD : I.cycle.Feasible T 2)
    (hED : I.cycle.theta E<I.cycle.theta D)
    (hDE3 : I.cycle.Feasible D 3) :
    ∃J : HardInput q,
      (∀i, i≠E → J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) ∧
      J.cycle.theta E=I.cycle.theta D ∧
      AnchorNonincrease I.cycle J.cycle ∧ StrictAnchorLoss I.cycle J.cycle ∧
      (J.cycle.point E).circle<(I.cycle.point E).circle ∧
      J.cycle.Feasible D 3 ∧ J.cycle.Feasible E 1 := by
  have hcap : q≤qCap := hq.trans (by norm_num [qTrial,qCap])
  have hb := I.nonpositive_composite_bounds hcap hAB hAG hGH hDT hTB hHG hTD
  obtain ⟨P,hP,hPangle,hPcircle,hPb,hPDE,hPEH⟩ :=
    I.nonpositive_below_primary_state hqL hq hAB hnorm hAG hGH hDT hTB hHG hTD hED hDE3
  obtain ⟨Q,hQ,hQangle,hQa,hQb,hQbP,hQcircle⟩ :=
    EInteriorGeometry.lower_tangent_at_D (by linarith [hb.span_lt]) hP hPangle hPb.1 hPDE
  let J := I.fromNonpositiveEInterior hcap hb hQ
  have hfixed (i : Vertex) (hi : i≠E) :
      J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i :=
    eInteriorCycle_unchanged I.cycle Q i hi
  have hJcircle : (J.cycle.point E).circle<(I.cycle.point E).circle := by
    rw [show (J.cycle.point E).circle=EInteriorGeometry.corner Q from
      eInteriorCycle_circle hQ.b_nonneg]
    exact hQcircle.trans_eq hPcircle
  have hJframe : J.cycle.theta E=I.cycle.theta D := by
    change I.cycle.theta D+Q.2.2=I.cycle.theta D
    rw [hQangle]
    ring
  have hnon : AnchorNonincrease I.cycle J.cycle := by
    intro i hi
    by_cases hiE : i=E
    · subst i; exact hJcircle.le
    · rw [(hfixed i hiE).1]
  have hstrict : StrictAnchorLoss I.cycle J.cycle :=
    ⟨E,by norm_num [anchorVertices,E],hJcircle⟩
  exact ⟨J,hfixed,hJframe,hnon,hstrict,hJcircle,
    eInteriorCycle_DE (by linarith [hb.span_lt]) hQ,
    eInteriorCycle_EH (by linarith [hb.span_lt]) hQ⟩

end SignedCycle
end SquaresInCircles.Eight
end
end
end

section
/-!
## Whole-interval bounds for the original-circle rotated DE2 curve

The source E primary greater than one
keeps the original-circle radical above 3/2.  The original D coordinate
bounds give the exact contact tangent and its positive derivative.
A circle projection and a single completed square bound the remaining
angular coefficient on the entire frame interval.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.NonpositiveDE2Contact

def b (D : SignedPoint) (z : ℝ) : ℝ :=
  1/2-(D.a-1/2)*Real.cos z+(1/2-D.y)*Real.sin z

def K (D : SignedPoint) (z : ℝ) : ℝ :=
  (D.a-1/2)*Real.sin z+(1/2-D.y)*Real.cos z

def Y (D : SignedPoint) (z : ℝ) : ℝ := b D z+1/2
def X (E D : SignedPoint) (z : ℝ) : ℝ := OriginalECircle.root E (b D z)
def U (E D : SignedPoint) (z : ℝ) : ℝ := X E D z-K D z

def J (E D H : SignedPoint) (α z : ℝ) : ℝ :=
  OriginalECircle.eh E H (α+z) (b D z)

@[simp] theorem b_zero (D : SignedPoint) : b D 0=1-D.a := by simp [b]; ring

theorem b_derivative (D : SignedPoint) (z : ℝ) : HasDerivAt (b D) (K D z) z := by
  have h := (((Real.hasDerivAt_cos z).const_mul (D.a-1/2)).const_sub (1/2)).add
    ((Real.hasDerivAt_sin z).const_mul (1/2-D.y))
  convert h using 1
  · funext x; simp only [b,Pi.add_apply]
  · simp only [K]; ring

theorem K_lower {D : SignedPoint} {z : ℝ}
    (hDa : 1/2≤D.a) (hDy : 353/500< -D.y) (hz : z∈Icc 0 (7/10:ℝ)) :
    (9/10:ℝ)<K D z := by
  have ht := transport_trig hz
  have hfirst := mul_nonneg (sub_nonneg.mpr hDa) ht.2.2.1
  have hsecond := mul_lt_mul_of_pos_left ht.1 (show 0<1/2-D.y by linarith)
  dsimp [K]
  nlinarith

theorem b_growth {D : SignedPoint} {x y : ℝ}
    (hDa : 1/2≤D.a) (hDy : 353/500< -D.y)
    (hx : x∈Icc 0 (7/10:ℝ)) (hy : y∈Icc 0 (7/10:ℝ)) (hxy : x≤y) :
    (9/10)*(y-x)≤b D y-b D x := by
  exact derivative_reserve
    (fun z _ => (b_derivative D z).continuousAt.continuousWithinAt)
    (fun z _ => b_derivative D z)
    (fun z hz => (K_lower hDa hDy (Ioo_subset_Icc_self hz)).le) hx hy hxy

theorem b_monotone {D : SignedPoint}
    (hDa : 1/2≤D.a) (hDy : 353/500< -D.y) : MonotoneOn (b D) (Icc 0 (7/10:ℝ)) := by
  intro x hx y hy hxy
  have hh := b_growth hDa hDy hx hy hxy
  linarith

theorem DE2_slack (E D : SignedPoint) {z : ℝ} (y : ℝ) (hz : z∈Icc 0 (7/10:ℝ)) :
    quarterProjection D (OriginalECircle.point E y) (-z) 2-edgeWidth (-z)=y-b D z := by
  rw [edgeWidth_negative_formula hz]
  simp [quarterProjection,OriginalECircle.point,b]
  ring

theorem eh_tangent_antitone (E H : SignedPoint) {p y₁ y₂ : ℝ}
    (hp : p∈Icc 0 (7/10:ℝ)) (hy₁ : 0≤y₁) (hy : y₁≤y₂) :
    OriginalECircle.eh E H p y₂≤OriginalECircle.eh E H p y₁ := by
  have hsq := pow_le_pow_left₀ (show 0≤y₁+1/2 by linarith)
    (show y₁+1/2≤y₂+1/2 by linarith) 2
  have hroot := Real.sqrt_le_sqrt (show E.circle-(y₂+1/2)^2≤E.circle-(y₁+1/2)^2 by linarith)
  have ht := transport_trig hp
  have hmajor := mul_le_mul_of_nonneg_right hroot ht.2.2.1
  have hminor := mul_le_mul_of_nonneg_right hy (show 0≤Real.cos p by linarith [ht.1])
  dsimp [OriginalECircle.eh,OriginalECircle.primary,OriginalECircle.root]
  nlinarith

def upper (z : ℝ) : ℝ := ((773/1000)-Real.sin z)/Real.cos z
def upperD (z : ℝ) : ℝ := ((773/1000)*Real.sin z-1)/(Real.cos z)^2

theorem upper_derivative {z : ℝ} (hz : z∈Icc 0 (7/10:ℝ)) :
    HasDerivAt upper (upperD z) z := by
  have hc : Real.cos z≠0 := ne_of_gt (by linarith [(transport_trig hz).1])
  convert ((Real.hasDerivAt_sin z).const_sub (773/1000)).div
    (Real.hasDerivAt_cos z) hc using 1
  · rfl
  · dsimp [upperD]
    field_simp [hc]
    nlinarith [Real.sin_sq_add_cos_sq z]

theorem upper_rate {z : ℝ} (hz : z∈Icc 0 (7/10:ℝ)) : upperD z< -(4/5) := by
  have hc : 0<Real.cos z := by linarith [(transport_trig hz).1]
  have hquad : 0<(4/5)*(Real.sin z)^2-(773/1000)*Real.sin z+1/5 := by
    nlinarith [sq_nonneg (Real.sin z-773/1600)]
  apply (div_lt_iff₀ (sq_pos_of_pos hc)).2
  nlinarith [Real.sin_sq_add_cos_sq z]

theorem upper_linear {z : ℝ} (hz : z∈Icc 0 (7/10:ℝ)) :
    upper z≤773/1000-(4/5)*z := by
  have hh := derivative_reserve
    (f := fun z => -upper z) (df := fun z => -upperD z) (k := (4/5:ℝ))
    (fun z hz => (upper_derivative hz).neg.continuousAt.continuousWithinAt)
    (fun z hz => (upper_derivative (Ioo_subset_Icc_self hz)).neg)
    (fun z hz => by linarith [upper_rate (Ioo_subset_Icc_self hz)])
    (show (0:ℝ)∈Icc 0 (7/10) by norm_num) hz hz.1
  have hzero : upper 0=773/1000 := by norm_num [upper]
  rw [hzero] at hh
  linarith

theorem U_upper {E D : SignedPoint} {z : ℝ}
    (hEs : E.Sorted) (hEy : E.y≤0) (hEc : E.circle≤qCap)
    (hDy : 353/500< -D.y) (hz : z∈Icc 0 (7/10:ℝ))
    (hb : b D z∈Icc 0 (-E.y)) :
    U E D z<773/1000-(4/5)*z := by
  have hr := OriginalECircle.root_bounds hEs hEy hb
  have hnorm : (X E D z)^2+(Y D z)^2=E.circle := by
    dsimp [X,Y]
    linarith [hr.2.2]
  have hrotation : (X E D z*Real.cos z+Y D z*Real.sin z)^2+
      (X E D z*Real.sin z-Y D z*Real.cos z)^2=E.circle := by
    have hh := circle_rotation_identity (X E D z) (-(Y D z)) z
    nlinarith
  have hproject : X E D z*Real.cos z+Y D z*Real.sin z<1979/1000 := by
    have hs := sq_nonneg (X E D z*Real.sin z-Y D z*Real.cos z)
    dsimp [qCap] at hEc
    nlinarith
  have hKidentity : K D z*Real.cos z+Y D z*Real.sin z=1/2-D.y+Real.sin z := by
    dsimp [K,Y,b]
    linear_combination (1/2-D.y)*(Real.sin_sq_add_cos_sq z)
  have hscaled : U E D z*Real.cos z<773/1000-Real.sin z := by
    dsimp [U]
    nlinarith
  have hc : 0<Real.cos z := by linarith [(transport_trig hz).1]
  have hu : U E D z<upper z := (lt_div_iff₀ hc).2 hscaled
  exact hu.trans_le (upper_linear hz)

theorem Y_upper {D : SignedPoint} {z : ℝ}
    (hDa : 353/500<D.a) (hDy : -D.y<9/10) (hz : z∈Icc 0 (7/10:ℝ)) :
    Y D z<(1399/1000)*(3/5+(11/10)*z) := by
  have ht := transport_trig hz
  have hcos : 0<Real.cos z := by linarith [ht.1]
  have hA := mul_lt_mul_of_pos_right (show 103/500<D.a-1/2 by linarith) hcos
  have hB := mul_le_mul_of_nonneg_right (show 1/2-D.y≤7/5 by linarith) ht.2.2.1
  have hsin := Real.sin_le hz.1
  have hcoslower := Real.one_sub_sq_div_two_le_cos (x:=z)
  have hquad := mul_nonneg hz.1 (show 0≤7/10-z by linarith [hz.2])
  dsimp [Y,b]
  nlinarith

theorem ratio_upper {E D : SignedPoint} {z : ℝ}
    (hEs : E.Sorted) (hEy : E.y≤0) (hEa : 1<E.a)
    (hDa : 353/500<D.a) (hDy : -D.y<9/10) (hz : z∈Icc 0 (7/10:ℝ))
    (hb : b D z∈Icc 0 (-E.y)) :
    Y D z/X E D z<3/5+(11/10)*z := by
  have hr := OriginalECircle.root_bounds hEs hEy hb
  have hX : (1399/1000:ℝ)<X E D z := by dsimp [X]; linarith [hr.2.1]
  have hX0 : 0<X E D z := by linarith
  have hrpos : 0<(3/5:ℝ)+(11/10)*z := by linarith [hz.1]
  have hY := Y_upper hDa hDy hz
  have hprod := mul_lt_mul_of_pos_right hX hrpos
  apply (div_lt_iff₀ hX0).2
  nlinarith

end SquaresInCircles.Eight.NonpositiveDE2Contact
end
end
end

section
/-!
## Strict EH improvement along the original rotated DE2 contact

The contact is the actual original D
projection and the radical belongs to E.circle.  Its derivative is
negative by a single cubic inequality on the whole frame interval.
The explicit 1/200 rate turns every positive angular movement into
strict actual EH slack at the endpoint.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.NonpositiveDE2Contact

def Jd (E D : SignedPoint) (α z : ℝ) : ℝ :=
  (U E D z-1)*Real.cos (α+z)+
    (Y D z*U E D z/X E D z)*Real.sin (α+z)

theorem J_derivative {E D H : SignedPoint} {α z : ℝ}
    (hEs : E.Sorted) (hEy : E.y≤0) (hb : b D z∈Icc 0 (-E.y)) :
    HasDerivAt (J E D H α) (Jd E D α z) z := by
  have hr := (OriginalECircle.root_bounds hEs hEy hb).1
  have hbder := b_derivative D z
  have hader := (OriginalECircle.derivative hEs hEy hb).1.comp z hbder
  have hpder : HasDerivAt (fun w : ℝ => α+w) 1 z := by
    simpa using (hasDerivAt_id z).const_add α
  convert ((hasDerivAt_const z (H.a-1/2)).add
    ((hader.sub_const (1/2)).mul hpder.sin)).sub
      ((hbder.add_const (1/2)).mul hpder.cos) using 1
  · rfl
  · dsimp [Jd,U,X,Y,OriginalECircle.primary,OriginalECircle.slope]
    field_simp [hr.ne']
    ring

/-- The quadratic chord dominates after the nonpositive cubic is
discarded.  Both intrinsic endpoint values leave a reserve beyond
1/150; no angular subdivision is involved. -/
theorem cubic_bound {z : ℝ} (hz : z∈Icc 0 (7/10:ℝ)) :
    (773/1000-(4/5)*z)*
      (1+(4/3)*(3/5+(11/10)*z)*(27/100+z))-1< -(1/150) := by
  have hquad := mul_nonneg hz.1 (show 0≤7/10-z by linarith [hz.2])
  have hcube : 0≤z^3 := pow_nonneg hz.1 3
  have hid : (773/1000-(4/5)*z)*
      (1+(4/3)*(3/5+(11/10)*z)*(27/100+z))-1=
      -(938/15625)-(12073/250000)*z+(1327/7500)*z^2-(88/75)*z^3 := by ring
  rw [hid]
  nlinarith

theorem J_rate {E D : SignedPoint} {α z : ℝ}
    (hEs : E.Sorted) (hEy : E.y≤0) (hEa : 1<E.a) (hEc : E.circle≤qCap)
    (hDa : 353/500<D.a) (hDy : -D.y∈Ioo (353/500:ℝ) (9/10))
    (hα : α∈Icc 0 (27/100:ℝ)) (hz : z∈Icc 0 (7/10:ℝ)) (hsum : α+z≤7/10)
    (hb : b D z∈Icc 0 (-E.y)) : Jd E D α z< -(1/200) := by
  have hu := U_upper hEs hEy hEc hDy.1 hz hb
  have hr := ratio_upper hEs hEy hEa hDa hDy.2 hz hb
  have hX : 0<X E D z := (OriginalECircle.root_bounds hEs hEy hb).1
  have hY : 0<Y D z := by dsimp [Y]; linarith [hb.1]
  have hp : α+z∈Icc 0 (7/10:ℝ) := ⟨by linarith [hα.1,hz.1],hsum⟩
  have ht := transport_trig hp
  have hc : 0<Real.cos (α+z) := by linarith [ht.1]
  by_cases hU : U E D z≤0
  · have hfirst : (U E D z-1)*Real.cos (α+z)< -(3/4) := by
      have hm := mul_nonpos_of_nonpos_of_nonneg hU hc.le
      nlinarith [ht.1]
    have hratio : Y D z*U E D z/X E D z≤0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hY.le hU) hX.le
    have hsecond := mul_nonpos_of_nonpos_of_nonneg hratio ht.2.2.1
    dsimp [Jd]
    linarith
  have hUpos : 0<U E D z := lt_of_not_ge hU
  let u : ℝ := 773/1000-(4/5)*z
  let r : ℝ := 3/5+(11/10)*z
  have hu0 : 0<u := by dsimp [u]; linarith [hz.2]
  have hr0 : 0<r := by dsimp [r]; linarith [hz.1]
  have hUone : U E D z<1 := by dsimp [u] at *; linarith [hz.1]
  have hfirst : (U E D z-1)*Real.cos (α+z)<(3/4)*(u-1) := by
    have hm := mul_lt_mul_of_neg_left ht.1 (show U E D z-1<0 by linarith)
    have hu' : U E D z<u := hu
    have hule : u≤1 := by dsimp [u]; linarith [hz.1]
    linarith
  have hs : Real.sin (α+z)≤27/100+z :=
    (Real.sin_le hp.1).trans (by linarith [hα.2])
  have hproduct : (Y D z/X E D z)*U E D z≤r*u :=
    mul_le_mul hr.le hu.le hUpos.le hr0.le
  have hsecond : (Y D z*U E D z/X E D z)*Real.sin (α+z)≤r*u*(27/100+z) := by
    have hh := mul_le_mul hproduct hs ht.2.2.1 (mul_nonneg hr0.le hu0.le)
    convert hh using 1; ring
  have hpoly := cubic_bound hz
  have hupper : (3/4)*(u-1)+r*u*(27/100+z)< -(1/200) := by
    dsimp [u,r]
    nlinarith
  dsimp [Jd]
  linarith

/-- The original circle contact has a quantified improvement between
any two of its actual nonnegative-tangent states.  The interval geometry
is derived from the two endpoint tangents by monotonicity of b. -/
theorem J_reverse_growth {E D H : SignedPoint} {α l r : ℝ}
    (hEs : E.Sorted) (hEy : E.y≤0) (hEa : 1<E.a) (hEc : E.circle≤qCap)
    (hDa : 353/500<D.a) (hDy : -D.y∈Ioo (353/500:ℝ) (9/10))
    (hα : α∈Icc 0 (27/100:ℝ))
    (hl : 0≤l) (hlr : l≤r) (hr : r≤7/10) (hsum : α+r≤7/10)
    (hbL : 0≤b D l) (hbR : b D r≤ -E.y) :
    (1/200)*(r-l)≤J E D H α l-J E D H α r := by
  have hlrange : l∈Icc 0 (7/10:ℝ) := ⟨hl,hlr.trans hr⟩
  have hrrange : r∈Icc 0 (7/10:ℝ) := ⟨hl.trans hlr,hr⟩
  have hm := b_monotone (show 1/2≤D.a by linarith) hDy.1
  have hgeometry (z : ℝ) (hz : z∈Icc l r) :
      z∈Icc 0 (7/10:ℝ) ∧ b D z∈Icc 0 (-E.y) := by
    have hzrange : z∈Icc 0 (7/10:ℝ) := ⟨hl.trans hz.1,hz.2.trans hr⟩
    exact ⟨hzrange,⟨hbL.trans (hm hlrange hzrange hz.1),
      (hm hzrange hrrange hz.2).trans hbR⟩⟩
  have hh := derivative_reserve
    (f := fun z => -J E D H α z) (df := fun z => -Jd E D α z) (k := (1/200:ℝ))
    (fun z hz => (J_derivative (H := H) (α := α) hEs hEy (hgeometry z hz).2).neg.continuousAt.continuousWithinAt)
    (fun z hz => (J_derivative (H := H) (α := α) hEs hEy
      (hgeometry z (Ioo_subset_Icc_self hz)).2).neg)
    (fun z hz => by
      have hz' := hgeometry z (Ioo_subset_Icc_self hz)
      have hs : α+z≤7/10 := by linarith [hz.2]
      linarith [J_rate hEs hEy hEa hEc hDa hDy hα hz'.1 hs hz'.2])
    (show l∈Icc l r from ⟨le_rfl,hlr⟩)
    (show r∈Icc l r from ⟨hlr,le_rfl⟩) hlr
  linarith

end SquaresInCircles.Eight.NonpositiveDE2Contact
end
end
end

section
/-!
## The original rotated DE2 source reaches E=D on its own circle

The source tangent first decreases to the
actual DE2 contact, improving EH.  The entire contact segment then has
the proved negative EH derivative.  Any earlier zero-tangent endpoint
is inserted into the actual same-q hard cycle and excluded.  Thus the
endpoint is E=D, on exactly the original E circle, with strict EH slack.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SignedCycle
open Candidate NonpositiveDE2Contact

theorem HardInput.nonpositive_below_rotated_state {q : ℝ}
    (I : HardInput q) (hqL : qLow≤q) (hq : q≤qTrial)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hHG : I.cycle.Feasible H 0) (hTD : I.cycle.Feasible T 2)
    (hED : I.cycle.theta E<I.cycle.theta D) (hDE2 : I.cycle.Feasible D 2) :
    ∃P : EInteriorGeometry.State,
      EInteriorGeometry.Feasible (I.cycle.point H).a (I.cycle.point D).a
        (I.cycle.theta H-I.cycle.theta D) q P ∧
      P.2.2=0 ∧ EInteriorGeometry.corner P=(I.cycle.point E).circle ∧
      P.2.1∈Ioc 0 (-(I.cycle.point E).y) ∧
      EInteriorGeometry.W P.2.2=EInteriorGeometry.deValue (I.cycle.point D).a P ∧
      EInteriorGeometry.W (I.cycle.theta H-I.cycle.theta D-P.2.2)<
        EInteriorGeometry.ehValue (I.cycle.point H).a (I.cycle.theta H-I.cycle.theta D) P := by
  have hcap : q≤qCap := hq.trans (by norm_num [qTrial,qCap])
  have hb := I.nonpositive_composite_bounds hcap hAB hAG hGH hDT hTB hHG hTD
  have hrad := I.nonpositive_E_radial hcap hAB hAG hGH hDT hTB hHG hTD
  have hEa := I.nonpositive_below_DE2_primary hcap hAB hAG hGH hDT hTB hHG hTD hED hDE2
  have hEc : (I.cycle.point E).circle≤qCap := (I.necessary.contained E).trans hcap
  have hDa : (353/500:ℝ)<(I.cycle.point D).a := by
    have hs : -(I.cycle.point D).y≤(I.cycle.point D).a := by
      simpa [abs_of_nonpos I.anchors_normal.D_nonpos] using (I.necessary.sorted D).2
    exact hb.D_tangent.1.trans_le hs
  have hDy : -(I.cycle.point D).y∈Ioo (353/500:ℝ) (9/10) := hb.D_tangent
  let α := I.cycle.theta H-I.cycle.theta D
  let x := I.cycle.theta D-I.cycle.theta E
  have hα : α∈Icc 0 (27/100:ℝ) := ⟨hb.span_nonneg,hb.span_lt.le⟩
  have hxpos : 0<x := sub_pos.mpr hED
  have hx : x∈Icc 0 (7/10:ℝ) :=
    ⟨hxpos.le,(le_abs_self _).trans (I.necessary.spread D E)⟩
  have hsum : α+x≤7/10 := by
    have hh := (le_abs_self _).trans (I.necessary.spread H E)
    dsimp [α,x,frameCap] at *
    linarith
  have hp : α+x∈Icc 0 (7/10:ℝ) := ⟨by linarith [hα.1],hsum⟩
  have hEHorder : I.cycle.theta E≤I.cycle.theta H :=
    hED.le.trans (sub_nonneg.mp hb.span_nonneg)
  have hEH1 := I.nonpositive_EH_primary_of_nonneg hcap hAB hAG hGH hDT hTB hHG hTD hEHorder
  have hDEraw : quarterFeasible (I.cycle.point D) (I.cycle.point E) (-x) 2 := by
    have heq : -x=I.cycle.theta E-I.cycle.theta D := by dsimp [x]; ring
    simpa [Feasible,slack,edge,word,delta,next,D,E,quarterFeasible,sub_nonneg,heq] using hDE2
  have hEHraw : quarterFeasible (I.cycle.point E) (I.cycle.point H) (α+x) 1 := by
    have heq : α+x=I.cycle.theta H-I.cycle.theta E := by dsimp [α,x]; ring
    simpa [Feasible,slack,edge,word,delta,next,E,H,quarterFeasible,sub_nonneg,heq] using hEH1
  have hsource_DE : b (I.cycle.point D) x≤ -(I.cycle.point E).y := by
    have hh : 0≤quarterProjection (I.cycle.point D)
        (OriginalECircle.point (I.cycle.point E) (-(I.cycle.point E).y)) (-x) 2-edgeWidth (-x) := by
      rw [OriginalECircle.initial (I.necessary.sorted E) I.E_nonpos]
      exact sub_nonneg.mpr hDEraw
    rw [DE2_slack _ _ _ hx] at hh
    linarith
  have hsource_EH : 0≤OriginalECircle.eh (I.cycle.point E) (I.cycle.point H)
      (α+x) (-(I.cycle.point E).y) := by
    rw [OriginalECircle.eh_actual _ _ _ hp,
      OriginalECircle.initial (I.necessary.sorted E) I.E_nonpos]
    exact sub_nonneg.mpr hEHraw
  /- Every floor state is an actual necessary cycle at the same q. -/
  have positive_tangent (z y : ℝ) (hz : z∈Icc 0 x)
      (hy : y∈Icc 0 (-(I.cycle.point E).y))
      (hcontact : b (I.cycle.point D) z≤y)
      (hEH : 0≤OriginalECircle.eh (I.cycle.point E) (I.cycle.point H) (α+z) y) : 0<y := by
    have hzrange : z∈Icc 0 (7/10:ℝ) := ⟨hz.1,hz.2.trans hx.2⟩
    have hprange : α+z∈Icc 0 (7/10:ℝ) := ⟨by linarith [hα.1,hz.1],by linarith [hz.2]⟩
    have hgeom := OriginalECircle.geometry (I.necessary.sorted E) I.E_nonpos hrad.1 hy
    let p := OriginalECircle.point (I.cycle.point E) y
    let θ := I.cycle.theta D-z
    have hpq : p.Contained q := hgeom.2.2.1.trans_le (I.necessary.contained E)
    have hpnegative : p.y≤0 := neg_nonpos.mpr hy.1
    have hprad : max |(I.cycle.point H).y| |(I.cycle.point D).y|≤p.a :=
      hrad.2.trans hgeom.2.2.2
    have hθ : θ∈Icc (I.cycle.theta E) (I.cycle.theta D) := by
      have hzu : z≤I.cycle.theta D-I.cycle.theta E := hz.2
      dsimp [θ]
      constructor <;> linarith [hz.1]
    have hDEactual : quarterFeasible (I.cycle.point D) p (θ-I.cycle.theta D) 2 := by
      have heq : θ-I.cycle.theta D= -z := by dsimp [θ]; ring
      rw [heq]
      apply sub_nonneg.mp
      rw [show p=OriginalECircle.point (I.cycle.point E) y from rfl,DE2_slack _ _ _ hzrange]
      exact sub_nonneg.mpr hcontact
    have hEHactual : quarterFeasible p (I.cycle.point H) (I.cycle.theta H-θ) 1 := by
      have heq : I.cycle.theta H-θ=α+z := by dsimp [θ,α]; ring
      rw [heq]
      have hh := hEH
      rw [OriginalECircle.eh_actual _ _ _ hprange] at hh
      exact sub_nonneg.mp hh
    let J := I.fromBelowERotated hgeom.1 hpq hgeom.2.1 hpnegative hprad hθ hDEactual hEHactual
    have hfixed (i : Vertex) (hi : i≠E) :
        J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i :=
      belowEPrimaryCycle_unchanged I.cycle p θ i hi
    have hH := hfixed H (by decide)
    have hG := hfixed G (by decide)
    have hA := hfixed A (by decide)
    have hB := hfixed B (by decide)
    have hT := hfixed T (by decide)
    have hD := hfixed D (by decide)
    have hJHG : J.cycle.Feasible H 0 :=
      (replacePoint_other_feasible (v := E) (by decide : H≠E) (by decide : next H≠E)).2 hHG
    have hJTD : J.cycle.Feasible T 2 :=
      (replacePoint_other_feasible (v := E) (by decide : T≠E) (by decide : next T≠E)).2 hTD
    have hJnegative := J.nonpositive_E_strict_negative hqL hq
      (by rw [hA.2,hB.2]; exact hAB)
      (by rw [hA.1,hB.1]; exact hnorm)
      (by rw [hA.2,hG.2]; exact hAG)
      (by rw [hG.2,hH.2]; exact hGH)
      (by rw [hD.2,hT.2]; exact hDT)
      (by rw [hT.2,hB.2]; exact hTB) hJHG hJTD
    change -y<0 at hJnegative
    linarith
  let y₀ := max 0 (b (I.cycle.point D) x)
  have hy₀ : y₀∈Icc 0 (-(I.cycle.point E).y) :=
    ⟨le_max_left _ _,max_le (neg_nonneg.mpr I.E_nonpos) hsource_DE⟩
  have hcontact₀ : b (I.cycle.point D) x≤y₀ := le_max_right _ _
  have hEH₀ : 0≤OriginalECircle.eh (I.cycle.point E) (I.cycle.point H) (α+x) y₀ :=
    hsource_EH.trans (eh_tangent_antitone _ _ hp hy₀.1 hy₀.2)
  have hy₀positive := positive_tangent x y₀ ⟨hx.1,le_rfl⟩ hy₀ hcontact₀ hEH₀
  have hbx : 0<b (I.cycle.point D) x := by
    by_contra! hbad
    have hh : y₀=0 := max_eq_left hbad
    linarith
  have hy₀eq : y₀=b (I.cycle.point D) x := max_eq_right hbx.le
  have hJx_nonneg : 0≤J (I.cycle.point E) (I.cycle.point D) (I.cycle.point H) α x := by
    simpa only [J,hy₀eq] using hEH₀
  have hbzero : 0<b (I.cycle.point D) 0 := by
    by_contra! hbad
    have hcontinuous : Continuous (b (I.cycle.point D)) :=
      continuous_iff_continuousAt.2 fun z => (b_derivative _ z).continuousAt
    have himage : 0∈b (I.cycle.point D) '' Icc 0 x := by
      apply intermediate_value_Icc hxpos.le hcontinuous.continuousOn
      exact ⟨hbad,hbx.le⟩
    obtain ⟨z,hz,hbz⟩ := himage
    have hJgrow := J_reverse_growth (H := I.cycle.point H)
      (I.necessary.sorted E) I.E_nonpos hEa hEc hDa hDy hα
      hz.1 hz.2 hx.2 hsum (by rw [hbz]) hsource_DE
    have hJz : 0≤J (I.cycle.point E) (I.cycle.point D) (I.cycle.point H) α z := by
      linarith [hz.2]
    have hzero : 0<(0:ℝ) := positive_tangent z 0 hz
      ⟨le_rfl,neg_nonneg.mpr I.E_nonpos⟩ (by rw [hbz])
      (by simpa only [J,hbz] using hJz)
    exact (lt_irrefl (0:ℝ)) hzero
  have hmon := b_monotone hb.D_primary.1.le hDy.1
  have hbupper : b (I.cycle.point D) 0≤ -(I.cycle.point E).y :=
    (hmon (by norm_num) hx hx.1).trans hsource_DE
  have hJgrow := J_reverse_growth (H := I.cycle.point H)
    (I.necessary.sorted E) I.E_nonpos hEa hEc hDa hDy hα
    (le_rfl : (0:ℝ)≤0) hx.1 hx.2 hsum hbzero.le hsource_DE
  have hJzero : 0<J (I.cycle.point E) (I.cycle.point D) (I.cycle.point H) α 0 := by
    linarith
  let P : EInteriorGeometry.State :=
    (OriginalECircle.primary (I.cycle.point E) (b (I.cycle.point D) 0),b (I.cycle.point D) 0,0)
  have hgeom := OriginalECircle.geometry (I.necessary.sorted E) I.E_nonpos hrad.1
    ⟨hbzero.le,hbupper⟩
  have hPcircle : EInteriorGeometry.corner P=(I.cycle.point E).circle := by
    simpa [P,EInteriorGeometry.corner,OriginalECircle.point,SignedPoint.circle,
      abs_neg,abs_of_nonneg hbzero.le,-b_zero] using hgeom.2.2.1
  have hPDE : EInteriorGeometry.W P.2.2=EInteriorGeometry.deValue (I.cycle.point D).a P := by
    simp [P,EInteriorGeometry.W,EInteriorGeometry.deValue]
  have hPEH : EInteriorGeometry.W (α-P.2.2)<EInteriorGeometry.ehValue (I.cycle.point H).a α P := by
    dsimp [J,OriginalECircle.eh] at hJzero
    dsimp [P,EInteriorGeometry.W,EInteriorGeometry.ehValue]
    simp only [add_zero,sub_zero] at *
    linarith
  refine ⟨P,?_,rfl,hPcircle,⟨hbzero,hbupper⟩,hPDE,hPEH⟩
  exact {
    b_nonneg := hbzero.le
    sorted := by
      simpa [P,OriginalECircle.point,abs_neg,abs_of_nonneg hbzero.le,-b_zero] using hgeom.1.2
    angle := ⟨le_rfl,hα.1⟩
    circle := hPcircle.trans_le (I.necessary.contained E)
    DE := hPDE.le
    EH := hPEH.le }

end SquaresInCircles.Eight.SignedCycle
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace EInteriorGeometry

theorem lower_primary_at_D {h d α q : ℝ} {P : State}
    (hp : Feasible h d α q P) (hPangle : P.2.2=0)
    (hsort : P.2.1<P.1) (hEH : W (α-P.2.2)<ehValue h α P) :
    ∃Q : State, Feasible h d α q Q ∧ Q.2.2=0 ∧ Q.2.1=P.2.1 ∧
      Q.1<P.1 ∧ corner Q<corner P := by
  let ε : ℝ := min ((P.1-P.2.1)/4) (ehSlack h α P/2)
  have hslack : 0<ehSlack h α P := sub_pos.mpr hEH
  have hε : 0<ε := lt_min (by linarith) (by linarith)
  have hεsort : ε≤(P.1-P.2.1)/4 := min_le_left _ _
  have hεEH : ε≤ehSlack h α P/2 := min_le_right _ _
  let Q : State := (P.1-ε,P.2.1,0)
  have hdrop : corner Q<corner P := by
    have hh := mul_pos hε (show 0<2*P.1+1-ε by linarith [hp.b_nonneg])
    dsimp [Q,corner]
    nlinarith
  have hsin := mul_le_mul_of_nonneg_left (Real.sin_le_one α) hε.le
  refine ⟨Q,?_,rfl,rfl,by dsimp [Q]; linarith,hdrop⟩
  refine {
    b_nonneg := hp.b_nonneg
    sorted := by dsimp [Q]; linarith
    angle := ⟨le_rfl,by simpa [hPangle] using hp.angle.2⟩
    circle := hdrop.le.trans hp.circle
    DE := ?_
    EH := ?_ }
  · have hh := hp.DE
    simpa [Q,deValue,W,hPangle] using hh
  · have hh := hp.EH
    dsimp [ehSlack] at hεEH
    dsimp [Q,ehValue] at hh hεEH ⊢
    simp only [hPangle,sub_zero] at hh hεEH ⊢
    nlinarith

end EInteriorGeometry

namespace SignedCycle
open Candidate

theorem HardInput.reduce_nonpositive_below_rotated {q : ℝ}
    (I : HardInput q) (hqL : qLow≤q) (hq : q≤qTrial)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hHG : I.cycle.Feasible H 0) (hTD : I.cycle.Feasible T 2)
    (hED : I.cycle.theta E<I.cycle.theta D) (hDE2 : I.cycle.Feasible D 2) :
    ∃J : HardInput q,
      (∀i, i≠E → J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) ∧
      J.cycle.theta E=I.cycle.theta D ∧
      AnchorNonincrease I.cycle J.cycle ∧ StrictAnchorLoss I.cycle J.cycle ∧
      (J.cycle.point E).circle<(I.cycle.point E).circle ∧
      J.cycle.Feasible D 3 ∧ J.cycle.Feasible E 1 := by
  have hcap : q≤qCap := hq.trans (by norm_num [qTrial,qCap])
  have hb := I.nonpositive_composite_bounds hcap hAB hAG hGH hDT hTB hHG hTD
  obtain ⟨P,hP,hPangle,hPcircle,hPb,hPDE,hPEH⟩ :=
    I.nonpositive_below_rotated_state hqL hq hAB hnorm hAG hGH hDT hTB hHG hTD hED hDE2
  have hsort := EInteriorGeometry.strict_sorting_wide hcap
    ⟨hb.span_nonneg,hb.span_lt.le⟩ hb.primary_sum hP
  obtain ⟨Q,hQ,hQangle,hQb,hQa,hQcircle⟩ :=
    EInteriorGeometry.lower_primary_at_D hP hPangle hsort hPEH
  let J := I.fromNonpositiveEInterior hcap hb hQ
  have hfixed (i : Vertex) (hi : i≠E) :
      J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i :=
    eInteriorCycle_unchanged I.cycle Q i hi
  have hJcircle : (J.cycle.point E).circle<(I.cycle.point E).circle := by
    rw [show (J.cycle.point E).circle=EInteriorGeometry.corner Q from
      eInteriorCycle_circle hQ.b_nonneg]
    exact hQcircle.trans_eq hPcircle
  have hJframe : J.cycle.theta E=I.cycle.theta D := by
    change I.cycle.theta D+Q.2.2=I.cycle.theta D
    rw [hQangle]
    ring
  have hnon : AnchorNonincrease I.cycle J.cycle := by
    intro i hi
    by_cases hiE : i=E
    · subst i; exact hJcircle.le
    · rw [(hfixed i hiE).1]
  have hstrict : StrictAnchorLoss I.cycle J.cycle :=
    ⟨E,by norm_num [anchorVertices,E],hJcircle⟩
  exact ⟨J,hfixed,hJframe,hnon,hstrict,hJcircle,
    eInteriorCycle_DE (by linarith [hb.span_lt]) hQ,
    eInteriorCycle_EH (by linarith [hb.span_lt]) hQ⟩

end SignedCycle
end SquaresInCircles.Eight
end
end
end
