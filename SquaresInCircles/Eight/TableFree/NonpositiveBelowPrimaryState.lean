module

public import SquaresInCircles.Eight.TableFree.OriginalECircle
public import SquaresInCircles.Eight.TableFree.NonpositiveEReplacement

/-!
# An original primary E below D reaches D with two strict margins

Uncompiled reconstruction.  A first actual circle movement creates a
positive common reserve.  Compact minimization keeps that reserve on
E's exact original circle.  At each possible tangent-floor state the
actual necessary seven-cycle is reconstructed and the proved E-zero
exclusion applies.  The least frame therefore reaches D; both original
primary margins remain strictly positive there.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SignedCycle
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
      have hright : I.cycle.theta H-I.cycle.theta D≤m := hm.1
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

end SquaresInCircles.Eight.TableFree.SignedCycle
