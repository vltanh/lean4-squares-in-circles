module

public import SquaresInCircles.Eight.Words.Aligned.CycleBounds
public import SquaresInCircles.Eight.Owners.E.ZeroCapped
public import SquaresInCircles.Eight.Owners.Ordered.CancelingSplit

/-!
# Eight squares: E-zero is impossible for the actual aligned hard chain

The E circle bounds both endpoint tangents.  The same
A circle and the actual AB contact then bound B before the original BT
composite is used.  Thus the scalar contradiction is obtained from shared
vertices, with arbitrary radial slack.  The hard split covers both
endpoints; its second endpoint uses only the E-zero symmetry of the
five-anchor inequalities.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.EZeroGeometry
open EZeroFunctions EZeroCapped

theorem E_primary {E : SignedPoint} (_hEs : E.Sorted) (hEc : E.Contained qCap)
    (hE0 : E.y=0) : E.a≤v+1/2 := by
  have hc := hEc
  simp only [SignedPoint.Contained,SignedPoint.circle,hE0,abs_zero] at hc
  have hs := Real.sq_sqrt (show 0≤qCap-1/4 by norm_num [qCap])
  have hn := Real.sqrt_nonneg (qCap-1/4)
  dsimp [v]
  nlinarith

theorem tangent_cap {P E : SignedPoint} {t : ℝ}
    (hPs : P.Sorted) (hy : 0≤P.y) (hPc : P.Contained qCap)
    (hEs : E.Sorted) (hEc : E.Contained qCap) (hE0 : E.y=0)
    (ht : t∈Icc 0 (7/10 : ℝ))
    (hc : edgeWidth t≤P.a+E.a*Real.sin t) : P.y≤capped t := by
  have hE := E_primary hEs hEc hE0
  have hsin := (transport_trig ht).2.2.1
  have hprod := mul_le_mul_of_nonneg_right hE hsin
  have hwidth := edgeWidth_positive_formula ht
  have hup : u t≤P.a+1/2 := by
    rw [hwidth] at hc
    dsimp [u]
    linarith
  have hu := uj_bounds ht
  have huc := pow_le_pow_left₀ hu.1.le hup 2
  have hcircle : (P.a+1/2)^2+(P.y+1/2)^2≤qCap := by
    simpa [SignedPoint.Contained,SignedPoint.circle,abs_of_nonneg hy] using hPc
  have hr := rho_sq ht
  have hrp := rho_pos ht
  have hh : P.y≤h t := by
    have h2 : (P.y+1/2)^2≤(rho t)^2 := by
      rw [hr]
      generalize qCap=Q at hcircle ⊢
      linarith
    have h3 := le_of_pow_le_pow_left₀ two_ne_zero hrp.le h2
    dsimp [h]
    linarith
  have hsort : P.y≤P.a := by simpa [abs_of_nonneg hy] using hPs.2
  have hpsq := pow_le_pow_left₀ (show 0≤P.y+1/2 by linarith) (show P.y+1/2≤P.a+1/2 by linarith) 2
  have hs := Real.sq_sqrt (show 0≤qCap/2 by norm_num [qCap])
  have hn := Real.sqrt_nonneg (qCap/2)
  have hd : P.y≤diagonalCoordinate qCap := by
    dsimp [diagonalCoordinate]
    nlinarith
  exact le_min hd hh

/-- The endpoint theorem uses only five shared circles and the displayed
original composites.  All five normal tangents here are magnitudes. -/
theorem five_anchor_GA_impossible {H A B D E : SignedPoint} {e d : ℝ}
    (hHs : H.Sorted) (_hAs : A.Sorted) (_hBs : B.Sorted) (hDs : D.Sorted) (hEs : E.Sorted)
    (hyH : 0≤H.y) (hyA : 0≤A.y) (hyB : 0≤B.y) (hyD : 0≤D.y)
    (hcH : H.Contained qCap) (hcA : A.Contained qCap) (hcB : B.Contained qCap)
    (hcD : D.Contained qCap) (hcE : E.Contained qCap) (hE0 : E.y=0)
    (he : 0≤e) (hd : 0≤d) (ha : e+d≤7/10)
    (hHA : 2≤H.y+A.a) (hAB : 1≤A.y+B.y)
    (hBD : 1+edgeWidth (e+d)≤B.a*Real.cos (e+d)-B.y*Real.sin (e+d)+D.y)
    (hDE : edgeWidth d≤D.a+E.a*Real.sin d)
    (hEH : edgeWidth e≤H.a+E.a*Real.sin e) : False := by
  have he' : e∈Icc 0 (7/10 : ℝ) := ⟨he,by linarith⟩
  have hd' : d∈Icc 0 (7/10 : ℝ) := ⟨hd,by linarith⟩
  have ha' : e+d∈Icc 0 (7/10 : ℝ) := ⟨add_nonneg he hd,ha⟩
  have hHcap := tangent_cap hHs hyH hcH hEs hcE hE0 he' hEH
  have hDcap := tangent_cap hDs hyD hcD hEs hcE hE0 hd' hDE
  have hb := nested_bounds he'
  have hcap := capped_bounds he'
  have hAc : (A.a+1/2)^2+(A.y+1/2)^2≤qCap := by
    simpa [SignedPoint.Contained,SignedPoint.circle,abs_of_nonneg hyA] using hcA
  have hBc : (B.a+1/2)^2+(B.y+1/2)^2≤qCap := by
    simpa [SignedPoint.Contained,SignedPoint.circle,abs_of_nonneg hyB] using hcB
  have hAlower : 5/2-capped e≤A.a+1/2 := by linarith
  have hApos : 0≤5/2-capped e := by linarith [hcap.2]
  have hAsq := pow_le_pow_left₀ hApos hAlower 2
  have hw := W_sq he'
  have hAupper : A.y+1/2≤W e := by
    have h2 : (A.y+1/2)^2≤(W e)^2 := by
      rw [hw]
      generalize qCap=Q at hAc ⊢
      linarith
    exact le_of_pow_le_pow_left₀ two_ne_zero (by linarith [hb.1]) h2
  have hYlower : Yc e≤B.y+1/2 := by
    dsimp [Yc]
    linarith
  have hYsq := pow_le_pow_left₀ (show 0≤Yc e by linarith [hb.2.2.1]) hYlower 2
  have hcorner := corner_square he'
  have hBupper : B.a-1/2≤Xc e := by
    have h2 : (B.a+1/2)^2≤(Xc e+1)^2 := by
      generalize qCap=Q at hBc hcorner
      linarith
    have h3 := le_of_pow_le_pow_left₀ two_ne_zero (by linarith [hb.2.2.2.2.1]) h2
    linarith
  obtain ⟨hc,hc1,hs,hs1,_⟩ := transport_trig ha'
  have hBcos := mul_le_mul_of_nonneg_right hBupper (show 0≤Real.cos (e+d) by linarith)
  have hYsin := mul_le_mul_of_nonneg_right hYlower hs
  rw [edgeWidth_positive_formula ha'] at hBD
  have hneeded : (3/2 : ℝ)≤Fc e d := by
    dsimp [Fc]
    linarith
  have himpossible := EZeroCapped.maximum he hd ha
  linarith

end EZeroGeometry

namespace SignedCycle
open Candidate EZeroGeometry

private theorem feasible_congr {C C' : SignedCycle} {i k : Vertex} (hk : next i=k) {j : Fin 4}
    (h1 : C'.point i=C.point i) (h2 : C'.theta i=C.theta i)
    (h3 : C'.point k=C.point k) (h4 : C'.theta k=C.theta k) :
    C'.Feasible i j ↔ C.Feasible i j := by
  subst hk
  simp only [Feasible,slack,edge,delta,h1,h2,h3,h4]

theorem HardInput.aligned_zero_E_impossible {q : ℝ} (I : HardInput q) (hq : q≤qCap)
    (hHG : I.cycle.theta G=I.cycle.theta H)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hTD : I.cycle.theta T=I.cycle.theta D)
    (hleft : I.cycle.theta A≤I.cycle.theta H)
    (hright : I.cycle.theta D≤I.cycle.theta A)
    (hE0 : (I.cycle.point E).y=0)
    (hDEorder : I.cycle.theta D≤I.cycle.theta E)
    (hEHorder : I.cycle.theta E≤I.cycle.theta H)
    (hDE : I.cycle.Feasible D 3) (hEH : I.cycle.Feasible E 1) : False := by
  obtain ⟨J,hend,hJAB,hnon,hstrict,hfixed⟩ := I.split_with_source_loss hq hHG hAB.symm hTD
    (by simpa [hHG] using hleft) (by simpa [hTD] using hright)
  have hH := hfixed H (by decide) (by decide)
  have hG := hfixed G (by decide) (by decide)
  have hT := hfixed T (by decide) (by decide)
  have hD := hfixed D (by decide) (by decide)
  have hE := hfixed E (by decide) (by decide)
  have hJHG : J.cycle.theta G=J.cycle.theta H := by rw [hG.2,hH.2,hHG]
  have hJTD : J.cycle.theta T=J.cycle.theta D := by rw [hT.2,hD.2,hTD]
  have hJE0 : (J.cycle.point E).y=0 := by rw [hE.1,hE0]
  have hJDE : J.cycle.Feasible D 3 :=
    (feasible_congr (by decide) hD.1 hD.2 hE.1 hE.2).2 hDE
  have hJEH : J.cycle.Feasible E 1 :=
    (feasible_congr (by decide) hE.1 hE.2 hH.1 hH.2).2 hEH
  have hJE6 : (J.cycle.point 6).y=0 := hJE0
  let e := J.cycle.theta H-J.cycle.theta E
  let d := J.cycle.theta E-J.cycle.theta D
  have he : 0≤e := by dsimp [e]; rw [hH.2,hE.2]; linarith
  have hd : 0≤d := by dsimp [d]; rw [hE.2,hD.2]; linarith
  have ha : e+d≤7/10 := by
    have hs := (abs_le.mp (J.necessary.spread H D)).2
    dsimp [e,d,frameCap] at *
    linarith
  have hDE' : edgeWidth d≤(J.cycle.point D).a+(J.cycle.point E).a*Real.sin d := by
    simpa [Feasible,slack,edge,word,delta,next,D,E,quarterProjection,hJE6,sub_nonneg,d]
      using hJDE
  have hEH' : edgeWidth e≤(J.cycle.point H).a+(J.cycle.point E).a*Real.sin e := by
    simpa [Feasible,slack,edge,word,delta,next,E,H,quarterProjection,hJE6,sub_nonneg,e]
      using hJEH
  have hcomp := J.aligned_composites hJHG hJAB hJTD
  have hc (i : Vertex) : (J.cycle.point i).Contained qCap := (J.necessary.contained i).trans hq
  rcases hend with h | h
  · have hAH : J.cycle.theta A=J.cycle.theta H := h.trans hJHG
    have hHA : 2≤(J.cycle.point H).y+(J.cycle.point A).a := by
      have h := hcomp.1
      simp [hAH] at h
      linarith
    have hBD : 1+edgeWidth (e+d)≤(J.cycle.point B).a*Real.cos (e+d)+
        (J.cycle.point B).y*Real.sin (e+d)-(J.cycle.point D).y := by
      have heq : J.cycle.theta A-J.cycle.theta D=e+d := by rw [hAH]; dsimp [e,d]; ring
      have h := hcomp.2.1
      rw [heq] at h
      linarith
    exact five_anchor_GA_impossible
      (H := J.cycle.point H) (A := J.cycle.point A) (B := (J.cycle.point B).reflect)
      (D := (J.cycle.point D).reflect) (E := J.cycle.point E)
      (J.necessary.sorted H) (J.necessary.sorted A)
      (by simpa using J.necessary.sorted B) (by simpa using J.necessary.sorted D) (J.necessary.sorted E)
      J.anchors_normal.H_nonneg J.anchors_normal.A_nonneg
      (by dsimp [SignedPoint.reflect]; linarith [J.anchors_normal.B_nonpos])
      (by dsimp [SignedPoint.reflect]; linarith [J.anchors_normal.D_nonpos])
      (hc H) (hc A) (by simpa using hc B) (by simpa using hc D) (hc E) hJE0 he hd ha
      hHA (by simp only [SignedPoint.reflect]; linarith [hcomp.2.2])
      (by simp only [SignedPoint.reflect]; linarith [hBD])
      hDE' hEH'
  · have hAD : J.cycle.theta A=J.cycle.theta D := h.trans hJTD
    have hBD : 2≤(J.cycle.point B).a-(J.cycle.point D).y := by
      have h := hcomp.2.1
      simp [hAD] at h
      linarith
    have hHA : 1+edgeWidth (d+e)≤(J.cycle.point H).y+
        (J.cycle.point A).a*Real.cos (d+e)-(J.cycle.point A).y*Real.sin (d+e) := by
      have heq : J.cycle.theta H-J.cycle.theta A=d+e := by rw [hAD]; dsimp [e,d]; ring
      have h := hcomp.1
      rw [heq] at h
      exact h
    exact five_anchor_GA_impossible
      (H := (J.cycle.point D).reflect) (A := (J.cycle.point B).reflect)
      (B := J.cycle.point A) (D := J.cycle.point H) (E := J.cycle.point E)
      (by simpa using J.necessary.sorted D) (by simpa using J.necessary.sorted B)
      (J.necessary.sorted A) (J.necessary.sorted H) (J.necessary.sorted E)
      (by dsimp [SignedPoint.reflect]; linarith [J.anchors_normal.D_nonpos])
      (by dsimp [SignedPoint.reflect]; linarith [J.anchors_normal.B_nonpos])
      J.anchors_normal.A_nonneg J.anchors_normal.H_nonneg
      (by simpa using hc D) (by simpa using hc B) (hc A) (hc H) (hc E) hJE0 hd he
      (by linarith [ha])
      (by simp only [SignedPoint.reflect]; linarith [hBD])
      (by simp only [SignedPoint.reflect]; linarith [hcomp.2.2])
      (by linarith [hHA]) hEH' hDE'

end SignedCycle
end SquaresInCircles.Eight
