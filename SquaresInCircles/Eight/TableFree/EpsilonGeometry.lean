module

public import SquaresInCircles.Eight.TableFree.EpsilonScalar
public import SquaresInCircles.Eight.TableFree.AlignedCycleBounds
public import SquaresInCircles.Eight.TableFree.OrderedCancelingSplit

/-!
# E cannot share H's frame in the actual aligned hard chain

Uncompiled draft.  The original EH axis bounds H's primary coordinate by
the original E tangent.  The original E circle then supplies D's primary
bound through DE3.  Both actual middle circles lie below the corresponding
hard caps.  The same-radius split and the scalar monotonicity theorem
exclude both endpoint choices, without reflecting E or discarding its
original circle slack.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.EpsilonGeometry
open EpsilonCapCalculus EpsilonTangent EpsilonScalar

theorem tangent_of_primary {P : SignedPoint} {x : ℝ}
    (hPc : P.Contained qCap) (hy : 0≤P.y)
    (hx : x∈Icc (1/2 : ℝ) (231/200)) (hxa : x≤P.a) : P.y≤EpsilonCapCalculus.f x := by
  have hcircle : (P.a+1/2)^2+(P.y+1/2)^2≤qCap := by
    simpa [SignedPoint.Contained,SignedPoint.circle,abs_of_nonneg hy] using hPc
  have hprimary := pow_le_pow_left₀ (show 0≤x+1/2 by linarith [hx.1])
    (show x+1/2≤P.a+1/2 by linarith) 2
  have hr := R_sq hx
  have hp := R_pos hx
  dsimp [EpsilonCapCalculus.f]
  nlinarith

theorem E_primary {P : SignedPoint} {b : ℝ}
    (hPs : P.Sorted) (hPc : P.Contained qCap)
    (hb : b∈Icc (0:ℝ) (31/200)) (hy : P.y= -b) : P.a≤EpsilonCapCalculus.f b := by
  have hcircle : (P.a+1/2)^2+(b+1/2)^2≤qCap := by
    simpa [SignedPoint.Contained,SignedPoint.circle,hy,abs_neg,abs_of_nonneg hb.1] using hPc
  have hr := E_root_bounds hb
  dsimp [EpsilonCapCalculus.f]
  nlinarith [hPs.1]

/-- A bound on the outer tangent gives an upper hard cap on the actual
middle tangent.  Only the source circle and its actual separator are
used; no contact equality or independent cap feasibility is assumed. -/
theorem cap_majorizes {P : SignedPoint} {t x z : ℝ}
    (hPs : P.Sorted) (hPy : 0≤P.y) (hPc : P.Contained qCap)
    (ht : t∈Icc 0 (11/50 : ℝ)) (hx : x∈Icc (1/2 : ℝ) (231/200))
    (hz : z≤EpsilonCapCalculus.f x)
    (hsep : 1+edgeWidth t≤z+P.a*Real.cos t-P.y*Real.sin t) :
    P.y+1/2≤H t x := by
  let X := P.a+1/2
  let Z := P.y+1/2
  let p := X*Real.cos t-Z*Real.sin t
  let r := X*Real.sin t+Z*Real.cos t
  have ht' : t∈Icc 0 (7/10 : ℝ) := ⟨ht.1,by linarith [ht.2]⟩
  have htrig := transport_trig ht'
  have hcos : 0≤Real.cos t := by linarith [htrig.1]
  have hsin : 0≤Real.sin t := htrig.2.2.1
  have hcircle : X^2+Z^2≤qCap := by
    simpa [X,Z,SignedPoint.Contained,SignedPoint.circle,abs_of_nonneg hPy] using hPc
  have hcontact : C t x≤p := by
    rw [edgeWidth_positive_formula ht'] at hsep
    dsimp [EpsilonCapCalculus.f] at hz
    dsimp [C,p,X,Z]
    linarith
  have hcpos := C_pos ht hx
  have hpsq := pow_le_pow_left₀ hcpos.le hcontact 2
  have hrot : p^2+r^2=X^2+Z^2 := by
    calc
      p^2+r^2=((Real.sin t)^2+(Real.cos t)^2)*(X^2+Z^2) := by
        dsimp [p,r]
        ring
      _ = X^2+Z^2 := by rw [Real.sin_sq_add_cos_sq,one_mul]
  have hr0 : 0≤r := add_nonneg
    (mul_nonneg (by dsimp [X]; linarith [hPs.1]) hsin)
    (mul_nonneg (by dsimp [Z]; linarith) hcos)
  have hwp := w_pos ht hx
  have hws := w_sq ht hx
  have hrw : r≤w t x := by nlinarith
  have hZ : Z=Real.cos t*r-Real.sin t*p := by
    calc
      Z=Z*((Real.sin t)^2+(Real.cos t)^2) := by rw [Real.sin_sq_add_cos_sq,mul_one]
      _ = Real.cos t*r-Real.sin t*p := by dsimp [p,r]; ring
  have hcr := mul_le_mul_of_nonneg_left hrw hcos
  have hsp := mul_le_mul_of_nonneg_left hcontact hsin
  change Z≤H t x
  rw [hZ]
  dsimp [H]
  linarith

theorem clipped_primary_mem {a b : ℝ}
    (ha : a∈Icc 0 (11/50 : ℝ)) (hb : b∈Icc (0:ℝ) (31/200)) :
    max (diagonalCoordinate qCap) (g a b)∈Icc (1/2 : ℝ) (231/200) := by
  have hg := g_primary ha hb
  have hc := EpsilonActiveRates.diagonal_bounds
  exact ⟨le_trans (by linarith [hc.1]) (le_max_left _ _),
    max_le (by linarith [hc.2]) hg.2⟩

end EpsilonGeometry

namespace SignedCycle
open Candidate EpsilonGeometry

private theorem feasible_quarter (C : SignedCycle) {i k : Vertex} (hw : Candidate.word i=1)
    (hk : next i=k) (j : Fin 4) :
    C.Feasible i j ↔ edgeWidth (C.theta k-C.theta i)≤
      quarterProjection (C.point i) (C.point k) (C.theta k-C.theta i) j := by
  subst hk
  simp only [Feasible,slack,edge,delta,hw,one_ne_zero,↓reduceIte,sub_nonneg]

private theorem feasible_congr {C C' : SignedCycle} {i k : Vertex} (hk : next i=k) {j : Fin 4}
    (h1 : C'.point i=C.point i) (h2 : C'.theta i=C.theta i)
    (h3 : C'.point k=C.point k) (h4 : C'.theta k=C.theta k) :
    C'.Feasible i j ↔ C.Feasible i j := by
  subst hk
  simp only [Feasible,slack,edge,delta,h1,h2,h3,h4]

/-- The actual E=H constraints bound both outer tangents by the same
original E parameter.  Their common angle and the E parameter bounds
come from the original aligned chain, not from a supplied scalar domain. -/
theorem HardInput.epsilon_zero_caps {q : ℝ} (I : HardInput q) (hq : q≤qCap)
    (hHG : I.cycle.theta G=I.cycle.theta H)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hTD : I.cycle.theta T=I.cycle.theta D)
    (hleft : I.cycle.theta A≤I.cycle.theta H)
    (hright : I.cycle.theta D≤I.cycle.theta A)
    (hEHframe : I.cycle.theta E=I.cycle.theta H)
    (hDE : I.cycle.Feasible D 3) (hEH : I.cycle.Feasible E 1) :
    let a := I.cycle.theta H-I.cycle.theta D
    let b := -(I.cycle.point E).y
    a∈Icc 0 (11/50 : ℝ) ∧ b∈Icc 0 (31/200 : ℝ) ∧
      (I.cycle.point H).y≤EpsilonCapCalculus.f (1+b) ∧
      -(I.cycle.point D).y≤EpsilonCapCalculus.f
        (max (diagonalCoordinate qCap) (EpsilonTangent.g a b)) := by
  dsimp only
  let a := I.cycle.theta H-I.cycle.theta D
  let b := -(I.cycle.point E).y
  show a∈Icc 0 (11/50 : ℝ) ∧ b∈Icc 0 (31/200 : ℝ) ∧
      (I.cycle.point H).y≤EpsilonCapCalculus.f (1+b) ∧
      -(I.cycle.point D).y≤EpsilonCapCalculus.f
        (max (diagonalCoordinate qCap) (EpsilonTangent.g a b))
  have hbounds := I.aligned_bounds hq hHG hAB hTD hleft hright
  have ha : a∈Icc 0 (11/50 : ℝ) := ⟨hbounds.span_nonneg,hbounds.span_lt.le⟩
  have hb0 : 0≤b := neg_nonneg.mpr I.E_nonpos
  have h0 : edgeWidth 0=1 := by
    rw [edgeWidth_positive_formula (by norm_num)]; norm_num
  have hEH' : 1≤(I.cycle.point H).a-b := by
    have h := (feasible_quarter I.cycle (i := E) (k := H) (by decide) (by decide) 1).1 hEH
    have h' : edgeWidth (I.cycle.theta H-I.cycle.theta E)≤(I.cycle.point H).a+
        (I.cycle.point E).a*Real.sin (I.cycle.theta H-I.cycle.theta E)+
        (I.cycle.point E).y*Real.cos (I.cycle.theta H-I.cycle.theta E) := h
    rw [hEHframe,sub_self,Real.sin_zero,Real.cos_zero,h0] at h'
    dsimp [b]
    linarith
  have hb : b∈Icc (0:ℝ) (31/200) := ⟨hb0,by linarith [hbounds.H_primary.2]⟩
  have hc (i : Vertex) : (I.cycle.point i).Contained qCap := (I.necessary.contained i).trans hq
  have hHcap := tangent_of_primary (hc H) I.anchors_normal.H_nonneg
    (EpsilonScalar.shifted_primary hb) (show 1+b≤(I.cycle.point H).a by linarith)
  have hEcap := E_primary (I.necessary.sorted E) (hc E) hb
    (show (I.cycle.point E).y= -b by dsimp [b]; ring)
  have hDE' : edgeWidth a≤(I.cycle.point D).a+
      (I.cycle.point E).a*Real.sin a+b*Real.cos a := by
    have h := (feasible_quarter I.cycle (i := D) (k := E) (by decide) (by decide) 3).1 hDE
    have h' : edgeWidth (I.cycle.theta E-I.cycle.theta D)≤(I.cycle.point D).a+
        (I.cycle.point E).a*Real.sin (I.cycle.theta E-I.cycle.theta D)-
        (I.cycle.point E).y*Real.cos (I.cycle.theta E-I.cycle.theta D) := h
    rw [hEHframe] at h'
    dsimp [a,b]
    linarith
  have ha' : a∈Icc 0 (7/10 : ℝ) := ⟨ha.1,by linarith [ha.2]⟩
  have hEprod := mul_le_mul_of_nonneg_right hEcap (transport_trig ha').2.2.1
  have hgD : EpsilonTangent.g a b≤(I.cycle.point D).a := by
    rw [edgeWidth_positive_formula ha'] at hDE'
    dsimp [EpsilonTangent.g]
    linarith
  have hDnormal : 0≤(I.cycle.point D).reflect.y := by
    dsimp [SignedPoint.reflect]
    linarith [I.anchors_normal.D_nonpos]
  have hDcap := tangent_of_primary
    (P := (I.cycle.point D).reflect) (by simpa using hc D) hDnormal
    (EpsilonScalar.g_primary ha hb) (by simpa [SignedPoint.reflect] using hgD)
  have hDdiagonal : -(I.cycle.point D).y≤diagonalCoordinate qCap := by
    simpa [abs_of_nonpos I.anchors_normal.D_nonpos] using
      SignedPoint.contained_minor_le_diagonal (I.necessary.sorted D) (hc D)
  refine ⟨ha,hb,hHcap,?_⟩
  by_cases hg : diagonalCoordinate qCap≤EpsilonTangent.g a b
  · rw [max_eq_right hg]
    simpa [SignedPoint.reflect] using hDcap
  · rw [max_eq_left (le_of_not_ge hg),EpsilonScalar.diagonal_self]
    exact hDdiagonal

/-- Both actual split endpoints contradict the cap sum. -/
theorem HardInput.epsilon_zero_endpoint_impossible {q : ℝ} (I : HardInput q) (hq : q≤qCap)
    (hHG : I.cycle.theta G=I.cycle.theta H)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hTD : I.cycle.theta T=I.cycle.theta D)
    (hleft : I.cycle.theta A≤I.cycle.theta H)
    (hright : I.cycle.theta D≤I.cycle.theta A)
    (hend : I.cycle.theta A=I.cycle.theta H ∨ I.cycle.theta A=I.cycle.theta D)
    (hEHframe : I.cycle.theta E=I.cycle.theta H)
    (hDE : I.cycle.Feasible D 3) (hEH : I.cycle.Feasible E 1) : False := by
  let a := I.cycle.theta H-I.cycle.theta D
  let b := -(I.cycle.point E).y
  let t := I.cycle.theta H-I.cycle.theta A
  let u := I.cycle.theta A-I.cycle.theta D
  obtain ⟨ha,hb,hHcap,hDcap⟩ := I.epsilon_zero_caps hq hHG hAB hTD hleft hright hEHframe hDE hEH
  have hsplit : (t=0 ∧ u=a) ∨ (t=a ∧ u=0) := by
    rcases hend with h | h
    · left; dsimp [t,u,a]; rw [h]; simp
    · right; dsimp [t,u,a]; rw [h]; simp
  have ht : t∈Icc 0 (11/50 : ℝ) := by
    rcases hsplit with ⟨h1,_⟩ | ⟨h1,_⟩
    · rw [h1]; norm_num
    · rw [h1]; exact ha
  have hu : u∈Icc 0 (11/50 : ℝ) := by
    rcases hsplit with ⟨_,h1⟩ | ⟨_,h1⟩
    · rw [h1]; exact ha
    · rw [h1]; norm_num
  have hc (i : Vertex) : (I.cycle.point i).Contained qCap := (I.necessary.contained i).trans hq
  have hcomp := I.aligned_composites hHG hAB hTD
  have hAcap := cap_majorizes (I.necessary.sorted A) I.anchors_normal.A_nonneg (hc A)
    ht (EpsilonScalar.shifted_primary hb) hHcap hcomp.1
  have hBcap := cap_majorizes (P := (I.cycle.point B).reflect)
    (by simpa using I.necessary.sorted B)
    (by dsimp [SignedPoint.reflect]; linarith [I.anchors_normal.B_nonpos])
    (by simpa using hc B) hu (clipped_primary_mem ha hb) hDcap
    (by simpa [u,SignedPoint.reflect,sub_eq_add_neg,add_comm,add_left_comm,add_assoc] using hcomp.2.1)
  have hsum : 2≤EpsilonScalar.value a t u b := by
    dsimp [EpsilonScalar.value]
    dsimp [SignedPoint.reflect] at hBcap
    linarith [hcomp.2.2]
  exact (not_lt_of_ge hsum) (EpsilonScalar.strict_bound ha hb hsplit)

/-- E=H is excluded before any source equality is used.  The split keeps
the literal H, D and E points, frames, circles, and original mixed axes. -/
theorem HardInput.aligned_epsilon_zero_impossible {q : ℝ} (I : HardInput q) (hq : q≤qCap)
    (hHG : I.cycle.theta G=I.cycle.theta H)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hTD : I.cycle.theta T=I.cycle.theta D)
    (hleft : I.cycle.theta A≤I.cycle.theta H)
    (hright : I.cycle.theta D≤I.cycle.theta A)
    (hEHframe : I.cycle.theta E=I.cycle.theta H)
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
  have hJend : J.cycle.theta A=J.cycle.theta H ∨ J.cycle.theta A=J.cycle.theta D := by
    simpa [hJHG,hJTD] using hend
  have horder : J.cycle.theta D≤J.cycle.theta H := by
    rw [hD.2,hH.2]
    exact hright.trans hleft
  have hJleft : J.cycle.theta A≤J.cycle.theta H := by
    rcases hJend with h | h
    · exact h.le
    · rw [h]; exact horder
  have hJright : J.cycle.theta D≤J.cycle.theta A := by
    rcases hJend with h | h
    · rw [h]; exact horder
    · exact h.ge
  have hJEHframe : J.cycle.theta E=J.cycle.theta H := by rw [hE.2,hH.2,hEHframe]
  have hJDE : J.cycle.Feasible D 3 :=
    (feasible_congr (by decide) hD.1 hD.2 hE.1 hE.2).2 hDE
  have hJEH : J.cycle.Feasible E 1 :=
    (feasible_congr (by decide) hE.1 hE.2 hH.1 hH.2).2 hEH
  exact J.epsilon_zero_endpoint_impossible hq hJHG hJAB hJTD hJleft hJright hJend hJEHframe hJDE hJEH

end SignedCycle
end SquaresInCircles.Eight.TableFree
