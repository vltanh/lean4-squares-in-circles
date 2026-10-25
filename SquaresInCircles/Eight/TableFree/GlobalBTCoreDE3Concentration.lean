module

public import SquaresInCircles.Eight.TableFree.GlobalBTCoreDE3Data

/-!
# Concentrating both core-E prefix placements

The original TD0 split uses the full norm concavity for arbitrary
positive coefficients.  TD2 uses the weighted cosine comparison.
The retained prefix multiplier is fixed throughout each comparison.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalBT.CoreDE3

open FrameCircleArc

def tail (second : Bool) (e c r s t : ℝ) : ℝ :=
  Real.pi-(r+s)-t+(3/2)*kappa+c+e+kappa*Real.cos r+c*Real.cos s+
    (e/2)*Real.cos t+e*(13/12)*Real.sin t-
      R*(if second then tailNorm kappa c (r+s)+tailNorm e c 0
        else tailNorm kappa c r+tailNorm e c s)

def split (e c r s t : ℝ) : ℝ :=
  Real.pi-(r+s)-t+(3/2)*kappa+c+e+(e/2)*Real.cos t+e*(13/12)*Real.sin t+
    normCos kappa c r+normCos c e s

theorem split_concave {e c p t : ℝ} (he : 0<e) (hc : 0<c)
    (hp : p∈Icc 0 frameCap) : ConcaveOn ℝ (Icc 0 p) (fun r => split e c r (p-r) t) := by
  have hfirst := (normCos_concave (a := kappa) (by norm_num [kappa]) hc).subset (Icc_subset_Icc le_rfl hp.2) (convex_Icc 0 p)
  have hlast := concave_affine_argument (normCos_concave hc he)
    (a := -1) (b := p) (l := 0) (u := p)
    (fun r hr => ⟨by linarith [hr.2],by linarith [hp.2,hr.1]⟩)
  have hconstant := affine_concave 0
    (Real.pi-p-t+(3/2)*kappa+c+e+(e/2)*Real.cos t+e*(13/12)*Real.sin t) 0 p
  convert (hconstant.add hfirst).add hlast using 1
  funext r
  dsimp [split]
  rw [show (-1:ℝ)*r+p=p-r by ring]
  ring

theorem split_zero (p t e : ℝ) : split e (weight p) 0 p t=last p t e := by
  dsimp [split,last,normCos]
  rw [tailNorm_comm (weight p) e p]
  simp only [Real.cos_zero,mul_one]
  ring

theorem split_last (p t e : ℝ) : split e (weight p) p 0 t=first p t e := by
  dsimp [split,first,normCos]
  rw [tailNorm_comm (weight p) e 0]
  simp only [Real.cos_zero,mul_one]
  ring

theorem tail_false_split (e c r s t : ℝ) : tail false e c r s t=split e c r s t := by
  dsimp [tail,split,normCos]
  rw [tailNorm_comm c e s]
  ring

theorem concentrated_lower (second : Bool) {r s t e : ℝ}
    (hr : 0≤r) (hs : 0≤ s) (hcap : r+s≤frameCap) (he : 0<e) :
    min (first (r+s) t e) (last (r+s) t e)≤tail second e (weight (r+s)) r s t := by
  have hp : r+s∈Icc 0 frameCap := ⟨add_nonneg hr hs,hcap⟩
  have hc := weight_pos hp
  cases second with
  | false =>
      have hconc := split_concave (t := t) he hc hp
      have hm := hconc.min_le_of_mem_Icc
        (show (0:ℝ)∈Icc 0 (r+s) from ⟨le_rfl,add_nonneg hr hs⟩)
        (show r+s∈Icc 0 (r+s) from ⟨add_nonneg hr hs,le_rfl⟩)
        (show r∈Icc 0 (r+s) from ⟨hr,by linarith⟩)
      simp only [sub_zero,sub_self] at hm
      rw [split_zero,split_last,min_comm] at hm
      rw [tail_false_split]
      simpa only [show r+s-r=s by ring] using hm
  | true =>
      have hcos := cosine_concentration hc.le (weight_bounds hp).2.2
        (show s∈Icc 0 frameCap from ⟨hs,by linarith⟩)
        (show r∈Icc 0 frameCap from ⟨hr,by linarith⟩)
      rw [add_comm s r] at hcos
      have hfirst : first (r+s) t e≤tail true e (weight (r+s)) r s t := by
        dsimp [first,tail]
        linarith only [hcos]
      exact (min_le_left _ _).trans hfirst

end SquaresInCircles.Eight.TableFree.GlobalBT.CoreDE3
