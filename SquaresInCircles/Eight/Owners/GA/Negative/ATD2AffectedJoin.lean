module

public import Mathlib.Tactic
public import SquaresInCircles.Eight.Owners.SplitConcavityTools

/-!
# Eight squares: joining the affected AB curve at its intrinsic coefficient equality

The
two tangent estimates join at the common value; the right derivative
may be smaller than the left derivative.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.AffectedJoin
open SplitConcavityTools

theorem downward {f g : ℝ→ℝ} {l c u dL dR : ℝ}
    (hc : c∈Icc l u) (hf : ConcaveOn ℝ (Icc l c) f)
    (hg : ConcaveOn ℝ (Icc c u) g) (he : f c=g c)
    (hdf : HasDerivAt f dL c) (hdg : HasDerivAt g dR c) (hdown : dR≤dL) :
    ConcaveOn ℝ (Icc l u) (fun x => if x≤c then f x else g x) := by
  let F : ℝ→ℝ := fun x => if x≤c then f x else g x
  have hFleft {x : ℝ} (hx : x≤c) : F x=f x := ite_eq_left hx
  have hFright {x : ℝ} (hx : c≤x) : F x=g x := by
    by_cases hxc : x≤c
    · have heq : x=c := le_antisymm hxc hx
      subst x
      simpa [F] using he
    · exact ite_eq_right hxc
  apply concave_of_chords
  intro x hx y hy hxy z hz
  change (y-z)*F x+(z-x)*F y≤(y-x)*F z
  by_cases hyc : y≤c
  · rw [hFleft (hxy.le.trans hyc),hFleft hyc,hFleft (hz.2.trans hyc)]
    exact chord hf ⟨hx.1,hxy.le.trans hyc⟩ ⟨hy.1,hyc⟩ hxy hz
  by_cases hcx : c≤x
  · rw [hFright hcx,hFright (hcx.trans hxy.le),hFright (hcx.trans hz.1)]
    exact chord hg ⟨hcx,hx.2⟩ ⟨hcx.trans hxy.le,hy.2⟩ hxy hz
  have hxc : x<c := lt_of_not_ge hcx
  have hcy : c<y := lt_of_not_ge hyc
  have hfx := tangent_upper hf (show c∈Icc l c from ⟨hc.1,le_rfl⟩) ⟨hx.1,hxc.le⟩ hdf
  have hgy := tangent_upper hg (show c∈Icc c u from ⟨le_rfl,hc.2⟩) ⟨hcy.le,hy.2⟩ hdg
  rw [← he] at hgy
  have hfx' := mul_le_mul_of_nonneg_left hfx (sub_nonneg.mpr hcy.le)
  have hgy' := mul_le_mul_of_nonneg_left hgy (sub_nonneg.mpr hxc.le)
  have hjump := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hdown)
    (mul_nonneg (sub_nonneg.mpr hxc.le) (sub_nonneg.mpr hcy.le))
  have hbridge : (y-c)*f x+(c-x)*g y≤(y-x)*f c := by
    nlinarith only [hfx',hgy',hjump]
  rw [hFleft hxc.le,hFright hcy.le]
  by_cases hzc : z≤c
  · rw [hFleft hzc]
    have hlocal := chord hf ⟨hx.1,hxc.le⟩ ⟨hc.1,le_rfl⟩ hxc ⟨hz.1,hzc⟩
    have hp := mul_le_mul_of_nonneg_left hlocal (sub_nonneg.mpr hxy.le)
    have hq := mul_le_mul_of_nonneg_left hbridge (sub_nonneg.mpr hz.1)
    have hh : (c-x)*((y-z)*f x+(z-x)*g y)≤(c-x)*((y-x)*f z) := by
      nlinarith only [hp,hq]
    exact le_of_mul_le_mul_left hh (sub_pos.mpr hxc)
  · rw [hFright (lt_of_not_ge hzc).le]
    have hlocal := chord hg ⟨le_rfl,hc.2⟩ ⟨hcy.le,hy.2⟩ hcy ⟨(lt_of_not_ge hzc).le,hz.2⟩
    rw [← he] at hlocal
    have hp := mul_le_mul_of_nonneg_left hlocal (sub_nonneg.mpr hxy.le)
    have hq := mul_le_mul_of_nonneg_left hbridge (sub_nonneg.mpr hz.2)
    have hh : (y-c)*((y-z)*f x+(z-x)*g y)≤(y-c)*((y-x)*g z) := by
      nlinarith only [hp,hq]
    exact le_of_mul_le_mul_left hh (sub_pos.mpr hcy)

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.AffectedJoin
