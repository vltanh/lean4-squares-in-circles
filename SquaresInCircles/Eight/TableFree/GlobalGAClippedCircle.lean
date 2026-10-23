module

public import SquaresInCircles.Eight.TableFree.GlobalGASortedSupport

/-!
# Constructed support points and exact support-transition gluing

Uncompiled source.  The support point is constructed from the force
vector, with its circle equation and sorting proved explicitly.  It is
used only to estimate a scalar support; no source cycle is moved.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.Secondary

theorem raw_full_support {a b f g : ℝ}
    (hc : (a+1/2)^2+(b+1/2)^2≤qCap) :
    f*a+g*b≤fullSupport f g := by
  have hcircle : normSq (a+1/2,b+1/2)≤R^2 := by
    rw [radius_sq]
    exact hc
  have h := dot_le_radius (v:=(f,g)) (p:=(a+1/2,b+1/2))
    (Real.sqrt_nonneg qCap) hcircle
  dsimp [dot,vectorLength,normSq,fullSupport] at *
  linarith

theorem raw_clipped_support {a b f g : ℝ}
    (hc : (a+1/2)^2+(b+1/2)^2≤qCap)
    (hs : b≤a) (hcorner : 0≤a+b+1) (hfg : 0≤f+g) :
    f*a+g*b≤clippedSupport f g := by
  unfold clippedSupport
  split_ifs with he
  · have hsum : a+b≤2*diagonal := by
      have hd : 0≤2*diagonal+1 := by linarith [diagonal_bounds.1]
      nlinarith [diagonal_circle,sq_nonneg (a-b)]
    have h₁ := mul_le_mul_of_nonneg_left hsum hfg
    have h₂ := mul_nonneg (sub_nonneg.mpr he) (sub_nonneg.mpr hs)
    dsimp [diagonalSupport]
    nlinarith
  · exact raw_full_support hc

structure ClippedPoint (f g : ℝ) where
  a : ℝ
  b : ℝ
  circle : (a+1/2)^2+(b+1/2)^2=qCap
  sorted : b≤a
  corners_nonneg : 0≤a+1/2 ∧ 0≤b+1/2
  primary_lower : diagonal≤a
  tangent_upper : b≤diagonal
  supports : clippedSupport f g=f*a+g*b

/-- The diagonal and interior formulas construct every support needed
for D.  Positivity of the transverse force is proved at the actual
D arguments by the later invocation. -/
def clippedPoint {f g : ℝ} (hsum : 0≤f+g) (hg : 0<g) : ClippedPoint f g := by
  classical
  by_cases hfg : f≤g
  · exact {
      a := diagonal
      b := diagonal
      circle := by nlinarith [diagonal_circle]
      sorted := le_rfl
      corners_nonneg := ⟨by linarith [diagonal_bounds.1],by linarith [diagonal_bounds.1]⟩
      primary_lower := le_rfl
      tangent_upper := le_rfl
      supports := by simp [clippedSupport,hfg,diagonalSupport]; ring }
  · have hf : 0<f := hg.trans (lt_of_not_ge hfg)
    let N := Real.sqrt (f^2+g^2)
    have hN : 0<N := Real.sqrt_pos.mpr (by positivity)
    have hN2 : N^2=f^2+g^2 := Real.sq_sqrt (by positivity)
    let a := R*f/N-1/2
    let b := R*g/N-1/2
    have ha : a+1/2=R*f/N := by dsimp [a]; ring
    have hb : b+1/2=R*g/N := by dsimp [b]; ring
    have ha0 : 0≤a+1/2 := by rw [ha]; positivity
    have hb0 : 0≤b+1/2 := by rw [hb]; positivity
    have hsort : b≤a := by
      dsimp [a,b]
      have hh := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (lt_of_not_ge hfg).le (Real.sqrt_nonneg qCap)) hN.le
      linarith
    have hc : (a+1/2)^2+(b+1/2)^2=qCap := by
      rw [ha,hb]
      field_simp [hN.ne']
      nlinarith [congrArg (fun x : ℝ => x*(f^2+g^2)) radius_sq,
        congrArg (fun x : ℝ => qCap*x) hN2]
    have hcompare := mul_nonneg (sub_nonneg.mpr hsort)
      (show 0≤a+b+1 by linarith)
    have hda : diagonal≤a := by
      nlinarith [diagonal_circle,diagonal_bounds.1]
    have hbd : b≤diagonal := by
      nlinarith [diagonal_circle,diagonal_bounds.1]
    have hs : clippedSupport f g=f*a+g*b := by
      rw [clippedSupport,if_neg hfg]
      change R*N-(f+g)/2=f*a+g*b
      dsimp [a,b]
      field_simp [hN.ne']
      nlinarith [congrArg (fun x : ℝ => R*x) hN2]
    exact ⟨a,b,hc,hsort,⟨ha0,hb0⟩,hda,hbd,hs⟩

/-- Continuous support formulas can be joined at their exact equality
events.  Both branch estimates are proved on the full interval before
this elementary intermediate-value argument is invoked. -/
theorem monotone_continuous_switch {f g e : ℝ → ℝ} {a b : ℝ}
    (he : Continuous e) (hf : MonotoneOn f (Icc a b))
    (hg : MonotoneOn g (Icc a b))
    (hmatch : ∀x∈Icc a b,e x=0 → f x=g x) :
    MonotoneOn (fun x => if e x≤0 then f x else g x) (Icc a b) := by
  intro x hx y hy hxy
  by_cases hx0 : e x≤0 <;> by_cases hy0 : e y≤0
  · simpa [hx0,hy0] using hf hx hy hxy
  · have hypos : 0<e y := lt_of_not_ge hy0
    obtain ⟨z,hz,hze⟩ := intermediate_value_Icc hxy he.continuousOn
      (show (0:ℝ)∈Icc (e x) (e y) from ⟨hx0,hypos.le⟩)
    have hz' : z∈Icc a b := ⟨hx.1.trans hz.1,hz.2.trans hy.2⟩
    have h₁ := hf hx hz' hz.1
    have h₂ := hg hz' hy hz.2
    rw [hmatch z hz' hze] at h₁
    simpa [hx0,hy0] using h₁.trans h₂
  · have hxpos : 0<e x := lt_of_not_ge hx0
    obtain ⟨z,hz,hze⟩ := intermediate_value_Icc hxy he.neg.continuousOn
      (show (0:ℝ)∈Icc (-e x) (-e y) from ⟨by linarith,by linarith⟩)
    have hz' : z∈Icc a b := ⟨hx.1.trans hz.1,hz.2.trans hy.2⟩
    have h₁ := hg hx hz' hz.1
    have h₂ := hf hz' hy hz.2
    rw [hmatch z hz' (by linarith)] at h₂
    simpa [hx0,hy0] using h₁.trans h₂
  · simpa [hx0,hy0] using hg hx hy hxy

end SquaresInCircles.Eight.TableFree.GlobalGA.Secondary
