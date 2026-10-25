module

public import Mathlib.Tactic
public import SquaresInCircles.Common.Analysis

/-!
# Eight squares: joining the smooth pieces of a split argument

Elementary calculus for the joins of branches: a minimum of concave branches (`minimum`,
`minimum_add`), composition with a concave increasing function (`compose`), matching tangent lines
at one transition of supports (`join`), and the minimum at an endpoint for a function with convex
derivative and nonpositive final derivative (`minimum_of_convex_derivative`).
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SplitConcavityTools

theorem minimum_add (a b c : ℝ) : min a b+c=min (a+c) (b+c) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h,min_eq_left (by linarith : a+c≤b+c)]
  · rw [min_eq_right h,min_eq_right (by linarith : b+c≤a+c)]

theorem minimum {f g : ℝ→ℝ} {l u : ℝ}
    (hf : ConcaveOn ℝ (Icc l u) f) (hg : ConcaveOn ℝ (Icc l u) g) :
    ConcaveOn ℝ (Icc l u) (fun x => min (f x) (g x)) := by
  refine ⟨hf.1,?_⟩
  intro x hx y hy r s hr hs hrs
  have hfx := mul_le_mul_of_nonneg_left (min_le_left (f x) (g x)) hr
  have hfy := mul_le_mul_of_nonneg_left (min_le_left (f y) (g y)) hs
  have hgx := mul_le_mul_of_nonneg_left (min_le_right (f x) (g x)) hr
  have hgy := mul_le_mul_of_nonneg_left (min_le_right (f y) (g y)) hs
  have h₁ := hf.2 hx hy hr hs hrs
  have h₂ := hg.2 hx hy hr hs hrs
  simp only [smul_eq_mul] at h₁ h₂ ⊢
  exact le_min (by linarith) (by linarith)

theorem compose {f g : ℝ→ℝ} {L U l u : ℝ}
    (hf : ConcaveOn ℝ (Icc L U) f) (hm : MonotoneOn f (Icc L U))
    (hg : ConcaveOn ℝ (Icc l u) g) (hmap : ∀x∈Icc l u,g x∈Icc L U) :
    ConcaveOn ℝ (Icc l u) (fun x => f (g x)) := by
  refine ⟨hg.1,?_⟩
  intro x hx y hy r s hr hs hrs
  have hxy := hg.1 hx hy hr hs hrs
  have hweighted := hf.1 (hmap x hx) (hmap y hy) hr hs hrs
  have hinner := hg.2 hx hy hr hs hrs
  have houter := hf.2 (hmap x hx) (hmap y hy) hr hs hrs
  exact houter.trans (hm hweighted (hmap _ hxy) hinner)

theorem tangent_upper {f : ℝ→ℝ} {l u t x d : ℝ}
    (hf : ConcaveOn ℝ (Icc l u) f) (ht : t∈Icc l u) (hx : x∈Icc l u)
    (hd : HasDerivAt f d t) : f x≤f t+d*(x-t) := by
  have hc : ConvexOn ℝ (Icc l u) (fun y => -f y) := hf.neg
  rcases lt_trichotomy t x with h | rfl | h
  · have hh := hc.le_slope_of_hasDerivAt ht hx h hd.neg
    rw [slope_def_field,le_div_iff₀ (sub_pos.mpr h)] at hh
    linarith
  · simp
  · have hh := hc.slope_le_of_hasDerivAt hx ht h hd.neg
    rw [slope_def_field,div_le_iff₀ (sub_pos.mpr h)] at hh
    linarith

theorem chord {f : ℝ→ℝ} {l u x y z : ℝ}
    (hf : ConcaveOn ℝ (Icc l u) f) (hx : x∈Icc l u) (hy : y∈Icc l u)
    (hxy : x<y) (hz : z∈Icc x y) :
    (y-z)*f x+(z-x)*f y≤(y-x)*f z := by
  have hden : 0<y-x := sub_pos.mpr hxy
  have hsum : (y-z)/(y-x)+(z-x)/(y-x)=1 := by field_simp; ring
  have hpoint : ((y-z)/(y-x))•x+((z-x)/(y-x))•y=z := by
    simp only [smul_eq_mul]
    field_simp
    ring
  have hh := hf.2 hx hy (div_nonneg (sub_nonneg.mpr hz.2) hden.le)
    (div_nonneg (sub_nonneg.mpr hz.1) hden.le) hsum
  rw [hpoint] at hh
  simp only [smul_eq_mul] at hh
  have hp := mul_le_mul_of_nonneg_left hh hden.le
  field_simp [hden.ne'] at hp
  nlinarith only [hp]

theorem concave_of_chords {f : ℝ→ℝ} {l u : ℝ}
    (hchord : ∀x∈Icc l u,∀y∈Icc l u,x<y→∀z∈Icc x y,
      (y-z)*f x+(z-x)*f y≤(y-x)*f z) : ConcaveOn ℝ (Icc l u) f := by
  have hordered : ∀x∈Icc l u,∀y∈Icc l u,∀r s : ℝ,
      0≤r → 0≤s → r+s=1 → x≤y → r*f x+s*f y≤f (r*x+s*y) := by
    intro x hx y hy r s hr hs hrs hxy
    rcases hxy.eq_or_lt with he | hxy
    · subst y
      have hpoint : r*x+s*x=x := by nlinarith only [congrArg (fun v : ℝ => v*x) hrs]
      rw [hpoint]
      nlinarith only [congrArg (fun v : ℝ => v*f x) hrs]
    · let z : ℝ := r*x+s*y
      have hleft : z-x=s*(y-x) := by
        dsimp [z]
        linear_combination x*hrs
      have hright : y-z=r*(y-x) := by
        dsimp [z]
        linear_combination -y*hrs
      have hz : z∈Icc x y := by
        constructor
        · have hp := mul_nonneg hs (sub_nonneg.mpr hxy.le)
          linarith
        · have hp := mul_nonneg hr (sub_nonneg.mpr hxy.le)
          linarith
      have hh := hchord x hx y hy hxy z hz
      rw [hleft,hright] at hh
      have hp : (y-x)*(r*f x+s*f y)≤(y-x)*f z := by nlinarith only [hh]
      exact le_of_mul_le_mul_left hp (sub_pos.mpr hxy)
  refine ⟨convex_Icc l u,?_⟩
  intro x hx y hy r s hr hs hrs
  simp only [smul_eq_mul]
  rcases le_total x y with hxy | hyx
  · exact hordered x hx y hy r s hr hs hrs hxy
  · simpa only [add_comm] using hordered y hy x hx s r hs hr (by linarith) hyx

/-- Matching values and first derivatives join two concave support branches. -/
theorem join {f g : ℝ→ℝ} {l c u d : ℝ}
    (hc : c∈Icc l u) (hf : ConcaveOn ℝ (Icc l c) f) (hg : ConcaveOn ℝ (Icc c u) g)
    (he : f c=g c) (hdf : HasDerivAt f d c) (hdg : HasDerivAt g d c) :
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
  have hbridge : (y-c)*f x+(c-x)*g y≤(y-x)*f c := by
    nlinarith only [hfx',hgy']
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

/-- A function whose derivative is convex and nonpositive at the right endpoint takes its minimum
at an endpoint; this is the shape of the cubic reserve of the high coefficient. -/
theorem minimum_of_convex_derivative {f d : ℝ→ℝ} {l u x : ℝ}
    (hf : ∀y∈Icc l u,HasDerivAt f (d y) y)
    (hd : ConvexOn ℝ (Icc l u) d) (hdu : d u≤0) (hx : x∈Icc l u) :
    min (f l) (f u)≤f x := by
  have hu : u∈Icc l u := ⟨hx.1.trans hx.2,le_rfl⟩
  have hnonpos {a b : ℝ} (ha : a∈Icc l u) (hb : b∈Icc a u) (hda : d a≤0) : d b≤0 := by
    have hh : min (-d a) (-d u)≤-d b := hd.neg.min_le_of_mem_Icc ha hu hb
    have hm : 0≤min (-d a) (-d u) := le_min (by linarith) (by linarith)
    linarith
  by_cases hdx : d x≤0
  · have hm : AntitoneOn f (Icc x u) := by
      apply antiOn_of_hasDeriv_nonpos
      · intro y hy
        exact (hf y ⟨hx.1.trans hy.1,hy.2⟩).continuousAt.continuousWithinAt
      · intro y hy
        exact hf y ⟨hx.1.trans hy.1.le,hy.2.le⟩
      · intro y hy
        exact hnonpos hx ⟨hy.1.le,hy.2.le⟩ hdx
    exact (min_le_right _ _).trans (hm ⟨le_rfl,hx.2⟩ ⟨hx.2,le_rfl⟩ hx.2)
  · have hm : MonotoneOn f (Icc l x) := by
      apply monoOn_of_hasDeriv_nonneg
      · intro y hy
        exact (hf y ⟨hy.1,hy.2.trans hx.2⟩).continuousAt.continuousWithinAt
      · intro y hy
        exact hf y ⟨hy.1.le,hy.2.le.trans hx.2⟩
      · intro y hy
        by_contra! hdy
        exact hdx (hnonpos ⟨hy.1.le,hy.2.le.trans hx.2⟩ ⟨hy.2.le,hx.2⟩ hdy.le)
    exact (min_le_left _ _).trans (hm ⟨le_rfl,hx.1⟩ ⟨hx.1,le_rfl⟩ hx.1)

end SquaresInCircles.Eight.SplitConcavityTools
