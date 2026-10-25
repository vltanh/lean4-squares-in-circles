module

public import SquaresInCircles.Eight.TableFree.NegativeCaptureStress
public import SquaresInCircles.Eight.TableFree.NegativeLargeDESimplex

/-!
# The four intrinsic vertices of the truncated negative simplex

Uncompiled reconstruction.  At a fixed total angle all three weights
are held fixed.  First the t/e split is concentrated, then the total
hard error is concentrated on the endpoints of its actual interval.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.NegativeCaptureSimplex
open NegativeLargeDECalculus NegativeLargeDESimplex

theorem hard_split_concave {p a lambda α r : ℝ}
    (hp : p∈Ioo (0:ℝ) (18/25)) (hlambda : |lambda|≤117/100)
    (hα : α∈Icc 0 (27/100 : ℝ)) (hr : r∈Icc 0 α) :
    ConcaveOn ℝ (Icc 0 r) (fun t => g p t+g a (α-r)+NegativeLargeDECalculus.f lambda (r-t)) := by
  have htdom (t : ℝ) (ht : t∈Icc 0 r) : t∈Icc 0 (27/100 : ℝ) :=
    ⟨ht.1,ht.2.trans (hr.2.trans hα.2)⟩
  have hedom (t : ℝ) (ht : t∈Icc 0 r) : r-t∈Icc 0 (27/100 : ℝ) :=
    ⟨by linarith [ht.2],by linarith [ht.1,hr.2,hα.2]⟩
  apply concave_of_deriv2
    (f' := fun t => gd p t-fd lambda (r-t))
    (f'' := fun t => gdd p t+fdd lambda (r-t))
  · intro t ht
    have he := (f_hasDerivAt (ε := lambda) (hedom t ht)).comp t
      ((hasDerivAt_const t r).sub (hasDerivAt_id t))
    convert ((g_hasDerivAt hp.1 (htdom t ht)).add_const (g a (α-r))).add he using 1
    · rfl
    · ring
  · intro t ht
    have he := (fd_hasDerivAt (ε := lambda) (hedom t ht)).comp t
      ((hasDerivAt_const t r).sub (hasDerivAt_id t))
    convert (gd_hasDerivAt hp.1 (htdom t ht)).sub he using 1
    · rfl
    · ring
  · intro t ht
    linarith [gdd_upper hp (htdom t ht),fdd_upper hlambda (hedom t ht)]

/-- Two concavity reductions on the original truncated simplex. -/
theorem truncated_min {p a lambda α r₀ t u e : ℝ}
    (hp : p∈Ioo (0:ℝ) (18/25)) (ha : a∈Ioo (0:ℝ) (18/25))
    (hlambda : |lambda|≤117/100) (hα : α∈Icc 0 (27/100 : ℝ))
    (hr₀ : 0≤r₀) (ht : 0≤t) (hu : 0≤u) (he : 0≤e)
    (hsum : t+u+e=α) (hcut : r₀≤t+e) :
    min (g p α+g a 0+NegativeLargeDECalculus.f lambda 0)
      (min (g p 0+g a 0+NegativeLargeDECalculus.f lambda α)
        (min (g p r₀+g a (α-r₀)+NegativeLargeDECalculus.f lambda 0)
          (g p 0+g a (α-r₀)+NegativeLargeDECalculus.f lambda r₀)))≤g p t+g a u+NegativeLargeDECalculus.f lambda e := by
  have hr : t+e∈Icc 0 α := ⟨by linarith,by linarith⟩
  have ht' : t∈Icc 0 (t+e) := ⟨ht,by linarith⟩
  have hfirst := endpoint_min (hard_split_concave (a := a) hp hlambda hα hr) ht'
  have hsub : Icc r₀ α⊆Icc (0:ℝ) α := fun _ hz => ⟨hr₀.trans hz.1,hz.2⟩
  have hordinary := ordinary_split_concave (p := p) (r := a) (β := 1)
    (ε := lambda) hp ha (by norm_num) hα (show (0:ℝ)∈Icc 0 α from ⟨le_rfl,hα.1⟩)
  simp only [sub_zero,one_mul] at hordinary
  have hsecant := second_edge_concave (p := p) (r := a) (β := 1)
    ha (by norm_num) hlambda hα
  simp only [one_mul] at hsecant
  have hleft := endpoint_min (hordinary.subset hsub (convex_Icc _ _))
    (show t+e∈Icc r₀ α from ⟨hcut,hr.2⟩)
  have hright := endpoint_min (hsecant.subset hsub (convex_Icc _ _))
    (show t+e∈Icc r₀ α from ⟨hcut,hr.2⟩)
  simp only [sub_zero,sub_self] at hfirst hleft hright
  rw [show α-(t+e)=u by linarith,show t+e-t=e by ring] at hfirst
  rw [show α-(t+e)=u by linarith] at hleft hright
  set A := g p α+g a 0+NegativeLargeDECalculus.f lambda 0
  set B := g p 0+g a 0+NegativeLargeDECalculus.f lambda α
  set C := g p r₀+g a (α-r₀)+NegativeLargeDECalculus.f lambda 0
  set D := g p 0+g a (α-r₀)+NegativeLargeDECalculus.f lambda r₀
  have hA : min A (min B (min C D))≤A := min_le_left _ _
  have hB : min A (min B (min C D))≤B := (min_le_right _ _).trans (min_le_left _ _)
  have hC : min A (min B (min C D))≤C := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hD : min A (min B (min C D))≤D := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  have hl := (le_min hC hA).trans hleft
  have hr' := (le_min hD hB).trans hright
  exact (le_min hr' hl).trans hfirst

end NegativeCaptureSimplex

namespace NegativeCaptureStress
open NegativeLargeDECalculus NegativeCaptureSimplex

theorem defect_lower_of_vertices {a f α r₀ t u e b : ℝ}
    (hp : a+η∈Ioo (0:ℝ) (18/25)) (ha : a∈Ioo (0:ℝ) (18/25))
    (hlambda : |lambda f α|≤117/100) (hα : α∈Icc 0 (27/100 : ℝ))
    (hr₀ : 0≤r₀) (ht : 0≤t) (hu : 0≤u) (he : 0≤e)
    (hsum : t+u+e=α) (hcut : r₀≤t+e)
    (hfirst : b≤defect a f α α 0 0)
    (hsecond : b≤defect a f α 0 0 α)
    (hthird : b≤defect a f α r₀ (α-r₀) 0)
    (hfourth : b≤defect a f α 0 (α-r₀) r₀) :
    b≤defect a f α t u e := by
  have hz : (0:ℝ)∈Icc 0 (27/100) := by norm_num
  have hr₀' : r₀∈Icc 0 (27/100 : ℝ) := ⟨hr₀,by linarith [hα.2]⟩
  rw [defect_decomposition hα hz] at hfirst hthird
  rw [defect_decomposition hα hα] at hsecond
  rw [defect_decomposition hα hr₀'] at hfourth
  rw [defect_decomposition hα
    (show e∈Icc 0 (27/100 : ℝ) from ⟨he,by linarith [hα.2]⟩)]
  have hlow : b-constant a f α≤
      min (g (a+η) α+g a 0+NegativeLargeDECalculus.f (lambda f α) 0)
        (min (g (a+η) 0+g a 0+NegativeLargeDECalculus.f (lambda f α) α)
          (min (g (a+η) r₀+g a (α-r₀)+NegativeLargeDECalculus.f (lambda f α) 0)
            (g (a+η) 0+g a (α-r₀)+NegativeLargeDECalculus.f (lambda f α) r₀))) := by
    apply le_min
    · linarith
    · apply le_min
      · linarith
      · apply le_min <;> linarith
  have hm := truncated_min hp ha hlambda hα hr₀ ht hu he hsum hcut
  linarith

theorem positive_on_truncated_simplex {a f α r₀ t u e : ℝ}
    (hp : a+η∈Ioo (0:ℝ) (18/25)) (ha : a∈Ioo (0:ℝ) (18/25))
    (hlambda : |lambda f α|≤117/100) (hα : α∈Icc 0 (27/100 : ℝ))
    (hr₀ : 0≤r₀) (ht : 0≤t) (hu : 0≤u) (he : 0≤e)
    (hsum : t+u+e=α) (hcut : r₀≤t+e)
    (hfirst : 0<defect a f α α 0 0)
    (hsecond : 0<defect a f α 0 0 α)
    (hthird : 0<defect a f α r₀ (α-r₀) 0)
    (hfourth : 0<defect a f α 0 (α-r₀) r₀) :
    0<defect a f α t u e := by
  let m := min (defect a f α α 0 0)
    (min (defect a f α 0 0 α)
      (min (defect a f α r₀ (α-r₀) 0) (defect a f α 0 (α-r₀) r₀)))
  have hm : 0< m := lt_min hfirst (lt_min hsecond (lt_min hthird hfourth))
  apply hm.trans_le
  exact defect_lower_of_vertices hp ha hlambda hα hr₀ ht hu he hsum hcut
    (min_le_left _ _) ((min_le_right _ _).trans (min_le_left _ _))
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))

end NegativeCaptureStress
end SquaresInCircles.Eight.TableFree
