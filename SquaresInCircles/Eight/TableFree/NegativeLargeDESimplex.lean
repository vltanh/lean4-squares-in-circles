module

public import SquaresInCircles.Eight.TableFree.NegativeLargeDEStress

/-!
# One common negative-DE stress on its complete angular simplex

Uncompiled draft.  The ordinary-angle curvature is below minus two
fifths, while the secant curvature is below .39.  Two genuine concavity
comparisons therefore reduce the whole simplex to its three geometric
vertices.  All weights remain fixed during both comparisons.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
namespace NegativeLargeDESimplex
open NegativeLargeDECalculus

theorem endpoint_min {F : ℝ → ℝ} {l u x : ℝ}
    (hF : ConcaveOn ℝ (Icc l u) F) (hx : x∈Icc l u) : min (F l) (F u)≤F x := by
  have hh := concave_endpoint_reserve (f := F) (k := (0:ℝ)) (by norm_num) hx
    (by simpa using hF)
  simpa using hh

theorem ordinary_split_concave {p r β ε α e : ℝ}
    (hp : p∈Ioo (0:ℝ) (18/25)) (hr : r∈Ioo (0:ℝ) (18/25)) (hβ : 0≤β)
    (hα : α∈Icc 0 (27/100 : ℝ)) (he : e∈Icc 0 α) :
    ConcaveOn ℝ (Icc 0 (α-e))
      (fun t => g p t+β*g r (α-e-t)+f ε e) := by
  have htdom (t : ℝ) (ht : t∈Icc 0 (α-e)) : t∈Icc 0 (27/100 : ℝ) :=
    ⟨ht.1,by linarith [ht.2,he.1,hα.2]⟩
  have hudom (t : ℝ) (ht : t∈Icc 0 (α-e)) : α-e-t∈Icc 0 (27/100 : ℝ) :=
    ⟨by linarith [ht.2],by linarith [ht.1,he.1,hα.2]⟩
  apply concave_of_deriv2
    (f' := fun t => gd p t-β*gd r (α-e-t))
    (f'' := fun t => gdd p t+β*gdd r (α-e-t))
  · intro t ht
    have hu := (g_hasDerivAt hr.1 (hudom t ht)).comp t
      ((hasDerivAt_const t (α-e)).sub (hasDerivAt_id t))
    convert ((g_hasDerivAt hp.1 (htdom t ht)).add (hu.const_mul β)).add_const (f ε e) using 1
    · rfl
    · ring
  · intro t ht
    have hu := (gd_hasDerivAt hr.1 (hudom t ht)).comp t
      ((hasDerivAt_const t (α-e)).sub (hasDerivAt_id t))
    convert (gd_hasDerivAt hp.1 (htdom t ht)).sub (hu.const_mul β) using 1
    · rfl
    · ring
  · intro t ht
    have hfirst := gdd_upper hp (htdom t ht)
    have hsecond := mul_le_mul_of_nonneg_left (gdd_upper hr (hudom t ht)).le hβ
    nlinarith

theorem first_edge_concave {p r β ε α : ℝ}
    (hp : p∈Ioo (0:ℝ) (18/25)) (hε : |ε|≤117/100)
    (hα : α∈Icc 0 (27/100 : ℝ)) :
    ConcaveOn ℝ (Icc 0 α) (fun e => g p (α-e)+β*g r 0+f ε e) := by
  have hedom (e : ℝ) (he : e∈Icc 0 α) : e∈Icc 0 (27/100 : ℝ) :=
    ⟨he.1,he.2.trans hα.2⟩
  have htdom (e : ℝ) (he : e∈Icc 0 α) : α-e∈Icc 0 (27/100 : ℝ) :=
    ⟨by linarith [he.2],by linarith [he.1,hα.2]⟩
  apply concave_of_deriv2
    (f' := fun e => -gd p (α-e)+fd ε e)
    (f'' := fun e => gdd p (α-e)+fdd ε e)
  · intro e he
    have ht := (g_hasDerivAt hp.1 (htdom e he)).comp e
      ((hasDerivAt_const e α).sub (hasDerivAt_id e))
    convert (ht.add_const (β*g r 0)).add (f_hasDerivAt (hedom e he)) using 1
    · rfl
    · ring
  · intro e he
    have ht := (gd_hasDerivAt hp.1 (htdom e he)).comp e
      ((hasDerivAt_const e α).sub (hasDerivAt_id e))
    convert ht.neg.add (fd_hasDerivAt (hedom e he)) using 1
    · rfl
    · ring
  · intro e he
    linarith [gdd_upper hp (htdom e he),fdd_upper hε (hedom e he)]

theorem second_edge_concave {p r β ε α : ℝ}
    (hr : r∈Ioo (0:ℝ) (18/25)) (hβ : 99/100≤β) (hε : |ε|≤117/100)
    (hα : α∈Icc 0 (27/100 : ℝ)) :
    ConcaveOn ℝ (Icc 0 α) (fun e => g p 0+β*g r (α-e)+f ε e) := by
  have hedom (e : ℝ) (he : e∈Icc 0 α) : e∈Icc 0 (27/100 : ℝ) :=
    ⟨he.1,he.2.trans hα.2⟩
  have hudom (e : ℝ) (he : e∈Icc 0 α) : α-e∈Icc 0 (27/100 : ℝ) :=
    ⟨by linarith [he.2],by linarith [he.1,hα.2]⟩
  apply concave_of_deriv2
    (f' := fun e => -β*gd r (α-e)+fd ε e)
    (f'' := fun e => β*gdd r (α-e)+fdd ε e)
  · intro e he
    have hu := (g_hasDerivAt hr.1 (hudom e he)).comp e
      ((hasDerivAt_const e α).sub (hasDerivAt_id e))
    convert ((hu.const_mul β).const_add (g p 0)).add (f_hasDerivAt (hedom e he)) using 1
    · rfl
    · ring
  · intro e he
    have hu := (gd_hasDerivAt hr.1 (hudom e he)).comp e
      ((hasDerivAt_const e α).sub (hasDerivAt_id e))
    convert (hu.const_mul (-β)).add (fd_hasDerivAt (hedom e he)) using 1
    · rfl
    · ring
  · intro e he
    have hg := mul_le_mul_of_nonneg_left (gdd_upper hr (hudom e he)).le
      (show 0≤β by linarith)
    have hf := fdd_upper hε (hedom e he)
    nlinarith

/-- The minimum is taken over precisely the t-only, u-only and e-only
vertices.  The weights p,r,beta,epsilon have never changed. -/
theorem simplex_min {p r β ε α t u e : ℝ}
    (hp : p∈Ioo (0:ℝ) (18/25)) (hr : r∈Ioo (0:ℝ) (18/25))
    (hβ : 99/100≤β) (hε : |ε|≤117/100)
    (hα : α∈Icc 0 (27/100 : ℝ))
    (ht : 0≤t) (hu : 0≤u) (he : 0≤e) (hsum : t+u+e=α) :
    min (g p α+β*g r 0+f ε 0)
      (min (g p 0+β*g r α+f ε 0) (g p 0+β*g r 0+f ε α))≤
        g p t+β*g r u+f ε e := by
  have he' : e∈Icc 0 α := ⟨he,by linarith⟩
  have ht' : t∈Icc 0 (α-e) := ⟨ht,by linarith⟩
  have hfirst := endpoint_min (ordinary_split_concave hp hr (by linarith) hα he') ht'
  have hleft := endpoint_min (first_edge_concave (r := r) (β := β) hp hε hα) he'
  have hright := endpoint_min (second_edge_concave (p := p) hr hβ hε hα) he'
  simp only [sub_zero,sub_self] at hfirst hleft hright
  rw [show α-e-t=u by linarith] at hfirst
  let A := g p α+β*g r 0+f ε 0
  let B := g p 0+β*g r α+f ε 0
  let C := g p 0+β*g r 0+f ε α
  have hA : min A (min B C)≤A := min_le_left _ _
  have hB : min A (min B C)≤B := (min_le_right _ _).trans (min_le_left _ _)
  have hC : min A (min B C)≤C := (min_le_right _ _).trans (min_le_right _ _)
  have hleft' : min A (min B C)≤g p (α-e)+β*g r 0+f ε e :=
    (le_min hA hC).trans hleft
  have hright' : min A (min B C)≤g p 0+β*g r (α-e)+f ε e :=
    (le_min hB hC).trans hright
  exact (le_min hright' hleft').trans hfirst

end NegativeLargeDESimplex

namespace NegativeLargeDEStress
open NegativeLargeDECalculus NegativeLargeDESimplex

theorem defect_lower_of_vertices {a β ε α t u e b : ℝ}
    (ha : a+η∈Ioo (0:ℝ) (18/25)) (hr : a/β∈Ioo (0:ℝ) (18/25))
    (hβ : 99/100≤β) (hε : |ε|≤117/100)
    (hα : α∈Icc 0 (27/100 : ℝ))
    (ht : 0≤t) (hu : 0≤u) (he : 0≤e) (hsum : t+u+e=α)
    (hfirst : b≤defect a β ε α α 0 0)
    (hsecond : b≤defect a β ε α 0 α 0)
    (hthird : b≤defect a β ε α 0 0 α) :
    b≤defect a β ε α t u e := by
  have hβ0 : 0<β := by linarith
  have hz : (0:ℝ)∈Icc 0 (27/100) := by norm_num
  rw [defect_decomposition hβ0 hα hz] at hfirst hsecond
  rw [defect_decomposition hβ0 hα hα] at hthird
  rw [defect_decomposition hβ0 hα (show e∈Icc 0 (27/100 : ℝ) from ⟨he,by linarith [hα.2]⟩)]
  have hlow : b-constant a β ε α≤
      min (g (a+η) α+β*g (a/β) 0+f ε 0)
        (min (g (a+η) 0+β*g (a/β) α+f ε 0)
          (g (a+η) 0+β*g (a/β) 0+f ε α)) := by
    apply le_min
    · linarith
    · apply le_min <;> linarith
  have hm := simplex_min ha hr hβ hε hα ht hu he hsum
  linarith

theorem positive_on_simplex {a β ε α t u e : ℝ}
    (ha : a+η∈Ioo (0:ℝ) (18/25)) (hr : a/β∈Ioo (0:ℝ) (18/25))
    (hβ : 99/100≤β) (hε : |ε|≤117/100)
    (hα : α∈Icc 0 (27/100 : ℝ))
    (ht : 0≤t) (hu : 0≤u) (he : 0≤e) (hsum : t+u+e=α)
    (hfirst : 0<defect a β ε α α 0 0)
    (hsecond : 0<defect a β ε α 0 α 0)
    (hthird : 0<defect a β ε α 0 0 α) :
    0<defect a β ε α t u e := by
  let m := min (defect a β ε α α 0 0)
    (min (defect a β ε α 0 α 0) (defect a β ε α 0 0 α))
  have hm : 0<m := lt_min hfirst (lt_min hsecond hthird)
  apply hm.trans_le
  exact defect_lower_of_vertices ha hr hβ hε hα ht hu he hsum
    (min_le_left _ _) ((min_le_right _ _).trans (min_le_left _ _))
    ((min_le_right _ _).trans (min_le_right _ _))

end NegativeLargeDEStress
end SquaresInCircles.Eight.TableFree
