module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Tactic
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import SquaresInCircles.Common.Analysis
public import SquaresInCircles.Eight.Boundary.Realization

/-!
# Eight squares: diagonal ties on the zero edges

At a sorted point on a diagonal the local angle is `±π/4` (`localAngle_of_positive_diagonal`,
`localAngle_of_negative_diagonal`). On an edge with quarter increment zero, a negative diagonal at
the source, or a positive diagonal at the target, would make the physical gap smaller than the
frame cap, against a gap above `19/25` (`zero_source_negative_diagonal_impossible`,
`zero_target_positive_diagonal_impossible`). This applies to every ordered signed cycle on the
boundary at a level `q ≤ Q0` with feasible owners, whose gaps exceed `19/25`
(`realized_zero_tie_exclusions`). The opposite diagonals of G and T recode to another binary
quarter word, which the word argument excludes.
-/

section
/-!
## Whole-interval upper-curvature estimates for frame supports

These two elementary calculus consequences retain the complete interval.
The second is the chord bound with an explicit curvature loss.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameCurvature

theorem upper_tangent {l u x t M : ℝ} {f d dd : ℝ → ℝ}
    (hx : x∈Icc l u) (ht : t∈Icc l u)
    (hd : ∀z∈Icc l u,HasDerivAt f (d z) z)
    (he : ∀z∈Icc l u,HasDerivAt d (dd z) z)
    (hM : ∀z∈Icc l u,dd z≤M) :
    f x≤f t+d t*(x-t)+M/2*(x-t)^2 := by
  have hh := curvature_tangent (f := fun z => -f z) (d := fun z => -d z)
    (dd := fun z => -dd z) (κ := -M) hx ht
    (fun z hz => (hd z hz).neg) (fun z hz => (he z hz).neg)
    (fun z hz => neg_le_neg (hM z hz))
  linarith

theorem lower_of_upper_curvature {l u x M m : ℝ} {f d dd : ℝ → ℝ}
    (hx : x∈Icc l u) (hM0 : 0≤M)
    (hd : ∀z∈Icc l u,HasDerivAt f (d z) z)
    (he : ∀z∈Icc l u,HasDerivAt d (dd z) z)
    (hM : ∀z∈Icc l u,dd z≤M) (hl : m<f l) (hu : m<f u) :
    m-M*(u-l)^2/8<f x := by
  let F : ℝ → ℝ := fun z => f z+M/2*(z-l)*(u-z)
  let D : ℝ → ℝ := fun z => d z+M/2*(u+l-2*z)
  have hF {z : ℝ} (hz : z∈Icc l u) : HasDerivAt F (D z) z := by
    have h := (hd z hz).fun_add ((((hasDerivAt_id' z).sub_const l).const_mul (M/2)).fun_mul
      ((hasDerivAt_id' z).const_sub u))
    convert h using 1
    simp only [D]
    ring
  have hD {z : ℝ} (hz : z∈Icc l u) : HasDerivAt D (dd z-M) z := by
    have h := (he z hz).fun_add
      ((((hasDerivAt_id' z).const_mul 2).const_sub (u+l)).const_mul (M/2))
    convert h using 1
    ring
  have hc : ConcaveOn ℝ (Icc l u) F := concave_of_deriv2
    (fun z hz => hF hz) (fun z hz => hD hz) (fun z hz => by linarith [hM z hz])
  have hpos : m<F x := concave_gt_of_endpoints hc hx
    (by simpa [F] using hl) (by simpa [F] using hu)
  have hquad : (x-l)*(u-x)≤(u-l)^2/4 := by nlinarith [sq_nonneg (2*x-l-u)]
  have hm := mul_le_mul_of_nonneg_left hquad hM0
  dsimp [F] at hpos
  linarith

theorem product_cage {s c sl su cl cu : ℝ}
    (hsl : 0≤ sl) (hcl : 0≤cl) (hs : sl≤ s ∧ s≤ su) (hc : cl≤c ∧ c≤cu) :
    sl^2≤ s^2 ∧ s^2≤ su^2 ∧ cl^2≤c^2 ∧ c^2≤cu^2 ∧ sl*cl≤ s*c ∧ s*c≤ su*cu := by
  have hs0 := hsl.trans hs.1
  have hc0 := hcl.trans hc.1
  exact ⟨pow_le_pow_left₀ hsl hs.1 2,pow_le_pow_left₀ hs0 hs.2 2,
    pow_le_pow_left₀ hcl hc.1 2,pow_le_pow_left₀ hc0 hc.2 2,
    mul_le_mul hs.1 hc.1 hcl hs0,mul_le_mul hs.2 hc.2 hc0 (hs0.trans hs.2)⟩

end SquaresInCircles.Eight.FrameCurvature
end
end
end

section
@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight
open Candidate
namespace SignedCycle

theorem localAngle_of_positive_diagonal {C : SignedCycle} {i : Vertex}
    (hs : (C.point i).Sorted) (hd : (C.point i).y=(C.point i).a) :
    C.localAngle i=Real.pi/4 := by
  simp [localAngle,hd,ne_of_gt hs.1,Real.arctan_one]

theorem localAngle_of_negative_diagonal {C : SignedCycle} {i : Vertex}
    (hs : (C.point i).Sorted) (hd : (C.point i).y= -(C.point i).a) :
    C.localAngle i= -(Real.pi/4) := by
  simp [localAngle,hd,ne_of_gt hs.1,Real.arctan_neg,Real.arctan_one]

theorem zero_source_negative_diagonal_impossible {C : SignedCycle}
    (hs : ∀ i,(C.point i).Sorted) (hf : C.StrictSpread) {i : Vertex}
    (hw : Candidate.word i=0) (hg : 19/25<C.physicalGap i) :
    (C.point i).y≠ -(C.point i).a := by
  intro hd
  have hsource := localAngle_of_negative_diagonal (hs i) hd
  have htarget := (localAngle_mem hs (next i)).1
  have hdelta := (abs_lt.mp (hf (next i) i)).2
  have hgap : C.physicalGap i=
      delta C.theta i+C.localAngle i-C.localAngle (next i) := by
    simp [physicalGap,hw]
  rw [hgap,hsource] at hg
  dsimp [delta] at hg
  dsimp [delta,frameCap] at hdelta
  linarith

theorem zero_target_positive_diagonal_impossible {C : SignedCycle}
    (hs : ∀ i,(C.point i).Sorted) (hf : C.StrictSpread) {i : Vertex}
    (hw : Candidate.word i=0) (hg : 19/25<C.physicalGap i) :
    (C.point (next i)).y≠(C.point (next i)).a := by
  intro hd
  have htarget := localAngle_of_positive_diagonal (hs (next i)) hd
  have hsource := (localAngle_mem hs i).2
  have hdelta := (abs_lt.mp (hf (next i) i)).2
  have hgap : C.physicalGap i=
      delta C.theta i+C.localAngle i-C.localAngle (next i) := by
    simp [physicalGap,hw]
  rw [hgap,htarget] at hg
  dsimp [delta] at hg
  dsimp [delta,frameCap] at hdelta
  linarith

/-- The two exclusions for an ordered signed cycle on the boundary at a level `q ≤ Q0` with
feasible owners: its gaps exceed `19/25` by `realized_gap_lower`. -/
theorem realized_zero_tie_exclusions {q : ℝ} (C : SignedCycle)
    (hn : C.Necessary q) (ho : C.Ordered)
    (hr : ∀ i,(C.point i).Boundary q)
    (owner : Vertex → Fin 4) (howner : ∀ i,C.Feasible i (owner i))
    (hq : q≤Q0) (hs : C.StrictSpread) {i : Vertex}
    (hw : Candidate.word i=0) :
    (C.point i).y≠ -(C.point i).a ∧
      (C.point (next i)).y≠(C.point (next i)).a := by
  have hg := C.realized_gap_lower hn ho hr owner howner hq i
  exact ⟨zero_source_negative_diagonal_impossible hn.sorted hs hw hg,
    zero_target_positive_diagonal_impossible hn.sorted hs hw hg⟩

end SignedCycle
end SquaresInCircles.Eight
end
end
end
