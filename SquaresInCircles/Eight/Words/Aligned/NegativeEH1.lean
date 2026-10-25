module

public import SquaresInCircles.Eight.Owners.Negative.ContactGeometry
public import SquaresInCircles.Eight.Words.Aligned.CycleBounds
public import SquaresInCircles.Eight.Words.Aligned.NegativeEH1Arc

/-!
# Eight squares: a hard endpoint for the short retained-EH1 branch

Compact minimization runs over the H/G circle arc with the positive reserve `(t-x)/4000`
(`Source.eh1_hard_point`). At a minimizing boundary the EH1 slack lies in the strip where its
derivative is negative (`Source.highMixedDerivative_negative`). The strict slack at the GA0
endpoint pays for a contraction on H's own circle (`Source.eh1_hard_endpoint`), which keeps any
earlier anchor loss.
-/

section
/-!
## The mixed E owners after alignment of the other anchors

The core exclusion `core_impossible` takes either original owner on each mixed edge, with
individual errors of either sign, at the original E point and frame. For nonnegative individual
errors, sorting and the remaining radial alternative (`HardInput.aligned_E_radial`) then give
the primary mixed axes DE3 and EH1 (`HardInput.aligned_primary_E_witnesses`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace AlignedMixedE

theorem cosine_loss {x : ℝ} (hx : x∈Icc 0 (7/10 : ℝ)) :
    1-Real.cos x≤(3/8)*Real.sin x := by
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hx
  have hcoef : 0≤(3/8)*(1+Real.cos x)-Real.sin x := by linarith
  have hprod := mul_nonneg hs0 hcoef
  have hid :
      (1+Real.cos x)*((3/8)*Real.sin x-(1-Real.cos x))=
        Real.sin x*((3/8)*(1+Real.cos x)-Real.sin x) := by
    nlinarith [Real.sin_sq_add_cos_sq x]
  by_contra! hbad
  have hneg := mul_neg_of_pos_of_neg (show 0<1+Real.cos x by linarith)
    (show (3/8)*Real.sin x-(1-Real.cos x)<0 by linarith)
  linarith

/-- The worst signed minor coefficient covers both primary mixed axes.
The negative-angle branch uses the lower primary bound as well. -/
theorem core_primary_charge {a b d : ℝ}
    (ha : a∈Icc (1/2 : ℝ) (7/12)) (hb : -(7/12 : ℝ)≤b)
    (hd : |d|≤7/10) :
    1-(1/2)*Real.sin d≤edgeWidth d-a*Real.sin d+b*(1-Real.cos d) := by
  by_cases hd0 : 0≤d
  · have hdi : d∈Icc 0 (7/10 : ℝ) := ⟨hd0,by simpa [abs_of_nonneg hd0] using hd⟩
    obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hdi
    have hl := cosine_loss hdi
    have ha' := mul_le_mul_of_nonneg_right ha.2 hs0
    have hb' := mul_le_mul_of_nonneg_right hb (sub_nonneg.mpr hc1)
    rw [edgeWidth_positive_formula hdi]
    nlinarith
  · have hdn : -d∈Icc 0 (7/10 : ℝ) :=
      ⟨by linarith,by simpa [abs_of_nonpos (by linarith : d≤0)] using hd⟩
    obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hdn
    have hl := cosine_loss hdn
    have ha' := mul_le_mul_of_nonneg_right ha.1 hs0
    have hb' := mul_le_mul_of_nonneg_right hb (sub_nonneg.mpr hc1)
    have hw := edgeWidth_negative_formula hdn
    simp only [neg_neg] at hw
    have hsin : Real.sin d= -Real.sin (-d) := by simp
    have hcos : Real.cos d=Real.cos (-d) := by simp
    rw [hw,hsin,hcos]
    nlinarith

theorem rotated_charge {a b d : ℝ}
    (ha : 1/2≤a) (hb : b∈Icc (0:ℝ) 1) (hd : |d|≤7/10) :
    1-(1/2)*Real.sin d≤edgeWidth d+a*(1-Real.cos d)-b*Real.sin d := by
  by_cases hd0 : 0≤d
  · have hdi : d∈Icc 0 (7/10 : ℝ) := ⟨hd0,by simpa [abs_of_nonneg hd0] using hd⟩
    obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hdi
    have ha' := mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hc1)
    have hb' := mul_nonneg (sub_nonneg.mpr hb.2) hs0
    rw [edgeWidth_positive_formula hdi]
    nlinarith
  · have hdn : -d∈Icc 0 (7/10 : ℝ) :=
      ⟨by linarith,by simpa [abs_of_nonpos (by linarith : d≤0)] using hd⟩
    obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hdn
    have ha' := mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hc1)
    have hb' := mul_nonneg hb.1 hs0
    have hw := edgeWidth_negative_formula hdn
    simp only [neg_neg] at hw
    have hsin : Real.sin d= -Real.sin (-d) := by simp
    have hcos : Real.cos d=Real.cos (-d) := by simp
    rw [hw,hsin,hcos]
    nlinarith

/-- The selected physical axes give two unrotated demands. The E tangent cancels in the sum
of the two weak inequalities. -/
theorem core_pair {H D E : SignedPoint} {u v : ℝ}
    (hHa : 1/2≤H.a) (hDa : 1/2≤D.a)
    (hHy : H.y∈Icc (0:ℝ) 1) (hDy : -D.y∈Icc (0:ℝ) 1)
    (hEa : E.a∈Icc (1/2 : ℝ) (7/12))
    (hEy : E.y∈Icc (-(7/12) : ℝ) 0)
    (hu : |u|≤7/10) (hv : |v|≤7/10)
    (hDE : quarterFeasible D E u 2 ∨ quarterFeasible D E u 3)
    (hEH : quarterFeasible E H v 0 ∨ quarterFeasible E H v 1) :
    2-(1/2)*(Real.sin u+Real.sin v)≤H.a+D.a := by
  have hD : 1-(1/2)*Real.sin u≤D.a-E.y := by
    rcases hDE with hDE | hDE
    · have hh := rotated_charge hDa hDy hu
      simp only [quarterFeasible,quarterProjection,Matrix.cons_val_two,Matrix.tail_cons,
        Matrix.head_cons] at hDE
      linarith
    · have hh := core_primary_charge hEa
        (show -(7/12 : ℝ)≤ -E.y by linarith [hEy.2]) hu
      simp only [quarterFeasible,quarterProjection,Matrix.cons_val_three,Matrix.tail_cons,
        Matrix.head_cons] at hDE
      linarith
  have hH : 1-(1/2)*Real.sin v≤H.a+E.y := by
    rcases hEH with hEH | hEH
    · have hh := rotated_charge hHa hHy hv
      simp only [quarterFeasible,quarterProjection,Matrix.cons_val_zero] at hEH
      linarith
    · have hh := core_primary_charge hEa hEy.1 hv
      simp only [quarterFeasible,quarterProjection,Matrix.cons_val_one,Matrix.cons_val_zero] at hEH
      linarith
  linarith

theorem sine_pair_bound {u v : ℝ} (hs : u+v∈Icc 0 (11/50 : ℝ)) :
    Real.sin u+Real.sin v≤2*Real.sin ((u+v)/2) := by
  have hw : (u+v)/2∈Icc 0 (7/10 : ℝ) := ⟨by linarith [hs.1],by linarith [hs.2]⟩
  have hsin := (transport_trig hw).2.2.1
  have hmul := mul_le_mul_of_nonneg_left (Real.cos_le_one ((u-v)/2)) hsin
  have hid : Real.sin u+Real.sin v=
      2*Real.sin ((u+v)/2)*Real.cos ((u-v)/2) := by
    calc
      Real.sin u+Real.sin v=
          Real.sin ((u+v)/2+(u-v)/2)+Real.sin ((u+v)/2-(u-v)/2) := by
        congr 1 <;> congr 1 <;> ring
      _=2*Real.sin ((u+v)/2)*Real.cos ((u-v)/2) := by
        rw [Real.sin_add,Real.sin_sub]
        ring
  rw [hid]
  linarith

theorem short_primary_gap {s : ℝ} (hs : s∈Icc 0 (11/50 : ℝ)) :
    1248/625-(359/500)*Real.sin s<2-Real.sin (s/2) := by
  have hw : s/2∈Icc 0 (7/10 : ℝ) := ⟨by linarith [hs.1],by linarith [hs.2]⟩
  have hsin := (transport_trig hw).2.2.1
  have hhalf : (s/2)^2≤(11/100 : ℝ)^2 := by
    exact pow_le_pow_left₀ hw.1 (by linarith [hs.2]) 2
  have hcos : 99/100<Real.cos (s/2) := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := s/2)]
  have hprod := mul_nonneg hsin (show 0≤(359/250)*Real.cos (s/2)-1 by linarith)
  have hdouble := Real.sin_two_mul (s/2)
  have heq : 2*(s/2)=s := by ring
  rw [heq] at hdouble
  linarith

theorem core_impossible {H D E : SignedPoint} {u v : ℝ}
    (hHa : 1/2≤H.a) (hDa : 1/2≤D.a)
    (hHy : H.y∈Icc (0:ℝ) 1) (hDy : -D.y∈Icc (0:ℝ) 1)
    (hEa : E.a∈Icc (1/2 : ℝ) (7/12))
    (hEy : E.y∈Icc (-(7/12) : ℝ) 0)
    (hu : |u|≤7/10) (hv : |v|≤7/10)
    (hs : u+v∈Icc 0 (11/50 : ℝ))
    (hsum : H.a+D.a<1248/625-(359/500)*Real.sin (u+v))
    (hDE : quarterFeasible D E u 2 ∨ quarterFeasible D E u 3)
    (hEH : quarterFeasible E H v 0 ∨ quarterFeasible E H v 1) : False := by
  have hpair := core_pair hHa hDa hHy hDy hEa hEy hu hv hDE hEH
  have hsines := sine_pair_bound hs
  have hgap := short_primary_gap hs
  linarith

/-- Sorting compensates the possibly negative first coefficient on DE.
The radial alternative supplies the second coefficient at the same E. -/
theorem DE_primary_of_nonneg {D E : SignedPoint} {u : ℝ}
    (hDs : D.Sorted) (hEs : E.Sorted) (hDy : D.y≤0) (hEy : E.y≤0)
    (hrad : -D.y≤E.a) (hu : u∈Icc 0 (7/10 : ℝ))
    (hDE : quarterFeasible D E u 2) : quarterFeasible D E u 3 := by
  have hDsort : -D.y≤D.a := by simpa [abs_of_nonpos hDy] using hDs.2
  have hEsort : -E.y≤E.a := by simpa [abs_of_nonpos hEy] using hEs.2
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hu
  have hphi := one_le_abs_cos_add_abs_sin u
  rw [abs_of_nonneg (by linarith : 0≤Real.cos u),abs_of_nonneg hs0] at hphi
  have hfirst := mul_nonneg (show 0≤D.a+E.y+E.a+D.y by linarith)
    (sub_nonneg.mpr hc1)
  have hsecond := mul_nonneg (show 0≤E.a+D.y by linarith)
    (show 0≤Real.sin u-(1-Real.cos u) by linarith)
  simp only [quarterFeasible,quarterProjection,Matrix.cons_val_two,Matrix.tail_cons,
    Matrix.head_cons] at hDE
  simp only [quarterFeasible,quarterProjection,Matrix.cons_val_three,Matrix.tail_cons,
    Matrix.head_cons]
  linarith

theorem EH_primary_of_nonneg {H E : SignedPoint} {v : ℝ}
    (hHa : 0≤H.a) (hEy : E.y≤0) (hrad : H.y≤E.a)
    (hv : v∈Icc 0 (7/10 : ℝ))
    (hEH : quarterFeasible E H v 0) : quarterFeasible E H v 1 := by
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hv
  have hfirst := mul_nonneg (show 0≤H.a-E.y by linarith) (sub_nonneg.mpr hc1)
  have hsecond := mul_nonneg (sub_nonneg.mpr hrad) hs0
  simp only [quarterFeasible,quarterProjection,Matrix.cons_val_zero] at hEH
  simp only [quarterFeasible,quarterProjection,Matrix.cons_val_one,Matrix.cons_val_zero]
  linarith

end AlignedMixedE

namespace SignedCycle
open Candidate AlignedMixedE

private theorem feasible_D_iff (C : SignedCycle) (j : Fin 4) :
    C.Feasible D j ↔ quarterFeasible (C.point D) (C.point E) (C.theta E-C.theta D) j := by
  rw [Feasible,slack,edge,ite_eq_right (show Candidate.word D≠0 by decide),delta,
    show next D=E from rfl,quarterFeasible,sub_nonneg]

private theorem feasible_E_iff (C : SignedCycle) (j : Fin 4) :
    C.Feasible E j ↔ quarterFeasible (C.point E) (C.point H) (C.theta H-C.theta E) j := by
  rw [Feasible,slack,edge,ite_eq_right (show Candidate.word E≠0 by decide),delta,
    show next E=H from rfl,quarterFeasible,sub_nonneg]

theorem HardInput.aligned_E_radial {q : ℝ} (I : HardInput q) (hq : q≤qCap)
    (hHG : I.cycle.theta G=I.cycle.theta H)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hTD : I.cycle.theta T=I.cycle.theta D)
    (hleft : I.cycle.theta A≤I.cycle.theta H)
    (hright : I.cycle.theta D≤I.cycle.theta A) :
    7/12<(I.cycle.point E).a ∧
      max |(I.cycle.point H).y| |(I.cycle.point D).y|≤(I.cycle.point E).a := by
  have hb := I.aligned_bounds hq hHG hAB hTD hleft hright
  have hnot : ¬(I.cycle.point E).a≤7/12 := by
    intro hcore
    have hEhal := SignedPoint.primary_gt_half (I.necessary.sorted E) (I.necessary.core E)
    have hEminor : -(7/12 : ℝ)≤(I.cycle.point E).y := by
      have hh := (abs_le.mp (I.necessary.sorted E).2).1
      linarith
    have hDowner : I.witnesses.owner D=2 ∨ I.witnesses.owner D=3 := by
      simpa [normalOwners,D] using I.witnesses.allowed D
    have hEowner : I.witnesses.owner E=0 ∨ I.witnesses.owner E=1 := by
      simpa [normalOwners,E] using I.witnesses.allowed E
    have hDE : quarterFeasible (I.cycle.point D) (I.cycle.point E)
        (I.cycle.theta E-I.cycle.theta D) 2 ∨
        quarterFeasible (I.cycle.point D) (I.cycle.point E)
        (I.cycle.theta E-I.cycle.theta D) 3 := by
      have hf := (feasible_D_iff I.cycle _).mp (I.witnesses.feasible D)
      rcases hDowner with hj | hj
      · left
        rwa [hj] at hf
      · right
        rwa [hj] at hf
    have hEH : quarterFeasible (I.cycle.point E) (I.cycle.point H)
        (I.cycle.theta H-I.cycle.theta E) 0 ∨
        quarterFeasible (I.cycle.point E) (I.cycle.point H)
        (I.cycle.theta H-I.cycle.theta E) 1 := by
      have hf := (feasible_E_iff I.cycle _).mp (I.witnesses.feasible E)
      rcases hEowner with hj | hj
      · left
        rwa [hj] at hf
      · right
        rwa [hj] at hf
    have heq : I.cycle.theta E-I.cycle.theta D+
        (I.cycle.theta H-I.cycle.theta E)=I.cycle.theta H-I.cycle.theta D := by ring
    apply core_impossible hb.H_primary.1.le hb.D_primary.1.le
      ⟨I.anchors_normal.H_nonneg,by linarith [hb.H_tangent.2]⟩
      ⟨by linarith [I.anchors_normal.D_nonpos],by linarith [hb.D_tangent.2]⟩
      ⟨hEhal.le,hcore⟩ ⟨hEminor,I.E_nonpos⟩
      (I.necessary.spread E D) (I.necessary.spread H E)
      (by rw [heq]; exact ⟨hb.span_nonneg,hb.span_lt.le⟩)
      (by rw [heq]; exact hb.primary_sum) hDE hEH
  exact ⟨lt_of_not_ge hnot,I.E_radial.resolve_left hnot⟩

/-- The witnesses are inequalities of the cycle itself. A secondary owner may remain the
selected one; ties are kept. -/
theorem HardInput.aligned_primary_E_witnesses {q : ℝ} (I : HardInput q) (hq : q≤qCap)
    (hHG : I.cycle.theta G=I.cycle.theta H)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hTD : I.cycle.theta T=I.cycle.theta D)
    (hleft : I.cycle.theta A≤I.cycle.theta H)
    (hright : I.cycle.theta D≤I.cycle.theta A)
    (hDEorder : I.cycle.theta D≤I.cycle.theta E)
    (hEHorder : I.cycle.theta E≤I.cycle.theta H) :
    I.cycle.Feasible D 3 ∧ I.cycle.Feasible E 1 := by
  have hrad := (I.aligned_E_radial hq hHG hAB hTD hleft hright).2
  have hDrad : -(I.cycle.point D).y≤(I.cycle.point E).a := by
    have hh := (le_max_right |(I.cycle.point H).y| |(I.cycle.point D).y|).trans hrad
    rwa [abs_of_nonpos I.anchors_normal.D_nonpos] at hh
  have hHrad : (I.cycle.point H).y≤(I.cycle.point E).a := by
    have hh := (le_max_left |(I.cycle.point H).y| |(I.cycle.point D).y|).trans hrad
    rwa [abs_of_nonneg I.anchors_normal.H_nonneg] at hh
  have hu : I.cycle.theta E-I.cycle.theta D∈Icc 0 (7/10 : ℝ) :=
    ⟨sub_nonneg.mpr hDEorder,(le_abs_self _).trans (I.necessary.spread E D)⟩
  have hv : I.cycle.theta H-I.cycle.theta E∈Icc 0 (7/10 : ℝ) :=
    ⟨sub_nonneg.mpr hEHorder,(le_abs_self _).trans (I.necessary.spread H E)⟩
  constructor
  · have hj : I.witnesses.owner D=2 ∨ I.witnesses.owner D=3 := by
      simpa [normalOwners,D] using I.witnesses.allowed D
    rcases hj with hj | hj
    · have hf : quarterFeasible (I.cycle.point D) (I.cycle.point E)
          (I.cycle.theta E-I.cycle.theta D) 2 := by
        have hh := (feasible_D_iff I.cycle _).mp (I.witnesses.feasible D)
        rwa [hj] at hh
      have hh := DE_primary_of_nonneg (I.necessary.sorted D) (I.necessary.sorted E)
        I.anchors_normal.D_nonpos I.E_nonpos hDrad hu hf
      exact (feasible_D_iff I.cycle 3).mpr hh
    · simpa only [hj] using I.witnesses.feasible D
  · have hj : I.witnesses.owner E=0 ∨ I.witnesses.owner E=1 := by
      simpa [normalOwners,E] using I.witnesses.allowed E
    rcases hj with hj | hj
    · have hf : quarterFeasible (I.cycle.point E) (I.cycle.point H)
          (I.cycle.theta H-I.cycle.theta E) 0 := by
        have hh := (feasible_E_iff I.cycle _).mp (I.witnesses.feasible E)
        rwa [hj] at hh
      have hh := EH_primary_of_nonneg (I.necessary.sorted H).1.le I.E_nonpos hHrad hv hf
      exact (feasible_E_iff I.cycle 1).mpr hh
    · simpa only [hj] using I.witnesses.feasible E

end SignedCycle
end SquaresInCircles.Eight
end
end
end

section
@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace SquaresInCircles.Eight
namespace AlignedNegative
open PrimaryCap

private theorem high_exists_left_improvement {f : ℝ → ℝ} {l m d : ℝ}
    (hd : HasDerivAt f d m) (hneg : d<0) (hlm : l< m) :
    ∃ x, x∈Ioo l m ∧ f m<f x := by
  have hf : HasDerivAt f d (-(-m)) := by rw [neg_neg]; exact hd
  have hg : HasDerivAt (fun z => f (-z)) (d*(-1)) (-m) :=
    HasDerivAt.comp (-m) hf (hasDerivAt_neg' (x := -m))
  have hbetter := NegativeContact.eventually_right_gt hg (by linarith)
  have hbound : ∀ᶠ z in 𝓝[>] (-m), z< -l :=
    (eventually_lt_nhds (show -m< -l by linarith)).filter_mono nhdsWithin_le_nhds
  obtain ⟨z,hz,hbound,hbetter⟩ :=
    (eventually_mem_nhdsWithin.and (hbound.and hbetter)).exists
  have hz' : -m<z := hz
  refine ⟨-z,⟨by linarith,by linarith⟩,?_⟩
  simpa using hbetter

private theorem exists_left_positive {f : ℝ → ℝ} {l m : ℝ}
    (hc : ContinuousAt f m) (hp : 0<f m) (hlm : l< m) :
    ∃ x, x∈Ioo l m ∧ 0<f x := by
  have hpositive : ∀ᶠ x in 𝓝[<] m, 0<f x :=
    (hc.tendsto.eventually (eventually_gt_nhds hp)).filter_mono nhdsWithin_le_nhds
  have hbound : ∀ᶠ x in 𝓝[<] m, l<x :=
    (eventually_gt_nhds hlm).filter_mono nhdsWithin_le_nhds
  obtain ⟨x,hxm,hlx,hpx⟩ :=
    (eventually_mem_nhdsWithin.and (hbound.and hpositive)).exists
  exact ⟨x,⟨hlx,hxm⟩,hpx⟩

theorem Source.eh1_hard_point {q t e : ℝ} {H G A E : SignedPoint}
    (I : Source q t H G A) (hq : q≤qCap)
    (hEs : E.Sorted) (hEc : E.Contained q) (hEy : E.y≤0)
    (he : |e+t|≤11/50) (hf : quarterFeasible E H (e+t) 1) :
    ∃ x, x∈Ico 0 t ∧ e+x∈Icc 0 (11/50 : ℝ) ∧
      quarterFeasible (point (A.a-1/2) x) A (-x) 0 ∧
      0<highMixedSlack H.circle (A.a-1/2) e E x := by
  let P := A.a-1/2
  let L : ℝ → ℝ := highMixedSlack H.circle P e E
  let l : ℝ := max 0 (-e)
  let k : ℝ := 1/4000
  let F : ℝ → ℝ := fun x => L x-k*(t-x)
  have hewide : |e+t|≤7/10 := by linarith
  have hεpos := I.eh1_error_positive hq hEs hEy hewide hf
  have hlt : l<t := max_lt_iff.mpr ⟨I.tilt_pos,by linarith⟩
  have hl0 : 0≤l := le_max_left _ _
  have hlE : -e≤l := le_max_right _ _
  have hεcap : e+t≤11/50 := (abs_le.mp he).2
  have hL0 : 0≤L t := by
    have hN := (I.normalize hq).retains_mixed hq hewide (Or.inr rfl) hf
    rw [(I.normalize hq).H_eq] at hN
    dsimp [L,P]
    rw [highMixedSlack_actual E ⟨hεpos.le,by linarith⟩]
    exact sub_nonneg.mpr hN
  let clamp : ℝ → ℝ := fun x => max l (min t x)
  have hclamp (x : ℝ) : clamp x∈Icc l t := by
    exact ⟨le_max_left _ _,max_le hlt.le (min_le_left _ _)⟩
  have hclamp_eq {x : ℝ} (hx : x∈Icc l t) : clamp x=x := by
    simp [clamp,min_eq_right hx.2,max_eq_right hx.1]
  have hcclamp : Continuous clamp := by dsimp [clamp]; fun_prop
  have hcosclamp (x : ℝ) : Real.cos (clamp x)≠0 := by
    apply (transport_cos_pos (x := clamp x) ?_).ne'
    rw [abs_of_nonneg (hl0.trans (hclamp x).1)]
    exact (hclamp x).2.trans I.tilt_cap
  have hvalue : Continuous (fun x => value P (clamp x)) := by
    unfold value
    exact (continuous_const.sub (continuous_const.mul
      (Real.continuous_sin.comp hcclamp))).div
      (Real.continuous_cos.comp hcclamp) hcosclamp
  have hcF : Continuous (fun x => F (clamp x)) := by
    dsimp [F,L,highMixedSlack,movingAnchor,anchorAt]
    fun_prop
  let S : Set ℝ := Icc l t ∩ {x | 0≤F (clamp x)}
  have hcompact : IsCompact S :=
    isCompact_Icc.inter_right (isClosed_le continuous_const hcF)
  have htS : t∈S := by
    refine ⟨⟨hlt.le,le_rfl⟩,?_⟩
    show 0≤F (clamp t)
    rw [hclamp_eq ⟨hlt.le,le_rfl⟩]
    simpa [F] using hL0
  obtain ⟨m,hm,hmin⟩ := hcompact.exists_isMinOn ⟨t,htS⟩ continuous_id.continuousOn
  have hmint : m∈Icc l t := hm.1
  have hm0 : 0≤m := hl0.trans hmint.1
  have hFm : 0≤F m := by
    have h : 0≤F (clamp m) := hm.2
    rwa [hclamp_eq hmint] at h
  have hLm : 0≤L m := by
    have hh := mul_nonneg (show 0≤k by norm_num [k]) (sub_nonneg.mpr hmint.2)
    dsimp [F] at hFm
    linarith
  have hem : e+m∈Icc 0 (11/50 : ℝ) := by
    constructor <;> linarith [hmint.1,hmint.2]
  have hhard : quarterFeasible (point P m) A (-m) 0 := by
    by_contra hnot
    have hmpos : 0<m := by
      by_contra! hmnonpos
      have hmzero : m=0 := le_antisymm hmnonpos hm0
      have hprimary : quarterFeasible (point P 0) A 0 1 := by
        have h := (actual_primary_contact
          (show A.a=P+1/2 by dsimp [P]; ring)
          (show (0:ℝ)∈Icc 0 (7/10) by constructor <;> norm_num)).ge
        rw [neg_zero] at h
        exact h
      apply hnot
      rw [hmzero,neg_zero]
      exact (quarter_low_tie (point P 0) A).2 hprimary
    have hlm : l<m := by
      by_contra! hml
      have hmeq : m=l := le_antisymm hml hmint.1
      have hezero : e+m=0 := by
        rcases le_total 0 (-e) with he0 | he0
        · have hleq : l= -e := max_eq_right he0
          linarith
        · have hleq : l=0 := max_eq_left he0
          linarith
      let J := I.atAngle hq ⟨hmpos,hmint.2⟩ hnot
      have hHa := (J.cuts hq).2.2.2.2.1
      have hLzero : L m=(movingAnchor H.circle P m).a+E.y-1 := by
        simp [L,highMixedSlack,hezero]
      rw [hLzero] at hLm
      linarith
    have hgeom := I.path_geometry hq ⟨hm0,hmint.2⟩
    have hc : Real.cos m≠0 := (transport_cos_pos (by
      rw [abs_of_nonneg hm0]; exact hmint.2.trans I.tilt_cap)).ne'
    have hdL := highMixedSlack_hasDerivAt (qH := H.circle) (P := P) (e := e) E hc
      hgeom.2.2.2.2.2.2
    have hdF : HasDerivAt F (highMixedDerivative H.circle P e E m+k) m := by
      have h := hdL.fun_sub (((hasDerivAt_id' m).const_sub t).const_mul k)
      convert h using 1
      ring
    have hleft : ∃ x, x∈Ioo l m ∧ 0≤F x := by
      by_cases hFzero : F m=0
      · have hsmall : L m≤1/1000 := by
          dsimp [F,k] at hFzero
          linarith [I.tilt_cap]
        have hnegative : highMixedDerivative H.circle P e E m+k<0 := by
          have hh := I.highMixedDerivative_negative hq hEc hEy
            ⟨hmpos,hmint.2⟩ hnot hem hsmall
          dsimp [k,P]
          linarith
        obtain ⟨x,hx,hbetter⟩ := high_exists_left_improvement hdF hnegative hlm
        exact ⟨x,hx,hFm.trans hbetter.le⟩
      · have hpos : 0<F m := lt_of_le_of_ne hFm (Ne.symm hFzero)
        obtain ⟨x,hx,hposx⟩ := exists_left_positive hdF.continuousAt hpos hlm
        exact ⟨x,hx,hposx.le⟩
    obtain ⟨x,hx,hposx⟩ := hleft
    have hxt : x∈Icc l t := ⟨hx.1.le,hx.2.le.trans hmint.2⟩
    have hxS : x∈S := by
      refine ⟨hxt,?_⟩
      show 0≤F (clamp x)
      rw [hclamp_eq hxt]
      exact hposx
    have hbad : m≤x := hmin hxS
    linarith [hx.2]
  have hmt : m<t := by
    apply lt_of_le_of_ne hmint.2
    intro hmeq
    have hn := (I.normalize hq).source.no_hard
    rw [(I.normalize hq).G_eq] at hn
    exact hn (by simpa [P,hmeq] using hhard)
  have hstrict : 0<L m := by
    have hgrowth := mul_pos (show 0<k by norm_num [k]) (sub_pos.mpr hmt)
    dsimp [F] at hFm
    linarith
  exact ⟨m,⟨hm0,hmt⟩,hem,hhard,hstrict⟩

structure HighMixedEndpoint {q t : ℝ} {H G A : SignedPoint}
    (I : Source q t H G A) (E : SignedPoint) (e : ℝ) where
  angle : ℝ
  angle_mem : angle∈Ico 0 t
  Hpoint : SignedPoint
  Gpoint : SignedPoint
  H_sorted : Hpoint.Sorted
  G_sorted : Gpoint.Sorted
  H_core : Hpoint.AvoidsCore
  G_core : Gpoint.Core
  H_circle_loss : Hpoint.circle<H.circle
  G_inside : Gpoint.circle<q
  H_positive : 0<Hpoint.y
  G_negative : Gpoint.y<0
  H_nondiagonal : |Hpoint.y|<Hpoint.a
  G_nondiagonal : |Gpoint.y|<Gpoint.a
  G_primary : Gpoint.a=7/12
  H_tangent_decreases : Hpoint.y<H.y
  HG0 : zeroFeasible Hpoint Gpoint 0 0
  HG2 : zeroFeasible Hpoint Gpoint 0 2
  GA0 : quarterFeasible Gpoint A (-angle) 0
  EH1 : quarterFeasible E Hpoint (e+angle) 1
  EH_error : e+angle∈Icc 0 (11/50 : ℝ)

theorem Source.eh1_hard_endpoint {q t e : ℝ} {H G A E : SignedPoint}
    (I : Source q t H G A) (hq : q≤qCap)
    (hEs : E.Sorted) (hEc : E.Contained q) (hEy : E.y≤0)
    (he : |e+t|≤11/50) (hf : quarterFeasible E H (e+t) 1) :
    Nonempty (HighMixedEndpoint I E e) := by
  obtain ⟨x,hx,heX,hGA,hL⟩ := I.eh1_hard_point hq hEs hEc hEy he hf
  let P := A.a-1/2
  let H₀ := movingAnchor H.circle P x
  let G₀ := point P x
  obtain ⟨hHs,hHcircle,hHprimary,hHtangent,hHcore,hHy,hHrad⟩ :=
    I.path_geometry hq ⟨hx.1,hx.2.le⟩
  have hHtangentStrict := I.path_tangent_strict hq hx
  have hHsort : H₀.y<H₀.a := by
    have hh := I.H_sorted.2
    rw [abs_of_nonneg I.H_nonneg] at hh
    exact hHtangentStrict.trans_le (hh.trans hHprimary)
  have hHhigh : 211/250<H₀.a := by
    have hh := I.H_sorted.2
    rw [abs_of_nonneg I.H_nonneg] at hh
    exact (I.cuts hq).2.2.2.1.trans_le (hh.trans hHprimary)
  let margin := highMixedSlack H.circle P e E x
  have hmargin : 0<margin := hL
  let η := min ((H₀.a-H₀.y)/2) (min ((H₀.a-7/12)/2) (margin/2))
  have hη : 0<η := by
    apply lt_min
    · exact div_pos (sub_pos.mpr hHsort) (by norm_num)
    · apply lt_min
      · apply div_pos _ (by norm_num)
        linarith
      · exact div_pos hmargin (by norm_num)
  have hηsort : η≤(H₀.a-H₀.y)/2 := min_le_left _ _
  have hηcore : η≤(H₀.a-7/12)/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hηslack : η≤margin/2 := (min_le_right _ _).trans (min_le_right _ _)
  let H' : SignedPoint := ⟨H₀.a-η,H₀.y⟩
  have hHs' : H'.Sorted := by
    constructor
    · dsimp [H']; linarith
    · dsimp [H']; rw [abs_of_pos hHy]; linarith
  have hHcore' : H'.AvoidsCore := by
    have ha : 7/12≤H'.a := by dsimp [H']; linarith
    unfold SignedPoint.AvoidsCore SignedPoint.coreDistance
    rw [max_eq_left (by linarith : 0≤H'.a-1/2)]
    nlinarith [sq_nonneg (max (|H'.y|-1/2) 0)]
  have hHloss : H'.circle<H.circle := by
    have hp : 0<η*(2*(H₀.a+1/2)-η) := by
      apply mul_pos hη
      linarith
    have heq : H₀.circle=H.circle := hHcircle
    rw [← heq]
    dsimp [H',SignedPoint.circle]
    nlinarith
  obtain ⟨hPlo,hPup,hcap,hDle⟩ := I.cap_data hq
  have hD := I.path_cap hq ⟨hx.1,hx.2.le⟩
  obtain ⟨hGs,hGcore,hGavoid,hGinside⟩ := point_geometric
    ⟨hPlo,hPup⟩ ⟨hx.1,hx.2.le.trans I.tilt_cap⟩ (by linarith [hD.1])
    (I.cuts hq).2.2.2.2.2.2.2
  have hGnegative : G₀.y<0 := by dsimp [G₀,point,P]; linarith [hD.1]
  have hHnondiagonal : |H'.y|<H'.a := by
    dsimp [H']; rw [abs_of_pos hHy]; linarith
  have hGnondiagonal : |G₀.y|<G₀.a := by
    rw [abs_of_neg hGnegative]
    dsimp [G₀,point]
    linarith [hD.2.1]
  have hHG0 : zeroFeasible H' G₀ 0 0 := by
    simp only [zeroFeasible,zeroProjection,H',H₀,G₀,movingAnchor,anchorAt,point,edgeWidth_zero,
      Real.sin_zero,Real.cos_zero,Matrix.cons_val_zero]
    linarith
  have hEH : quarterFeasible E H' (e+x) 1 := by
    have hm : margin=quarterProjection E H₀ (e+x) 1-edgeWidth (e+x) :=
      highMixedSlack_actual E ⟨heX.1,by linarith [heX.2]⟩
    change edgeWidth (e+x)≤quarterProjection E H' (e+x) 1
    simp only [quarterProjection,Matrix.cons_val_one,Matrix.cons_val_zero,H'] at hm ⊢
    linarith
  exact ⟨{
    angle := x
    angle_mem := hx
    Hpoint := H'
    Gpoint := G₀
    H_sorted := hHs'
    G_sorted := hGs
    H_core := hHcore'
    G_core := hGcore
    H_circle_loss := hHloss
    G_inside := hGinside
    H_positive := hHy
    G_negative := hGnegative
    H_nondiagonal := hHnondiagonal
    G_nondiagonal := hGnondiagonal
    G_primary := rfl
    H_tangent_decreases := hHtangentStrict
    HG0 := hHG0
    HG2 := (zero_owner_tie _ _).1 hHG0
    GA0 := hGA
    EH1 := hEH
    EH_error := heX }⟩

end AlignedNegative
end SquaresInCircles.Eight
end
end
end
