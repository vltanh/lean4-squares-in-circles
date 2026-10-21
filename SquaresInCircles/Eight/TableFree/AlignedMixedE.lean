module

public import SquaresInCircles.Eight.TableFree.AlignedCycleBounds

/-!
# The actual mixed E owners after alignment of the other anchors

Uncompiled draft.  The core exclusion uses either original owner on each
mixed edge, with arbitrary signed individual errors.  It retains the
original E point and frame.  For nonnegative individual errors, sorting
and the surviving radial alternative then give the actual primary mixed
axis, without reconstructing an endpoint or changing any circle value.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
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
The negative-angle branch uses the actual lower primary bound as well. -/
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

/-- The selected physical axes give two unrotated demands.  The E
tangent cancels only after both original weak inequalities are retained. -/
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
      simp only [quarterFeasible,quarterProjection,Matrix.cons_val_two] at hDE
      nlinarith
    · have hh := core_primary_charge hEa
        (show -(7/12 : ℝ)≤ -E.y by linarith [hEy.2]) hu
      simp [quarterFeasible,quarterProjection] at hDE
      nlinarith
  have hH : 1-(1/2)*Real.sin v≤H.a+E.y := by
    rcases hEH with hEH | hEH
    · have hh := rotated_charge hHa hHy hv
      simp only [quarterFeasible,quarterProjection,Matrix.cons_val_zero] at hEH
      nlinarith
    · have hh := core_primary_charge hEa hEy.1 hv
      simp only [quarterFeasible,quarterProjection,Matrix.cons_val_one] at hEH
      nlinarith
  linarith

theorem sine_pair_bound {u v : ℝ} (hs : u+v∈Icc 0 (11/50 : ℝ)) :
    Real.sin u+Real.sin v≤2*Real.sin ((u+v)/2) := by
  have hw : (u+v)/2∈Icc 0 (7/10 : ℝ) := ⟨by linarith [hs.1],by linarith [hs.2]⟩
  have hsin := (transport_trig hw).2.2.1
  have hmul := mul_le_mul_of_nonneg_left (Real.cos_le_one ((u-v)/2)) hsin
  have hid : Real.sin u+Real.sin v=
      2*Real.sin ((u+v)/2)*Real.cos ((u-v)/2) := by
    have hu : u=(u+v)/2+(u-v)/2 := by ring
    have hv : v=(u+v)/2-(u-v)/2 := by ring
    conv_lhs => rw [hu,hv,Real.sin_add,Real.sin_sub]
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
    nlinarith [Real.one_sub_sq_div_two_le_cos (s/2)]
  have hprod := mul_nonneg hsin (show 0≤(359/250)*Real.cos (s/2)-1 by linarith)
  have hdouble := Real.sin_two_mul (s/2)
  have heq : 2*(s/2)=s := by ring
  rw [heq] at hdouble
  nlinarith

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
  simp only [quarterFeasible,quarterProjection,Matrix.cons_val_two] at hDE
  simp [quarterFeasible,quarterProjection]
  nlinarith

theorem EH_primary_of_nonneg {H E : SignedPoint} {v : ℝ}
    (hHa : 0≤H.a) (hEy : E.y≤0) (hrad : H.y≤E.a)
    (hv : v∈Icc 0 (7/10 : ℝ))
    (hEH : quarterFeasible E H v 0) : quarterFeasible E H v 1 := by
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hv
  have hfirst := mul_nonneg (show 0≤H.a-E.y by linarith) (sub_nonneg.mpr hc1)
  have hsecond := mul_nonneg (sub_nonneg.mpr hrad) hs0
  simp only [quarterFeasible,quarterProjection,Matrix.cons_val_zero] at hEH
  simp only [quarterFeasible,quarterProjection,Matrix.cons_val_one]
  nlinarith

end AlignedMixedE

namespace SignedCycle
open AlignedMixedE

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
      rcases hDowner with hj | hj
      · left
        simpa [Feasible,slack,edge,word,delta,next,D,E,quarterFeasible,sub_nonneg,hj]
          using I.witnesses.feasible D
      · right
        simpa [Feasible,slack,edge,word,delta,next,D,E,quarterFeasible,sub_nonneg,hj]
          using I.witnesses.feasible D
    have hEH : quarterFeasible (I.cycle.point E) (I.cycle.point H)
        (I.cycle.theta H-I.cycle.theta E) 0 ∨
        quarterFeasible (I.cycle.point E) (I.cycle.point H)
        (I.cycle.theta H-I.cycle.theta E) 1 := by
      rcases hEowner with hj | hj
      · left
        simpa [Feasible,slack,edge,word,delta,next,E,H,quarterFeasible,sub_nonneg,hj]
          using I.witnesses.feasible E
      · right
        simpa [Feasible,slack,edge,word,delta,next,E,H,quarterFeasible,sub_nonneg,hj]
          using I.witnesses.feasible E
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

/-- The witnesses are actual inequalities of the unchanged cycle.  An
original secondary owner can remain selected; ties are not discarded. -/
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
    simpa [abs_of_nonpos I.anchors_normal.D_nonpos] using hh
  have hHrad : (I.cycle.point H).y≤(I.cycle.point E).a := by
    have hh := (le_max_left |(I.cycle.point H).y| |(I.cycle.point D).y|).trans hrad
    simpa [abs_of_nonneg I.anchors_normal.H_nonneg] using hh
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
        simpa [Feasible,slack,edge,word,delta,next,D,E,quarterFeasible,sub_nonneg,hj]
          using I.witnesses.feasible D
      have hh := DE_primary_of_nonneg (I.necessary.sorted D) (I.necessary.sorted E)
        I.anchors_normal.D_nonpos I.E_nonpos hDrad hu hf
      simpa [Feasible,slack,edge,word,delta,next,D,E,quarterFeasible,sub_nonneg] using hh
    · simpa only [hj] using I.witnesses.feasible D
  · have hj : I.witnesses.owner E=0 ∨ I.witnesses.owner E=1 := by
      simpa [normalOwners,E] using I.witnesses.allowed E
    rcases hj with hj | hj
    · have hf : quarterFeasible (I.cycle.point E) (I.cycle.point H)
          (I.cycle.theta H-I.cycle.theta E) 0 := by
        simpa [Feasible,slack,edge,word,delta,next,E,H,quarterFeasible,sub_nonneg,hj]
          using I.witnesses.feasible E
      have hh := EH_primary_of_nonneg (I.necessary.sorted H).1.le I.E_nonpos hHrad hv hf
      simpa [Feasible,slack,edge,word,delta,next,E,H,quarterFeasible,sub_nonneg] using hh
    · simpa only [hj] using I.witnesses.feasible E

end SignedCycle
end SquaresInCircles.Eight.TableFree
