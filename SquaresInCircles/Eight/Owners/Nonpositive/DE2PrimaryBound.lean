module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TotallySplit
public import SquaresInCircles.Eight.Owners.E.ContactConcavity
public import SquaresInCircles.Eight.Owners.Endpoint.Principles
public import SquaresInCircles.Eight.Owners.Epsilon.Geometry
public import SquaresInCircles.Eight.Owners.Negative.LargeBEEndpoint
public import SquaresInCircles.Eight.Owners.Nonpositive.MixedE
public import SquaresInCircles.Eight.Owners.Nonpositive.OuterReduction
public import SquaresInCircles.Eight.Words.Aligned.NegativeEH1

/-!
# Eight squares: a rotated DE2 witness below D gives E primary above one

The two mixed inequalities and the bound on the primary sum of the nonpositive chain suffice
(`original_primary_gt_one`). Concavity on the whole triangular frame domain proves the scalar gap
(`gap_concave`, `gap_positive`), whose three endpoint reserves use Taylor bounds; E needs no circle
or radial boundary hypothesis. On a hard input with E below D and a DE2 witness, the primary of E
exceeds `1` (`HardInput.nonpositive_below_DE2_primary`).
-/

section
/-!
## The original rotated EH0 contact above H reaches E=H

The actual EH0 inequality supplies a short tangent interval.  On that
whole interval the original q-circle has a uniform projection-growth
reserve.  Moving to H's frame gives an actual E point with EH1 exact and
DE3 strictly improved.  This is an exclusion construction, so its initial
primary lift is not counted as a source-circle decrease.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.NonpositiveEH0Transport

def root (q b : ℝ) : ℝ := Real.sqrt (q-(b+1/2)^2)
def primary (q b : ℝ) : ℝ := root q b-1/2
def M (q α b : ℝ) : ℝ :=
  (primary q b-1/2)*Real.sin α+(b-1/2)*Real.cos α
def N (q α b : ℝ) : ℝ :=
  (primary q b-1/2)*Real.cos α-(b-1/2)*Real.sin α
def Md (q α b : ℝ) : ℝ :=
  Real.cos α-((b+1/2)/root q b)*Real.sin α

theorem root_bounds {q b : ℝ} (hqL : qLow≤q) (hb : b∈Icc 0 (1/10:ℝ)) :
    (9/5:ℝ)<root q b ∧ (root q b)^2=q-(b+1/2)^2 := by
  have hy0 : 0≤b+1/2 := by linarith [hb.1]
  have hy1 : b+1/2≤3/5 := by linarith [hb.2]
  have hy2 := pow_le_pow_left₀ hy0 hy1 2
  have hr : 0<q-(b+1/2)^2 := by norm_num [qLow] at hqL; nlinarith
  have he := Real.sq_sqrt hr.le
  have hn := Real.sqrt_nonneg (q-(b+1/2)^2)
  refine ⟨?_,he⟩
  dsimp [root]
  norm_num [qLow] at hqL
  nlinarith

theorem primary_bounds {q b : ℝ} (hqL : qLow≤q) (hqU : q≤qCap)
    (hb : b∈Icc 0 (1/10:ℝ)) :
    (13/10:ℝ)<primary q b ∧ primary q b<283/200 := by
  have hr := root_bounds hqL hb
  have hminor := pow_le_pow_left₀ (show (0:ℝ)≤1/2 by norm_num)
    (show 1/2≤b+1/2 by linarith [hb.1]) 2
  have hQ := hqU
  norm_num [qCap] at hQ
  dsimp [primary]
  constructor
  · linarith [hr.1]
  · nlinarith [hr.2]

theorem root_ratio {q b : ℝ} (hqL : qLow≤q) (hb : b∈Icc 0 (1/10:ℝ)) :
    0≤(b+1/2)/root q b ∧ (b+1/2)/root q b<1/3 := by
  have hr : 0<root q b := by linarith [(root_bounds hqL hb).1]
  constructor
  · exact div_nonneg (by linarith [hb.1]) hr.le
  · apply (div_lt_iff₀ hr).2
    linarith [(root_bounds hqL hb).1,hb.2]

theorem primary_hasDerivAt {q b : ℝ} (hqL : qLow≤q) (hb : b∈Icc 0 (1/10:ℝ)) :
    HasDerivAt (primary q) (-((b+1/2)/root q b)) b := by
  have hr := root_bounds hqL hb
  have hr0 : 0<root q b := by linarith [hr.1]
  have harg : q-(b+1/2)^2≠0 := by nlinarith [hr.2]
  have hd := ((hasDerivAt_const b q).sub
    (((hasDerivAt_id b).add_const (1/2)).pow 2)).sqrt harg
  convert hd.sub_const (1/2) using 1
  · rfl
  · dsimp [root]
    field_simp [hr0.ne']
    ring

theorem M_hasDerivAt {q α b : ℝ} (hqL : qLow≤q) (hb : b∈Icc 0 (1/10:ℝ)) :
    HasDerivAt (M q α) (Md q α b) b := by
  convert (((primary_hasDerivAt hqL hb).sub_const (1/2)).mul_const (Real.sin α)).add
    (((hasDerivAt_id b).sub_const (1/2)).mul_const (Real.cos α)) using 1
  · rfl
  · dsimp [Md]
    ring

theorem M_derivative_lower {q α b : ℝ} (hqL : qLow≤q)
    (hα : α∈Icc 0 (27/100:ℝ)) (hb : b∈Icc 0 (1/10:ℝ)) :
    (87/100:ℝ)<Md q α b := by
  have hr := root_ratio hqL hb
  have hs : 0≤Real.sin α :=
    Real.sin_nonneg_of_nonneg_of_le_pi hα.1 (by linarith [hα.2,Real.pi_gt_three])
  have hsu : Real.sin α≤27/100 := (Real.sin_le hα.1).trans hα.2
  have hsq := pow_le_pow_left₀ hα.1 hα.2 2
  have hcos := Real.one_sub_sq_div_two_le_cos (x := α)
  have hprod := mul_le_mul_of_nonneg_right hr.2.le hs
  dsimp [Md]
  norm_num at hsq
  nlinarith

theorem M_growth {q α b c : ℝ} (hqL : qLow≤q)
    (hα : α∈Icc 0 (27/100:ℝ)) (hb : b∈Icc 0 (1/10:ℝ))
    (hc : c∈Icc 0 (1/10:ℝ)) (hbc : b≤c) :
    (87/100)*(c-b)≤M q α c-M q α b := by
  exact derivative_reserve
    (fun z hz => (M_hasDerivAt hqL hz).continuousAt.continuousWithinAt)
    (fun z hz => M_hasDerivAt hqL (Ioo_subset_Icc_self hz))
    (fun z hz => (M_derivative_lower hqL hα (Ioo_subset_Icc_self hz)).le) hb hc hbc

def angularUpper (α : ℝ) : ℝ := (183/200)*Real.cos α+(1/2)*Real.sin α
def angularUpperD (α : ℝ) : ℝ := -(183/200)*Real.sin α+(1/2)*Real.cos α

theorem angularUpper_hasDerivAt (α : ℝ) :
    HasDerivAt angularUpper (angularUpperD α) α := by
  have h := ((Real.hasDerivAt_cos α).const_mul (183/200)).fun_add
    ((Real.hasDerivAt_sin α).const_mul (1/2))
  refine HasDerivAt.congr_deriv (show HasDerivAt angularUpper _ α from h) ?_
  simp only [angularUpperD]
  ring

theorem angularUpperD_positive {α : ℝ} (hα : α∈Icc 0 (27/100:ℝ)) :
    0<angularUpperD α := by
  have hs := (Real.sin_le hα.1).trans hα.2
  have hsq := pow_le_pow_left₀ hα.1 hα.2 2
  have hc := Real.one_sub_sq_div_two_le_cos (x := α)
  dsimp [angularUpperD]
  norm_num at hsq
  nlinarith

theorem angularUpper_bound {α : ℝ} (hα : α∈Icc 0 (27/100:ℝ)) :
    angularUpper α<127/125 := by
  have hh := derivative_reserve
    (f := angularUpper) (df := angularUpperD)
    (l := (0:ℝ)) (u := 27/100) (x := α) (y := 27/100) (k := 0)
    (fun z _ => (angularUpper_hasDerivAt z).continuousAt.continuousWithinAt)
    (fun z _ => angularUpper_hasDerivAt z)
    (fun z hz => (angularUpperD_positive (Ioo_subset_Icc_self hz)).le)
    hα (by norm_num) hα.2
  have hc := cos_upper_four (show (0:ℝ)≤27/100 by norm_num)
  have hs := sin_upper_five (show (0:ℝ)≤27/100 by norm_num)
  have hend : angularUpper (27/100)<127/125 := by
    dsimp [angularUpper]
    norm_num at hc hs
    linarith
  linarith

theorem M_lower {q α b : ℝ} (hqL : qLow≤q) (hqU : q≤qCap)
    (hα : α∈Icc 0 (27/100:ℝ)) (hb : b∈Icc 0 (1/10:ℝ)) :
    -(1/2:ℝ)≤M q α b := by
  have ha := (primary_bounds hqL hqU hb).1
  have hs : 0≤Real.sin α :=
    Real.sin_nonneg_of_nonneg_of_le_pi hα.1 (by linarith [hα.2,Real.pi_gt_three])
  have hc : 0≤Real.cos α := by
    have hsq := pow_le_pow_left₀ hα.1 hα.2 2
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := α)]
  have hfirst := mul_nonneg (show 0≤primary q b-1/2 by linarith) hs
  have hsecond := mul_le_mul_of_nonneg_right (show -(1/2:ℝ)≤b-1/2 by linarith [hb.1]) hc
  have hcos := Real.cos_le_one α
  dsimp [M]
  linarith

theorem N_upper {q α b : ℝ} (hqL : qLow≤q) (hqU : q≤qCap)
    (hα : α∈Icc 0 (27/100:ℝ)) (hb : b∈Icc 0 (1/10:ℝ)) :
    N q α b<127/125 := by
  have ha := (primary_bounds hqL hqU hb).2
  have hs : 0≤Real.sin α :=
    Real.sin_nonneg_of_nonneg_of_le_pi hα.1 (by linarith [hα.2,Real.pi_gt_three])
  have hc : 0≤Real.cos α := by
    have hsq := pow_le_pow_left₀ hα.1 hα.2 2
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := α)]
  have hfirst := mul_le_mul_of_nonneg_right (show primary q b-1/2≤183/200 by linarith) hc
  have hsecond := mul_nonneg hb.1 hs
  have hbound : N q α b≤angularUpper α := by
    dsimp [N,angularUpper]
    nlinarith
  exact hbound.trans_lt (angularUpper_bound hα)

theorem angular_identity (q α b x : ℝ) :
    M q (α+x) b=M q α b*Real.cos x+N q α b*Real.sin x := by
  simp only [M,N,Real.sin_add,Real.cos_add]
  ring

/-- The actual EH0 demand pays for the entire rotation, with an explicit
strict reserve on the original whole angle interval. -/
theorem strict_endpoint_gain {q α x b c AH BH : ℝ}
    (hqL : qLow≤q) (hqU : q≤qCap) (hα : α∈Icc 0 (27/100:ℝ))
    (hx : x∈Ioc 0 (7/10:ℝ)) (hb : b∈Icc 0 (1/10:ℝ))
    (hc : c∈Icc 0 (1/10:ℝ)) (hbc : b≤c)
    (hA : 1/2≤AH) (hB : 603/500≤BH)
    (hcontact : AH*(1-Real.cos x)+BH*Real.sin x≤c-b) :
    (1769/200000)*Real.sin x<M q α c-M q (α+x) b := by
  have hg := M_growth hqL hα hb hc hbc
  have hm := M_lower hqL hqU hα hb
  have hn := N_upper hqL hqU hα hb
  have hs : 0<Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith [hx.2,Real.pi_gt_three])
  have hc0 : 0≤1-Real.cos x := sub_nonneg.mpr (Real.cos_le_one x)
  have hcos := AlignedMixedE.cosine_loss ⟨hx.1.le,hx.2⟩
  have hA' := mul_le_mul_of_nonneg_right hA hc0
  have hB' := mul_le_mul_of_nonneg_right hB hs.le
  have hm' := mul_le_mul_of_nonneg_right hm hc0
  have hn' := mul_lt_mul_of_pos_right hn hs
  rw [angular_identity]
  nlinarith

theorem source_primary_le {q : ℝ} {E : SignedPoint}
    (hqL : qLow≤q) (hs : E.Sorted) (hy : E.y≤0) (hc : E.Contained q)
    (hb : -E.y∈Icc 0 (1/10:ℝ)) : E.a≤primary q (-E.y) := by
  have hr := root_bounds hqL hb
  have hh := hc
  rw [SignedPoint.Contained,SignedPoint.circle,abs_of_nonpos hy] at hh
  have hEa := hs.1
  dsimp [primary]
  nlinarith [hr.1,hr.2]

/-- A real endpoint of the original rotated EH0 pair.  DE3 is strict,
EH1 is exact, and the new point is on the same working q-circle. -/
theorem endpoint_state {q α x : ℝ} {H D E : SignedPoint}
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hHa : 1/2<H.a) (hHu : H.a<11/10) (hHy : 353/500<H.y)
    (hEs : E.Sorted) (hEy : E.y≤0) (hEc : E.Contained q)
    (hα : α∈Icc 0 (27/100:ℝ)) (hx : x∈Ioc 0 (7/10:ℝ))
    (hsum : α+x≤7/10)
    (hDE : quarterFeasible D E (α+x) 3)
    (hEH : quarterFeasible E H (-x) 0) :
    ∃P : EInteriorGeometry.State,
      EInteriorGeometry.Feasible H.a D.a α q P ∧ P.2.2=α ∧
      EInteriorGeometry.W P.2.2<EInteriorGeometry.deValue D.a P ∧
      EInteriorGeometry.W (α-P.2.2)=EInteriorGeometry.ehValue H.a α P := by
  let b : ℝ := -E.y
  let c : ℝ := H.a-1
  have hb0 : 0≤b := by dsimp [b]; linarith
  have hxsin : 0<Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith [hx.2,Real.pi_gt_three])
  have hcosloss : 0≤1-Real.cos x := sub_nonneg.mpr (Real.cos_le_one x)
  have hcontact : (H.a-1/2)*(1-Real.cos x)+(H.y+1/2)*Real.sin x≤c-b := by
    have hw := edgeWidth_negative_formula ⟨hx.1.le,hx.2⟩
    dsimp [quarterFeasible] at hEH
    rw [hw] at hEH
    simp only [quarterProjection,Matrix.cons_val_zero,Real.cos_neg,Real.sin_neg] at hEH
    dsimp [c,b]
    linarith
  have hpositive : 0<(H.a-1/2)*(1-Real.cos x)+(H.y+1/2)*Real.sin x :=
    add_pos_of_nonneg_of_pos (mul_nonneg (by linarith) hcosloss)
      (mul_pos (by linarith) hxsin)
  have hbc : b<c := by linarith
  have hc : c∈Icc 0 (1/10:ℝ) := by dsimp [c] at *; constructor <;> linarith
  have hb : b∈Icc 0 (1/10:ℝ) := ⟨hb0,hbc.le.trans hc.2⟩
  have hHlarge : 1<H.a := by dsimp [c] at hbc; linarith
  have hgain := strict_endpoint_gain hqL hqU hα hx hb hc hbc.le
    (show 1/2≤H.a-1/2 by linarith) (show 603/500≤H.y+1/2 by linarith) hcontact
  have hlift : E.a≤primary q b := source_primary_le hqL hEs hEy hEc hb
  have hsumdom : α+x∈Icc 0 (7/10:ℝ) := ⟨by linarith [hα.1,hx.1],hsum⟩
  have hsin := (transport_trig hsumdom).2.2.1
  have hlift' := mul_le_mul_of_nonneg_right hlift hsin
  have hsource : 0≤D.a-1/2+M q (α+x) b := by
    have h : edgeWidth (α+x)≤D.a+E.a*Real.sin (α+x)-E.y*Real.cos (α+x) := hDE
    rw [edgeWidth_positive_formula hsumdom] at h
    dsimp only [M,b]
    linarith
  have htarget : 0<D.a-1/2+M q α c := by
    have hg0 : 0<(1769/200000:ℝ)*Real.sin x := mul_pos (by norm_num) hxsin
    linarith
  let P : EInteriorGeometry.State := (primary q c,c,α)
  have hprim := primary_bounds hqL hqU hc
  have hcircle : EInteriorGeometry.corner P=q := by
    have hr := (root_bounds hqL hc).2
    dsimp [P,EInteriorGeometry.corner,primary]
    linear_combination hr
  have hDEstrict : EInteriorGeometry.W P.2.2<EInteriorGeometry.deValue D.a P := by
    dsimp [EInteriorGeometry.W,EInteriorGeometry.deValue,P,M] at *
    linarith
  have hEHexact : EInteriorGeometry.W (α-P.2.2)=EInteriorGeometry.ehValue H.a α P := by
    simp [P,EInteriorGeometry.W,EInteriorGeometry.ehValue,c]
  refine ⟨P,?_,rfl,hDEstrict,hEHexact⟩
  exact {
    b_nonneg := hc.1
    sorted := by change c≤primary q c; linarith [hc.2,hprim.1]
    angle := ⟨hα.1,le_rfl⟩
    circle := hcircle.le
    DE := hDEstrict.le
    EH := hEHexact.le }

end SquaresInCircles.Eight.NonpositiveEH0Transport
end
end
end

section
/-!
## Mixed owners outside the nonpositive H–D interval

Each nonnegative mixed error gives its primary axis whatever the sign of the other error
(`HardInput.nonpositive_DE_primary_of_nonneg`, `HardInput.nonpositive_EH_primary_of_nonneg`). The
barrier at `E = H` is proved from the small-side transports
(`HardInput.nonpositive_EH_impossible`), and the rotated EH0 construction above H, inserted into
the necessary cycle at the same `q`, reaches that excluded endpoint
(`HardInput.nonpositive_above_EH0_impossible`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SignedCycle
open Candidate AlignedMixedE

private theorem r60_feasible_quarter {C : SignedCycle} {i : Vertex} (hw : Candidate.word i≠0)
    (j : Fin 4) : C.Feasible i j ↔
      quarterFeasible (C.point i) (C.point (next i)) (C.theta (next i)-C.theta i) j := by
  simp only [Feasible,slack,edge,hw,↓reduceIte,quarterFeasible,delta,sub_nonneg]

private theorem r60_feasible_congr {C C' : SignedCycle} {i : Vertex}
    (h1 : C'.point i=C.point i) (h2 : C'.point (next i)=C.point (next i))
    (h3 : C'.theta i=C.theta i) (h4 : C'.theta (next i)=C.theta (next i)) (j : Fin 4) :
    C'.Feasible i j ↔ C.Feasible i j := by
  simp only [Feasible,slack,edge,delta,h1,h2,h3,h4]

theorem HardInput.nonpositive_DE_primary_of_nonneg {q : ℝ}
    (I : HardInput q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hHG : I.cycle.Feasible H 0) (hTD : I.cycle.Feasible T 2)
    (hDEorder : I.cycle.theta D≤I.cycle.theta E) : I.cycle.Feasible D 3 := by
  have hrad := (I.nonpositive_E_radial hq hAB hAG hGH hDT hTB hHG hTD).2
  have hDrad : -(I.cycle.point D).y≤(I.cycle.point E).a := by
    have hh := (le_max_right |(I.cycle.point H).y| |(I.cycle.point D).y|).trans hrad
    simpa [abs_of_nonpos I.anchors_normal.D_nonpos] using hh
  have hu : I.cycle.theta E-I.cycle.theta D∈Icc 0 (7/10:ℝ) :=
    ⟨sub_nonneg.mpr hDEorder,(le_abs_self _).trans (I.necessary.spread E D)⟩
  have hj : I.witnesses.owner D=2 ∨ I.witnesses.owner D=3 := by
    simpa [normalOwners,D] using I.witnesses.allowed D
  rcases hj with hj | hj
  · have hsource : quarterFeasible (I.cycle.point D) (I.cycle.point E)
        (I.cycle.theta E-I.cycle.theta D) 2 := by
      have h := (r60_feasible_quarter (C := I.cycle) (i := D) (by decide) _).1
        (I.witnesses.feasible D)
      rwa [show next D=E by decide,hj] at h
    have hh := DE_primary_of_nonneg (I.necessary.sorted D) (I.necessary.sorted E)
      I.anchors_normal.D_nonpos I.E_nonpos hDrad hu hsource
    exact (r60_feasible_quarter (C := I.cycle) (i := D) (by decide) 3).2
      (by rw [show next D=E by decide]; exact hh)
  · simpa [hj] using I.witnesses.feasible D

theorem HardInput.nonpositive_EH_primary_of_nonneg {q : ℝ}
    (I : HardInput q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hHG : I.cycle.Feasible H 0) (hTD : I.cycle.Feasible T 2)
    (hEHorder : I.cycle.theta E≤I.cycle.theta H) : I.cycle.Feasible E 1 := by
  have hrad := (I.nonpositive_E_radial hq hAB hAG hGH hDT hTB hHG hTD).2
  have hHrad : (I.cycle.point H).y≤(I.cycle.point E).a := by
    have hh := (le_max_left |(I.cycle.point H).y| |(I.cycle.point D).y|).trans hrad
    simpa [abs_of_nonneg I.anchors_normal.H_nonneg] using hh
  have hv : I.cycle.theta H-I.cycle.theta E∈Icc 0 (7/10:ℝ) :=
    ⟨sub_nonneg.mpr hEHorder,(le_abs_self _).trans (I.necessary.spread H E)⟩
  have hj : I.witnesses.owner E=0 ∨ I.witnesses.owner E=1 := by
    simpa [normalOwners,E] using I.witnesses.allowed E
  rcases hj with hj | hj
  · have hsource : quarterFeasible (I.cycle.point E) (I.cycle.point H)
        (I.cycle.theta H-I.cycle.theta E) 0 := by
      have h := (r60_feasible_quarter (C := I.cycle) (i := E) (by decide) _).1
        (I.witnesses.feasible E)
      rwa [show next E=H by decide,hj] at h
    have hh := EH_primary_of_nonneg (I.necessary.sorted H).1.le
      I.E_nonpos hHrad hv hsource
    exact (r60_feasible_quarter (C := I.cycle) (i := E) (by decide) 1).2
      (by rw [show next E=H by decide]; exact hh)
  · simpa [hj] using I.witnesses.feasible E

/-- A nonpositive hard cycle cannot have E at the frame of H; the small-side construction produces
the three outer alternatives. -/
theorem HardInput.nonpositive_EH_impossible {q : ℝ}
    (I : HardInput q) (hqL : qLow≤q) (hq : q≤qTrial)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hHG : I.cycle.Feasible H 0) (hTD : I.cycle.Feasible T 2)
    (hEHframe : I.cycle.theta E=I.cycle.theta H)
    (hDE : I.cycle.Feasible D 3) (hEH : I.cycle.Feasible E 1) : False := by
  have hcap : q≤qCap := hq.trans (by norm_num [qTrial,qCap])
  obtain ⟨J,hJAB,hJnorm,hJAG,hJGH,hJDT,hJTB,hJHG,hJTD,hcases,hnon,hstrict,
    hJAy,hJBy,hθ,hfixed⟩ :=
    I.reduce_nonpositive_small_sides hqL hcap hAB hnorm hAG hGH hDT hTB hHG hTD
  have hH := hfixed H (by simp)
  have hD := hfixed D (by simp)
  have hE := hfixed E (by simp)
  have hJframe : J.cycle.theta E=J.cycle.theta H := by rw [hE.2,hH.2]; exact hEHframe
  have hJDE : J.cycle.Feasible D 3 := by
    have hn : next D=E := by decide
    exact (r60_feasible_congr hD.1 (by rw [hn]; exact hE.1) hD.2 (by rw [hn]; exact hE.2) 3).2 hDE
  have hJEH : J.cycle.Feasible E 1 := by
    have hn : next E=H := by decide
    exact (r60_feasible_congr hE.1 (by rw [hn]; exact hH.1) hE.2 (by rw [hn]; exact hH.2) 1).2 hEH
  rcases hcases with ⟨hHGframe,hTDframe⟩ | ⟨hAy,hTDframe⟩ | ⟨hBy,hHGframe⟩
  · exact J.aligned_epsilon_zero_impossible hcap hHGframe hJAB hTDframe
      (hJAG.trans hJGH) (by rw [hJAB]; exact hJDT.trans hJTB) hJframe hJDE hJEH
  · exact J.nonpositive_large_A_EH_impossible hcap hJAG hJGH hJHG hAy.le hJframe hJEH
  · exact J.nonpositive_large_B_EH_impossible hq hJAB (hJAG.trans hJGH) hHGframe
      hJDT hJTB hJTD hBy.le hJframe hJDE hJEH

/-- A rotated EH0 witness with E strictly above H leads to the excluded endpoint `E = H` on the
same circle; the DE witness is first upgraded at the same point, and every point other than E
stays. -/
theorem HardInput.nonpositive_above_EH0_impossible {q : ℝ}
    (I : HardInput q) (hqL : qLow≤q) (hq : q≤qTrial)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hHG : I.cycle.Feasible H 0) (hTD : I.cycle.Feasible T 2)
    (hEHorder : I.cycle.theta H<I.cycle.theta E)
    (hEH0 : I.cycle.Feasible E 0) : False := by
  have hcap : q≤qCap := hq.trans (by norm_num [qTrial,qCap])
  have hb := I.nonpositive_composite_bounds hcap hAB hAG hGH hDT hTB hHG hTD
  have hDEorder : I.cycle.theta D≤I.cycle.theta E := by
    have hDH : I.cycle.theta D≤I.cycle.theta H := sub_nonneg.mp hb.span_nonneg
    exact hDH.trans hEHorder.le
  have hDE := I.nonpositive_DE_primary_of_nonneg hcap hAB hAG hGH hDT hTB hHG hTD hDEorder
  let α := I.cycle.theta H-I.cycle.theta D
  let x := I.cycle.theta E-I.cycle.theta H
  have hα : α∈Icc 0 (27/100:ℝ) := ⟨hb.span_nonneg,hb.span_lt.le⟩
  have hx : x∈Ioc 0 (7/10:ℝ) :=
    ⟨sub_pos.mpr hEHorder,(le_abs_self _).trans (I.necessary.spread E H)⟩
  have hsum : α+x≤7/10 := by
    have hh := (le_abs_self _).trans (I.necessary.spread E D)
    dsimp [α,x,frameCap] at *
    linarith
  have hDE' : quarterFeasible (I.cycle.point D) (I.cycle.point E) (α+x) 3 := by
    have heq : α+x=I.cycle.theta E-I.cycle.theta D := by dsimp [α,x]; ring
    simpa [Feasible,slack,edge,word,delta,next,D,E,quarterFeasible,sub_nonneg,heq] using hDE
  have hEH' : quarterFeasible (I.cycle.point E) (I.cycle.point H) (-x) 0 := by
    have heq : -x=I.cycle.theta H-I.cycle.theta E := by dsimp [x]; ring
    simpa [Feasible,slack,edge,word,delta,next,E,H,quarterFeasible,sub_nonneg,heq] using hEH0
  obtain ⟨P,hP,hPangle,hPDE,hPEH⟩ := NonpositiveEH0Transport.endpoint_state hqL hcap
    hb.H_primary.1 hb.H_primary.2 hb.H_tangent.1 (I.necessary.sorted E) I.E_nonpos
    (I.necessary.contained E) hα hx hsum hDE' hEH'
  let J := I.fromNonpositiveEInterior hcap hb hP
  have hfixed (i : Vertex) (hi : i≠E) :
      J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i :=
    eInteriorCycle_unchanged I.cycle P i hi
  have hH := hfixed H (by decide)
  have hG := hfixed G (by decide)
  have hA := hfixed A (by decide)
  have hB := hfixed B (by decide)
  have hT := hfixed T (by decide)
  have hD := hfixed D (by decide)
  have hJEHframe : J.cycle.theta E=J.cycle.theta H := by
    rw [hH.2]
    change I.cycle.theta D+P.2.2=I.cycle.theta H
    rw [hPangle]
    dsimp [α]
    ring
  have hJDE : J.cycle.Feasible D 3 := eInteriorCycle_DE (by linarith [hb.span_lt]) hP
  have hJEH : J.cycle.Feasible E 1 := eInteriorCycle_EH (by linarith [hb.span_lt]) hP
  apply J.nonpositive_EH_impossible hqL hq
  · rw [hA.2,hB.2]; exact hAB
  · rw [hA.1,hB.1]; exact hnorm
  · rw [hA.2,hG.2]; exact hAG
  · rw [hG.2,hH.2]; exact hGH
  · rw [hD.2,hT.2]; exact hDT
  · rw [hT.2,hB.2]; exact hTB
  · have hn : next H=G := by decide
    exact (r60_feasible_congr hH.1 (by rw [hn]; exact hG.1) hH.2 (by rw [hn]; exact hG.2) 0).2 hHG
  · have hn : next T=D := by decide
    exact (r60_feasible_congr hT.1 (by rw [hn]; exact hD.1) hT.2 (by rw [hn]; exact hD.2) 2).2 hTD
  · exact hJEHframe
  · exact hJDE
  · exact hJEH

end SquaresInCircles.Eight.SignedCycle
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.NonpositiveDE2PrimaryBound

def gap (α x : ℝ) : ℝ :=
  2/625+(359/500)*Real.sin α+(603/500)*Real.sin x-
    (1/2)*Real.sin (α+x)-(3/2)*(1-Real.cos (α+x))

def gapD (α x : ℝ) : ℝ :=
  (603/500)*Real.cos x-(1/2)*Real.cos (α+x)-(3/2)*Real.sin (α+x)

def gapDD (α x : ℝ) : ℝ :=
  -(603/500)*Real.sin x+(1/2)*Real.sin (α+x)-(3/2)*Real.cos (α+x)

theorem gap_derivative (α x : ℝ) : HasDerivAt (gap α) (gapD α x) x := by
  have hd : HasDerivAt (fun z : ℝ => α+z) 1 x := by
    simpa using (hasDerivAt_id x).const_add α
  have h := (((hasDerivAt_const x (2/625+(359/500)*Real.sin α)).fun_add
    ((Real.hasDerivAt_sin x).const_mul (603/500))).fun_sub
      (hd.sin.const_mul (1/2))).fun_sub ((hd.cos.const_sub 1).const_mul (3/2))
  refine HasDerivAt.congr_deriv (show HasDerivAt (gap α) _ x from h) ?_
  simp only [gapD]
  ring

theorem gap_second_derivative (α x : ℝ) : HasDerivAt (gapD α) (gapDD α x) x := by
  have hd : HasDerivAt (fun z : ℝ => α+z) 1 x := by
    simpa using (hasDerivAt_id x).const_add α
  have h := (((Real.hasDerivAt_cos x).const_mul (603/500)).fun_sub
    (hd.cos.const_mul (1/2))).fun_sub (hd.sin.const_mul (3/2))
  refine HasDerivAt.congr_deriv (show HasDerivAt (gapD α) _ x from h) ?_
  simp only [gapDD]
  ring

theorem gap_concave {α : ℝ} (hα : α∈Icc 0 (27/100:ℝ)) :
    ConcaveOn ℝ (Icc 0 (7/10-α)) (gap α) := by
  apply concave_of_deriv2 (f' := gapD α) (f'' := gapDD α)
  · intro x hx; exact gap_derivative α x
  · intro x hx; exact gap_second_derivative α x
  · intro x hx
    have hxdom : x∈Icc 0 (7/10:ℝ) := ⟨hx.1,by linarith [hx.2,hα.1]⟩
    have hpdom : α+x∈Icc 0 (7/10:ℝ) := ⟨by linarith [hα.1,hx.1],by linarith [hx.2]⟩
    have hsx := (transport_trig hxdom).2.2.1
    have hcp := (transport_trig hpdom).1
    have hsp := (Real.sin_le hpdom.1).trans hpdom.2
    dsimp [gapDD]
    linarith

theorem near_endpoint {α : ℝ} (hα : α∈Icc 0 (27/100:ℝ)) : 0<gap α 0 := by
  have hsq := pow_le_pow_left₀ hα.1 hα.2 2
  have hcube : α^3≤(27/100)^2*α := by
    calc α^3=α^2*α := by ring
      _≤(27/100)^2*α := mul_le_mul_of_nonneg_right hsq hα.1
  have hsin : (49/50)*α≤Real.sin α := by
    linarith [Real.sin_ge_sub_cube hα.1,hα.1]
  have hquad := mul_nonneg hα.1 (show 0≤27/100-α by linarith [hα.2])
  have hcos := Real.one_sub_sq_div_two_le_cos (x := α)
  simp only [gap,Real.sin_zero,mul_zero,add_zero]
  nlinarith

def far (α : ℝ) : ℝ :=
  2/625+(359/500)*Real.sin α+(603/500)*Real.sin (7/10-α)-
    (1/2)*Real.sin (7/10)-(3/2)*(1-Real.cos (7/10))

def farD (α : ℝ) : ℝ :=
  (359/500)*Real.cos α-(603/500)*Real.cos (7/10-α)

def farDD (α : ℝ) : ℝ :=
  -(359/500)*Real.sin α-(603/500)*Real.sin (7/10-α)

theorem far_derivative (α : ℝ) : HasDerivAt far (farD α) α := by
  have hd : HasDerivAt (fun z : ℝ => 7/10-z) (-1) α := by
    simpa using (hasDerivAt_id α).const_sub (7/10)
  have h := (((((Real.hasDerivAt_sin α).const_mul (359/500)).const_add (2/625)).fun_add
    (hd.sin.const_mul (603/500))).sub_const ((1/2)*Real.sin (7/10))).sub_const
      ((3/2)*(1-Real.cos (7/10)))
  refine HasDerivAt.congr_deriv (show HasDerivAt (far) _ α from h) ?_
  simp only [farD]
  ring

theorem far_second_derivative (α : ℝ) : HasDerivAt farD (farDD α) α := by
  have hd : HasDerivAt (fun z : ℝ => 7/10-z) (-1) α := by
    simpa using (hasDerivAt_id α).const_sub (7/10)
  have h := ((Real.hasDerivAt_cos α).const_mul (359/500)).fun_sub
    (hd.cos.const_mul (603/500))
  refine HasDerivAt.congr_deriv (show HasDerivAt (farD) _ α from h) ?_
  simp only [farDD]
  ring

theorem far_concave : ConcaveOn ℝ (Icc (0:ℝ) (27/100)) far := by
  apply concave_of_deriv2 (f' := farD) (f'' := farDD)
  · intro α hα; exact far_derivative α
  · intro α hα; exact far_second_derivative α
  · intro α hα
    have hαdom : α∈Icc 0 (7/10:ℝ) := ⟨hα.1,by linarith [hα.2]⟩
    have hβdom : 7/10-α∈Icc 0 (7/10:ℝ) := ⟨by linarith [hα.2],by linarith [hα.1]⟩
    dsimp [farDD]
    linarith [(transport_trig hαdom).2.2.1,(transport_trig hβdom).2.2.1]

theorem far_zero : 0<far 0 := by
  have hs := Real.sin_ge_sub_cube (show (0:ℝ)≤7/10 by norm_num)
  have hc := Real.one_sub_sq_div_two_le_cos (x := (7/10:ℝ))
  simp only [far,Real.sin_zero,mul_zero,add_zero,sub_zero]
  norm_num at hs hc ⊢
  linarith

theorem far_last : 0<far (27/100) := by
  have hsα := Real.sin_ge_sub_cube (show (0:ℝ)≤27/100 by norm_num)
  have hsβ := Real.sin_ge_sub_cube (show (0:ℝ)≤43/100 by norm_num)
  have hsp := sin_upper_five (show (0:ℝ)≤7/10 by norm_num)
  have hcp := Real.one_sub_sq_div_two_le_cos (x := (7/10:ℝ))
  simp only [far]
  norm_num at hsα hsβ hsp hcp ⊢
  linarith

theorem far_positive {α : ℝ} (hα : α∈Icc 0 (27/100:ℝ)) : 0<far α := by
  have hm := far_concave.min_le_of_mem_Icc
    (show (0:ℝ)∈Icc 0 (27/100) by norm_num)
    (show (27/100:ℝ)∈Icc 0 (27/100) by norm_num) hα
  exact (lt_min far_zero far_last).trans_le hm

theorem gap_positive {α x : ℝ} (hα : α∈Icc 0 (27/100:ℝ))
    (hx : 0≤x) (hsum : α+x≤7/10) : 0<gap α x := by
  have hright : 0<gap α (7/10-α) := by
    simpa [gap,far,show α+(7/10-α)=7/10 by ring] using far_positive hα
  have hu : 0≤7/10-α := by linarith [hα.2]
  have hm := (gap_concave hα).min_le_of_mem_Icc
    (show (0:ℝ)∈Icc 0 (7/10-α) from ⟨le_rfl,hu⟩)
    (show 7/10-α∈Icc 0 (7/10-α) from ⟨hu,le_rfl⟩)
    (show x∈Icc 0 (7/10-α) from ⟨hx,by linarith⟩)
  exact (lt_min (near_endpoint hα) hright).trans_le hm

/-- The weak DE2 and EH1 witnesses with the bound on the primary sum give `1 < E.a`; the radius of
E is unrestricted. -/
theorem original_primary_gt_one {H D E : SignedPoint} {α x : ℝ}
    (hEs : E.Sorted) (hEy : E.y≤0) (hDa : 1/2≤D.a) (hDy : 353/500< -D.y)
    (hα : α∈Icc 0 (27/100:ℝ)) (hx : 0≤x) (hsum : α+x≤7/10)
    (hprimary : H.a+D.a<1248/625-(359/500)*Real.sin α)
    (hDE : quarterFeasible D E (-x) 2) (hEH : quarterFeasible E H (α+x) 1) :
    1<E.a := by
  by_contra! hbad
  have hb : 0≤ -E.y := neg_nonneg.mpr hEy
  have hbu : -E.y≤1 := by
    have hs : -E.y≤E.a := by simpa [abs_of_nonpos hEy] using hEs.2
    exact hs.trans hbad
  have hxdom : x∈Icc 0 (7/10:ℝ) := ⟨hx,by linarith [hα.1]⟩
  have hpdom : α+x∈Icc 0 (7/10:ℝ) := ⟨by linarith [hα.1],hsum⟩
  have hsx := (transport_trig hxdom).2.2.1
  have hsp := (transport_trig hpdom).2.2.1
  have hLx : 0≤1-Real.cos x := sub_nonneg.mpr (Real.cos_le_one x)
  have hLp : 0≤1-Real.cos (α+x) := sub_nonneg.mpr (Real.cos_le_one (α+x))
  have hdeDa := mul_nonneg (sub_nonneg.mpr hDa) hLx
  have hdeDy := mul_nonneg (show 0≤ -D.y+1/2-603/500 by linarith) hsx
  have hEHmajor := mul_le_mul_of_nonneg_right (show E.a-1/2≤1/2 by linarith) hsp
  have hEHminor := mul_le_mul_of_nonneg_right (show -E.y+1/2≤3/2 by linarith) hLp
  have hDEbound : 1+(603/500)*Real.sin x≤D.a-E.y := by
    have h : edgeWidth (-x)≤D.a*Real.cos (-x)-D.y*Real.sin (-x)-E.y := hDE
    rw [edgeWidth_negative_formula hxdom,Real.cos_neg,Real.sin_neg] at h
    linarith
  have hEHbound : 1-(1/2)*Real.sin (α+x)-(3/2)*(1-Real.cos (α+x))≤H.a+E.y := by
    have h : edgeWidth (α+x)≤H.a+E.a*Real.sin (α+x)+E.y*Real.cos (α+x) := hEH
    rw [edgeWidth_positive_formula hpdom] at h
    linarith
  have hgap := gap_positive hα hx hsum
  dsimp [gap] at hgap
  linarith

end SquaresInCircles.Eight.NonpositiveDE2PrimaryBound

namespace SquaresInCircles.Eight.SignedCycle
open Candidate

theorem HardInput.nonpositive_below_DE2_primary {q : ℝ}
    (I : HardInput q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hHG : I.cycle.Feasible H 0) (hTD : I.cycle.Feasible T 2)
    (hED : I.cycle.theta E<I.cycle.theta D) (hDE2 : I.cycle.Feasible D 2) :
    1<(I.cycle.point E).a := by
  have hb := I.nonpositive_composite_bounds hq hAB hAG hGH hDT hTB hHG hTD
  have hEHorder : I.cycle.theta E≤I.cycle.theta H :=
    hED.le.trans (sub_nonneg.mp hb.span_nonneg)
  have hEH1 := I.nonpositive_EH_primary_of_nonneg hq hAB hAG hGH hDT hTB hHG hTD hEHorder
  let α := I.cycle.theta H-I.cycle.theta D
  let x := I.cycle.theta D-I.cycle.theta E
  have hα : α∈Icc 0 (27/100:ℝ) := ⟨hb.span_nonneg,hb.span_lt.le⟩
  have hx : 0≤x := (sub_pos.mpr hED).le
  have hsum : α+x≤7/10 := by
    have hh := (le_abs_self _).trans (I.necessary.spread H E)
    dsimp [α,x,frameCap] at *
    linarith
  have hDE : quarterFeasible (I.cycle.point D) (I.cycle.point E) (-x) 2 := by
    have heq : -x=I.cycle.theta E-I.cycle.theta D := by dsimp [x]; ring
    simpa [Feasible,slack,edge,word,delta,next,D,E,quarterFeasible,sub_nonneg,heq] using hDE2
  have hEH : quarterFeasible (I.cycle.point E) (I.cycle.point H) (α+x) 1 := by
    have heq : α+x=I.cycle.theta H-I.cycle.theta E := by dsimp [α,x]; ring
    simpa [Feasible,slack,edge,word,delta,next,E,H,quarterFeasible,sub_nonneg,heq] using hEH1
  exact NonpositiveDE2PrimaryBound.original_primary_gt_one
    (I.necessary.sorted E) I.E_nonpos hb.D_primary.1.le hb.D_tangent.1
    hα hx hsum hb.primary_sum hDE hEH

end SquaresInCircles.Eight.SignedCycle
end
end
end
