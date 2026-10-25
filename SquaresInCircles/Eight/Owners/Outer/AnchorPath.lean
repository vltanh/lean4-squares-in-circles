module

public import SquaresInCircles.Eight.Owners.Outer.AnchorDomain
public import SquaresInCircles.Eight.Owners.Quarter.SignScalar

/-!
# Eight squares: no core anchor between a zero edge and a high quarter

Each projection receives its positive coefficient `mass`, and the shared core point has positive
combined force coordinates (`force_component_lower`, `force_sum_upper`). With the bounds on the
core coordinates their sum leaves a strict reserve in all four cases of endpoint signs
(`path_scalar_reserve`), so the two-edge charge exceeds `2` (`core_path_charge`). The return along
the other five edges is a separate statement.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalOuterAnchor

open FramePair ZeroPrimary GlobalQuarterSign

def forceX (primary : Bool) (lam d : ℝ) : ℝ := if primary then 0 else lam*Real.sin d
def forceY (primary : Bool) (lam d : ℝ) : ℝ :=
  if primary then lam/Real.cos d else lam*Real.cos d
def angle (primary : Bool) (lam a d : ℝ) : ℝ :=
  if primary then primaryAngle lam a d else secondaryAngle lam d
def scale (primary : Bool) (lam d : ℝ) : ℝ := if primary then lam/Real.cos d else lam
def forceCap (bad : Bool) : ℝ := if bad then m*(25/19) else k*(10/7)

theorem mass_positive (bad : Bool) : 0< mass bad := by cases bad <;> norm_num [mass,k,m]

theorem scale_nonneg (p : Bool) {lam d : ℝ} (hlam : 0≤lam) (hd : |d|≤frameCap) :
    0≤ scale p lam d := by
  have hc : 0≤Real.cos d := by linarith [(signed_trig hd).1]
  cases p
  · exact hlam
  · exact div_nonneg hlam hc

theorem left_charge (s c : State) (p : Bool) {lam d : ℝ}
    (hlam : 0≤lam) (hd : |d|≤frameCap)
    (hl : lam*transverse s≤ s.signedLabel) (hm : width d≤leftProjection p s c d) :
    lam/2+angle p lam s.a d-forceX p lam d*(c.a-1/2)-forceY p lam d*(c.b-1/2)≤
      d+s.signedLabel := by
  have hc : Real.cos d≠0 := ne_of_gt (by linarith [(signed_trig hd).1])
  have hid : lam/2+angle p lam s.a d-forceX p lam d*(c.a-1/2)-forceY p lam d*(c.b-1/2)=
      d+lam*transverse s+scale p lam d*(width d-leftProjection p s c d) := by
    cases p <;> dsimp [angle,forceX,forceY,scale,leftProjection,width,
      primaryAngle,secondaryAngle] <;> field_simp [hc] <;> ring
  rw [hid]
  have hn := mul_nonpos_of_nonneg_of_nonpos (scale_nonneg p hlam hd) (sub_nonpos.mpr hm)
  linarith

theorem right_charge (c t : State) (p : Bool) {lam d : ℝ}
    (hlam : 0≤lam) (hd : |d|≤frameCap)
    (hl : -(lam*transverse t)≤ -t.signedLabel) (hm : width d≤rightProjection p c t d) :
    lam/2+angle p lam t.a d-forceY p lam d*(c.a-1/2)-forceX p lam d*(c.b-1/2)≤
      d-t.signedLabel := by
  have hc : Real.cos d≠0 := ne_of_gt (by linarith [(signed_trig hd).1])
  have hid : lam/2+angle p lam t.a d-forceY p lam d*(c.a-1/2)-forceX p lam d*(c.b-1/2)=
      d-lam*transverse t+scale p lam d*(width d-rightProjection p c t d) := by
    cases p <;> dsimp [angle,forceX,forceY,scale,rightProjection,width,
      primaryAngle,secondaryAngle] <;> field_simp [hc] <;> ring
  rw [hid]
  have hn := mul_nonpos_of_nonneg_of_nonpos (scale_nonneg p hlam hd) (sub_nonpos.mpr hm)
  linarith

theorem force_component_lower (p bad : Bool) {d : ℝ} (hd : |d|≤frameCap)
    (hp : bad=true → p=true) :
    -k*(13/20)≤forceX p (mass bad) d ∧
      k*(19/25)≤forceY p (mass bad) d := by
  have ht := signed_trig hd
  have hs : -(13/20:ℝ)≤Real.sin d := by linarith [neg_le_abs (Real.sin d)]
  have hsec := (secant_upper hd).2.1
  have hdiv (lam : ℝ) : lam/Real.cos d=lam*(1/Real.cos d) := by ring
  cases hb : bad
  · cases p <;> dsimp [forceX,forceY,mass,k] <;> (try rw [hdiv]) <;>
      constructor <;> nlinarith
  · have hpp : p=true := hp hb
    rw [hpp]
    dsimp [forceX,forceY,mass,k,m]
    rw [hdiv]
    constructor <;> nlinarith

theorem force_sum_upper (p bad : Bool) {d : ℝ} (hd : |d|≤frameCap)
    (hp : bad=true → p=true) :
    forceX p (mass bad) d+forceY p (mass bad) d<forceCap bad := by
  have hsec := (secant_upper hd).2.2
  have hsum := sine_cosine_sum_upper d
  have hdiv (lam : ℝ) : lam/Real.cos d=lam*(1/Real.cos d) := by ring
  cases hb : bad
  · cases p <;> dsimp [forceX,forceY,mass,forceCap,k] <;> (try rw [hdiv]) <;> nlinarith
  · have hpp : p=true := hp hb
    rw [hpp]
    dsimp [forceX,forceY,mass,forceCap,m]
    rw [hdiv]
    nlinarith

theorem angle_k_lower (p : Bool) {a d : ℝ} (ha : 447/800≤a) (hA : a≤283/200)
    (hd : |d|≤frameCap) : negativeCost (max 0 (-d))≤angle p k a d := by
  cases p
  · exact secondary_k_lower hd
  · exact primary_k_lower ha hA hd

theorem negative_part_mem {d : ℝ} (hd : |d|≤frameCap) : max 0 (-d)∈Icc 0 frameCap := by
  exact ⟨le_max_left _ _,max_le (by norm_num [frameCap]) ((neg_le_abs d).trans hd)⟩

/-- The masses and the angle bounds leave a strict reserve in all four cells of endpoint signs, over
the whole frame domain of the path. -/
theorem path_scalar_reserve (p q badL badR : Bool) {a A v d : ℝ}
    (ha : 447/800≤a) (hA : a≤283/200) (ha' : 447/800≤A) (hA' : A≤283/200)
    (hv : |v|≤frameCap) (hd : |d|≤frameCap) (hsum : |v+d|≤frameCap)
    (hp : badL=true → p=true ∧ 0<v) (hq : badR=true → q=true ∧ 0<d) :
    2<Real.pi/2+(mass badL+mass badR)/2+
      angle p (mass badL) a v+angle q (mass badR) A d-
        (forceCap badL+forceCap badR)/12 := by
  have hnv := negative_part_mem hv
  have hnd := negative_part_mem hd
  cases hbL : badL <;> cases hbR : badR
  · have hl := angle_k_lower p ha hA hv
    have hr := angle_k_lower q ha' hA' hd
    have hc := negative_cost_sum hnv.1 hnd.1 (negative_parts_sum hv hd hsum)
    dsimp [mass,forceCap,k,m] at *
    linarith [half_pi_lower]
  · have hright := hq hbR
    have hr := primary_m_positive_lower hA'
      ⟨hright.2.le,(le_abs_self d).trans hd⟩
    have hl := angle_k_lower p ha hA hv
    have hc := negative_cost_lower hnv
    rw [hright.1]
    dsimp [mass,forceCap,angle,k,m] at *
    linarith [half_pi_lower]
  · have hleft := hp hbL
    have hl := primary_m_positive_lower hA
      ⟨hleft.2.le,(le_abs_self v).trans hv⟩
    have hr := angle_k_lower q ha' hA' hd
    have hc := negative_cost_lower hnd
    rw [hleft.1]
    dsimp [mass,forceCap,angle,k,m] at *
    linarith [half_pi_lower]
  · have hleft := hp hbL
    have hright := hq hbR
    have hl := primary_m_positive_lower hA
      ⟨hleft.2.le,(le_abs_self v).trans hv⟩
    have hr := primary_m_positive_lower hA'
      ⟨hright.2.le,(le_abs_self d).trans hd⟩
    rw [hleft.1,hright.1]
    dsimp [mass,forceCap,angle,k,m] at *
    linarith [half_pi_lower]

/-- Around a core vertex with nonpositive transverse coordinate, the two-edge charge exceeds `2`,
for both zero owners and both high-quarter owners and any endpoint signs. -/
theorem core_path_charge (s c t : State) (p q : Bool) {v d : ℝ}
    (hcore : c.branch.type=0) (hc : transverse c≤0)
    (hv : |v|≤frameCap) (hd : |d|≤frameCap) (hsum : |v+d|≤frameCap)
    (hl : s.Feasible c (leftOwner p) v)
    (hr : c.Feasible t (rightOwner q) (Real.pi/2+d)) :
    2<Real.pi/2+v+d+s.signedLabel-t.signedLabel := by
  have hlm := (left_margin s c p hv hc).1 hl
  have hrm := (right_margin c t q hd hc).1 hr
  obtain ⟨badL,hlabelL,hbadL⟩ := left_mass_exists s c p hcore hv hlm
  obtain ⟨badR,hlabelR,hbadR⟩ := right_mass_exists c t q hcore hd hrm
  have hleft := left_charge s c p (mass_positive badL).le hv hlabelL hlm
  have hright := right_charge c t q (mass_positive badR).le hd hlabelR hrm
  have hfl := force_component_lower p badL hv (fun hh => (hbadL hh).1)
  have hfr := force_component_lower q badR hd (fun hh => (hbadR hh).1)
  have hU : 0≤forceX p (mass badL) v+forceY q (mass badR) d := by
    dsimp [k] at hfl hfr
    linarith
  have hV : 0≤forceY p (mass badL) v+forceX q (mass badR) d := by
    dsimp [k] at hfl hfr
    linarith
  have hcb := core_bounds c hcore
  have hcoreA := mul_le_mul_of_nonneg_left (show c.a-1/2≤(1/12:ℝ) by linarith) hU
  have hcoreB := mul_le_mul_of_nonneg_left (show c.b-1/2≤(1/12:ℝ) by linarith) hV
  have hcapL := force_sum_upper p badL hv (fun hh => (hbadL hh).1)
  have hcapR := force_sum_upper q badR hd (fun hh => (hbadR hh).1)
  have hscalar := path_scalar_reserve p q badL badR
    (primary_lower s).le (coordinates s).2.1.le
    (primary_lower t).le (coordinates t).2.1.le hv hd hsum hbadL hbadR
  nlinarith only [hleft,hright,hcoreA,hcoreB,hcapL,hcapR,hscalar]

end SquaresInCircles.Eight.GlobalOuterAnchor
