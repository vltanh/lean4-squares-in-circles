module

public import SquaresInCircles.Eight.TableFree.GlobalOuterAnchorDomain

/-!
# Complete original zero--high-quarter core-anchor contradiction

Each retained projection receives its explicit positive coefficient.
The shared core point has positive combined force coordinates.  Their
sum bounds leave strict reserves in all four endpoint-sign cases using
the actual core coordinate bounds.  The five-edge cyclic return is
joined separately.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalOuterAnchor

open FramePair ZeroPrimary GlobalQuarterSign

def forceX (primary : Bool) (λ d : ℝ) : ℝ := if primary then 0 else λ*Real.sin d
def forceY (primary : Bool) (λ d : ℝ) : ℝ :=
  if primary then λ/Real.cos d else λ*Real.cos d
def angle (primary : Bool) (λ a d : ℝ) : ℝ :=
  if primary then primaryAngle λ a d else secondaryAngle λ d
def scale (primary : Bool) (λ d : ℝ) : ℝ := if primary then λ/Real.cos d else λ
def forceCap (bad : Bool) : ℝ := if bad then m*(25/19) else k*(10/7)

theorem mass_positive (bad : Bool) : 0<mass bad := by cases bad <;> norm_num [mass,k,m]

theorem scale_nonneg (p : Bool) {λ d : ℝ} (hλ : 0≤λ) (hd : |d|≤frameCap) :
    0≤scale p λ d := by
  have hc : 0≤Real.cos d := by linarith [(signed_trig hd).1]
  cases p
  · exact hλ
  · exact div_nonneg hλ hc

theorem left_charge (s c : State) (p : Bool) {λ d : ℝ}
    (hλ : 0≤λ) (hd : |d|≤frameCap)
    (hl : λ*transverse s≤s.signedLabel) (hm : width d≤leftProjection p s c d) :
    λ/2+angle p λ s.a d-forceX p λ d*(c.a-1/2)-forceY p λ d*(c.b-1/2)≤
      d+s.signedLabel := by
  have hc : Real.cos d≠0 := ne_of_gt (by linarith [(signed_trig hd).1])
  have hid : λ/2+angle p λ s.a d-forceX p λ d*(c.a-1/2)-forceY p λ d*(c.b-1/2)=
      d+λ*transverse s+scale p λ d*(width d-leftProjection p s c d) := by
    cases p <;> dsimp [angle,forceX,forceY,scale,leftProjection,width,
      primaryAngle,secondaryAngle] <;> field_simp [hc] <;> ring
  rw [hid]
  have hn := mul_nonpos_of_nonneg_of_nonpos (scale_nonneg p hλ hd) (sub_nonpos.mpr hm)
  linarith

theorem right_charge (c t : State) (p : Bool) {λ d : ℝ}
    (hλ : 0≤λ) (hd : |d|≤frameCap)
    (hl : -(λ*transverse t)≤ -t.signedLabel) (hm : width d≤rightProjection p c t d) :
    λ/2+angle p λ t.a d-forceY p λ d*(c.a-1/2)-forceX p λ d*(c.b-1/2)≤
      d-t.signedLabel := by
  have hc : Real.cos d≠0 := ne_of_gt (by linarith [(signed_trig hd).1])
  have hid : λ/2+angle p λ t.a d-forceY p λ d*(c.a-1/2)-forceX p λ d*(c.b-1/2)=
      d-λ*transverse t+scale p λ d*(width d-rightProjection p c t d) := by
    cases p <;> dsimp [angle,forceX,forceY,scale,rightProjection,width,
      primaryAngle,secondaryAngle] <;> field_simp [hc] <;> ring
  rw [hid]
  have hn := mul_nonpos_of_nonneg_of_nonpos (scale_nonneg p hλ hd) (sub_nonpos.mpr hm)
  linarith

theorem force_component_lower (p bad : Bool) {d : ℝ} (hd : |d|≤frameCap)
    (hp : bad=true → p=true) :
    -k*(13/20)≤forceX p (mass bad) d ∧
      k*(19/25)≤forceY p (mass bad) d := by
  have ht := signed_trig hd
  have hs : -(13/20:ℝ)≤Real.sin d := by linarith [neg_le_abs (Real.sin d)]
  have hsec := (secant_upper hd).2.1
  cases hb : bad
  · cases p <;> dsimp [forceX,forceY,mass,k] <;> constructor <;> nlinarith
  · have hpp : p=true := hp hb
    rw [hpp]
    dsimp [forceX,forceY,mass,k,m]
    constructor <;> nlinarith

theorem force_sum_upper (p bad : Bool) {d : ℝ} (hd : |d|≤frameCap)
    (hp : bad=true → p=true) :
    forceX p (mass bad) d+forceY p (mass bad) d<forceCap bad := by
  have hsec := (secant_upper hd).2.2
  have hsum := sine_cosine_sum_upper d
  cases hb : bad
  · cases p <;> dsimp [forceX,forceY,mass,forceCap,k] <;> nlinarith
  · have hpp : p=true := hp hb
    rw [hpp]
    dsimp [forceX,forceY,mass,forceCap,m]
    nlinarith

theorem angle_k_lower (p : Bool) {a d : ℝ} (ha : 447/800≤a) (hA : a≤283/200)
    (hd : |d|≤frameCap) : negativeCost (max 0 (-d))≤angle p k a d := by
  cases p
  · exact secondary_k_lower hd
  · exact primary_k_lower ha hA hd

theorem negative_part_mem {d : ℝ} (hd : |d|≤frameCap) : max 0 (-d)∈Icc 0 frameCap := by
  exact ⟨le_max_left _ _,max_le (by norm_num [frameCap]) ((neg_le_abs d).trans hd)⟩

/-- The explicit masses and angle bounds close all four endpoint-sign
cells over the whole actual path frame domain. -/
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

/-- The complete local two-edge theorem retains both original zero
owners and both high-quarter owners, with arbitrary endpoint signs. -/
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

end SquaresInCircles.Eight.TableFree.GlobalOuterAnchor
