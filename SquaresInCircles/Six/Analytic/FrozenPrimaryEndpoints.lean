module
public import SquaresInCircles.Six.Analytic.FrozenTrigStress
public import SquaresInCircles.Six.Analytic.OutwardAxes
public import SquaresInCircles.Six.Stress.Support
public import SquaresInCircles.Seven.Analysis

@[expose] public section

/-!
# Four original corners of the OWN-W inward-primary stress

The multiplier triple is (19/50,43/100,19/100) on C-D,C-W,W-D.
At fixed centers the stress is concave in v=-w and d. Only the original
rectangle corners (0 or 2/3, 0 or pi/4) are needed. The axial corner uses the
primary radius bound, not an invalid vertex/cap substitution. At the other
three corners the universally valid signed vertex bound suffices.

The root upper bounds are the displayed fractions 26/100,281/1000,405/1000.
They follow by squaring and fixed-angle Taylor bounds. There is no interval
partition, support-wall differentiation, or generated checker in this proof.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization Stress

def inwardPrimaryFrozen (v d aw ad bd cx cy : ℝ) : ℝ :=
  frozenTrig (1/2-(31/50)*aw-(19/50)*ad)
    ((43/100)*(1/2-cx)) ((43/100)*(1/2+cy))
    ((19/50)*(1/2-cx)) ((19/50)*(1/2-cy))
    ((19/100)*(1/2+ad)) ((19/100)*(1/2-bd)) v d

lemma vertex_linear_upper {a b U V L : ℝ} (hc : ContainedChart a |b|)
    (hV : 0≤V) (hL : 0≤L) (hNorm : U^2+V^2≤L^2) :
    U*a-V*b≤(1689/1000)*L-(U+V)/2 := by
  have hcircle : normSq (a+1/2,|b|+1/2)≤R0^2 := by
    simpa only [normSq,R0_sq] using hc.containment
  have hdot := dot_le_radius (v := (U,V)) R0_nonneg hcircle
  have hn : 0≤vectorLength (U,V) := vectorLength_nonneg _
  have hs : (vectorLength (U,V))^2=U^2+V^2 := vectorLength_sq _
  have hlen : vectorLength (U,V)≤L := by nlinarith
  have hprod := mul_le_mul_of_nonneg_left hlen R0_nonneg
  have hR := mul_le_mul_of_nonneg_right R0_lt_1689_1000.le hL
  have hb := mul_le_mul_of_nonneg_left (neg_le_abs b) hV
  dsimp [dot] at hdot
  nlinarith

lemma coarse_central_work {cx cy gx gy X Y : ℝ}
    (hc : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0))
    (hX : 0≤X) (hY : 0≤Y) (hx : gx≤X) (hy : gy≤Y) :
    gx*cx+gy*cy≤(113/1000)*(X+Y) := by
  have hcx : cx≤113/1000 := by dsimp [c0] at hc; linarith [rho0_upper]
  have hcy : cy≤113/1000 := by dsimp [c0] at hc; linarith [rho0_upper]
  have h1 := mul_le_mul_of_nonneg_right hx hc.1.1
  have h2 := mul_le_mul_of_nonneg_right hy hc.2.1
  have h3 := mul_le_mul_of_nonneg_left hcx hX
  have h4 := mul_le_mul_of_nonneg_left hcy hY
  nlinarith

lemma inward_primary_norm_identity (q : ℝ) :
    (19/50-(19/100)*Real.cos q)^2+((19/100)*Real.sin q)^2=
      361/2000-(361/2500)*Real.cos q := by
  nlinarith [Real.sin_sq_add_cos_sq q]

/-- A single endpoint support rule; L,X,Y are proved bounds, not a certificate. -/
lemma inward_primary_endpoint_lower {v d aw ad bd cx cy L X Y : ℝ}
    (haw : aw≤rho0) (hc : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0))
    (hD : ContainedChart ad |bd|)
    (hV : 0≤Real.sin (v+d)) (hL : 0≤L)
    (hNorm : 361/2000-(361/2500)*Real.cos (v+d)≤L^2)
    (hX : 0≤X) (hY : 0≤Y)
    (hcx : (43/100)*Real.cos v+(19/50)*Real.cos d≤X)
    (hcy : (19/50)*Real.sin d-(43/100)*Real.sin v≤Y) :
    69/100+(19/100)*(Real.cos d+Real.sin d)+(43/200)*(Real.cos v+Real.sin v)+
      (19/100)*Real.sin (v+d)-(31/50)*(1113/1000)-(1689/1000)*L-
      (113/1000)*(X+Y)≤inwardPrimaryFrozen v d aw ad bd cx cy := by
  have hsupport := vertex_linear_upper hD
    (U := 19/50-(19/100)*Real.cos (v+d)) (V := (19/100)*Real.sin (v+d))
    (by positivity) hL (by rwa [inward_primary_norm_identity])
  have hcentral := coarse_central_work hc hX hY hcx hcy
  have haw' : aw≤1113/1000 := haw.trans rho0_upper.le
  dsimp [inwardPrimaryFrozen,frozenTrig]
  nlinarith

lemma two_thirds_endpoint_bracket :
    (157:ℝ)/200≤Real.cos (2/3) ∧ Real.cos (2/3)≤787/1000 ∧
    (309:ℝ)/500≤Real.sin (2/3) ∧ Real.sin (2/3)≤619/1000 := by
  have hcl := Seven.cos_lower_six (x := (2:ℝ)/3) (by norm_num)
  have hcu := Seven.cos_upper_four (x := (2:ℝ)/3) (by norm_num)
  have hsl := Seven.sin_lower_seven (x := (2:ℝ)/3) (by norm_num)
  have hsu := Seven.sin_upper_five (x := (2:ℝ)/3) (by norm_num)
  norm_num at hcl hcu hsl hsu
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma quarter_endpoint_bracket :
    (707:ℝ)/1000≤Real.cos (Real.pi/4) ∧ Real.cos (Real.pi/4)≤708/1000 ∧
      Real.sin (Real.pi/4)=Real.cos (Real.pi/4) := by
  rw [Real.cos_pi_div_four,Real.sin_pi_div_four]
  have h := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  have hn := Real.sqrt_nonneg (2:ℝ)
  refine ⟨?_,?_,rfl⟩ <;> nlinarith

lemma inward_primary_corner_zero {aw ad bd cx cy : ℝ}
    (haw : aw≤rho0) (hD : ContainedChart ad |bd|)
    (hc : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0)) :
    0<inwardPrimaryFrozen 0 0 aw ad bd cx cy := by
  have had := hD.a_le_rho0
  have hcx := hc.1.2
  dsimp [c0] at hcx
  norm_num [inwardPrimaryFrozen,frozenTrig]
  linarith [rho0_upper]

lemma inward_primary_corner_far_zero {aw ad bd cx cy : ℝ}
    (haw : aw≤rho0) (hD : ContainedChart ad |bd|)
    (hc : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0)) :
    0<inwardPrimaryFrozen (2/3) 0 aw ad bd cx cy := by
  obtain ⟨hcl,hcu,hsl,hsu⟩ := two_thirds_endpoint_bracket
  have h := inward_primary_endpoint_lower (v := (2:ℝ)/3) (d := 0)
    (L := 26/100) (X := (43/100)*(787/1000)+19/50) (Y := 0)
    haw hc hD (by simpa using (show 0≤Real.sin (2/3) by linarith))
    (by norm_num) (by simp only [add_zero]; nlinarith)
    (by norm_num) (by norm_num)
    (by simp only [Real.cos_zero]; linarith)
    (by simp only [Real.sin_zero]; linarith)
  norm_num at h
  linarith

lemma inward_primary_corner_zero_quarter {aw ad bd cx cy : ℝ}
    (haw : aw≤rho0) (hD : ContainedChart ad |bd|)
    (hc : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0)) :
    0<inwardPrimaryFrozen 0 (Real.pi/4) aw ad bd cx cy := by
  obtain ⟨hhl,hhu,hsc⟩ := quarter_endpoint_bracket
  have h := inward_primary_endpoint_lower (v := 0) (d := Real.pi/4)
    (L := 281/1000) (X := 43/100+(19/50)*(708/1000)) (Y := (19/50)*(708/1000))
    haw hc hD (by rw [zero_add,hsc]; linarith)
    (by norm_num) (by simp only [zero_add]; nlinarith)
    (by norm_num) (by norm_num)
    (by simp only [Real.cos_zero]; linarith)
    (by simp only [Real.sin_zero,hsc]; linarith)
  simp only [Real.cos_zero,Real.sin_zero,zero_add,hsc] at h
  linarith

lemma inward_primary_corner_far_quarter {aw ad bd cx cy : ℝ}
    (haw : aw≤rho0) (hD : ContainedChart ad |bd|)
    (hc : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0)) :
    0<inwardPrimaryFrozen (2/3) (Real.pi/4) aw ad bd cx cy := by
  obtain ⟨hcl,hcu,hsl,hsu⟩ := two_thirds_endpoint_bracket
  obtain ⟨hhl,hhu,hsc⟩ := quarter_endpoint_bracket
  have hdiff : (166:ℝ)/1000≤Real.cos (2/3)-Real.sin (2/3) := by linarith
  have hsum : (1403:ℝ)/1000≤Real.cos (2/3)+Real.sin (2/3) := by linarith
  have hmc := mul_le_mul hdiff hhl (by norm_num : (0:ℝ)≤707/1000)
    (show 0≤Real.cos (2/3)-Real.sin (2/3) by linarith)
  have hms := mul_le_mul hsum hhl (by norm_num : (0:ℝ)≤707/1000)
    (show 0≤Real.cos (2/3)+Real.sin (2/3) by linarith)
  have hqcos : (166:ℝ)/1000*(707/1000)≤Real.cos (2/3+Real.pi/4) := by
    rw [Real.cos_add,hsc]
    nlinarith only [hmc]
  have hqsin : (1403:ℝ)/1000*(707/1000)≤Real.sin (2/3+Real.pi/4) := by
    rw [Real.sin_add,hsc]
    nlinarith only [hms]
  have h := inward_primary_endpoint_lower (v := (2:ℝ)/3) (d := Real.pi/4)
    (L := 405/1000) (X := (43/100)*(787/1000)+(19/50)*(708/1000)) (Y := 4/1000)
    haw hc hD (by linarith) (by norm_num) (by nlinarith)
    (by norm_num) (by norm_num) (by linarith) (by rw [hsc]; linarith)
  rw [hsc] at h
  linarith

end SquaresInCircles.Six.Analytic
