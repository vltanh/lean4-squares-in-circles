module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDEHighLateData

/-!
# The late correlated radical derivative, with both original coefficient lines

Uncompiled transcription of the logarithmic-derivative calculation in
the high-DE companions. The first term uses the already transcribed
quartic certificate. The second term is bounded by monotonicity of its
explicit reciprocal bracket. The coefficient and angle remain correlated
in the differentiated function.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEHighShape.Late
open Candidate Secondary PositiveAngularEnvelope
open NegativeAPositiveTD.SecantCoordinate

theorem mass_hasDerivAt (c x : ℝ) :
    HasDerivAt (mass c) (mass c x*firstLog c x) x := by
  have hA : (0:ℝ)<1+c^2 := by positivity
  have hn := radical_positive (A:=1+c^2) (x:=x) hA
  have hn2 := radical_square (A:=1+c^2) (x:=x) hA
  have h1 : HasDerivAt (fun y : ℝ => 1+y^2) (2*x) x :=
    ((hasDerivAt_pow 2 x).const_add 1).congr_deriv (by norm_num)
  have hu : HasDerivAt (fun y : ℝ => R*(1+c^2)*(1+y^2)^3) (R*(1+c^2)*(3*(1+x^2)^2*(2*x))) x :=
    ((h1.pow 3).const_mul (R*(1+c^2))).congr_deriv (by norm_num)
  have hv : HasDerivAt (fun y => (radical (1+c^2) y)^5)
      (5*(radical (1+c^2) x)^4*(x/radical (1+c^2) x)) x :=
    ((radical_hasDerivAt (x:=x) hA).pow 5).congr_deriv (by norm_num)
  have hd := hu.div hv (pow_ne_zero 5 hn.ne')
  have hf : mass c=fun y => R*(1+c^2)*(1+y^2)^3/(radical (1+c^2) y)^5 := rfl
  rw [hf]
  refine hd.congr_deriv ?_
  simp only [firstLog]
  generalize radical (1+c^2) x=N at hn hn2 ⊢
  have hx1 : (0:ℝ)<1+x^2 := by positivity
  calc _=R*(1+c^2)*(1+x^2)^2*x*(6*N^2-5*(1+x^2))/(N^5*N^2) := by
          field_simp
          ring
    _=R*(1+c^2)*(1+x^2)^2*x*(6*(1+c^2+x^2)-5*(1+x^2))/(N^5*(1+c^2+x^2)) := by rw [hn2]
    _=_ := by
          field_simp
          ring

theorem mass_monotone_angle (c : ℝ) {x y : ℝ} (hx : 0≤x) (hxy : x≤y) :
    mass c x≤ mass c y := by
  have hm : MonotoneOn (mass c) (Icc x y) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun t _ => (mass_hasDerivAt c t).continuousAt.continuousWithinAt)
      (fun t _ => mass_hasDerivAt c t)
    intro t ht
    have ht0 : 0≤t := hx.trans ht.1.le
    have hh : 0≤firstLog c t := by dsimp [firstLog]; positivity
    exact mul_nonneg (mass_pos c t).le hh
  exact hm ⟨le_rfl,hxy⟩ ⟨hxy,le_rfl⟩ hxy

theorem total_upper (bt3 : Bool) {x : ℝ}
    (hx : x∈Icc (Real.tan (11/20:ℝ)) (Real.tan frameCap)) : total bt3 x<183/100 := by
  have hd := (domain hx).1
  have hc := coefficient_bounds bt3 hx
  have hmono := mass_antitone_coefficient
    (by norm_num : (0:ℝ)≤863/1000) hc.1 (by linarith [hd.1])
    (by nlinarith [pow_le_pow_left₀ (show 0≤x by linarith [hd.1]) hd.2 2] : 2*x^2≤3)
  have ht := mass_monotone_angle (863/1000) (by linarith [hd.1]) hd.2
  exact (hmono.trans ht).trans_lt rational_mass_endpoints.1

theorem firstLog_upper {c x : ℝ}
    (hc : c∈Icc (863/1000:ℝ) (909/1000))
    (hx : x∈Icc (613/1000:ℝ) (843/1000)) : firstLog c x<27/20 := by
  have hx0 : 0≤x := by linarith [hx.1]
  have hc0 : 0≤c := by linarith [hc.1]
  have hc2 : c^2≤827/1000 := by
    nlinarith [pow_le_pow_left₀ hc0 hc.2 2]
  have ha : 0<1+x^2 := by positivity
  have hd : 0<1+x^2+c^2 := by positivity
  have hD : 0<1+x^2+827/1000 := by positivity
  have hcompare : firstLog c x≤
      x*(1+x^2+6*(827/1000))/((1+x^2)*(1+x^2+827/1000)) := by
    unfold firstLog
    apply (div_le_div_iff₀ (mul_pos ha hd) (mul_pos ha hD)).2
    have hprod := mul_nonneg (show 0≤5*x*(1+x^2)^2 by positivity)
      (sub_nonneg.mpr hc2)
    nlinarith only [hprod]
  have hpoly := Certificate.late_fraction_lower hx
  have hupper : x*(1+x^2+6*(827/1000))/((1+x^2)*(1+x^2+827/1000))<27/20 := by
    apply (div_lt_iff₀ (mul_pos ha hD)).2
    linarith
  exact hcompare.trans_lt hupper

theorem bracket_hasDerivAt (c x : ℝ) :
    HasDerivAt (fun c => bracket c x)
      (2*c*(2*(1+x^2+c^2)^2-5*(1+c^2)^2)/
        ((1+x^2+c^2)^2*(1+c^2)^2)) c := by
  have h1 : HasDerivAt (fun c : ℝ => 1+x^2+c^2) (2*c) c :=
    ((hasDerivAt_pow 2 c).const_add (1+x^2)).congr_deriv (by norm_num)
  have h2 : HasDerivAt (fun c : ℝ => 1+c^2) (2*c) c :=
    ((hasDerivAt_pow 2 c).const_add 1).congr_deriv (by norm_num)
  have hd := ((hasDerivAt_const c (5:ℝ)).div h1 (by positivity)).sub
    ((hasDerivAt_const c (2:ℝ)).div h2 (by positivity))
  have hf : (fun c => bracket c x)=fun c : ℝ => 5/(1+x^2+c^2)-2/(1+c^2) := rfl
  rw [hf]
  refine hd.congr_deriv ?_
  field_simp
  ring

theorem bracket_antitone_coefficient {c x : ℝ}
    (hc : c∈Icc (863/1000:ℝ) (909/1000))
    (hx : x∈Icc (613/1000:ℝ) (843/1000)) :
    bracket c x≤bracket (863/1000) x := by
  have hx2 := pow_le_pow_left₀ (show 0≤x by linarith [hx.1]) hx.2 2
  have hm : AntitoneOn (fun c => bracket c x) (Icc (863/1000:ℝ) c) := by
    apply antiOn_of_hasDeriv_nonpos
      (fun v _ => (bracket_hasDerivAt v x).continuousAt.continuousWithinAt)
      (fun v _ => bracket_hasDerivAt v x)
    intro v hv
    have hv0 : 0≤v := by linarith [hv.1]
    have hv2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤863/1000) hv.1.le 2
    have hcomparison : 1+x^2+v^2≤(3/2)*(1+v^2) := by nlinarith
    have hsquare := pow_le_pow_left₀ (by positivity : 0≤1+x^2+v^2) hcomparison 2
    have hnum : 2*(1+x^2+v^2)^2-5*(1+v^2)^2≤0 := by
      nlinarith [sq_nonneg (1+v^2)]
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by linarith) hnum) (by positivity)
  exact hm ⟨le_rfl,hc.1⟩ ⟨hc.1,le_rfl⟩ hc.1

theorem bracket_bounds {c x : ℝ}
    (hc : c∈Icc (863/1000:ℝ) (909/1000))
    (hx : x∈Icc (613/1000:ℝ) (843/1000)) :
    0≤bracket c x ∧ bracket c x≤bracket (863/1000) (613/1000) := by
  have hx0 : 0≤x := by linarith [hx.1]
  have hxl := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤613/1000) hx.1 2
  have hxu := pow_le_pow_left₀ hx0 hx.2 2
  constructor
  · unfold bracket
    apply sub_nonneg.mpr
    apply (div_le_div_iff₀ (by positivity : 0<1+c^2) (by positivity : 0<1+x^2+c^2)).2
    nlinarith [sq_nonneg c]
  · have hangle : bracket (863/1000) x≤bracket (863/1000) (613/1000) := by
      have hh := div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤5)
        (by norm_num : (0:ℝ)<1+(613/1000)^2+(863/1000)^2)
        (show 1+(613/1000:ℝ)^2+(863/1000:ℝ)^2≤1+x^2+(863/1000:ℝ)^2 by linarith)
      exact sub_le_sub_right hh _
    exact (bracket_antitone_coefficient hc hx).trans hangle

theorem secondLog_upper (bt3 : Bool) {c x : ℝ}
    (hc : c∈Icc (863/1000:ℝ) (909/1000))
    (hx : x∈Icc (613/1000:ℝ) (843/1000)) : secondLog bt3 c x<63/250 := by
  have hc0 : 0≤c := by linarith [hc.1]
  have hxl := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤613/1000) hx.1 2
  have hnum := mul_le_mul (rate_bounds bt3).2 hc.2 hc0 (by norm_num : (0:ℝ)≤61/200)
  have hcoef : rate bt3*c/(1+x^2)≤
      ((61/200:ℝ)*(909/1000))/(1+(613/1000:ℝ)^2) :=
    div_le_div₀ (by norm_num) hnum (by norm_num) (by linarith)
  have hb := bracket_bounds hc hx
  have hh := mul_le_mul hcoef hb.2 hb.1 (by norm_num)
  have hfinal : (((61/200:ℝ)*(909/1000))/(1+(613/1000:ℝ)^2))*
      bracket (863/1000) (613/1000)<63/250 := by norm_num [bracket]
  exact hh.trans_lt hfinal

theorem total_hasDerivAt (bt3 : Bool) (x : ℝ) :
    HasDerivAt (total bt3) (totalFirst bt3 x) x := by
  have hk := coefficient_hasDerivAt bt3 x
  have hx2 : HasDerivAt (fun y : ℝ => y^2) (2*x) x := (hasDerivAt_pow 2 x).congr_deriv (by norm_num)
  have hP : HasDerivAt (fun y => 1+(coefficient bt3 y)^2)
      (2*coefficient bt3 x*(-rate bt3/(1+x^2))) x :=
    ((hk.pow 2).const_add 1).congr_deriv (by norm_num)
  have hQ : HasDerivAt (fun y : ℝ => (1+y^2)^3) (3*(1+x^2)^2*(2*x)) x :=
    ((hx2.const_add 1).pow 3).congr_deriv (by norm_num)
  have hS := hP.add hx2
  have hSpos : 0<1+(coefficient bt3 x)^2+x^2 := by positivity
  have hroot := hS.sqrt hSpos.ne'
  have hNpos : 0<Real.sqrt (1+(coefficient bt3 x)^2+x^2) := Real.sqrt_pos.mpr hSpos
  have hden : HasDerivAt (fun y => (Real.sqrt (1+(coefficient bt3 y)^2+y^2))^5)
      (5*(Real.sqrt (1+(coefficient bt3 x)^2+x^2))^4*
        ((2*coefficient bt3 x*(-rate bt3/(1+x^2))+2*x)/
          (2*Real.sqrt (1+(coefficient bt3 x)^2+x^2)))) x :=
    (hroot.pow 5).congr_deriv (by norm_num)
  have hnum := (hP.mul hQ).const_mul R
  have hd := hnum.div hden (pow_ne_zero 5 hNpos.ne')
  have hf : total bt3=fun y => R*((1+(coefficient bt3 y)^2)*(1+y^2)^3)/
      (Real.sqrt (1+(coefficient bt3 y)^2+y^2))^5 := by
    funext y
    simp only [total,mass,radical]
    ring
  rw [hf]
  refine hd.congr_deriv ?_
  simp only [totalFirst,total,mass,firstLog,secondLog,bracket,radical,Pi.mul_apply]
  have hN2 := Real.sq_sqrt hSpos.le
  generalize Real.sqrt (1+(coefficient bt3 x)^2+x^2)=N at hNpos hN2 ⊢
  generalize coefficient bt3 x=c at hN2 ⊢
  have hx1 : (0:ℝ)<1+x^2 := by positivity
  have hc1 : (0:ℝ)<1+c^2 := by positivity
  calc _=R*(1+x^2)^2*(2*c*(-rate bt3/(1+x^2))*(1+x^2)*N^2+6*x*(1+c^2)*N^2-
          5*(1+c^2)*(1+x^2)*(c*(-rate bt3/(1+x^2))+x))/(N^5*N^2) := by
          field_simp
          ring
    _=R*(1+x^2)^2*(2*c*(-rate bt3/(1+x^2))*(1+x^2)*(1+c^2+x^2)+6*x*(1+c^2)*(1+c^2+x^2)-
          5*(1+c^2)*(1+x^2)*(c*(-rate bt3/(1+x^2))+x))/(N^5*(1+c^2+x^2)) := by rw [hN2]
    _=_ := by
          field_simp
          ring

theorem total_derivative_upper (bt3 : Bool) {x : ℝ}
    (hx : x∈Icc (Real.tan (11/20:ℝ)) (Real.tan frameCap)) : totalFirst bt3 x<3 := by
  have hc := coefficient_bounds bt3 hx
  have hd := (domain hx).1
  have hfirst := firstLog_upper hc hd
  have hsecond := secondLog_upper bt3 hc hd
  have htotal := total_upper bt3 hx
  have hpos : 0<total bt3 x := mass_pos _ _
  have hh := mul_le_mul_of_nonneg_left
    (show firstLog (coefficient bt3 x) x+secondLog bt3 (coefficient bt3 x) x≤
      27/20+63/250 by linarith) hpos.le
  dsimp [totalFirst]
  nlinarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEHighShape.Late
