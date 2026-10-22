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
  have hn := radical_positive (A:=1+c^2) (x:=x) (by positivity)
  have hn2 := radical_square (A:=1+c^2) (x:=x) (by positivity)
  have hpow (n : ℕ) : (radical (1+c^2) x)^(n+2)=
      (radical (1+c^2) x)^n*(1+c^2+x^2) := by rw [pow_add,hn2]
  have hd := (((((hasDerivAt_id x).pow 2).const_add 1).pow 3).const_mul
    (R*(1+c^2))).div ((radical_hasDerivAt (A:=1+c^2) (by positivity)).pow 5)
      (pow_ne_zero 5 hn.ne')
  convert hd using 1
  · funext y
    dsimp [mass]
    ring
  · dsimp [mass,firstLog]
    field_simp [hn.ne',show 1+x^2≠0 by positivity,
      show 1+x^2+c^2≠0 by positivity]
    ring_nf
    simp only [hpow 0,hpow 1,hpow 2,hpow 3,hpow 4,hpow 5,hpow 6,
      hpow 7,hpow 8,hpow 9,hpow 10,hpow 11,hpow 12,hpow 13,
      hpow 14,hpow 15,hpow 16,hpow 17,hpow 18,pow_zero,pow_one]
    ring

theorem mass_monotone_angle (c : ℝ) {x y : ℝ} (hx : 0≤x) (hxy : x≤y) :
    mass c x≤mass c y := by
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
  have hd := ((hasDerivAt_const c (5:ℝ)).div
    (((hasDerivAt_id c).pow 2).const_add (1+x^2)) (by positivity : 1+x^2+c^2≠0)).sub
    ((hasDerivAt_const c (2:ℝ)).div (((hasDerivAt_id c).pow 2).const_add 1)
      (by positivity : 1+c^2≠0))
  convert hd using 1
  · rfl
  · field_simp [show 1+x^2+c^2≠0 by positivity,show 1+c^2≠0 by positivity]
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
  let c := coefficient bt3 x
  have hn := radical_positive (A:=1+c^2) (x:=x) (by positivity)
  have hn2 := radical_square (A:=1+c^2) (x:=x) (by positivity)
  have hpow (n : ℕ) : (radical (1+c^2) x)^(n+2)=
      (radical (1+c^2) x)^n*(1+c^2+x^2) := by rw [pow_add,hn2]
  have hA := ((coefficient_hasDerivAt bt3 x).pow 2).const_add 1
  have ha := ((hasDerivAt_id x).pow 2).const_add 1
  have hroot := (hA.add ((hasDerivAt_id x).pow 2)).sqrt
    (by positivity : 1+(coefficient bt3 x)^2+x^2≠0)
  have hd := ((hA.mul (ha.pow 3)).const_mul R).div (hroot.pow 5)
    (pow_ne_zero 5 hn.ne')
  convert hd using 1
  · funext y
    dsimp [total,mass,radical]
    ring
  · change mass c x*(firstLog c x+secondLog bt3 c x)=_
    dsimp [mass,firstLog,secondLog,bracket]
    change _=(_ : ℝ)
    field_simp [hn.ne',show 1+x^2≠0 by positivity,show 1+c^2≠0 by positivity,
      show 1+x^2+c^2≠0 by positivity,show 1+c^2+x^2≠0 by positivity]
    ring_nf
    simp only [hpow 0,hpow 1,hpow 2,hpow 3,hpow 4,hpow 5,hpow 6,
      hpow 7,hpow 8,hpow 9,hpow 10,hpow 11,hpow 12,hpow 13,
      hpow 14,hpow 15,hpow 16,hpow 17,hpow 18,pow_zero,pow_one]
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
