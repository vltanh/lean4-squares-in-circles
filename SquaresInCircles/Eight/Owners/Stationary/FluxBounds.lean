module

public import SquaresInCircles.Eight.Owners.Stationary.TerminalWeights

/-!
# Eight squares: the secant flux reserve on the affine strip of positions

The first two circle equations express `r - U` exactly through `1 - u` (`circle_ratio_formula`).
The affine bounds of the position then control the flux ratio by one cubic inequality on the whole
tangent interval (`affine_ratio_upper`, `flux_ratio_upper`). This gives the second strict reserve
of the error, `23/1000` (`secant_reserve`).
-/

section
/-!
## The stationary cancellation in the normalized middle weight

Dividing the actual five raw masses by the
actual raw middle weight gives the exact reciprocal formula.  Its five
positive terms are bounded on the whole rectangle, yielding the middle
weight bounds needed by the sharp terminal correction.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.StationaryTerminal
open Stationary.FiveCornerGeometry StationaryPrimitives

theorem rawAlpha_identity (q u h : ℝ) (hr : lowerRight q u≠0) :
    rawAlpha q u h=cosine h*(u+h*lowerRight q u)/lowerRight q u := by
  dsimp [rawAlpha,positionA]
  rw [sine_eq]
  field_simp [hr]
  ring

theorem rawBeta_pos {q u h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (hh : h∈Icc (1/10:ℝ) (41/250)) : 0<rawBeta q u h := by
  have hr := radical_bounds hq hu
  have hf := force_bounds hq hu hh
  exact div_pos (mul_pos (by dsimp [rawAlpha]; linarith [hf.a_lower])
    (by linarith [hr.U_lower])) (by linarith [hu.2])

theorem beta_pos {q u h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (hh : h∈Icc (1/10:ℝ) (41/250)) : 0<(weights q u h).beta := by
  exact mul_pos (by linarith [(omega_bounds hq hu hh).1]) (rawBeta_pos hq hu hh)

theorem reciprocal_beta {q u h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (hh : h∈Icc (1/10:ℝ) (41/250))
    (hz : positionHalf q (cosine h) (sine h) u=0) :
    1/(weights q u h).beta=
      (2-u)/(2*topRight q u*(u+h*lowerRight q u))+
      1/(2*topRight q u)+1/(2*topLeft q u)+
      topHeight q u/(2*secondComponent q (cosine h) (sine h) u*topLeft q u*
        cosine h*(1+h*lowerHeight q u/lowerLeft q u))+
      h*topHeight q u/(2*topLeft q u*(lowerLeft q u+h*lowerHeight q u)) := by
  have hr := radical_bounds hq hu
  have hf := force_bounds hq hu hh
  have hcp := cosine_pos h
  have hp : 0<h := by linarith [hh.1]
  have hup : 0<u := by linarith [hu.1]
  have hrp : 0<lowerRight q u := by linarith [hr.r_lower]
  have hUp : 0<topRight q u := by linarith [hr.U_lower]
  have hVp : 0<topLeft q u := by linarith [hr.V_lower]
  have hYp : 0<topHeight q u := by linarith [hr.Y_lower]
  have hvp : 0<lowerHeight q u := by linarith [hr.v_lower]
  have hwp : 0<lowerLeft q u := by linarith [hr.w_lower]
  have hK1p : 0<firstComponent q (cosine h) (sine h) u := by linarith [hf.k1_lower]
  have hK2p : 0<secondComponent q (cosine h) (sine h) u := by linarith [hf.k2_lower]
  have hLp : 0<2-u := by linarith [hu.2]
  have hap : 0<rawAlpha q u h := by dsimp [rawAlpha]; linarith [hf.a_lower]
  have hbp := rawBeta_pos hq hu hh
  have hMp : 0<rawMassSum q u h := by linarith [(raw_mass_bounds hq hu hh).2.1]
  have hnr : 0<u+h*lowerRight q u := by positivity
  have hnw : 0<lowerLeft q u+h*lowerHeight q u := by positivity
  have hg : 0<1+h*lowerHeight q u/lowerLeft q u := by positivity
  have hcancel := rawBeta_cancellation hq hu hh hz
  have hA : rawMass q u h 0/rawBeta q u h=
      (2-u)/(2*topRight q u*(u+h*lowerRight q u)) := by
    change (cosine h/(2*lowerRight q u))/(rawAlpha q u h*topRight q u/(2-u))=_
    rw [rawAlpha_identity q u h hrp.ne']
    field_simp [hrp.ne',hUp.ne',hLp.ne',hcp.ne',hnr.ne']
  have hB : rawMass q u h 1/rawBeta q u h=1/(2*topRight q u) := by
    change (rawAlpha q u h/(2*(2-u)))/(rawAlpha q u h*topRight q u/(2-u))=_
    field_simp [hap.ne',hUp.ne',hLp.ne']
  have hD : rawMass q u h 2/rawBeta q u h=1/(2*topLeft q u) := by
    change (rawBeta q u h/(2*topLeft q u))/rawBeta q u h=_
    field_simp [hbp.ne',hVp.ne']
  have hH : rawMass q u h 4/rawBeta q u h=
      topHeight q u/(2*secondComponent q (cosine h) (sine h) u*topLeft q u*
        cosine h*(1+h*lowerHeight q u/lowerLeft q u)) := by
    change (1/(2*firstComponent q (cosine h) (sine h) u))/rawBeta q u h=_
    rw [hcancel]
    dsimp [rawEpsilon]
    field_simp [hK1p.ne',hK2p.ne',hVp.ne',hYp.ne',hcp.ne',hwp.ne',hg.ne',hnw.ne']
  have hE : rawMass q u h 3/rawBeta q u h=
      h*topHeight q u/(2*topLeft q u*(lowerLeft q u+h*lowerHeight q u)) := by
    change (sine h*rawEpsilon q u h/(2*lowerLeft q u))/rawBeta q u h=_
    rw [hcancel,sine_eq]
    dsimp [rawEpsilon]
    field_simp [hK1p.ne',hK2p.ne',hVp.ne',hYp.ne',hcp.ne',hwp.ne',hg.ne',hnw.ne']
  calc
    _ = rawMassSum q u h/rawBeta q u h := by
      dsimp [weights,omega]
      field_simp [hMp.ne',hbp.ne']
    _ = rawMass q u h 0/rawBeta q u h+rawMass q u h 1/rawBeta q u h+
        rawMass q u h 2/rawBeta q u h+rawMass q u h 4/rawBeta q u h+
        rawMass q u h 3/rawBeta q u h := by rw [massSum_formula]; ring
    _ = _ := by rw [hA,hB,hD,hH,hE]

theorem reciprocal_beta_bounds {q u h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (hh : h∈Icc (1/10:ℝ) (41/250))
    (hz : positionHalf q (cosine h) (sine h) u=0) :
    1293/1000<1/(weights q u h).beta ∧ 1/(weights q u h).beta<1439/1000 := by
  have hr := radical_bounds hq hu
  have hf := force_bounds hq hu hh
  have ht := trig_bounds hh
  have hl : 2-u∈Icc (53/50:ℝ) (221/200) := ⟨by linarith [hu.2],by linarith [hu.1]⟩
  let one := Interval.point 1
  let two := Interval.point 2
  let X := Interval.of_bounds hu
  let H := Interval.of_bounds hh
  let L := Interval.of_bounds hl
  let R := Interval.of_bounds hr.r
  let U := Interval.of_bounds hr.U
  let V := Interval.of_bounds hr.V
  let Y := Interval.of_bounds hr.Y
  let v := Interval.of_bounds hr.v
  let W := Interval.of_bounds hr.w
  let C := Interval.of_bounds ht.c
  let K2 := Interval.of_bounds hf.k2
  let G := one.add ((H.mul v).div W (by norm_num [W,Interval.of_bounds]))
  let tA := L.div ((two.mul U).mul (X.add (H.mul R)))
    (by norm_num [two,U,X,H,R,Interval.point,Interval.of_bounds,Interval.add,Interval.mul])
  let tB := one.div (two.mul U)
    (by norm_num [two,U,Interval.point,Interval.of_bounds,Interval.mul])
  let tD := one.div (two.mul V)
    (by norm_num [two,V,Interval.point,Interval.of_bounds,Interval.mul])
  let tH := Y.div ((((two.mul K2).mul V).mul C).mul G)
    (by norm_num [two,one,K2,V,C,G,H,v,W,Interval.point,Interval.of_bounds,
      Interval.add,Interval.mul,Interval.div,Interval.inv])
  let tE := (H.mul Y).div ((two.mul V).mul (W.add (H.mul v)))
    (by norm_num [two,V,W,H,v,Interval.point,Interval.of_bounds,Interval.add,Interval.mul])
  let S := (((tA.add tB).add tD).add tH).add tE
  have hS := S.mem
  have hlo : (1293/1000:ℝ)<S.lo := by
    norm_num [S,tA,tB,tD,tH,tE,G,one,two,X,H,L,R,U,V,Y,v,W,C,K2,
      Interval.point,Interval.of_bounds,Interval.add,Interval.mul,Interval.div,Interval.inv]
  have hhi : S.hi<(1439/1000:ℝ) := by
    norm_num [S,tA,tB,tD,tH,tE,G,one,two,X,H,L,R,U,V,Y,v,W,C,K2,
      Interval.point,Interval.of_bounds,Interval.add,Interval.mul,Interval.div,Interval.inv]
  rw [reciprocal_beta hq hu hh hz]
  exact ⟨hlo.trans_le hS.1,hS.2.trans_lt hhi⟩

theorem beta_bounds {q u h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (hh : h∈Icc (1/10:ℝ) (41/250))
    (hz : positionHalf q (cosine h) (sine h) u=0) :
    69/100<(weights q u h).beta ∧ (weights q u h).beta<39/50 := by
  have hp := beta_pos hq hu hh
  obtain ⟨hl,hu⟩ := reciprocal_beta_bounds hq hu hh hz
  rw [lt_div_iff₀ hp] at hl
  rw [div_lt_iff₀ hp] at hu
  exact ⟨by linarith,by linarith⟩

end SquaresInCircles.Eight.StationaryTerminal
end
end
end

section
/-!
## Exact force ratios and the first strict terminal reserve

The normalized masses cancel in the three
quadratic coefficients.  Their bounds and the small-error flux reserve
then follow from the actual circle rectangle and the position equation.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.StationaryTerminal
open Stationary.FiveCornerGeometry StationaryPrimitives CanonicalNegativeStress

theorem coefficient_identities {q u h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (hh : h∈Icc (1/10:ℝ) (41/250)) :
    (weights q u h).a=(weights q u h).beta*(2-u)/topRight q u ∧
    KA (weights q u h)=(weights q u h).a*lowerRight q u/cosine h ∧
    KB (weights q u h)=(weights q u h).beta*(2-u) ∧
    (weights q u h).beta^2/(2*(weights q u h).mu 2)=
      (weights q u h).beta*topLeft q u := by
  have hr := radical_bounds hq hu
  have hf := force_bounds hq hu hh
  have hL : 2-u≠0 := ne_of_gt (by linarith [hu.2])
  have hR : lowerRight q u≠0 := ne_of_gt (by linarith [hr.r_lower])
  have hU : topRight q u≠0 := ne_of_gt (by linarith [hr.U_lower])
  have hV : topLeft q u≠0 := ne_of_gt (by linarith [hr.V_lower])
  have hC : cosine h≠0 := (cosine_pos h).ne'
  have hA : rawAlpha q u h≠0 := ne_of_gt (by dsimp [rawAlpha]; linarith [hf.a_lower])
  have hB : rawBeta q u h≠0 := (rawBeta_pos hq hu hh).ne'
  have hO : omega q u h≠0 := ne_of_gt (by linarith [(omega_bounds hq hu hh).1])
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [weights,rawBeta]
    field_simp [hL,hU]
  · dsimp [KA,weights,rawMass]
    field_simp [hO,hR,hC]
  · dsimp [KB,weights,rawMass]
    field_simp [hO,hA,hL]
  · dsimp [weights,rawMass]
    field_simp [hO,hB,hV]

theorem alpha_bound {q u h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (hh : h∈Icc (1/10:ℝ) (41/250))
    (hz : positionHalf q (cosine h) (sine h) u=0) :
    0≤(weights q u h).a ∧ (weights q u h).a<263/500 := by
  have hr := radical_bounds hq hu
  have hl : 2-u∈Icc (53/50:ℝ) (221/200) := ⟨by linarith [hu.2],by linarith [hu.1]⟩
  have hratio := quotient_bounds hl hr.U (by norm_num) (by norm_num)
  have hratio' : (2-u)/topRight q u∈Icc 0 (337/500:ℝ) :=
    ⟨by linarith [hratio.1],by linarith [hratio.2]⟩
  have hb := beta_bounds hq hu hh hz
  have hp := product_bounds
    (show (weights q u h).beta∈Icc 0 (39/50:ℝ) from ⟨by linarith [hb.1],hb.2.le⟩)
    hratio' (by norm_num) (by norm_num)
  rw [(coefficient_identities hq hu hh).1,mul_div_assoc]
  constructor <;> linarith [hp.1,hp.2]

theorem correction_coefficients {q u h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (hh : h∈Icc (1/10:ℝ) (41/250))
    (hz : positionHalf q (cosine h) (sine h) u=0) :
    (weights q u h).omega∈Icc 0 (4/5:ℝ) ∧
    KA (weights q u h)∈Icc 0 (471/500:ℝ) ∧
    (weights q u h).beta∈Icc 0 (39/50:ℝ) ∧
    KB (weights q u h)∈Icc 0 (431/500:ℝ) ∧
    (weights q u h).beta^2/(2*(weights q u h).mu 2)∈Icc 0 (6/5:ℝ) := by
  have hr := radical_bounds hq hu
  have ht := trig_bounds hh
  have ho := omega_bounds hq hu hh
  have ha := alpha_bound hq hu hh hz
  have hb := beta_bounds hq hu hh hz
  have hbc : (weights q u h).beta∈Icc 0 (39/50:ℝ) := ⟨by linarith [hb.1],hb.2.le⟩
  have hl : 2-u∈Icc (53/50:ℝ) (221/200) := ⟨by linarith [hu.2],by linarith [hu.1]⟩
  obtain ⟨_,hKA,hKB,hgamma⟩ := coefficient_identities hq hu hh
  have hrc := quotient_bounds hr.r ht.c (by norm_num) (by norm_num)
  have hA := product_bounds (show (weights q u h).a∈Icc 0 (263/500:ℝ) from ⟨ha.1,ha.2.le⟩)
    hrc (by norm_num) (by norm_num)
  have hB := product_bounds hbc hl (by norm_num) (by norm_num)
  have hD := product_bounds hbc hr.V (by norm_num) (by norm_num)
  refine ⟨⟨by change 0≤omega q u h; linarith [ho.1],ho.2.le⟩,?_,hbc,?_,?_⟩
  · rw [hKA,mul_div_assoc]
    constructor <;> linarith [hA.1,hA.2]
  · rw [hKB]
    exact ⟨by linarith [hB.1],by linarith [hB.2]⟩
  · rw [hgamma]
    exact ⟨by linarith [hD.1],by linarith [hD.2]⟩

theorem flux_formula {q u h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (hh : h∈Icc (1/10:ℝ) (41/250)) :
    flux (weights q u h) (Real.arctan h)=
      omega q u h*(cosine h*u+sine h*(lowerRight q u-1)) := by
  have hr := radical_bounds hq hu
  have hR : lowerRight q u≠0 := ne_of_gt (by linarith [hr.r_lower])
  have hC : cosine h≠0 := (cosine_pos h).ne'
  rw [flux,(coefficient_identities hq hu hh).2.1]
  change (omega q u h*rawAlpha q u h*lowerRight q u/cosine h)*cosine h-
    omega q u h*sine h=_
  dsimp [rawAlpha,positionA]
  field_simp [hR,hC]
  ring

theorem flux_pos {q u h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (hh : h∈Icc (1/10:ℝ) (41/250)) :
    0<flux (weights q u h) (Real.arctan h) := by
  have hr := radical_bounds hq hu
  have ht := trig_bounds hh
  rw [flux_formula hq hu hh]
  apply mul_pos (by linarith [(omega_bounds hq hu hh).1])
  exact add_pos (mul_pos (cosine_pos h) (by linarith [hu.1]))
    (mul_pos (by linarith [ht.s_lower]) (by linarith [hr.r_lower]))

theorem small_reserve_identity {q u h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (hh : h∈Icc (1/10:ℝ) (41/250)) :
    KB (weights q u h)-flux (weights q u h) (Real.arctan h)=
      omega q u h*(sine h-rawAlpha q u h*(lowerRight q u-topRight q u)) := by
  have hr := radical_bounds hq hu
  have hL : 2-u≠0 := ne_of_gt (by linarith [hu.2])
  have hR : lowerRight q u≠0 := ne_of_gt (by linarith [hr.r_lower])
  rw [(coefficient_identities hq hu hh).2.2.1,flux_formula hq hu hh]
  dsimp [weights,rawBeta,rawAlpha,positionA]
  field_simp [hL,hR]
  ring

/-- This reserve uses the whole rectangle only; it remains strict even
before imposing the narrower affine strip. -/
theorem small_reserve {q u h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (hh : h∈Icc (1/10:ℝ) (41/250)) :
    3367/250000<KB (weights q u h)-flux (weights q u h) (Real.arctan h) := by
  have hr := radical_bounds hq hu
  have ht := trig_bounds hh
  have hf := force_bounds hq hu hh
  have hcur := quotient_bounds (product_bounds ht.c hu (by norm_num) (by norm_num)) hr.r
    (by norm_num) (by norm_num)
  have hcurU : cosine h*u/lowerRight q u<27/50 := by linarith [hcur.2]
  have hdelta : lowerRight q u-topRight q u<31/250 := by linarith [hr.r_upper,hr.U_lower]
  have ha : 0<rawAlpha q u h := by dsimp [rawAlpha]; linarith [hf.a_lower]
  have hp := mul_lt_mul_of_pos_left hdelta ha
  have hbase : 10101/500000<sine h-(31/250)*rawAlpha q u h := by
    dsimp [rawAlpha,positionA]
    linarith [ht.s_lower]
  have hinner : 10101/500000<
      sine h-rawAlpha q u h*(lowerRight q u-topRight q u) := by linarith
  have ho := (omega_bounds hq hu hh).1
  have hprod := mul_lt_mul_of_pos_left hinner (by linarith : 0<omega q u h)
  rw [small_reserve_identity hq hu hh]
  nlinarith

end SquaresInCircles.Eight.StationaryTerminal
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.StationaryTerminal
open Stationary.FiveCornerGeometry StationaryPrimitives CanonicalNegativeStress

theorem circle_ratio_formula {q u : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50)) :
    lowerRight q u/topRight q u=
      1+4*(1-u)/((lowerRight q u+topRight q u)*topRight q u) := by
  have hr := radical_bounds hq hu
  have hd := hr.smoothDomain (by linarith [hq.2]) (by linarith [hu.1])
  have hR : 0<lowerRight q u := by linarith [hr.r_lower]
  have hU : 0<topRight q u := by linarith [hr.U_lower]
  have hsum : 0<lowerRight q u+topRight q u := add_pos hR hU
  have hcR := upper_circle hd.first_radicand
  have hcU := upper_circle hd.second_radicand
  change lowerRight q u^2+u^2=q at hcR
  change topRight q u^2+(2-u)^2=q at hcU
  have hdiff : (lowerRight q u-topRight q u)*(lowerRight q u+topRight q u)=4*(1-u) := by
    nlinarith
  have he : 4*(1-u)/(lowerRight q u+topRight q u)=lowerRight q u-topRight q u :=
    (div_eq_iff hsum.ne').2 hdiff.symm
  calc
    _ = 1+(lowerRight q u-topRight q u)/topRight q u := by field_simp [hU.ne']; ring
    _ = _ := by rw [← he]; simp only [div_eq_mul_inv,mul_inv_rev]; ring

theorem affine_ratio_upper {q u h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (_hh : h∈Icc (1/10:ℝ) (41/250))
    (ha : 1-(7/10)*h<u ∧ u<1-(3/5)*h) :
    lowerRight q u/topRight q u<1+(101/200)*h ∧
      u+h*lowerRight q u<1+(233/200)*h := by
  have hr := radical_bounds hq hu
  have hp : 0<h := by linarith
  have hsum : lowerRight q u+topRight q u∈Icc (1691/500:ℝ) (859/250) :=
    ⟨by linarith [hr.r_lower,hr.U_lower],by linarith [hr.r_upper,hr.U_upper]⟩
  have hden := product_bounds hsum hr.U (by norm_num) (by norm_num)
  have hdenp : 0<(lowerRight q u+topRight q u)*topRight q u := by linarith [hden.1]
  have hscaled := mul_le_mul_of_nonneg_left hden.1 (by positivity : 0≤(101/200:ℝ)*h)
  have hquot : 4*(1-u)/((lowerRight q u+topRight q u)*topRight q u)<(101/200)*h := by
    apply (div_lt_iff₀ hdenp).2
    nlinarith [ha.1]
  have hR := mul_lt_mul_of_pos_left hr.r_upper hp
  refine ⟨?_,by linarith [ha.2]⟩
  rw [circle_ratio_formula hq hu]
  linarith

theorem flux_ratio_formula {q u h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (hh : h∈Icc (1/10:ℝ) (41/250)) :
    flux (weights q u h) (Real.arctan h)/(weights q u h).beta=
      (2-u)*(lowerRight q u/topRight q u)*(1-h/(u+h*lowerRight q u)) := by
  have hr := radical_bounds hq hu
  have hR : lowerRight q u≠0 := ne_of_gt (by linarith [hr.r_lower])
  have hU : topRight q u≠0 := ne_of_gt (by linarith [hr.U_lower])
  have hL : 2-u≠0 := ne_of_gt (by linarith [hu.2])
  have hC : cosine h≠0 := (cosine_pos h).ne'
  have hO : omega q u h≠0 := ne_of_gt (by linarith [(omega_bounds hq hu hh).1])
  have hN : u+h*lowerRight q u≠0 := ne_of_gt (by
    have hu0 : 0<u := by linarith [hu.1]
    have hh0 : 0<h := by linarith [hh.1]
    have hr0 : 0<lowerRight q u := by linarith [hr.r_lower]
    positivity)
  rw [flux_formula hq hu hh]
  change (omega q u h*(cosine h*u+sine h*(lowerRight q u-1)))/
    (omega q u h*(rawAlpha q u h*topRight q u/(2-u)))=_
  rw [rawAlpha_identity q u h hR,sine_eq]
  field_simp [hR,hU,hL,hC,hO,hN]
  ring

/-- On the whole tangent interval the flux ratio is below `21/20`, by a cubic comparison. -/
theorem flux_ratio_upper {q u h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (hh : h∈Icc (1/10:ℝ) (41/250))
    (ha : 1-(7/10)*h<u ∧ u<1-(3/5)*h) :
    flux (weights q u h) (Real.arctan h)/(weights q u h).beta<21/20 := by
  have hr := radical_bounds hq hu
  have hp : 0<h := by linarith [hh.1]
  have hu0 : 0<u := by linarith [hu.1]
  have hr0 : 0<lowerRight q u := by linarith [hr.r_lower]
  have hU0 : 0<topRight q u := by linarith [hr.U_lower]
  obtain ⟨hru,hNu⟩ := affine_ratio_upper hq hu hh ha
  have hL : 2-u<1+(7/10)*h := by linarith [ha.1]
  have hN : 0<u+h*lowerRight q u := by positivity
  have hNm : 0<u+h*lowerRight q u-h := by
    have hpR := mul_pos hp (by linarith [hr.r_lower] : 0<lowerRight q u-1)
    nlinarith
  have hD : 0<1+(233/200)*h := by positivity
  have hF : 1-h/(u+h*lowerRight q u)=
      (u+h*lowerRight q u-h)/(u+h*lowerRight q u) := by field_simp [hN.ne']
  have hz0 : 0<1-h/(u+h*lowerRight q u) := by rw [hF]; exact div_pos hNm hN
  have hzU : 1-h/(u+h*lowerRight q u)<(1+(33/200)*h)/(1+(233/200)*h) := by
    rw [hF]
    apply (div_lt_div_iff₀ hN hD).2
    have hs := mul_pos hp (sub_pos.mpr hNu)
    nlinarith
  have hratio0 : 0<lowerRight q u/topRight q u := div_pos hr0 hU0
  have hprod : (2-u)*(lowerRight q u/topRight q u)<
      (1+(7/10)*h)*(1+(101/200)*h) := by
    calc
      _ < (1+(7/10)*h)*(lowerRight q u/topRight q u) := mul_lt_mul_of_pos_right hL hratio0
      _ < _ := mul_lt_mul_of_pos_left hru (by positivity)
  have hprod2 : (2-u)*(lowerRight q u/topRight q u)*(1-h/(u+h*lowerRight q u))<
      (1+(7/10)*h)*(1+(101/200)*h)*((1+(33/200)*h)/(1+(233/200)*h)) := by
    calc
      _ < (1+(7/10)*h)*(1+(101/200)*h)*(1-h/(u+h*lowerRight q u)) :=
        mul_lt_mul_of_pos_right hprod hz0
      _ < _ := mul_lt_mul_of_pos_left hzU (by positivity)
  have hh2 := pow_le_pow_left₀ hp.le hh.2 2
  have hh3 := pow_le_pow_left₀ hp.le hh.2 3
  have hpoly : 0<(1/20:ℝ)-(587/4000)*h-(22093/40000)*h^2-(23331/400000)*h^3 := by
    nlinarith [hh.2]
  have hid : (21/20:ℝ)*(1+(233/200)*h)-
      (1+(7/10)*h)*(1+(101/200)*h)*(1+(33/200)*h)=
      (1/20:ℝ)-(587/4000)*h-(22093/40000)*h^2-(23331/400000)*h^3 := by ring
  have hupper : (1+(7/10)*h)*(1+(101/200)*h)*((1+(33/200)*h)/(1+(233/200)*h))<21/20 := by
    rw [show (1+(7/10)*h)*(1+(101/200)*h)*((1+(33/200)*h)/(1+(233/200)*h))=
      ((1+(7/10)*h)*(1+(101/200)*h)*(1+(33/200)*h))/(1+(233/200)*h) by ring]
    apply (div_lt_iff₀ hD).2
    linarith
  rw [flux_ratio_formula hq hu hh]
  exact hprod2.trans hupper

theorem secant_reserve {q u h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (hh : h∈Icc (1/10:ℝ) (41/250))
    (ha : 1-(7/10)*h<u ∧ u<1-(3/5)*h)
    (hz : positionHalf q (cosine h) (sine h) u=0) :
    23/1000<(weights q u h).beta*(13/12)-flux (weights q u h) (Real.arctan h) := by
  have hb := (beta_bounds hq hu hh hz).1
  have hc := (div_lt_iff₀ (beta_pos hq hu hh)).mp (flux_ratio_upper hq hu hh ha)
  linarith

end SquaresInCircles.Eight.StationaryTerminal
end
end
end
