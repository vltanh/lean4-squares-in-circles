module

public import SquaresInCircles.Eight.TableFree.StationaryTerminalWeights

/-!
# The stationary cancellation in the normalized middle weight

Uncompiled reconstruction.  Dividing the actual five raw masses by the
actual raw middle weight gives the exact reciprocal formula.  Its five
positive terms are bounded on the whole rectangle, yielding the middle
weight bounds needed by the sharp terminal correction.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.StationaryTerminal
open ExactFamily.FiveCornerGeometry StationaryPrimitives

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

end SquaresInCircles.Eight.TableFree.StationaryTerminal
