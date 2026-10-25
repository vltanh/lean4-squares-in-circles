module

public import SquaresInCircles.Eight.TableFree.CrossedClampInverseGeometry

/-!
# Exact cap derivatives and their geometric rate formulas

Uncompiled source draft.  The derivatives of the explicit inverse HG
cap and unchanged BT cap agree with the shared rational rate functions.
All denominators are positive on their actual physical domains.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree

namespace CrossedClampInverse

def cap1 (q b r : ℝ) : ℝ := -(D q b r+1)*D1 q b r/cap q b r

theorem cap_hasDerivAt {q b r : ℝ} (S : Domain q b) (hr : r∈Icc (0:ℝ) (1/25)) :
    HasDerivAt (cap q b) (cap1 q b r) r := by
  have hc := cap_bounds S hr
  have hr0 : q-(D q b r+1)^2≠0 := by nlinarith [hc.1,hc.2.2.2]
  have hd := ((((D_hasDerivAt S hr).add_const 1).pow 2).const_sub q).sqrt hr0
  convert hd using 1
  · rfl
  · dsimp [cap1,cap]
    field_simp [show Real.sqrt (q-(D q b r+1)^2)≠0 by
      change cap q b r≠0; linarith [hc.1]]

theorem cap_radius {q b r : ℝ} (S : Domain q b) (hr : r∈Icc (0:ℝ) (1/25)) :
    CrossedClampRates.radius q (cap q b r)=D q b r+1 := by
  dsimp [CrossedClampRates.radius]
  rw [show q-(cap q b r)^2=(D q b r+1)^2 by nlinarith [(cap_bounds S hr).2.2.2]]
  exact Real.sqrt_sq (by linarith [(D_bounds S hr).1])

theorem cap_transverse {q b r : ℝ} (S : Domain q b) (hr : r∈Icc (0:ℝ) (1/25)) :
    CrossedClampRates.transverse q (cap q b r)=D q b r := by
  dsimp [CrossedClampRates.transverse]
  rw [cap_radius S hr]
  ring

theorem cap_adjacent {q b r : ℝ} (S : Domain q b) (hr : r∈Icc (0:ℝ) (1/25)) :
    CrossedClampRates.adjacent q (cap q b r)=X q b r := by
  dsimp [CrossedClampRates.adjacent]
  rw [cap_transverse S hr]
  exact radius_eq S hr

theorem cap_rate {q b r : ℝ} (S : Domain q b) (hr : r∈Icc (0:ℝ) (1/25)) :
    cap1 q b r=CrossedClampRates.angularInverseRate q (cap q b r) r := by
  have hc : 0<Real.cos r := by linarith [(trig hr).2.2.2.1]
  have hw : 0<W q b r := by linarith [(W_bounds S hr).1.1]
  have hy : 0<cap q b r := by linarith [(cap_bounds S hr).1]
  have hden : X q b r-D q b r*(Real.sin r/Real.cos r)=W q b r/Real.cos r := by
    field_simp [hc.ne']
    nlinarith [reverse q b r]
  rw [CrossedClampRates.angularInverseRate,CrossedClampRates.inverseRate,
    cap_radius S hr,cap_transverse S hr,cap_adjacent S hr,Real.tan_eq_sin_div_cos,hden]
  dsimp [cap1,D1]
  rw [←reverse q b r]
  field_simp [hc.ne',hy.ne',show X q b r*Real.cos r-D q b r*Real.sin r≠0 by
    rw [reverse]; exact hw.ne']
  ring

theorem cap_angular_hasDerivAt {q b r : ℝ} (S : Domain q b)
    (hr : r∈Icc (0:ℝ) (1/25)) :
    HasDerivAt (cap q b) (CrossedClampRates.angularInverseRate q (cap q b r) r) r := by
  simpa only [cap_rate S hr] using cap_hasDerivAt S hr

theorem source_bound {q b r : ℝ} (S : Domain q b) (hr : r∈Icc (0:ℝ) (1/25)) :
    1/2+(1-CrossedClampRates.transverse q (cap q b r))*Real.cos r-
      (CrossedClampRates.adjacent q (cap q b r)-1)*Real.sin r=b := by
  rw [cap_transverse S hr,cap_adjacent S hr]
  have hh := contact q b r
  dsimp [M] at hh
  nlinarith

end CrossedClampInverse

namespace CrossedClampRates
open HardSplitCap

theorem hard_cap_radius {q d u : ℝ} (S : MiddleHardCap.Feasible q d)
    (hu : u∈Icc 0 frameCap) : radius q (cap q d u)=cornerX q d u := by
  dsimp [radius]
  rw [show q-(cap q d u)^2=(cornerX q d u)^2 by nlinarith [MiddleHardCap.corner_norm S hu]]
  exact Real.sqrt_sq (MiddleHardCap.cornerX_pos S hu).le

theorem hard_cap_rate {q d u : ℝ} (S : MiddleHardCap.Feasible q d)
    (hu : u∈Icc 0 frameCap) : first q d u= -angularHardRate q (cap q d u) u := by
  have hc : 0<Real.cos u := by linarith [(transport_trig hu).1]
  have hw := MiddleHardCap.root_pos S hu
  have hback : cap q d u*Real.cos u+cornerX q d u*Real.sin u=root q d u := by
    dsimp [cap,cornerX]
    linear_combination root q d u*Real.sin_sq_add_cos_sq u
  have hden : cap q d u+cornerX q d u*(Real.sin u/Real.cos u)=root q d u/Real.cos u := by
    field_simp [hc.ne']
    nlinarith
  rw [angularHardRate,hardRate,hard_cap_radius S hu,Real.tan_eq_sin_div_cos,hden]
  dsimp [first,drift]
  rw [←hback]
  field_simp [hc.ne',show cap q d u*Real.cos u+cornerX q d u*Real.sin u≠0 by
    rw [hback]; exact hw.ne']
  ring

theorem hard_cap_angular_hasDerivAt {q d u : ℝ} (S : MiddleHardCap.Feasible q d)
    (hu : u∈Icc 0 frameCap) :
    HasDerivAt (cap q d) (-angularHardRate q (cap q d u) u) u := by
  simpa only [hard_cap_rate S hu] using MiddleHardCap.cap_deriv S hu

theorem hard_cap_contact {q d u : ℝ} (S : MiddleHardCap.Feasible q d)
    (hu : u∈Icc 0 frameCap) :
    (radius q (cap q d u)-1)*Real.cos u-cap q d u*Real.sin u=d := by
  rw [hard_cap_radius S hu]
  exact corner_contact q d u

end CrossedClampRates
end SquaresInCircles.Eight.TableFree
