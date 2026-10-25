module

public import SquaresInCircles.Eight.Owners.E.ZeroCapped
public import SquaresInCircles.Eight.Owners.Hard.SplitConstruction

/-!
# Eight squares: both E-zero endpoint cap sums are strictly below two

The circular-cap rotation identity transfers the
proved coupled scalar bound to the cap sum.  No comparison packing is
assumed to exist, and no numerical derivative estimate is required for
this strict version of the transfer.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.EZeroCapEndpoints
open EZeroFunctions EZeroCapped HardSplitCap

theorem feasible {t : ℝ} (ht : t∈Icc 0 (7/10 : ℝ)) :
    HardSplitCap.Feasible qCap (3/2-capped t) := by
  have hb := capped_bounds ht
  have hpos : 0≤5/2-capped t := by linarith
  have hupper : 5/2-capped t≤171/100 := by linarith
  have hsq := pow_le_pow_left₀ hpos hupper 2
  refine ⟨le_rfl,by linarith,?_⟩
  dsimp [qCap]
  nlinarith

theorem zero_cap (t : ℝ) : cap qCap (3/2-capped t) 0=W t := by
  simp [cap,root,contact,W]
  congr 2
  ring

theorem first_endpoint {e d : ℝ} (he : 0≤e) (hd : 0≤d) (ha : e+d≤7/10) :
    cap qCap (3/2-capped e) 0+cap qCap (3/2-capped d) (e+d)<2 := by
  by_contra! hbad
  have he' : e∈Icc 0 (7/10 : ℝ) := ⟨he,by linarith⟩
  have hd' : d∈Icc 0 (7/10 : ℝ) := ⟨hd,by linarith⟩
  have ha' : e+d∈Icc 0 (7/10 : ℝ) := ⟨by linarith,ha⟩
  let L := cap qCap (3/2-capped d) (e+d)
  let Z := cornerX qCap (3/2-capped d) (e+d)
  have hL : Yc e≤L := by
    rw [zero_cap] at hbad
    dsimp [Yc,L]
    linarith
  have hb := nested_bounds he'
  have hY : 0≤Yc e := by linarith [hb.2.2.1]
  have hYsq := pow_le_pow_left₀ hY hL 2
  have hnorm : Z^2+L^2=qCap := corner_norm (feasible hd') ha'
  have hcontact : (Z-1)*Real.cos (e+d)-L*Real.sin (e+d)=3/2-capped d :=
    corner_contact _ _ _
  have hZ : 0<Z := cornerX_pos (feasible hd') ha'
  have hcorner := corner_square he'
  have hX : Z≤Xc e+1 := by nlinarith [hb.2.2.2.2.1]
  obtain ⟨hc,hc1,hs,hs1,_⟩ := transport_trig ha'
  have hcos := mul_le_mul_of_nonneg_right hX (show 0≤Real.cos (e+d) by linarith)
  have hsin := mul_le_mul_of_nonneg_right hL hs
  have hF : (3/2 : ℝ)≤Fc e d := by
    dsimp [Fc]
    linarith
  linarith [EZeroCapped.maximum he hd ha]

theorem second_endpoint {e d : ℝ} (he : 0≤e) (hd : 0≤d) (ha : e+d≤7/10) :
    cap qCap (3/2-capped e) (e+d)+cap qCap (3/2-capped d) 0<2 := by
  have hh := first_endpoint hd he (by simpa [add_comm] using ha)
  simpa [add_comm] using hh

end SquaresInCircles.Eight.EZeroCapEndpoints
