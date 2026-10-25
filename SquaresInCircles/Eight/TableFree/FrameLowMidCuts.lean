module

public import SquaresInCircles.Eight.TableFree.FrameLowMidPrimaryScalars

/-!
# Coarse cuts forced by the original low/middle separators

Every strict cut is a consequence of a weak original margin.  The
primary cuts use a positive sinusoidal projection and its two endpoints
on a whole quadrant.  They do not assume a concentrated frame window.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameLowMidCuts
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc FramePairCalculus
open FrameLowMidGeometry

theorem harmonic_endpoint_lower {p q t x m : ℝ}
    (hp : 0≤p) (hq : 0≤q) (ht : t∈Icc 0 (Real.pi/2))
    (hx : x∈Icc 0 t) (h0 : m<p)
    (h1 : m<p*Real.cos t+q*Real.sin t) : m<p*Real.cos x+q*Real.sin x := by
  have hd (z : ℝ) : HasDerivAt (fun z => p*Real.cos z+q*Real.sin z)
      (-p*Real.sin z+q*Real.cos z) z :=
    (((Real.hasDerivAt_cos z).const_mul p).add
      ((Real.hasDerivAt_sin z).const_mul q)).congr_deriv (by ring)
  have he (z : ℝ) : HasDerivAt (fun z => -p*Real.sin z+q*Real.cos z)
      (-p*Real.cos z-q*Real.sin z) z :=
    (((Real.hasDerivAt_sin z).const_mul (-p)).add
      ((Real.hasDerivAt_cos z).const_mul q)).congr_deriv (by ring)
  have hc : ConcaveOn ℝ (Icc 0 t) (fun z => p*Real.cos z+q*Real.sin z) := by
    apply concave_of_deriv2 (f' := fun z => -p*Real.sin z+q*Real.cos z)
      (f'' := fun z => -p*Real.cos z-q*Real.sin z) (fun z _ => hd z) (fun z _ => he z)
    intro z hz
    have htrig := FrameLowPair.quadrant ⟨hz.1,hz.2.trans ht.2⟩
    have hpc := mul_nonneg hp htrig.2.2.1
    have hqs := mul_nonneg hq htrig.1
    linarith
  have h0' : m<p*Real.cos 0+q*Real.sin 0 := by simpa using h0
  exact concave_gt_of_endpoints (f := fun z => p*Real.cos z+q*Real.sin z) hc hx h0' h1

theorem low_mid_negative_cut {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b1 b2) (hx : 0≤x)
    (hm : 0≤primary false b B x) : (19/20:ℝ)<x := by
  by_contra! hsmall
  have hxq : x∈Icc 0 (Real.pi/2) := ⟨hx,by linarith [FrameLowPair.pi_lower]⟩
  have ht := FrameLowPair.quadrant hxq
  have ha := A_low_bounds hb
  have hA := A_mid_bounds hB
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi hx
    (by linarith [FrameLowPair.pi_lower] : (19/20:ℝ)≤Real.pi) hsmall
  have hce := cos_lower_six (show (0:ℝ)≤19/20 by norm_num)
  norm_num at hce
  have hco : (29/50:ℝ)<Real.cos x := by linarith
  have hAc := mul_le_mul_of_nonneg_right
    (show (1699/1000:ℝ)≤A B+1/2 by linarith [hA.1,a2_bounds.1]) ht.2.2.1
  have hBs := mul_le_mul_of_nonneg_right
    (show B-1/2≤7/500 by linarith [hB.2,FrameLowMidArc.b2_precise.2]) ht.1
  dsimp [primary] at hm
  rw [(first_width hxq).1] at hm
  norm_num [sign] at hm
  nlinarith [ha.2,a0_precise.2,ht.2.1]

theorem low_mid_positive_cut {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b1 b2) (hx : 0≤x)
    (hm : 0≤primary true b B x) : (3/2:ℝ)<x := by
  by_contra! hsmall
  have hxq : x∈Icc 0 (Real.pi/2) := ⟨hx,by linarith [FrameLowPair.pi_lower]⟩
  have ht := FrameLowPair.quadrant hxq
  have ha := A_low_bounds hb
  have hA := A_mid_bounds hB
  have hsE := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤3/2 by norm_num)
  have hcE := HighOrderTaylor.C14_le_cos (show (0:ℝ)≤3/2 by norm_num)
  norm_num [HighOrderTaylor.S11,HighOrderTaylor.C14,HighOrderTaylor.C12,
    Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at hsE hcE
  have hproject := harmonic_endpoint_lower (p := (1699/1000:ℝ)) (q := (4123/5000:ℝ))
    (m := (183/200:ℝ)) (by norm_num) (by norm_num)
    ⟨by norm_num,by linarith [FrameLowPair.pi_lower]⟩ ⟨hx,hsmall⟩
    (by norm_num) (by nlinarith)
  have hAc := mul_le_mul_of_nonneg_right
    (show (1699/1000:ℝ)≤A B+1/2 by linarith [hA.1,a2_bounds.1]) ht.2.2.1
  have hBs := mul_le_mul_of_nonneg_right
    (show (4123/5000:ℝ)≤B+1/2 by linarith [hB.1,FrameLowMidArc.b1_precise.1]) ht.1
  dsimp [primary] at hm
  rw [(first_width hxq).1] at hm
  norm_num [sign] at hm
  nlinarith [ha.2,a0_precise.2]

theorem mid_low_negative_cut {b B x : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc 0 b1) (hx : 0≤x)
    (hm : 0≤primary false b B x) : (11/10:ℝ)<x := by
  by_contra! hsmall
  have hxq : x∈Icc 0 (Real.pi/2) := ⟨hx,by linarith [FrameLowPair.pi_lower]⟩
  have ht := FrameLowPair.quadrant hxq
  have ha := A_mid_bounds hb
  have hA := A_low_bounds hB
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi hx
    (by linarith [FrameLowPair.pi_lower] : (11/10:ℝ)≤Real.pi) hsmall
  have hce := cos_lower_six (show (0:ℝ)≤11/10 by norm_num)
  norm_num at hce
  have hco : (9/20:ℝ)<Real.cos x := by linarith
  have hAc := mul_le_mul_of_nonneg_right
    (show (899/500:ℝ)≤A B+1/2 by linarith [hA.1,a1_precise.1]) ht.2.2.1
  have hBs := mul_nonpos_of_nonpos_of_nonneg
    (show B-1/2≤0 by linarith [hB.2,FrameLowMidArc.b1_precise.2]) ht.1
  dsimp [primary] at hm
  rw [(first_width hxq).1] at hm
  norm_num [sign] at hm
  nlinarith [ha.2,a1_precise.2]

theorem mid_low_positive_cut {b B x : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc 0 b1) (hx : 0≤x)
    (hm : 0≤primary true b B x) : (13/10:ℝ)<x := by
  by_contra! hsmall
  have hxq : x∈Icc 0 (Real.pi/2) := ⟨hx,by linarith [FrameLowPair.pi_lower]⟩
  have ht := FrameLowPair.quadrant hxq
  have ha := A_mid_bounds hb
  have hA := A_low_bounds hB
  have hsE := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤13/10 by norm_num)
  have hcE := HighOrderTaylor.C14_le_cos (show (0:ℝ)≤13/10 by norm_num)
  norm_num [HighOrderTaylor.S11,HighOrderTaylor.C14,HighOrderTaylor.C12,
    Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at hsE hcE
  have hproject := harmonic_endpoint_lower (p := (899/500:ℝ)) (q := (1/2:ℝ))
    (m := (799/1000:ℝ)) (by norm_num) (by norm_num)
    ⟨by norm_num,by linarith [FrameLowPair.pi_lower]⟩ ⟨hx,hsmall⟩
    (by norm_num) (by nlinarith)
  have hAc := mul_le_mul_of_nonneg_right
    (show (899/500:ℝ)≤A B+1/2 by linarith [hA.1,a1_precise.1]) ht.2.2.1
  have hBs := mul_nonneg hB.1 ht.1
  dsimp [primary] at hm
  rw [(first_width hxq).1] at hm
  norm_num [sign] at hm
  nlinarith [ha.2,a1_precise.2]

theorem mid_low_secondary_cut {b B x : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc 0 b1) (hx : 0≤x)
    (hm : 0≤ secondary true true b B x) : (2/5:ℝ)<x := by
  by_contra! hsmall
  have hxq : x∈Icc 0 (Real.pi/2) := ⟨hx,by linarith [FrameLowPair.pi_lower]⟩
  have ht := FrameLowPair.quadrant hxq
  have hA := A_low_bounds hB
  have hs := Real.sin_le hx
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  have hxx := pow_le_pow_left₀ hx hsmall 2
  have hAs := mul_le_mul_of_nonneg_right
    (show A B-1/2≤183/200 by linarith [hA.2,a0_precise.2]) ht.1
  have hBc := mul_nonneg hB.1 ht.2.2.1
  dsimp [secondary] at hm
  rw [(first_width hxq).1] at hm
  norm_num [sign] at hm
  linarith [hb.2,FrameLowMidArc.b2_precise.2]

end SquaresInCircles.Eight.TableFree.FrameLowMidCuts
