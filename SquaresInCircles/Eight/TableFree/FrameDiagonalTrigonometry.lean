module

public import SquaresInCircles.Eight.TableFree.FrameDiagonalCuts

/-!
# Continuous trigonometric cuts for the folded pair arcs

Each lower bound is propagated on its whole interval by concavity; each
difference bound is propagated by monotonicity.  Only the two genuine
endpoints of an interval are evaluated by rational Taylor inequalities.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameDiagonalTrigonometry
open FramePairCalculus

def harmonic (p q x : ℝ) : ℝ := p*Real.sin x+q*Real.cos x

theorem harmonic_deriv (p q x : ℝ) :
    HasDerivAt (harmonic p q) (p*Real.cos x-q*Real.sin x) x := by
  have h := ((Real.hasDerivAt_sin x).const_mul p).fun_add
    ((Real.hasDerivAt_cos x).const_mul q)
  rw [show p*Real.cos x-q*Real.sin x=p*Real.cos x+q*(-Real.sin x) by ring]
  exact h

theorem harmonic_second (p q x : ℝ) :
    HasDerivAt (fun z => p*Real.cos z-q*Real.sin z) (-harmonic p q x) x := by
  have h := ((Real.hasDerivAt_cos x).const_mul p).fun_sub
    ((Real.hasDerivAt_sin x).const_mul q)
  exact h.congr_deriv (by simp only [harmonic]; ring)

theorem harmonic_concave {p q l h : ℝ} (hp : 0≤p) (hq : 0≤q)
    (hl : 0≤l) (hh : h≤Real.pi/2) :
    ConcaveOn ℝ (Icc l h) (harmonic p q) := by
  apply concave_of_deriv2 (fun x _ => harmonic_deriv p q x)
    (fun x _ => harmonic_second p q x)
  intro x hx
  have ht := FrameLowPair.quadrant ⟨hl.trans hx.1,hx.2.trans hh⟩
  have hs := mul_nonneg hp ht.1
  have hc := mul_nonneg hq ht.2.2.1
  dsimp [harmonic]
  linarith

theorem harmonic_lower {p q l h x c : ℝ} (hp : 0≤p) (hq : 0≤q)
    (hl : 0≤l) (hh : h≤Real.pi/2) (hx : x∈Icc l h)
    (hleft : c<harmonic p q l) (hright : c<harmonic p q h) :
    c<harmonic p q x :=
  concave_gt_of_endpoints (harmonic_concave hp hq hl hh) hx hleft hright

theorem harmonic_taylor_lower {p q x c : ℝ} (hp : 0≤p) (hq : 0≤q)
    (hx : 0≤x) (hpoly : c<p*Arithmetic.sin7 x+q*Arithmetic.cos10 x) :
    c<harmonic p q x := by
  have ht := Arithmetic.trig_taylor_bounds hx
  have hs := mul_le_mul_of_nonneg_left ht.1 hp
  have hc := mul_le_mul_of_nonneg_left ht.2.2.1 hq
  dsimp [harmonic]
  linarith

theorem sine_monotone : MonotoneOn Real.sin (Icc 0 (Real.pi/2)) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun x _ => (Real.hasDerivAt_sin x).continuousAt.continuousWithinAt
  · exact fun x _ => Real.hasDerivAt_sin x
  · exact fun x hx => (FrameLowPair.quadrant (Ioo_subset_Icc_self hx)).2.2.1

theorem cosine_antitone : AntitoneOn Real.cos (Icc 0 (Real.pi/2)) := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun x _ => (Real.hasDerivAt_cos x).continuousAt.continuousWithinAt
  · exact fun x _ => Real.hasDerivAt_cos x
  · exact fun x hx => neg_nonpos.mpr
      (FrameLowPair.quadrant (Ioo_subset_Icc_self hx)).1

theorem difference_deriv (x : ℝ) :
    HasDerivAt (fun z => Real.sin z-Real.cos z) (Real.cos x+Real.sin x) x := by
  exact ((Real.hasDerivAt_sin x).fun_sub (Real.hasDerivAt_cos x)).congr_deriv (by ring)

theorem difference_monotone :
    MonotoneOn (fun x => Real.sin x-Real.cos x) (Icc 0 (Real.pi/2)) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun x _ => (difference_deriv x).continuousAt.continuousWithinAt
  · exact fun x _ => difference_deriv x
  · intro x hx
    have ht := FrameLowPair.quadrant (Ioo_subset_Icc_self hx)
    exact add_nonneg ht.2.2.1 ht.1

theorem rational_quadrant {x : ℝ} (hx : x∈Icc 0 (71/50:ℝ)) :
    x∈Icc 0 (Real.pi/2) :=
  ⟨hx.1,by linarith [hx.2,Arithmetic.pi_hand_enclosure.1]⟩

theorem sum_early {x : ℝ} (hx : x∈Icc (7/20:ℝ) (6/5)) :
    (32/25:ℝ)<Real.sin x+Real.cos x := by
  suffices (32/25:ℝ)<harmonic 1 1 x by simpa [harmonic] using this
  apply harmonic_lower (p := 1) (q := 1) (l := 7/20) (h := 6/5)
    (by norm_num) (by norm_num) (by norm_num)
    (by linarith [Arithmetic.pi_hand_enclosure.1]) hx
  all_goals apply harmonic_taylor_lower (by norm_num) (by norm_num) (by norm_num)
  all_goals norm_num [Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8]

theorem sum_middle {x : ℝ} (hx : x∈Icc (3/5:ℝ) (19/20)) :
    (69/50:ℝ)<Real.sin x+Real.cos x := by
  suffices (69/50:ℝ)<harmonic 1 1 x by simpa [harmonic] using this
  apply harmonic_lower (p := 1) (q := 1) (l := 3/5) (h := 19/20)
    (by norm_num) (by norm_num) (by norm_num)
    (by linarith [Arithmetic.pi_hand_enclosure.1]) hx
  all_goals apply harmonic_taylor_lower (by norm_num) (by norm_num) (by norm_num)
  all_goals norm_num [Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8]

theorem sum_high {x : ℝ} (hx : x∈Icc (1:ℝ) (13/10)) :
    (123/100:ℝ)<Real.sin x+Real.cos x := by
  suffices (123/100:ℝ)<harmonic 1 1 x by simpa [harmonic] using this
  apply harmonic_lower (p := 1) (q := 1) (l := 1) (h := 13/10)
    (by norm_num) (by norm_num) (by norm_num)
    (by linarith [Arithmetic.pi_hand_enclosure.1]) hx
  all_goals apply harmonic_taylor_lower (by norm_num) (by norm_num) (by norm_num)
  all_goals norm_num [Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8]

theorem sum_target_middle {x : ℝ} (hx : x∈Icc (11/10:ℝ) (71/50)) :
    (113/100:ℝ)<Real.sin x+Real.cos x := by
  suffices (113/100:ℝ)<harmonic 1 1 x by simpa [harmonic] using this
  apply harmonic_lower (p := 1) (q := 1) (l := 11/10) (h := 71/50)
    (by norm_num) (by norm_num) (by norm_num)
    (by linarith [Arithmetic.pi_hand_enclosure.1]) hx
  all_goals apply harmonic_taylor_lower (by norm_num) (by norm_num) (by norm_num)
  all_goals norm_num [Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8]

theorem sum_negative {x : ℝ} (hx : x∈Icc (9/10:ℝ) (6/5)) :
    (129/100:ℝ)<Real.sin x+Real.cos x := by
  suffices (129/100:ℝ)<harmonic 1 1 x by simpa [harmonic] using this
  apply harmonic_lower (p := 1) (q := 1) (l := 9/10) (h := 6/5)
    (by norm_num) (by norm_num) (by norm_num)
    (by linarith [Arithmetic.pi_hand_enclosure.1]) hx
  all_goals apply harmonic_taylor_lower (by norm_num) (by norm_num) (by norm_num)
  all_goals norm_num [Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8]

theorem weighted_negative {x : ℝ} (hx : x∈Icc (9/10:ℝ) (6/5)) :
    (23/20:ℝ)<(747/1000)*Real.sin x+(1253/1000)*Real.cos x := by
  change (23/20:ℝ)<harmonic (747/1000) (1253/1000) x
  apply harmonic_lower (p := 747/1000) (q := 1253/1000) (l := 9/10) (h := 6/5)
    (by norm_num) (by norm_num) (by norm_num)
    (by linarith [Arithmetic.pi_hand_enclosure.1]) hx
  all_goals apply harmonic_taylor_lower (by norm_num) (by norm_num) (by norm_num)
  all_goals norm_num [Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8]

theorem difference_061_negative {x : ℝ} (hx : x∈Icc 0 (61/100:ℝ)) :
    Real.sin x-Real.cos x<0 := by
  have hm := difference_monotone
    (rational_quadrant ⟨hx.1,by linarith [hx.2]⟩)
    (rational_quadrant (show (61/100:ℝ)∈Icc 0 (71/50) by norm_num)) hx.2
  have ht := Arithmetic.trig_taylor_bounds (show (0:ℝ)≤61/100 by norm_num)
  simp only at hm
  norm_num [Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at ht
  linarith [ht.2.1,ht.2.2.1]

theorem difference_080_upper {x : ℝ} (hx : x∈Icc 0 (4/5:ℝ)) :
    Real.sin x-Real.cos x<(21/1000:ℝ) := by
  have hm := difference_monotone
    (rational_quadrant ⟨hx.1,by linarith [hx.2]⟩)
    (rational_quadrant (show (4/5:ℝ)∈Icc 0 (71/50) by norm_num)) hx.2
  have ht := Arithmetic.trig_taylor_bounds (show (0:ℝ)≤4/5 by norm_num)
  simp only at hm
  norm_num [Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at ht
  linarith [ht.2.1,ht.2.2.1]

theorem difference_095_upper {x : ℝ} (hx : x∈Icc 0 (19/20:ℝ)) :
    Real.sin x-Real.cos x<(29/125:ℝ) := by
  have hm := difference_monotone
    (rational_quadrant ⟨hx.1,by linarith [hx.2]⟩)
    (rational_quadrant (show (19/20:ℝ)∈Icc 0 (71/50) by norm_num)) hx.2
  have ht := Arithmetic.trig_taylor_bounds (show (0:ℝ)≤19/20 by norm_num)
  simp only at hm
  norm_num [Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at ht
  linarith [ht.2.1,ht.2.2.1]

theorem difference_110_lower {x : ℝ} (hx : x∈Icc (11/10:ℝ) (71/50)) :
    (43/100:ℝ)<Real.sin x-Real.cos x := by
  have hm := difference_monotone
    (rational_quadrant (show (11/10:ℝ)∈Icc 0 (71/50) by norm_num))
    (rational_quadrant ⟨by linarith [hx.1],hx.2⟩) hx.1
  have ht := Arithmetic.trig_taylor_bounds (show (0:ℝ)≤11/10 by norm_num)
  norm_num [Arithmetic.sin7,Arithmetic.cos8] at ht
  linarith [ht.1,ht.2.2.2]

theorem difference_100_positive {x : ℝ} (hx : x∈Icc (1:ℝ) (13/10)) :
    0<Real.sin x-Real.cos x := by
  have hm := difference_monotone
    (rational_quadrant (show (1:ℝ)∈Icc 0 (71/50) by norm_num))
    (rational_quadrant ⟨by linarith [hx.1],by linarith [hx.2]⟩) hx.1
  have ht := Arithmetic.trig_taylor_bounds (show (0:ℝ)≤1 by norm_num)
  norm_num [Arithmetic.sin7,Arithmetic.cos8] at ht
  linarith [ht.1,ht.2.2.2]

end SquaresInCircles.Eight.TableFree.FrameDiagonalTrigonometry
