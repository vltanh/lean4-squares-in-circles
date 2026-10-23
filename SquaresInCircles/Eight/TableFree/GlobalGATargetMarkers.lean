module

public import SquaresInCircles.Eight.TableFree.GlobalBTMarkers
public import SquaresInCircles.Eight.TableFree.GlobalEHPath

/-!
# The stronger original outer marker floor for the high-GA target cut

Uncompiled transcription of Section 2 of
`HAND_G3_HIGH_GA_TARGET_HAS_SMALL_TANGENT.md`.
The three original charts keep their actual markers, including both
choices at either junction. The low arc uses its whole-arc derivative,
the middle arc its two intrinsic endpoints, and the high arc the
displayed positive shifted-circle square reserve.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.Target
open FramePair ZeroPrimary FrameCircleArc FrameLowArc FrameMidArc
open GlobalZeroSign

def m : ℝ := 8669/10000

lemma low_marker {b : ℝ} (hb : b∈Icc 0 b1) : m*b≤L b := by
  have hmono : MonotoneOn (fun z => L z-m*z) (Icc 0 b1) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun z hz => ((L_hasDerivAt hz).sub ((hasDerivAt_id z).const_mul m)).
        continuousAt.continuousWithinAt)
      (fun z hz => (L_hasDerivAt (Ioo_subset_Icc_self hz)).sub ((hasDerivAt_id z).const_mul m))
    intro z hz
    have hr := (slope_bounds (Ioo_subset_Icc_self hz)).2
    dsimp [Ld,FrameLowArc.u,FrameLowArc.v,m]
    linarith
  have hh := hmono ⟨le_rfl,b1_mem.1⟩ hb hb.1
  simpa only [L_zero,mul_zero,sub_zero,sub_nonneg] using hh

lemma middle_marker {b : ℝ} (hb : b∈Icc b1 b2) : m*b≤M b := by
  have he := linear_endpoint_lower (p:=p) (q:=q-m) (by norm_num [p]) b1_mem.1 b2_mem.2 hb
  have hleft : -cM<linear p (q-m) b1 := by
    rw [linear,A_b1]
    dsimp [p,q,m,cM,b1]
    linarith [a1_bounds.1]
  have hright : -cM<linear p (q-m) b2 := by
    rw [linear,A_b2]
    dsimp [p,q,m,cM,b2]
    linarith [a2_bounds.1]
  have hh := (lt_min hleft hright).trans_le he
  dsimp [linear,M] at hh ⊢
  linarith

lemma high_square_reserve :
    ((314159/100000:ℝ)/4+(89293/500000)*(449607/500000)+
      (FrameHighArc.u+(m-FrameHighArc.v))/2)^2-
        Q0*(FrameHighArc.u^2+(m-FrameHighArc.v)^2)=
      6545897824987888201/62500000000000000000000 := by
  norm_num [FrameHighArc.u,FrameHighArc.v,m,Q0]

lemma high_support_reserve :
    CommonQuarter.radius*Real.sqrt (FrameHighArc.u^2+(m-FrameHighArc.v)^2)-
      (FrameHighArc.u+(m-FrameHighArc.v))/2<FrameHighArc.k := by
  let n : ℝ := Real.sqrt (FrameHighArc.u^2+(m-FrameHighArc.v)^2)
  let l : ℝ := (314159/100000:ℝ)/4+(89293/500000)*(449607/500000)+
    (FrameHighArc.u+(m-FrameHighArc.v))/2
  have hn : n^2=FrameHighArc.u^2+(m-FrameHighArc.v)^2 := Real.sq_sqrt (by positivity)
  have hprod : (CommonQuarter.radius*n)^2=Q0*(FrameHighArc.u^2+(m-FrameHighArc.v)^2) := by
    rw [mul_pow,CommonQuarter.radius_sq,hn]
  have hl : 0<l := by norm_num [l,FrameHighArc.u,FrameHighArc.v,m]
  have hreserve := high_square_reserve
  change l^2-Q0*(FrameHighArc.u^2+(m-FrameHighArc.v)^2)=_ at hreserve
  have hroot : CommonQuarter.radius*n<l := by nlinarith
  have hpi := Arithmetic.pi_hand_enclosure.1
  have hc := FrameHighArc.diagonal_bounds.1
  change CommonQuarter.radius*n-(FrameHighArc.u+(m-FrameHighArc.v))/2<FrameHighArc.k
  dsimp [l,FrameHighArc.k,FrameHighArc.u,FrameHighArc.v,m] at *
  linarith

theorem marker_floor (s : State) (hs : s.branch.type≠0) : m*s.b≤unsigned s := by
  cases hj : s.branch with
  | coreSide | coreCorner => simp [hj,Branch.type] at hs
  | low =>
      have hc := state_low_chart s hj
      simpa [unsigned,hj,label,L,FrameLowArc.u,FrameLowArc.v,←hc.1] using low_marker hc.2
  | middle =>
      have hc := state_mid_chart s hj
      simpa [unsigned,hj,label,M,p,q,cM,←hc.1] using middle_marker hc.2
  | high =>
      have hp := state_support s FrameHighArc.u (m-FrameHighArc.v)
      have hr := high_support_reserve
      dsimp [unsigned]
      rw [hj]
      dsimp [label,FrameHighArc.k,FrameHighArc.u,FrameHighArc.v,m] at *
      linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.Target
