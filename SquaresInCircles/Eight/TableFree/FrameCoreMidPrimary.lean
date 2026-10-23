module

public import SquaresInCircles.Eight.TableFree.FrameCoreMidTransverse

/-!
# Both orientations of the original core/middle primary axis

The contact estimate cancels the actual core tangent.  Its circle
support is followed by a whole-arc endpoint support.  A positive rounded
core target is handled directly from its original separating inequality.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameCoreMidPrimary
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameCoreArc
open FramePairCalculus FrameCoreMidScalars FrameCoreMidGeometry

theorem core_primary (i k : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc b1 b2)
    (hx : x∈Icc (-(54/125:ℝ)) (109/50))
    (hm : 0≤coreMidPrimary k a B x) :
    (1801/2000:ℝ)<coreMidCost i k a b B x := by
  have hcut := core_primary_cut k hc hB hx.1 hm
  cases k with
  | false =>
      have hs := (FrameCoreArc.signed_label_bounds i hc).1
      have ht := (M_bounds hB).1
      have hch := CorePairGeometry.charge_upper x
      dsimp [coreMidCost,sign]
      linarith [M_endpoints.1]
  | true => exact False.elim (core_primary_positive_false hc hB ⟨hcut.le,hx.2⟩ hm)

/-- This is the geometric case distinction on the original target:
its sign is negative, or its point is on the straight core side. -/
def CancellationSide (k : Bool) (a B : ℝ) : Prop :=
  k=false ∨ (a=7/12 ∧ B≤1/2)

theorem cancellation_sine {x : ℝ} (hx : x∈Icc (3/5:ℝ) (97/50)) :
    (14/25:ℝ)<Real.sin x := by
  apply sin_endpoint_lower (by norm_num : (0:ℝ)≤3/5)
    (by linarith [FrameLowPair.pi_lower] : (97/50:ℝ)≤Real.pi) hx
  · have hh := Real.sin_ge_sub_cube (show (0:ℝ)≤3/5 by norm_num)
    norm_num at hh
    linarith
  · linarith [trig_primary_cut.1]

theorem cancellation_target (k : Bool) {a B x : ℝ}
    (hc : CoreState a B) (hside : CancellationSide k a B)
    (hx : x∈Icc (3/5:ℝ) (97/50)) :
    (g/Real.sin x)*(7/12)*Real.cos x≤
      -sign k*coreLabel a B+(g/Real.sin x)*a*Real.cos x+
        (g/Real.sin x)*sign k*B*Real.sin x := by
  have hs := cancellation_sine hx
  have hs0 : 0<Real.sin x := by linarith
  have hλ0 : 0≤g/Real.sin x := div_nonneg (by norm_num [g]) hs0.le
  have hλU : g/Real.sin x<2 := (div_lt_iff₀ hs0).2 (by dsimp [g]; linarith)
  have hcλ := mul_le_mul_of_nonneg_left (Real.cos_le_one x) hλ0
  have hcan : (g/Real.sin x)*Real.sin x=g := div_mul_cancel₀ _ hs0.ne'
  cases k with
  | false =>
      have ht := positive_support (r := -(g/Real.sin x)*Real.cos x)
        (z := (g/Real.sin x)*Real.sin x) hc
        (by dsimp [K]; nlinarith) (by rw [hcan])
      simp only [sign,ite_false] at *
      nlinarith
  | true =>
      have ha : a=7/12 := by
        rcases hside with h | h
        · cases h
        · exact h.1
      subst a
      dsimp [coreLabel,sign]
      nlinarith

theorem cancellation_target_tail (k : Bool) {a B : ℝ}
    (hc : CoreState a B) (hside : CancellationSide k a B) :
    -(g/2)≤ -sign k*coreLabel a B := by
  cases k with
  | false =>
      have hh := (label_bounds hc).1
      simp only [sign,ite_false]
      dsimp [g]
      linarith
  | true =>
      have hh : a=7/12 ∧ B≤1/2 := by
        rcases hside with h | h
        · cases h
        · exact h
      dsimp [sign,coreLabel]
      rw [hh.1]
      have hb := mul_le_mul_of_nonneg_left hh.2 (show (0:ℝ)≤g by norm_num [g])
      nlinarith

theorem cancellation_circle_support (i k : Bool) {b a B x : ℝ}
    (hb : b∈Icc b1 b2) (hc : CoreState a B)
    (hside : CancellationSide k a B) (hx : x∈Icc (3/5:ℝ) (6/5))
    (hm : 0≤midCorePrimary k b a B x) :
    FrameCoreMidContact.scalar x≤midCoreCost i k b a B x := by
  have hdom : x∈Icc (3/5:ℝ) (97/50) := ⟨hx.1,by linarith [hx.2]⟩
  have hs0 : 0<Real.sin x := by linarith [cancellation_sine hdom]
  have hλ0 : 0≤g/Real.sin x := div_nonneg (by norm_num [g]) hs0.le
  have hscaled := mul_nonneg hλ0 hm
  have hsource := middle_minus_label i hb
  have htarget := cancellation_target k hc hside hdom
  have hcircle := circle_linear_lower
    (A_circle ⟨b1_mem.1.trans hb.1,hb.2.trans b2_mem.2⟩)
    (-p-g/Real.sin x) (-q)
  have hn : Real.sqrt ((-p-g/Real.sin x)^2+(-q)^2)=
      FrameCoreMidContact.N (1/Real.sin x) := by
    unfold FrameCoreMidContact.N
    congr 1
    ring
  rw [hn] at hcircle
  have hcan : (g/Real.sin x)*Real.sin x=g := div_mul_cancel₀ _ hs0.ne'
  have hxq : x∈Icc 0 (Real.pi/2) :=
    ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have hw := first_width hxq
  have he : (13*g/12)*(Real.cos x/Real.sin x)=
      (13/12)*(g/Real.sin x)*Real.cos x := by ring
  dsimp [midCorePrimary] at hscaled
  rw [hw.1] at hscaled
  dsimp [midCoreCost,FrameCoreMidContact.scalar,M]
  rw [hw.2,he]
  dsimp [M] at hsource
  nlinarith

theorem cancellation_source_antitone {x : ℝ}
    (hx : x∈Icc (6/5:ℝ) (97/50)) :
    AntitoneOn (linear (-p-g/Real.sin x) (-q)) (Icc b1 b2) := by
  have hs := FrameCoreMidPrimaryContinuation.interval_sine hx
  have hs0 : 0<Real.sin x := by linarith
  have hλ0 : 0≤g/Real.sin x := div_nonneg (by norm_num [g]) hs0.le
  have hλU : g/Real.sin x<g/(233/250) := by
    apply (div_lt_iff₀ hs0).2
    dsimp [g] at *
    nlinarith
  have hp : 0≤p+g/Real.sin x := by dsimp [p]; linarith
  apply antiOn_of_hasDeriv_nonpos
  · intro b hb
    exact (linear_hasDerivAt ⟨b1_mem.1.trans hb.1,hb.2.trans b2_mem.2⟩ _ _).
      continuousAt.continuousWithinAt
  · intro b hb
    exact linear_hasDerivAt ⟨b1_mem.1.trans hb.1.le,hb.2.le.trans b2_mem.2⟩ _ _
  · intro b hb
    have hr := slope_mid_bounds (Ioo_subset_Icc_self hb)
    have hh := mul_le_mul_of_nonneg_left hr.2.le hp
    dsimp [Ad,slope,p,q,g] at *
    nlinarith

theorem cancellation_endpoint_support (i k : Bool) {b a B x : ℝ}
    (hb : b∈Icc b1 b2) (hc : CoreState a B)
    (hside : CancellationSide k a B) (hx : x∈Icc (6/5:ℝ) (97/50))
    (hm : 0≤midCorePrimary k b a B x) :
    FrameCoreMidPrimaryContinuation.G x≤midCoreCost i k b a B x := by
  have hdom : x∈Icc (3/5:ℝ) (97/50) := ⟨by linarith [hx.1],hx.2⟩
  have hs0 : 0<Real.sin x := by linarith [cancellation_sine hdom]
  have hscaled := mul_nonneg
    (div_nonneg (show (0:ℝ)≤g by norm_num [g]) hs0.le) hm
  have hsource := middle_minus_label i hb
  have htarget := cancellation_target k hc hside hdom
  have hend := cancellation_source_antitone hx hb ⟨b1_lt_b2.le,le_rfl⟩ hb.2
  dsimp [linear] at hend
  rw [A_b2] at hend
  dsimp [FrameCoreMidPrimaryContinuation.G,midCoreCost,midCorePrimary,M,M2,ac] at *
  nlinarith

theorem cancellation_large (i k : Bool) {b a B x : ℝ}
    (hb : b∈Icc b1 b2) (hc : CoreState a B)
    (hside : CancellationSide k a B) (hx : (97/50:ℝ)≤x) :
    (1801/2000:ℝ)<midCoreCost i k b a B x := by
  have hsource := (signed_middle_bounds i hb).1
  have htarget := cancellation_target_tail k hc hside
  have hch := CorePairGeometry.charge_upper x
  dsimp [midCoreCost,g] at *
  linarith [M_endpoints.2.2.2]

theorem cancellation_primary (i k : Bool) {b a B x : ℝ}
    (hb : b∈Icc b1 b2) (hc : CoreState a B)
    (hside : CancellationSide k a B) (hx : (3/5:ℝ)≤x)
    (hm : 0≤midCorePrimary k b a B x) :
    (1801/2000:ℝ)<midCoreCost i k b a B x := by
  by_cases hlarge : (97/50:ℝ)≤x
  · exact cancellation_large i k hb hc hside hlarge
  · by_cases hsmall : x≤6/5
    · have hdom : x∈Icc (3/5:ℝ) (6/5) := ⟨hx,hsmall⟩
      exact (lt_trans (by norm_num) (FrameCoreMidContact.scalar_lower hdom)).trans_le
        (cancellation_circle_support i k hb hc hside hdom hm)
    · have hdom : x∈Icc (6/5:ℝ) (97/50) :=
        ⟨(lt_of_not_ge hsmall).le,(lt_of_not_ge hlarge).le⟩
      exact (lt_trans (by norm_num) (FrameCoreMidPrimaryContinuation.G_lower hdom)).trans_le
        (cancellation_endpoint_support i k hb hc hside hdom hm)

theorem rounded_primary_quadrant_false {b a B x : ℝ}
    (hb : b∈Icc b1 b2) (hc : CoreState a B) (hB : 1/2≤B)
    (hx : x∈Icc 0 (Real.pi/2)) (hm : 0≤midCorePrimary true b a B x) : False := by
  have hcore := core_bounds hc
  have hmid := middle_bounds hb
  have ht := FrameLowPair.quadrant hx
  have hA := mul_le_mul_of_nonneg_right
    (show (1/2:ℝ)≤a by linarith [hcore.1,CoreAngleEndpoint.diagonal_bounds.1]) ht.2.2.1
  have hB' := mul_le_mul_of_nonneg_right hB ht.1
  have hw := (first_width hx).1
  have hsc : 1≤Real.sin x+Real.cos x := by linarith [width_one_le x]
  dsimp [midCorePrimary,sign] at hm
  rw [hw] at hm
  nlinarith

theorem rounded_primary_cap {b a B x : ℝ}
    (hc : CoreState a B) (hB : 1/2≤B)
    (hx : x∈Icc (Real.pi/2) Real.pi)
    (hm : 0≤midCorePrimary true b a B x) :
    1/2+Real.sin x+(1/12)*Real.cos x≤A b := by
  have hcore := core_bounds hc
  have ht := second_signs hx
  have hA := mul_le_mul_of_nonpos_right hcore.2.1 ht.2
  have hB' := mul_le_mul_of_nonneg_right hB ht.1
  dsimp [midCorePrimary,sign] at hm
  rw [(second_width hx).1] at hm
  nlinarith

theorem rounded_primary_cut {b a B x : ℝ}
    (hb : b∈Icc b1 b2) (hc : CoreState a B) (hB : 1/2≤B)
    (hx : x∈Icc (3/5:ℝ) (109/50))
    (hm : 0≤midCorePrimary true b a B x) : (213/100:ℝ)<x := by
  by_contra! hsmall
  by_cases hfirst : x≤Real.pi/2
  · exact rounded_primary_quadrant_false hb hc hB ⟨by linarith [hx.1],hfirst⟩ hm
  · have hxq : x∈Icc (Real.pi/2) Real.pi :=
      ⟨(lt_of_not_ge hfirst).le,by linarith [hx.2,FrameLowPair.pi_lower]⟩
    have hcap := rounded_primary_cap hc hB hxq hm
    have hs := sin_endpoint_lower (by positivity : (0:ℝ)≤Real.pi/2)
      (by linarith [FrameLowPair.pi_lower] : (213/100:ℝ)≤Real.pi)
      (show x∈Icc (Real.pi/2) (213/100:ℝ) from ⟨hxq.1,hsmall⟩)
      (by norm_num : (847/1000:ℝ)<Real.sin (Real.pi/2)) trig_corner_cut.1
    have hcos := Real.cos_le_cos_of_nonneg_of_le_pi
      (by linarith [hx.1] : 0≤x) (by linarith [FrameLowPair.pi_lower]) hsmall
    have ha := (A_mid_bounds hb).2
    linarith [trig_corner_cut.2,a1_precise.2]

theorem rounded_primary_marker {b a B x : ℝ}
    (hb : b∈Icc b1 b2) (hc : CoreState a B) (hB : 1/2≤B)
    (hx : x∈Icc (213/100:ℝ) (109/50))
    (hm : 0≤midCorePrimary true b a B x) : M b<(197/500:ℝ) := by
  have hxq : x∈Icc (Real.pi/2) Real.pi :=
    ⟨by linarith [hx.1,Arithmetic.pi_hand_enclosure.2],
      by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have hcap := rounded_primary_cap hc hB hxq hm
  have hs := (high_angle_trig ⟨by linarith [hx.1],hx.2⟩).1
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi
    (by linarith [hx.1] : 0≤x) (by linarith [FrameLowPair.pi_lower]) hx.2
  have haL : (5089/4000:ℝ)<A b := by linarith [trig_last.2]
  have hcircle := A_circle ⟨b1_mem.1.trans hb.1,hb.2.trans b2_mem.2⟩
  have hb0 := b1_mem.1.trans hb.1
  have hbU : b<(381/1000:ℝ) := by
    by_contra! hbad
    have ha2 := pow_le_pow_left₀ (show (0:ℝ)≤5089/4000+1/2 by norm_num)
      (show (5089/4000:ℝ)+1/2≤A b+1/2 by linarith) 2
    have hb2 := pow_le_pow_left₀ (show (0:ℝ)≤381/1000+1/2 by norm_num)
      (show (381/1000:ℝ)+1/2≤b+1/2 by linarith) 2
    norm_num [Q0] at hcircle
    nlinarith
  have haU := (A_mid_bounds hb).2.trans a1_precise.2.le
  dsimp [M,p,q,cM]
  linarith

theorem rounded_primary (i : Bool) {b a B x : ℝ}
    (hb : b∈Icc b1 b2) (hc : CoreState a B) (hB : 1/2≤B)
    (hx : x∈Icc (3/5:ℝ) (109/50))
    (hm : 0≤midCorePrimary true b a B x) :
    (1801/2000:ℝ)<midCoreCost i true b a B x := by
  have hcut := rounded_primary_cut hb hc hB hx hm
  have hmark := rounded_primary_marker hb hc hB ⟨hcut.le,hx.2⟩ hm
  have hsource := middle_minus_label i hb
  have htarget := (label_bounds hc).2
  have hch := CorePairGeometry.charge_upper x
  dsimp [midCoreCost,sign]
  linarith

theorem middle_primary (i k : Bool) {b a B x : ℝ}
    (hb : b∈Icc b1 b2) (hc : CoreState a B)
    (hx : x∈Icc (-(54/125:ℝ)) (109/50))
    (hm : 0≤midCorePrimary k b a B x) :
    (1801/2000:ℝ)<midCoreCost i k b a B x := by
  have hcut := middle_primary_cut k hb hc hx.1 hm
  cases k with
  | false => exact cancellation_primary i false hb hc (Or.inl rfl) hcut.le hm
  | true =>
      by_cases hB : B<1/2
      · have hside : CancellationSide true a B := Or.inr ⟨(label_side hc hB).1,hB.le⟩
        exact cancellation_primary i true hb hc hside hcut.le hm
      · exact rounded_primary i hb hc (le_of_not_gt hB) ⟨hcut.le,hx.2⟩ hm

end SquaresInCircles.Eight.TableFree.FrameCoreMidPrimary
