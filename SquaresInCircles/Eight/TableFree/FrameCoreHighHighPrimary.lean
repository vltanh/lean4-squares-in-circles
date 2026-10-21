module

public import SquaresInCircles.Eight.TableFree.FrameCoreHighCorner

/-!
# Every original high-source primary witness against a core state

The cancellation multiplier acts on the original weak margin and retains
the entire high circle.  The positive rounded-core branch uses the exact
radical cap forced by that same margin.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameCoreHighHighPrimary
open FramePair FrameCircleArc FrameHighArc FrameCoreArc FramePairCalculus
open FrameMidArc (b2 g K)
open FrameCoreHighGeometry
open FrameCoreHighPrimaryCurvature (gamma primaryFirst primaryFirst_lower)
open FrameCoreHighPrimaryContinuation (N X primarySecond)
open FrameCoreHighCorner (capK capY)

def CancellationSide (j : Bool) (a B : ℝ) : Prop :=
  j=false ∨ (a=7/12 ∧ B≤1/2)
def G (x : ℝ) : ℝ :=
  x-(9/50)*periodicFrameCost x-k+(-u+v+g/Real.sin x)/2-R*N x+
    (g/Real.sin x)*pairWidth x+(g/Real.sin x)*(7/12)*Real.cos x

theorem cancellation_target (j : Bool) {a B x : ℝ}
    (hc : CoreState a B) (hside : CancellationSide j a B)
    (hx : x∈Icc (3/4:ℝ) (5/2)) :
    (g/Real.sin x)*(7/12)*Real.cos x≤
      -sign j*coreLabel a B+(g/Real.sin x)*a*Real.cos x+
        (g/Real.sin x)*sign j*B*Real.sin x := by
  have hs := FrameCoreHighPrimaryContinuation.interval_sine hx
  have hs0 : 0<Real.sin x := by linarith
  have hλ0 : 0≤g/Real.sin x := div_nonneg (by norm_num [g]) hs0.le
  have hλU : g/Real.sin x<2 := (div_lt_iff₀ hs0).2 (by dsimp [g]; linarith)
  have hcλ := mul_le_mul_of_nonneg_left (Real.cos_le_one x) hλ0
  have hcan : (g/Real.sin x)*Real.sin x=g := div_mul_cancel₀ _ hs0.ne'
  cases j with
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

theorem cancellation_support (i j : Bool) {b a B x : ℝ}
    (hb : b∈Icc b2 c0) (hc : CoreState a B) (hside : CancellationSide j a B)
    (hx : x∈Icc (3/4:ℝ) (5/2)) (hm : 0≤highCorePrimary j b a B x) :
    G x≤highCoreCost i j b a B x := by
  have hs := FrameCoreHighPrimaryContinuation.interval_sine hx
  have hλ0 : 0≤g/Real.sin x := div_nonneg (by norm_num [g]) (by linarith)
  have hscaled := mul_nonneg hλ0 hm
  have hsource := circle_linear_lower (A_circle ⟨FrameMidArc.b2_mem.1.trans hb.1,hb.2⟩)
    (u-g/Real.sin x) (-v)
  have hn : Real.sqrt ((u-g/Real.sin x)^2+(-v)^2)=N x := by
    dsimp [N,X]
    congr 1
    ring
  rw [hn] at hsource
  have hsign := FrameHighArc.minus_label_le i hb
  have htarget := cancellation_target j hc hside hx
  dsimp [G,highCoreCost,highCorePrimary,H] at *
  nlinarith

theorem G_lower {x : ℝ} (hx : x∈Icc (3/4:ℝ) (5/2)) : gamma<G x := by
  have hs : Real.sin x≠0 := by linarith [FrameCoreHighPrimaryContinuation.interval_sine hx]
  by_cases hq : x≤Real.pi/2
  · have hw := first_width ⟨by linarith [hx.1],hq⟩
    have he : G x=primaryFirst x := by
      dsimp [G,primaryFirst,N,X]
      rw [hw.1,hw.2]
      field_simp [hs]
      ring
    rw [he]
    by_cases hshort : x≤3/2
    · exact primaryFirst_lower ⟨hx.1,hshort⟩
    · exact FrameCoreHighPrimaryContinuation.first_tail_lower ⟨(lt_of_not_ge hshort).le,hq⟩
  · have hxq : x∈Icc (Real.pi/2) Real.pi :=
      ⟨(lt_of_not_ge hq).le,by linarith [hx.2,FrameLowPair.pi_lower]⟩
    have hw := second_width hxq
    have he : G x=primarySecond x := by
      dsimp [G,primarySecond]
      rw [hw.1,hw.2]
      field_simp [hs]
      ring
    rw [he]
    exact FrameCoreHighPrimaryContinuation.second_lower ⟨hxq.1,hx.2⟩

theorem rounded_quadrant_false {b a B x : ℝ}
    (hb : b∈Icc b2 c0) (hc : CoreState a B) (hB : 1/2≤B)
    (hx : x∈Icc 0 (Real.pi/2)) (hm : 0≤highCorePrimary true b a B x) : False := by
  have hcore := core_bounds hc
  have hhigh := high_bounds hb
  have ht := FrameLowPair.quadrant hx
  have hA := mul_le_mul_of_nonneg_right
    (show (1/2:ℝ)≤a by linarith [hcore.1,CoreAngleEndpoint.diagonal_bounds.1]) ht.2.2.1
  have hB' := mul_le_mul_of_nonneg_right hB ht.1
  have hw := (first_width hx).1
  have hsc : 1≤Real.sin x+Real.cos x := by linarith [width_one_le x]
  dsimp [highCorePrimary,sign] at hm
  rw [hw] at hm
  nlinarith

theorem rounded_cap {b a B x : ℝ}
    (hc : CoreState a B) (hB : 1/2≤B) (hx : x∈Icc (Real.pi/2) Real.pi)
    (hm : 0≤highCorePrimary true b a B x) : capK x≤A b+1/2 := by
  have hcore := core_bounds hc
  have ht := second_signs hx
  have hA := mul_le_mul_of_nonpos_right hcore.2.1 ht.2
  have hB' := mul_le_mul_of_nonneg_right hB ht.1
  dsimp [highCorePrimary,sign] at hm
  rw [(second_width hx).1] at hm
  dsimp [capK,FrameCoreHighCorner.z]
  nlinarith

theorem rounded_cut {b a B x : ℝ}
    (hb : b∈Icc b2 c0) (hc : CoreState a B) (hB : 1/2≤B)
    (hx : x∈Icc (3/4:ℝ) (5/2)) (hm : 0≤highCorePrimary true b a B x) :
    (57/25:ℝ)<x := by
  by_contra! hsmall
  by_cases hfirst : x≤Real.pi/2
  · exact rounded_quadrant_false hb hc hB ⟨by linarith [hx.1],hfirst⟩ hm
  · have hxq : x∈Icc (Real.pi/2) Real.pi :=
      ⟨(lt_of_not_ge hfirst).le,by linarith [hx.2,FrameLowPair.pi_lower]⟩
    have hcap := rounded_cap hc hB hxq hm
    have hs := sin_endpoint_lower (by positivity : 0≤Real.pi/2)
      (by linarith [FrameLowPair.pi_lower] : (57/25:ℝ)≤Real.pi)
      (show x∈Icc (Real.pi/2) (57/25:ℝ) from ⟨hxq.1,hsmall⟩)
      (by simp : (379/500:ℝ)<Real.sin (Real.pi/2)) FrameCoreHighCorner.endpoint_trig.1
    have hcos := Real.cos_le_cos_of_nonneg_of_le_pi
      (by linarith [hx.1] : 0≤x) (by linarith [FrameLowPair.pi_lower]) hsmall
    have ha := (high_bounds hb).2.2.2
    dsimp [capK,FrameCoreHighCorner.z] at hcap
    linarith [FrameCoreHighCorner.endpoint_trig.2.2.1]

theorem rounded_tangent_cap {b a B x : ℝ}
    (hb : b∈Icc b2 c0) (hc : CoreState a B) (hB : 1/2≤B)
    (hx : x∈Icc (57/25:ℝ) (5/2)) (hm : 0≤highCorePrimary true b a B x) :
    b≤capY x-1/2 := by
  have hxq : x∈Icc (Real.pi/2) Real.pi :=
    ⟨by linarith [hx.1,Arithmetic.pi_hand_enclosure.2],
      by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have hcap := rounded_cap hc hB hxq hm
  have hz := FrameCoreHighCorner.domain hx
  have hy := FrameCoreHighCorner.capY_pos hx
  have hs := FrameCoreHighCorner.capY_sq hx
  have hcircle := A_circle ⟨FrameMidArc.b2_mem.1.trans hb.1,hb.2⟩
  have hK0 : 0≤capK x := by dsimp [capK]; linarith [hz.1]
  have hA := pow_le_pow_left₀ hK0 hcap 2
  have hbp : 0≤b+1/2 := by linarith [(high_bounds hb).1]
  nlinarith

theorem rounded_primary (i : Bool) {b a B x : ℝ}
    (hb : b∈Icc b2 c0) (hc : CoreState a B) (hB : 1/2≤B)
    (hx : x∈Icc (3/4:ℝ) (5/2)) (hm : 0≤highCorePrimary true b a B x) :
    gamma<highCoreCost i true b a B x := by
  have hcut := rounded_cut hb hc hB hx hm
  have hdom : x∈Icc (57/25:ℝ) (5/2) := ⟨hcut.le,hx.2⟩
  have hxq : x∈Icc (Real.pi/2) Real.pi :=
    ⟨by linarith [hcut,Arithmetic.pi_hand_enclosure.2],
      by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have hcapA := rounded_cap hc hB hxq hm
  have hcapB := rounded_tangent_cap hb hc hB hdom hm
  have hA := mul_le_mul_of_nonneg_left hcapA (show 0≤u by norm_num [u])
  have hB' := mul_le_mul_of_nonneg_left hcapB (show 0≤v by norm_num [v])
  have hsource := FrameHighArc.minus_label_le i hb
  have htarget := (label_bounds hc).2
  have hch := CorePairGeometry.charge_upper x
  have hscalar := FrameCoreHighCorner.J_lower hdom
  dsimp [highCoreCost,FrameCoreHighCorner.J,H,sign,gamma] at *
  nlinarith

theorem high_primary (i j : Bool) {b a B x : ℝ}
    (hb : b∈Icc b2 c0) (hc : CoreState a B)
    (hx : x∈Icc (-(203/250:ℝ)) (5/2))
    (hpositive : j=true → -(13/500:ℝ)≤x)
    (hm : 0≤highCorePrimary j b a B x) :
    (8833/10000:ℝ)<highCoreCost i j b a B x := by
  have hcut := high_primary_angle j hb hc hx.1 hpositive hm
  have hdom : x∈Icc (3/4:ℝ) (5/2) := ⟨hcut.le,hx.2⟩
  change gamma<highCoreCost i j b a B x
  cases j with
  | false => exact (G_lower hdom).trans_le (cancellation_support i false hb hc (Or.inl rfl) hdom hm)
  | true =>
      by_cases hB : B<1/2
      · have ha := (label_side hc hB).1
        exact (G_lower hdom).trans_le (cancellation_support i true hb hc (Or.inr ⟨ha,hB.le⟩) hdom hm)
      · exact rounded_primary i hb hc (le_of_not_gt hB) hdom hm

end SquaresInCircles.Eight.TableFree.FrameCoreHighHighPrimary
