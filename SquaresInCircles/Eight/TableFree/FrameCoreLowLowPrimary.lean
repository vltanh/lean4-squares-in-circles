module

public import SquaresInCircles.Eight.TableFree.FrameCoreLowLowScalars

/-!
# The complete original low-source primary witness

The short interval uses the actual core equation and one completed square.
The remaining straight-side and negative-tangent cases use cancellation
with the exact low endpoint.  A positive rounded-core target forces an
actual circle cap, whose scalar envelope is proved on its whole interval.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameCoreLowLowPrimary
open FramePair FrameCircleArc FrameLowArc FrameCoreArc FramePairCalculus
open FrameMidArc (g K)
open FrameCoreLowGeometry FrameCoreLowLowScalars

def CancellationSide (k : Bool) (a B : ℝ) : Prop :=
  k=false ∨ (a=7/12 ∧ B≤1/2)

theorem side_linear_lower {w B : ℝ} (hB : B∈Icc (0:ℝ) (1/2)) :
    min (w/2) (-w/2)≤w*B := by
  by_cases hw : 0≤w
  · have hp := mul_nonneg hw hB.1
    exact (min_le_right _ _).trans (by linarith)
  · have hh := mul_le_mul_of_nonpos_left hB.2 (le_of_not_ge hw)
    exact (min_le_left _ _).trans (by linarith)

theorem corner_quadratic {a B : ℝ} (hc : CoreState a B) (hB : 1/2≤B) :
    6*(B-1/2)^2≤7/12-a := by
  rcases hc with ⟨rfl,hb,hbu⟩ | ⟨hb,hab,hcircle⟩
  · have he : B=1/2 := by linarith
    rw [he]
    norm_num
  · have ha := CorePairGeometry.corner_geometry hb hab hcircle
    have hprod := mul_nonneg (show 0≤7/12-a by linarith [ha.2.1])
      (show 0≤7/12-a by linarith [ha.2.1])
    nlinarith

theorem short_target (k : Bool) {a B x : ℝ}
    (hc : CoreState a B) (hside : CancellationSide k a B)
    (hx : x∈Icc (3/10:ℝ) (3/5)) :
    3*(7/12)*Real.cos x+min ((g-3*Real.sin x)/2) (-(g-3*Real.sin x)/2)-1/200≤
      -sign k*coreLabel a B+3*a*Real.cos x+3*sign k*B*Real.sin x := by
  have hcore := core_bounds hc
  have ht := short_trig hx
  have hc1 := Real.cos_le_one x
  have hlow : g-9/5≤g-3*Real.sin x := by linarith [ht.2.1]
  cases k with
  | false =>
      by_cases hBside : B≤1/2
      · have ha : a=7/12 := by
          rcases hc with ⟨ha,_,_⟩ | ⟨hb,hab,hcircle⟩
          · exact ha
          · have he : B=1/2 := by linarith
            rw [he] at hcircle
            have hap : 1/2<a := by
              linarith [hcore.1,CoreAngleEndpoint.diagonal_bounds.1]
            nlinarith
        have hh := side_linear_lower (w := g-3*Real.sin x) ⟨hcore.2.2.1,hBside⟩
        dsimp [coreLabel,sign]
        rw [ha]
        nlinarith
      · have hB : 1/2≤B := (lt_of_not_ge hBside).le
        have hd : 0≤B-1/2 := sub_nonneg.mpr hB
        have he : 0≤7/12-a := sub_nonneg.mpr hcore.2.1
        have hquad := corner_quadratic hc hB
        have hcD : K-3≤K-3*Real.cos x := by linarith
        have heD := mul_le_mul_of_nonneg_right hcD he
        have hquadD := mul_le_mul_of_nonneg_left hquad (show 0≤K-3 by norm_num [K])
        have hwD := mul_le_mul_of_nonneg_right hlow hd
        have hsquare : -(1/200:ℝ)≤
            6*(K-3)*(B-1/2)^2+(g-9/5)*(B-1/2) := by
          have hs := sq_nonneg ((B-1/2)-(9/5-g)/(12*(K-3)))
          norm_num [K,g] at hs ⊢
          nlinarith
        have hm := min_le_left ((g-3*Real.sin x)/2) (-(g-3*Real.sin x)/2)
        dsimp [coreLabel,sign]
        nlinarith
  | true =>
      have ha : a=7/12 := by
        rcases hside with h | h
        · cases h
        · exact h.1
      have hB : B≤1/2 := by
        rcases hside with h | h
        · cases h
        · exact h.2
      have hh := side_linear_lower (w := -(g-3*Real.sin x)) ⟨hcore.2.2.1,hB⟩
      have hmin : min ((g-3*Real.sin x)/2) (-(g-3*Real.sin x)/2)=
          min (-(g-3*Real.sin x)/2) (-(-(g-3*Real.sin x))/2) := by
        rw [neg_neg,min_comm]
      rw [← hmin] at hh
      dsimp [coreLabel,sign]
      rw [ha]
      nlinarith

theorem short_source {b : ℝ} (hb : b∈Icc 0 b1) : sourceFloor< -L b-3*A b := by
  have hs := circle_linear_lower (A_circle ⟨hb.1,hb.2.trans b1_mem.2⟩) (-u-3) (-v)
  obtain ⟨N,hN⟩ : ∃ N, N=Real.sqrt ((-u-3)^2+(-v)^2) := ⟨_,rfl⟩
  rw [← hN] at hs
  have hroot : N<(1787/500:ℝ) := by
    rw [hN,Real.sqrt_lt' (by norm_num)]
    norm_num [u,v]
  have hN0 : 0≤N := hN ▸ Real.sqrt_nonneg _
  have hRN := mul_lt_mul' FrameCoreLowCorePrimary.radius_upper.le hroot hN0
    (by norm_num : (0:ℝ)<1979/1000)
  have hu : 0<u := by norm_num [u]
  have ha := mul_lt_mul_of_pos_left a0_bounds.1 hu
  dsimp [sourceFloor,L]
  linarith

theorem short_primary (i k : Bool) {b a B x : ℝ}
    (hb : b∈Icc 0 b1) (hc : CoreState a B) (hside : CancellationSide k a B)
    (hx : x∈Icc (3/10:ℝ) (3/5)) (hm : 0≤lowCorePrimary k b a B x) :
    (91/100:ℝ)<lowCoreCost i k b a B x := by
  have hsource := short_source hb
  have hsign := FrameLowPair.minus_label_le i hb
  have htarget := short_target k hc hside hx
  have hw := first_width
    (show x∈Icc 0 (Real.pi/2) from
      ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩)
  let base : ℝ := x-(9/50)*periodicFrameCost x+sourceFloor+
    3*pairWidth x+3*(7/12)*Real.cos x-1/200
  have he0 : base+(g-3*Real.sin x)/2=Hminus x := by
    dsimp [base,Hminus,shortConstant]
    rw [hw.1,hw.2]
    ring
  have he1 : base+(-(g-3*Real.sin x)/2)=Hplus x := by
    dsimp [base,Hplus,shortConstant]
    rw [hw.1,hw.2]
    ring
  have h0 := (short_lower hx).trans_le (min_le_left (Hminus x) (Hplus x))
  have h1 := (short_lower hx).trans_le (min_le_right (Hminus x) (Hplus x))
  have hmin : (91/100:ℝ)-base<
      min ((g-3*Real.sin x)/2) (-(g-3*Real.sin x)/2) := by
    apply lt_min <;> linarith
  dsimp [base,lowCoreCost,lowCorePrimary] at *
  nlinarith

theorem cancellation_target (k : Bool) {a B x : ℝ}
    (hc : CoreState a B) (hside : CancellationSide k a B)
    (hx : x∈Icc (3/5:ℝ) (41/20)) :
    (g/Real.sin x)*(7/12)*Real.cos x≤
      -sign k*coreLabel a B+(g/Real.sin x)*a*Real.cos x+
        (g/Real.sin x)*sign k*B*Real.sin x := by
  have hs := FrameCoreLowCancellation.interval_sine hx
  have hs0 : 0<Real.sin x := by linarith
  have hlam0 : 0≤g/Real.sin x := div_nonneg (by norm_num [g]) hs0.le
  have hlamU : g/Real.sin x<2 := (div_lt_iff₀ hs0).2 (by dsimp [g]; linarith)
  have hclam := mul_le_mul_of_nonneg_left (Real.cos_le_one x) hlam0
  have hcan : (g/Real.sin x)*Real.sin x=g := div_mul_cancel₀ _ hs0.ne'
  cases k with
  | false =>
      have ht := positive_support (r := -(g/Real.sin x)*Real.cos x)
        (z := (g/Real.sin x)*Real.sin x) hc
        (by dsimp [K]; nlinarith) (by rw [hcan])
      have hsg : sign false=-1 := rfl
      rw [hsg]
      linarith
  | true =>
      have ha : a=7/12 := by
        rcases hside with h | h
        · cases h
        · exact h.1
      subst a
      have hcB : (g/Real.sin x)*1*B*Real.sin x=g*B := by
        rw [mul_one,mul_right_comm,hcan]
      dsimp [coreLabel,sign]
      linarith

theorem cancellation_source_antitone {x : ℝ} (hx : x∈Icc (3/5:ℝ) (41/20)) :
    AntitoneOn (linear (-u-g/Real.sin x) (-v)) (Icc 0 b1) := by
  have hs := FrameCoreLowCancellation.interval_sine hx
  have hs0 : 0<Real.sin x := by linarith
  have hlam0 : 0≤g/Real.sin x := div_nonneg (by norm_num [g]) hs0.le
  have hlamU : g/Real.sin x<(1911/1000:ℝ) :=
    (div_lt_iff₀ hs0).2 (by dsimp [g]; linarith)
  apply antiOn_of_hasDeriv_nonpos
  · exact fun b hb => (linear_hasDerivAt ⟨hb.1,hb.2.trans b1_mem.2⟩ _
      _).continuousAt.continuousWithinAt
  · exact fun b hb => linear_hasDerivAt ⟨hb.1.le,hb.2.le.trans b1_mem.2⟩ _ _
  · intro b hb
    have hr := slope_bounds (Ioo_subset_Icc_self hb)
    have hm := mul_le_mul_of_nonneg_left hr.2.le
      (show 0≤u+g/Real.sin x by dsimp [u]; linarith)
    have hAd : Ad b=-FrameLowArc.slope b := by
      simp only [Ad,FrameLowArc.slope,neg_div]
    rw [hAd]
    dsimp only [u,v] at hm ⊢
    linarith

theorem cancellation_endpoint (i k : Bool) {b a B x : ℝ}
    (hb : b∈Icc 0 b1) (hc : CoreState a B) (hside : CancellationSide k a B)
    (hx : x∈Icc (3/5:ℝ) (41/20)) (hm : 0≤lowCorePrimary k b a B x) :
    FrameCoreLowCancellation.G x≤lowCoreCost i k b a B x := by
  have hs := FrameCoreLowCancellation.interval_sine hx
  have hlam0 : 0≤g/Real.sin x := div_nonneg (by norm_num [g]) (by linarith)
  have hscaled := mul_nonneg hlam0 hm
  have hsource := cancellation_source_antitone hx hb ⟨b1_mem.1,le_rfl⟩ hb.2
  dsimp [linear] at hsource
  rw [A_b1] at hsource
  have hsign := FrameLowPair.minus_label_le i hb
  have htarget := cancellation_target k hc hside hx
  dsimp [FrameCoreLowCancellation.G,FrameCoreMidScalars.ac,
    lowCoreCost,lowCorePrimary,L,L1] at *
  nlinarith

theorem cancellation_primary (i k : Bool) {b a B x : ℝ}
    (hb : b∈Icc 0 b1) (hc : CoreState a B) (hside : CancellationSide k a B)
    (hx : x∈Icc (3/10:ℝ) (41/20)) (hm : 0≤lowCorePrimary k b a B x) :
    (91/100:ℝ)<lowCoreCost i k b a B x := by
  by_cases hshort : x≤3/5
  · exact short_primary i k hb hc hside ⟨hx.1,hshort⟩ hm
  · have hdom : x∈Icc (3/5:ℝ) (41/20) := ⟨(lt_of_not_ge hshort).le,hx.2⟩
    exact (FrameCoreLowCancellation.G_lower hdom).trans_le
      (cancellation_endpoint i k hb hc hside hdom hm)

theorem rounded_primary_quadrant_false {b a B x : ℝ}
    (hb : b∈Icc 0 b1) (hc : CoreState a B) (hB : 1/2≤B)
    (hx : x∈Icc 0 (Real.pi/2)) (hm : 0≤lowCorePrimary true b a B x) : False := by
  have hcore := core_bounds hc
  have hlow := low_bounds hb
  have ht := FrameLowPair.quadrant hx
  have hA := mul_le_mul_of_nonneg_right
    (show (1/2:ℝ)≤a by linarith [hcore.1,CoreAngleEndpoint.diagonal_bounds.1]) ht.2.2.1
  have hB' := mul_le_mul_of_nonneg_right hB ht.1
  have hw := (first_width hx).1
  have hsc : 1≤Real.sin x+Real.cos x := by linarith [width_one_le x]
  dsimp [lowCorePrimary,sign] at hm
  rw [hw] at hm
  nlinarith

theorem rounded_primary_cap {b a B x : ℝ}
    (hc : CoreState a B) (hB : 1/2≤B) (hx : x∈Icc (Real.pi/2) Real.pi)
    (hm : 0≤lowCorePrimary true b a B x) : capK x≤A b+1/2 := by
  have hcore := core_bounds hc
  have ht := second_signs hx
  have hA := mul_le_mul_of_nonpos_right hcore.2.1 ht.2
  have hB' := mul_le_mul_of_nonneg_right hB ht.1
  dsimp [lowCorePrimary,sign] at hm
  rw [(second_width hx).1] at hm
  dsimp [capK]
  nlinarith

theorem rounded_primary_cut {b a B x : ℝ}
    (hb : b∈Icc 0 b1) (hc : CoreState a B) (hB : 1/2≤B)
    (hx : x∈Icc (3/10:ℝ) (41/20)) (hm : 0≤lowCorePrimary true b a B x) :
    (19/10:ℝ)<x := by
  by_contra! hsmall
  by_cases hfirst : x≤Real.pi/2
  · exact rounded_primary_quadrant_false hb hc hB ⟨by linarith [hx.1],hfirst⟩ hm
  · have hxq : x∈Icc (Real.pi/2) Real.pi :=
      ⟨(lt_of_not_ge hfirst).le,by linarith [hx.2,FrameLowPair.pi_lower]⟩
    have hcap := rounded_primary_cap hc hB hxq hm
    have hs := sin_endpoint_lower (by positivity : 0≤Real.pi/2)
      (by linarith [FrameLowPair.pi_lower] : (19/10:ℝ)≤Real.pi)
      (show x∈Icc (Real.pi/2) (19/10:ℝ) from ⟨hxq.1,hsmall⟩)
      (by rw [Real.sin_pi_div_two]; norm_num : (473/500:ℝ)<Real.sin (Real.pi/2))
      FrameCoreLowCorePrimary.trig_nineteen_tenths.1
    have hcos := Real.cos_le_cos_of_nonneg_of_le_pi
      (by linarith [hx.1] : 0≤x) (by linarith [FrameLowPair.pi_lower]) hsmall
    have ha := (A_low_bounds hb).2
    dsimp [capK] at hcap
    linarith [FrameCoreLowCorePrimary.trig_nineteen_tenths.2.2.1,a0_bounds.2]

theorem rounded_tangent_cap {b a B x : ℝ}
    (hb : b∈Icc 0 b1) (hc : CoreState a B) (hB : 1/2≤B)
    (hx : x∈Icc (19/10:ℝ) (41/20)) (hm : 0≤lowCorePrimary true b a B x) :
    b≤capB x := by
  have hxq : x∈Icc (Real.pi/2) Real.pi :=
    ⟨by linarith [hx.1,Arithmetic.pi_hand_enclosure.2],
      by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have hcap := rounded_primary_cap hc hB hxq hm
  have hk := capK_bounds hx
  have hy := capY_bounds hx
  have hs : (capY x)^2=Q0-(capK x)^2 := Real.sq_sqrt (cap_radicand_pos hx).le
  have hcircle := A_circle ⟨hb.1,hb.2.trans b1_mem.2⟩
  have hA := pow_le_pow_left₀ (show 0≤capK x by linarith [hk.1]) hcap 2
  have hbp : 0≤b+1/2 := by linarith [hb.1]
  dsimp [capB]
  nlinarith

theorem rounded_primary (i : Bool) {b a B x : ℝ}
    (hb : b∈Icc 0 b1) (hc : CoreState a B) (hB : 1/2≤B)
    (hx : x∈Icc (3/10:ℝ) (41/20)) (hm : 0≤lowCorePrimary true b a B x) :
    (91/100:ℝ)<lowCoreCost i true b a B x := by
  have hcut := rounded_primary_cut hb hc hB hx hm
  have hdom : x∈Icc (19/10:ℝ) (41/20) := ⟨hcut.le,hx.2⟩
  have hcap := rounded_tangent_cap hb hc hB hdom hm
  have hlabel := (low_label_linear hb).2
  have hscaled := mul_le_mul_of_nonneg_left hcap (show 0≤v by norm_num [v])
  have hsource := FrameLowPair.minus_label_le i hb
  have htarget := (label_bounds hc).2
  have hch := CorePairGeometry.charge_upper x
  have hscalar := J_lower hdom
  dsimp [lowCoreCost,J,sign] at *
  nlinarith

theorem low_primary (i k : Bool) {b a B x : ℝ}
    (hb : b∈Icc 0 b1) (hc : CoreState a B)
    (hx : x∈Icc (-(3/10:ℝ)) (41/20)) (hm : 0≤lowCorePrimary k b a B x) :
    (91/100:ℝ)<lowCoreCost i k b a B x := by
  have hcut := low_primary_angle k hb hc hx.1 hm
  have hdom : x∈Icc (3/10:ℝ) (41/20) := ⟨hcut.le,hx.2⟩
  cases k with
  | false => exact cancellation_primary i false hb hc (Or.inl rfl) hdom hm
  | true =>
      by_cases hB : B<1/2
      · have ha := (label_side hc hB).1
        exact cancellation_primary i true hb hc (Or.inr ⟨ha,hB.le⟩) hdom hm
      · exact rounded_primary i hb hc (le_of_not_gt hB) hdom hm

end SquaresInCircles.Eight.TableFree.FrameCoreLowLowPrimary
