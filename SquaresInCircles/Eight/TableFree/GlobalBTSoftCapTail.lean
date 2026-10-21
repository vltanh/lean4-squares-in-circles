module

public import SquaresInCircles.Eight.TableFree.GlobalBTSoftCapTransport

/-!
# Both complete original tails after the positive-AB2 soft prefix

The original AB2 and BT1 contacts directly pay the transported T
force.  The unchanged D circle and E marker give the two already
closed continuous tail scalar families for either original TD owner.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalBT.SoftCap

open FramePair FrameCircleArc GlobalOuterAnchor GlobalZeroSign

theorem ordinary_support (a b t d e : State) (second : Bool)
    {c eWeight margin v z s u : ℝ}
    (ha : 0≤transverse a) (ht : 0≤transverse t)
    (hd : transverse d≤0) (he : transverse e≤0)
    (hc : (3/5:ℝ)≤c) (hv : v∈Icc 0 frameCap) (hz : z∈Icc 0 frameCap)
    (hs : s∈Icc 0 frameCap) (hu : u∈Icc 0 frameCap)
    (hAB : width v≤projection false a b v 2)
    (hBT : width (-z)≤projection true b t (-z) 1)
    (hmarker : margin+eWeight*e.b≤ZeroPrimary.unsigned e) :
    de2Tail second eWeight margin c 0 s u≤
      Real.pi+v-z+kappa*a.b+zeroDual second t d (-s) c+
        quarterDual d e 2 (-u) eWeight+ZeroPrimary.unsigned e := by
  have hty := transverse_of_nonneg t ht
  have hdy := transverse_nonpos_eq d hd
  have hey := transverse_nonpos_eq e he
  cases second with
  | false =>
      have hT := transported_prefix a b t ha hv hz hc
        (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hAB hBT
      have hD := mixed_state_support d eWeight c u s
      rw [add_comm u s] at hD
      simp only [Real.sin_zero,Real.cos_zero,mul_zero,mul_one,sub_zero,add_zero] at hT
      dsimp [de2Tail,quarterDual,zeroDual,leftOwner,projection]
      rw [width_negative hs,width_negative hu,hty,hdy,hey]
      simp only [Real.cos_neg,Real.sin_neg,Real.cos_zero,Real.sin_zero,
        mul_one,mul_zero,add_zero,zero_add,sub_zero]
      nlinarith only [hT,hD,hmarker]
  | true =>
      have hT := transported_prefix a b t ha hv hz hc hs hAB hBT
      have hD := mixed_state_support d eWeight c u 0
      simp only [Real.sin_zero,Real.cos_zero,mul_zero,mul_one,sub_zero,add_zero] at hD
      dsimp [de2Tail,quarterDual,zeroDual,leftOwner,projection]
      rw [width_negative hs,width_negative hu,hty,hdy,hey]
      simp only [Real.cos_neg,Real.sin_neg,Real.cos_zero,Real.sin_zero,
        mul_one,mul_zero,add_zero,zero_add,sub_zero]
      nlinarith only [hT,hD,hmarker]

theorem core_support (a b t d e : State) (second : Bool) {c v z s u : ℝ}
    (ha : 0≤transverse a) (ht : 0≤transverse t)
    (hd : transverse d≤0) (he : transverse e≤0) (hcore : e.branch.type=0)
    (hc : (3/5:ℝ)≤c) (hv : v∈Icc 0 frameCap) (hz : z∈Icc 0 frameCap)
    (hs : s∈Icc 0 frameCap) (hu : u∈Icc 0 frameCap)
    (hAB : width v≤projection false a b v 2)
    (hBT : width (-z)≤projection true b t (-z) 1) :
    CoreDE3.tail second (CoreDE3.endpointWeight u) c 0 s u≤
      Real.pi+v-z+kappa*a.b+zeroDual second t d (-s) c+
        quarterDual d e 3 (-u) (CoreDE3.endpointWeight u)+ZeroPrimary.unsigned e := by
  have hty := transverse_of_nonneg t ht
  have hdy := transverse_nonpos_eq d hd
  have hey := transverse_nonpos_eq e he
  have hmarker := CoreDE3.core_endpoint_marker e hcore hu
  cases second with
  | false =>
      have hT := transported_prefix a b t ha hv hz hc
        (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hAB hBT
      have hD := mixed_state_support d (CoreDE3.endpointWeight u) c 0 s
      simp only [Real.sin_zero,Real.cos_zero,mul_zero,mul_one,sub_zero,add_zero,zero_add] at hT hD
      dsimp [CoreDE3.tail,quarterDual,zeroDual,leftOwner,projection]
      rw [width_negative hs,width_negative hu,hty,hdy,hey]
      simp only [Real.cos_neg,Real.sin_neg,Real.cos_zero,Real.sin_zero,
        mul_one,mul_zero,add_zero,zero_add,sub_zero]
      nlinarith only [hT,hD,hmarker]
  | true =>
      have hT := transported_prefix a b t ha hv hz hc hs hAB hBT
      have hD := mixed_state_support d (CoreDE3.endpointWeight u) c 0 0
      simp only [Real.sin_zero,Real.cos_zero,mul_zero,mul_one,sub_zero,add_zero,zero_add] at hD
      dsimp [CoreDE3.tail,quarterDual,zeroDual,leftOwner,projection]
      rw [width_negative hs,width_negative hu,hty,hdy,hey]
      simp only [Real.cos_neg,Real.sin_neg,Real.cos_zero,Real.sin_zero,
        mul_one,mul_zero,add_zero,zero_add,sub_zero]
      nlinarith only [hT,hD,hmarker]

end SquaresInCircles.Eight.TableFree.GlobalBT.SoftCap
