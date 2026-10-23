module

public import SquaresInCircles.Eight.TableFree.GlobalBTHighPrimaryTransport

/-!
# Both complete TD--DE scalar tails after high-primary transport

The necessary cap and prefix charge are separate hypotheses.  The
transport acts only on the unchanged T circle; D, E, their errors,
the TD owner and the exact DE marker chart remain original.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalBT.HighPrimary

open FramePair FrameCircleArc GlobalOuterAnchor GlobalZeroSign

theorem aligned_formula (c eta : ℝ) :
    aligned c eta=2*kappa-R*tailNorm kappa c eta+
      (kappa-c*Real.sin eta+c*Real.cos eta)/2 := by
  have hn : Real.sqrt ((kappa-c*Real.sin eta)^2+(c*Real.cos eta)^2)=
      tailNorm kappa c eta := by
    simpa only [Real.cos_zero,Real.sin_zero,mul_one,mul_zero,sub_zero,zero_add]
      using mixed_force_norm kappa c 0 eta
  dsimp [aligned,full]
  rw [hn]
  ring

theorem transported_prefix (a t : State) {c eta z P : ℝ}
    (hc : (3/5:ℝ)≤c) (heta : eta∈Icc 0 frameCap) (hz : z∈Icc 0 frameCap)
    (hpref : prefix z≤a.b+t.a/Real.cos z)
    (hcharge : -z+kappa*(prefix z-t.a/Real.cos z)≤P) :
    2*kappa-R*tailNorm kappa c eta+(kappa-c*Real.sin eta+c*Real.cos eta)/2≤
      P+c*Real.sin eta*t.a-c*Real.cos eta*t.b := by
  have ht := state_transport a t hc heta hz hpref
  rw [aligned_formula] at ht
  dsimp [charge,force] at ht
  nlinarith only [ht,hcharge]

theorem ordinary_support (a t d e : State) (second : Bool)
    {c eWeight margin z s u P : ℝ}
    (ht : 0≤transverse t) (hd : transverse d≤0) (he : transverse e≤0)
    (hc : (3/5:ℝ)≤c) (hz : z∈Icc 0 frameCap)
    (hs : s∈Icc 0 frameCap) (hu : u∈Icc 0 frameCap)
    (hpref : prefix z≤a.b+t.a/Real.cos z)
    (hcharge : -z+kappa*(prefix z-t.a/Real.cos z)≤P)
    (hmarker : margin+eWeight*e.b≤ZeroPrimary.unsigned e) :
    de2Tail second eWeight margin c 0 s u≤
      Real.pi+P+zeroDual second t d (-s) c+
        quarterDual d e 2 (-u) eWeight+ZeroPrimary.unsigned e := by
  have hty := transverse_of_nonneg t ht
  have hdy := transverse_nonpos_eq d hd
  have hey := transverse_nonpos_eq e he
  cases second with
  | false =>
      have hT := transported_prefix a t hc
        (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hz hpref hcharge
      have hD := mixed_state_support d eWeight c u s
      rw [add_comm u s] at hD
      simp only [Real.sin_zero,Real.cos_zero,mul_zero,mul_one,sub_zero,add_zero] at hT
      dsimp [de2Tail,quarterDual,zeroDual,leftOwner,projection]
      rw [width_negative hs,width_negative hu,hty,hdy,hey]
      simp only [Real.cos_neg,Real.sin_neg,Real.cos_zero,Real.sin_zero,
        mul_one,mul_zero,add_zero,zero_add,sub_zero]
      nlinarith only [hT,hD,hmarker]
  | true =>
      have hT := transported_prefix a t hc hs hz hpref hcharge
      have hD := mixed_state_support d eWeight c u 0
      simp only [Real.sin_zero,Real.cos_zero,mul_zero,mul_one,sub_zero,add_zero] at hD
      dsimp [de2Tail,quarterDual,zeroDual,leftOwner,projection]
      rw [width_negative hs,width_negative hu,hty,hdy,hey]
      simp only [Real.cos_neg,Real.sin_neg,Real.cos_zero,Real.sin_zero,
        mul_one,mul_zero,add_zero,zero_add,sub_zero]
      nlinarith only [hT,hD,hmarker]

theorem core_support (a t d e : State) (second : Bool) {c z s u P : ℝ}
    (ht : 0≤transverse t) (hd : transverse d≤0) (he : transverse e≤0)
    (hcore : e.branch.type=0) (hc : (3/5:ℝ)≤c)
    (hz : z∈Icc 0 frameCap) (hs : s∈Icc 0 frameCap) (hu : u∈Icc 0 frameCap)
    (hpref : prefix z≤a.b+t.a/Real.cos z)
    (hcharge : -z+kappa*(prefix z-t.a/Real.cos z)≤P) :
    CoreDE3.tail second (CoreDE3.endpointWeight u) c 0 s u≤
      Real.pi+P+zeroDual second t d (-s) c+
        quarterDual d e 3 (-u) (CoreDE3.endpointWeight u)+ZeroPrimary.unsigned e := by
  have hty := transverse_of_nonneg t ht
  have hdy := transverse_nonpos_eq d hd
  have hey := transverse_nonpos_eq e he
  have hmarker := CoreDE3.core_endpoint_marker e hcore hu
  cases second with
  | false =>
      have hT := transported_prefix a t hc
        (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hz hpref hcharge
      have hD := mixed_state_support d (CoreDE3.endpointWeight u) c 0 s
      simp only [Real.sin_zero,Real.cos_zero,mul_zero,mul_one,sub_zero,add_zero,zero_add] at hT hD
      dsimp [CoreDE3.tail,quarterDual,zeroDual,leftOwner,projection]
      rw [width_negative hs,width_negative hu,hty,hdy,hey]
      simp only [Real.cos_neg,Real.sin_neg,Real.cos_zero,Real.sin_zero,
        mul_one,mul_zero,add_zero,zero_add,sub_zero]
      nlinarith only [hT,hD,hmarker]
  | true =>
      have hT := transported_prefix a t hc hs hz hpref hcharge
      have hD := mixed_state_support d (CoreDE3.endpointWeight u) c 0 0
      simp only [Real.sin_zero,Real.cos_zero,mul_zero,mul_one,sub_zero,add_zero,zero_add] at hD
      dsimp [CoreDE3.tail,quarterDual,zeroDual,leftOwner,projection]
      rw [width_negative hs,width_negative hu,hty,hdy,hey]
      simp only [Real.cos_neg,Real.sin_neg,Real.cos_zero,Real.sin_zero,
        mul_one,mul_zero,add_zero,zero_add,sub_zero]
      nlinarith only [hT,hD,hmarker]

end SquaresInCircles.Eight.TableFree.GlobalBT.HighPrimary
