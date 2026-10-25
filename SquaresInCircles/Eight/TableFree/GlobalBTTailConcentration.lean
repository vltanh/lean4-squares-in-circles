module

public import SquaresInCircles.Eight.TableFree.GlobalBTTailWeights

/-!
# Complete concentration of the three DE2 tail errors

Both original TD owners reduce to the same two retained-circle
endpoint scalars.  The TD error is first concentrated by a cosine
comparison, and the remaining split uses the full norm concavity.
The strengthened weight remains fixed during both comparisons.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalBT

open Polynomial FrameCircleArc

def tailSplit (e m c r t : ℝ) : ℝ :=
  Real.pi-(r+t)+(3/2)*kappa+2*c+e/2+m+normCos kappa c r+normCos e c t
def de2Tail (second : Bool) (e m c r s t : ℝ) : ℝ :=
  Real.pi-(r+s+t)+(3/2)*kappa+c+e/2+m+
    kappa*Real.cos r+c*Real.cos s+e*Real.cos t-
    R*(if second then tailNorm kappa c (r+s)+tailNorm e c t
      else tailNorm kappa c r+tailNorm e c (s+t))

theorem cosine_concentration {c e s t : ℝ} (hc : 0≤c) (hce : c≤e)
    (hs : s∈Icc 0 frameCap) (ht : t∈Icc 0 frameCap) :
    c+e*Real.cos (s+t)≤c*Real.cos s+e*Real.cos t := by
  have trs := transport_trig hs
  have trt := transport_trig ht
  have hcs : 0≤Real.cos s := by linarith [trs.1]
  have hct : 0≤Real.cos t := by linarith [trt.1]
  have hss := trs.2.2.1
  have hst := trt.2.2.1
  have hsumS := one_le_abs_cos_add_abs_sin s
  have hsumT := one_le_abs_cos_add_abs_sin t
  rw [abs_of_nonneg hcs,abs_of_nonneg hss] at hsumS
  rw [abs_of_nonneg hct,abs_of_nonneg hst] at hsumT
  have hdS : 0≤1-Real.cos s := sub_nonneg.mpr (Real.cos_le_one s)
  have hdT : 0≤1-Real.cos t := sub_nonneg.mpr (Real.cos_le_one t)
  have hprod := mul_le_mul (show 1-Real.cos s≤Real.sin s by linarith)
    (show 1-Real.cos t≤Real.sin t by linarith) hdT hss
  have hbase : 0≤Real.cos s+Real.cos t-1-Real.cos (s+t) := by
    rw [Real.cos_add]
    nlinarith only [hprod]
  have hmono : 0≤Real.cos t-Real.cos (s+t) := by
    rw [Real.cos_add]
    nlinarith only [mul_nonneg hct hdS,mul_nonneg hss hst]
  have hfirst := mul_nonneg hc hbase
  have hsecond := mul_nonneg (sub_nonneg.mpr hce) hmono
  nlinarith only [hfirst,hsecond]

theorem tailSplit_concave {e m c z : ℝ} (he : 0<e) (hc : 0<c)
    (hz : z∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 z) (fun r => tailSplit e m c r (z-r)) := by
  have hfirst := (normCos_concave (a := kappa) (by norm_num [kappa]) hc).subset (Icc_subset_Icc le_rfl hz.2) (convex_Icc 0 z)
  have hsecond := concave_affine_argument (normCos_concave he hc)
    (a := -1) (b := z) (l := 0) (u := z)
    (fun r hr => ⟨by linarith [hr.2],by linarith [hz.2,hr.1]⟩)
  have hconstant := affine_concave 0
    (Real.pi-z+(3/2)*kappa+2*c+e/2+m) 0 z
  convert (hconstant.add hfirst).add hsecond using 1
  funext r
  dsimp [tailSplit]
  rw [show (-1:ℝ)*r+z=z-r by ring]
  ring

theorem tailSplit_zero (e m c z : ℝ) : tailSplit e m c 0 z=tailEndpoint true e m c z := by
  simp [tailSplit,tailEndpoint,normCos] <;> ring

theorem tailSplit_last (e m c z : ℝ) : tailSplit e m c z 0=tailEndpoint false e m c z := by
  simp [tailSplit,tailEndpoint,normCos] <;> ring

theorem strengthened_tailSplit (i : Fin 3) {r t : ℝ} (hr : 0≤r) (ht : 0≤t)
    (hcap : r+t≤frameCap) :
    pathThreshold<tailSplit (TailPolynomial.e i:ℝ) (TailPolynomial.m i:ℝ)
      (strengthenedWeight i (r+t)) r t := by
  let z : ℝ := r+t
  have hz : z∈Icc 0 frameCap := ⟨add_nonneg hr ht,hcap⟩
  let c := strengthenedWeight i z
  have hc : 0<c := by have hh := (strengthened_bounds i hz).1; dsimp [c]; linarith
  have hconc := tailSplit_concave (m := (TailPolynomial.m i:ℝ))
    (TailPolynomial.chart_positive i) hc hz
  have hleft := strengthened_tail_endpoint i true hz
  have hright := strengthened_tail_endpoint i false hz
  rw [← tailSplit_zero] at hleft
  rw [← tailSplit_last] at hright
  have hh := concave_gt_of_endpoints hconc
    (show r∈Icc 0 z from ⟨hr,by dsimp [z]; linarith⟩)
    (by simpa [c] using hleft) (by simpa [c] using hright)
  simpa [c,z] using hh

/-- The complete continuous DE2 tail, for either original TD owner and
all three nonnegative retained negative errors with shared total cap. -/
theorem strengthened_de2Tail (i : Fin 3) (second : Bool) {r s t : ℝ}
    (hr : 0≤r) (hs : 0≤ s) (ht : 0≤t) (hcap : r+s+t≤frameCap) :
    pathThreshold<de2Tail second (TailPolynomial.e i:ℝ) (TailPolynomial.m i:ℝ)
      (strengthenedWeight i (r+s+t)) r s t := by
  let c := strengthenedWeight i (r+s+t)
  have htotal : r+s+t∈Icc 0 frameCap := ⟨by positivity,hcap⟩
  have hweights := strengthened_bounds i htotal
  have hc : 0≤c := by dsimp [c]; linarith [hweights.1]
  have hrange : r∈Icc 0 frameCap := ⟨hr,by linarith⟩
  have hsrange : s∈Icc 0 frameCap := ⟨hs,by linarith⟩
  have htrange : t∈Icc 0 frameCap := ⟨ht,by linarith⟩
  cases second with
  | false =>
      have hcos := cosine_concentration hc hweights.2.2 hsrange htrange
      have hsplit := strengthened_tailSplit i hr (add_nonneg hs ht)
        (by linarith : r+(s+t)≤frameCap)
      have hsame : r+(s+t)=r+s+t := by ring
      rw [hsame] at hsplit
      dsimp [tailSplit,normCos,de2Tail]
      dsimp [tailSplit,normCos] at hsplit
      dsimp [c] at hcos
      linarith
  | true =>
      have hcos := cosine_concentration hc hweights.2.1 hsrange hrange
      rw [add_comm s r] at hcos
      have hsplit := strengthened_tailSplit i (add_nonneg hr hs) ht hcap
      dsimp [tailSplit,normCos] at hsplit
      dsimp [de2Tail]
      dsimp [c] at hcos
      linarith

end SquaresInCircles.Eight.TableFree.GlobalBT
