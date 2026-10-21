module

public import SquaresInCircles.Eight.TableFree.GlobalBTRetainedErrors
public import SquaresInCircles.Eight.TableFree.GlobalBTTailConcentration

/-!
# The two original circles in the DE2 tail

The exact signed projections cancel B and the linear A charge.  The
remaining T and D forces have the two radicals already bounded by the
continuous tail theorem.  Their components may have either sign.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalBT

open FramePair FrameCircleArc GlobalOuterAnchor GlobalZeroSign

def tailChart : Fin 4→Fin 3 := ![0,0,1,2]

theorem tailChart_weight (i : Fin 4) : (TailPolynomial.e (tailChart i):ℝ)=tailWeight i := by
  fin_cases i <;> norm_num [tailChart,TailPolynomial.e,tailWeight]

theorem tailChart_margin (i : Fin 4) : (TailPolynomial.m (tailChart i):ℝ)=tailMargin i := by
  fin_cases i <;> norm_num [tailChart,TailPolynomial.m,tailMargin]

theorem tailChart_marker (s : State) :
    (TailPolynomial.m (tailChart s.branch.type):ℝ)+
      (TailPolynomial.e (tailChart s.branch.type):ℝ)*s.b≤ZeroPrimary.unsigned s := by
  rw [tailChart_weight,tailChart_margin]
  exact tail_marker s

theorem tailChart_weight_bounds (i : Fin 3) :
    0<(TailPolynomial.e i:ℝ) ∧ (TailPolynomial.e i:ℝ)≤kappa := by
  fin_cases i <;> norm_num [TailPolynomial.e,kappa]

theorem mixed_force_norm (a c r s : ℝ) :
    Real.sqrt ((a*Real.cos r-c*Real.sin s)^2+(c*Real.cos s-a*Real.sin r)^2)=
      tailNorm a c (r+s) := by
  unfold tailNorm
  congr 1
  rw [Real.sin_add]
  linear_combination a^2*(Real.sin_sq_add_cos_sq r)+c^2*(Real.sin_sq_add_cos_sq s)

theorem mixed_state_support (t : State) (a c r s : ℝ) :
    (a*Real.cos r-c*Real.sin s)*t.a+(c*Real.cos s-a*Real.sin r)*t.b≤
      R*tailNorm a c (r+s)-
        ((a*Real.cos r-c*Real.sin s)+(c*Real.cos s-a*Real.sin r))/2 := by
  have hh := state_support t (a*Real.cos r-c*Real.sin s) (c*Real.cos s-a*Real.sin r)
  rw [mixed_force_norm] at hh
  exact hh

def reducedDE2Tail (b t d e : State) (second : Bool)
    (c eWeight r s u : ℝ) : ℝ :=
  Real.pi+kappa*(1+transverse b)+quarterDual b t 0 (-r) kappa+
    zeroDual second t d (-s) c+quarterDual d e 2 (-u) eWeight+ZeroPrimary.unsigned e

/-- A support inequality on the unchanged states, with the original
T and D circles and both original TD owners. -/
theorem de2_support (b t d e : State) (second : Bool) {c eWeight margin r s u : ℝ}
    (ht : 0≤transverse t) (hd : transverse d≤0) (he : transverse e≤0)
    (hr : r∈Icc 0 frameCap) (hs : s∈Icc 0 frameCap) (hu : u∈Icc 0 frameCap)
    (hmarker : margin+eWeight*e.b≤ZeroPrimary.unsigned e) :
    de2Tail second eWeight margin c r s u≤reducedDE2Tail b t d e second c eWeight r s u := by
  have hty := transverse_of_nonneg t ht
  have hdy := transverse_nonpos_eq d hd
  have hey := transverse_nonpos_eq e he
  cases second with
  | false =>
      have hT := mixed_state_support t kappa c r 0
      have hD := mixed_state_support d eWeight c u s
      rw [add_comm u s] at hD
      simp only [Real.sin_zero,Real.cos_zero,mul_zero,mul_one,sub_zero,add_zero] at hT
      dsimp [de2Tail,reducedDE2Tail,quarterDual,zeroDual,leftOwner,projection]
      rw [width_negative hr,width_negative hs,width_negative hu,hty,hdy,hey]
      simp only [Real.cos_neg,Real.sin_neg]
      nlinarith only [hT,hD,hmarker]
  | true =>
      have hT := mixed_state_support t kappa c r s
      have hD := mixed_state_support d eWeight c u 0
      simp only [Real.sin_zero,Real.cos_zero,mul_zero,mul_one,sub_zero,add_zero] at hD
      dsimp [de2Tail,reducedDE2Tail,quarterDual,zeroDual,leftOwner,projection]
      rw [width_negative hr,width_negative hs,width_negative hu,hty,hdy,hey]
      simp only [Real.cos_neg,Real.sin_neg]
      nlinarith only [hT,hD,hmarker]

theorem reduced_de2_strict (b t d e : State) (second : Bool) {r s u : ℝ}
    (ht : 0≤transverse t) (hd : transverse d≤0) (he : transverse e≤0)
    (hr : 0≤r) (hs : 0≤s) (hu : 0≤u) (hcap : r+s+u≤frameCap) :
    pathThreshold<reducedDE2Tail b t d e second
      (strengthenedWeight (tailChart e.branch.type) (r+s+u))
      (TailPolynomial.e (tailChart e.branch.type):ℝ) r s u := by
  have htail := strengthened_de2Tail (tailChart e.branch.type) second hr hs hu hcap
  have hsupport := de2_support b t d e second
    (c := strengthenedWeight (tailChart e.branch.type) (r+s+u)) ht hd he
    (show r∈Icc 0 frameCap from ⟨hr,by linarith⟩)
    (show s∈Icc 0 frameCap from ⟨hs,by linarith⟩)
    (show u∈Icc 0 frameCap from ⟨hu,by linarith⟩) (tailChart_marker e)
  exact htail.trans_le hsupport

end SquaresInCircles.Eight.TableFree.GlobalBT
