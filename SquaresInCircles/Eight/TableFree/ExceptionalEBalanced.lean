module

public import SquaresInCircles.Eight.TableFree.ExceptionalETaylor

/-!
# The complete middle/high ordinary envelope at exceptional contact

Uncompiled source. The two-angle H block is retained. A coarse .95
lower bound for the larger coefficients is sufficient to pay every
positive ordinary allocation, since .545*1.131 < (2/3)*.95. Thus the
same four pure charges cover both intrinsic split endpoints and every
original AB choice without an aligned-EH restriction.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.ExceptionalEBalanced
open Candidate ExceptionalECoefficients ExceptionalContactBlocks ExceptionalContactStress
open SingleAngleConcavity PositiveAngularEnvelope OrdinaryAngleConcavity
open ExceptionalEScalarData (charge firstData secondData nuData)

def endpointX (atG : Bool) (t : ℝ) : ℝ := if atG then t else 0
def endpointE (atG : Bool) (t : ℝ) : ℝ := if atG then 0 else t

theorem endpoints_mem (atG : Bool) {t : ℝ} (ht : 0≤t) :
    endpointX atG t∈Icc 0 t ∧ endpointE atG t∈Icc 0 t := by
  cases atG <;> simp [endpointX,endpointE,ht]

theorem conditions {b : Band} {t x e : ℝ} (hb : b≠.low) (ht : t∈domain b)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) :
    (∀ i,(2/3)*large (k b t) (ell b t) (c b t) (eta b t) x e i≤
      small (k b t) (ell b t) (c b t) (eta b t) x e i) ∧
    (∀ i,(19/20:ℝ)≤large (k b t) (ell b t) (c b t) (eta b t) x e i ∧
      large (k b t) (ell b t) (c b t) (eta b t) x e i≤1131/1000) := by
  rcases balanced_bounds hb ht with ⟨hk,hl0,hl1,hc0,hc1,hcl,he0,he1⟩
  obtain ⟨hx0,hx1⟩ := balanced_tilt hb ht hx
  obtain ⟨he0',he1'⟩ := balanced_tilt hb ht he
  have hH := SoleBalancedCoefficients.ratio_from_interval
    (show tilt (eta b t) e∈Icc (19/20:ℝ) (53/50) from ⟨he0'.le,he1'.le⟩)
    (show tilt (eta b t) x∈Icc (19/20:ℝ) (53/50) from ⟨hx0.le,hx1.le⟩) (by norm_num)
  have hlc : ell b t≤c b t := by linarith
  constructor
  · intro i
    fin_cases i
    · simpa [small,large,alpha,beta,hk] using hH
    · simp [small,large,alpha,beta,hk,min_eq_left hl1.le,max_eq_right hl1.le]
      linarith
    · simpa [small,large,alpha,beta,min_eq_left hlc,max_eq_right hlc] using hcl
    · simp [small,large,alpha,beta,min_eq_left hc0.le,max_eq_right hc0.le]
      linarith
  · intro i
    fin_cases i
    · simp only [large,alpha,beta,Matrix.cons_val_zero,hk,one_mul]
      exact ⟨he0'.le.trans (le_max_left _ _),max_le (by linarith) (by linarith)⟩
    · simp [large,alpha,beta,hk,max_eq_right hl1.le]
    · simp [large,alpha,beta,max_eq_right hlc]
      constructor <;> linarith
    · simp [large,alpha,beta,max_eq_right hc0.le]
      constructor <;> linarith

theorem original_lower {C : SignedCycle} {ab : Fin 4} {b : Band} {R t x e L : ℝ}
    (hb : b≠.low) (hab : ab=0 ∨ ab=2) (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈domain b) (hx : x∈Icc 0 t) (he : e∈Icc 0 t)
    (ha : ∀ i,|delta C.theta i|≤frameCap) (hvar : positiveVariation C.theta≤frameCap)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D)
    (htotal : delta C.theta G+delta C.theta D=t)
    (hpure : ∀ i,L≤pure (single i) R
      (small (k b t) (ell b t) (c b t) (eta b t) x e i)
      (large (k b t) (ell b t) (c b t) (eta b t) x e i)
      (nu (k b t) (ell b t) (c b t) (eta b t) x e i) t) :
    L≤ExceptionalContactSupport.increment C ab R (k b t) (ell b t) (c b t) (eta b t) x e := by
  rcases ranges ht with ⟨hk,hl,hl1,hc,hc1,heta⟩
  have hp := small_pos (by linarith [hk.1]) hl hc (tilt_pos ht hx) (tilt_pos ht he)
  obtain ⟨ht0,hP,hN⟩ := original_budgets hab (k b t) (ell b t) (c b t) (eta b t) t x e
    hvar hG hD htotal
  have hconditions := conditions hb ht hx he
  have hlow := SoleAngleGrowth.balanced_envelope single R
    (small (k b t) (ell b t) (c b t) (eta b t) x e)
    (large (k b t) (ell b t) (c b t) (eta b t) x e)
    (nu (k b t) (ell b t) (c b t) (eta b t) x e)
    (fun i => (blocks C ab (k b t) (ell b t) (c b t) (eta b t) x e i).P)
    (fun i => (blocks C ab (k b t) (ell b t) (c b t) (eta b t) x e i).N)
    (qlo := 19/20) (qhi := 1131/1000) hR hQL hQU hp
    (small_le_large _ _ _ _ _ _) hconditions.1 (nu_between _ _ _ _ _ _) hconditions.2 (by norm_num)
    (fun i => (blocks C ab (k b t) (ell b t) (c b t) (eta b t) x e i).P_nonneg)
    (fun i => (blocks C ab (k b t) (ell b t) (c b t) (eta b t) x e i).N_nonneg)
    (angle ht) hP hN (single_parts C ab _ _ _ _ _ _) hpure
  exact hlow.trans (sum_minorant hab ht0 (fun i => (hp i).le) ha hP hN)

theorem norm_sorted (a b s : ℝ) : pairNorm (min a b) (max a b) s=pairNorm a b s := by
  rcases le_total a b with h | h
  · simp [min_eq_left h,max_eq_right h]
  · simp [min_eq_right h,max_eq_left h,pairNorm_symm]

def actualNu (b : Band) (t : ℝ) : Fin 4 → ℝ :=
  ![max 1 (tilt (eta b t) t),ell b t,c b t,c b t]

theorem pure_at_endpoint (atG : Bool) {b : Band} {R t : ℝ}
    (hb : b≠.low) (ht : t∈domain b) (i : Fin 4) :
    pure (single i) R
      (small (k b t) (ell b t) (c b t) (eta b t) (endpointX atG t) (endpointE atG t) i)
      (large (k b t) (ell b t) (c b t) (eta b t) (endpointX atG t) (endpointE atG t) i)
      (nu (k b t) (ell b t) (c b t) (eta b t) (endpointX atG t) (endpointE atG t) i) t=
    Vnu R (firstData b t (Real.sin t) (Real.cos t) i) (secondData b t i) (actualNu b t i) t := by
  rcases balanced_bounds hb ht with ⟨hk,hl0,hl1,hc0,hc1,hcl,he0,he1⟩
  have hlc : ell b t≤c b t := by linarith
  cases atG <;> fin_cases i <;>
    simp [endpointX,endpointE,small,large,alpha,beta,single,nu,pure,V,Vnu,norm_sorted,
      actualNu,firstData,secondData,hk,tilt,max_eq_right hl1.le,max_eq_right hlc,
      max_eq_right hc0.le,max_comm,pairNorm_symm] <;> ring

theorem charge_le_pure (atG : Bool) {b : Band} {R t : ℝ}
    (hb : b≠.low) (ht : t∈domain b) (i : Fin 4) :
    charge R b t i≤pure (single i) R
      (small (k b t) (ell b t) (c b t) (eta b t) (endpointX atG t) (endpointE atG t) i)
      (large (k b t) (ell b t) (c b t) (eta b t) (endpointX atG t) (endpointE atG t) i)
      (nu (k b t) (ell b t) (c b t) (eta b t) (endpointX atG t) (endpointE atG t) i) t := by
  rw [pure_at_endpoint atG hb ht]
  have hp := (balanced_tilt hb ht (show t∈Icc 0 t from ⟨(angle ht).1,le_rfl⟩)).2
  have hnu : actualNu b t i≤nuData b t i := by
    fin_cases i <;> simp [actualNu,nuData]
    exact max_le (by norm_num) hp.le
  have hm := mul_le_mul_of_nonpos_right hnu (show Real.cos t-1≤0 by linarith [Real.cos_le_one t])
  dsimp [charge,Vnu]
  linarith

theorem original_endpoint_lower (atG : Bool) {C : SignedCycle} {ab : Fin 4}
    {b : Band} {R t : ℝ} (hb : b≠.low) (hab : ab=0 ∨ ab=2)
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap) (ht : t∈domain b)
    (ha : ∀ i,|delta C.theta i|≤frameCap) (hvar : positiveVariation C.theta≤frameCap)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D)
    (htotal : delta C.theta G+delta C.theta D=t) :
    SoleBalancedEnvelope.minimumFour (charge R b t)≤
      ExceptionalContactSupport.increment C ab R (k b t) (ell b t) (c b t) (eta b t)
        (endpointX atG t) (endpointE atG t) := by
  obtain ⟨hx,he⟩ := endpoints_mem atG (angle ht).1
  exact original_lower hb hab hR hQL hQU ht hx he ha hvar hG hD htotal
    (fun i => (SoleBalancedEnvelope.minimumFour_le (charge R b t) i).trans (charge_le_pure atG hb ht i))

theorem scalar_endpoints {b : Band} {R t : ℝ} (hb : b≠.low) (ht : t∈domain b)
    (hR : 0≤R) (hQU : R^2≤qTrial) :
    0<ExceptionalContactSupport.atE R (k b t) (ell b t) (c b t) (eta b t) t+
      SoleBalancedEnvelope.minimumFour (charge R b t) ∧
    0<ExceptionalContactSupport.atG R (k b t) (ell b t) (c b t) (eta b t) t+
      SoleBalancedEnvelope.minimumFour (charge R b t) := by
  have hcharges : ∀ i,0<ExceptionalContactSupport.atE R (k b t) (ell b t) (c b t) (eta b t) t+
      charge R b t i := by
    intro i
    cases b
    · exact (hb rfl).elim
    · exact ExceptionalETaylor.endpoint_positive (.middle i)
        (by simpa [ExceptionalEPolynomials.domain,ExceptionalEPolynomials.origin,
          ExceptionalEPolynomials.length,domain] using ht) hR hQU
    · exact ExceptionalETaylor.endpoint_positive (.high i)
        (by simpa [ExceptionalEPolynomials.domain,ExceptionalEPolynomials.origin,
          ExceptionalEPolynomials.length,domain,frameCap] using ht) hR hQU
  have hE := SoleBalancedEnvelope.minimumFour_positive hcharges
  have hk := (balanced_bounds hb ht).1
  have heq : ExceptionalContactSupport.atG R (k b t) (ell b t) (c b t) (eta b t) t=
      ExceptionalContactSupport.atE R (k b t) (ell b t) (c b t) (eta b t) t := by
    simp [ExceptionalContactSupport.atG,ExceptionalContactSupport.atE,hk,pairNorm_symm]
  exact ⟨hE,by simpa only [heq] using hE⟩

end SquaresInCircles.Eight.TableFree.ExceptionalEBalanced
