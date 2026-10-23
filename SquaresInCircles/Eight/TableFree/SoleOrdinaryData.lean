module

public import SquaresInCircles.Eight.TableFree.SoleLowCoefficientBounds

/-!
# Ordinary coefficients for the two sole-E stresses

Uncompiled source. The four indices are H, A, B, D. The Boolean `de`
distinguishes sole-DE from sole-EH. H is a two-angle block only in the
sole-DE case; A retains its actual smaller negative coefficient. B and
D use the full two-angle domain, which also covers a missing incident
ordinary angle by setting that angle to zero.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SoleOrdinaryData
open SoleECoefficients SoleLowCoefficientBounds SoleLowChargeBounds
open SingleAngleConcavity OrdinaryAngleConcavity PositiveAngularEnvelope

def alpha (b : Band) (de : Bool) (t x e : ℝ) : Fin 4 → ℝ :=
  ![if de then r b e else 1,ell b t,ell b t,if de then 1 else p b t e]
def beta (b : Band) (t x : ℝ) : Fin 4 → ℝ := ![n b t x,k b t,c b t,c b t]
def small (b : Band) (de : Bool) (t x e : ℝ) (i : Fin 4) : ℝ :=
  min (alpha b de t x e i) (beta b t x i)
def large (b : Band) (de : Bool) (t x e : ℝ) (i : Fin 4) : ℝ :=
  max (alpha b de t x e i) (beta b t x i)
def single (de : Bool) : Fin 4 → Bool := ![!de,true,false,false]
def nu (b : Band) (de : Bool) (t x e : ℝ) : Fin 4 → ℝ :=
  ![if de then large b de t x e 0 else n b t x,ell b t,c b t,large b de t x e 3]

theorem alpha_beta_pos {b : Band} {de : Bool} {t x e : ℝ}
    (ht : t∈domain b) (hx : x∈Icc 0 t) (he : e∈Icc 0 t) (i : Fin 4) :
    0<alpha b de t x e i ∧ 0<beta b t x i := by
  obtain ⟨hk,hl,hc,hg,heta⟩ := SoleECoefficients.positive ht
  obtain ⟨hn,hp,hr⟩ := weights_positive ht hx he
  fin_cases i <;> cases de <;> simp [alpha,beta,hk,hl,hc,hn,hp,hr]

theorem small_pos {b : Band} {de : Bool} {t x e : ℝ}
    (ht : t∈domain b) (hx : x∈Icc 0 t) (he : e∈Icc 0 t) (i : Fin 4) :
    0<small b de t x e i := lt_min (alpha_beta_pos ht hx he i).1 (alpha_beta_pos ht hx he i).2

theorem small_le_large (b : Band) (de : Bool) (t x e : ℝ) (i : Fin 4) :
    small b de t x e i≤large b de t x e i := min_le_max

theorem ell_le_k_c {b : Band} {t : ℝ} (ht : t∈domain b) :
    ell b t≤k b t ∧ ell b t≤c b t := by
  cases b
  · have hb := low_bounds ht
    exact ⟨hb.2.2.2.2.2.2.1.le,hb.2.2.2.2.2.2.1.le.trans hb.2.2.1⟩
  · have hb := middle_bounds ht
    exact ⟨hb.2.2.2.2.2.2.1.le,by linarith [hb.2.2.1,hb.2.2.2.2.2.1]⟩
  · have hb := high_bounds ht
    exact ⟨hb.2.2.2.2.2.1.le,by linarith [hb.2.2.1,hb.2.2.2.2.1]⟩

theorem nu_between {b : Band} {de : Bool} {t x e : ℝ}
    (ht : t∈domain b) (i : Fin 4) :
    small b de t x e i≤nu b de t x e i ∧
      nu b de t x e i≤large b de t x e i := by
  have hA := (ell_le_k_c ht).1
  have hB := (ell_le_k_c ht).2
  fin_cases i <;> cases de <;>
    simp [small,large,alpha,beta,nu,min_eq_left hA,max_eq_right hA,
      min_eq_left hB,max_eq_right hB,min_le_right,le_max_right,min_le_max]

theorem A_data {b : Band} {de : Bool} {t x e : ℝ} (ht : t∈domain b) :
    small b de t x e 1=ell b t ∧ large b de t x e 1=k b t ∧
      nu b de t x e 1=ell b t := by
  have hh := (ell_le_k_c ht).1
  simp [small,large,alpha,beta,nu,min_eq_left hh,max_eq_right hh]

theorem B_data {b : Band} {de : Bool} {t x e : ℝ} (ht : t∈domain b) :
    small b de t x e 2=ell b t ∧ large b de t x e 2=c b t ∧
      nu b de t x e 2=c b t := by
  have hh := (ell_le_k_c ht).2
  simp [small,large,alpha,beta,nu,min_eq_left hh,max_eq_right hh]

theorem low_wide {de : Bool} {t x e : ℝ} (ht : t∈domain .low)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) {i : Fin 4} (hi : i=0 ∨ i=3) :
    base≤small .low de t x e i ∧ large .low de t x e i∈Icc 1 (28/25 : ℝ) := by
  rcases hi with rfl | rfl
  · simpa [small,large,alpha,beta] using wide_pair_H (de := de) ht hx he
  · simpa [small,large,alpha,beta] using wide_pair_D (de := de) ht hx he

theorem low_half_ratio {de : Bool} {t x e : ℝ} (ht : t∈domain .low)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) (i : Fin 4) :
    large .low de t x e i≤2*small .low de t x e i := by
  have hb := low_bounds ht
  fin_cases i
  · have hw := low_wide ht hx he (Or.inl rfl)
    dsimp [base] at hw
    linarith [hw.1,hw.2.2]
  · rcases A_data (de := de) (x := x) (e := e) ht with ⟨hs,hl,hn⟩
    rw [hs,hl]
    linarith [hb.2.2.1,hb.2.2.2.2.2.2.2.1]
  · rcases B_data (de := de) (x := x) (e := e) ht with ⟨hs,hl,hn⟩
    rw [hs,hl]
    exact hb.2.2.2.2.2.2.2.1
  · have hw := low_wide ht hx he (Or.inr rfl)
    dsimp [base] at hw
    linarith [hw.1,hw.2.2]

theorem low_large_upper {de : Bool} {t x e : ℝ} (ht : t∈domain .low)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) (i : Fin 4) :
    large .low de t x e i≤1+(7/10)*t := by
  obtain ⟨hk,hl,hc,hn,hp,hr⟩ := coarse_upper ht hx he
  have h1 : (1:ℝ)≤1+(7/10)*t := by linarith [ht.1]
  fin_cases i <;> cases de <;> simp [large,alpha,beta,max_le_iff,hk,hl,hc,hn,hp,hr,h1]

end SquaresInCircles.Eight.TableFree.SoleOrdinaryData
