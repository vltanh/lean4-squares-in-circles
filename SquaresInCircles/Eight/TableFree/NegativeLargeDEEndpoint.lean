module

public import SquaresInCircles.Eight.TableFree.NegativeLargeDEPolynomials
public import SquaresInCircles.Eight.TableFree.NegativeLargeDESimplex

/-!
# Positive exact-norm vertices for the negative-DE stress

Uncompiled reconstruction.  The actual cosine is retained until the
explicit positive denominator has been cleared.  Endpoint circle masses
are then compared to the exact norms by a squared real inequality.  The
vanishing E force is factored by sin(alpha), so alpha zero is included
without dividing by a zero E mass.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.TableFree.NegativeLargeDEEndpoint
open NegativeLargeDEPolynomials

def C6 (s : ℝ) : ℝ := 1-s^2/2-s^4/8-s^6/16

theorem cosine_sandwich {s c : ℝ} (hs : s∈Icc 0 (27/100:ℝ))
    (hc : 0≤c) (hunit : c^2+s^2=1) :
    C6 s-s^8/20≤c ∧ c≤C6 s := by
  have h2 := pow_le_pow_left₀ hs.1 hs.2 2
  have h4 := pow_le_pow_left₀ hs.1 hs.2 4
  have h6 := pow_le_pow_left₀ hs.1 hs.2 6
  have h8 := pow_le_pow_left₀ hs.1 hs.2 8
  have hC : (24/25:ℝ)<C6 s := by
    dsimp [C6]
    norm_num at h2 h4 h6
    nlinarith
  have hL : 0<C6 s-s^8/20 := by
    norm_num at h8
    nlinarith
  have hu : (C6 s)^2-(1-s^2)=5*s^8/64+s^10/64+s^12/256 := by
    dsimp [C6]
    ring
  have hl : (C6 s-s^8/20)^2-(1-s^2)=
      s^8*(5/64+s^2/64+s^4/256-C6 s/10+s^8/400) := by
    dsimp [C6]
    ring
  have hb : 5/64+s^2/64+s^4/256-C6 s/10+s^8/400<0 := by
    norm_num at h2 h4 h8
    nlinarith
  have hp := mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hs.1 8) hb.le
  constructor
  · nlinarith
  · nlinarith [pow_nonneg hs.1 8,pow_nonneg hs.1 10,pow_nonneg hs.1 12]

theorem cleared_positive {b : Band} {s c : ℝ} (hs : s∈domain b)
    (hc : 0≤c) (hunit : c^2+s^2=1) (j : Fin 3) :
    0<aeval s (constantNumerator b j)+aeval s (cosineNumerator b j)*c := by
  have hcos := cosine_sandwich (domain_full hs) hc hunit
  have hB := cosine_upper hs j
  have hM : 0≤(cosineReserve b:ℝ) := by cases b <;> norm_num [cosineReserve]
  have h8 : 0≤s^8/20 := div_nonneg (pow_nonneg (domain_full hs).1 8) (by norm_num)
  have hcompare :
      aeval s (cosineNumerator b j)*C6 s-(cosineReserve b:ℝ)*(s^8/20)≤
        aeval s (cosineNumerator b j)*c := by
    by_cases hsign : 0≤aeval s (cosineNumerator b j)
    · have h1 := mul_le_mul_of_nonneg_left hcos.1 hsign
      have h2 := mul_le_mul_of_nonneg_right hB.le h8
      nlinarith
    · exact le_trans (by nlinarith [mul_nonneg hM h8])
        (mul_le_mul_of_nonpos_left hcos.2 (le_of_not_ge hsign))
  have hP := polynomial_positive hs j
  have he : aeval s (P b j)=
      aeval s (constantNumerator b j)+aeval s (cosineNumerator b j)*C6 s-
        (cosineReserve b:ℝ)*(s^8/20) := by
    simp [P,cosineSix,C6]
    ring
  rw [he] at hP
  linarith

def massValue (b : Band) (j : Fin 3) (s : ℝ) (i : Fin 5) : ℝ := aeval s (mass b j i)

def massSupport (m X Y : ℝ) : ℝ :=
  m*qTrial+(X^2+Y^2)/(4*m)-(X+Y)/2

theorem support_le_mass {m : ℝ} (hm : 0<m) (X Y : ℝ) :
    NegativeLargeDEStress.support X Y≤massSupport m X Y := by
  have hs : (Real.sqrt (X^2+Y^2))^2=X^2+Y^2 :=
    Real.sq_sqrt (add_nonneg (sq_nonneg X) (sq_nonneg Y))
  have hr := NegativeLargeDECalculus.radius_sq
  have hr' := congrArg (fun z : ℝ => 4*m^2*z) hr
  have hfour : 0<4*m := by positivity
  have hh :
      (NegativeLargeDECalculus.R*Real.sqrt (X^2+Y^2)-m*qTrial)*(4*m)≤X^2+Y^2 := by
    nlinarith [sq_nonneg (2*m*NegativeLargeDECalculus.R-Real.sqrt (X^2+Y^2))]
  have hd := (le_div_iff₀ hfour).2 hh
  dsimp [NegativeLargeDEStress.support,massSupport]
  linarith

theorem support_smul {s : ℝ} (hs : 0≤s) (X Y : ℝ) :
    NegativeLargeDEStress.support (s*X) (s*Y)=s*NegativeLargeDEStress.support X Y := by
  have hn : (s*X)^2+(s*Y)^2=s^2*(X^2+Y^2) := by ring
  dsimp [NegativeLargeDEStress.support]
  rw [hn,Real.sqrt_mul (sq_nonneg s),Real.sqrt_sq hs]
  ring

/-- The rational lower bound at a geometric vertex.  The E term uses
M_E directly, including when its actual force and mass both vanish. -/
def rationalDefect (j : Fin 3) (a β ε mA mB mD mH mE s c : ℝ) : ℝ :=
  (if j=1 then 3 else 2)+2*a+(1/400)+
    (if j=1 then 2 else 3)*β+2*(307/1000)*s+ε+ε*s+
    (2*ε+(if j=0 then 1 else if j=1 then β else 0))*c+
    (if j=2 then (1+(13/12)*s)/c else 0)-
    qTrial*(mA+mB+mD+mH+s*mE)-
    (if j=0 then c^2+(a+1/400-s)^2 else 1+(a+1/400)^2)/(4*mA)-
    (if j=1 then (β*c)^2+(a-β*s)^2 else β^2+a^2)/(4*mB)-
    ((ε*c+(307/1000)*s)^2+β^2)/(4*mD)-
    (ε^2+(if j=2 then 1/c^2 else 1))/(4*mH)-
    s*(ε^2+(307/1000)^2)/(4*mE)

theorem cleared_identity {b : Band} {s c : ℝ} (hs : s∈domain b)
    (hc : c≠0) (hunit : c^2+s^2=1) (j : Fin 3) :
    aeval s (constantNumerator b j)+aeval s (cosineNumerator b j)*c=
      aeval s (denominator b j)*(if j=2 then c^2 else 1)*
        rationalDefect j (a b s) (beta b s) (epsilon b s)
          (massValue b j s 0) (massValue b j s 1) (massValue b j s 2)
          (massValue b j s 3) (massValue b j s 4) s c := by
  have hma := (mass_positive hs j 0).ne'
  have hmb := (mass_positive hs j 1).ne'
  have hmd := (mass_positive hs j 2).ne'
  have hmh := (mass_positive hs j 3).ne'
  have hme := (mass_positive hs j 4).ne'
  have hA : c^2+(a b s+1/400-s)^2=
      1+(a b s+1/400)^2-2*(a b s+1/400)*s := by nlinarith
  have hB : (beta b s*c)^2+(a b s-beta b s*s)^2=
      (beta b s)^2+(a b s)^2-2*a b s*beta b s*s := by
    nlinarith [congrArg (fun x : ℝ => (beta b s)^2*x) hunit]
  have hD : (epsilon b s*c+(307/1000)*s)^2+(beta b s)^2=
      (epsilon b s)^2*(1-s^2)+(307/1000)^2*s^2+(beta b s)^2+
        2*(307/1000)*epsilon b s*s*c := by
    nlinarith [congrArg (fun x : ℝ => (epsilon b s)^2*x) hunit]
  have hsc : 1-s^2=c^2 := by linarith
  fin_cases j <;>
    simp only [rationalDefect,Fin.isValue,ite_true,ite_false,Fin.reduceEq,hA,hB,hD] <;>
    simp only [constantNumerator,cosineNumerator,denominator,otherA,otherB,otherD,
      otherH,otherE,base,totalMass,scale,Fin.isValue,Fin.reduceEq,ite_true,ite_false,
      map_add,map_sub,map_mul,map_pow,map_one,map_zero,aeval_C,aeval_X] <;>
    norm_num [Q,eta,k,K] <;>
    dsimp [a,beta,epsilon,massValue] at * <;>
    simp only [hsc] <;>
    field_simp [hma,hmb,hmd,hmh,hme,hc] <;>
    ring

theorem rational_positive {b : Band} {s c : ℝ} (hs : s∈domain b)
    (hc : 0<c) (hunit : c^2+s^2=1) (j : Fin 3) :
    0<rationalDefect j (a b s) (beta b s) (epsilon b s)
      (massValue b j s 0) (massValue b j s 1) (massValue b j s 2)
      (massValue b j s 3) (massValue b j s 4) s c := by
  have hp := cleared_positive hs hc.le hunit j
  rw [cleared_identity hs hc.ne' hunit j] at hp
  have hden : 0<aeval s (denominator b j) := by
    simp only [denominator,map_mul,aeval_C]
    exact mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (by norm_num)
      (mass_positive hs j 0)) (mass_positive hs j 1))
        (mass_positive hs j 2)) (mass_positive hs j 3)) (mass_positive hs j 4)
  have hscale : 0<(if j=2 then c^2 else 1) := by
    split_ifs <;> positivity
  by_contra! hbad
  have hn := mul_nonpos_of_nonneg_of_nonpos (mul_pos hden hscale).le hbad
  linarith

def tVertex (j : Fin 3) (α : ℝ) : ℝ := if j=0 then α else 0
def uVertex (j : Fin 3) (α : ℝ) : ℝ := if j=1 then α else 0
def eVertex (j : Fin 3) (α : ℝ) : ℝ := if j=2 then α else 0

theorem rational_is_mass_defect (j : Fin 3)
    (a β ε mA mB mD mH mE α : ℝ) :
    rationalDefect j a β ε mA mB mD mH mE (Real.sin α) (Real.cos α)=
      NegativeLargeDEStress.demand a β ε α (tVertex j α) (uVertex j α) (eVertex j α)-
      (massSupport mA (Real.cos (tVertex j α))
          (a+NegativeLargeDEStress.η-Real.sin (tVertex j α))+
        massSupport mB (β*Real.cos (uVertex j α)) (a-β*Real.sin (uVertex j α))+
        massSupport mD (NegativeLargeDEStress.d ε α) β+
        massSupport mH ε (1/Real.cos (eVertex j α))+
        Real.sin α*massSupport mE ε NegativeLargeDEStress.k) := by
  fin_cases j <;>
    simp [rationalDefect,tVertex,uVertex,eVertex,NegativeLargeDEStress.demand,
      NegativeLargeDEStress.W,NegativeLargeDEStress.d,NegativeLargeDEStress.η,
      NegativeLargeDEStress.k,massSupport,Real.tan_eq_sin_div_cos,div_pow] <;>
    ring

theorem rational_le_exact {b : Band} {s α : ℝ}
    (hs : s∈domain b) (heq : s=Real.sin α) (j : Fin 3) :
    rationalDefect j (a b s) (beta b s) (epsilon b s)
      (massValue b j s 0) (massValue b j s 1) (massValue b j s 2)
      (massValue b j s 3) (massValue b j s 4) s (Real.cos α)≤
      NegativeLargeDEStress.defect (a b s) (beta b s) (epsilon b s) α
        (tVertex j α) (uVertex j α) (eVertex j α) := by
  have hA := support_le_mass (mass_positive hs j 0) (Real.cos (tVertex j α))
    (a b s+NegativeLargeDEStress.η-Real.sin (tVertex j α))
  have hB := support_le_mass (mass_positive hs j 1) (beta b s*Real.cos (uVertex j α))
    (a b s-beta b s*Real.sin (uVertex j α))
  have hD := support_le_mass (mass_positive hs j 2)
    (NegativeLargeDEStress.d (epsilon b s) α) (beta b s)
  have hH := support_le_mass (mass_positive hs j 3) (epsilon b s) (1/Real.cos (eVertex j α))
  have hE := mul_le_mul_of_nonneg_left
    (support_le_mass (mass_positive hs j 4) (epsilon b s) NegativeLargeDEStress.k)
    (domain_full hs).1
  have hE' : NegativeLargeDEStress.support (epsilon b s*Real.sin α)
      (NegativeLargeDEStress.k*Real.sin α)≤
      Real.sin α*massSupport (massValue b j s 4) (epsilon b s) NegativeLargeDEStress.k := by
    rw [mul_comm (epsilon b s),mul_comm NegativeLargeDEStress.k,
      support_smul (by rw [←heq]; exact (domain_full hs).1)]
    simpa [heq,massValue] using hE
  have hid := rational_is_mass_defect j (a b s) (beta b s) (epsilon b s)
    (massValue b j s 0) (massValue b j s 1) (massValue b j s 2)
    (massValue b j s 3) (massValue b j s 4) α
  rw [←heq] at hid
  rw [hid]
  dsimp [NegativeLargeDEStress.defect]
  change _≤_ at hA hB hD hH
  simp only [heq] at *
  dsimp [massValue] at *
  linarith

/-- All three actual exact-norm vertices are strictly positive. -/
theorem vertex_positive {b : Band} {α : ℝ}
    (hα : α∈Icc 0 (27/100:ℝ)) (hs : Real.sin α∈domain b) (j : Fin 3) :
    0<NegativeLargeDEStress.defect (a b (Real.sin α)) (beta b (Real.sin α))
      (epsilon b (Real.sin α)) α (tVertex j α) (uVertex j α) (eVertex j α) := by
  have hc : 0<Real.cos α := by
    linarith [(NegativeLargeDECalculus.short_trig hα).1]
  have hu : (Real.cos α)^2+(Real.sin α)^2=1 := by
    nlinarith [Real.sin_sq_add_cos_sq α]
  exact (rational_positive hs hc hu j).trans_le (rational_le_exact hs rfl j)

/-- A band is selected only from the total sine.  That one continuous
weight formula is then used for every split of the original angles. -/
theorem exists_positive_defect {α t u e : ℝ}
    (hα : α∈Icc 0 (27/100:ℝ))
    (ht : 0≤t) (hu : 0≤u) (he : 0≤e) (hsum : t+u+e=α) :
    ∃a β ε : ℝ, 0≤a ∧ 0≤β ∧ 0≤ε ∧
      0<NegativeLargeDEStress.defect a β ε α t u e := by
  have hs : Real.sin α∈Icc 0 (27/100:ℝ) :=
    ⟨(NegativeLargeDECalculus.short_trig hα).2.2.1,(Real.sin_le hα.1).trans hα.2⟩
  let b : Band := if Real.sin α≤4/25 then .low else .high
  have hdom : Real.sin α∈domain b := by
    dsimp [b]
    split_ifs with h
    · exact ⟨hs.1,h⟩
    · exact ⟨by linarith,hs.2⟩
  obtain ⟨ha0,ha1,hb0,hb1,he0,he1⟩ := actual_weight_bounds hdom
  let a := NegativeLargeDEPolynomials.a b (Real.sin α)
  let β := beta b (Real.sin α)
  let ε := epsilon b (Real.sin α)
  have hA : a+NegativeLargeDEStress.η∈Ioo (0:ℝ) (18/25) := by
    dsimp [a,NegativeLargeDEStress.η]
    constructor <;> linarith
  have hβ : 0<β := by dsimp [β]; linarith
  have hB : a/β∈Ioo (0:ℝ) (18/25) := by
    constructor
    · exact div_pos (by dsimp [a]; linarith) hβ
    · apply (div_lt_iff₀ hβ).2
      dsimp [a,β]
      linarith
  have hε : |ε|≤117/100 := by
    rw [abs_of_nonneg (show 0≤ε by dsimp [ε]; linarith)]
    exact he1.le
  have hp := NegativeLargeDEStress.positive_on_simplex hA hB
    (show 99/100≤β from hb0.le) hε hα ht hu he hsum
    (by simpa [tVertex,uVertex,eVertex] using vertex_positive hα hdom 0)
    (by simpa [tVertex,uVertex,eVertex] using vertex_positive hα hdom 1)
    (by simpa [tVertex,uVertex,eVertex] using vertex_positive hα hdom 2)
  exact ⟨a,β,ε,by dsimp [a]; linarith,hβ.le,by dsimp [ε]; linarith,hp⟩

end SquaresInCircles.Eight.TableFree.NegativeLargeDEEndpoint
