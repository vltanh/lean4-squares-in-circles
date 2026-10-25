module

public import SquaresInCircles.Eight.Owners.DirectedPowerBounds
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2PolynomialData
public import SquaresInCircles.Eight.Arithmetic.PolynomialCertificates

/-!
# Eight squares: positive tangent denominators for the negative-A scalar endpoints

Each bound holds on the whole coefficient interval. It applies the centered monomial coefficient
norm to the auxiliary polynomial itself (`mass_reserve`, `cut_mass_reserve`).
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.Certificate
open Polynomial PowerTailBounds
open PositiveTD.Certificate (C4 h)
open WholeIntervalPolynomial.Certificate (Scaled)
open PositiveTD.Certificate (S5 etaQ)

def mass (f : Family) : Fin 15→ℚ[X] :=
  ![RH f,RG f,RB f,RD f,RHminus f,RGminus f,RBminus f,
    C4*RH f,equalGAR f 1,C4*RB f,C4*RD f,C4*RG f,
    C (4/5)*l f+C (3/5)*mu f*C4,C (77/100),C (77/100)*l f]
def midpoint (f : Family) : ℚ := (left f+right f)/2
def radius (f : Family) : ℚ := (right f-left f)/2
def massCentered (f : Family) (i : Fin 15) : ℚ[X] :=
  DirectedPowerBounds.shift (midpoint f) (mass f i)

/-! ### The auxiliary masses as scaled integer coefficient lists -/

private def r42S5 : Scaled :=
  (Scaled.var.sub ((Scaled.const (1/6)).mul (Scaled.var.pow 3))).add
    ((Scaled.const (1/120)).mul (Scaled.var.pow 5))
private theorem r42S5_rep : r42S5.Rep S5 :=
  (Scaled.rep_var.sub ((Scaled.rep_const _).mul (Scaled.rep_var.pow 3))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 5))
private def r42C4 : Scaled :=
  ((Scaled.ofNat 1).sub ((Scaled.const (1/2)).mul (Scaled.var.pow 2))).add
    ((Scaled.const (1/24)).mul (Scaled.var.pow 4))
private theorem r42C4_rep : r42C4.Rep C4 :=
  (Scaled.rep_one.sub ((Scaled.rep_const _).mul (Scaled.rep_var.pow 2))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 4))
private def r42t : Family → Scaled
  | .low => (Scaled.const split).sub Scaled.var
  | .high => Scaled.var.sub (Scaled.const split)
private theorem r42t_rep : ∀ f, (r42t f).Rep (t f)
  | .low => (Scaled.rep_const _).sub Scaled.rep_var
  | .high => Scaled.rep_var.sub (Scaled.rep_const _)
private def r42k : Family → Scaled
  | .low => (((Scaled.const (169/250)).sub ((Scaled.const (1/5)).mul (r42t .low))).add
      ((Scaled.const (19/5)).mul ((r42t .low).pow 2))).sub
      ((Scaled.const 5).mul ((r42t .low).pow 3))
  | .high => (((Scaled.const (169/250)).add ((Scaled.const (1/5)).mul (r42t .high))).add
      ((Scaled.const (9/10)).mul ((r42t .high).pow 2))).sub
      ((Scaled.const (13/10)).mul ((r42t .high).pow 3))
private theorem r42k_rep : ∀ f, (r42k f).Rep (k f)
  | .low => (((Scaled.rep_const _).sub ((Scaled.rep_const _).mul (r42t_rep .low))).add
      ((Scaled.rep_const _).mul ((r42t_rep .low).pow 2))).sub
      ((Scaled.rep_const _).mul ((r42t_rep .low).pow 3))
  | .high => (((Scaled.rep_const _).add ((Scaled.rep_const _).mul (r42t_rep .high))).add
      ((Scaled.rep_const _).mul ((r42t_rep .high).pow 2))).sub
      ((Scaled.rep_const _).mul ((r42t_rep .high).pow 3))
private def r42l : Family → Scaled
  | .low => ((((Scaled.const (41/40)).sub ((Scaled.const (1/4)).mul (r42t .low))).add
      ((Scaled.const (29/2)).mul ((r42t .low).pow 2))).add
      ((Scaled.const (55/4)).mul ((r42t .low).pow 3))).sub
      ((Scaled.const 200).mul ((r42t .low).pow 4))
  | .high => ((Scaled.const (41/40)).add ((Scaled.const (11/50)).mul (r42t .high))).sub
      ((Scaled.const (3/10)).mul ((r42t .high).pow 2))
private theorem r42l_rep : ∀ f, (r42l f).Rep (l f)
  | .low => ((((Scaled.rep_const _).sub ((Scaled.rep_const _).mul (r42t_rep .low))).add
      ((Scaled.rep_const _).mul ((r42t_rep .low).pow 2))).add
      ((Scaled.rep_const _).mul ((r42t_rep .low).pow 3))).sub
      ((Scaled.rep_const _).mul ((r42t_rep .low).pow 4))
  | .high => ((Scaled.rep_const _).add ((Scaled.rep_const _).mul (r42t_rep .high))).sub
      ((Scaled.rep_const _).mul ((r42t_rep .high).pow 2))
private def r42c : Family → Scaled
  | .low => ((Scaled.ofNat 1).add ((Scaled.const (11/10)).mul (r42t .low))).add
      ((Scaled.const 17).mul ((r42t .low).pow 2))
  | .high => ((Scaled.ofNat 1).sub ((Scaled.const (7/10)).mul (r42t .high))).add
      ((Scaled.const (22/25)).mul ((r42t .high).pow 2))
private theorem r42c_rep : ∀ f, (r42c f).Rep (c f)
  | .low => (Scaled.rep_one.add ((Scaled.rep_const _).mul (r42t_rep .low))).add
      ((Scaled.rep_const _).mul ((r42t_rep .low).pow 2))
  | .high => (Scaled.rep_one.sub ((Scaled.rep_const _).mul (r42t_rep .high))).add
      ((Scaled.rep_const _).mul ((r42t_rep .high).pow 2))
private def r42mu (f : Family) : Scaled := (r42c f).mul (r42C4.add ((Scaled.const etaQ).mul r42S5))
private theorem r42mu_rep (f : Family) : (r42mu f).Rep (mu f) :=
  (r42c_rep f).mul (r42C4_rep.add ((Scaled.rep_const _).mul r42S5_rep))
private def r42RH (f : Family) : Scaled := (Scaled.const (83/100)).add ((Scaled.const (279/500)).mul (r42k f))
private theorem r42RH_rep (f : Family) : (r42RH f).Rep (RH f) :=
  (Scaled.rep_const _).add ((Scaled.rep_const _).mul (r42k_rep f))
private def r42RG (f : Family) : Scaled :=
  ((Scaled.const (11/20)).mul (r42k f)).add ((Scaled.const (167/200)).mul (r42l f))
private theorem r42RG_rep (f : Family) : (r42RG f).Rep (RG f) :=
  ((Scaled.rep_const _).mul (r42k_rep f)).add ((Scaled.rep_const _).mul (r42l_rep f))
private def r42RB (f : Family) : Scaled :=
  ((Scaled.const (29/40)).mul (r42mu f)).add ((Scaled.const (689/1000)).mul (r42l f))
private theorem r42RB_rep (f : Family) : (r42RB f).Rep (RB f) :=
  ((Scaled.rep_const _).mul (r42mu_rep f)).add ((Scaled.rep_const _).mul (r42l_rep f))
private def r42RD (f : Family) : Scaled := (Scaled.const (7071/10000)).mul ((Scaled.ofNat 1).add (r42c f))
private theorem r42RD_rep (f : Family) : (r42RD f).Rep (RD f) :=
  (Scaled.rep_const _).mul (Scaled.rep_one.add (r42c_rep f))
private def r42RHminus (f : Family) : Scaled :=
  ((Scaled.const (179/200)).mul r42C4).add ((Scaled.const (223/500)).mul ((r42k f).sub r42S5))
private theorem r42RHminus_rep (f : Family) : (r42RHminus f).Rep (RHminus f) :=
  ((Scaled.rep_const _).mul r42C4_rep).add ((Scaled.rep_const _).mul ((r42k_rep f).sub r42S5_rep))
private def r42RGminus (f : Family) : Scaled :=
  (((Scaled.const (9/10)).mul (r42l f)).mul r42C4).add
    ((Scaled.const (109/250)).mul ((r42k f).sub ((r42l f).mul r42S5)))
private theorem r42RGminus_rep (f : Family) : (r42RGminus f).Rep (RGminus f) :=
  (((Scaled.rep_const _).mul (r42l_rep f)).mul r42C4_rep).add
    ((Scaled.rep_const _).mul ((r42k_rep f).sub ((r42l_rep f).mul r42S5_rep)))
private def r42RBminus (f : Family) : Scaled :=
  (((Scaled.const (94/125)).mul (r42l f)).mul r42C4).add
    ((Scaled.const (33/50)).mul ((r42mu f).sub ((r42l f).mul r42S5)))
private theorem r42RBminus_rep (f : Family) : (r42RBminus f).Rep (RBminus f) :=
  (((Scaled.rep_const _).mul (r42l_rep f)).mul r42C4_rep).add
    ((Scaled.rep_const _).mul ((r42mu_rep f).sub ((r42l_rep f).mul r42S5_rep)))
private theorem r42_rep_eval {S : Scaled} {p : ℚ[X]} (hp : S.Rep p) (num den : ℕ) (s : ℤ)
    {a : ℚ} (hden : den≠0) (ha : a=num*s/den) : (S.center num den s 0).Rep (C (p.eval a)) := by
  have hc := hp.centered num den s 0 (a:=a) (b:=a) hden (by rw [← ha]; ring) (by simp)
  have he : WholeIntervalPolynomial.centered a a p=C (p.eval a) := by
    rw [WholeIntervalPolynomial.centered,WholeIntervalPolynomial.affine,sub_self,zero_div,
      map_zero,zero_mul,add_zero,add_self_div_two,comp_C]
  rwa [he] at hc
private theorem r42_rep_Cmul {S T : Scaled} {a b : ℚ} (hS : S.Rep (C a)) (hT : T.Rep (C b)) :
    (S.mul T).Rep (C (a*b)) := by rw [map_mul]; exact hS.mul hT
private def r42head (S : Scaled) : Scaled := ⟨[S.l.getD 0 0],S.s⟩
private theorem r42head_rep {S : Scaled} {c : ℚ} (hS : S.Rep (C c)) : (r42head S).Rep (C c) := by
  unfold Scaled.Rep at *
  have h0 := congrArg (fun q => q.coeff 0) hS
  simp only [WholeIntervalPolynomial.Certificate.coeff_toPoly,coeff_C_mul,coeff_C_zero] at h0
  simp only [r42head,WholeIntervalPolynomial.Certificate.toPoly,mul_zero,add_zero,h0,map_mul]
private def r42ang (e : Cut) (S : Scaled) : Scaled :=
  r42head (if cutAtG e then S.center 1 4 1 0 else S.center 19 50 1 0)
private theorem r42ang_rep (e : Cut) {S : Scaled} {p : ℚ[X]} (hp : S.Rep p) :
    (r42ang e S).Rep (C (p.eval (cutAngle e))) := by
  apply r42head_rep
  rcases hb : cutAtG e with _|_ <;> simp only [cutAngle,hb,Bool.false_eq_true,↓reduceIte]
  · exact r42_rep_eval hp 19 50 1 (by norm_num) (by norm_num)
  · exact r42_rep_eval hp 1 4 1 (by norm_num) (by norm_num)
private def r42ga (e : Cut) : Scaled := r42ang e r42C4
private def r42ta (e : Cut) : Scaled := r42ang e r42S5
private theorem r42ga_rep (e : Cut) : (r42ga e).Rep (C (gammaApprox e)) := r42ang_rep e r42C4_rep
private theorem r42ta_rep (e : Cut) : (r42ta e).Rep (C (tauApprox e)) := r42ang_rep e r42S5_rep
private def r42cosAp (e : Cut) : Scaled := ((r42ga e).mul r42C4).add ((r42ta e).mul r42S5)
private theorem r42cosAp_rep (e : Cut) : (r42cosAp e).Rep (thetaCosApprox e) :=
  ((r42ga_rep e).mul r42C4_rep).add ((r42ta_rep e).mul r42S5_rep)
private def r42sinAp (e : Cut) : Scaled := ((r42ga e).mul r42S5).sub ((r42ta e).mul r42C4)
private theorem r42sinAp_rep (e : Cut) : (r42sinAp e).Rep (thetaSinApprox e) :=
  ((r42ga_rep e).mul r42S5_rep).sub ((r42ta_rep e).mul r42C4_rep)
private def r42theta (e : Cut) : Scaled := Scaled.var.sub (Scaled.const (cutAngle e))
private theorem r42theta_rep (e : Cut) : (r42theta e).Rep (theta e) :=
  Scaled.rep_var.sub (Scaled.rep_const _)
private def r42cR0 (e : Cut) : Scaled := (r42ga e).mul (r42RH .high)
private theorem r42cR0_rep (e : Cut) : (r42cR0 e).Rep (C (gammaApprox e)*RH .high) :=
  (r42ga_rep e).mul (r42RH_rep .high)
private def r42cR0u (e : Cut) : Scaled :=
  (r42ga e).mul (((Scaled.const (87/100)).mul (r42cosAp e)).add
    ((Scaled.const (493/1000)).mul ((r42k .high).sub (r42sinAp e))))
private theorem r42cR0u_rep (e : Cut) : (r42cR0u e).Rep (C (gammaApprox e)*
    (C (87/100)*thetaCosApprox e+C (493/1000)*(k .high-thetaSinApprox e))) :=
  (r42ga_rep e).mul (((Scaled.rep_const _).mul (r42cosAp_rep e)).add
    ((Scaled.rep_const _).mul ((r42k_rep .high).sub (r42sinAp_rep e))))
private def r42cR1g (e : Cut) : Scaled :=
  ((Scaled.const (21/25)).mul (r42l .high)).add
    (((Scaled.const (543/1000)).mul (r42ga e)).mul (r42k .high))
private theorem r42cR1g_rep (e : Cut) : (r42cR1g e).Rep
    (C (21/25)*l .high+C (543/1000*gammaApprox e)*k .high) :=
  ((Scaled.rep_const _).mul (r42l_rep .high)).add
    ((r42_rep_Cmul (Scaled.rep_const _) (r42ga_rep e)).mul (r42k_rep .high))
private def r42cR1a (e : Cut) : Scaled := (r42ga e).mul (r42RG .high)
private theorem r42cR1a_rep (e : Cut) : (r42cR1a e).Rep (C (gammaApprox e)*RG .high) :=
  (r42ga_rep e).mul (r42RG_rep .high)
private def r42cR1u (e : Cut) : Scaled :=
  (r42ga e).mul ((((Scaled.const (9/10)).mul (r42l .high)).mul (r42cosAp e)).add
    ((Scaled.const (109/250)).mul ((r42k .high).sub ((r42l .high).mul (r42sinAp e)))))
private theorem r42cR1u_rep (e : Cut) : (r42cR1u e).Rep (C (gammaApprox e)*
    (C (9/10)*l .high*thetaCosApprox e+C (109/250)*(k .high-l .high*thetaSinApprox e))) :=
  (r42ga_rep e).mul ((((Scaled.rep_const _).mul (r42l_rep .high)).mul (r42cosAp_rep e)).add
    ((Scaled.rep_const _).mul ((r42k_rep .high).sub ((r42l_rep .high).mul (r42sinAp_rep e)))))
private def r42cR2g (e : Cut) : Scaled := (r42ga e).mul (r42RB .high)
private theorem r42cR2g_rep (e : Cut) : (r42cR2g e).Rep (C (gammaApprox e)*RB .high) :=
  (r42ga_rep e).mul (r42RB_rep .high)
private def r42cR2a (e : Cut) : Scaled :=
  ((Scaled.const (4/5)).mul (r42l .high)).add (((Scaled.const (3/5)).mul (r42ga e)).mul (r42mu .high))
private theorem r42cR2a_rep (e : Cut) : (r42cR2a e).Rep
    (C (4/5)*l .high+C (3/5*gammaApprox e)*mu .high) :=
  ((Scaled.rep_const _).mul (r42l_rep .high)).add
    ((r42_rep_Cmul (Scaled.rep_const _) (r42ga_rep e)).mul (r42mu_rep .high))
private def r42cR2u (e : Cut) : Scaled :=
  (r42ga e).mul (((((Scaled.const (357/500)).add ((Scaled.const (11/20)).mul (r42theta e))).mul
      (r42l .high)).mul (r42cosAp e)).add
    (((Scaled.const (7/10)).sub ((Scaled.const (41/50)).mul (r42theta e))).mul
      ((r42mu .high).sub ((r42l .high).mul (r42sinAp e)))))
private theorem r42cR2u_rep (e : Cut) : (r42cR2u e).Rep (C (gammaApprox e)*
    ((C (357/500)+C (11/20)*theta e)*l .high*thetaCosApprox e+
      (C (7/10)-C (41/50)*theta e)*(mu .high-l .high*thetaSinApprox e))) :=
  (r42ga_rep e).mul (((((Scaled.rep_const _).add ((Scaled.rep_const _).mul (r42theta_rep e))).mul
      (r42l_rep .high)).mul (r42cosAp_rep e)).add
    (((Scaled.rep_const _).sub ((Scaled.rep_const _).mul (r42theta_rep e))).mul
      ((r42mu_rep .high).sub ((r42l_rep .high).mul (r42sinAp_rep e)))))
private def r42cR3 (e : Cut) : Scaled := (r42ga e).mul (r42RD .high)
private theorem r42cR3_rep (e : Cut) : (r42cR3 e).Rep (C (gammaApprox e)*RD .high) :=
  (r42ga_rep e).mul (r42RD_rep .high)

private def r42mass (f : Family) : Fin 15→Scaled :=
  ![r42RH f,r42RG f,r42RB f,r42RD f,r42RHminus f,r42RGminus f,r42RBminus f,
    r42C4.mul (r42RH f),
    ((Scaled.const (21/25)).mul (r42l f)).add (((Scaled.const (543/1000)).mul (r42k f)).mul r42C4),
    r42C4.mul (r42RB f),r42C4.mul (r42RD f),r42C4.mul (r42RG f),
    ((Scaled.const (4/5)).mul (r42l f)).add (((Scaled.const (3/5)).mul (r42mu f)).mul r42C4),
    Scaled.const (77/100),(Scaled.const (77/100)).mul (r42l f)]
private theorem r42mass_rep (f : Family) (i : Fin 15) : (r42mass f i).Rep (mass f i) := by
  fin_cases i
  exacts [r42RH_rep f,r42RG_rep f,r42RB_rep f,r42RD_rep f,r42RHminus_rep f,r42RGminus_rep f,
    r42RBminus_rep f,r42C4_rep.mul (r42RH_rep f),
    ((Scaled.rep_const _).mul (r42l_rep f)).add (((Scaled.rep_const _).mul (r42k_rep f)).mul r42C4_rep),
    r42C4_rep.mul (r42RB_rep f),r42C4_rep.mul (r42RD_rep f),r42C4_rep.mul (r42RG_rep f),
    ((Scaled.rep_const _).mul (r42l_rep f)).add (((Scaled.rep_const _).mul (r42mu_rep f)).mul r42C4_rep),
    Scaled.rep_const _,(Scaled.rep_const _).mul (r42l_rep f)]

private theorem r42_shift_rep {S : Scaled} {p : ℚ[X]} (hp : S.Rep p) (num den : ℕ) (s t : ℤ)
    {m : ℚ} (hden : den≠0) (hm : m=num*s/den) (h1 : (1:ℚ)=num*t/den) :
    (S.center num den s t).Rep (DirectedPowerBounds.shift m p) := by
  have hc := hp.centered num den s t (a:=m-1) (b:=m+1) hden (by rw [← hm]; ring) (by rw [← h1]; ring)
  rwa [WholeIntervalPolynomial.centered,WholeIntervalPolynomial.affine,show (m-1+(m+1))/2=m by ring,
    show (m+1-(m-1))/2=1 by ring,map_one,one_mul] at hc

private def r42mc : Family→Fin 15→Scaled
  | .low,i => (r42mass .low i).center 1 10 1 10
  | .high,i => (r42mass .high i).center 1 20 9 20
private theorem r42mc_rep : ∀ f i,(r42mc f i).Rep (massCentered f i)
  | .low,i => r42_shift_rep (r42mass_rep .low i) 1 10 1 10 (by norm_num)
      (by norm_num [midpoint,left,right,split]) (by norm_num)
  | .high,i => r42_shift_rep (r42mass_rep .high i) 1 20 9 20 (by norm_num)
      (by norm_num [midpoint,left,right,split,h]) (by norm_num)

/-- A polynomial of degree at most `n` is its constant term plus its power tail. -/
private theorem r42_tail_identity {p : ℚ[X]} {n : ℕ} (hp : p.natDegree≤n) :
    p=C (p.coeff 0)+tail p 1 n := by
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow' (n:=n+1) (Nat.lt_succ_of_le hp)]
  rw [Finset.sum_range_succ',tail,← Fin.sum_univ_eq_sum_range (fun i => C (p.coeff (i+1))*X^(i+1)) n,
    pow_zero,mul_one,add_comm]

private theorem r42_reserve_of_rep {S : Scaled} {p : ℚ[X]} (hp : S.Rep p) (hs : S.s≠0)
    (n : ℕ) (r ρ : ℚ) (h : ρ<(S.l.getD 0 0:ℚ)/S.s-
      ∑ j : Fin n,|(S.l.getD (j.val+1) 0:ℚ)/S.s| *r^(j.val+1)) :
    ρ<p.coeff 0-PowerTailBounds.norm p 1 n r := by
  simp only [PowerTailBounds.norm,hp.coeff hs]
  exact h

theorem mass_identity (f : Family) (i : Fin 15) :
    massCentered f i=C ((massCentered f i).coeff 0)+tail (massCentered f i) 1 11 := by
  cases f <;> fin_cases i <;>
    exact r42_tail_identity (((r42mc_rep _ _).natDegree_le (by decide +kernel)).trans
      (by decide +kernel))

theorem mass_reserve (f : Family) (i : Fin 15) :
    (29/50:ℚ)<(massCentered f i).coeff 0-
      PowerTailBounds.norm (massCentered f i) 1 11 (radius f) := by
  cases f <;> fin_cases i <;>
    exact r42_reserve_of_rep (r42mc_rep _ _) (by decide +kernel) _ _ _ (by decide +kernel)

theorem mass_lower (f : Family) (i : Fin 15) {z : ℝ}
    (hz : z∈Set.Icc (left f:ℝ) (right f:ℝ)) :
    (29/50:ℝ)<aeval z (mass f i) := by
  have hx : |z-(midpoint f:ℝ)|≤(radius f:ℝ) := by
    apply abs_le.mpr
    simp only [midpoint,radius]
    push_cast
    exact ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hb := DirectedPowerBounds.constant_lower (mass_identity f i) hx
  have hr := (Rat.cast_lt (K:=ℝ)).mpr (mass_reserve f i)
  push_cast at hr
  have he : aeval (z-(midpoint f:ℝ)) (massCentered f i)=aeval z (mass f i) := by
    simp [massCentered]
  rw [he] at hb
  linarith

theorem mass_positive (f : Family) (i : Fin 15) {z : ℝ}
    (hz : z∈Set.Icc (left f:ℝ) (right f:ℝ)) : 0<aeval z (mass f i) := by
  have hh := mass_lower f i hz
  linarith

theorem ordinary_masses_positive (f : Family) {z : ℝ}
    (hz : z∈Set.Icc (left f:ℝ) (right f:ℝ)) :
    0<aeval z (RH f) ∧ 0<aeval z (RG f) ∧ 0<aeval z (RB f) ∧
    0<aeval z (RD f) ∧ 0<aeval z (RHminus f) ∧
    0<aeval z (RGminus f) ∧ 0<aeval z (RBminus f) := by
  exact ⟨by simpa [mass] using mass_positive f 0 hz,
    by simpa [mass] using mass_positive f 1 hz,
    by simpa [mass] using mass_positive f 2 hz,
    by simpa [mass] using mass_positive f 3 hz,
    by simpa [mass] using mass_positive f 4 hz,
    by simpa [mass] using mass_positive f 5 hz,
    by simpa [mass] using mass_positive f 6 hz⟩

theorem equal_GA_masses_positive (f : Family) {z : ℝ}
    (hz : z∈Set.Icc (left f:ℝ) (right f:ℝ)) (i : Fin 4) :
    0<aeval z (equalGAR f i) := by
  fin_cases i
  · simpa [mass,equalGAR] using mass_positive f 7 hz
  · simpa [mass] using mass_positive f 8 hz
  · simpa [mass,equalGAR] using mass_positive f 9 hz
  · simpa [mass,equalGAR] using mass_positive f 10 hz

theorem equal_AB_masses_positive {z : ℝ}
    (hz : z∈Set.Icc (1/5:ℝ) (7/10:ℝ)) (i : Fin 4) :
    0<aeval z (equalABR i) := by
  have hz' : z∈Set.Icc (left .high:ℝ) (right .high:ℝ) := by
    norm_num [left,right,split,h]
    exact ⟨by linarith [hz.1],by linarith [hz.2]⟩
  fin_cases i
  · simpa [mass,equalABR] using mass_positive .high 7 hz'
  · simpa [mass,equalABR] using mass_positive .high 11 hz'
  · simpa [mass,equalABR] using mass_positive .high 12 hz'
  · simpa [mass,equalABR] using mass_positive .high 10 hz'

def cutMidpoint (e : Cut) : ℚ := (cutAngle e+h)/2
def cutRadius (e : Cut) : ℚ := (h-cutAngle e)/2
def cutMassCentered (e : Cut) (i : Fin 4) : ℚ[X] :=
  DirectedPowerBounds.shift (cutMidpoint e) (cutR e i)

private def r42cutR : Cut→Fin 4→Scaled
  | .gaH => ![r42cR0u .gaH,r42cR1g .gaH,r42cR2g .gaH,r42cR3 .gaH]
  | .gaB => ![r42cR0 .gaB,r42cR1g .gaB,r42cR2u .gaB,r42cR3 .gaB]
  | .abG => ![r42cR0 .abG,r42cR1u .abG,r42cR2a .abG,r42cR3 .abG]
  | .abH => ![r42cR0u .abH,r42cR1a .abH,r42cR2a .abH,r42cR3 .abH]
private theorem r42cutR_rep (e : Cut) (i : Fin 4) : (r42cutR e i).Rep (cutR e i) := by
  cases e <;> fin_cases i
  exacts [r42cR0u_rep .gaH,r42cR1g_rep .gaH,r42cR2g_rep .gaH,r42cR3_rep .gaH,
    r42cR0_rep .gaB,r42cR1g_rep .gaB,r42cR2u_rep .gaB,r42cR3_rep .gaB,
    r42cR0_rep .abG,r42cR1u_rep .abG,r42cR2a_rep .abG,r42cR3_rep .abG,
    r42cR0u_rep .abH,r42cR1a_rep .abH,r42cR2a_rep .abH,r42cR3_rep .abH]

private def r42cmc (e : Cut) (i : Fin 4) : Scaled :=
  if cutAtG e then (r42cutR e i).center 1 40 19 40 else (r42cutR e i).center 1 50 27 50
private theorem r42cmc_rep (e : Cut) (i : Fin 4) : (r42cmc e i).Rep (cutMassCentered e i) := by
  rcases hb : cutAtG e with _|_ <;> simp only [r42cmc,hb,Bool.false_eq_true,↓reduceIte]
  · exact r42_shift_rep (r42cutR_rep e i) 1 50 27 50 (by norm_num)
      (by norm_num [cutMidpoint,cutAngle,hb,h]) (by norm_num)
  · exact r42_shift_rep (r42cutR_rep e i) 1 40 19 40 (by norm_num)
      (by norm_num [cutMidpoint,cutAngle,hb,h]) (by norm_num)

theorem cut_mass_identity (e : Cut) (i : Fin 4) :
    cutMassCentered e i=C ((cutMassCentered e i).coeff 0)+
      tail (cutMassCentered e i) 1 8 := by
  cases e <;> fin_cases i <;>
    exact r42_tail_identity (((r42cmc_rep _ _).natDegree_le (by decide +kernel)).trans
      (by decide +kernel))

theorem cut_mass_reserve (e : Cut) (i : Fin 4) :
    (93/100:ℚ)<(cutMassCentered e i).coeff 0-
      PowerTailBounds.norm (cutMassCentered e i) 1 8 (cutRadius e) := by
  cases e <;> fin_cases i <;>
    exact r42_reserve_of_rep (r42cmc_rep _ _) (by decide +kernel) _ _ _ (by decide +kernel)

theorem cut_mass_lower (e : Cut) (i : Fin 4) {z : ℝ}
    (hz : z∈Set.Icc (cutAngle e:ℝ) (h:ℝ)) :
    (93/100:ℝ)<aeval z (cutR e i) := by
  have hh : ((h:ℚ):ℝ)=7/10 := by norm_num [h]
  rw [hh] at hz
  have hx : |z-(cutMidpoint e:ℝ)|≤(cutRadius e:ℝ) := by
    apply abs_le.mpr
    simp only [cutMidpoint,cutRadius]
    push_cast
    exact ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hb := DirectedPowerBounds.constant_lower (cut_mass_identity e i) hx
  have hr := (Rat.cast_lt (K:=ℝ)).mpr (cut_mass_reserve e i)
  push_cast at hr
  have he : aeval (z-(cutMidpoint e:ℝ)) (cutMassCentered e i)=aeval z (cutR e i) := by
    simp [cutMassCentered]
  rw [he] at hb
  linarith

theorem cut_masses_positive (e : Cut) {z : ℝ}
    (hz : z∈Set.Icc (cutAngle e:ℝ) (h:ℝ)) (i : Fin 4) :
    0<aeval z (cutR e i) := by
  have hh := cut_mass_lower e i hz
  linarith

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.Certificate
