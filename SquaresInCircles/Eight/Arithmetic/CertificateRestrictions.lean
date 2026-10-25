module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Rat.Star
public import SquaresInCircles.Eight.Owners.GA.Positive.TDPolynomialData
public import SquaresInCircles.Eight.Arithmetic.PolynomialCertificates
public import SquaresInCircles.Eight.Arithmetic.TwoVariablePolynomial

/-!
# Eight squares: exact restrictions of bivariate numerators to edges

A bivariate numerator is a ring expression in `X`, `C X`, rational scalars,
Taylor polynomials composed with bivariate arguments (`lift`), and cubic masses
(`cubicMass`). This module computes its restriction to an edge as a scaled
integer list of `PolynomialCertificates`, so that the univariate certificates
(`lowerOn`, `upperOn`, Chebyshev re-expansions, values at the endpoints) reduce
to integer computations that the kernel checks.

* Restrictions are ring homomorphisms `Bivar →+* ℚ[X]`: `yZero` (the edge
  `y = 0`), `xZero` (the edge `x = 0`), `onLine t` (the line `y = t x`) and
  `onCurve u v` (the curve `x = u(t)`, `y = v(t)`, e.g. an affine edge).
  `RepOn φ a p` says that the scaled list `a` represents `φ p`.
* Along the axes and the lines `y = ±x` the truncation in `cubicMass` commutes
  with the restriction (`hom_cubicMass`). Along any other curve the cubic mass
  is recovered from its restrictions to these four lines (`mixed_coeffs`,
  `rep_curveCubicMassS`).
* The tactics `build_rep_yZero`, `build_rep_xZero` and `build_rep_curve` build
  `RepOn φ ?a p` along the syntax of `p`, leaving integer side conditions
  (nonzero scales, positive constant terms) for `decide +kernel`.
* `reduceScaled` divides a scaled list by the gcd of its entries and scale, which
  keeps the integers small.
* `lower_cert`, `upper_cert`, `initial_cert`, `chord_cert`, `far_rep`,
  `far_slope_cert` and `quadratic_tail_cert` turn integer facts about a scaled
  list into the univariate certificate statements on an interval `[0,B]`,
  `B/2 = num/den`. Exact quotients by `X` and by `X(B-X)` are verified by a
  product identity of integer lists (`edge_div`); derivatives are computed
  from the list (`derivS`).
-/

@[expose] public section
noncomputable section
open Polynomial
namespace SquaresInCircles.Eight.CertificateRestrictions
open WholeIntervalPolynomial.Certificate TensorWholeIntervalPolynomial TwoVariablePolynomial

/-! ### Truncation and the restrictions to the axes -/

/-- Univariate truncation to degree three. -/
def truncCubic (q : ℚ[X]) : ℚ[X] :=
  C (q.coeff 0)+C (q.coeff 1)*X+C (q.coeff 2)*X^2+C (q.coeff 3)*X^3

theorem coeff_truncCubic (q : ℚ[X]) (n : ℕ) :
    (truncCubic q).coeff n=if n<4 then q.coeff n else 0 := by
  unfold truncCubic
  rcases n with _|_|_|_|n <;> simp [coeff_X,coeff_X_pow]

theorem hom_lift (φ : Bivar →+* ℚ[X]) (hφ : ∀ q : ℚ,φ (C (C q))=C q) (f : Bivar) (p : ℚ[X]) :
    φ (lift f p)=p.comp (φ f) := by
  have hc : φ.comp (Polynomial.C.comp Polynomial.C)=Polynomial.C := by
    ext q; simp [hφ]
  simp only [lift,coe_eval₂RingHom,Polynomial.hom_eval₂,hc]
  rfl

/-- Restriction to the edge `y = 0`. -/
def yZero : Bivar →+* ℚ[X] := Polynomial.mapRingHom (Polynomial.evalRingHom 0)

theorem baseY_eq_yZero (p : Bivar) : baseY p=yZero p := by
  unfold baseY TwoVariablePolynomial.restrict yZero
  rw [coe_mapRingHom,Polynomial.map]
  congr 1
  apply Polynomial.ringHom_ext
  · intro a; simp
  · simp

theorem yZero_C (q : ℚ) : yZero (C (C q))=C q := by simp [yZero]
theorem yZero_X : yZero X=X := by simp [yZero]
theorem yZero_CX : yZero (C X)=0 := by simp [yZero]

theorem yZero_coeff (p : Bivar) (n : ℕ) : (yZero p).coeff n=(p.coeff n).coeff 0 := by
  simp [yZero,coeff_map,coeff_zero_eq_eval_zero]

theorem yZero_truncate3 (p : Bivar) : yZero (truncate3 p)=truncCubic (yZero p) := by
  simp [truncate3,truncCubic,Fin.sum_univ_four,yZero,scalar,coeff_map,
    coeff_zero_eq_eval_zero]

theorem constant_eq_yZero (p : Bivar) : constant p=(yZero p).coeff 0 := by
  rw [yZero_coeff]; rfl

/-- Restriction to the edge `x = 0`. -/
def xZero : Bivar →+* ℚ[X] := Polynomial.constantCoeff

theorem baseX_eq_xZero (p : Bivar) : baseX p=xZero p := by
  unfold baseX TwoVariablePolynomial.restrict xZero
  rw [eval₂_at_zero,coe_eval₂RingHom,eval₂_C_X,constantCoeff_apply]

theorem xZero_C (q : ℚ) : xZero (C (C q) : Bivar)=C q := by simp [xZero]
theorem xZero_X : xZero (X : Bivar)=0 := by simp [xZero]
theorem xZero_CX : xZero (C X : Bivar)=X := by simp [xZero]

theorem xZero_coeff (p : Bivar) (n : ℕ) : (xZero p).coeff n=(p.coeff 0).coeff n := by
  simp [xZero,constantCoeff_apply]

theorem coeff_zero_CX_pow (n : ℕ) : ((C X : Bivar)^n).coeff 0=X^n := by
  rw [← C_pow,coeff_C_zero]

theorem xZero_truncate3 (p : Bivar) : xZero (truncate3 p)=truncCubic (xZero p) := by
  simp [xZero,truncate3,truncCubic,Fin.sum_univ_four,scalar,constantCoeff_apply,coeff_C,
    coeff_X_pow,coeff_zero_CX_pow]

theorem constant_eq_xZero (p : Bivar) : constant p=(xZero p).coeff 0 := by
  unfold xZero; rw [constantCoeff_apply]; rfl

/-- A restriction that commutes with `truncate3` maps a cubic mass to the cubic
mass of the restricted polynomial. -/
theorem hom_cubicMass (φ : Bivar →+* ℚ[X]) (hφ : ∀ q : ℚ,φ (C (C q))=C q)
    (hT : ∀ p,φ (truncate3 p)=truncCubic (φ p)) (h0 : ∀ p,constant p=(φ p).coeff 0)
    (rho : ℚ) (p : Bivar) :
    φ (cubicMass rho p)=C rho*truncCubic (1+C (1/2)*
      (C (1/(φ p).coeff 0)*(truncCubic (φ p)-C ((φ p).coeff 0)))-
      C (1/8)*(C (1/(φ p).coeff 0)*(truncCubic (φ p)-C ((φ p).coeff 0)))^2+
      C (1/16)*(C (1/(φ p).coeff 0)*(truncCubic (φ p)-C ((φ p).coeff 0)))^3) := by
  simp only [cubicMass,scalar,map_mul,map_add,map_sub,map_pow,map_one,hφ,hT,h0]

/-! ### Substitutions -/

theorem substitute_X (f g : Bivar) : substitute f g X=f := by simp [substitute]
theorem substitute_CX (f g : Bivar) : substitute f g (C X)=g := by simp [substitute,lift]
theorem substitute_scalar (f g : Bivar) (q : ℚ) : substitute f g (scalar q)=scalar q := by
  simp [substitute,lift,scalar]

theorem substitute_lift (f g u : Bivar) (p : ℚ[X]) :
    substitute f g (lift u p)=lift (substitute f g u) p := by
  have h : (substitute f g).comp (lift u)=lift (substitute f g u) := by
    apply Polynomial.ringHom_ext
    · intro a; simp [substitute,lift]
    · simp [lift]
  exact congrArg (fun F : ℚ[X] →+* Bivar => F p) h

theorem substitute_X_CX (p : Bivar) : substitute X (C X) p=p := by
  have h : substitute (X : Bivar) (C X)=RingHom.id Bivar := by
    apply Polynomial.ringHom_ext
    · intro a
      have hl : lift (C X : Bivar)=Polynomial.C := by
        apply Polynomial.ringHom_ext
        · intro b; simp [lift]
        · simp [lift]
      simp [substitute,hl]
    · simp [substitute]
  exact congrArg (fun F : Bivar →+* Bivar => F p) h

/-! ### Scaled lists of truncations and Taylor compositions -/

def takeCubic (a : Scaled) : Scaled := ⟨a.l.take 4,a.s⟩

theorem rep_takeCubic {a : Scaled} {q : ℚ[X]} (ha : a.Rep q) : (takeCubic a).Rep (truncCubic q) := by
  unfold Scaled.Rep at *
  ext n
  have h := congrArg (fun p => p.coeff n) ha
  simp only [coeff_toPoly,coeff_C_mul] at h
  simp only [takeCubic,coeff_toPoly,coeff_C_mul,coeff_truncCubic]
  split_ifs with hn
  · rw [← h]
    simp [List.getD_eq_getElem?_getD,hn]
  · simp [List.getD_eq_getElem?_getD,hn]

/-- The relative deviation `(trunc q - q(0))/q(0)` inside a cubic mass. -/
def massDeviationS (a : Scaled) : Scaled :=
  ⟨0 :: (a.l.drop 1).take 3,(a.l.headD 0).toNat⟩

theorem rep_massDeviationS {a : Scaled} {q : ℚ[X]} (ha : a.Rep q) (hs : a.s≠0)
    (hl : 0<a.l.headD 0) :
    (massDeviationS a).Rep (C (1/q.coeff 0)*(truncCubic q-C (q.coeff 0))) := by
  have hc := ha.coeff hs
  have hs' : (a.s:ℚ)≠0 := by exact_mod_cast hs
  have h0 : a.l.getD 0 0=a.l.headD 0 := by cases a.l <;> rfl
  have hl' : ((a.l.headD 0:ℤ):ℚ)≠0 := by exact_mod_cast hl.ne'
  unfold Scaled.Rep
  ext n
  simp only [massDeviationS,coeff_toPoly,coeff_C_mul,coeff_sub,coeff_C,coeff_truncCubic,hc,h0]
  have hnat : (((a.l.headD 0).toNat:ℕ):ℚ)=((a.l.headD 0:ℤ):ℚ) := by
    rw [show ((a.l.headD 0).toNat:ℚ)=(((a.l.headD 0).toNat:ℤ):ℚ) by norm_cast,
      Int.toNat_of_nonneg hl.le]
  rw [hnat]
  have hh : ((a.l.head?.getD 0:ℤ):ℚ)≠0 := by simpa using hl'
  have hg0 : a.l[0]?.getD 0=a.l.head?.getD 0 := by cases a.l <;> rfl
  rcases n with _|_|_|_|n
  · simp [hg0]
  · simp only [List.getD_eq_getElem?_getD,List.getElem?_cons_succ,List.getElem?_take,
      List.getElem?_drop]
    simp
    field_simp
  · simp only [List.getD_eq_getElem?_getD,List.getElem?_cons_succ,List.getElem?_take,
      List.getElem?_drop]
    simp
    field_simp
  · simp only [List.getD_eq_getElem?_getD,List.getElem?_cons_succ,List.getElem?_take,
      List.getElem?_drop]
    simp
    field_simp
  · simp [List.getD_eq_getElem?_getD]

theorem C10_comp (q : ℚ[X]) : GlobalGA.PositiveTD.Certificate.C10.comp q=
    1-C (1/2)*q^2+C (1/24)*q^4-C (1/720)*q^6+C (1/40320)*q^8-C (1/3628800)*q^10 := by
  simp only [GlobalGA.PositiveTD.Certificate.C10,GlobalGA.PositiveTD.Certificate.C4,sub_comp,add_comp,mul_comp,
    C_comp,pow_comp,X_comp,one_comp]

theorem C12_comp (q : ℚ[X]) : GlobalGA.PositiveTD.Certificate.C12.comp q=
    1-C (1/2)*q^2+C (1/24)*q^4-C (1/720)*q^6+C (1/40320)*q^8-C (1/3628800)*q^10+
      C (1/479001600)*q^12 := by
  simp only [GlobalGA.PositiveTD.Certificate.C12,GlobalGA.PositiveTD.Certificate.C10,GlobalGA.PositiveTD.Certificate.C4,
    sub_comp,add_comp,mul_comp,C_comp,pow_comp,X_comp,one_comp]

theorem S9_comp (q : ℚ[X]) : GlobalGA.PositiveTD.Certificate.S9.comp q=
    q-C (1/6)*q^3+C (1/120)*q^5-C (1/5040)*q^7+C (1/362880)*q^9 := by
  simp only [GlobalGA.PositiveTD.Certificate.S9,GlobalGA.PositiveTD.Certificate.S5,sub_comp,add_comp,mul_comp,
    C_comp,pow_comp,X_comp]

theorem S11_comp (q : ℚ[X]) : GlobalGA.PositiveTD.Certificate.S11.comp q=
    q-C (1/6)*q^3+C (1/120)*q^5-C (1/5040)*q^7+C (1/362880)*q^9-C (1/39916800)*q^11 := by
  simp only [GlobalGA.PositiveTD.Certificate.S11,GlobalGA.PositiveTD.Certificate.S9,GlobalGA.PositiveTD.Certificate.S5,
    sub_comp,add_comp,mul_comp,C_comp,pow_comp,X_comp]

def C10S (v : Scaled) : Scaled :=
  (((((Scaled.ofNat 1).sub ((Scaled.const (1/2)).mul (v.pow 2))).add
    ((Scaled.const (1/24)).mul (v.pow 4))).sub ((Scaled.const (1/720)).mul (v.pow 6))).add
    ((Scaled.const (1/40320)).mul (v.pow 8))).sub ((Scaled.const (1/3628800)).mul (v.pow 10))
def C12S (v : Scaled) : Scaled :=
  (C10S v).add ((Scaled.const (1/479001600)).mul (v.pow 12))
def S9S (v : Scaled) : Scaled :=
  (((v.sub ((Scaled.const (1/6)).mul (v.pow 3))).add ((Scaled.const (1/120)).mul (v.pow 5))).sub
    ((Scaled.const (1/5040)).mul (v.pow 7))).add ((Scaled.const (1/362880)).mul (v.pow 9))
def S11S (v : Scaled) : Scaled :=
  (S9S v).sub ((Scaled.const (1/39916800)).mul (v.pow 11))

theorem rep_C10S {v : Scaled} {q : ℚ[X]} (hv : v.Rep q) :
    (C10S v).Rep (GlobalGA.PositiveTD.Certificate.C10.comp q) := by
  rw [C10_comp]
  exact ((((Scaled.rep_one.sub ((Scaled.rep_const _).mul (hv.pow 2))).add
    ((Scaled.rep_const _).mul (hv.pow 4))).sub ((Scaled.rep_const _).mul (hv.pow 6))).add
    ((Scaled.rep_const _).mul (hv.pow 8))).sub ((Scaled.rep_const _).mul (hv.pow 10))
theorem rep_C12S {v : Scaled} {q : ℚ[X]} (hv : v.Rep q) :
    (C12S v).Rep (GlobalGA.PositiveTD.Certificate.C12.comp q) := by
  rw [C12_comp]
  exact (((((Scaled.rep_one.sub ((Scaled.rep_const _).mul (hv.pow 2))).add
    ((Scaled.rep_const _).mul (hv.pow 4))).sub ((Scaled.rep_const _).mul (hv.pow 6))).add
    ((Scaled.rep_const _).mul (hv.pow 8))).sub ((Scaled.rep_const _).mul (hv.pow 10))).add
    ((Scaled.rep_const _).mul (hv.pow 12))
theorem rep_S9S {v : Scaled} {q : ℚ[X]} (hv : v.Rep q) :
    (S9S v).Rep (GlobalGA.PositiveTD.Certificate.S9.comp q) := by
  rw [S9_comp]
  exact (((hv.sub ((Scaled.rep_const _).mul (hv.pow 3))).add
    ((Scaled.rep_const _).mul (hv.pow 5))).sub ((Scaled.rep_const _).mul (hv.pow 7))).add
    ((Scaled.rep_const _).mul (hv.pow 9))
theorem rep_S11S {v : Scaled} {q : ℚ[X]} (hv : v.Rep q) :
    (S11S v).Rep (GlobalGA.PositiveTD.Certificate.S11.comp q) := by
  rw [S11_comp]
  exact ((((hv.sub ((Scaled.rep_const _).mul (hv.pow 3))).add
    ((Scaled.rep_const _).mul (hv.pow 5))).sub ((Scaled.rep_const _).mul (hv.pow 7))).add
    ((Scaled.rep_const _).mul (hv.pow 9))).sub ((Scaled.rep_const _).mul (hv.pow 11))

/-- The cubic mass of a polynomial represented by `a`, along a restriction that
commutes with the truncation. -/
def cubicMassS (rho : ℚ) (a : Scaled) : Scaled :=
  (Scaled.const rho).mul (takeCubic ((((Scaled.ofNat 1).add
    ((Scaled.const (1/2)).mul (massDeviationS a))).sub
    ((Scaled.const (1/8)).mul ((massDeviationS a).pow 2))).add
    ((Scaled.const (1/16)).mul ((massDeviationS a).pow 3))))

/-! ### gcd normalization -/

/-- The gcd of `s` and the entries of a list. -/
def listGcd (s : ℕ) : List ℤ → ℕ
  | [] => s
  | a :: l => Nat.gcd a.natAbs (listGcd s l)

theorem listGcd_dvd (s : ℕ) : ∀ l : List ℤ,
    listGcd s l ∣ s ∧ ∀ a ∈ l,((listGcd s l : ℕ):ℤ) ∣ a
  | [] => by simp [listGcd]
  | a :: l => by
    obtain ⟨h1,h2⟩ := listGcd_dvd s l
    refine ⟨(Nat.gcd_dvd_right _ _).trans h1,?_⟩
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact Int.natCast_dvd.mpr (Nat.gcd_dvd_left _ _)
    · exact (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right _ _)).trans (h2 b hb)

theorem smul_map_ediv (g : ℤ) : ∀ l : List ℤ,(∀ a ∈ l,g ∣ a) →
    WholeIntervalPolynomial.Certificate.smul g (l.map (fun a => a/g))=l
  | [],_ => rfl
  | a :: l,h => by
    simp only [List.map_cons,WholeIntervalPolynomial.Certificate.smul]
    rw [Int.mul_ediv_cancel' (h a List.mem_cons_self),
      smul_map_ediv g l (fun b hb => h b (List.mem_cons_of_mem a hb))]

theorem toPoly_map_zero : ∀ l : List ℤ,toPoly (l.map (fun _ => (0:ℤ)))=0
  | [] => rfl
  | a :: l => by
    simp only [List.map_cons,toPoly,toPoly_map_zero l,Int.cast_zero,map_zero,mul_zero,add_zero]

/-- A scaled list divided by the gcd of its entries and its scale. -/
def reduceScaled (c : Scaled) : Scaled :=
  ⟨c.l.map (fun a => a/((listGcd c.s c.l : ℕ):ℤ)),c.s/listGcd c.s c.l⟩

theorem rep_reduceScaled {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) : (reduceScaled c).Rep p := by
  obtain ⟨h1,h2⟩ := listGcd_dvd c.s c.l
  set g := listGcd c.s c.l with hg
  have hl := smul_map_ediv (g:ℤ) c.l h2
  unfold Scaled.Rep at *
  rw [← hl,WholeIntervalPolynomial.Certificate.toPoly_smul] at hc
  obtain ⟨k,hk⟩ := h1
  simp only [reduceScaled,← hg]
  rcases Nat.eq_zero_or_pos g with h0 | hpos
  · have hs : c.s=0 := by rw [hk,h0,zero_mul]
    rw [h0,hs]
    simp only [Nat.cast_zero,Int.ediv_zero,Nat.zero_div,map_zero,zero_mul]
    exact toPoly_map_zero _
  · have hg0 : (g:ℚ)≠0 := by exact_mod_cast hpos.ne'
    rw [hk,Nat.mul_div_cancel_left k hpos]
    rw [hk] at hc
    push_cast at hc
    exact mul_left_cancel₀ (show C (g:ℚ)≠0 from C_ne_zero.mpr hg0)
      (hc.trans (by rw [map_mul,mul_assoc]))

/-! ### Representation through a restriction -/

/-- `a` represents the restriction `φ p`. -/
def RepOn (φ : Bivar →+* ℚ[X]) (a : Scaled) (p : Bivar) : Prop := a.Rep (φ p)

theorem RepOn.add {φ : Bivar →+* ℚ[X]} {a b : Scaled} {p q : Bivar}
    (ha : RepOn φ a p) (hb : RepOn φ b q) : RepOn φ (reduceScaled (a.add b)) (p+q) := by
  unfold RepOn at *; rw [map_add]; exact rep_reduceScaled (ha.add hb)
theorem RepOn.sub {φ : Bivar →+* ℚ[X]} {a b : Scaled} {p q : Bivar}
    (ha : RepOn φ a p) (hb : RepOn φ b q) : RepOn φ (reduceScaled (a.sub b)) (p-q) := by
  unfold RepOn at *; rw [map_sub]; exact rep_reduceScaled (ha.sub hb)
theorem RepOn.mul {φ : Bivar →+* ℚ[X]} {a b : Scaled} {p q : Bivar}
    (ha : RepOn φ a p) (hb : RepOn φ b q) : RepOn φ (reduceScaled (a.mul b)) (p*q) := by
  unfold RepOn at *; rw [map_mul]; exact rep_reduceScaled (ha.mul hb)
theorem RepOn.pow {φ : Bivar →+* ℚ[X]} {a : Scaled} {p : Bivar} (n : ℕ)
    (ha : RepOn φ a p) : RepOn φ (reduceScaled (a.pow n)) (p^n) := by
  unfold RepOn at *; rw [map_pow]; exact rep_reduceScaled (ha.pow n)
theorem RepOn.neg {φ : Bivar →+* ℚ[X]} {a : Scaled} {p : Bivar}
    (ha : RepOn φ a p) : RepOn φ a.neg (-p) := by
  unfold RepOn at *; rw [map_neg]; exact ha.neg
theorem RepOn.one {φ : Bivar →+* ℚ[X]} : RepOn φ (Scaled.ofNat 1) 1 := by
  unfold RepOn; rw [map_one]; exact Scaled.rep_one
theorem RepOn.zero {φ : Bivar →+* ℚ[X]} : RepOn φ ⟨[],1⟩ 0 := by
  unfold RepOn; rw [map_zero]; exact Scaled.rep_zero

theorem RepOn.yZero_scalar (q : ℚ) : RepOn yZero (Scaled.const q) (scalar q) := by
  unfold RepOn scalar; rw [yZero_C]; exact Scaled.rep_const q
theorem RepOn.xZero_scalar (q : ℚ) : RepOn xZero (Scaled.const q) (scalar q) := by
  unfold RepOn scalar; rw [xZero_C]; exact Scaled.rep_const q
theorem RepOn.yZero_X : RepOn yZero Scaled.var Polynomial.X := by
  unfold RepOn; rw [CertificateRestrictions.yZero_X]; exact Scaled.rep_var
theorem RepOn.xZero_X : RepOn xZero ⟨[],1⟩ Polynomial.X := by
  unfold RepOn; rw [CertificateRestrictions.xZero_X]; exact Scaled.rep_zero
theorem RepOn.yZero_CX : RepOn yZero ⟨[],1⟩ (Polynomial.C Polynomial.X) := by
  unfold RepOn; rw [CertificateRestrictions.yZero_CX]; exact Scaled.rep_zero
theorem RepOn.xZero_CX : RepOn xZero Scaled.var (Polynomial.C Polynomial.X) := by
  unfold RepOn; rw [CertificateRestrictions.xZero_CX]; exact Scaled.rep_var

theorem RepOn.yZero_liftC10 {v : Scaled} {f : Bivar} (hv : RepOn yZero v f) :
    RepOn yZero (reduceScaled (C10S v)) (lift f GlobalGA.PositiveTD.Certificate.C10) := by
  unfold RepOn at *; rw [hom_lift _ yZero_C]; exact rep_reduceScaled (rep_C10S hv)
theorem RepOn.yZero_liftC12 {v : Scaled} {f : Bivar} (hv : RepOn yZero v f) :
    RepOn yZero (reduceScaled (C12S v)) (lift f GlobalGA.PositiveTD.Certificate.C12) := by
  unfold RepOn at *; rw [hom_lift _ yZero_C]; exact rep_reduceScaled (rep_C12S hv)
theorem RepOn.yZero_liftS9 {v : Scaled} {f : Bivar} (hv : RepOn yZero v f) :
    RepOn yZero (reduceScaled (S9S v)) (lift f GlobalGA.PositiveTD.Certificate.S9) := by
  unfold RepOn at *; rw [hom_lift _ yZero_C]; exact rep_reduceScaled (rep_S9S hv)
theorem RepOn.yZero_liftS11 {v : Scaled} {f : Bivar} (hv : RepOn yZero v f) :
    RepOn yZero (reduceScaled (S11S v)) (lift f GlobalGA.PositiveTD.Certificate.S11) := by
  unfold RepOn at *; rw [hom_lift _ yZero_C]; exact rep_reduceScaled (rep_S11S hv)
theorem RepOn.xZero_liftC10 {v : Scaled} {f : Bivar} (hv : RepOn xZero v f) :
    RepOn xZero (reduceScaled (C10S v)) (lift f GlobalGA.PositiveTD.Certificate.C10) := by
  unfold RepOn at *; rw [hom_lift _ xZero_C]; exact rep_reduceScaled (rep_C10S hv)
theorem RepOn.xZero_liftC12 {v : Scaled} {f : Bivar} (hv : RepOn xZero v f) :
    RepOn xZero (reduceScaled (C12S v)) (lift f GlobalGA.PositiveTD.Certificate.C12) := by
  unfold RepOn at *; rw [hom_lift _ xZero_C]; exact rep_reduceScaled (rep_C12S hv)
theorem RepOn.xZero_liftS9 {v : Scaled} {f : Bivar} (hv : RepOn xZero v f) :
    RepOn xZero (reduceScaled (S9S v)) (lift f GlobalGA.PositiveTD.Certificate.S9) := by
  unfold RepOn at *; rw [hom_lift _ xZero_C]; exact rep_reduceScaled (rep_S9S hv)
theorem RepOn.xZero_liftS11 {v : Scaled} {f : Bivar} (hv : RepOn xZero v f) :
    RepOn xZero (reduceScaled (S11S v)) (lift f GlobalGA.PositiveTD.Certificate.S11) := by
  unfold RepOn at *; rw [hom_lift _ xZero_C]; exact rep_reduceScaled (rep_S11S hv)

theorem RepOn.yZero_cubicMass {a : Scaled} {p : Bivar} (rho : ℚ) (ha : RepOn yZero a p)
    (hs : a.s≠0) (hl : 0<a.l.headD 0) :
    RepOn yZero (reduceScaled (cubicMassS rho a)) (cubicMass rho p) := by
  unfold RepOn at *
  rw [hom_cubicMass yZero yZero_C yZero_truncate3 constant_eq_yZero]
  have hw := rep_massDeviationS ha hs hl
  refine rep_reduceScaled ?_
  exact (Scaled.rep_const rho).mul (rep_takeCubic ((((Scaled.rep_one).add
    ((Scaled.rep_const _).mul hw)).sub ((Scaled.rep_const _).mul (hw.pow 2))).add
    ((Scaled.rep_const _).mul (hw.pow 3))))
theorem RepOn.xZero_cubicMass {a : Scaled} {p : Bivar} (rho : ℚ) (ha : RepOn xZero a p)
    (hs : a.s≠0) (hl : 0<a.l.headD 0) :
    RepOn xZero (reduceScaled (cubicMassS rho a)) (cubicMass rho p) := by
  unfold RepOn at *
  rw [hom_cubicMass xZero xZero_C xZero_truncate3 constant_eq_xZero]
  have hw := rep_massDeviationS ha hs hl
  refine rep_reduceScaled ?_
  exact (Scaled.rep_const rho).mul (rep_takeCubic ((((Scaled.rep_one).add
    ((Scaled.rep_const _).mul hw)).sub ((Scaled.rep_const _).mul (hw.pow 2))).add
    ((Scaled.rep_const _).mul (hw.pow 3))))

/-- Builds `RepOn yZero ?a p` along the syntax of `p`. -/
macro "build_rep_yZero" : tactic => `(tactic| repeat' first
  | with_reducible apply RepOn.add
  | with_reducible apply RepOn.sub
  | with_reducible apply RepOn.pow
  | with_reducible apply RepOn.mul
  | with_reducible apply RepOn.neg
  | with_reducible apply RepOn.one
  | with_reducible apply RepOn.zero
  | with_reducible apply RepOn.yZero_scalar
  | with_reducible apply RepOn.yZero_X
  | with_reducible apply RepOn.yZero_CX
  | with_reducible apply RepOn.yZero_liftC10
  | with_reducible apply RepOn.yZero_liftC12
  | with_reducible apply RepOn.yZero_liftS9
  | with_reducible apply RepOn.yZero_liftS11
  | with_reducible apply RepOn.yZero_cubicMass)

/-- Builds `RepOn xZero ?a p` along the syntax of `p`. -/
macro "build_rep_xZero" : tactic => `(tactic| repeat' first
  | with_reducible apply RepOn.add
  | with_reducible apply RepOn.sub
  | with_reducible apply RepOn.pow
  | with_reducible apply RepOn.mul
  | with_reducible apply RepOn.neg
  | with_reducible apply RepOn.one
  | with_reducible apply RepOn.zero
  | with_reducible apply RepOn.xZero_scalar
  | with_reducible apply RepOn.xZero_X
  | with_reducible apply RepOn.xZero_CX
  | with_reducible apply RepOn.xZero_liftC10
  | with_reducible apply RepOn.xZero_liftC12
  | with_reducible apply RepOn.xZero_liftS9
  | with_reducible apply RepOn.xZero_liftS11
  | with_reducible apply RepOn.xZero_cubicMass)

/-! ### Univariate certificates on `[0,B]` from integer facts -/

theorem lt_div_of_int {n : ℤ} {dd : ℕ} {Z : ℤ} {s len : ℕ} (hdd : 0<dd) (hs : s≠0)
    (h : n*((s*2^len:ℕ):ℤ)<2*dd*Z) :
    (n/dd:ℚ)<(Z:ℚ)/(s*2^len/2) := by
  have hs0 : (0:ℚ)<s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hs' : (0:ℚ)<s*2^len/2 := by positivity
  have hd' : (0:ℚ)<dd := by exact_mod_cast hdd
  rw [div_lt_div_iff₀ hd' hs']
  have h' : (n:ℚ)*((s*2^len:ℕ):ℚ)<2*dd*Z := by exact_mod_cast h
  push_cast at h'
  linarith

theorem div_lt_of_int {n : ℤ} {dd : ℕ} {Z : ℤ} {s len : ℕ} (hdd : 0<dd) (hs : s≠0)
    (h : 2*dd*Z<n*((s*2^len:ℕ):ℤ)) :
    (Z:ℚ)/(s*2^len/2)<(n/dd:ℚ) := by
  have hs0 : (0:ℚ)<s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hs' : (0:ℚ)<s*2^len/2 := by positivity
  have hd' : (0:ℚ)<dd := by exact_mod_cast hdd
  rw [div_lt_div_iff₀ hs' hd']
  have h' : ((2*dd*Z:ℤ):ℚ)<((n*((s*2^len:ℕ):ℤ):ℤ):ℚ) := by exact_mod_cast h
  push_cast at h'
  linarith

/-- The centered polynomial on `[0,B]`, `B/2 = num/den`. -/
theorem rep_centered_zero {p : ℚ[X]} {a : Scaled} (ha : a.Rep p) (B : ℚ) (num den : ℕ)
    (hden : den≠0) (hB : B/2=num/den) :
    (a.center num den 1 1).Rep (WholeIntervalPolynomial.centered 0 B p) :=
  ha.centered num den 1 1 (a:=0) (b:=B) hden (by rw [zero_add,hB]; push_cast; ring)
    (by rw [sub_zero,hB]; push_cast; ring)

theorem lower_cert {p : ℚ[X]} {a : Scaled} (ha : a.Rep p) (B : ℚ) (num den : ℕ) (hden : den≠0)
    (hB : B/2=num/den) (D : ℕ) (q : ℚ) (n : ℤ) (dd : ℕ) (hq : q=n/dd) (hdd : 0<dd)
    (h : ((a.center num den 1 1).s≠0 ∧ (a.center num den 1 1).l.length≤D+1) ∧
      n*(((a.center num den 1 1).s*2^(a.center num den 1 1).l.length:ℕ):ℤ)<
        2*dd*lowerZ D (fun j => (chebList (a.center num den 1 1).l).getD j 0)) :
    WholeIntervalPolynomial.centered 0 B p=
      WholeIntervalPolynomial.expansion D (WholeIntervalPolynomial.centered 0 B p) ∧
    q<WholeIntervalPolynomial.lowerOn D 0 B p := by
  have hc := rep_centered_zero ha B num den hden hB
  refine ⟨hc.eq_expansion h.1.1 h.1.2,?_⟩
  rw [lowerOn_eq_of_rep hc h.1.1 h.1.2,hq]
  exact lt_div_of_int hdd h.1.1 h.2

theorem upper_cert {p : ℚ[X]} {a : Scaled} (ha : a.Rep p) (B : ℚ) (num den : ℕ) (hden : den≠0)
    (hB : B/2=num/den) (D : ℕ) (q : ℚ) (n : ℤ) (dd : ℕ) (hq : q=n/dd) (hdd : 0<dd)
    (h : ((a.center num den 1 1).s≠0 ∧ (a.center num den 1 1).l.length≤D+1) ∧
      2*dd*upperZ D (fun j => (chebList (a.center num den 1 1).l).getD j 0)<
        n*(((a.center num den 1 1).s*2^(a.center num den 1 1).l.length:ℕ):ℤ)) :
    WholeIntervalPolynomial.centered 0 B p=
      WholeIntervalPolynomial.expansion D (WholeIntervalPolynomial.centered 0 B p) ∧
    WholeIntervalPolynomial.upperOn D 0 B p<q := by
  have hc := rep_centered_zero ha B num den hden hB
  refine ⟨hc.eq_expansion h.1.1 h.1.2,?_⟩
  rw [upperOn_eq_of_rep hc h.1.1 h.1.2,hq]
  exact div_lt_of_int hdd h.1.1 h.2

theorem lt_eval_zero {p : ℚ[X]} {a : Scaled} (ha : a.Rep p) (q : ℚ) (n : ℤ) (dd : ℕ)
    (hq : q=n/dd) (hdd : 0<dd) (h : a.s≠0 ∧ n*(a.s:ℤ)<dd*a.l.headD 0) : q<p.eval 0 := by
  have hc := ha.coeff h.1 0
  have h0 : a.l.getD 0 0=a.l.headD 0 := by cases a.l <;> rfl
  rw [← coeff_zero_eq_eval_zero,hc,h0,hq]
  have hs0 : (0:ℚ)<a.s := by exact_mod_cast Nat.pos_of_ne_zero h.1
  have hd' : (0:ℚ)<dd := by exact_mod_cast hdd
  rw [div_lt_div_iff₀ hd' hs0]
  have h' : (n:ℚ)*(a.s:ℤ)<dd*a.l.headD 0 := by exact_mod_cast h.2
  push_cast at h'
  linarith

/-- A positive value at `0` and a lower bound for the slope `p.divX` on `[0,B]`. -/
theorem initial_cert {p : ℚ[X]} {a : Scaled} (ha : a.Rep p) (B : ℚ) (num den : ℕ)
    (hden : den≠0) (hB : B/2=num/den) (D : ℕ)
    (q₁ : ℚ) (n₁ : ℤ) (d₁ : ℕ) (hq₁ : q₁=n₁/d₁) (hd₁ : 0<d₁)
    (q₂ : ℚ) (n₂ : ℤ) (d₂ : ℕ) (hq₂ : q₂=n₂/d₂) (hd₂ : 0<d₂)
    (h : (a.s≠0 ∧ n₁*(a.s:ℤ)<d₁*a.l.headD 0) ∧
      ((a.divX.center num den 1 1).s≠0 ∧ (a.divX.center num den 1 1).l.length≤D+1) ∧
      n₂*(((a.divX.center num den 1 1).s*2^(a.divX.center num den 1 1).l.length:ℕ):ℤ)<
        2*d₂*lowerZ D (fun j => (chebList (a.divX.center num den 1 1).l).getD j 0)) :
    q₁<p.eval 0 ∧
    WholeIntervalPolynomial.centered 0 B p.divX=
      WholeIntervalPolynomial.expansion D (WholeIntervalPolynomial.centered 0 B p.divX) ∧
    q₂<WholeIntervalPolynomial.lowerOn D 0 B p.divX :=
  ⟨lt_eval_zero ha q₁ n₁ d₁ hq₁ hd₁ h.1,
    lower_cert ha.divX B num den hden hB D q₂ n₂ d₂ hq₂ hd₂ h.2⟩

theorem eval_one_toPoly : ∀ l : List ℤ,(toPoly l).eval 1=(l.sum:ℚ)
  | [] => by simp [toPoly]
  | a :: l => by simp [toPoly,eval_one_toPoly l]

/-- The value at the right endpoint `B`. -/
theorem eval_right {p : ℚ[X]} {a : Scaled} (ha : a.Rep p) (B : ℚ) (num den : ℕ)
    (hden : den≠0) (hB : B/2=num/den) (hs : (a.center num den 1 1).s≠0) :
    p.eval B=((a.center num den 1 1).l.sum:ℚ)/(a.center num den 1 1).s := by
  have hc := rep_centered_zero ha B num den hden hB
  have hs' : ((a.center num den 1 1).s:ℚ)≠0 := by exact_mod_cast hs
  have h1 := congrArg (fun q => q.eval 1) hc
  simp only [eval_one_toPoly,eval_mul,eval_C,WholeIntervalPolynomial.centered,eval_comp,
    WholeIntervalPolynomial.affine,eval_add,eval_X] at h1
  rw [h1,show (0+B)/2+(B-0)/2*1=B by ring]
  field_simp

theorem lt_eval_right {p : ℚ[X]} {a : Scaled} (ha : a.Rep p) (B : ℚ) (num den : ℕ)
    (hden : den≠0) (hB : B/2=num/den) (q : ℚ) (n : ℤ) (dd : ℕ) (hq : q=n/dd) (hdd : 0<dd)
    (h : (a.center num den 1 1).s≠0 ∧
      n*((a.center num den 1 1).s:ℤ)<dd*(a.center num den 1 1).l.sum) :
    q<p.eval B := by
  rw [eval_right ha B num den hden hB h.1,hq]
  have hc0 : (0:ℚ)<(a.center num den 1 1).s := by exact_mod_cast Nat.pos_of_ne_zero h.1
  have hd' : (0:ℚ)<dd := by exact_mod_cast hdd
  rw [div_lt_div_iff₀ hd' hc0]
  have h' : ((n*((a.center num den 1 1).s:ℤ):ℤ):ℚ)<
      ((dd*(a.center num den 1 1).l.sum:ℤ):ℚ) := by exact_mod_cast h.2
  simp only [Int.cast_mul,Int.cast_natCast] at h'
  linarith

/-! ### Exact quotients by `X(B-X)` and chords -/

/-- The scaled chord numerator `p - p(0) - ((p(B)-p(0))/B) X`, `B = 2 num/den`. -/
def chordNumeratorS (num den : ℕ) (a : Scaled) : Scaled :=
  (a.sub ⟨[a.l.headD 0],a.s⟩).sub
    ((⟨[den*((a.center num den 1 1).l.sum*a.s-a.l.headD 0*(a.center num den 1 1).s)],
      2*num*(a.center num den 1 1).s*a.s⟩ : Scaled).mul Scaled.var)

theorem rep_chordNumeratorS {p : ℚ[X]} {a : Scaled} (ha : a.Rep p) (B : ℚ) (num den : ℕ)
    (hnum : num≠0) (hden : den≠0) (hB : B/2=num/den) (hs : a.s≠0)
    (hc : (a.center num den 1 1).s≠0) :
    (chordNumeratorS num den a).Rep (p-C (p.eval 0)-C ((p.eval B-p.eval 0)/B)*X) := by
  have h0 : p.eval 0=(a.l.headD 0:ℚ)/a.s := by
    have h := ha.coeff hs 0
    have hh : a.l.getD 0 0=a.l.headD 0 := by cases a.l <;> rfl
    rw [← coeff_zero_eq_eval_zero,h,hh]
  have hd := eval_right ha B num den hden hB hc
  have hs' : (a.s:ℚ)≠0 := by exact_mod_cast hs
  have hc' : ((a.center num den 1 1).s:ℚ)≠0 := by exact_mod_cast hc
  have hn' : (num:ℚ)≠0 := by exact_mod_cast hnum
  have hd' : (den:ℚ)≠0 := by exact_mod_cast hden
  have hB' : B=2*num/den := by linear_combination 2*hB
  have hP : (⟨[a.l.headD 0],a.s⟩ : Scaled).Rep (C (p.eval 0)) := by
    unfold Scaled.Rep
    simp only [toPoly,mul_zero,add_zero,h0,← map_mul]
    congr 1
    field_simp
  have hQ : (⟨[den*((a.center num den 1 1).l.sum*a.s-a.l.headD 0*(a.center num den 1 1).s)],
      2*num*(a.center num den 1 1).s*a.s⟩ : Scaled).Rep (C ((p.eval B-p.eval 0)/B)) := by
    unfold Scaled.Rep
    rw [hd,h0]
    simp only [toPoly,mul_zero,add_zero,← map_mul]
    congr 1
    rw [hB']
    push_cast
    field_simp
  exact (ha.sub hP).sub (hQ.mul Scaled.rep_var)

/-- Candidate coefficients `P_1,…,P_m` of a quotient by `X(n-mX)`:
`P_1=-g_m`, `P_{j+1}=nP_j-m^j g_{m-j}`. -/
def edgeQuotientAux (n m : ℤ) : ℤ → ℕ → List ℤ → List ℤ
  | Q,_,[] => [Q]
  | Q,j,g :: rest => Q :: edgeQuotientAux n m (n*Q-m^j*g) (j+1) rest

/-- Candidate quotient of `f` by `X(B-X)`, `B = 2 num/den`; it is verified by a product
identity (`edge_div`). -/
def edgeQuotient (num den : ℕ) (f : Scaled) : Scaled :=
  let g := f.l.tail.reverse
  let Q := (edgeQuotientAux (2*num) den (-g.headD 0) 1 g.tail.dropLast).reverse
  ⟨Q.zipIdx.map (fun x => x.1*(den:ℤ)^x.2),f.s*den^(Q.length-1)⟩

theorem toPoly_edge (B : ℚ) (num den : ℕ) (hden : den≠0) (hB : B/2=num/den) :
    toPoly [0,2*num,-den]=C (den:ℚ)*(X*(C B-X)) := by
  have hd' : (den:ℚ)≠0 := by exact_mod_cast hden
  have hB' : (den:ℚ)*B=2*num := by field_simp at hB; linear_combination hB
  simp only [toPoly]
  rw [show C (den:ℚ)*(X*(C B-X))=C ((den:ℚ)*B)*X-C (den:ℚ)*X^2 by rw [map_mul]; ring,hB']
  push_cast
  simp only [map_zero,map_mul,map_neg,mul_zero,add_zero,zero_add]
  ring

theorem X_mul_sub_ne_zero (B : ℚ) : (X*(C B-X) : ℚ[X])≠0 := by
  refine mul_ne_zero X_ne_zero ?_
  intro h0
  have := congrArg (fun q => q.coeff 1) h0
  simp at this

theorem edge_div {f : ℚ[X]} {a b : Scaled} (B : ℚ) (num den : ℕ) (hden : den≠0)
    (hB : B/2=num/den) (ha : a.Rep f) (hs : a.s≠0) (hb : b.s≠0)
    (h : smul ((b.s:ℤ)*den) a.l=smul (a.s:ℤ) (mul b.l [0,2*num,-den])) :
    f/(X*(C B-X))=C (1/(b.s:ℚ))*toPoly b.l ∧ f=C (1/(b.s:ℚ))*toPoly b.l*(X*(C B-X)) := by
  have hD := X_mul_sub_ne_zero B
  have hs' : (a.s:ℚ)≠0 := by exact_mod_cast hs
  have hb' : (b.s:ℚ)≠0 := by exact_mod_cast hb
  have hd' : (den:ℚ)≠0 := by exact_mod_cast hden
  have h2 := congrArg toPoly h
  simp only [toPoly_smul,toPoly_mul,toPoly_edge B num den hden hB] at h2
  unfold Scaled.Rep at ha
  rw [ha] at h2
  have hf : f=C (1/(b.s:ℚ))*toPoly b.l*(X*(C B-X)) := by
    have hne : C ((b.s:ℚ)*den*a.s)≠0 := by
      rw [Ne,C_eq_zero]; exact mul_ne_zero (mul_ne_zero hb' hd') hs'
    apply mul_left_cancel₀ hne
    calc C ((b.s:ℚ)*den*a.s)*f=C ((b.s:ℚ)*den)*(C (a.s:ℚ)*f) := by
          simp only [map_mul]; ring
      _=C (a.s:ℚ)*(toPoly b.l*(C (den:ℚ)*(X*(C B-X)))) := by
          push_cast at h2 ⊢; linear_combination h2
      _=C ((b.s:ℚ)*(1/(b.s:ℚ))*den*a.s)*toPoly b.l*(X*(C B-X)) := by
          simp only [map_mul]
          rw [show C (b.s:ℚ)*C (1/(b.s:ℚ))=1 by rw [← map_mul,mul_one_div_cancel hb',map_one]]
          ring
      _=C ((b.s:ℚ)*den*a.s)*(C (1/(b.s:ℚ))*toPoly b.l*(X*(C B-X))) := by
          simp only [map_mul]; ring
  exact ⟨by rw [hf,mul_div_cancel_right₀ _ hD],hf⟩

theorem rep_self (b : Scaled) (hb : b.s≠0) : b.Rep (C (1/(b.s:ℚ))*toPoly b.l) := by
  have hb' : (b.s:ℚ)≠0 := by exact_mod_cast hb
  unfold Scaled.Rep
  rw [← mul_assoc,← map_mul,mul_one_div_cancel hb',map_one,one_mul]

/-- The chord decomposition `p = p(0) + ((p(B)-p(0))/B) X + X(B-X) Q` with the exact
quotient `Q`, positive values at both ends, and a lower bound for `Q` on `[0,B]`. -/
theorem chord_cert {p : ℚ[X]} {a : Scaled} (ha : a.Rep p) (B : ℚ) (num den : ℕ)
    (hnum : num≠0) (hden : den≠0) (hB : B/2=num/den) (D : ℕ)
    (q₀ : ℚ) (n₀ : ℤ) (d₀ : ℕ) (hq₀ : q₀=n₀/d₀) (hd₀ : 0<d₀)
    (q₁ : ℚ) (n₁ : ℤ) (d₁ : ℕ) (hq₁ : q₁=n₁/d₁) (hd₁ : 0<d₁)
    (h : (a.s≠0 ∧ (a.center num den 1 1).s≠0 ∧
        (edgeQuotient num den (chordNumeratorS num den a)).s≠0) ∧
      smul (((edgeQuotient num den (chordNumeratorS num den a)).s:ℤ)*den)
          (chordNumeratorS num den a).l=
        smul ((chordNumeratorS num den a).s:ℤ)
          (mul (edgeQuotient num den (chordNumeratorS num den a)).l [0,2*num,-den]) ∧
      (n₀*(a.s:ℤ)<d₀*a.l.headD 0 ∧
        n₀*((a.center num den 1 1).s:ℤ)<d₀*(a.center num den 1 1).l.sum) ∧
      (((edgeQuotient num den (chordNumeratorS num den a)).center num den 1 1).s≠0 ∧
        ((edgeQuotient num den (chordNumeratorS num den a)).center num den 1 1).l.length≤D+1) ∧
      n₁*((((edgeQuotient num den (chordNumeratorS num den a)).center num den 1 1).s*
        2^((edgeQuotient num den (chordNumeratorS num den a)).center num den 1 1).l.length:ℕ):ℤ)<
        2*d₁*lowerZ D (fun j =>
          (chebList ((edgeQuotient num den (chordNumeratorS num den a)).center num den 1 1).l).getD
            j 0)) :
    p=C (p.eval 0)+C ((p.eval B-p.eval 0)/B)*X+
      X*(C B-X)*((p-C (p.eval 0)-C ((p.eval B-p.eval 0)/B)*X)/(X*(C B-X))) ∧
    q₀<p.eval 0 ∧ q₀<p.eval B ∧
    WholeIntervalPolynomial.centered 0 B ((p-C (p.eval 0)-C ((p.eval B-p.eval 0)/B)*X)/(X*(C B-X)))=
      WholeIntervalPolynomial.expansion D
        (WholeIntervalPolynomial.centered 0 B ((p-C (p.eval 0)-C ((p.eval B-p.eval 0)/B)*X)/
          (X*(C B-X)))) ∧
    q₁<WholeIntervalPolynomial.lowerOn D 0 B
      ((p-C (p.eval 0)-C ((p.eval B-p.eval 0)/B)*X)/(X*(C B-X))) := by
  obtain ⟨⟨hs,hc,hq⟩,hid,⟨h0,hd⟩,hcert⟩ := h
  have hf := rep_chordNumeratorS ha B num den hnum hden hB hs hc
  have hfs : (chordNumeratorS num den a).s≠0 := by
    simp only [chordNumeratorS,Scaled.sub,Scaled.mul,Scaled.var]
    exact mul_ne_zero (mul_ne_zero hs hs) (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero two_ne_zero hnum) hc) hs) one_ne_zero)
  obtain ⟨hdiv,hmul⟩ := edge_div B num den hden hB hf hfs hq hid
  rw [hdiv]
  refine ⟨?_,lt_eval_zero ha _ n₀ d₀ hq₀ hd₀ ⟨hs,h0⟩,
    lt_eval_right ha B num den hden hB _ n₀ d₀ hq₀ hd₀ ⟨hc,hd⟩,
    lower_cert (rep_self _ hq) B num den hden hB D q₁ n₁ d₁ hq₁ hd₁ hcert⟩
  linear_combination hmul

/-! ### Lines through the origin -/

/-- Restriction to the line `y = t x`. -/
def onLine (t : ℚ) : Bivar →+* ℚ[X] :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom C (C t*X)) X

theorem onLine_coeff (t : ℚ) (p : Bivar) (m : ℕ) :
    (onLine t p).coeff m=∑ i ∈ Finset.range (m+1),(p.coeff i).coeff (m-i)*t^(m-i) := by
  have hn : p.natDegree<p.natDegree+(m+1) := by omega
  simp only [onLine,coe_eval₂RingHom]
  rw [eval₂_eq_sum_range' _ hn,finsetSum_coeff]
  simp only [coe_eval₂RingHom,coeff_mul_X_pow',← comp.eq_def,comp_C_mul_X_coeff]
  rw [add_comm,Finset.sum_range_add]
  have h2 : ∑ x ∈ Finset.range p.natDegree,
      (if m+1+x ≤ m then (p.coeff (m+1+x)).coeff (m-(m+1+x))*t^(m-(m+1+x)) else 0)=0 :=
    Finset.sum_eq_zero (fun x _ => by simp only [show ¬(m+1+x ≤ m) by omega,↓reduceIte])
  rw [h2,add_zero]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  simp only [show i ≤ m by simp at hi; omega,↓reduceIte]

theorem onLine_C (t q : ℚ) : onLine t (C (C q))=C q := by simp [onLine]
theorem onLine_X (t : ℚ) : onLine t X=X := by simp [onLine]
theorem onLine_CX (t : ℚ) : onLine t (C X)=C t*X := by simp [onLine]

theorem constant_eq_onLine (t : ℚ) (p : Bivar) : constant p=(onLine t p).coeff 0 := by
  rw [onLine_coeff]; simp [constant]

theorem truncate3_eq (p : Bivar) : truncate3 p=
    C (C ((p.coeff 0).coeff 0))+C (C ((p.coeff 1).coeff 0))*X+C (C ((p.coeff 2).coeff 0))*X^2+
    C (C ((p.coeff 3).coeff 0))*X^3+C (C ((p.coeff 0).coeff 1))*C X+
    C (C ((p.coeff 1).coeff 1))*X*C X+C (C ((p.coeff 2).coeff 1))*X^2*C X+
    C (C ((p.coeff 0).coeff 2))*C X^2+C (C ((p.coeff 1).coeff 2))*X*C X^2+
    C (C ((p.coeff 0).coeff 3))*C X^3 := by
  simp only [truncate3,Fin.sum_univ_four,scalar,Fin.isValue,
    Fin.coe_ofNat_eq_mod,Nat.reduceMod,Nat.reduceLeDiff,↓reduceIte,pow_zero,
    mul_one,pow_one,add_zero]
  ring

theorem onLine_truncate3 (t : ℚ) (p : Bivar) :
    onLine t (truncate3 p)=truncCubic (onLine t p) := by
  rw [truncate3_eq]
  simp only [truncCubic,onLine_coeff,Finset.sum_range_succ,Finset.sum_range_zero,map_add,
    map_mul,map_pow,onLine_C,onLine_X,onLine_CX,Nat.sub_self,Nat.reduceSub,pow_zero,
    mul_one,zero_add,pow_one]
  ring

/-! ### Restrictions to curves -/

/-- Restriction to the curve `x = u`, `y = v`. -/
def onCurve (u v : ℚ[X]) : Bivar →+* ℚ[X] :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom C v) u

theorem onCurve_C (u v : ℚ[X]) (q : ℚ) : onCurve u v (C (C q))=C q := by simp [onCurve]
theorem onCurve_X (u v : ℚ[X]) : onCurve u v X=u := by simp [onCurve]
theorem onCurve_CX (u v : ℚ[X]) : onCurve u v (C X)=v := by simp [onCurve]
theorem restrict_eq_onCurve (p : Bivar) (u v : ℚ[X]) : restrict p u v=onCurve u v p := rfl

theorem onCurve_truncate3 (u v : ℚ[X]) (p : Bivar) : onCurve u v (truncate3 p)=
    C ((p.coeff 0).coeff 0)+C ((p.coeff 1).coeff 0)*u+C ((p.coeff 2).coeff 0)*u^2+
    C ((p.coeff 3).coeff 0)*u^3+C ((p.coeff 0).coeff 1)*v+
    C ((p.coeff 1).coeff 1)*u*v+C ((p.coeff 2).coeff 1)*u^2*v+
    C ((p.coeff 0).coeff 2)*v^2+C ((p.coeff 1).coeff 2)*u*v^2+
    C ((p.coeff 0).coeff 3)*v^3 := by
  rw [truncate3_eq]
  simp only [map_add,map_mul,map_pow,onCurve_C,onCurve_X,onCurve_CX]

/-- The mixed coefficients of total degree at most three, from the restrictions to
the axes and to the lines `y = ±x`. -/
theorem mixed_coeffs (Q : Bivar) :
    (Q.coeff 1).coeff 1=(onLine 1 Q).coeff 2-(yZero Q).coeff 2-(xZero Q).coeff 2 ∧
    (Q.coeff 2).coeff 1=((onLine 1 Q).coeff 3-(onLine (-1) Q).coeff 3)/2-(xZero Q).coeff 3 ∧
    (Q.coeff 1).coeff 2=((onLine 1 Q).coeff 3+(onLine (-1) Q).coeff 3)/2-(yZero Q).coeff 3 := by
  simp only [onLine_coeff,yZero_coeff,xZero_coeff,Finset.sum_range_succ,
    Finset.sum_range_zero,Nat.sub_self,Nat.reduceSub,pow_zero,pow_one,zero_add]
  refine ⟨by ring,by ring,by ring⟩

/-- The polynomial truncated in `cubicMass`. -/
def cubicMassInner (P : Bivar) : Bivar :=
  1+scalar (1/2)*(scalar (1/constant P)*(truncate3 P-scalar (constant P)))-
    scalar (1/8)*(scalar (1/constant P)*(truncate3 P-scalar (constant P)))^2+
    scalar (1/16)*(scalar (1/constant P)*(truncate3 P-scalar (constant P)))^3

theorem cubicMass_eq_inner (rho : ℚ) (P : Bivar) :
    cubicMass rho P=scalar rho*truncate3 (cubicMassInner P) := rfl

theorem hom_cubicMassInner (φ : Bivar →+* ℚ[X]) (hφ : ∀ q : ℚ,φ (C (C q))=C q)
    (hT : ∀ p,φ (truncate3 p)=truncCubic (φ p)) (h0 : ∀ p,constant p=(φ p).coeff 0)
    (P : Bivar) :
    φ (cubicMassInner P)=1+C (1/2)*
      (C (1/(φ P).coeff 0)*(truncCubic (φ P)-C ((φ P).coeff 0)))-
      C (1/8)*(C (1/(φ P).coeff 0)*(truncCubic (φ P)-C ((φ P).coeff 0)))^2+
      C (1/16)*(C (1/(φ P).coeff 0)*(truncCubic (φ P)-C ((φ P).coeff 0)))^3 := by
  simp only [cubicMassInner,scalar,map_mul,map_add,map_sub,map_pow,map_one,hφ,hT,h0]

def cubicMassInnerS (a : Scaled) : Scaled :=
  reduceScaled ((((Scaled.ofNat 1).add ((Scaled.const (1/2)).mul (massDeviationS a))).sub
    ((Scaled.const (1/8)).mul ((massDeviationS a).pow 2))).add
    ((Scaled.const (1/16)).mul ((massDeviationS a).pow 3)))

theorem rep_cubicMassInnerS {a : Scaled} {q : ℚ[X]} (ha : a.Rep q) (hs : a.s≠0)
    (hl : 0<a.l.headD 0) :
    (cubicMassInnerS a).Rep (1+C (1/2)*(C (1/q.coeff 0)*(truncCubic q-C (q.coeff 0)))-
      C (1/8)*(C (1/q.coeff 0)*(truncCubic q-C (q.coeff 0)))^2+
      C (1/16)*(C (1/q.coeff 0)*(truncCubic q-C (q.coeff 0)))^3) := by
  have hw := rep_massDeviationS ha hs hl
  exact rep_reduceScaled ((((Scaled.rep_one).add ((Scaled.rep_const _).mul hw)).sub
    ((Scaled.rep_const _).mul (hw.pow 2))).add ((Scaled.rep_const _).mul (hw.pow 3)))

/-- The constant `C (R.coeff k)` of a represented polynomial. -/
def coeffS (R : Scaled) (k : ℕ) : Scaled := ⟨[R.l.getD k 0],R.s⟩

theorem rep_coeffS {R : Scaled} {q : ℚ[X]} (hR : R.Rep q) (hs : R.s≠0) (k : ℕ) :
    (coeffS R k).Rep (C (q.coeff k)) := by
  have hc := hR.coeff hs k
  have hs' : (R.s:ℚ)≠0 := by exact_mod_cast hs
  unfold Scaled.Rep
  simp only [coeffS,toPoly,mul_zero,add_zero,hc,← map_mul]
  congr 1
  field_simp

/-- The restriction of a cubic mass to the curve `x = U`, `y = V`, from the restrictions
of its inner polynomial to the axes and to the lines `y = ±x`. -/
def curveCubicMassS (rho : ℚ) (QY QX Q1 Qm U V : Scaled) : Scaled :=
  let c00 := coeffS QY 0
  let c10 := coeffS QY 1
  let c20 := coeffS QY 2
  let c30 := coeffS QY 3
  let c01 := coeffS QX 1
  let c02 := coeffS QX 2
  let c03 := coeffS QX 3
  let c11 := ((coeffS Q1 2).sub (coeffS QY 2)).sub (coeffS QX 2)
  let c21 := ((Scaled.const (1/2)).mul ((coeffS Q1 3).sub (coeffS Qm 3))).sub (coeffS QX 3)
  let c12 := ((Scaled.const (1/2)).mul ((coeffS Q1 3).add (coeffS Qm 3))).sub (coeffS QY 3)
  reduceScaled ((Scaled.const rho).mul ((((((((((c00).add (c10.mul U)).add
    (c20.mul (U.pow 2))).add (c30.mul (U.pow 3))).add (c01.mul V)).add (c11.mul (U.mul V))).add
    (c21.mul ((U.pow 2).mul V))).add (c02.mul (V.pow 2))).add (c12.mul (U.mul (V.pow 2)))).add
    (c03.mul (V.pow 3))))

theorem rep_curveCubicMassS {rho : ℚ} {P : Bivar} {QY QX Q1 Qm U V : Scaled} {u v : ℚ[X]}
    (hY : QY.Rep (yZero (cubicMassInner P))) (hX : QX.Rep (xZero (cubicMassInner P)))
    (h1 : Q1.Rep (onLine 1 (cubicMassInner P))) (hm : Qm.Rep (onLine (-1) (cubicMassInner P)))
    (hs : QY.s≠0 ∧ QX.s≠0 ∧ Q1.s≠0 ∧ Qm.s≠0) (hU : U.Rep u) (hV : V.Rep v) :
    (curveCubicMassS rho QY QX Q1 Qm U V).Rep (onCurve u v (cubicMass rho P)) := by
  obtain ⟨sY,sX,s1,sm⟩ := hs
  obtain ⟨r11,r21,r12⟩ := mixed_coeffs (cubicMassInner P)
  set yq := yZero (cubicMassInner P)
  set xq := xZero (cubicMassInner P)
  set q1 := onLine 1 (cubicMassInner P)
  set qm := onLine (-1) (cubicMassInner P)
  have h00 := rep_coeffS hY sY 0
  have h10 := rep_coeffS hY sY 1
  have h20 := rep_coeffS hY sY 2
  have h30 := rep_coeffS hY sY 3
  have h01 := rep_coeffS hX sX 1
  have h02 := rep_coeffS hX sX 2
  have h03 := rep_coeffS hX sX 3
  have h11 := ((rep_coeffS h1 s1 2).sub (rep_coeffS hY sY 2)).sub (rep_coeffS hX sX 2)
  have h21 := ((Scaled.rep_const (1/2)).mul ((rep_coeffS h1 s1 3).sub (rep_coeffS hm sm 3))).sub
    (rep_coeffS hX sX 3)
  have h12 := ((Scaled.rep_const (1/2)).mul ((rep_coeffS h1 s1 3).add (rep_coeffS hm sm 3))).sub
    (rep_coeffS hY sY 3)
  set A00 := C (yq.coeff 0)
  set A10 := C (yq.coeff 1)
  set A20 := C (yq.coeff 2)
  set A30 := C (yq.coeff 3)
  set A01 := C (xq.coeff 1)
  set A02 := C (xq.coeff 2)
  set A03 := C (xq.coeff 3)
  set A11 := C (q1.coeff 2)-C (yq.coeff 2)-C (xq.coeff 2)
  set A21 := C (1/2)*(C (q1.coeff 3)-C (qm.coeff 3))-C (xq.coeff 3)
  set A12 := C (1/2)*(C (q1.coeff 3)+C (qm.coeff 3))-C (yq.coeff 3)
  have e : onCurve u v (cubicMass rho P)=C rho*(A00+A10*u+A20*u^2+A30*u^3+A01*v+A11*(u*v)+
      A21*(u^2*v)+A02*v^2+A12*(u*v^2)+A03*v^3) := by
    rw [cubicMass_eq_inner,map_mul,scalar,onCurve_C,onCurve_truncate3,r11,r21,r12]
    simp only [A00,A10,A20,A30,A01,A02,A03,A11,A21,A12,yq,xq,q1,qm,yZero_coeff,
      xZero_coeff,div_eq_mul_inv,map_sub,map_add,map_mul,map_one]
    ring
  rw [e]
  exact rep_reduceScaled ((Scaled.rep_const rho).mul ((((((((((h00).add (h10.mul hU)).add
    (h20.mul (hU.pow 2))).add (h30.mul (hU.pow 3))).add (h01.mul hV)).add
    (h11.mul (hU.mul hV))).add (h21.mul ((hU.pow 2).mul hV))).add (h02.mul (hV.pow 2))).add
    (h12.mul (hU.mul (hV.pow 2)))).add (h03.mul (hV.pow 3))))

theorem RepOn.line_scalar (t q : ℚ) : RepOn (onLine t) (Scaled.const q) (scalar q) := by
  unfold RepOn scalar; rw [onLine_C]; exact Scaled.rep_const q
theorem RepOn.line_X (t : ℚ) : RepOn (onLine t) Scaled.var Polynomial.X := by
  unfold RepOn; rw [onLine_X]; exact Scaled.rep_var
theorem RepOn.line_CX (t : ℚ) :
    RepOn (onLine t) ((Scaled.const t).mul Scaled.var) (Polynomial.C Polynomial.X) := by
  unfold RepOn; rw [onLine_CX]; exact (Scaled.rep_const t).mul Scaled.rep_var
theorem RepOn.line_cubicMass {t : ℚ} {a : Scaled} {p : Bivar} (rho : ℚ)
    (ha : RepOn (onLine t) a p) (hs : a.s≠0) (hl : 0<a.l.headD 0) :
    RepOn (onLine t) (reduceScaled (cubicMassS rho a)) (cubicMass rho p) := by
  unfold RepOn at *
  rw [hom_cubicMass (onLine t) (onLine_C t) (onLine_truncate3 t) (constant_eq_onLine t)]
  have hw := rep_massDeviationS ha hs hl
  refine rep_reduceScaled ?_
  exact (Scaled.rep_const rho).mul (rep_takeCubic ((((Scaled.rep_one).add
    ((Scaled.rep_const _).mul hw)).sub ((Scaled.rep_const _).mul (hw.pow 2))).add
    ((Scaled.rep_const _).mul (hw.pow 3))))
theorem RepOn.curve_scalar (u v : ℚ[X]) (q : ℚ) :
    RepOn (onCurve u v) (Scaled.const q) (scalar q) := by
  unfold RepOn scalar; rw [onCurve_C]; exact Scaled.rep_const q
theorem RepOn.curve_X {u v : ℚ[X]} {U : Scaled} (hU : U.Rep u) :
    RepOn (onCurve u v) U Polynomial.X := by
  unfold RepOn; rw [onCurve_X]; exact hU
theorem RepOn.curve_CX {u v : ℚ[X]} {V : Scaled} (hV : V.Rep v) :
    RepOn (onCurve u v) V (Polynomial.C Polynomial.X) := by
  unfold RepOn; rw [onCurve_CX]; exact hV
theorem RepOn.curve_cubicMass {u v : ℚ[X]} {U V : Scaled} (hU : U.Rep u) (hV : V.Rep v)
    {aY aX a1 am : Scaled} {P : Bivar} (rho : ℚ)
    (hY : RepOn yZero aY P) (hX : RepOn xZero aX P)
    (h1 : RepOn (onLine 1) a1 P) (hm : RepOn (onLine (-1)) am P)
    (hc : ((aY.s≠0 ∧ 0<aY.l.headD 0) ∧ (aX.s≠0 ∧ 0<aX.l.headD 0) ∧
      (a1.s≠0 ∧ 0<a1.l.headD 0) ∧ (am.s≠0 ∧ 0<am.l.headD 0)) ∧
      ((cubicMassInnerS aY).s≠0 ∧ (cubicMassInnerS aX).s≠0 ∧ (cubicMassInnerS a1).s≠0 ∧
        (cubicMassInnerS am).s≠0)) :
    RepOn (onCurve u v)
      (curveCubicMassS rho (cubicMassInnerS aY) (cubicMassInnerS aX) (cubicMassInnerS a1)
        (cubicMassInnerS am) U V)
      (cubicMass rho P) := by
  unfold RepOn at *
  obtain ⟨⟨⟨sY,lY⟩,⟨sX,lX⟩,⟨s1,l1⟩,⟨sm,lm⟩⟩,hs⟩ := hc
  have qY := rep_cubicMassInnerS hY sY lY
  have qX := rep_cubicMassInnerS hX sX lX
  have q1 := rep_cubicMassInnerS h1 s1 l1
  have qm := rep_cubicMassInnerS hm sm lm
  rw [← hom_cubicMassInner yZero yZero_C yZero_truncate3 constant_eq_yZero] at qY
  rw [← hom_cubicMassInner xZero xZero_C xZero_truncate3 constant_eq_xZero] at qX
  rw [← hom_cubicMassInner (onLine 1) (onLine_C 1) (onLine_truncate3 1)
    (constant_eq_onLine 1)] at q1
  rw [← hom_cubicMassInner (onLine (-1)) (onLine_C (-1)) (onLine_truncate3 (-1))
    (constant_eq_onLine (-1))] at qm
  exact rep_curveCubicMassS qY qX q1 qm hs hU hV

theorem RepOn.line_liftC10 {t : ℚ} {v : Scaled} {f : Bivar} (hv : RepOn (onLine t) v f) :
    RepOn (onLine t) (reduceScaled (C10S v)) (lift f GlobalGA.PositiveTD.Certificate.C10) := by
  unfold RepOn at *; rw [hom_lift _ (onLine_C t)]; exact rep_reduceScaled (rep_C10S hv)
theorem RepOn.line_liftC12 {t : ℚ} {v : Scaled} {f : Bivar} (hv : RepOn (onLine t) v f) :
    RepOn (onLine t) (reduceScaled (C12S v)) (lift f GlobalGA.PositiveTD.Certificate.C12) := by
  unfold RepOn at *; rw [hom_lift _ (onLine_C t)]; exact rep_reduceScaled (rep_C12S hv)
theorem RepOn.line_liftS9 {t : ℚ} {v : Scaled} {f : Bivar} (hv : RepOn (onLine t) v f) :
    RepOn (onLine t) (reduceScaled (S9S v)) (lift f GlobalGA.PositiveTD.Certificate.S9) := by
  unfold RepOn at *; rw [hom_lift _ (onLine_C t)]; exact rep_reduceScaled (rep_S9S hv)
theorem RepOn.line_liftS11 {t : ℚ} {v : Scaled} {f : Bivar} (hv : RepOn (onLine t) v f) :
    RepOn (onLine t) (reduceScaled (S11S v)) (lift f GlobalGA.PositiveTD.Certificate.S11) := by
  unfold RepOn at *; rw [hom_lift _ (onLine_C t)]; exact rep_reduceScaled (rep_S11S hv)
theorem RepOn.curve_liftC10 {u v : ℚ[X]} {w : Scaled} {f : Bivar}
    (hv : RepOn (onCurve u v) w f) :
    RepOn (onCurve u v) (reduceScaled (C10S w)) (lift f GlobalGA.PositiveTD.Certificate.C10) := by
  unfold RepOn at *; rw [hom_lift _ (onCurve_C u v)]; exact rep_reduceScaled (rep_C10S hv)
theorem RepOn.curve_liftC12 {u v : ℚ[X]} {w : Scaled} {f : Bivar}
    (hv : RepOn (onCurve u v) w f) :
    RepOn (onCurve u v) (reduceScaled (C12S w)) (lift f GlobalGA.PositiveTD.Certificate.C12) := by
  unfold RepOn at *; rw [hom_lift _ (onCurve_C u v)]; exact rep_reduceScaled (rep_C12S hv)
theorem RepOn.curve_liftS9 {u v : ℚ[X]} {w : Scaled} {f : Bivar}
    (hv : RepOn (onCurve u v) w f) :
    RepOn (onCurve u v) (reduceScaled (S9S w)) (lift f GlobalGA.PositiveTD.Certificate.S9) := by
  unfold RepOn at *; rw [hom_lift _ (onCurve_C u v)]; exact rep_reduceScaled (rep_S9S hv)
theorem RepOn.curve_liftS11 {u v : ℚ[X]} {w : Scaled} {f : Bivar}
    (hv : RepOn (onCurve u v) w f) :
    RepOn (onCurve u v) (reduceScaled (S11S w)) (lift f GlobalGA.PositiveTD.Certificate.S11) := by
  unfold RepOn at *; rw [hom_lift _ (onCurve_C u v)]; exact rep_reduceScaled (rep_S11S hv)

/-- Builds `RepOn (onCurve u v) ?a p` along the syntax of `p`, with `hU : U.Rep u` and
`hV : V.Rep v` in the context; the cubic masses go through the four line restrictions. -/
macro "build_rep_curve" : tactic => `(tactic| repeat' first
  | with_reducible apply RepOn.add
  | with_reducible apply RepOn.sub
  | with_reducible apply RepOn.pow
  | with_reducible apply RepOn.mul
  | with_reducible apply RepOn.neg
  | with_reducible apply RepOn.one
  | with_reducible apply RepOn.zero
  | with_reducible apply RepOn.yZero_scalar
  | with_reducible apply RepOn.yZero_X
  | with_reducible apply RepOn.yZero_CX
  | with_reducible apply RepOn.yZero_liftC10
  | with_reducible apply RepOn.yZero_liftC12
  | with_reducible apply RepOn.yZero_liftS9
  | with_reducible apply RepOn.yZero_liftS11
  | with_reducible apply RepOn.yZero_cubicMass
  | with_reducible apply RepOn.xZero_scalar
  | with_reducible apply RepOn.xZero_X
  | with_reducible apply RepOn.xZero_CX
  | with_reducible apply RepOn.xZero_liftC10
  | with_reducible apply RepOn.xZero_liftC12
  | with_reducible apply RepOn.xZero_liftS9
  | with_reducible apply RepOn.xZero_liftS11
  | with_reducible apply RepOn.xZero_cubicMass
  | with_reducible apply RepOn.line_scalar
  | with_reducible apply RepOn.line_X
  | with_reducible apply RepOn.line_CX
  | with_reducible apply RepOn.line_liftC10
  | with_reducible apply RepOn.line_liftC12
  | with_reducible apply RepOn.line_liftS9
  | with_reducible apply RepOn.line_liftS11
  | with_reducible apply RepOn.line_cubicMass
  | with_reducible apply RepOn.curve_scalar
  | with_reducible apply RepOn.curve_liftC10
  | with_reducible apply RepOn.curve_liftC12
  | with_reducible apply RepOn.curve_liftS9
  | with_reducible apply RepOn.curve_liftS11
  | (with_reducible apply RepOn.curve_X; assumption)
  | (with_reducible apply RepOn.curve_CX; assumption)
  | (with_reducible apply RepOn.curve_cubicMass (by assumption) (by assumption)))

/-! ### The far edge `x + y = B` through `divY` -/

theorem onCurve_swap (u v : ℚ[X]) (Z : Bivar) : onCurve u v (swap Z)=onCurve v u Z := by
  have h : (onCurve u v).comp (substitute (C X) X)=onCurve v u := by
    apply Polynomial.ringHom_ext
    · intro a
      induction a using Polynomial.induction_on' with
      | add p q hp hq => simp only [map_add] at hp hq ⊢; rw [hp,hq]
      | monomial n c =>
        simp [substitute,lift,onCurve,← C_mul_X_pow_eq_monomial,eval₂_mul,eval₂_pow,eval₂_C]
    · simp [substitute,lift,onCurve]
  exact congrArg (fun F : Bivar →+* ℚ[X] => F Z) h

theorem swap_coeff_zero (Z : Bivar) : (swap Z).coeff 0=yZero Z := by
  have h : (Polynomial.constantCoeff).comp (substitute (C X) X)=yZero := by
    apply Polynomial.ringHom_ext
    · intro a
      induction a using Polynomial.induction_on' with
      | add p q hp hq => simp only [map_add] at hp hq ⊢; rw [hp,hq]
      | monomial n c =>
        simp [substitute,lift,yZero,← C_mul_X_pow_eq_monomial,eval₂_mul,eval₂_pow,eval₂_C]
        rcases n with _|n <;> simp
    · simp [substitute,lift,yZero]
  have := congrArg (fun F : Bivar →+* ℚ[X] => F Z) h
  simpa [constantCoeff_apply,swap] using this

/-- Restriction to the far edge of the triangle `x + y ≤ B`, through `divY`. -/
theorem far_identity (B : ℚ) (N : Bivar) :
    onCurve X (C B-X) N=(C B-X)*restrict (divY N) X (C B-X)+yZero N := by
  rw [restrict_eq_onCurve,divY,onCurve_swap,← onCurve_swap (C B-X) X N]
  conv_lhs => rw [← Polynomial.X_mul_divX_add (swap N)]
  rw [map_add,map_mul,onCurve_X,swap_coeff_zero]
  simp [onCurve]

theorem rep_X_mul {a : Scaled} {p : ℚ[X]} (ha : a.Rep p) :
    (⟨0 :: a.l,a.s⟩ : Scaled).Rep (X*p) := by
  unfold Scaled.Rep at *
  simp only [toPoly,Int.cast_zero,map_zero,zero_add,ha]
  ring

/-- The restriction of `divY N` to the far edge `y = B - x`, from the restrictions of `N` to
that edge and to `y = 0`; the quotient by `X(B-X)` is checked by a product identity. -/
theorem far_rep {N : Bivar} {Ψ Bs : Scaled} (B : ℚ) (num den : ℕ) (hden : den≠0)
    (hB : B/2=num/den) (hΨ : RepOn (onCurve X (C B-X)) Ψ N) (hBs : RepOn yZero Bs N)
    (h : (reduceScaled (Ψ.sub Bs)).s≠0 ∧
      (edgeQuotient num den ⟨0 :: (reduceScaled (Ψ.sub Bs)).l,(reduceScaled (Ψ.sub Bs)).s⟩).s≠0 ∧
      smul (((edgeQuotient num den
          ⟨0 :: (reduceScaled (Ψ.sub Bs)).l,(reduceScaled (Ψ.sub Bs)).s⟩).s:ℤ)*den)
          (0 :: (reduceScaled (Ψ.sub Bs)).l)=
        smul ((reduceScaled (Ψ.sub Bs)).s:ℤ)
          (mul (edgeQuotient num den
            ⟨0 :: (reduceScaled (Ψ.sub Bs)).l,(reduceScaled (Ψ.sub Bs)).s⟩).l [0,2*num,-den])) :
    (edgeQuotient num den ⟨0 :: (reduceScaled (Ψ.sub Bs)).l,(reduceScaled (Ψ.sub Bs)).s⟩).Rep
      (restrict (divY N) X (C B-X)) := by
  obtain ⟨hs,hq,hid⟩ := h
  have hD := rep_reduceScaled (Scaled.Rep.sub hΨ hBs)
  obtain ⟨-,hmul⟩ := edge_div B num den hden hB (rep_X_mul hD) hs hq hid
  set Q := C (1/((edgeQuotient num den
    ⟨0 :: (reduceScaled (Ψ.sub Bs)).l,(reduceScaled (Ψ.sub Bs)).s⟩).s:ℚ))*
    toPoly (edgeQuotient num den ⟨0 :: (reduceScaled (Ψ.sub Bs)).l,(reduceScaled (Ψ.sub Bs)).s⟩).l
  have hdX : (C B-X : ℚ[X])≠0 := by
    intro h0
    have := congrArg (fun q => q.coeff 1) h0
    simp at this
  have h1 : onCurve X (C B-X) N-yZero N=Q*(C B-X) := by
    apply mul_left_cancel₀ (X_ne_zero (R:=ℚ))
    rw [hmul]; ring
  have h2 := far_identity B N
  have h3 : restrict (divY N) X (C B-X)=Q := by
    apply mul_left_cancel₀ hdX
    linear_combination h1-h2
  rw [h3]
  exact rep_self _ hq

/-- Derivative of a represented polynomial. -/
def derivS (a : Scaled) : Scaled :=
  ⟨a.l.tail.zipIdx.map (fun x => x.1*((x.2+1:ℕ):ℤ)),a.s⟩

theorem rep_derivS {a : Scaled} {p : ℚ[X]} (ha : a.Rep p) : (derivS a).Rep p.derivative := by
  unfold Scaled.Rep at *
  ext n
  have h := congrArg (fun q => q.coeff (n+1)) ha
  simp only [coeff_toPoly,coeff_C_mul] at h
  simp only [derivS,coeff_toPoly,coeff_C_mul,coeff_derivative]
  rw [← mul_assoc,← h]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_zipIdx,
    List.getElem?_tail]
  cases hx : a.l[n+1]? <;> simp

/-- An upper bound for the derivative on `[0,B]` and a lower bound for the value at `B`. -/
theorem far_slope_cert {p : ℚ[X]} {a : Scaled} (ha : a.Rep p) (B : ℚ) (num den : ℕ)
    (hden : den≠0) (hB : B/2=num/den) (D : ℕ)
    (q₁ : ℚ) (n₁ : ℤ) (d₁ : ℕ) (hq₁ : q₁=n₁/d₁) (hd₁ : 0<d₁)
    (q₂ : ℚ) (n₂ : ℤ) (d₂ : ℕ) (hq₂ : q₂=n₂/d₂) (hd₂ : 0<d₂)
    (h : ((((derivS a).center num den 1 1).s≠0 ∧ ((derivS a).center num den 1 1).l.length≤D+1) ∧
      2*d₁*upperZ D (fun j => (chebList ((derivS a).center num den 1 1).l).getD j 0)<
        n₁*((((derivS a).center num den 1 1).s*
          2^((derivS a).center num den 1 1).l.length:ℕ):ℤ)) ∧
      ((a.center num den 1 1).s≠0 ∧
        n₂*((a.center num den 1 1).s:ℤ)<d₂*(a.center num den 1 1).l.sum)) :
    WholeIntervalPolynomial.centered 0 B p.derivative=
      WholeIntervalPolynomial.expansion D (WholeIntervalPolynomial.centered 0 B p.derivative) ∧
    WholeIntervalPolynomial.upperOn D 0 B p.derivative<q₁ ∧
    q₂<p.eval B := by
  obtain ⟨hU,hd⟩ := h
  obtain ⟨h1,h2⟩ := upper_cert (rep_derivS ha) B num den hden hB D q₁ n₁ d₁ hq₁ hd₁ hU
  exact ⟨h1,h2,lt_eval_right ha B num den hden hB q₂ n₂ d₂ hq₂ hd₂ hd⟩

/-! ### A quadratic minorant with a geometric tail -/

/-- The composition `p(x₀ + X)`, when `x₀ = num*s/den` and `1 = num*t/den`. -/
theorem rep_comp_shift {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (num den : ℕ) (s t : ℤ)
    (x₀ : ℚ) (hden : den≠0) (hm : x₀=num*s/den) (hh : (1:ℚ)=num*t/den) :
    (c.center num den s t).Rep (p.comp (C x₀+X)) := by
  have h := hc.centered num den s t (a:=x₀-1) (b:=x₀+1) hden (by rw [← hm]; ring)
    (by rw [← hh]; ring)
  have ha : WholeIntervalPolynomial.affine (x₀-1) (x₀+1)=C x₀+X := by
    rw [WholeIntervalPolynomial.affine,show (x₀-1+(x₀+1))/2=x₀ by ring,
      show (x₀+1-(x₀-1))/2=1 by ring,map_one,one_mul]
  rwa [WholeIntervalPolynomial.centered,ha] at h

/-- `∑_{j<N} |l_{j+3}| rn^(j+1) rd^(N-1-j)`. -/
def tailZ (l : List ℤ) (rn rd : ℤ) : ℕ → ℤ
  | 0 => 0
  | N+1 => tailZ l rn rd N*rd+|l.getD (N+3) 0| * rn^(N+1)

theorem tailZ_div (l : List ℤ) (rn rd : ℤ) (hrd : rd≠0) (N : ℕ) :
    ((tailZ l rn rd N:ℤ):ℚ)/(rd:ℚ)^N=
      ∑ j : Fin N,|(l.getD (j.val+3) 0:ℚ)| * ((rn:ℚ)/rd)^(j.val+1) := by
  have hr : (rd:ℚ)≠0 := by exact_mod_cast hrd
  induction N with
  | zero => simp [tailZ]
  | succ N ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last]
    rw [← ih]
    simp only [tailZ]
    push_cast
    rw [div_pow,pow_succ (rd:ℚ)]
    field_simp

theorem sum_tail_eq {q : ℚ[X]} {a : Scaled} (ha : a.Rep q) (hs : a.s≠0) (N : ℕ) (r : ℚ)
    (rn : ℤ) (rd : ℕ) (hr : r=rn/rd) (hrd : 0<rd) :
    ∑ j : Fin N,|q.coeff (j.val+3)| * r^(j.val+1)=
      ((tailZ a.l rn rd N:ℤ):ℚ)/((a.s:ℚ)*(rd:ℚ)^N) := by
  have hs' : (0:ℚ)<a.s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hrd' : ((rd:ℤ):ℚ)≠0 := by exact_mod_cast hrd.ne'
  have e := tailZ_div a.l rn rd (by exact_mod_cast hrd.ne') N
  push_cast at e
  rw [mul_comm,← div_div,e,Finset.sum_div]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [ha.coeff hs,hr,abs_div,abs_of_pos hs']
  ring

/-- A polynomial of degree at most `N+2` with `κ < c₂ - ∑_{j<N} |c_{j+3}| r^(j+1)` and
`ρ < c₀ - c₁²/(4(c₂ - ∑ ...))`, from integer facts on its scaled list. -/
theorem quadratic_tail_cert {q : ℚ[X]} {a : Scaled} (ha : a.Rep q) (N : ℕ)
    (r : ℚ) (rn : ℤ) (rd : ℕ) (hr : r=rn/rd) (hrd : 0<rd)
    (κ : ℚ) (κn : ℤ) (κd : ℕ) (hκ : κ=κn/κd) (hκd : 0<κd)
    (ρ : ℚ) (ρn : ℤ) (ρd : ℕ) (hρ : ρ=ρn/ρd) (hρd : 0<ρd)
    (h : (a.s≠0 ∧ a.l.length≤N+3) ∧
      0<a.l.getD 2 0*(rd:ℤ)^N-tailZ a.l rn rd N ∧
      κn*((a.s:ℤ)*(rd:ℤ)^N)<κd*(a.l.getD 2 0*(rd:ℤ)^N-tailZ a.l rn rd N) ∧
      ρn*(4*(a.l.getD 2 0*(rd:ℤ)^N-tailZ a.l rn rd N)*a.s)<
        ρd*(4*(a.l.getD 2 0*(rd:ℤ)^N-tailZ a.l rn rd N)*a.l.getD 0 0-
          a.l.getD 1 0^2*(rd:ℤ)^N)) :
    q=C (q.coeff 0)+C (q.coeff 1)*X+C (q.coeff 2)*X^2+
      ∑ j : Fin N,C (q.coeff (j.val+3))*X^(j.val+3) ∧
    κ<q.coeff 2-∑ j : Fin N,|q.coeff (j.val+3)| * r^(j.val+1) ∧
    ρ<q.coeff 0-(q.coeff 1)^2/(4*(q.coeff 2-∑ j : Fin N,|q.coeff (j.val+3)| * r^(j.val+1))) := by
  obtain ⟨⟨hs,hl⟩,hK,hκK,hρK⟩ := h
  have hdeg : q.natDegree<N+3 := by
    have := ha.natDegree_le hs
    omega
  have hs' : (0:ℚ)<a.s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hR : (0:ℚ)<(rd:ℚ)^N := by positivity
  have htail := sum_tail_eq ha hs N r rn rd hr hrd
  have hc0 := ha.coeff hs 0
  have hc1 := ha.coeff hs 1
  have hc2 := ha.coeff hs 2
  set K : ℤ := a.l.getD 2 0*(rd:ℤ)^N-tailZ a.l rn rd N with hKdef
  have hcurv : q.coeff 2-∑ j : Fin N,|q.coeff (j.val+3)| * r^(j.val+1)=
      (K:ℚ)/((a.s:ℚ)*(rd:ℚ)^N) := by
    rw [htail,hc2,hKdef]
    push_cast
    field_simp
  have hK' : (0:ℚ)<K := by exact_mod_cast hK
  refine ⟨?_,?_,?_⟩
  · conv_lhs => rw [q.as_sum_range_C_mul_X_pow' hdeg]
    rw [show N+3=3+N by ring,Finset.sum_range_add,Fin.sum_univ_eq_sum_range
      (fun j => C (q.coeff (j+3))*X^(j+3)) N]
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,mul_one,pow_one]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [add_comm 3 j]
  · rw [hcurv,hκ,div_lt_div_iff₀ (by exact_mod_cast hκd) (by positivity)]
    have h' : ((κn*((a.s:ℤ)*(rd:ℤ)^N):ℤ):ℚ)<((κd*K:ℤ):ℚ) := by exact_mod_cast hκK
    push_cast at h'
    linarith
  · rw [hcurv,hc0,hc1,hρ]
    have hK0 : (K:ℚ)≠0 := hK'.ne'
    rw [show ((a.l.getD 0 0:ℤ):ℚ)/a.s-(((a.l.getD 1 0:ℤ):ℚ)/a.s)^2/
        (4*((K:ℚ)/((a.s:ℚ)*(rd:ℚ)^N)))=
        ((4*K*a.l.getD 0 0-a.l.getD 1 0^2*(rd:ℤ)^N:ℤ):ℚ)/((4*K*a.s:ℤ):ℚ) by
      push_cast; field_simp]
    rw [div_lt_div_iff₀ (by exact_mod_cast hρd) (by push_cast; positivity)]
    have h' : ((ρn*(4*K*a.s):ℤ):ℚ)<((ρd*(4*K*a.l.getD 0 0-a.l.getD 1 0^2*(rd:ℤ)^N):ℤ):ℚ) := by
      exact_mod_cast hρK
    push_cast at h' ⊢
    linarith

end SquaresInCircles.Eight.CertificateRestrictions
