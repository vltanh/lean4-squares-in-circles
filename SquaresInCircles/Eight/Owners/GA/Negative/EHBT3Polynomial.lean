module

public import Mathlib.Algebra.Order.Floor.Semifield
public import SquaresInCircles.Eight.Arithmetic.FastPolynomials
public import SquaresInCircles.Eight.Owners.GA.Negative.EHBT3PolynomialData

/-!
# Eight squares: whole-interval positivity of all EH1/BT3 endpoint numerators

Each exact finite transform
covers its full native interval. The two small-high H/G alternatives
retain their constant and first quotient. Every other numerator uses
its stated coefficient-norm reserve directly, with no angular mesh.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.Certificate
open WholeIntervalPolynomial
open WholeIntervalPolynomial.Certificate (Scaled lowerOn_eq_of_rep lowerZ chebList toPoly)
open WholeIntervalPolynomial.Certificate.Fast (chebF lowL chebF_eq lowL_eq)
open PositiveTD.Certificate (S9 S11 C10 C12)

/-! ### Scaled-list helpers: truncation, fractions -/

/-- The first four entries. -/
private def r76trunc (c : Scaled) : Scaled := ⟨c.l.take 4,c.s⟩

private theorem r76trunc_rep {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) :
    (r76trunc c).Rep (truncate3 p) := by
  unfold Scaled.Rep at *
  ext n
  have hco := congrArg (fun q => q.coeff n) hc
  simp only [WholeIntervalPolynomial.Certificate.coeff_toPoly,coeff_C_mul] at hco
  rw [WholeIntervalPolynomial.Certificate.coeff_toPoly,coeff_C_mul]
  simp only [r76trunc,truncate3,Fin.sum_univ_four,
    Fin.val_zero,Fin.val_one,Fin.val_two,coeff_add,coeff_C_mul_X_pow]
  rcases Nat.lt_or_ge n 4 with hn|hn
  · interval_cases n <;> simpa [List.getD_eq_getElem?_getD] using hco
  · have ht : (c.l.take 4).getD n 0=0 := by
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by simp; omega)]
      rfl
    rw [ht]
    simp [show n≠0 by omega,show n≠1 by omega,show n≠2 by omega,show n≠3 by omega]

private theorem r76frac_rep (a : ℤ) (b : ℕ) (hb : b≠0) :
    (⟨[a],b⟩ : Scaled).Rep (C ((a:ℚ)/b)) := by
  unfold Scaled.Rep
  simp only [toPoly,mul_zero,add_zero,← map_mul]
  congr 1
  field_simp

/-- The rounded square root, reduced to one integer square root. -/
private theorem r76root12 {a : ℤ} {b n : ℕ} (hb : b≠0) (ha : 0≤a)
    (hn : n*n≤a.toNat*1000000000000000000000000/b ∧ a.toNat*1000000000000000000000000/b<(n+1)*(n+1)) :
    root12 ((a:ℚ)/b)=((if 4*a*1000000000000000000000000<(2*(n:ℤ)+1)^2*b then n else n+1 : ℕ):ℚ)/
      1000000000000 := by
  have hb' : (0:ℚ)<b := by exact_mod_cast Nat.pos_of_ne_zero hb
  have hq0 : 0≤(a:ℚ)/b := div_nonneg (by exact_mod_cast ha) hb'.le
  have hfl : ((a:ℚ)/b).num.natAbs*1000000000000000000000000/((a:ℚ)/b).den=
      a.toNat*1000000000000000000000000/b := by
    have e1 : ((((a:ℚ)/b).num.natAbs:ℕ):ℚ)=(((a:ℚ)/b).num:ℚ) := by
      rw [Nat.cast_natAbs,Int.cast_abs,abs_of_nonneg (by exact_mod_cast Rat.num_nonneg.2 hq0)]
    have e2 : ((a.toNat:ℕ):ℚ)=(a:ℚ) := by exact_mod_cast Int.toNat_of_nonneg ha
    have hx : ((((a:ℚ)/b).num.natAbs*1000000000000000000000000:ℕ):ℚ)/(((a:ℚ)/b).den:ℕ)=
        ((a.toNat*1000000000000000000000000:ℕ):ℚ)/(b:ℕ) := by
      rw [Nat.cast_mul,Nat.cast_mul,e1,e2,mul_div_right_comm,Rat.num_div_den]
      ring
    rw [← Nat.floor_div_eq_div (K:=ℚ),← Nat.floor_div_eq_div (K:=ℚ),hx]
  have key : ((a:ℚ)/b*1000000000000000000000000<((n:ℚ)+1/2)^2)↔
      (4*a*1000000000000000000000000<(2*(n:ℤ)+1)^2*b) := by
    rw [← @Int.cast_lt ℚ]
    push_cast
    rw [div_mul_eq_mul_div,div_lt_iff₀ hb']
    constructor <;> intro h <;>
      linarith [show ((2*(n:ℚ)+1)^2*b)=4*(((n:ℚ)+1/2)^2*b) by ring]
  unfold root12
  simp only [hfl,(Nat.eq_sqrt.2 hn).symm]
  congr 2
  exact if_congr key rfl rfl

/-! ### Taylor polynomials composed with a represented polynomial -/

private def r76S9of (v : Scaled) : Scaled := Scaled.normF
  ((((v.subF ((Scaled.const (1/6)).mulF (v.powF 3))).addF
    ((Scaled.const (1/120)).mulF (v.powF 5))).subF
    ((Scaled.const (1/5040)).mulF (v.powF 7))).addF
    ((Scaled.const (1/362880)).mulF (v.powF 9)))

private theorem r76S9of_rep {v : Scaled} {q : ℚ[X]} (hv : v.Rep q) :
    (r76S9of v).Rep (S9.comp q) := by
  have e : S9.comp q=q-C (1/6)*q^3+C (1/120)*q^5-C (1/5040)*q^7+C (1/362880)*q^9 := by
    simp only [S9,PositiveTD.Certificate.S5,sub_comp,add_comp,mul_comp,C_comp,X_comp,pow_comp]
  rw [e]
  exact Scaled.Rep.normF ((((hv.subF ((Scaled.rep_const _).mulF (hv.powF 3))).addF
    ((Scaled.rep_const _).mulF (hv.powF 5))).subF
    ((Scaled.rep_const _).mulF (hv.powF 7))).addF
    ((Scaled.rep_const _).mulF (hv.powF 9)))

private def r76S11of (v : Scaled) : Scaled := Scaled.normF
  ((r76S9of v).subF ((Scaled.const (1/39916800)).mulF (v.powF 11)))

private theorem r76S11of_rep {v : Scaled} {q : ℚ[X]} (hv : v.Rep q) :
    (r76S11of v).Rep (S11.comp q) := by
  have e : S11.comp q=S9.comp q-C (1/39916800)*q^11 := by
    simp only [S11,sub_comp,mul_comp,C_comp,X_comp,pow_comp]
  rw [e]
  exact Scaled.Rep.normF ((r76S9of_rep hv).subF ((Scaled.rep_const _).mulF (hv.powF 11)))

private def r76C10of (v : Scaled) : Scaled := Scaled.normF
  (((((((Scaled.ofNat 1).subF ((Scaled.const (1/2)).mulF (v.powF 2))).addF
    ((Scaled.const (1/24)).mulF (v.powF 4))).subF
    ((Scaled.const (1/720)).mulF (v.powF 6))).addF
    ((Scaled.const (1/40320)).mulF (v.powF 8))).subF
    ((Scaled.const (1/3628800)).mulF (v.powF 10))))

private theorem r76C10of_rep {v : Scaled} {q : ℚ[X]} (hv : v.Rep q) :
    (r76C10of v).Rep (C10.comp q) := by
  have e : C10.comp q=1-C (1/2)*q^2+C (1/24)*q^4-C (1/720)*q^6+C (1/40320)*q^8-
      C (1/3628800)*q^10 := by
    simp only [C10,PositiveTD.Certificate.C4,sub_comp,add_comp,mul_comp,C_comp,X_comp,pow_comp,
      one_comp]
  rw [e]
  exact Scaled.Rep.normF (((((Scaled.rep_one.subF ((Scaled.rep_const _).mulF (hv.powF 2))).addF
    ((Scaled.rep_const _).mulF (hv.powF 4))).subF
    ((Scaled.rep_const _).mulF (hv.powF 6))).addF
    ((Scaled.rep_const _).mulF (hv.powF 8))).subF
    ((Scaled.rep_const _).mulF (hv.powF 10)))

private def r76C12of (v : Scaled) : Scaled := Scaled.normF
  ((r76C10of v).addF ((Scaled.const (1/479001600)).mulF (v.powF 12)))

private theorem r76C12of_rep {v : Scaled} {q : ℚ[X]} (hv : v.Rep q) :
    (r76C12of v).Rep (C12.comp q) := by
  have e : C12.comp q=C10.comp q+C (1/479001600)*q^12 := by
    simp only [C12,add_comp,mul_comp,C_comp,X_comp,pow_comp]
  rw [e]
  exact Scaled.Rep.normF ((r76C10of_rep hv).addF ((Scaled.rep_const _).mulF (hv.powF 12)))

/-! ### The row data -/

private def r76theta (r : Row) : Scaled := Scaled.var.addF (Scaled.const (left r))

private theorem r76theta_rep (r : Row) : (r76theta r).Rep (theta r) :=
  Scaled.rep_var.addF (Scaled.rep_const _)

private def r76kB : Family→Scaled→Scaled
  | .smallLow,v => (Scaled.const (2933/5000)).addF ((Scaled.const (1239/2500)).mulF v)
  | .smallHigh,v => (((Scaled.const (1673/2500)).addF
      ((Scaled.const (2609/5000)).mulF (v.subF (Scaled.const (1/6))))).subF
      ((Scaled.const (1489/2500)).mulF ((v.subF (Scaled.const (1/6))).powF 2))).addF
      ((Scaled.const (527/1250)).mulF ((v.subF (Scaled.const (1/6))).powF 3))
  | .farLow,_ => Scaled.const (121/200)
  | .farHigh,v => (Scaled.const (101/200)).addF ((Scaled.const (2/5)).mulF v)

private theorem r76kB_rep (f : Family) {v : Scaled} {q : ℚ[X]} (hv : v.Rep q) :
    (r76kB f v).Rep ((kBase f).comp q) := by
  cases f <;> simp only [kBase,r76kB,add_comp,sub_comp,mul_comp,C_comp,X_comp,pow_comp]
  · exact (Scaled.rep_const _).addF ((Scaled.rep_const _).mulF hv)
  · exact (((Scaled.rep_const _).addF ((Scaled.rep_const _).mulF (hv.subF (Scaled.rep_const _)))).subF
      ((Scaled.rep_const _).mulF ((hv.subF (Scaled.rep_const _)).powF 2))).addF
      ((Scaled.rep_const _).mulF ((hv.subF (Scaled.rep_const _)).powF 3))
  · exact Scaled.rep_const _
  · exact (Scaled.rep_const _).addF ((Scaled.rep_const _).mulF hv)

private def r76lB : Family→Scaled→Scaled
  | .smallLow,_ => Scaled.ofNat 1
  | .smallHigh,v => (((Scaled.ofNat 1).addF
      ((Scaled.const (7/400)).mulF (v.subF (Scaled.const (1/6))))).subF
      ((Scaled.const (2733/2500)).mulF ((v.subF (Scaled.const (1/6))).powF 2))).addF
      ((Scaled.const (639/500)).mulF ((v.subF (Scaled.const (1/6))).powF 3))
  | .farLow,v => (Scaled.ofNat 1).subF ((Scaled.const (9/25)).mulF v)
  | .farHigh,v => (Scaled.const (381/400)).subF ((Scaled.const (17/100)).mulF v)

private theorem r76lB_rep (f : Family) {v : Scaled} {q : ℚ[X]} (hv : v.Rep q) :
    (r76lB f v).Rep ((lBase f).comp q) := by
  cases f <;> simp only [lBase,r76lB,add_comp,sub_comp,mul_comp,C_comp,X_comp,pow_comp,one_comp]
  · exact Scaled.rep_one
  · exact ((Scaled.rep_one.addF ((Scaled.rep_const _).mulF (hv.subF (Scaled.rep_const _)))).subF
      ((Scaled.rep_const _).mulF ((hv.subF (Scaled.rep_const _)).powF 2))).addF
      ((Scaled.rep_const _).mulF ((hv.subF (Scaled.rep_const _)).powF 3))
  · exact Scaled.rep_one.subF ((Scaled.rep_const _).mulF hv)
  · exact (Scaled.rep_const _).subF ((Scaled.rep_const _).mulF hv)

private def r76mB : Family→Scaled→Scaled
  | .smallLow,v => (Scaled.const (5821/5000)).subF ((Scaled.const (4437/5000)).mulF v)
  | .smallHigh,v => (((Scaled.const (10163/10000)).subF
      ((Scaled.const (209/10000)).mulF (v.subF (Scaled.const (1/6))))).subF
      ((Scaled.const (5743/5000)).mulF ((v.subF (Scaled.const (1/6))).powF 2))).addF
      ((Scaled.const (14069/10000)).mulF ((v.subF (Scaled.const (1/6))).powF 3))
  | .farLow,v => (Scaled.const (111/100)).subF ((Scaled.const (77/100)).mulF v)
  | .farHigh,v => (Scaled.const (1929/2000)).subF ((Scaled.const (47/250)).mulF v)

private theorem r76mB_rep (f : Family) {v : Scaled} {q : ℚ[X]} (hv : v.Rep q) :
    (r76mB f v).Rep ((mBase f).comp q) := by
  cases f <;> simp only [mBase,r76mB,add_comp,sub_comp,mul_comp,C_comp,X_comp,pow_comp]
  · exact (Scaled.rep_const _).subF ((Scaled.rep_const _).mulF hv)
  · exact (((Scaled.rep_const _).subF ((Scaled.rep_const _).mulF (hv.subF (Scaled.rep_const _)))).subF
      ((Scaled.rep_const _).mulF ((hv.subF (Scaled.rep_const _)).powF 2))).addF
      ((Scaled.rep_const _).mulF ((hv.subF (Scaled.rep_const _)).powF 3))
  · exact (Scaled.rep_const _).subF ((Scaled.rep_const _).mulF hv)
  · exact (Scaled.rep_const _).subF ((Scaled.rep_const _).mulF hv)

private def r76k (r : Row) : Scaled := Scaled.normF (r76kB (family r) (r76theta r))
private def r76l (r : Row) : Scaled := Scaled.normF (r76lB (family r) (r76theta r))
private def r76m (r : Row) : Scaled := Scaled.normF (r76mB (family r) (r76theta r))

private theorem r76k_rep (r : Row) : (r76k r).Rep (k r) :=
  Scaled.Rep.normF (r76kB_rep _ (r76theta_rep r))
private theorem r76l_rep (r : Row) : (r76l r).Rep (l r) :=
  Scaled.Rep.normF (r76lB_rep _ (r76theta_rep r))
private theorem r76m_rep (r : Row) : (r76m r).Rep (m r) :=
  Scaled.Rep.normF (r76mB_rep _ (r76theta_rep r))

private def r76s (r : Row) : Scaled :=
  if equal r then r76theta r else match r with
    | .farHigh _ true => Scaled.const (1/4)
    | _ => Scaled.const (1/10)

private theorem r76s_rep (r : Row) : (r76s r).Rep (s r) := by
  rcases r with _|_|i|i|i|_|⟨i,_|_⟩
  · exact r76theta_rep _
  all_goals first
    | exact r76theta_rep _
    | exact Scaled.rep_const _

private def r76d (r : Row) : Scaled :=
  if positive r then (r76s r).subF (r76theta r) else (r76theta r).subF (r76s r)

private theorem r76d_rep (r : Row) : (r76d r).Rep (d r) := by
  unfold r76d d
  split_ifs
  · exact (r76s_rep r).subF (r76theta_rep r)
  · exact (r76theta_rep r).subF (r76s_rep r)

private def r76J0of (v : Scaled) : Scaled :=
  ((Scaled.const (1/2)).mulF ((r76C10of v).subF (Scaled.ofNat 1))).addF
    ((Scaled.const (1/2-abar)).mulF (r76S9of v))

private theorem r76J0of_rep {v : Scaled} {q : ℚ[X]} (hv : v.Rep q) :
    (r76J0of v).Rep (J0.comp q) := by
  have e : J0.comp q=C (1/2)*(C10.comp q-1)+C (1/2-abar)*S9.comp q := by
    simp only [J0,add_comp,sub_comp,mul_comp,C_comp,one_comp]
  rw [e]
  exact ((Scaled.rep_const _).mulF ((r76C10of_rep hv).subF Scaled.rep_one)).addF
    ((Scaled.rep_const _).mulF (r76S9of_rep hv))

private def r76JB : Family→Scaled→Scaled
  | .smallHigh,v => (r76J0of v).subF ((Scaled.const (43/500)).mulF ((v.subF (Scaled.const (1/6))).powF 4))
  | .farHigh,v => (r76J0of v).subF ((Scaled.const (151/500)).mulF ((v.subF (Scaled.const (1/6))).powF 6))
  | .smallLow,v => r76J0of v
  | .farLow,v => r76J0of v

private theorem r76JB_rep (f : Family) {v : Scaled} {q : ℚ[X]} (hv : v.Rep q) :
    (r76JB f v).Rep ((JBase f).comp q) := by
  cases f <;> simp only [JBase,r76JB,sub_comp,mul_comp,C_comp,X_comp,pow_comp]
  · exact r76J0of_rep hv
  · exact (r76J0of_rep hv).subF ((Scaled.rep_const _).mulF ((hv.subF (Scaled.rep_const _)).powF 4))
  · exact r76J0of_rep hv
  · exact (r76J0of_rep hv).subF ((Scaled.rep_const _).mulF ((hv.subF (Scaled.rep_const _)).powF 6))

private def r76J (r : Row) : Scaled := Scaled.normF (r76JB (family r) (r76theta r))

private theorem r76J_rep (r : Row) : (r76J r).Rep (J r) :=
  Scaled.Rep.normF (r76JB_rep _ (r76theta_rep r))

private def r76qStar (r : Row) : Scaled :=
  Scaled.normF ((r76l r).addF ((Scaled.const (3/20)).mulF ((Scaled.const h).subF (r76theta r))))

private theorem r76qStar_rep (r : Row) : (r76qStar r).Rep (qStar r) :=
  Scaled.Rep.normF ((r76l_rep r).addF ((Scaled.rep_const _).mulF ((Scaled.rep_const _).subF (r76theta_rep r))))

private def r76cUpper (r : Row) : Split→Scaled
  | .atA => r76m r
  | .atT => Scaled.normF ((r76m r).mulF ((r76C12of (r76theta r)).addF
      ((Scaled.const eta).mulF (r76S9of (r76theta r)))))

private theorem r76cUpper_rep (r : Row) : ∀ ep,(r76cUpper r ep).Rep (cUpper r ep)
  | .atA => r76m_rep r
  | .atT => Scaled.Rep.normF ((r76m_rep r).mulF ((r76C12of_rep (r76theta_rep r)).addF
      ((Scaled.rep_const _).mulF (r76S9of_rep (r76theta_rep r)))))

private def r76head (c0 : ℚ) (r : Row) : Scaled :=
  (((Scaled.const 2).mulF (r76k r)).addF ((Scaled.const 3).mulF (r76l r))).addF (Scaled.const c0)

private theorem r76head_rep (c0 : ℚ) (r : Row) :
    (r76head c0 r).Rep (C 2*k r+C 3*l r+C c0) :=
  (((Scaled.rep_const _).mulF (r76k_rep r)).addF ((Scaled.rep_const _).mulF (r76l_rep r))).addF
    (Scaled.rep_const _)

private def r76tail (a b : ℚ) (r : Row) : Scaled :=
  ((Scaled.ofNat 1).addF ((Scaled.const a).mulF (r76C10of (r76theta r)))).addF
    ((Scaled.const b).mulF (r76S9of (r76theta r)))

private theorem r76tail_rep (a b : ℚ) (r : Row) :
    (r76tail a b r).Rep (1+C a*C10.comp (theta r)+C b*S9.comp (theta r)) :=
  (Scaled.rep_one.addF ((Scaled.rep_const _).mulF (r76C10of_rep (r76theta_rep r)))).addF
    ((Scaled.rep_const _).mulF (r76S9of_rep (r76theta_rep r)))

private def r76baseA (c0 c1 : ℚ) (r : Row) : Scaled :=
  ((r76head c0 r).addF ((Scaled.const c1).mulF (r76m r))).addF ((r76l r).mulF (r76J r))

private theorem r76baseA_rep (c0 c1 : ℚ) (r : Row) :
    (r76baseA c0 c1 r).Rep (C 2*k r+C 3*l r+C c0+C c1*m r+l r*J r) :=
  ((r76head_rep c0 r).addF ((Scaled.rep_const _).mulF (r76m_rep r))).addF
    ((r76l_rep r).mulF (r76J_rep r))

private def r76baseT (c0 a b : ℚ) (r : Row) : Scaled :=
  (r76head c0 r).addF ((r76m r).mulF (r76tail a b r))

private theorem r76baseT_rep (c0 a b : ℚ) (r : Row) :
    (r76baseT c0 a b r).Rep (C 2*k r+C 3*l r+C c0+
      m r*(1+C a*C10.comp (theta r)+C b*S9.comp (theta r))) :=
  (r76head_rep c0 r).addF ((r76m_rep r).mulF (r76tail_rep a b r))

private def r76base (r : Row) (ep : Split) : Scaled :=
  Scaled.normF (if family r=.smallLow then
    match ep with
    | .atA => r76baseA (5/2-cbar) (5/2-cbar) r
    | .atT => r76baseT (5/2-cbar) (3/2-cbar) (1/2+eta*(1-cbar)-sigmabar) r
  else
    match ep with
    | .atA => r76baseA 3 3 r
    | .atT => r76baseT 3 2 (1/2+(3/2)*eta-sigmabar) r)

private theorem r76base_rep (r : Row) (ep : Split) : (r76base r ep).Rep (base r ep) := by
  unfold r76base base
  apply Scaled.Rep.normF
  split_ifs <;> cases ep
  · exact r76baseA_rep _ _ r
  · exact r76baseT_rep _ _ _ r
  · exact r76baseA_rep _ _ r
  · exact r76baseT_rep _ _ _ r

private def r76g (r : Row) : Scaled :=
  Scaled.normF (((Scaled.const (13/12)).mulF (r76S11of (r76s r))).addF
    ((Scaled.const (82/125)).mulF ((r76C10of (r76s r)).subF (Scaled.ofNat 1))))

private theorem r76g_rep (r : Row) : (r76g r).Rep (g r) :=
  Scaled.Rep.normF (((Scaled.rep_const _).mulF (r76S11of_rep (r76s_rep r))).addF
    ((Scaled.rep_const _).mulF ((r76C10of_rep (r76s_rep r)).subF Scaled.rep_one)))

private def r76gainLower (r : Row) : Scaled :=
  if far (family r) then Scaled.normF (((Scaled.const (201/200)).mulF (r76g r)).subF
    (Scaled.const (11/50000))) else r76g r

private theorem r76gainLower_rep (r : Row) : (r76gainLower r).Rep (gainLower r) := by
  unfold r76gainLower gainLower
  split_ifs
  · exact Scaled.Rep.normF (((Scaled.rep_const _).mulF (r76g_rep r)).subF (Scaled.rep_const _))
  · exact r76g_rep r

private def r76smaller (r : Row) : Fin 4→Scaled := ![r76k r,r76k r,r76l r,Scaled.ofNat 1]
private def r76larger (r : Row) : Fin 4→Scaled := ![Scaled.ofNat 1,r76l r,r76qStar r,Scaled.ofNat 1]

private theorem r76smaller_rep (r : Row) (i : Fin 4) : (r76smaller r i).Rep (smaller r i) := by
  fin_cases i
  exacts [r76k_rep r,r76k_rep r,r76l_rep r,Scaled.rep_one]

private theorem r76larger_rep (r : Row) (i : Fin 4) : (r76larger r i).Rep (larger r i) := by
  fin_cases i
  exacts [Scaled.rep_one,r76l_rep r,r76qStar_rep r,Scaled.rep_one]

private def r76extra (r : Row) : Scaled :=
  if equal r then ⟨[],1⟩ else if positive r then
    Scaled.normF (((r76smaller r (index r)).mulF
      (((r76C10of (r76d r)).addF (r76S11of (r76d r))).subF (Scaled.ofNat 1))).subF
      ((Scaled.const (1/200)).mulF (r76d r)))
  else Scaled.normF ((r76larger r (index r)).mulF ((r76C10of (r76d r)).subF (Scaled.ofNat 1)))

private theorem r76extra_rep (r : Row) : (r76extra r).Rep
    (if equal r then 0 else if positive r then positiveExtra r else negativeExtra r) := by
  unfold r76extra
  split_ifs
  · exact Scaled.rep_zero
  · exact Scaled.Rep.normF (((r76smaller_rep r (index r)).mulF
      (((r76C10of_rep (r76d_rep r)).addF (r76S11of_rep (r76d_rep r))).subF Scaled.rep_one)).subF
      ((Scaled.rep_const _).mulF (r76d_rep r)))
  · exact Scaled.Rep.normF ((r76larger_rep r (index r)).mulF
      ((r76C10of_rep (r76d_rep r)).subF Scaled.rep_one))

private def r76A (r : Row) (ep : Split) : Scaled :=
  Scaled.normF (((r76base r ep).addF (r76gainLower r)).addF (r76extra r))

private theorem r76A_rep (r : Row) (ep : Split) : (r76A r ep).Rep (A r ep) :=
  Scaled.Rep.normF (((r76base_rep r ep).addF (r76gainLower_rep r)).addF (r76extra_rep r))

private def r76normZero (r : Row) (ep : Split) : Fin 4→Scaled :=
  ![(Scaled.ofNat 1).addF ((r76k r).powF 2),((r76k r).powF 2).addF ((r76l r).powF 2),
    ((r76l r).powF 2).addF ((r76m r).powF 2),(Scaled.ofNat 1).addF ((r76cUpper r ep).powF 2)]

private theorem r76normZero_rep (r : Row) (ep : Split) (i : Fin 4) :
    (r76normZero r ep i).Rep (normZero r ep i) := by
  fin_cases i
  exacts [Scaled.rep_one.addF ((r76k_rep r).powF 2),((r76k_rep r).powF 2).addF ((r76l_rep r).powF 2),
    ((r76l_rep r).powF 2).addF ((r76m_rep r).powF 2),Scaled.rep_one.addF ((r76cUpper_rep r ep).powF 2)]

private def r76product (r : Row) (ep : Split) : Fin 4→Scaled :=
  ![r76k r,(r76k r).mulF (r76l r),(r76l r).mulF (r76m r),r76cUpper r ep]

private theorem r76product_rep (r : Row) (ep : Split) (i : Fin 4) :
    (r76product r ep i).Rep (product r ep i) := by
  fin_cases i
  exacts [r76k_rep r,(r76k_rep r).mulF (r76l_rep r),(r76l_rep r).mulF (r76m_rep r),r76cUpper_rep r ep]

private def r76P (r : Row) (ep : Split) (i : Fin 4) : Scaled :=
  if active r i then Scaled.normF ((r76normZero r ep i).addF
    (if equal r∨i≠index r then ⟨[],1⟩
    else if positive r then ((Scaled.const 2).mulF (r76product r ep i)).mulF (r76S9of (r76d r))
    else (((Scaled.const 2).negF.mulF (r76product r ep i)).mulF (r76S11of (r76d r)))))
  else ⟨[],1⟩

private theorem r76P_rep (r : Row) (ep : Split) (i : Fin 4) : (r76P r ep i).Rep (P r ep i) := by
  unfold r76P P
  split_ifs
  · exact Scaled.Rep.normF ((r76normZero_rep r ep i).addF Scaled.rep_zero)
  · exact Scaled.Rep.normF ((r76normZero_rep r ep i).addF (((Scaled.rep_const _).mulF
      (r76product_rep r ep i)).mulF (r76S9of_rep (r76d_rep r))))
  · exact Scaled.Rep.normF ((r76normZero_rep r ep i).addF ((((Scaled.rep_const _).negF).mulF
      (r76product_rep r ep i)).mulF (r76S11of_rep (r76d_rep r))))
  · exact Scaled.rep_zero

/-! ### The masses -/

private def r76w (c : Scaled) : Scaled :=
  Scaled.normF ((⟨[(c.s:ℤ)],(c.l.getD 0 0).toNat⟩ : Scaled).mulF
    ((r76trunc c).subF ⟨[c.l.getD 0 0],c.s⟩))

private theorem r76eval0 {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (hs : c.s≠0) :
    p.eval 0=((c.l.getD 0 0:ℤ):ℚ)/c.s := by
  rw [← coeff_zero_eq_eval_zero,hc.coeff hs 0]

private theorem r76w_rep {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (hs : c.s≠0)
    (ha : 0<c.l.getD 0 0) :
    (r76w c).Rep (C (1/p.eval 0)*(truncate3 p-C (p.eval 0))) := by
  have h0 := r76eval0 hc hs
  have ht : ((((c.l.getD 0 0).toNat:ℕ):ℤ):ℚ)=((c.l.getD 0 0:ℤ):ℚ) := by
    rw [Int.toNat_of_nonneg ha.le]
  have hinv : (1:ℚ)/p.eval 0=(((c.s:ℕ):ℤ):ℚ)/(((c.l.getD 0 0).toNat:ℕ):ℚ) := by
    rw [h0,one_div_div,Int.cast_natCast,← ht,Int.cast_natCast]
  rw [hinv,h0]
  exact Scaled.Rep.normF ((r76frac_rep _ _ (by omega)).mulF ((r76trunc_rep hc).subF (r76frac_rep _ _ hs)))

private def r76rhoJ (c : Scaled) (n : ℕ) : ℕ :=
  if 4*(c.l.getD 0 0)*1000000000000000000000000<(2*(n:ℤ)+1)^2*c.s then n else n+1

private def r76massB (c : Scaled) (n : ℕ) : Scaled :=
  Scaled.normF ((⟨[(r76rhoJ c n:ℤ)],1000000000000⟩ : Scaled).mulF (r76trunc
    ((((Scaled.ofNat 1).addF ((Scaled.const (1/2)).mulF (r76w c))).subF
      ((Scaled.const (1/8)).mulF ((r76w c).powF 2))).addF
      ((Scaled.const (1/16)).mulF ((r76w c).powF 3)))))

private theorem r76massB_rep {c : Scaled} {p : ℚ[X]} {n : ℕ} (hc : c.Rep p) (hs : c.s≠0)
    (ha : 0<c.l.getD 0 0)
    (hn : n*n≤(c.l.getD 0 0).toNat*1000000000000000000000000/c.s ∧
      (c.l.getD 0 0).toNat*1000000000000000000000000/c.s<(n+1)*(n+1)) :
    (r76massB c n).Rep (C (root12 (p.eval 0))*truncate3
      (1+C (1/2)*(C (1/p.eval 0)*(truncate3 p-C (p.eval 0)))-
        C (1/8)*(C (1/p.eval 0)*(truncate3 p-C (p.eval 0)))^2+
        C (1/16)*(C (1/p.eval 0)*(truncate3 p-C (p.eval 0)))^3)) := by
  have hρ : root12 (p.eval 0)=(((r76rhoJ c n:ℕ):ℤ):ℚ)/((1000000000000:ℕ):ℚ) := by
    rw [r76eval0 hc hs,r76root12 hs ha.le hn,Int.cast_natCast]
    rfl
  have hw := r76w_rep hc hs ha
  rw [hρ]
  exact Scaled.Rep.normF ((r76frac_rep _ _ (by norm_num)).mulF (r76trunc_rep (((Scaled.rep_one.addF
    ((Scaled.rep_const _).mulF hw)).subF ((Scaled.rep_const _).mulF (hw.powF 2))).addF
    ((Scaled.rep_const _).mulF (hw.powF 3)))))

/-- The facts about `P` at zero that the mass representation uses. -/
private def r76PFact (r : Row) (ep : Split) (i : Fin 4) (n : ℕ) : Prop :=
  active r i → (r76P r ep i).s≠0 ∧ 0<(r76P r ep i).l.getD 0 0 ∧
    n*n≤((r76P r ep i).l.getD 0 0).toNat*1000000000000000000000000/(r76P r ep i).s ∧
    ((r76P r ep i).l.getD 0 0).toNat*1000000000000000000000000/(r76P r ep i).s<(n+1)*(n+1)

private def r76mass (r : Row) (ep : Split) (i : Fin 4) (n : ℕ) : Scaled :=
  if active r i then r76massB (r76P r ep i) n else Scaled.ofNat 1

private theorem r76mass_rep (r : Row) (ep : Split) (i : Fin 4) (n : ℕ) (h : r76PFact r ep i n) :
    (r76mass r ep i n).Rep (mass r ep i) := by
  unfold r76mass mass
  split_ifs with ha
  · obtain ⟨h1,h2,h3,h4⟩ := h ha
    exact r76massB_rep (r76P_rep r ep i) h1 h2 ⟨h3,h4⟩
  · exact Scaled.rep_one

/-! ### The numerators -/

private theorem r76erase (f : Fin 4→ℚ[X]) :
    ∏ j∈Finset.univ.erase (0:Fin 4),f j=f 1*f 2*f 3 ∧
    ∏ j∈Finset.univ.erase (1:Fin 4),f j=f 0*f 2*f 3 ∧
    ∏ j∈Finset.univ.erase (2:Fin 4),f j=f 0*f 1*f 3 ∧
    ∏ j∈Finset.univ.erase (3:Fin 4),f j=f 0*f 1*f 2 := by
  refine ⟨?_,?_,?_,?_⟩
  · rw [show Finset.univ.erase (0:Fin 4)={1,2,3} by decide]; simp; ring
  · rw [show Finset.univ.erase (1:Fin 4)={0,2,3} by decide]; simp; ring
  · rw [show Finset.univ.erase (2:Fin 4)={0,1,3} by decide]; simp; ring
  · rw [show Finset.univ.erase (3:Fin 4)={0,1,2} by decide]; simp; ring

private def r76T (r : Row) (ep : Split) (i : Fin 4) (Mi o : Scaled) : Scaled :=
  if active r i then ((r76P r ep i).addF (Mi.powF 2)).mulF o else ⟨[],1⟩

private theorem r76T_rep (r : Row) (ep : Split) (i : Fin 4) {Mi o : Scaled} {q : ℚ[X]}
    (hM : Mi.Rep (mass r ep i)) (ho : o.Rep q) :
    (r76T r ep i Mi o).Rep (if active r i then (P r ep i+(mass r ep i)^2)*q else 0) := by
  unfold r76T
  split_ifs
  · exact ((r76P_rep r ep i).addF (hM.powF 2)).mulF ho
  · exact Scaled.rep_zero

/-- The numerator, not divided by the gcd of its entries: they have thousands of bits, and a gcd
of such numbers costs the kernels outside Lean more than it saves. -/
private def r76numB (r : Row) (ep : Split) (M : Fin 4→Scaled) : Scaled :=
  (((Scaled.const 2).mulF (r76A r ep)).mulF ((((M 0).mulF (M 1)).mulF (M 2)).mulF (M 3))).subF
    ((Scaled.const Rbar).mulF ((((r76T r ep 0 (M 0) (((M 1).mulF (M 2)).mulF (M 3))).addF
      (r76T r ep 1 (M 1) (((M 0).mulF (M 2)).mulF (M 3)))).addF
      (r76T r ep 2 (M 2) (((M 0).mulF (M 1)).mulF (M 3)))).addF
      (r76T r ep 3 (M 3) (((M 0).mulF (M 1)).mulF (M 2)))))

private theorem r76numB_rep (r : Row) (ep : Split) {M : Fin 4→Scaled}
    (hM : ∀ i,(M i).Rep (mass r ep i)) : (r76numB r ep M).Rep (numerator r ep) := by
  obtain ⟨e0,e1,e2,e3⟩ := r76erase (mass r ep)
  unfold numerator
  rw [Fin.prod_univ_four,Fin.sum_univ_four,e0,e1,e2,e3]
  exact ((((Scaled.rep_const _).mulF (r76A_rep r ep)).mulF
    ((((hM 0).mulF (hM 1)).mulF (hM 2)).mulF (hM 3))).subF
    ((Scaled.rep_const _).mulF ((((r76T_rep r ep 0 (hM 0) (((hM 1).mulF (hM 2)).mulF (hM 3))).addF
      (r76T_rep r ep 1 (hM 1) (((hM 0).mulF (hM 2)).mulF (hM 3)))).addF
      (r76T_rep r ep 2 (hM 2) (((hM 0).mulF (hM 1)).mulF (hM 3)))).addF
      (r76T_rep r ep 3 (hM 3) (((hM 0).mulF (hM 1)).mulF (hM 2))))))

/-! ### Integer certificates -/

/-- The whole-interval certificate from one integer computation. -/
private theorem r76cert {c : Scaled} {lo hi : ℚ} {p : ℚ[X]} {D : ℕ}
    (hq : c.Rep (WholeIntervalPolynomial.centered lo hi p)) {a : ℤ} {b : ℕ}
    (h : c.s≠0 ∧ c.l.length≤D+1 ∧ b≠0 ∧ (chebF c.l).length≤D+1 ∧
      a*((c.s*2^c.l.length:ℕ):ℤ)<2*lowL (chebF c.l)*b) :
    WholeIntervalPolynomial.centered lo hi p=expansion D (WholeIntervalPolynomial.centered lo hi p) ∧
      (a:ℚ)/b<lowerOn D lo hi p := by
  refine ⟨hq.eq_expansion h.1 h.2.1,?_⟩
  rw [lowerOn_eq_of_rep hq h.1 h.2.1]
  have hM : (0:ℚ)<(c.s:ℚ)*2^c.l.length := by
    have : (0:ℚ)<c.s := by exact_mod_cast Nat.pos_of_ne_zero h.1
    positivity
  have hb : (0:ℚ)<b := by exact_mod_cast Nat.pos_of_ne_zero h.2.2.1
  rw [show ((lowerZ D (fun j => (chebList c.l).getD j 0):ℤ):ℚ)/((c.s:ℚ)*2^c.l.length/2)=
    (2*(lowerZ D (fun j => (chebList c.l).getD j 0):ℤ):ℚ)/((c.s:ℚ)*2^c.l.length) by
      field_simp,div_lt_div_iff₀ hb hM]
  have h4 := h.2.2.2.2
  rw [← lowL_eq h.2.2.2.1,chebF_eq] at h4
  exact_mod_cast h4

private def r76wn : Row→ℕ
  | .lowEqual => 1 | .lowNegative => 1 | .smallHigh _ => 4 | .farPositive _ => 1
  | .farNegative _ => 3 | .farEqual => 3 | .farHigh _ _ => 9
private def r76wd : Row→ℕ
  | .lowEqual => 20 | .lowNegative => 30 | .smallHigh _ => 15 | .farPositive _ => 20
  | .farNegative _ => 40 | .farEqual => 40 | .farHigh _ _ => 40

private theorem r76centered {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (r : Row) :
    (c.centerF (r76wn r) (r76wd r) 1 1).Rep (centered 0 (width r) p) := by
  apply hc.centeredF _ _ 1 1 <;> cases r <;> norm_num [r76wn,r76wd,width,left,right]

private def r76n : Row→Split→Fin 4→ℕ
  | .lowEqual,.atA => ![1159353078229,1159353078229,1534718749478,0]
  | .lowEqual,.atT => ![1159353078229,1159353078229,1534718749478,0]
  | .lowNegative,.atA => ![1185200213297,1185200213297,1468541525323,0]
  | .lowNegative,.atT => ![1185200213297,1185200213297,1468541525323,0]
  | .farEqual,.atA => ![1168770721741,1138121698237,1412934888804,1437737458648]
  | .farEqual,.atT => ![1168770721741,1138121698237,1412934888804,1455844098859]
  | .smallHigh i,.atA => (![![1165619171288,1203257511923,1425785990252,1425785990252],![1203257511923,1165619171288,1425785990252,1425785990252],![1203257511923,1203257511923,1377482985861,1425785990252]] : Fin 3→Fin 4→ℕ) i
  | .smallHigh i,.atT => (![![1165619171288,1203257511923,1425785990252,1451171530871],![1203257511923,1165619171288,1425785990252,1451171530871],![1203257511923,1203257511923,1377482985861,1451171530871]] : Fin 3→Fin 4→ℕ) i
  | .farPositive i,.atA => (![![1219353695259,1168770721741,1494021418855,1494021418855],![1168770721741,1168770721741,1566438694924,1494021418855],![1168770721741,1168770721741,1494021418855,1566438694924]] : Fin 3→Fin 4→ℕ) i
  | .farPositive i,.atT => (![![1219353695259,1168770721741,1494021418855,1494021418855],![1168770721741,1168770721741,1566438694924,1494021418855],![1168770721741,1168770721741,1494021418855,1566438694924]] : Fin 3→Fin 4→ℕ) i
  | .farNegative i,.atA => (![![1168770721741,1138121698237,1412934888804,1437737458648],![1168770721741,1138121698237,1412934888804,1437737458648]] : Fin 2→Fin 4→ℕ) i
  | .farNegative i,.atT => (![![1168770721741,1138121698237,1412934888804,1455844098859],![1168770721741,1138121698237,1412934888804,1455844098859]] : Fin 2→Fin 4→ℕ) i
  | .farHigh i true,.atA => (![![1168770721741,1092760266481,1292248524858,1357131625893],![1168770721741,1092760266481,1292248524858,1357131625893],![1168770721741,1092760266481,1292248524858,1357131625893]] : Fin 3→Fin 4→ℕ) i
  | .farHigh i true,.atT => (![![1168770721741,1092760266481,1292248524858,1383095713878],![1168770721741,1092760266481,1292248524858,1383095713878],![1168770721741,1092760266481,1292248524858,1383095713878]] : Fin 3→Fin 4→ℕ) i
  | .farHigh i false,.atA => (![![1088671143967,1092760266481,1292248524858,1357131625893],![1168770721741,1014681562034,1292248524858,1357131625893],![1168770721741,1092760266481,1191791502104,1357131625893]] : Fin 3→Fin 4→ℕ) i
  | .farHigh i false,.atT => (![![1088671143967,1092760266481,1292248524858,1383095713878],![1168770721741,1014681562034,1292248524858,1383095713878],![1168770721741,1092760266481,1191791502104,1383095713878]] : Fin 3→Fin 4→ℕ) i


private def r76M (r : Row) (ep : Split) (i : Fin 4) : Scaled := r76mass r ep i (r76n r ep i)
private def r76num (r : Row) (ep : Split) : Scaled := r76numB r ep (r76M r ep)

private def r76mr (r : Row) (i : Fin 4) : ℤ×ℕ :=
  if active r i then
    match family r with
    | .smallLow => (23,20) | .smallHigh => (83,100) | .farLow => (101,100) | .farHigh => (3,4)
  else (0,1)
private def r76rr (r : Row) : ℤ×ℕ :=
  match family r with
  | .smallLow => (49,10000) | .smallHigh => (27,500) | .farLow => (61,5000) | .farHigh => (29,2500)

/-- The integer facts of one row and split, checked by one kernel evaluation. -/
private abbrev r76Facts (r : Row) (ep : Split) : Prop :=
  (∀ i,active r i → (r76P r ep i).s≠0 ∧ 0<(r76P r ep i).l.getD 0 0 ∧
    r76n r ep i*r76n r ep i≤((r76P r ep i).l.getD 0 0).toNat*1000000000000000000000000/
      (r76P r ep i).s ∧
    ((r76P r ep i).l.getD 0 0).toNat*1000000000000000000000000/(r76P r ep i).s<
      (r76n r ep i+1)*(r76n r ep i+1) ∧
    0<r76rhoJ (r76P r ep i) (r76n r ep i) ∧
    (2*(r76rhoJ (r76P r ep i) (r76n r ep i):ℤ)-1)^2*(r76P r ep i).s≤
      4*(r76P r ep i).l.getD 0 0*1000000000000000000000000 ∧
    4*(r76P r ep i).l.getD 0 0*1000000000000000000000000<
      (2*(r76rhoJ (r76P r ep i) (r76n r ep i):ℤ)+1)^2*(r76P r ep i).s) ∧
  (∀ i,((r76M r ep i).centerF (r76wn r) (r76wd r) 1 1).s≠0 ∧
    ((r76M r ep i).centerF (r76wn r) (r76wd r) 1 1).l.length≤3+1 ∧ (r76mr r i).2≠0 ∧
    (chebF ((r76M r ep i).centerF (r76wn r) (r76wd r) 1 1).l).length≤3+1 ∧
    (r76mr r i).1*((((r76M r ep i).centerF (r76wn r) (r76wd r) 1 1).s*
      2^((r76M r ep i).centerF (r76wn r) (r76wd r) 1 1).l.length:ℕ):ℤ)<
      2*lowL (chebF ((r76M r ep i).centerF (r76wn r) (r76wd r) 1 1).l)*
        (r76mr r i).2) ∧
  (affineCertificate r=false →
    ((r76num r ep).centerF (r76wn r) (r76wd r) 1 1).s≠0 ∧
    ((r76num r ep).centerF (r76wn r) (r76wd r) 1 1).l.length≤39+1 ∧ (r76rr r).2≠0 ∧
    (chebF ((r76num r ep).centerF (r76wn r) (r76wd r) 1 1).l).length≤39+1 ∧
    (r76rr r).1*((((r76num r ep).centerF (r76wn r) (r76wd r) 1 1).s*
      2^((r76num r ep).centerF (r76wn r) (r76wd r) 1 1).l.length:ℕ):ℤ)<
      2*lowL (chebF ((r76num r ep).centerF (r76wn r) (r76wd r) 1 1).l)*
        (r76rr r).2) ∧
  (affineCertificate r=true →
    (r76num r ep).s≠0 ∧ (r76num r ep).l.length≤40 ∧
    13*((r76num r ep).s:ℤ)<2000*(r76num r ep).l.getD 0 0 ∧
    ((r76num r ep).divX.centerF (r76wn r) (r76wd r) 1 1).s≠0 ∧
    ((r76num r ep).divX.centerF (r76wn r) (r76wd r) 1 1).l.length≤38+1 ∧ (250:ℕ)≠0 ∧
    (chebF ((r76num r ep).divX.centerF (r76wn r) (r76wd r) 1 1).l).length≤38+1 ∧
    (1:ℤ)*((((r76num r ep).divX.centerF (r76wn r) (r76wd r) 1 1).s*
      2^((r76num r ep).divX.centerF (r76wn r) (r76wd r) 1 1).l.length:ℕ):ℤ)<
      2*lowL (chebF ((r76num r ep).divX.centerF (r76wn r) (r76wd r) 1 1).l)*
        (250:ℕ))

/-! ### The kernel checks, one row at a time

Both splits of a row share their masses and most of their numerator, so they are checked in
one kernel evaluation. -/

private abbrev r76Both (r : Row) : Prop := r76Facts r .atA ∧ r76Facts r .atT

set_option synthInstance.maxSize 4096 in
private theorem r76f_lowEqual : r76Both .lowEqual := by
  decide +kernel
set_option synthInstance.maxSize 4096 in
private theorem r76f_lowNegative : r76Both .lowNegative := by
  decide +kernel
set_option synthInstance.maxSize 4096 in
private theorem r76f_farEqual : r76Both .farEqual := by
  decide +kernel
set_option synthInstance.maxSize 4096 in
private theorem r76f_smallHigh (i : Fin 3) : r76Both (.smallHigh i) := by
  fin_cases i <;> decide +kernel
set_option synthInstance.maxSize 4096 in
private theorem r76f_farPositive (i : Fin 3) : r76Both (.farPositive i) := by
  fin_cases i <;> decide +kernel
set_option synthInstance.maxSize 4096 in
private theorem r76f_farNegative (i : Fin 2) : r76Both (.farNegative i) := by
  fin_cases i <;> decide +kernel
set_option synthInstance.maxSize 4096 in
private theorem r76f_farHigh_false (i : Fin 3) : r76Both (.farHigh i false) := by
  fin_cases i <;> decide +kernel
set_option synthInstance.maxSize 4096 in
private theorem r76f_farHigh_true (i : Fin 3) : r76Both (.farHigh i true) := by
  fin_cases i <;> decide +kernel

private theorem r76facts (r : Row) (ep : Split) : r76Facts r ep := by
  have h : r76Both r := by
    rcases r with _|_|i|i|i|_|⟨i,_|_⟩
    · exact r76f_lowEqual
    · exact r76f_lowNegative
    · exact r76f_smallHigh i
    · exact r76f_farPositive i
    · exact r76f_farNegative i
    · exact r76f_farEqual
    · exact r76f_farHigh_false i
    · exact r76f_farHigh_true i
  cases ep
  · exact h.1
  · exact h.2


/-! ### From the integer facts to the stated certificates -/

private theorem r76M_rep (r : Row) (ep : Split) (i : Fin 4) : (r76M r ep i).Rep (mass r ep i) :=
  r76mass_rep r ep i _ (fun ha => by
    obtain ⟨h1,h2,h3,h4,-⟩ := (r76facts r ep).1 i ha
    exact ⟨h1,h2,h3,h4⟩)

private theorem r76num_rep (r : Row) (ep : Split) : (r76num r ep).Rep (numerator r ep) :=
  r76numB_rep r ep (r76M_rep r ep)

private theorem r76mr_eq (r : Row) (i : Fin 4) :
    (if active r i then massReserve r else 0)=(((r76mr r i).1:ℤ):ℚ)/((r76mr r i).2:ℕ) := by
  unfold r76mr massReserve
  split_ifs
  · cases family r <;> norm_num
  · norm_num

private theorem r76rr_eq (r : Row) : reserve r=(((r76rr r).1:ℤ):ℚ)/((r76rr r).2:ℕ) := by
  unfold r76rr reserve
  cases family r <;> norm_num

private theorem r76quot {p : ℚ[X]} (hp : p.natDegree≤39) :
    (∑i : Fin 39,C (p.coeff (i.val+1))*X^i.val)=divX p := by
  ext n
  rw [finsetSum_coeff,coeff_divX]
  simp only [coeff_C_mul_X_pow]
  rw [Fin.sum_univ_eq_sum_range (fun i => if n=i then p.coeff (i+1) else 0) 39,
    Finset.sum_ite_eq]
  split_ifs with hn
  · rfl
  · rw [Finset.mem_range,not_lt] at hn
    exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm

theorem mass_certificate : ∀r : Row,∀ep : Split,∀i : Fin 4,
    centered 0 (width r) (mass r ep i)=expansion 3 (centered 0 (width r) (mass r ep i)) ∧
    (if active r i then massReserve r else 0)<lowerOn 3 0 (width r) (mass r ep i) := by
  intro r ep i
  rw [r76mr_eq]
  exact r76cert (r76centered (r76M_rep r ep i) r) ((r76facts r ep).2.1 i)

theorem direct_certificate : ∀r : Row,∀ep : Split,affineCertificate r=false →
    centered 0 (width r) (numerator r ep)=
      expansion 39 (centered 0 (width r) (numerator r ep)) ∧
    reserve r<lowerOn 39 0 (width r) (numerator r ep) := by
  intro r ep ha
  rw [r76rr_eq]
  exact r76cert (r76centered (r76num_rep r ep) r) ((r76facts r ep).2.2.1 ha)

theorem affine_certificate : ∀r : Row,∀ep : Split,affineCertificate r=true →
    numerator r ep=C ((numerator r ep).coeff 0)+X*quotient r ep ∧
    (13/2000:ℚ)<(numerator r ep).coeff 0 ∧
    centered 0 (width r) (quotient r ep)=
      expansion 38 (centered 0 (width r) (quotient r ep)) ∧
    (1/250:ℚ)<lowerOn 38 0 (width r) (quotient r ep) := by
  intro r ep ha
  obtain ⟨h1,h2,h3,h4⟩ := (r76facts r ep).2.2.2 ha
  have hN := r76num_rep r ep
  have hq : quotient r ep=divX (numerator r ep) :=
    r76quot ((hN.natDegree_le h1).trans (by omega))
  have hc := r76cert (r76centered hN.divX r) h4
  rw [hq]
  refine ⟨(X_mul_divX_add _).symm.trans (add_comm _ _),?_,hc.1,?_⟩
  · rw [hN.coeff h1 0]
    have hs : (0:ℚ)<(r76num r ep).s := by exact_mod_cast Nat.pos_of_ne_zero h1
    rw [lt_div_iff₀ hs]
    have h3' : ((13*((r76num r ep).s:ℤ):ℤ):ℚ)<((2000*(r76num r ep).l.getD 0 0:ℤ):ℚ) := by
      exact_mod_cast h3
    push_cast at h3'
    linarith
  · have h := hc.2
    norm_num at h
    exact h

theorem mass_positive (r : Row) (ep : Split) (i : Fin 4) {x : ℝ}
    (hx : x∈Icc 0 (width r:ℝ)) : 0<aeval x (mass r ep i) := by
  have hc := mass_certificate r ep i
  have hh := positive_on_interval (interval_positive r) hc.1 hc.2
    (show x∈Icc ((0:ℚ):ℝ) (width r:ℝ) by simpa using hx)
  have hreserve : (0:ℝ)≤((if active r i then massReserve r else 0:ℚ):ℝ) := by
    split_ifs
    · cases r <;> norm_num [massReserve,family]
    · norm_num
  exact hreserve.trans_lt hh

theorem numerator_positive (r : Row) (ep : Split) {x : ℝ}
    (hx : x∈Icc 0 (width r:ℝ)) : 0<aeval x (numerator r ep) := by
  have hx' : x∈Icc ((0:ℚ):ℝ) (width r:ℝ) := by simpa using hx
  cases ha : affineCertificate r
  · have hc := direct_certificate r ep ha
    have hh := positive_on_interval (interval_positive r) hc.1 hc.2 hx'
    have hr : (0:ℝ)<(reserve r:ℝ) := by cases r <;> norm_num [reserve,family]
    exact hr.trans hh
  · have hc := affine_certificate r ep ha
    have hq := positive_on_interval (interval_positive r) hc.2.2.1 hc.2.2.2 hx'
    have hconst : (13/2000:ℝ)<((numerator r ep).coeff 0:ℝ) := by
      have h := (Rat.cast_lt (K:=ℝ)).mpr hc.2.1
      rwa [show (((13/2000:ℚ)):ℝ)=13/2000 by norm_num] at h
    have he := congrArg (fun p : ℚ[X] => aeval x p) hc.1
    simp only [map_add,map_mul,aeval_C,aeval_X,eq_ratCast] at he
    have hm := mul_nonneg hx.1 (show 0≤aeval x (quotient r ep) by linarith)
    linarith

end SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.Certificate
