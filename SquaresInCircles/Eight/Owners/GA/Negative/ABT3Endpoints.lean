module

public import SquaresInCircles.Eight.Owners.GA.Negative.ELowAStress
public import SquaresInCircles.Eight.Owners.GA.Negative.ABT3Polynomial
public import SquaresInCircles.Eight.Owners.GA.Negative.ABT3PolynomialData
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2LowABSlope
public import SquaresInCircles.Eight.Owners.GA.Nonnegative.TotalsNorms

/-!
# Eight squares: the fourteen actual reference endpoint inequalities

Each endpoint follows from its exact rational
numerator, the separately positive cubic masses, the norm square bounds,
and the signed nonradical Taylor comparison. The cosine scale is removed
only after its positivity has been established.
-/

section
/-!
## Exact radical forms of the fourteen reference endpoints

The secant cancellation is exact
before any Taylor bound. The native polynomial variable is always
the actual endpoint parameter minus its stated left endpoint.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.GlobalGA.NegativeABT3
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

def nonradical (f : Certificate.Family) (z : ℝ) : ℝ :=
  if f=.low then 2*Explicit.k f z+3*Explicit.l f z+5/2-GlobalGA.Secondary.diagonal+
    Explicit.m f z*(1+(3/2-GlobalGA.Secondary.diagonal)*Real.cos z+
      (1/2+PositiveTD.eta*(1-GlobalGA.Secondary.diagonal)-PositiveTD.sigma)*Real.sin z)
  else 2*Explicit.k f z+3*Explicit.l f z+3+
    Explicit.m f z*(1+2*Real.cos z+(1/2+3*PositiveTD.eta/2-PositiveTD.sigma)*Real.sin z)

theorem reduced_identity (f : Certificate.Family) (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hs : s∈Icc 0 frameCap) :
    reducedBaseline f atG s z=nonradical f z+secant (Explicit.l f z) s-Explicit.l f z+
      (13/12)*Explicit.l f z*Real.tan s-
      R*normSum f (norms atG (Explicit.k f z) (Explicit.l f z) (Explicit.m f z) s z) := by
  have hwidth := NegativeAPositiveTD.secant_width_identity (l:=Explicit.l f z) hs
  have hzf := Explicit.frame_domain f hz
  cases f
  · have hz' : z∈Icc (0:ℝ) (1/4) := by
      have h := hz
      norm_num [Certificate.left,Certificate.right,Certificate.split] at h
      exact h
    have hc : 1≤PositiveBT3.tilted (Explicit.m .low z) z := (Explicit.low_rotation hz').1.le
    simp only [PositiveBT3.tilted] at hc
    cases atG <;>
      simp only [reducedBaseline,baseline,nonradical,normSum,NegativeAPositiveTD.normSum,norms,
        lambdaG,lambdaB,NegativeAPositiveTD.lambdaG,NegativeAPositiveTD.lambdaB,↓reduceIte,
        Bool.false_eq_true,Matrix.cons_val,fullSupport_pair,clippedSupport,
        PositiveBT3.tilted,hc,diagonalSupport,edgeWidth_positive_formula hzf]
      <;> linear_combination hwidth
  · cases atG <;>
      simp only [reducedBaseline,baseline,nonradical,normSum,NegativeAPositiveTD.normSum,norms,
        lambdaG,lambdaB,NegativeAPositiveTD.lambdaG,NegativeAPositiveTD.lambdaB,↓reduceIte,
        Bool.false_eq_true,reduceCtorEq,Matrix.cons_val,fullSupport_pair,
        pairNorm_symm (Explicit.m .high z*(Real.cos z+PositiveTD.eta*Real.sin z)) 1,
        edgeWidth_positive_formula hzf,Explicit.c,PositiveBT3.tilted]
      <;> linear_combination hwidth

namespace Analytic
open Certificate (Curve)

def Domain (e : Curve) (z : ℝ) : Prop := z∈Icc (Certificate.start e:ℝ) (Certificate.right (Certificate.family e):ℝ)
def angle : Curve→ℝ→ℝ
  | .lowGA,z | .highGA,z | .highAB,z => z
  | .gaH,_ | .gaB,_ => 1/4
  | .abG,_ | .abH,_ => 19/50
  | _,_ => 0
def negativeAngle (e : Curve) (z : ℝ) : ℝ :=
  match e with
  | .lowSH | .lowSG => frameCap
  | .gaH | .gaB | .abG | .abH => z-angle e z
  | _ => z
def cost (e : Curve) (z : ℝ) : ℝ :=
  match Certificate.selected e with
  | none => 0
  | some j => if j=0 then 1 else Explicit.l (Certificate.family e) z
def extra (e : Curve) (z : ℝ) : ℝ :=
  if e=.lowM then Explicit.k .low z*(PositiveAngularEnvelope.phi (frameCap-z)-1)+Explicit.l .low z*(Real.cos frameCap-1)
  else cost e z*(Real.cos (negativeAngle e z)-1)-
    if Certificate.separated e then (109/160)*(frameCap-z) else 0
def p (e : Curve) (z : ℝ) : Fin 4→ℝ :=
  ![Explicit.k (Certificate.family e) z,Explicit.k (Certificate.family e) z,
    Explicit.m (Certificate.family e) z,1]
def q (e : Curve) (z : ℝ) : Fin 4→ℝ :=
  ![1,lambdaG (Certificate.atG e) (Explicit.l (Certificate.family e) z) (angle e z),
    lambdaB (Certificate.atG e) (Explicit.l (Certificate.family e) z) (angle e z),
    Explicit.c (Certificate.family e) z]
def norm (e : Curve) (z : ℝ) (i : Fin 4) : ℝ :=
  pairNorm (p e z i) (q e z i) (if Certificate.selected e=some i then -negativeAngle e z else 0)
def scale (e : Curve) (z : ℝ) : ℝ := if Certificate.scaled e then Real.cos (angle e z) else 1
def scaledNorm (e : Curve) (z : ℝ) (i : Fin 4) : ℝ := scale e z*norm e z i
def nonradical (e : Curve) (z : ℝ) : ℝ :=
  if Certificate.scaled e then Real.cos (angle e z)*(NegativeABT3.nonradical (Certificate.family e) z-
      Explicit.l (Certificate.family e) z)+Explicit.l (Certificate.family e) z+
      (13/12)*Explicit.l (Certificate.family e) z*Real.sin (angle e z)+Real.cos (angle e z)*extra e z
  else NegativeABT3.nonradical (Certificate.family e) z+extra e z
def charge (e : Curve) (z : ℝ) : ℝ :=
  match e with
  | .lowM => mixedG (Explicit.k .low z) (Explicit.l .low z) z
  | .lowSH => -(109/160)*(frameCap-z)+V R (Explicit.k .low z) 1 frameCap
  | .lowSG => -(109/160)*(frameCap-z)+V R (Explicit.k .low z) (Explicit.l .low z) frameCap
  | .lowH | .highH | .gaH | .abH => V R (Explicit.k (Certificate.family e) z) 1 (negativeAngle e z)
  | .highG | .abG => V R (Explicit.k .high z) (Explicit.l .high z) (negativeAngle e z)
  | .highB | .gaB => V R (Explicit.m .high z) (Explicit.l .high z) (negativeAngle e z)
  | _ => 0
def curve (e : Curve) (z : ℝ) : ℝ :=
  reducedBaseline (Certificate.family e) (Certificate.atG e) (angle e z) z+charge e z

theorem native_domain (e : Curve) {z : ℝ} (hz : Domain e z) :
    z-(Certificate.start e:ℝ)∈Icc 0 (Certificate.length e:ℝ) := by
  dsimp [Domain,Certificate.length] at *
  push_cast
  exact ⟨by linarith [hz.1],by linarith [hz.2]⟩

theorem domains (e : Curve) {z : ℝ} (hz : Domain e z) :
    z∈Icc (Certificate.left (Certificate.family e):ℝ) (Certificate.right (Certificate.family e):ℝ) ∧
    angle e z∈Icc 0 frameCap ∧ negativeAngle e z∈Icc 0 frameCap ∧ frameCap-z∈Icc 0 frameCap := by
  cases e <;> norm_num [Domain,Certificate.start,Certificate.family,Certificate.left,Certificate.right,
    Certificate.split,angle,negativeAngle,frameCap] at hz ⊢ <;>
    (repeat' constructor) <;> linarith [hz.1,hz.2]

@[simp] theorem native_z (e : Curve) (z : ℝ) :
    aeval (z-(Certificate.start e:ℝ)) (Certificate.z e)=z := by
  simp [Certificate.z]
@[simp] theorem native_k (e : Curve) (z : ℝ) :
    aeval (z-(Certificate.start e:ℝ)) (Certificate.kAt e)=Explicit.k (Certificate.family e) z := by
  simp [Certificate.kAt,aeval_comp]
@[simp] theorem native_l (e : Curve) (z : ℝ) :
    aeval (z-(Certificate.start e:ℝ)) (Certificate.lAt e)=Explicit.l (Certificate.family e) z := by
  simp [Certificate.lAt,aeval_comp]
@[simp] theorem native_m (e : Curve) (z : ℝ) :
    aeval (z-(Certificate.start e:ℝ)) (Certificate.mAt e)=Explicit.m (Certificate.family e) z := by
  simp [Certificate.mAt,aeval_comp]
@[simp] theorem native_angle (e : Curve) (z : ℝ) :
    aeval (z-(Certificate.start e:ℝ)) (Certificate.angle e)=angle e z := by
  cases e <;> simp [Certificate.angle,angle]
@[simp] theorem native_negativeAngle (e : Curve) (z : ℝ) :
    aeval (z-(Certificate.start e:ℝ)) (Certificate.negativeAngle e)=negativeAngle e z := by
  cases e <;> simp [Certificate.negativeAngle,negativeAngle,PositiveTD.Certificate.h,frameCap]
@[simp] theorem native_cost (e : Curve) (z : ℝ) :
    aeval (z-(Certificate.start e:ℝ)) (Certificate.cost e)=cost e z := by
  cases e <;> simp [Certificate.cost,Certificate.selected,cost]

theorem scale_positive (e : Curve) {z : ℝ} (hz : Domain e z) : 0<scale e z := by
  have hc : 0<Real.cos (angle e z) := by linarith [(transport_trig (domains e hz).2.1).1]
  dsimp [scale]
  split_ifs <;> positivity

theorem curve_identity (e : Curve) {z : ℝ} (hz : Domain e z) :
    scale e z*curve e z=nonradical e z-R*normSum (Certificate.family e) (scaledNorm e z) := by
  have hd := domains e hz
  have he := reduced_identity (Certificate.family e) (Certificate.atG e) hd.1 hd.2.1
  have hc : Real.cos (angle e z)≠0 := (show 0<Real.cos (angle e z) by
    linarith [(transport_trig hd.2.1).1]).ne'
  unfold curve
  rw [he]
  cases e <;>
    simp [scale,scaledNorm,norm,nonradical,extra,charge,angle,negativeAngle,p,q,cost,
      Certificate.scaled,Certificate.family,Certificate.atG,Certificate.selected,Certificate.separated,
      normSum,NegativeAPositiveTD.normSum,norms,lambdaG,lambdaB,secant,
      NegativeAPositiveTD.lambdaG,NegativeAPositiveTD.lambdaB,NegativeAPositiveTD.secant,
      mixedG,NegativeAPositiveTD.mixedG,V,Real.tan_eq_sin_div_cos,Explicit.c] at hc ⊢ <;>
    field_simp [hc] <;> ring

end Analytic
end SquaresInCircles.Eight.GlobalGA.NegativeABT3
end
end
end

section
/-!
## Nonradical lower bounds for the reference endpoints

The low diagonal term uses its rational upper
constant. Every cosine-scaled positive baseline factor is proved
positive first, and the negative angular cost is multiplied by the
upper cosine polynomial, as required by its sign.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.GlobalGA.NegativeABT3
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

namespace Certificate
open WholeIntervalPolynomial

/-! ### Kernel certificate of the baseline factor (scaled integer lists, as in
`GlobalGANegativeABT3Polynomial`) -/

section Certificates
open WholeIntervalPolynomial.Certificate
open PositiveTD.Certificate (S5 S9 S11 C4 C10 C12 etaQ cbar sigmabar)

private def gcdAcc : List ℤ → ℕ → ℕ
  | [],g => g
  | x :: l,g => gcdAcc l (Nat.gcd x.natAbs g)

private theorem gcdAcc_dvd_acc : ∀ (l : List ℤ) (g : ℕ),gcdAcc l g∣g
  | [],_ => dvd_rfl
  | _ :: l,_ => (gcdAcc_dvd_acc l _).trans (Nat.gcd_dvd_right _ _)

private theorem gcdAcc_dvd_mem : ∀ (l : List ℤ) (g : ℕ),∀ x∈l,((gcdAcc l g:ℕ):ℤ)∣x
  | [],_,_,hx => by simp at hx
  | _ :: l,_,x,hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact Int.natCast_dvd.2 ((gcdAcc_dvd_acc l _).trans (Nat.gcd_dvd_left _ _))
    · exact gcdAcc_dvd_mem l _ x hx

private theorem toPoly_map_div (g : ℤ) : ∀ l : List ℤ,(∀ x∈l,g∣x) →
    toPoly l=C (g:ℚ)*toPoly (l.map (fun x => x/g))
  | [],_ => by simp [toPoly]
  | x :: l,h => by
    have hx : (x:ℚ)=(g:ℚ)*((x/g:ℤ):ℚ) := by
      rw [← Int.cast_mul,Int.mul_ediv_cancel' (h x List.mem_cons_self)]
    rw [List.map_cons,toPoly,toPoly,
      toPoly_map_div g l (fun y hy => h y (List.mem_cons_of_mem _ hy)),hx,C_mul]
    ring

private theorem toPoly_map_div_zero : ∀ l : List ℤ,toPoly (l.map (fun x => x/(0:ℤ)))=0
  | [] => by simp [toPoly]
  | x :: l => by rw [List.map_cons,toPoly,toPoly_map_div_zero l,Int.ediv_zero]; simp

private def trim : List ℤ → List ℤ
  | [] => []
  | x :: l => match trim l with
    | [] => if x=0 then [] else [x]
    | y :: t => x :: y :: t

private theorem toPoly_trim : ∀ l : List ℤ,toPoly (trim l)=toPoly l
  | [] => rfl
  | x :: l => by
    have ih := toPoly_trim l
    simp only [trim]
    split
    · rename_i h
      rw [h] at ih
      change (0:ℚ[X])=toPoly l at ih
      change _=C (x:ℚ)+X*toPoly l
      rw [← ih]
      split_ifs with hx
      · rw [hx]; simp [toPoly]
      · change C (x:ℚ)+X*0=_
        rfl
    · rename_i y t h
      rw [h] at ih
      change C (x:ℚ)+X*toPoly (y :: t)=C (x:ℚ)+X*toPoly l
      rw [ih]

/-- The list divided by the gcd of its entries and its scale, without trailing zeros. -/
private def nrm (a : Scaled) : Scaled :=
  ⟨trim (a.l.map (fun x => x/((gcdAcc a.l a.s:ℕ):ℤ))),a.s/gcdAcc a.l a.s⟩

private theorem rep_nrm {a : Scaled} {p : ℚ[X]} (ha : a.Rep p) : (nrm a).Rep p := by
  unfold Scaled.Rep at *
  rw [nrm,toPoly_trim]
  have h1 := toPoly_map_div ((gcdAcc a.l a.s:ℕ):ℤ) a.l (gcdAcc_dvd_mem a.l a.s)
  have h2 : gcdAcc a.l a.s∣a.s := gcdAcc_dvd_acc a.l a.s
  generalize gcdAcc a.l a.s=g at h1 h2
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · have hs : a.s=0 := Nat.eq_zero_of_zero_dvd h2
    simp only [Nat.cast_zero,Nat.div_zero,map_zero,zero_mul] at h1 ⊢
    exact toPoly_map_div_zero a.l
  · have hgq : (g:ℚ)≠0 := by exact_mod_cast hg.ne'
    have hdiv : ((a.s/g:ℕ):ℚ)=(a.s:ℚ)/g := Nat.cast_div h2 hgq
    apply mul_left_cancel₀ (show (C (g:ℚ):ℚ[X])≠0 from C_ne_zero.2 hgq)
    push_cast at h1
    rw [← h1,ha,hdiv,← mul_assoc,← C_mul,mul_div_cancel₀ _ hgq]

/-! #### Normalized operations -/

private def nadd (a b : Scaled) : Scaled := nrm (a.add b)
private def nsub (a b : Scaled) : Scaled := nrm (a.sub b)
private def nmul (a b : Scaled) : Scaled := nrm (a.mul b)
private def npow (a : Scaled) : ℕ → Scaled
  | 0 => Scaled.ofNat 1
  | n+1 => nmul (npow a n) a
private def ncst (q : ℚ) : Scaled := Scaled.const q
private def none' : Scaled := ⟨[],1⟩

private theorem rep_nadd {a b : Scaled} {p q : ℚ[X]} (ha : a.Rep p) (hb : b.Rep q) :
    (nadd a b).Rep (p+q) := rep_nrm (ha.add hb)
private theorem rep_nsub {a b : Scaled} {p q : ℚ[X]} (ha : a.Rep p) (hb : b.Rep q) :
    (nsub a b).Rep (p-q) := rep_nrm (ha.sub hb)
private theorem rep_nmul {a b : Scaled} {p q : ℚ[X]} (ha : a.Rep p) (hb : b.Rep q) :
    (nmul a b).Rep (p*q) := rep_nrm (ha.mul hb)
private theorem rep_npow {a : Scaled} {p : ℚ[X]} (ha : a.Rep p) : ∀ n : ℕ,(npow a n).Rep (p^n)
  | 0 => by rw [pow_zero]; exact Scaled.rep_one
  | n+1 => by rw [pow_succ]; exact rep_nmul (rep_npow ha n) ha
private theorem rep_ncst (q : ℚ) : (ncst q).Rep (C q) := Scaled.rep_const q

/-! #### Polynomials in a represented argument -/

private def bS5 (v : Scaled) : Scaled :=
  nadd (nsub v (nmul (ncst (1/6)) (npow v 3))) (nmul (ncst (1/120)) (npow v 5))
private theorem rep_bS5 {v : Scaled} {q : ℚ[X]} (hv : v.Rep q) : (bS5 v).Rep (S5.comp q) := by
  have e : S5.comp q=q-C (1/6)*q^3+C (1/120)*q^5 := by
    simp only [S5,add_comp,sub_comp,mul_comp,C_comp,X_comp,pow_comp]
  rw [e]
  exact rep_nadd (rep_nsub hv (rep_nmul (rep_ncst _) (rep_npow hv 3)))
    (rep_nmul (rep_ncst _) (rep_npow hv 5))
private def bS9 (v : Scaled) : Scaled :=
  nadd (nsub (bS5 v) (nmul (ncst (1/5040)) (npow v 7))) (nmul (ncst (1/362880)) (npow v 9))
private theorem rep_bS9 {v : Scaled} {q : ℚ[X]} (hv : v.Rep q) : (bS9 v).Rep (S9.comp q) := by
  have e : S9.comp q=S5.comp q-C (1/5040)*q^7+C (1/362880)*q^9 := by
    simp only [S9,add_comp,sub_comp,mul_comp,C_comp,X_comp,pow_comp]
  rw [e]
  exact rep_nadd (rep_nsub (rep_bS5 hv) (rep_nmul (rep_ncst _) (rep_npow hv 7)))
    (rep_nmul (rep_ncst _) (rep_npow hv 9))
private def bS11 (v : Scaled) : Scaled := nsub (bS9 v) (nmul (ncst (1/39916800)) (npow v 11))
private theorem rep_bS11 {v : Scaled} {q : ℚ[X]} (hv : v.Rep q) : (bS11 v).Rep (S11.comp q) := by
  have e : S11.comp q=S9.comp q-C (1/39916800)*q^11 := by
    simp only [S11,sub_comp,mul_comp,C_comp,X_comp,pow_comp]
  rw [e]
  exact rep_nsub (rep_bS9 hv) (rep_nmul (rep_ncst _) (rep_npow hv 11))
private def bC4 (v : Scaled) : Scaled :=
  nadd (nsub (Scaled.ofNat 1) (nmul (ncst (1/2)) (npow v 2))) (nmul (ncst (1/24)) (npow v 4))
private theorem rep_bC4 {v : Scaled} {q : ℚ[X]} (hv : v.Rep q) : (bC4 v).Rep (C4.comp q) := by
  have e : C4.comp q=1-C (1/2)*q^2+C (1/24)*q^4 := by
    simp only [C4,add_comp,sub_comp,mul_comp,C_comp,X_comp,pow_comp,one_comp]
  rw [e]
  exact rep_nadd (rep_nsub Scaled.rep_one (rep_nmul (rep_ncst _) (rep_npow hv 2)))
    (rep_nmul (rep_ncst _) (rep_npow hv 4))
private def bC10 (v : Scaled) : Scaled :=
  nsub (nadd (nsub (bC4 v) (nmul (ncst (1/720)) (npow v 6))) (nmul (ncst (1/40320)) (npow v 8)))
    (nmul (ncst (1/3628800)) (npow v 10))
private theorem rep_bC10 {v : Scaled} {q : ℚ[X]} (hv : v.Rep q) : (bC10 v).Rep (C10.comp q) := by
  have e : C10.comp q=C4.comp q-C (1/720)*q^6+C (1/40320)*q^8-C (1/3628800)*q^10 := by
    simp only [C10,add_comp,sub_comp,mul_comp,C_comp,X_comp,pow_comp]
  rw [e]
  exact rep_nsub (rep_nadd (rep_nsub (rep_bC4 hv) (rep_nmul (rep_ncst _) (rep_npow hv 6)))
    (rep_nmul (rep_ncst _) (rep_npow hv 8))) (rep_nmul (rep_ncst _) (rep_npow hv 10))
private def bC12 (v : Scaled) : Scaled := nadd (bC10 v) (nmul (ncst (1/479001600)) (npow v 12))
private theorem rep_bC12 {v : Scaled} {q : ℚ[X]} (hv : v.Rep q) : (bC12 v).Rep (C12.comp q) := by
  have e : C12.comp q=C10.comp q+C (1/479001600)*q^12 := by
    simp only [C12,add_comp,mul_comp,C_comp,X_comp,pow_comp]
  rw [e]
  exact rep_nadd (rep_bC10 hv) (rep_nmul (rep_ncst _) (rep_npow hv 12))

/-! #### The two families -/

private def bk : Family → Scaled → Scaled
  | .low,v => nadd (ncst (2/3)) (nmul (ncst (1/20)) v)
  | .high,v =>
    let t := nsub v (ncst (1/5))
    nsub (nadd (nadd (ncst (169/250)) (nmul (ncst (1/5)) t)) (nmul (ncst (9/10)) (npow t 2)))
      (nmul (ncst (13/10)) (npow t 3))
private theorem rep_bk (f : Family) {v : Scaled} {q : ℚ[X]} (hv : v.Rep q) :
    (bk f v).Rep ((k f).comp q) := by
  cases f
  · have e : (k .low).comp q=C (2/3)+C (1/20)*q := by
      simp only [k,add_comp,mul_comp,C_comp,X_comp]
    rw [e]
    exact rep_nadd (rep_ncst _) (rep_nmul (rep_ncst _) hv)
  · have e : (k .high).comp q=C (169/250)+C (1/5)*(q-C (1/5))+C (9/10)*(q-C (1/5))^2-
        C (13/10)*(q-C (1/5))^3 := by
      simp only [k,add_comp,sub_comp,mul_comp,C_comp,X_comp,pow_comp]
    rw [e]
    have ht := rep_nsub hv (rep_ncst (1/5))
    exact rep_nsub (rep_nadd (rep_nadd (rep_ncst _) (rep_nmul (rep_ncst _) ht))
      (rep_nmul (rep_ncst _) (rep_npow ht 2))) (rep_nmul (rep_ncst _) (rep_npow ht 3))
private def bl : Family → Scaled → Scaled
  | .low,v => nsub (ncst (533/500)) (nmul (ncst (4/25)) v)
  | .high,v =>
    let t := nsub v (ncst (1/5))
    nsub (nadd (ncst (41/40)) (nmul (ncst (11/50)) t)) (nmul (ncst (3/10)) (npow t 2))
private theorem rep_bl (f : Family) {v : Scaled} {q : ℚ[X]} (hv : v.Rep q) :
    (bl f v).Rep ((l f).comp q) := by
  cases f
  · have e : (l .low).comp q=C (533/500)-C (4/25)*q := by
      simp only [l,sub_comp,mul_comp,C_comp,X_comp]
    rw [e]
    exact rep_nsub (rep_ncst _) (rep_nmul (rep_ncst _) hv)
  · have e : (l .high).comp q=C (41/40)+C (11/50)*(q-C (1/5))-C (3/10)*(q-C (1/5))^2 := by
      simp only [l,add_comp,sub_comp,mul_comp,C_comp,X_comp,pow_comp]
    rw [e]
    have ht := rep_nsub hv (rep_ncst (1/5))
    exact rep_nsub (rep_nadd (rep_ncst _) (rep_nmul (rep_ncst _) ht))
      (rep_nmul (rep_ncst _) (rep_npow ht 2))
private def bm : Family → Scaled → Scaled
  | .low,v => nsub (nadd (ncst (59/50)) (nmul (ncst (1/10)) v)) (nmul (ncst (769/200)) (npow v 2))
  | .high,v =>
    let t := nsub v (ncst (1/4))
    nadd (nsub (ncst (24/25)) (nmul (ncst (7/10)) t)) (nmul (ncst (6/5)) (npow t 2))
private theorem rep_bm (f : Family) {v : Scaled} {q : ℚ[X]} (hv : v.Rep q) :
    (bm f v).Rep ((m f).comp q) := by
  cases f
  · have e : (m .low).comp q=C (59/50)+C (1/10)*q-C (769/200)*q^2 := by
      simp only [m,add_comp,sub_comp,mul_comp,C_comp,X_comp,pow_comp]
    rw [e]
    exact rep_nsub (rep_nadd (rep_ncst _) (rep_nmul (rep_ncst _) hv))
      (rep_nmul (rep_ncst _) (rep_npow hv 2))
  · have e : (m .high).comp q=C (24/25)-C (7/10)*(q-C (1/4))+C (6/5)*(q-C (1/4))^2 := by
      simp only [m,add_comp,sub_comp,mul_comp,C_comp,X_comp,pow_comp]
    rw [e]
    have ht := rep_nsub hv (rep_ncst (1/4))
    exact rep_nadd (rep_nsub (rep_ncst _) (rep_nmul (rep_ncst _) ht))
      (rep_nmul (rep_ncst _) (rep_npow ht 2))
private def belem : Family → Scaled → Scaled
  | .low,v => nadd (nadd (nadd (nmul (ncst 2) (bk .low v)) (nmul (ncst 3) (bl .low v)))
      (ncst (5/2-cbar))) (nmul (bm .low v) (nadd (nadd (Scaled.ofNat 1)
        (nmul (ncst (3/2-cbar)) (bC10 v))) (nmul (ncst (1/2+etaQ*(1-cbar)-sigmabar)) (bS9 v))))
  | .high,v => nadd (nadd (nadd (nmul (ncst 2) (bk .high v)) (nmul (ncst 3) (bl .high v)))
      (ncst 3)) (nmul (bm .high v) (nadd (nadd (Scaled.ofNat 1)
        (nmul (ncst 2) (bC10 v))) (nmul (ncst (1/2+3*etaQ/2-sigmabar)) (bS9 v))))
private theorem rep_belem (f : Family) {v : Scaled} {q : ℚ[X]} (hv : v.Rep q) :
    (belem f v).Rep ((elementary f).comp q) := by
  cases f
  · rw [elementary,ite_eq_left rfl]
    simp only [add_comp,mul_comp,C_comp,one_comp]
    exact rep_nadd (rep_nadd (rep_nadd (rep_nmul (rep_ncst _) (rep_bk .low hv))
      (rep_nmul (rep_ncst _) (rep_bl .low hv))) (rep_ncst _)) (rep_nmul (rep_bm .low hv)
        (rep_nadd (rep_nadd Scaled.rep_one (rep_nmul (rep_ncst _) (rep_bC10 hv)))
          (rep_nmul (rep_ncst _) (rep_bS9 hv))))
  · rw [elementary,ite_eq_right (by decide)]
    simp only [add_comp,mul_comp,C_comp,one_comp]
    exact rep_nadd (rep_nadd (rep_nadd (rep_nmul (rep_ncst _) (rep_bk .high hv))
      (rep_nmul (rep_ncst _) (rep_bl .high hv))) (rep_ncst _)) (rep_nmul (rep_bm .high hv)
        (rep_nadd (rep_nadd Scaled.rep_one (rep_nmul (rep_ncst _) (rep_bC10 hv)))
          (rep_nmul (rep_ncst _) (rep_bS9 hv))))

/-! #### The fourteen curves -/

private def bz (e : Curve) : Scaled := nadd Scaled.var (ncst (start e))
private theorem rep_bz (e : Curve) : (bz e).Rep (z e) := rep_nadd Scaled.rep_var (rep_ncst _)
private def blAt (e : Curve) : Scaled := bl (family e) (bz e)
private theorem rep_blAt (e : Curve) : (blAt e).Rep (lAt e) := rep_bl (family e) (rep_bz e)
private def bbaseA (e : Curve) : Scaled := belem (family e) (bz e)
private theorem rep_bbaseA (e : Curve) : (bbaseA e).Rep (baseA e) := rep_belem (family e) (rep_bz e)
private def cnum : Curve → ℕ
  | .lowH | .lowM | .lowSH | .lowSG | .lowGA => 1
  | .abG | .abH => 4
  | _ => 9
private def cden : Curve → ℕ
  | .lowH | .lowM | .lowSH | .lowSG | .lowGA => 8
  | .abG | .abH => 25
  | _ => 40
private theorem center_data (e : Curve) :
    cden e≠0 ∧ ((0:ℚ)+length e)/2=(cnum e:ℚ)*((1:ℤ):ℚ)/(cden e:ℚ) ∧
      (length e-(0:ℚ))/2=(cnum e:ℚ)*((1:ℤ):ℚ)/(cden e:ℚ) := by
  cases e <;> norm_num [cnum,cden,length,right,family,start,split]
private theorem rep_center {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (e : Curve) :
    (c.center (cnum e) (cden e) 1 1).Rep (WholeIntervalPolynomial.centered 0 (length e) p) :=
  hc.centered (cnum e) (cden e) 1 1 (center_data e).1 (center_data e).2.1 (center_data e).2.2

/-- The kernel-checked facts of a whole-interval bound `r < lowerOn D` for the centered list `c`. -/
private abbrev certOK (r : ℚ) (D : ℕ) (c : Scaled) : Prop :=
  c.s≠0 ∧ c.l.length≤D+1 ∧
    r.num*((c.s*2^c.l.length:ℕ):ℤ)<lowerZ D (fun i => (chebList c.l).getD i 0)*((2*r.den:ℕ):ℤ)
private theorem of_certOK {r : ℚ} {D : ℕ} {c : Scaled} {a b : ℚ} {p : ℚ[X]}
    (hc : c.Rep (WholeIntervalPolynomial.centered a b p)) (h : certOK r D c) :
    WholeIntervalPolynomial.centered a b p=expansion D (WholeIntervalPolynomial.centered a b p) ∧
      r<lowerOn D a b p := by
  obtain ⟨hs,hl,hz⟩ := h
  refine ⟨hc.eq_expansion hs hl,?_⟩
  rw [lowerOn_eq_of_rep hc hs hl]
  have hb : (0:ℚ)<r.den := by exact_mod_cast r.pos
  have hs' : (0:ℚ)<c.s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have h' : (r.num:ℚ)*((c.s*2^c.l.length:ℕ):ℚ)<
      (lowerZ D (fun i => (chebList c.l).getD i 0):ℚ)*((2*r.den:ℕ):ℚ) := by exact_mod_cast hz
  push_cast at h'
  rw [← Rat.num_div_den r,div_lt_div_iff₀ hb (by positivity)]
  linarith
private theorem baseline_check_lowH :
    certOK 0 14 ((nsub (bbaseA .lowH) (blAt .lowH)).center (cnum .lowH) (cden .lowH) 1 1) := by
  decide +kernel
private theorem baseline_check_lowM :
    certOK 0 14 ((nsub (bbaseA .lowM) (blAt .lowM)).center (cnum .lowM) (cden .lowM) 1 1) := by
  decide +kernel
private theorem baseline_check_lowSH :
    certOK 0 14 ((nsub (bbaseA .lowSH) (blAt .lowSH)).center (cnum .lowSH) (cden .lowSH) 1 1) := by
  decide +kernel
private theorem baseline_check_lowSG :
    certOK 0 14 ((nsub (bbaseA .lowSG) (blAt .lowSG)).center (cnum .lowSG) (cden .lowSG) 1 1) := by
  decide +kernel
private theorem baseline_check_lowGA :
    certOK 0 14 ((nsub (bbaseA .lowGA) (blAt .lowGA)).center (cnum .lowGA) (cden .lowGA) 1 1) := by
  decide +kernel
private theorem baseline_check_highH :
    certOK 0 14 ((nsub (bbaseA .highH) (blAt .highH)).center (cnum .highH) (cden .highH) 1 1) := by
  decide +kernel
private theorem baseline_check_highG :
    certOK 0 14 ((nsub (bbaseA .highG) (blAt .highG)).center (cnum .highG) (cden .highG) 1 1) := by
  decide +kernel
private theorem baseline_check_highB :
    certOK 0 14 ((nsub (bbaseA .highB) (blAt .highB)).center (cnum .highB) (cden .highB) 1 1) := by
  decide +kernel
private theorem baseline_check_highGA :
    certOK 0 14 ((nsub (bbaseA .highGA) (blAt .highGA)).center (cnum .highGA) (cden .highGA) 1 1) := by
  decide +kernel
private theorem baseline_check_highAB :
    certOK 0 14 ((nsub (bbaseA .highAB) (blAt .highAB)).center (cnum .highAB) (cden .highAB) 1 1) := by
  decide +kernel
private theorem baseline_check_gaH :
    certOK 0 14 ((nsub (bbaseA .gaH) (blAt .gaH)).center (cnum .gaH) (cden .gaH) 1 1) := by
  decide +kernel
private theorem baseline_check_gaB :
    certOK 0 14 ((nsub (bbaseA .gaB) (blAt .gaB)).center (cnum .gaB) (cden .gaB) 1 1) := by
  decide +kernel
private theorem baseline_check_abG :
    certOK 0 14 ((nsub (bbaseA .abG) (blAt .abG)).center (cnum .abG) (cden .abG) 1 1) := by
  decide +kernel
private theorem baseline_check_abH :
    certOK 0 14 ((nsub (bbaseA .abH) (blAt .abH)).center (cnum .abH) (cden .abH) 1 1) := by
  decide +kernel
end Certificates
open WholeIntervalPolynomial.Certificate (lowerZ chebList)

theorem baseline_factor_certificate (e : Curve) :
    WholeIntervalPolynomial.centered 0 (length e) (baseA e-lAt e)=
      WholeIntervalPolynomial.expansion 14
        (WholeIntervalPolynomial.centered 0 (length e) (baseA e-lAt e)) ∧
    0<WholeIntervalPolynomial.lowerOn 14 0 (length e) (baseA e-lAt e) := by
  have h : certOK 0 14 ((nsub (bbaseA e) (blAt e)).center (cnum e) (cden e) 1 1) := by
    cases e
    · exact baseline_check_lowH
    · exact baseline_check_lowM
    · exact baseline_check_lowSH
    · exact baseline_check_lowSG
    · exact baseline_check_lowGA
    · exact baseline_check_highH
    · exact baseline_check_highG
    · exact baseline_check_highB
    · exact baseline_check_highGA
    · exact baseline_check_highAB
    · exact baseline_check_gaH
    · exact baseline_check_gaB
    · exact baseline_check_abG
    · exact baseline_check_abH
  exact of_certOK (rep_center (rep_nsub (rep_bbaseA e) (rep_blAt e)) e) h

theorem elementary_lower (f : Family) {z : ℝ}
    (hz : z∈Icc (left f:ℝ) (right f:ℝ)) : aeval z (elementary f)≤NegativeABT3.nonradical f z := by
  have hzf := Explicit.frame_domain f hz
  have hm := (Explicit.positive f hz).2.2
  have ht := PositiveTD.Certificate.taylor_bounds hzf
  have hs := (transport_trig hzf).2.2.1
  have hc0 : 0≤Real.cos z := by linarith [(transport_trig hzf).1]
  have hD : Secondary.diagonal≤(899214066/1000000000:ℝ) := by
    have h := PositiveTD.Certificate.diagonal_le_cbar
    simp only [PositiveTD.Certificate.cbar] at h
    push_cast at h
    exact h
  have hS : PositiveTD.sigma≤(1415477291/1000000000:ℝ) := by
    have h := PositiveTD.Certificate.sigma_le_sigmabar
    simp only [PositiveTD.Certificate.sigmabar] at h
    push_cast at h
    exact h
  cases f
  · have hcos := mul_le_mul_of_nonneg_left ht.2.2.2.2.1
      (show (0:ℝ)≤3/2-899214066/1000000000 by norm_num)
    have hsin := mul_le_mul_of_nonpos_left ht.2.2.1
      (show (1/2:ℝ)+(293/1000)*(1-899214066/1000000000)-1415477291/1000000000≤0 by norm_num)
    have hdc := mul_le_mul_of_nonneg_right hD hc0
    have hds := mul_le_mul_of_nonneg_right hD hs
    have hss := mul_le_mul_of_nonneg_right hS hs
    have hinner : 1+(3/2-899214066/1000000000)*aeval z PositiveTD.Certificate.C10+
        (1/2+(293/1000)*(1-899214066/1000000000)-1415477291/1000000000)*
          aeval z PositiveTD.Certificate.S9≤
      1+(3/2-Secondary.diagonal)*Real.cos z+
        (1/2+PositiveTD.eta*(1-Secondary.diagonal)-PositiveTD.sigma)*Real.sin z := by
      simp only [PositiveTD.eta]
      linarith
    have hprod := mul_le_mul_of_nonneg_left hinner hm.le
    simp only [elementary,NegativeABT3.nonradical,↓reduceIte,map_add,map_sub,map_mul,
      map_one,aeval_C,eq_ratCast,Explicit.k_eval,Explicit.l_eval,Explicit.m_eval]
    push_cast
    norm_num only [PositiveTD.Certificate.cbar,PositiveTD.Certificate.sigmabar,
      PositiveTD.Certificate.etaQ] at hprod ⊢
    linarith
  · have hsin := mul_le_mul_of_nonpos_left ht.2.2.1
      (show (1/2:ℝ)+3*(293/1000)/2-1415477291/1000000000≤0 by norm_num)
    have hss := mul_le_mul_of_nonneg_right hS hs
    have hinner : 1+2*aeval z PositiveTD.Certificate.C10+
        (1/2+3*(293/1000)/2-1415477291/1000000000)*aeval z PositiveTD.Certificate.S9≤
      1+2*Real.cos z+(1/2+3*PositiveTD.eta/2-PositiveTD.sigma)*Real.sin z := by
      simp only [PositiveTD.eta]
      linarith [ht.2.2.2.2.1]
    have hprod := mul_le_mul_of_nonneg_left hinner hm.le
    simp only [elementary,NegativeABT3.nonradical,↓reduceIte,reduceCtorEq,map_add,map_sub,map_mul,
      map_one,aeval_C,eq_ratCast,Explicit.k_eval,Explicit.l_eval,Explicit.m_eval]
    push_cast
    norm_num only [PositiveTD.Certificate.cbar,PositiveTD.Certificate.sigmabar,
      PositiveTD.Certificate.etaQ] at hprod ⊢
    linarith
end Certificate

namespace Analytic
open Certificate (Curve)

theorem cost_nonnegative (e : Curve) {z : ℝ} (hz : Domain e z) : 0≤cost e z := by
  have hl := (Explicit.positive (Certificate.family e) (domains e hz).1).2.1
  cases e <;> simp [cost,Certificate.selected] <;> linarith

theorem base_lower (e : Curve) {z : ℝ} (hz : Domain e z) :
    aeval (z-(Certificate.start e:ℝ)) (Certificate.baseA e)≤
      NegativeABT3.nonradical (Certificate.family e) z := by
  simpa [Certificate.baseA,aeval_comp] using Certificate.elementary_lower (Certificate.family e) (domains e hz).1

theorem base_factor_positive (e : Curve) {z : ℝ} (hz : Domain e z) :
    0<aeval (z-(Certificate.start e:ℝ)) (Certificate.baseA e)-Explicit.l (Certificate.family e) z := by
  have hh := WholeIntervalPolynomial.positive_on_interval (Certificate.length_positive e)
    (Certificate.baseline_factor_certificate e).1 (Certificate.baseline_factor_certificate e).2
    (by rw [Rat.cast_zero]; exact native_domain e hz)
  simpa using hh

theorem extra_lower (e : Curve) {z : ℝ} (hz : Domain e z) :
    aeval (z-(Certificate.start e:ℝ)) (Certificate.extraA e)≤extra e z := by
  have hd := domains e hz
  have hn := PositiveTD.Certificate.taylor_bounds hd.2.2.1
  have hcoeff := cost_nonnegative e hz
  have hcost := mul_le_mul_of_nonneg_left (sub_le_sub_right hn.2.2.2.2.1 1) hcoeff
  by_cases he : e=.lowM
  · subst e
    have hrest := PositiveTD.Certificate.taylor_bounds hd.2.2.2
    have hcap := PositiveTD.Certificate.taylor_bounds (show frameCap∈Icc 0 frameCap by norm_num [frameCap])
    have hb := Explicit.positive .low hd.1
    have h₁ := mul_le_mul_of_nonneg_left
      (show aeval (frameCap-z) PositiveTD.Certificate.C10+aeval (frameCap-z) PositiveTD.Certificate.S11-1≤
        PositiveAngularEnvelope.phi (frameCap-z)-1 by
          dsimp [PositiveAngularEnvelope.phi]; linarith [hrest.2.1,hrest.2.2.2.2.1]) hb.1.le
    have h₂ := mul_le_mul_of_nonneg_left (sub_le_sub_right hcap.2.2.2.2.1 1)
      (show 0≤Explicit.l .low z by linarith [hb.2.1])
    have hev : algebraMap ℚ ℝ (PositiveTD.Certificate.C10.eval PositiveTD.Certificate.h)=
        aeval frameCap PositiveTD.Certificate.C10 := by
      rw [← Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]
      norm_num [PositiveTD.Certificate.h,frameCap]
    have hh : algebraMap ℚ ℝ PositiveTD.Certificate.h=frameCap := by
      norm_num [PositiveTD.Certificate.h,frameCap]
    simp only [Certificate.extraA,extra,↓reduceIte,map_add,map_sub,map_mul,map_one,aeval_comp,
      aeval_C,hev,hh,native_z,native_k,native_l,Certificate.family]
    linarith
  · simp only [Certificate.extraA,extra,ite_eq_right he,map_sub,map_mul,aeval_comp,
      native_cost,native_negativeAngle,map_one]
    split_ifs <;> norm_num [PositiveTD.Certificate.h,frameCap] at hcost ⊢ <;> linarith

theorem scaled_extra_nonpositive (e : Curve) {z : ℝ} (he : Certificate.scaled e=true)
    (hz : Domain e z) : extra e z≤0 := by
  have hcost := mul_nonpos_of_nonneg_of_nonpos (cost_nonnegative e hz)
    (sub_nonpos.mpr (Real.cos_le_one (negativeAngle e z)))
  cases e <;> simp only [Certificate.scaled] at he <;> first | contradiction |
    simpa [extra,Certificate.separated] using hcost

theorem nonradical_lower (e : Curve) {z : ℝ} (hz : Domain e z) :
    aeval (z-(Certificate.start e:ℝ)) (Certificate.A e)≤nonradical e z := by
  have hd := domains e hz
  have ht := PositiveTD.Certificate.taylor_bounds hd.2.1
  have hc0 : 0≤Real.cos (angle e z) := by linarith [(transport_trig hd.2.1).1]
  have hbase := base_lower e hz
  have hextra := extra_lower e hz
  by_cases he : Certificate.scaled e=true
  · have hl : 0≤Explicit.l (Certificate.family e) z :=
      by linarith [(Explicit.positive (Certificate.family e) hd.1).2.1]
    have hpos := base_factor_positive e hz
    have h₁ := mul_le_mul ht.2.2.2.2.1 (sub_le_sub_right hbase (Explicit.l (Certificate.family e) z))
      hpos.le hc0
    have h₂ := mul_le_mul_of_nonneg_left ht.2.1 (show 0≤(13/12)*Explicit.l (Certificate.family e) z by positivity)
    have he0 := scaled_extra_nonpositive e he hz
    have h₃ := mul_le_mul_of_nonpos_right ht.2.2.2.2.2 (hextra.trans he0)
    have h₄ := mul_le_mul_of_nonneg_left hextra hc0
    simp only [Certificate.A,nonradical,ite_eq_left he,map_add,map_mul,map_sub,
      aeval_comp,native_angle,native_l,aeval_C,eq_ratCast]
    push_cast
    linarith
  · simp only [Certificate.A,nonradical,ite_eq_right he,map_add]
    exact add_le_add hbase hextra

end Analytic
end SquaresInCircles.Eight.GlobalGA.NegativeABT3
end
end
end

section
/-!
## Squared-norm bounds at all reference endpoints

The affected zero-angle norm cancels its secant. At an unaffected negative-angle norm the lower
bound of the cosine square is used only after the comparison with the sine itself, which is
nonnegative. The only coefficient bounded above by a Taylor polynomial is the zero-angle rotating
coefficient of D (`native_rotation`).
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.GlobalGA.NegativeABT3.Analytic
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open Certificate (Curve)

theorem unscaled_angle (e : Curve) (z : ℝ) (he : Certificate.scaled e≠true) : angle e z=0 := by
  cases e <;> simp [Certificate.scaled,angle] at he ⊢

theorem coefficient_positive (e : Curve) {z : ℝ} (hz : Domain e z) (j : Fin 4) :
    0<p e z j ∧ 0<q e z j := by
  have hd := domains e hz
  have hb := Explicit.positive (Certificate.family e) hd.1
  have hl : 0<Explicit.l (Certificate.family e) z := by linarith [hb.2.1]
  have hcos : 0<Real.cos (angle e z) := by linarith [(transport_trig hd.2.1).1]
  have hsec : 0<secant (Explicit.l (Certificate.family e) z) (angle e z) := div_pos hl hcos
  have hc : 0<Explicit.c (Certificate.family e) z :=
    PositiveTD.tilted_pos hb.2.2 (Explicit.frame_domain (Certificate.family e) hd.1)
  fin_cases j
  · simpa [p,q] using And.intro hb.1 (show (0:ℝ)<1 by norm_num)
  · dsimp [p,q,lambdaG,NegativeAPositiveTD.lambdaG]
    split_ifs <;> exact ⟨hb.1,by assumption⟩
  · dsimp [p,q,lambdaB,NegativeAPositiveTD.lambdaB]
    split_ifs <;> exact ⟨hb.2.2,by assumption⟩
  · simpa [p,q] using And.intro (show (0:ℝ)<1 by norm_num) hc

theorem native_rotation (e : Curve) (z : ℝ) :
    aeval (z-(Certificate.start e:ℝ)) (Certificate.rotation e)=
      aeval z (Certificate.rotationHi (Certificate.family e)) := by
  simp [Certificate.rotation,Certificate.rotationHi,aeval_comp,PositiveTD.Certificate.etaQ]

theorem base_square_bounds (e : Curve) {z : ℝ} (hz : Domain e z) (j : Fin 4) :
    (scale e z*pairNorm (p e z j) (q e z j) 0)^2≤
      aeval (z-(Certificate.start e:ℝ))
        (if Certificate.scaled e then Certificate.scaledP e j else Certificate.baseP e j) := by
  have hd := domains e hz
  have hcos := NegativeAPositiveTD.Certificate.cosine_square_upper hd.2.1
  have hc : 0<Real.cos (angle e z) := by linarith [(transport_trig hd.2.1).1]
  have hrot := (Explicit.rotation_bounds (Certificate.family e) hd.1).2
  have hrot0 : 0≤Explicit.c (Certificate.family e) z := (coefficient_positive e hz 3).2.le
  have hD := NonnegativeTotals.Analytic.norm_zero_coefficient_upper (p:=1) hrot0 hrot
  rw [NonnegativeTotals.Analytic.norm_zero_square] at hD
  have hsq (a b : ℝ) : (pairNorm a b 0)^2=a^2+b^2 := NonnegativeTotals.Analytic.norm_zero_square a b
  by_cases he : Certificate.scaled e=true
  · rw [ite_eq_left he,show scale e z=Real.cos (angle e z) by simp [scale,he]]
    fin_cases j
    · have hh := mul_le_mul_of_nonneg_right hcos
        (add_nonneg (sq_nonneg (Explicit.k (Certificate.family e) z)) (sq_nonneg (1:ℝ)))
      rw [mul_pow,hsq]
      simp [p,q,Certificate.scaledP,Certificate.baseP,aeval_comp] at hh ⊢
      linarith
    · by_cases hg : Certificate.atG e=true
      · have hh := mul_le_mul_of_nonneg_right hcos (sq_nonneg (Explicit.k (Certificate.family e) z))
        have hs := NegativeAPositiveTD.Certificate.scaled_secant_norm_sq
          (a:=Explicit.k (Certificate.family e) z) (l:=Explicit.l (Certificate.family e) z) hc
        simp only [p,q,lambdaG,NegativeAPositiveTD.lambdaG,ite_eq_left hg,Fin.mk_one,Fin.isValue,
          Matrix.cons_val_one,Matrix.cons_val_zero] at hs ⊢
        rw [hs]
        simp [Certificate.scaledP,hg,aeval_comp] at hh ⊢
        linarith
      · have hh := mul_le_mul_of_nonneg_right hcos
          (add_nonneg (sq_nonneg (Explicit.k (Certificate.family e) z))
            (sq_nonneg (Explicit.l (Certificate.family e) z)))
        rw [mul_pow,hsq]
        simp [p,q,lambdaG,NegativeAPositiveTD.lambdaG,hg,Certificate.scaledP,
          Certificate.baseP,aeval_comp] at hh ⊢
        linarith
    · by_cases hg : Certificate.atG e=true
      · have hh := mul_le_mul_of_nonneg_right hcos
          (add_nonneg (sq_nonneg (Explicit.m (Certificate.family e) z))
            (sq_nonneg (Explicit.l (Certificate.family e) z)))
        rw [mul_pow,hsq]
        simp [p,q,lambdaB,NegativeAPositiveTD.lambdaB,hg,Certificate.scaledP,
          Certificate.baseP,aeval_comp] at hh ⊢
        linarith
      · have hg' : Certificate.atG e=false := by simpa using hg
        have hh := mul_le_mul_of_nonneg_right hcos (sq_nonneg (Explicit.m (Certificate.family e) z))
        have hs := NegativeAPositiveTD.Certificate.scaled_secant_norm_sq
          (a:=Explicit.m (Certificate.family e) z) (l:=Explicit.l (Certificate.family e) z) hc
        have hq2 : q e z 2=NegativeAPositiveTD.secant (Explicit.l (Certificate.family e) z)
            (angle e z) := by
          simp [q,lambdaB,NegativeAPositiveTD.lambdaB,hg']
        change (Real.cos (angle e z)*pairNorm (p e z 2) (q e z 2) 0)^2≤
          aeval (z-(Certificate.start e:ℝ)) (Certificate.scaledP e 2)
        rw [show p e z 2=Explicit.m (Certificate.family e) z from rfl,hq2,hs]
        simp [Certificate.scaledP,hg',aeval_comp] at hh ⊢
        linarith
    · have hh := mul_le_mul hcos hD (by positivity) (sq_nonneg _)
      rw [mul_pow,hsq]
      simp [p,q,Certificate.scaledP,Certificate.baseP,aeval_comp,native_rotation] at hh ⊢
      linarith
  · have hs := unscaled_angle e z he
    rw [ite_eq_right he,show scale e z=1 by simp [scale,he],one_mul,hsq]
    fin_cases j
    · simp [p,q,Certificate.baseP]
      linarith
    · simp [p,q,lambdaG,NegativeAPositiveTD.lambdaG,NegativeAPositiveTD.secant,hs,Certificate.baseP]
    · simp [p,q,lambdaB,NegativeAPositiveTD.lambdaB,NegativeAPositiveTD.secant,hs,Certificate.baseP]
      linarith
    · simp [p,q,Certificate.baseP,native_rotation] at hD ⊢
      linarith

theorem selected_fixed (e : Curve) (z : ℝ) (j : Fin 4) (hj : Certificate.selected e=some j) :
    j≠3 ∧ q e z j=(![1,Explicit.l (Certificate.family e) z,Explicit.l (Certificate.family e) z,
      Explicit.c (Certificate.family e) z] j) ∧
    Certificate.scaledP e j=(PositiveTD.Certificate.C12.comp (Certificate.angle e))^2*Certificate.baseP e j := by
  cases e <;> fin_cases j <;>
    simp [Certificate.selected] at hj <;>
    simp [q,angle,lambdaG,lambdaB,NegativeAPositiveTD.lambdaG,NegativeAPositiveTD.lambdaB,
      NegativeAPositiveTD.secant,Certificate.atG,Certificate.scaledP] <;>
    simp [Certificate.angle,Certificate.baseP,PositiveTD.Certificate.C12,PositiveTD.Certificate.C10,
      PositiveTD.Certificate.C4,add_comm]

theorem selected_base (e : Curve) {z : ℝ} (_hz : Domain e z) (j : Fin 4)
    (hj : Certificate.selected e=some j) :
    (p e z j)^2+(q e z j)^2=aeval (z-(Certificate.start e:ℝ)) (Certificate.baseP e j) ∧
    p e z j*q e z j=aeval (z-(Certificate.start e:ℝ)) (Certificate.pairProduct e j) := by
  have hf := selected_fixed e z j hj
  rw [hf.2.1]
  fin_cases j
  · simp [p,Certificate.baseP,Certificate.pairProduct,add_comm]
  · simp [p,Certificate.baseP,Certificate.pairProduct]
  · simp [p,Certificate.baseP,Certificate.pairProduct,add_comm,mul_comm]
  · exact False.elim (hf.1 rfl)

theorem norm_square_upper (e : Curve) {z : ℝ} (hz : Domain e z) (j : Fin 4) :
    (scaledNorm e z j)^2≤aeval (z-(Certificate.start e:ℝ)) (Certificate.P e j) := by
  have hbase := base_square_bounds e hz j
  by_cases hj : Certificate.selected e=some j
  · have hfixed := selected_fixed e z j hj
    have hpair := selected_base e hz j hj
    have hp := coefficient_positive e hz j
    have hd := domains e hz
    have hs := PositiveTD.Certificate.taylor_bounds hd.2.1
    have hn := PositiveTD.Certificate.taylor_bounds hd.2.2.1
    by_cases he : Certificate.scaled e=true
    · have hClo : (aeval (angle e z) PositiveTD.Certificate.C10)^2≤(Real.cos (angle e z))^2 :=
        pow_le_pow_left₀ (by linarith [hs.2.2.2.1]) hs.2.2.2.2.1 2
      have hChi := NegativeAPositiveTD.Certificate.cosine_square_upper hd.2.1
      have hh := NegativeAPositiveTD.Certificate.scaled_negative_norm_bound hp.1 hp.2 hd.2.2.1
        hClo hChi hpair.1.le (mul_nonneg hp.1.le hp.2.le) (le_refl (p e z j*q e z j)) hn.2.1
      rw [hpair.2] at hh
      simpa [scaledNorm,scale,he,norm,hj,Certificate.P,hfixed.2.2,aeval_comp] using hh
    · have hh := NonnegativeTotals.Analytic.norm_negative_polynomial hp.1 hp.2 hd.2.2.1
      rw [hpair.1,mul_assoc 2,hpair.2] at hh
      simpa [scaledNorm,scale,he,norm,hj,Certificate.P,aeval_comp] using hh
  · simpa [scaledNorm,norm,hj,Certificate.P] using hbase

theorem scaledNorm_nonnegative (e : Curve) {z : ℝ} (hz : Domain e z) (j : Fin 4) :
    0≤ scaledNorm e z j := mul_nonneg (scale_positive e hz).le (Real.sqrt_nonneg _)

end SquaresInCircles.Eight.GlobalGA.NegativeABT3.Analytic
end
end
end

section
@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.GlobalGA.NegativeABT3
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

namespace Analytic
open Certificate (Curve)

theorem curve_positive (e : Curve) {z : ℝ} (hz : Domain e z) : 0<curve e z := by
  have hx := native_domain e hz
  have hr := fun j => Certificate.mass_positive e j hx
  have hn := scaledNorm_nonnegative e hz
  have hsq := norm_square_upper e hz
  have hA := nonradical_lower e hz
  have hnum := Certificate.numerator_positive e hx
  have hpos : 0<nonradical e z-R*normSum (Certificate.family e) (scaledNorm e z) := by
    by_cases hf : Certificate.family e=.low
    · have hh := PositiveTD.Certificate.num3_transfer (hr 0) (hr 1) (hr 2)
        (hn 0) (hn 1) (hn 2) (hsq 0) (hsq 1) (hsq 2) hA
        (by simpa only [Certificate.numerator,ite_eq_left hf] using hnum)
      simpa only [normSum,NegativeAPositiveTD.normSum,hf,↓reduceIte] using hh
    · have hh := PositiveTD.Certificate.num4_transfer (hr 0) (hr 1) (hr 2) (hr 3)
        (hn 0) (hn 1) (hn 2) (hn 3) (hsq 0) (hsq 1) (hsq 2) (hsq 3) hA
        (by simpa only [Certificate.numerator,ite_eq_right hf] using hnum)
      simpa only [normSum,NegativeAPositiveTD.normSum,ite_eq_right hf] using hh
  rw [←curve_identity e hz] at hpos
  exact (mul_pos_iff_of_pos_left (scale_positive e hz)).mp hpos

theorem endpoint_positive (e : Curve) {z : ℝ} (hz : Domain e z) :
    0<baseline (Certificate.atG e) (Explicit.k (Certificate.family e) z)
      (Explicit.l (Certificate.family e) z) (Explicit.m (Certificate.family e) z)
      (angle e z) z+charge e z := by
  have hh := curve_positive e hz
  have hl := reduced_le_baseline (Certificate.family e) (Certificate.atG e) (angle e z) z
  dsimp [curve] at hh
  linarith
end Analytic

theorem low_endpoints {z : ℝ} (hz : z∈Icc 0 (1/4:ℝ)) :
    0<baselineZero (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) z+
      V R (Explicit.k .low z) 1 z ∧
    0<baselineZero (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) z+
      mixedG (Explicit.k .low z) (Explicit.l .low z) z ∧
    0<baselineZero (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) z-
      (109/160)*(frameCap-z)+V R (Explicit.k .low z) 1 frameCap ∧
    0<baselineZero (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) z-
      (109/160)*(frameCap-z)+V R (Explicit.k .low z) (Explicit.l .low z) frameCap ∧
    0<baseline true (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) z z := by
  have hD (e : Certificate.Curve) (hf : Certificate.family e=.low)
      (hs : Certificate.start e=0) : Analytic.Domain e z := by
    simp only [Analytic.Domain,hf,hs,Certificate.right,Certificate.split]
    push_cast
    exact hz
  have h₀ : 0<baselineZero (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) z+
      V R (Explicit.k .low z) 1 z := Analytic.endpoint_positive .lowH (hD .lowH rfl rfl)
  have h₁ : 0<baselineZero (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) z+
      mixedG (Explicit.k .low z) (Explicit.l .low z) z :=
    Analytic.endpoint_positive .lowM (hD .lowM rfl rfl)
  have h₂ : 0<baselineZero (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) z+
      (-(109/160)*(frameCap-z)+V R (Explicit.k .low z) 1 frameCap) :=
    Analytic.endpoint_positive .lowSH (hD .lowSH rfl rfl)
  have h₃ : 0<baselineZero (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) z+
      (-(109/160)*(frameCap-z)+V R (Explicit.k .low z) (Explicit.l .low z) frameCap) :=
    Analytic.endpoint_positive .lowSG (hD .lowSG rfl rfl)
  have h₄ : 0<baseline true (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) z z+0 :=
    Analytic.endpoint_positive .lowGA (hD .lowGA rfl rfl)
  refine ⟨h₀,h₁,?_,?_,?_⟩
  · linarith
  · linarith
  · simpa using h₄

theorem high_endpoints {z : ℝ} (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) :
    0<baselineZero (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) z+
      V R (Explicit.k .high z) 1 z ∧
    0<baselineZero (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) z+
      V R (Explicit.k .high z) (Explicit.l .high z) z ∧
    0<baselineZero (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) z+
      V R (Explicit.m .high z) (Explicit.l .high z) z ∧
    0<baseline true (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) z z ∧
    0<baseline false (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) z z := by
  have hD (e : Certificate.Curve) (hf : Certificate.family e=.high)
      (hs : Certificate.start e=1/4) : Analytic.Domain e z := by
    simp only [Analytic.Domain,hf,hs,Certificate.right]
    push_cast
    exact hz
  have h₀ : 0<baselineZero (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) z+
      V R (Explicit.k .high z) 1 z := Analytic.endpoint_positive .highH (hD .highH rfl rfl)
  have h₁ : 0<baselineZero (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) z+
      V R (Explicit.k .high z) (Explicit.l .high z) z :=
    Analytic.endpoint_positive .highG (hD .highG rfl rfl)
  have h₂ : 0<baselineZero (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) z+
      V R (Explicit.m .high z) (Explicit.l .high z) z :=
    Analytic.endpoint_positive .highB (hD .highB rfl rfl)
  have h₃ : 0<baseline true (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z)
      z z+0 := Analytic.endpoint_positive .highGA (hD .highGA rfl rfl)
  have h₄ : 0<baseline false (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z)
      z z+0 := Analytic.endpoint_positive .highAB (hD .highAB rfl rfl)
  rw [add_zero] at h₃ h₄
  exact ⟨h₀,h₁,h₂,h₃,h₄⟩

theorem GA_cut_endpoints {z : ℝ} (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) :
    0<baseline true (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) (1/4) z+
      V R (Explicit.k .high z) 1 (z-1/4) ∧
    0<baseline true (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) (1/4) z+
      V R (Explicit.m .high z) (Explicit.l .high z) (z-1/4) := by
  have hD (e : Certificate.Curve) (hf : Certificate.family e=.high)
      (hs : Certificate.start e=1/4) : Analytic.Domain e z := by
    simp only [Analytic.Domain,hf,hs,Certificate.right]
    push_cast
    exact hz
  have hH : 0<baseline true (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z)
      (1/4) z+V R (Explicit.k .high z) 1 (z-1/4) :=
    Analytic.endpoint_positive .gaH (hD .gaH rfl rfl)
  have hB : 0<baseline true (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z)
      (1/4) z+V R (Explicit.m .high z) (Explicit.l .high z) (z-1/4) :=
    Analytic.endpoint_positive .gaB (hD .gaB rfl rfl)
  exact ⟨hH,hB⟩

theorem AB_cut_endpoints {z : ℝ} (hz : z∈Icc (19/50:ℝ) (7/10:ℝ)) :
    0<baseline false (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) (19/50) z+
      V R (Explicit.k .high z) (Explicit.l .high z) (z-19/50) ∧
    0<baseline false (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) (19/50) z+
      V R (Explicit.k .high z) 1 (z-19/50) := by
  have hD (e : Certificate.Curve) (hf : Certificate.family e=.high)
      (hs : Certificate.start e=19/50) : Analytic.Domain e z := by
    simp only [Analytic.Domain,hf,hs,Certificate.right]
    push_cast
    exact hz
  have hG : 0<baseline false (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z)
      (19/50) z+V R (Explicit.k .high z) (Explicit.l .high z) (z-19/50) :=
    Analytic.endpoint_positive .abG (hD .abG rfl rfl)
  have hH : 0<baseline false (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z)
      (19/50) z+V R (Explicit.k .high z) 1 (z-19/50) :=
    Analytic.endpoint_positive .abH (hD .abH rfl rfl)
  exact ⟨hG,hH⟩

end SquaresInCircles.Eight.GlobalGA.NegativeABT3
end
end
end
