module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHBT3Polynomial
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHTD2EndpointData
public import SquaresInCircles.Eight.TableFree.PolynomialCertificates

/-!
# Exact original-angle inputs for all thirty-four EH1/BT3 endpoints

Uncompiled Section 8. The native polynomial coordinate is x=theta-b.
All angle domains, coefficient signs, and the q-star replacement are
proved before the radical transfer. The small-high A-support allowance
follows from the already proved sixth-order bound, since
(151/500)*(8/15)^2 < 43/500. No additional A-support hypothesis is used.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHBT3.EndpointInputs
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open Certificate
open WholeIntervalPolynomial
open PositiveTD.Certificate (taylor_bounds)

abbrev thetaAt (r : Row) (x : ℝ) : ℝ := x+(left r:ℝ)
def aAt : Split→ℝ→ℝ | .atA,t=>t | .atT,_=>0
def zAt : Split→ℝ→ℝ | .atA,_=>0 | .atT,t=>t
abbrev Kactual (r : Row) (x : ℝ) := Explicit.k (family r) (thetaAt r x)
abbrev Lactual (r : Row) (x : ℝ) := Explicit.l (family r) (thetaAt r x)
abbrev Mactual (r : Row) (x : ℝ) := Explicit.m (family r) (thetaAt r x)
def Cactual (r : Row) (ep : Split) (x : ℝ) :=
  Explicit.c (family r) (thetaAt r x) (zAt ep (thetaAt r x))
def argument (r : Row) (x : ℝ) : ℝ :=
  if positive r then gainArgument r (thetaAt r x)-thetaAt r x
  else thetaAt r x-gainArgument r (thetaAt r x)

@[simp] theorem theta_eval (r : Row) (x : ℝ) : aeval x (theta r)=thetaAt r x := by
  simp [theta,thetaAt]
@[simp] theorem d_eval (r : Row) (x : ℝ) : aeval x (d r)=argument r x := by
  simp only [d,argument]
  split <;> simp_all only [map_sub,s_eval,theta_eval]

lemma original_domain (r : Row) {x : ℝ} (hx : x∈Icc 0 (GlobalGA.NegativeEHBT3.Certificate.width r:ℝ)) :
    thetaAt r x∈Icc (left r:ℝ) (right r:ℝ) := by
  dsimp [thetaAt,GlobalGA.NegativeEHBT3.Certificate.width] at *
  push_cast at *
  exact ⟨by linarith [hx.1],by linarith [hx.2]⟩

lemma frame_domain (r : Row) {x : ℝ} (hx : x∈Icc 0 (GlobalGA.NegativeEHBT3.Certificate.width r:ℝ)) :
    thetaAt r x∈Icc 0 frameCap := total_domain r (original_domain r hx)

lemma split_domains (r : Row) (ep : Split) {x : ℝ}
    (hx : x∈Icc 0 (GlobalGA.NegativeEHBT3.Certificate.width r:ℝ)) :
    aAt ep (thetaAt r x)∈Icc 0 frameCap ∧
      zAt ep (thetaAt r x)∈Icc 0 frameCap := by
  have ht := frame_domain r hx
  cases ep <;> simp [aAt,zAt,ht,show (0:ℝ)≤frameCap by norm_num [frameCap]]

lemma gain_domain (r : Row) {x : ℝ} (hx : x∈Icc 0 (GlobalGA.NegativeEHBT3.Certificate.width r:ℝ)) :
    gainArgument r (thetaAt r x)∈Icc 0 frameCap := by
  have ht := frame_domain r hx
  cases r with
  | farHigh i b => cases b <;> norm_num [gainArgument,equal,u,v,frameCap]
  | _ => simp [gainArgument,equal,v,ht] <;> norm_num [frameCap]

lemma argument_domain (r : Row) {x : ℝ} (hx : x∈Icc 0 (GlobalGA.NegativeEHBT3.Certificate.width r:ℝ)) :
    argument r x∈Icc 0 frameCap := by
  have ht := original_domain r hx
  cases r <;>
    norm_num [argument,positive,equal,gainArgument,left,right,u,v,frameCap] at ht ⊢
  all_goals first
    | exact ⟨by linarith [ht.1,ht.2],by linarith [ht.1,ht.2]⟩
    | split <;> norm_num [u,v] <;>
        exact ⟨by linarith [ht.1,ht.2],by linarith [ht.1,ht.2]⟩

/-- Five elementary coefficient margins, each on its full native interval. -/
def coefficientMargin (r : Row) : Fin 5→ℚ[X] :=
  ![k r-C (1/2),l r-C (1/2),m r-C (1/2),1-k r,l r-k r]

/-! ### Kernel certificates

The margins are the family margins composed with `theta r = X + left r`, so
their centered polynomials on `[0,width r]` are the family margins centered on
`[left r,right r]`; these are represented by scaled integer lists
(`WholeIntervalPolynomial.Certificate`). -/

open WholeIntervalPolynomial.Certificate in
private theorem r75_repC (n : ℤ) (d : ℕ) {q : ℚ} (hd : d≠0) (h : q=n/d) :
    (⟨[n],d⟩ : Scaled).Rep (C q) := by
  unfold Scaled.Rep
  have hd' : (d:ℚ)≠0 := by exact_mod_cast hd
  simp only [toPoly,mul_zero,add_zero,← map_mul]
  congr 1
  rw [h]
  field_simp

private theorem r75_centered_shift (a b : ℚ) (p : ℚ[X]) :
    centered 0 (b-a) (p.comp (X+C a))=centered a b p := by
  simp only [centered,comp_assoc,affine,add_comp,X_comp,C_comp]
  congr 1
  rw [show (a+b)/2=(0+(b-a))/2+a by ring,show (b-a-0)/2=(b-a)/2 by ring,C_add]
  ring

open WholeIntervalPolynomial.Certificate in
private theorem r75_cert {q : ℚ[X]} {a b : ℚ} {c : Scaled} (hc : c.Rep (centered a b q))
    (hs : c.s≠0) (hl : c.l.length≤3+1) (hpos : 0<lowerZ 3 (fun j => (chebList c.l).getD j 0)) :
    centered 0 (b-a) (q.comp (X+C a))=expansion 3 (centered 0 (b-a) (q.comp (X+C a))) ∧
      (0:ℚ)<lowerOn 3 0 (b-a) (q.comp (X+C a)) := by
  have e : lowerOn 3 0 (b-a) (q.comp (X+C a))=lowerOn 3 a b q := by
    simp only [lowerOn,r75_centered_shift]
  rw [r75_centered_shift,e,lowerOn_eq_of_rep hc hs hl]
  exact ⟨hc.eq_expansion hs hl,div_pos (by exact_mod_cast hpos) (scale_pos hs)⟩

private def r75_bm (f : Family) : Fin 5→ℚ[X] :=
  ![kBase f-C (1/2),lBase f-C (1/2),mBase f-C (1/2),1-kBase f,lBase f-kBase f]

private theorem r75_margin_comp (r : Row) (i : Fin 5) :
    coefficientMargin r i=(r75_bm (family r) i).comp (theta r) := by
  fin_cases i <;> simp [coefficientMargin,r75_bm,Certificate.k,Certificate.l,Certificate.m,
    sub_comp,one_comp]

open WholeIntervalPolynomial.Certificate in
private def r75_YS : Scaled := Scaled.var.sub ⟨[1],6⟩

open WholeIntervalPolynomial.Certificate in
private theorem r75_rep_Y : r75_YS.Rep (X-C (1/6)) :=
  Scaled.rep_var.sub (r75_repC 1 6 (by norm_num) (by norm_num))

open WholeIntervalPolynomial.Certificate in
private def r75_kS : Family→Scaled
  | .smallLow => (⟨[2933],5000⟩ : Scaled).add ((⟨[1239],2500⟩ : Scaled).mul Scaled.var)
  | .smallHigh => (((⟨[1673],2500⟩ : Scaled).add ((⟨[2609],5000⟩ : Scaled).mul r75_YS)).sub
      ((⟨[1489],2500⟩ : Scaled).mul (r75_YS.pow 2))).add ((⟨[527],1250⟩ : Scaled).mul (r75_YS.pow 3))
  | .farLow => ⟨[121],200⟩
  | .farHigh => (⟨[101],200⟩ : Scaled).add ((⟨[2],5⟩ : Scaled).mul Scaled.var)

open WholeIntervalPolynomial.Certificate in
private theorem r75_rep_k (f : Family) : (r75_kS f).Rep (kBase f) := by
  cases f
  · exact (r75_repC 2933 5000 (by norm_num) (by norm_num)).add
      ((r75_repC 1239 2500 (by norm_num) (by norm_num)).mul Scaled.rep_var)
  · exact (((r75_repC 1673 2500 (by norm_num) (by norm_num)).add
      ((r75_repC 2609 5000 (by norm_num) (by norm_num)).mul r75_rep_Y)).sub
      ((r75_repC 1489 2500 (by norm_num) (by norm_num)).mul (r75_rep_Y.pow 2))).add
      ((r75_repC 527 1250 (by norm_num) (by norm_num)).mul (r75_rep_Y.pow 3))
  · exact r75_repC 121 200 (by norm_num) (by norm_num)
  · exact (r75_repC 101 200 (by norm_num) (by norm_num)).add
      ((r75_repC 2 5 (by norm_num) (by norm_num)).mul Scaled.rep_var)

open WholeIntervalPolynomial.Certificate in
private def r75_lS : Family→Scaled
  | .smallLow => Scaled.ofNat 1
  | .smallHigh => (((Scaled.ofNat 1).add ((⟨[7],400⟩ : Scaled).mul r75_YS)).sub
      ((⟨[2733],2500⟩ : Scaled).mul (r75_YS.pow 2))).add ((⟨[639],500⟩ : Scaled).mul (r75_YS.pow 3))
  | .farLow => (Scaled.ofNat 1).sub ((⟨[9],25⟩ : Scaled).mul Scaled.var)
  | .farHigh => (⟨[381],400⟩ : Scaled).sub ((⟨[17],100⟩ : Scaled).mul Scaled.var)

open WholeIntervalPolynomial.Certificate in
private theorem r75_rep_l (f : Family) : (r75_lS f).Rep (lBase f) := by
  cases f
  · exact Scaled.rep_one
  · exact (((Scaled.rep_one.add
      ((r75_repC 7 400 (by norm_num) (by norm_num)).mul r75_rep_Y)).sub
      ((r75_repC 2733 2500 (by norm_num) (by norm_num)).mul (r75_rep_Y.pow 2))).add
      ((r75_repC 639 500 (by norm_num) (by norm_num)).mul (r75_rep_Y.pow 3)))
  · exact Scaled.rep_one.sub ((r75_repC 9 25 (by norm_num) (by norm_num)).mul Scaled.rep_var)
  · exact (r75_repC 381 400 (by norm_num) (by norm_num)).sub
      ((r75_repC 17 100 (by norm_num) (by norm_num)).mul Scaled.rep_var)

open WholeIntervalPolynomial.Certificate in
private def r75_mS : Family→Scaled
  | .smallLow => (⟨[5821],5000⟩ : Scaled).sub ((⟨[4437],5000⟩ : Scaled).mul Scaled.var)
  | .smallHigh => (((⟨[10163],10000⟩ : Scaled).sub ((⟨[209],10000⟩ : Scaled).mul r75_YS)).sub
      ((⟨[5743],5000⟩ : Scaled).mul (r75_YS.pow 2))).add
      ((⟨[14069],10000⟩ : Scaled).mul (r75_YS.pow 3))
  | .farLow => (⟨[111],100⟩ : Scaled).sub ((⟨[77],100⟩ : Scaled).mul Scaled.var)
  | .farHigh => (⟨[1929],2000⟩ : Scaled).sub ((⟨[47],250⟩ : Scaled).mul Scaled.var)

open WholeIntervalPolynomial.Certificate in
private theorem r75_rep_m (f : Family) : (r75_mS f).Rep (mBase f) := by
  cases f
  · exact (r75_repC 5821 5000 (by norm_num) (by norm_num)).sub
      ((r75_repC 4437 5000 (by norm_num) (by norm_num)).mul Scaled.rep_var)
  · exact (((r75_repC 10163 10000 (by norm_num) (by norm_num)).sub
      ((r75_repC 209 10000 (by norm_num) (by norm_num)).mul r75_rep_Y)).sub
      ((r75_repC 5743 5000 (by norm_num) (by norm_num)).mul (r75_rep_Y.pow 2))).add
      ((r75_repC 14069 10000 (by norm_num) (by norm_num)).mul (r75_rep_Y.pow 3))
  · exact (r75_repC 111 100 (by norm_num) (by norm_num)).sub
      ((r75_repC 77 100 (by norm_num) (by norm_num)).mul Scaled.rep_var)
  · exact (r75_repC 1929 2000 (by norm_num) (by norm_num)).sub
      ((r75_repC 47 250 (by norm_num) (by norm_num)).mul Scaled.rep_var)

open WholeIntervalPolynomial.Certificate in
private def r75_bmS (f : Family) : Fin 5→Scaled :=
  ![(r75_kS f).sub ⟨[1],2⟩,(r75_lS f).sub ⟨[1],2⟩,(r75_mS f).sub ⟨[1],2⟩,
    (Scaled.ofNat 1).sub (r75_kS f),(r75_lS f).sub (r75_kS f)]

open WholeIntervalPolynomial.Certificate in
private theorem r75_rep_bm (f : Family) (i : Fin 5) : (r75_bmS f i).Rep (r75_bm f i) := by
  have hh : (⟨[1],2⟩ : Scaled).Rep (C (1/2)) := r75_repC 1 2 (by norm_num) (by norm_num)
  fin_cases i
  · exact (r75_rep_k f).sub hh
  · exact (r75_rep_l f).sub hh
  · exact (r75_rep_m f).sub hh
  · exact Scaled.rep_one.sub (r75_rep_k f)
  · exact (r75_rep_l f).sub (r75_rep_k f)

open WholeIntervalPolynomial.Certificate in
private theorem r75_family_cert (f : Family) (i : Fin 5) (a b : ℚ) (num den : ℕ) (s t : ℤ)
    (hden : den≠0) (hm : (a+b)/2=num*s/den) (hh : (b-a)/2=num*t/den)
    (hall : ∀ j : Fin 5,((r75_bmS f j).center num den s t).s≠0 ∧
      ((r75_bmS f j).center num den s t).l.length≤3+1 ∧
      0<lowerZ 3 (fun n => (chebList ((r75_bmS f j).center num den s t).l).getD n 0)) :
    centered 0 (b-a) ((r75_bm f i).comp (X+C a))=
        expansion 3 (centered 0 (b-a) ((r75_bm f i).comp (X+C a))) ∧
      (0:ℚ)<lowerOn 3 0 (b-a) ((r75_bm f i).comp (X+C a)) :=
  r75_cert ((r75_rep_bm f i).centered num den s t hden hm hh) (hall i).1 (hall i).2.1 (hall i).2.2

open WholeIntervalPolynomial.Certificate in
private def r75_qS (f : Family) : Scaled :=
  ((r75_lS f).add ((⟨[3],20⟩ : Scaled).mul ((⟨[7],10⟩ : Scaled).sub Scaled.var))).sub (r75_mS f)

open WholeIntervalPolynomial.Certificate in
private theorem r75_qstar_cert (f : Family) (a b : ℚ) (num den : ℕ) (s t : ℤ)
    (hden : den≠0) (hm : (a+b)/2=num*s/den) (hh : (b-a)/2=num*t/den)
    (hall : ((r75_qS f).center num den s t).s≠0 ∧
      ((r75_qS f).center num den s t).l.length≤3+1 ∧
      0<lowerZ 3 (fun n => (chebList ((r75_qS f).center num den s t).l).getD n 0)) :
    let q := (lBase f+C (3/20)*(C Certificate.h-X)-mBase f).comp (X+C a)
    centered 0 (b-a) q=expansion 3 (centered 0 (b-a) q) ∧ (0:ℚ)<lowerOn 3 0 (b-a) q :=
  r75_cert ((((r75_rep_l f).add ((r75_repC 3 20 (by norm_num) (by norm_num)).mul
    ((r75_repC 7 10 (by norm_num) (by norm_num [Certificate.h])).sub Scaled.rep_var))).sub
    (r75_rep_m f)).centered num den s t hden hm hh) hall.1 hall.2.1 hall.2.2

theorem coefficient_certificate : ∀r : Row,∀i : Fin 5,
    centered 0 (GlobalGA.NegativeEHBT3.Certificate.width r) (coefficientMargin r i)=
      expansion 3 (centered 0 (GlobalGA.NegativeEHBT3.Certificate.width r) (coefficientMargin r i)) ∧
    (0:ℚ)<lowerOn 3 0 (GlobalGA.NegativeEHBT3.Certificate.width r) (coefficientMargin r i) := by
  intro r i
  rw [r75_margin_comp,show GlobalGA.NegativeEHBT3.Certificate.width r=right r-left r from rfl]
  cases r with
  | lowEqual =>
    exact r75_family_cert .smallLow i 0 (1/10) 1 20 1 1 (by norm_num) (by norm_num)
      (by norm_num) (by decide +kernel)
  | lowNegative =>
    exact r75_family_cert .smallLow i (1/10) (1/6) 1 30 4 1 (by norm_num)
      (by norm_num) (by norm_num) (by decide +kernel)
  | smallHigh j =>
    exact r75_family_cert .smallHigh i (1/6) (7/10) 1 30 13 8 (by norm_num)
      (by norm_num) (by norm_num) (by decide +kernel)
  | farPositive j =>
    exact r75_family_cert .farLow i 0 (1/10) 1 20 1 1 (by norm_num)
      (by norm_num) (by norm_num) (by decide +kernel)
  | farNegative j =>
    exact r75_family_cert .farLow i (1/10) (1/4) 1 40 7 3 (by norm_num)
      (by norm_num) (by norm_num) (by decide +kernel)
  | farEqual =>
    exact r75_family_cert .farLow i (1/10) (1/4) 1 40 7 3 (by norm_num)
      (by norm_num) (by norm_num) (by decide +kernel)
  | farHigh j b =>
    exact r75_family_cert .farHigh i (1/4) (7/10) 1 40 19 9 (by norm_num)
      (by norm_num) (by norm_num) (by decide +kernel)

lemma coefficient_margin_positive (r : Row) (i : Fin 5) {x : ℝ}
    (hx : x∈Icc 0 (GlobalGA.NegativeEHBT3.Certificate.width r:ℝ)) : 0<aeval x (coefficientMargin r i) := by
  have hh := coefficient_certificate r i
  have h := positive_on_interval (interval_positive r) hh.1 hh.2 (x:=x)
    (by rw [Rat.cast_zero]; exact hx)
  rwa [Rat.cast_zero] at h

lemma coefficient_bounds (r : Row) {x : ℝ} (hx : x∈Icc 0 (GlobalGA.NegativeEHBT3.Certificate.width r:ℝ)) :
    0<Kactual r x ∧ 0<Lactual r x ∧ 0<Mactual r x ∧
      Kactual r x≤1 ∧ Kactual r x≤Lactual r x := by
  have hk : 0<aeval x (k r-C (1/2)) := coefficient_margin_positive r 0 hx
  have hl : 0<aeval x (l r-C (1/2)) := coefficient_margin_positive r 1 hx
  have hm : 0<aeval x (m r-C (1/2)) := coefficient_margin_positive r 2 hx
  have hk1 : 0<aeval x (1-k r) := coefficient_margin_positive r 3 hx
  have hkl : 0<aeval x (l r-k r) := coefficient_margin_positive r 4 hx
  simp only [map_sub,map_one,aeval_C,k_eval,l_eval,m_eval,eq_ratCast] at hk hl hm hk1 hkl
  push_cast at hk hl hm
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩

lemma c_positive (r : Row) (ep : Split) {x : ℝ}
    (hx : x∈Icc 0 (GlobalGA.NegativeEHBT3.Certificate.width r:ℝ)) : 0<Cactual r ep x := by
  have hm := (coefficient_bounds r hx).2.2.1
  have hz := (split_domains r ep hx).2
  have hf := PositiveTD.Explicit.factor_lower hz
  change 0<Mactual r x*(Real.cos (zAt ep (thetaAt r x))+
    PositiveTD.eta*Real.sin (zAt ep (thetaAt r x)))
  exact mul_pos hm (lt_trans (by norm_num) hf)

lemma c_upper (r : Row) (ep : Split) {x : ℝ}
    (hx : x∈Icc 0 (GlobalGA.NegativeEHBT3.Certificate.width r:ℝ)) : Cactual r ep x≤aeval x (cUpper r ep) := by
  have hp := coefficient_bounds r hx
  have ht := taylor_bounds (frame_domain r hx)
  cases ep
  · simp [Cactual,Explicit.c,zAt,PositiveBT3.tilted,cUpper]
  · have hh := mul_le_mul_of_nonneg_left
      (show Real.cos (thetaAt r x)+PositiveTD.eta*Real.sin (thetaAt r x)≤
        aeval (thetaAt r x) PositiveTD.Certificate.C12+
          PositiveTD.eta*aeval (thetaAt r x) PositiveTD.Certificate.S9 by
            dsimp [PositiveTD.eta]; linarith [ht.2.2.2.2.2,ht.2.2.1]) hp.2.2.1.le
    simpa [Cactual,Explicit.c,zAt,PositiveBT3.tilted,cUpper,aeval_comp,
      Certificate.eta,PositiveTD.eta] using hh

/-- A q-star comparison is needed only for the high-family B-negative rows. -/
def needs_qstar : Row→Bool
  | .smallHigh i => decide (i=2)
  | .farHigh i _ => decide (i=2)
  | _ => false

theorem qstar_certificate : ∀r : Row,needs_qstar r=true →
    centered 0 (GlobalGA.NegativeEHBT3.Certificate.width r) (qStar r-m r)=
      expansion 3 (centered 0 (GlobalGA.NegativeEHBT3.Certificate.width r) (qStar r-m r)) ∧
    (0:ℚ)<lowerOn 3 0 (GlobalGA.NegativeEHBT3.Certificate.width r) (qStar r-m r) := by
  intro r hr
  have hcomp : qStar r-m r=(lBase (family r)+C (3/20)*(C Certificate.h-X)-mBase (family r)).comp (theta r) := by
    simp [qStar,Certificate.l,Certificate.m,sub_comp,add_comp,mul_comp,C_comp,X_comp]
  rw [hcomp,show GlobalGA.NegativeEHBT3.Certificate.width r=right r-left r from rfl]
  cases r with
  | smallHigh j =>
    exact r75_qstar_cert .smallHigh (1/6) (7/10) 1 30 13 8 (by norm_num)
      (by norm_num) (by norm_num) (by decide +kernel)
  | farHigh j b =>
    exact r75_qstar_cert .farHigh (1/4) (7/10) 1 40 19 9 (by norm_num)
      (by norm_num) (by norm_num) (by decide +kernel)
  | _ => simp [needs_qstar] at hr

lemma qstar_bound (r : Row) (hr : needs_qstar r=true) {x : ℝ}
    (hx : x∈Icc 0 (GlobalGA.NegativeEHBT3.Certificate.width r:ℝ)) :
    max (Lactual r x) (Mactual r x)≤aeval x (qStar r) := by
  have hc := qstar_certificate r hr
  have hm := positive_on_interval (interval_positive r) hc.1 hc.2 (x:=x)
    (by rw [Rat.cast_zero]; exact hx)
  simp only [map_sub,m_eval,Rat.cast_zero] at hm
  have ht := frame_domain r hx
  refine max_le ?_ (by linarith)
  simp only [qStar,map_add,map_mul,map_sub,aeval_C,l_eval,theta_eval,eq_ratCast]
  norm_num [Certificate.h,frameCap] at ht ⊢
  linarith [ht.2]

/-- The quartic small-high allowance is weaker than the existing sixth-order
support bound on the whole native interval. -/
lemma small_high_charge {t : ℝ} (ht : t∈Icc (1/6:ℝ) (7/10)) :
    aeval t (JBase .smallHigh)≤TwoPositive.ASupport.charge t := by
  have hh := NegativeDEPositiveTD.AEnvelope.high_polynomial_charge ht
  have hx : t-1/6∈Icc (0:ℝ) (8/15) := ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have hx2 := pow_le_pow_left₀ hx.1 hx.2 2
  have hmul := mul_le_mul_of_nonneg_left hx2 (pow_nonneg hx.1 4)
  have hcompare : (151/500:ℝ)*(t-1/6)^6≤(43/500)*(t-1/6)^4 := by
    nlinarith [pow_nonneg hx.1 4]
  have hJ : aeval t J0=aeval t NegativeDEPositiveTD.Certificate.J0 := by
    simp [J0,abar,NegativeDEPositiveTD.Certificate.J0]
  simp only [JBase,map_sub,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast]
  rw [hJ]
  simp only [NegativeDEPositiveTD.Certificate.J1,map_sub,map_mul,map_pow,
    aeval_C,aeval_X,eq_ratCast] at hh
  push_cast [PositiveTD.Certificate.L] at hh ⊢
  linarith only [hh,hcompare]

lemma charge_lower (r : Row) {x : ℝ} (hx : x∈Icc 0 (GlobalGA.NegativeEHBT3.Certificate.width r:ℝ)) :
    aeval x (J r)≤TwoPositive.ASupport.charge (thetaAt r x) := by
  have ht := original_domain r hx
  simp only [J,aeval_comp,theta_eval]
  have hq (h0 : ((left r:ℚ):ℝ)=0 ∨ ((left r:ℚ):ℝ)=1/10) (h1 : ((right r:ℚ):ℝ)≤1/4) :
      thetaAt r x∈Icc (0:ℝ) (1/4) := by
    constructor
    · rcases h0 with h0|h0 <;> linarith [ht.1]
    · linarith [ht.2]
  cases r
  · simpa [family,JBase,J0,abar,NegativeDEPositiveTD.Certificate.J0] using
      NegativeEHPositiveTD.Certificate.low_A_charge_quarter
        (hq (Or.inl (by norm_num [left])) (by norm_num [right]))
  · simpa [family,JBase,J0,abar,NegativeDEPositiveTD.Certificate.J0] using
      NegativeEHPositiveTD.Certificate.low_A_charge_quarter
        (hq (Or.inr (by norm_num [left])) (by norm_num [right]))
  · exact small_high_charge (by simpa [left,right] using ht)
  · simpa [family,JBase,J0,abar,NegativeDEPositiveTD.Certificate.J0] using
      NegativeEHPositiveTD.Certificate.low_A_charge_quarter
        (hq (Or.inl (by norm_num [left])) (by norm_num [right]))
  · simpa [family,JBase,J0,abar,NegativeDEPositiveTD.Certificate.J0] using
      NegativeEHPositiveTD.Certificate.low_A_charge_quarter
        (hq (Or.inr (by norm_num [left])) (by norm_num [right]))
  · simpa [family,JBase,J0,abar,NegativeDEPositiveTD.Certificate.J0] using
      NegativeEHPositiveTD.Certificate.low_A_charge_quarter
        (hq (Or.inr (by norm_num [left])) (by norm_num [right]))
  · rename_i j b
    have ht' : thetaAt (.farHigh j b) x∈Icc (1/6:ℝ) (7/10) := by
      norm_num [left,right] at ht
      exact ⟨by linarith [ht.1],ht.2⟩
    simpa [family,JBase,J0,abar,NegativeDEPositiveTD.Certificate.J1,
      NegativeDEPositiveTD.Certificate.J0,PositiveTD.Certificate.L] using
      NegativeDEPositiveTD.AEnvelope.high_polynomial_charge ht'

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHBT3.EndpointInputs
