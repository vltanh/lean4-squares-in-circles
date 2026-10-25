module

public import SquaresInCircles.Eight.TableFree.PowerTailBounds

/-!
# The continuous stress polynomial at the wrong aligned GA/DE endpoint

Uncompiled draft.  All coefficients are the explicit rational edge
weights and circle masses of the hand proof.  Clearing their positive
denominators gives one polynomial on the complete sine interval.  Its
negative tail is bounded by its coefficient norm and the retained cubic
is positive by one completed square.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.AlignedGAEndpointPolynomial
open Polynomial PowerTailBounds

def aP : ℚ[X] := C (24/41)+C (3/5)*X+C (1/10)*X^2+C (1/5)*X^3
def betaP : ℚ[X] := 1+C (33/100)*X-C (27/200)*X^2+C (9/25)*X^3
def deltaP : ℚ[X] := C (36/31)-C (49/100)*X-C (1/20)*X^2+C (9/100)*X^3
def epsilonP : ℚ[X] := C (36/31)-C (159/200)*X+C (83/200)*X^2-C (87/400)*X^3
def massAP : ℚ[X] := C (12/41)+C (19/250)*X+C (41/1000)*X^2
def massBP : ℚ[X] := C (12/41)+C (1/50)*X-C (67/500)*X^2+C (19/500)*X^3
def massDP : ℚ[X] := C (12/31)-C (1/25)*X-C (7/1000)*X^2+C (41/500)*X^3
def massHP : ℚ[X] := C (12/31)-C (19/125)*X+C (101/1000)*X^2-C (53/1000)*X^3
def massEP : ℚ[X] := X*(C (38/125)-C (47/250)*X+C (11/100)*X^2-C (11/250)*X^3)
def denominator : ℚ[X] := C 4*massAP*massBP*massDP*massHP*massEP

def constantNumerator : ℚ[X] :=
  denominator*(C 3+C 2*aP+C 2*betaP+C 2*deltaP+epsilonP+epsilonP*X-
      C (9789/2500)*(massAP+massBP+massDP+massHP+massEP))-
    massBP*massDP*massHP*massEP*(1+aP^2)-
    massAP*massDP*massHP*massEP*(betaP^2+aP^2-C 2*aP*betaP*X)-
    massAP*massBP*massHP*massEP*(deltaP^2+betaP^2)-
    massAP*massBP*massDP*massEP*(epsilonP^2+1)-
    massAP*massBP*massDP*massHP*(deltaP^2+epsilonP^2)

def cosineNumerator : ℚ[X] :=
  denominator*betaP+C 2*deltaP*epsilonP*massAP*massBP*massDP*massHP
def cosineLower : ℚ[X] := 1-C (1/2)*X^2-C (13/100)*X^4
def P : ℚ[X] := constantNumerator+cosineNumerator*cosineLower
def L : ℚ[X] := ∑j : Fin 22,C (P.coeff (j.val+1))*X^j.val

def negativeTailNorm (p : ℚ[X]) (start count : ℕ) (r : ℚ) : ℚ :=
  ∑j : Fin count,max 0 (-(p.coeff (j.val+start)))*r^(j.val+start-3)

/-! Exact rational coefficient lists: `r23ev l` is the polynomial with coefficient list `l`;
sums and products of lists are computed by the kernel. -/
private def r23ev : List ℚ → ℚ[X]
  | [] => 0
  | a :: l => C a + X * r23ev l

private def r23add : List ℚ → List ℚ → List ℚ
  | [], m => m
  | a :: l, [] => a :: l
  | a :: l, b :: m => (a+b) :: r23add l m

private def r23smul (c : ℚ) : List ℚ → List ℚ
  | [] => []
  | a :: l => (c*a) :: r23smul c l

private def r23mul : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | a :: l, m => r23add (r23smul a m) (0 :: r23mul l m)

private def r23sub (l m : List ℚ) : List ℚ := r23add l (r23smul (-1) m)

private theorem r23ev_add (l m : List ℚ) : r23ev (r23add l m)=r23ev l+r23ev m := by
  induction l generalizing m with
  | nil => simp [r23add,r23ev]
  | cons a l ih =>
    cases m with
    | nil => simp [r23add,r23ev]
    | cons b m => simp only [r23add,r23ev,ih,map_add]; ring

private theorem r23ev_smul (c : ℚ) (l : List ℚ) : r23ev (r23smul c l)=C c*r23ev l := by
  induction l with
  | nil => simp [r23smul,r23ev]
  | cons a l ih => simp only [r23smul,r23ev,ih,map_mul]; ring

private theorem r23ev_mul (l m : List ℚ) : r23ev (r23mul l m)=r23ev l*r23ev m := by
  induction l with
  | nil => simp [r23mul,r23ev]
  | cons a l ih => simp only [r23mul,r23ev,r23ev_add,r23ev_smul,ih,map_zero]; ring

private theorem r23ev_sub (l m : List ℚ) : r23ev (r23sub l m)=r23ev l-r23ev m := by
  simp only [r23sub,r23ev_add,r23ev_smul,map_neg,map_one]; ring

private theorem r23ev_single (a : ℚ) : r23ev [a]=C a := by simp [r23ev]

private theorem r23ev_X : r23ev [0,1]=X := by simp [r23ev]

private theorem r23_coeff (l : List ℚ) (n : ℕ) : (r23ev l).coeff n=l.getD n 0 := by
  induction l generalizing n with
  | nil => simp [r23ev]
  | cons a l ih =>
    cases n with
    | zero => simp [r23ev]
    | succ n => simp [r23ev,ih]

private theorem r23_natDegree (l : List ℚ) (n : ℕ) (h : l.length≤n+1) :
    (r23ev l).natDegree≤n := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [r23_coeff,List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega)]
  rfl

private def r23aL : List ℚ := [24/41,3/5,1/10,1/5]
private def r23betaL : List ℚ := [1,33/100,-(27/200),9/25]
private def r23deltaL : List ℚ := [36/31,-(49/100),-(1/20),9/100]
private def r23epsL : List ℚ := [36/31,-(159/200),83/200,-(87/400)]
private def r23mAL : List ℚ := [12/41,19/250,41/1000]
private def r23mBL : List ℚ := [12/41,1/50,-(67/500),19/500]
private def r23mDL : List ℚ := [12/31,-(1/25),-(7/1000),41/500]
private def r23mHL : List ℚ := [12/31,-(19/125),101/1000,-(53/1000)]
private def r23mEL : List ℚ := [0,38/125,-(47/250),11/100,-(11/250)]
private def r23cosLL : List ℚ := [1,0,-(1/2),0,-(13/100)]

private def r23denL : List ℚ :=
  r23smul 4 (r23mul (r23mul (r23mul (r23mul r23mAL r23mBL) r23mDL) r23mHL) r23mEL)

/-- The coefficient list of `P`, built from the coefficient lists of its factors. -/
private def r23PL : List ℚ :=
  r23add
    (r23sub (r23sub (r23sub (r23sub (r23sub
      (r23mul r23denL
        (r23sub (r23add (r23add (r23add (r23add (r23add [3] (r23smul 2 r23aL))
          (r23smul 2 r23betaL)) (r23smul 2 r23deltaL)) r23epsL) (r23mul r23epsL [0,1]))
          (r23smul (9789/2500)
            (r23add (r23add (r23add (r23add r23mAL r23mBL) r23mDL) r23mHL) r23mEL))))
      (r23mul (r23mul (r23mul (r23mul r23mBL r23mDL) r23mHL) r23mEL)
        (r23add [1] (r23mul r23aL r23aL))))
      (r23mul (r23mul (r23mul (r23mul r23mAL r23mDL) r23mHL) r23mEL)
        (r23sub (r23add (r23mul r23betaL r23betaL) (r23mul r23aL r23aL))
          (r23mul (r23mul (r23smul 2 r23aL) r23betaL) [0,1]))))
      (r23mul (r23mul (r23mul (r23mul r23mAL r23mBL) r23mHL) r23mEL)
        (r23add (r23mul r23deltaL r23deltaL) (r23mul r23betaL r23betaL))))
      (r23mul (r23mul (r23mul (r23mul r23mAL r23mBL) r23mDL) r23mEL)
        (r23add (r23mul r23epsL r23epsL) [1])))
      (r23mul (r23mul (r23mul (r23mul r23mAL r23mBL) r23mDL) r23mHL)
        (r23add (r23mul r23deltaL r23deltaL) (r23mul r23epsL r23epsL))))
    (r23mul
      (r23add (r23mul r23denL r23betaL)
        (r23mul (r23mul (r23mul (r23mul (r23mul (r23smul 2 r23deltaL) r23epsL) r23mAL)
          r23mBL) r23mDL) r23mHL))
      r23cosLL)

/-- The exact coefficients of `P`, from degree `0` to degree `22`. -/
private def r23Pval : List ℚ :=
  [0,
    (9540716544/160408243046875),
    -(634136910024996/621581941806640625),
    (404890745041756854/77697742725830078125),
    -(681559526107238333121/155395485451660156250000),
    (57787135570716920459771/15539548545166015625000000),
    (2053387667144162876703857/1553954854516601562500000000),
    -(67219609180953900335828631/31079097090332031250000000000),
    (9947098672517793825760090283/2486327767226562500000000000000),
    -(24235702328351608358798480487/9945311068906250000000000000000),
    (26218056087615356689275839/15649584687500000000000000000),
    -(2512558152083908969682339/3912396171875000000000000000),
    (613754001009047374459979/15649584687500000000000000000),
    (27217136776673006251589/201930125000000000000000000),
    -(386783771623942816459439/2019301250000000000000000000),
    (24641958841780056090521/201930125000000000000000000),
    -(160453607752165575971777/2019301250000000000000000000),
    (3653958631474495541/99296875000000000000000),
    -(2923688617249312569/198593750000000000000000),
    (4557954318519557087/794375000000000000000000),
    -(6614981565063/5000000000000000000),
    (825534164871/2500000000000000000),
    -(2178591129/39062500000000000)]

private theorem r23PL_val : r23PL=r23Pval := by decide +kernel

private theorem r23aP : aP=r23ev r23aL := by
  simp only [aP,r23aL,r23ev]; ring
private theorem r23betaP : betaP=r23ev r23betaL := by
  simp only [betaP,r23betaL,r23ev,map_neg,map_one]; ring
private theorem r23deltaP : deltaP=r23ev r23deltaL := by
  simp only [deltaP,r23deltaL,r23ev,map_neg]; ring
private theorem r23epsP : epsilonP=r23ev r23epsL := by
  simp only [epsilonP,r23epsL,r23ev,map_neg]; ring
private theorem r23mAP : massAP=r23ev r23mAL := by
  simp only [massAP,r23mAL,r23ev]; ring
private theorem r23mBP : massBP=r23ev r23mBL := by
  simp only [massBP,r23mBL,r23ev,map_neg]; ring
private theorem r23mDP : massDP=r23ev r23mDL := by
  simp only [massDP,r23mDL,r23ev,map_neg]; ring
private theorem r23mHP : massHP=r23ev r23mHL := by
  simp only [massHP,r23mHL,r23ev,map_neg]; ring
private theorem r23mEP : massEP=r23ev r23mEL := by
  simp only [massEP,r23mEL,r23ev,map_neg,map_zero]; ring
private theorem r23cosL : cosineLower=r23ev r23cosLL := by
  simp only [cosineLower,r23cosLL,r23ev,map_neg,map_one,map_zero]; ring

private theorem r23P_ev : P=r23ev r23Pval := by
  rw [← r23PL_val]
  simp only [r23PL,r23denL,r23ev_add,r23ev_sub,r23ev_mul,r23ev_smul,r23ev_single,r23ev_X,
    map_one,← r23aP,← r23betaP,← r23deltaP,← r23epsP,← r23mAP,← r23mBP,← r23mDP,← r23mHP,
    ← r23mEP,← r23cosL]
  simp only [P,constantNumerator,cosineNumerator,denominator]
  ring

private theorem r23L_coeff (k : ℕ) (hk : k<22) : L.coeff k=r23Pval.getD (k+1) 0 := by
  rw [← r23_coeff,← r23P_ev]
  simp only [L,finsetSum_coeff,coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single ⟨k,hk⟩]
  · simp
  · intro j _ hj
    rw [ite_eq_right_iff]
    intro h
    exact absurd (Fin.ext h.symm) hj
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem negative_tail_cubic {p : ℚ[X]} {start count : ℕ} {r : ℚ} {s : ℝ}
    (hstart : 3≤ start) (hr : 0≤r) (hs : s∈Icc 0 (r:ℝ)) :
    -(negativeTailNorm p start count r:ℝ)*s^3≤aeval s (tail p start count) := by
  have hterm (j : Fin count) :
      -(max 0 (-(p.coeff (j.val+start))):ℝ)*(r:ℝ)^(j.val+start-3)*s^3≤
        (p.coeff (j.val+start):ℝ)*s^(j.val+start) := by
    have hco : -(max 0 (-(p.coeff (j.val+start))):ℝ)≤(p.coeff (j.val+start):ℝ) := by
      have hh : -(max 0 (-(p.coeff (j.val+start))))≤p.coeff (j.val+start) := by
        linarith [le_max_right 0 (-(p.coeff (j.val+start)))]
      exact_mod_cast hh
    have hn0 : (0:ℝ)≤(max 0 (-(p.coeff (j.val+start))):ℝ) := by
      exact_mod_cast (le_max_left 0 (-(p.coeff (j.val+start))))
    have hp := pow_le_pow_left₀ hs.1 hs.2 (j.val+start-3)
    have hm := mul_le_mul_of_nonneg_left hp hn0
    have hm' := mul_le_mul_of_nonneg_right hm (pow_nonneg hs.1 3)
    have hc := mul_le_mul_of_nonneg_right hco (pow_nonneg hs.1 (j.val+start))
    have hid : s^(j.val+start-3)*s^3=s^(j.val+start) := by
      rw [←pow_add]
      congr 1
      omega
    nlinarith [hid]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hterm j)
  simp only [tail,map_sum,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast]
  have hn : (negativeTailNorm p start count r:ℝ)=
      ∑j : Fin count,(max 0 (-(p.coeff (j.val+start))):ℝ)*(r:ℝ)^(j.val+start-3) := by
    simp [negativeTailNorm]
  rw [hn]
  simpa only [neg_mul,Finset.sum_neg_distrib,Finset.sum_mul] using hsum

theorem P_factor : P=X*L := by
  have hdeg : P.natDegree<23 := by
    rw [r23P_ev]
    exact Nat.lt_succ_of_le (r23_natDegree _ 22 (by rfl))
  have h0 : P.coeff 0=0 := by
    rw [r23P_ev,r23_coeff]
    rfl
  conv_lhs => rw [as_sum_range_C_mul_X_pow' P hdeg]
  rw [Finset.sum_range_succ',h0,map_zero,zero_mul,add_zero,← Fin.sum_univ_eq_sum_range,L,
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

theorem L_expansion :
    L=C (L.coeff 0)+C (L.coeff 1)*X+C (L.coeff 2)*X^2+C (L.coeff 3)*X^3+
      C (L.coeff 4)*X^4+C (L.coeff 5)*X^5+C (L.coeff 6)*X^6+
      C (L.coeff 7)*X^7+tail L 8 14 := by
  have hdeg : L.natDegree<22 := by
    have h : L.natDegree≤21 := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro N hN
      simp only [L,finsetSum_coeff,coeff_C_mul_X_pow]
      refine Finset.sum_eq_zero (fun j _ => ?_)
      have := j.2
      rw [ite_eq_right_iff]
      intro h
      omega
    omega
  conv_lhs => rw [as_sum_range_C_mul_X_pow' L hdeg]
  rw [show (22:ℕ)=8+14 from rfl,Finset.sum_range_add,tail,
    Fin.sum_univ_eq_sum_range (fun j => C (L.coeff (j+8))*X^(j+8)) 14]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,pow_zero,pow_one,mul_one,zero_add]

theorem leading_reserves :
    (5947/100000000 : ℚ)<L.coeff 0 ∧
      -(10203/10000000 : ℚ)<L.coeff 1 ∧
      (5211/1000000 : ℚ)<L.coeff 2 ∧
      -(2193/500000 : ℚ)<L.coeff 3 ∧
      0≤L.coeff 4 ∧ 0≤L.coeff 5 ∧
      -(2163/1000000 : ℚ)<L.coeff 6 ∧ 0≤L.coeff 7 := by
  rw [r23L_coeff 0 (by norm_num),r23L_coeff 1 (by norm_num),r23L_coeff 2 (by norm_num),
    r23L_coeff 3 (by norm_num),r23L_coeff 4 (by norm_num),r23L_coeff 5 (by norm_num),
    r23L_coeff 6 (by norm_num),r23L_coeff 7 (by norm_num)]
  decide +kernel

theorem tail_reserve :
    (2163/1000000 : ℚ)*(11/50)^3+negativeTailNorm L 8 14 (11/50)<1/40000 := by
  have h : negativeTailNorm L 8 14 (11/50)=
      ∑j : Fin 14,max 0 (-(r23Pval.getD (j.val+8+1) 0))*(11/50)^(j.val+8-3) := by
    unfold negativeTailNorm
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [r23L_coeff _ (by omega)]
  rw [h]
  decide +kernel

def cubic (s : ℝ) : ℝ :=
  5947/100000000-(10203/10000000)*s+(5211/1000000)*s^2-(4411/1000000)*s^3

theorem cubic_lower {s : ℝ} (hs : s∈Icc 0 (11/50 : ℝ)) : cubic s≤aeval s L := by
  have hs' : s∈Icc 0 ((11/50:ℚ):ℝ) := by
    push_cast
    exact hs
  have ht := negative_tail_cubic (p := L) (start := 8) (count := 14)
    (by norm_num) (by norm_num : (0:ℚ)≤11/50) hs'
  have hc0 : (5947/100000000 : ℝ)≤(L.coeff 0:ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr leading_reserves.1.le
    push_cast at h
    exact h
  have hc1 : -(10203/10000000 : ℝ)≤(L.coeff 1:ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr leading_reserves.2.1.le
    push_cast at h
    exact h
  have hc2 : (5211/1000000 : ℝ)≤(L.coeff 2:ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr leading_reserves.2.2.1.le
    push_cast at h
    exact h
  have hc3 : -(2193/500000 : ℝ)≤(L.coeff 3:ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr leading_reserves.2.2.2.1.le
    push_cast at h
    exact h
  have hc4 : (0:ℝ)≤(L.coeff 4:ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr leading_reserves.2.2.2.2.1
    push_cast at h
    exact h
  have hc5 : (0:ℝ)≤(L.coeff 5:ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr leading_reserves.2.2.2.2.2.1
    push_cast at h
    exact h
  have hc6 : -(2163/1000000 : ℝ)≤(L.coeff 6:ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr leading_reserves.2.2.2.2.2.2.1.le
    push_cast at h
    exact h
  have hc7 : (0:ℝ)≤(L.coeff 7:ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr leading_reserves.2.2.2.2.2.2.2
    push_cast at h
    exact h
  have ht' : (2163/1000000 : ℝ)*(11/50)^3+(negativeTailNorm L 8 14 (11/50):ℝ)≤1/40000 := by
    have h := (Rat.cast_le (K := ℝ)).mpr tail_reserve.le
    push_cast at h
    exact h
  have h1 := mul_le_mul_of_nonneg_right hc1 hs.1
  have h2 := mul_le_mul_of_nonneg_right hc2 (pow_nonneg hs.1 2)
  have h3 := mul_le_mul_of_nonneg_right hc3 (pow_nonneg hs.1 3)
  have h4 := mul_nonneg hc4 (pow_nonneg hs.1 4)
  have h5 := mul_nonneg hc5 (pow_nonneg hs.1 5)
  have h6 := mul_le_mul_of_nonneg_right hc6 (pow_nonneg hs.1 6)
  have h6power := mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ hs.1 hs.2 3) (pow_nonneg hs.1 3)
  have h7 := mul_nonneg hc7 (pow_nonneg hs.1 7)
  have htail := mul_le_mul_of_nonneg_right ht' (pow_nonneg hs.1 3)
  have hid := congrArg (fun p : ℚ[X] => aeval s p) L_expansion
  simp only [map_add,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast] at hid
  have h66 : s^3*s^3=s^6 := by ring
  dsimp [cubic]
  linarith

theorem cubic_positive {s : ℝ} (hs : s∈Icc 0 (11/50 : ℝ)) : 0<cubic s := by
  have hcoef : 0≤99529/50000000-(4411/1000000)*s := by linarith [hs.2]
  have hrem := mul_nonneg (sq_nonneg (s-11/100)) hcoef
  have hid : cubic s=
      4419059/1000000000000-(339993/10000000000)*(s-11/100)+
        (9/4000)*(s-11/100)^2+
        (s-11/100)^2*(99529/50000000-(4411/1000000)*s) := by
    dsimp [cubic]
    ring
  nlinarith [sq_nonneg (s-11/100-37777/5000000)]

theorem P_positive {s : ℝ} (hs : s∈Ioc 0 (11/50 : ℝ)) : 0<aeval s P := by
  have hl := (cubic_positive ⟨hs.1.le,hs.2⟩).trans_le (cubic_lower ⟨hs.1.le,hs.2⟩)
  rw [P_factor,map_mul,aeval_X]
  exact mul_pos hs.1 hl

theorem cosine_lower {s c : ℝ} (hs : s∈Icc 0 (11/50 : ℝ))
    (hc : 0≤c) (hunit : c^2+s^2=1) :
    (1-s^2/2-(13/100)*s^4)≤c := by
  have h2 := pow_le_pow_left₀ hs.1 hs.2 2
  have h4 := pow_le_pow_left₀ hs.1 hs.2 4
  have hpositive : 0≤1-s^2/2-(13/100)*s^4 := by nlinarith
  have hcoef : -(1/100 : ℝ)+(13/100)*s^2+(169/10000)*s^4≤0 := by nlinarith
  have hprod := mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hs.1 4) hcoef
  have hid : (1-s^2/2-(13/100)*s^4)^2-(1-s^2)=
      s^4*(-1/100+(13/100)*s^2+(169/10000)*s^4) := by ring
  nlinarith

end SquaresInCircles.Eight.TableFree.AlignedGAEndpointPolynomial
