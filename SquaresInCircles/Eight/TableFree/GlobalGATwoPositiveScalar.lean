module

public import SquaresInCircles.Eight.TableFree.GlobalGATwoPositiveSplit

/-!
# Every intrinsic scalar of the two-positive split is positive

Uncompiled transcription of the endpoint join in Section 8 of the
two-positive scalar proof.  In the low range each of the pure,
same-block and separated alternatives is concave in the actual split.
In the high range the already proved balanced reduction leaves three
pure alternatives.  The coefficient families stay fixed at the total
angle during each split comparison.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalGA.TwoPositive
open Candidate Secondary PositiveTD PositiveAngularEnvelope OrdinaryAngleConcavity
open OrdinaryAngleConcentration SplitConcavityTools

namespace Split

def constant (k l c : ℝ) : ℝ :=
  k+(5/2)*l+2-fullSupport 1 k-fullSupport l k-clippedSupport 1 c

def increment (l m s g e : ℝ) : ℝ :=
  g*min l m+e*max l m-R*(pairNorm l m s-pairNorm l m 0)

theorem base_identity {k l c t a : ℝ}
    (ht : t∈Icc 0 frameCap) (ha : a∈Icc 0 t) :
    splitBase k l c t a=constant k l c+
      Coefficient.H l 0 0 0 (tilted c (t-a))+rest c l t a := by
  rw [splitBase,rest,smooth_actual (split_domain ht ha).2]
  simp only [baseline,fullSupport_pair,Coefficient.H,constant,zero_mul,add_zero]
  rw [pairNorm_symm (tilted c (t-a)) l 0]
  ring

theorem increment_identity {k l c t a s g e : ℝ}
    (ht : t∈Icc 0 frameCap) (ha : a∈Icc 0 t) :
    splitBase k l c t a+increment l (tilted c (t-a)) s g e=
      constant k l c+Coefficient.H l s g e (tilted c (t-a))+rest c l t a := by
  rw [base_identity ht ha]
  dsimp [increment,Coefficient.H]
  ring

theorem add_constant {f : ℝ→ℝ} {t : ℝ} (hf : ConcaveOn ℝ (Icc 0 t) f) (K : ℝ) :
    ConcaveOn ℝ (Icc 0 t) (fun a => f a+K) := by
  refine ⟨hf.1,?_⟩
  intro x hx y hy r v hr hv hrv
  have hh := hf.2 hx hy hr hv hrv
  have he := congrArg (fun w : ℝ => w*K) hrv
  simp only [smul_eq_mul] at hh ⊢
  nlinarith only [hh,he]

theorem congr_on {f g : ℝ→ℝ} {t : ℝ} (hf : ConcaveOn ℝ (Icc 0 t) f)
    (he : ∀a∈Icc 0 t,f a=g a) : ConcaveOn ℝ (Icc 0 t) g := by
  refine ⟨hf.1,?_⟩
  intro x hx y hy r v hr hv hrv
  have hh := hf.2 hx hy hr hv hrv
  rw [he x hx,he y hy,he _ (hf.1 hx hy hr hv hrv)] at hh
  exact hh

theorem low_increment_concave {k c l t s g e : ℝ}
    (hc : 0<c) (hl : 0<l) (hcl : c≤(3/2)*l)
    (ht : t∈Icc 0 (1/6:ℝ)) (hs : |s|≤frameCap)
    (hg : 0≤g) (he : e≤0) (heLow : Real.cos frameCap-1≤e)
    (hePos : 0<s→e=0)
    (hm : ∀a∈Icc 0 t,tilted c (t-a)≤(3/2)*l) :
    ConcaveOn ℝ (Icc 0 t)
      (fun a => splitBase k l c t a+increment l (tilted c (t-a)) s g e) := by
  have ht' : t∈Icc 0 frameCap := ⟨ht.1,by norm_num [frameCap]; linarith [ht.2]⟩
  have hh := add_constant (low_scalar_concave hc hl hcl ht hs hg he heLow hePos hm)
    (constant k l c)
  apply congr_on hh
  intro a ha
  rw [increment_identity ht' ha]
  ring

theorem high_increment_concave {k c l t s g e L U : ℝ}
    (hl : 0<l) (hcLow : (9/10)*l≤c) (hcHigh : c≤(11/10)*l)
    (ht : t∈Icc 0 frameCap) (hs : s∈Icc 0 frameCap)
    (hL : 0<L) (hU : U≤(23/20)*l)
    (hge : e≤g) (he : Real.cos s-1≤e)
    (hm : ∀a∈Icc 0 t,tilted c (t-a)∈Icc L U) :
    ConcaveOn ℝ (Icc 0 t)
      (fun a => splitBase k l c t a+increment l (tilted c (t-a)) (-s) g e) := by
  have hh := add_constant (high_scalar_concave hl hcLow hcHigh ht hs hL hU hge he hm)
    (constant k l c)
  apply congr_on hh
  intro a ha
  rw [increment_identity ht ha]
  ring

@[simp] theorem increment_zero (l m : ℝ) : increment l m 0 0 0=0 := by
  simp [increment]

theorem increment_V (l m s : ℝ) :
    increment l m (-s) 0 (Real.cos s-1)=V R (min l m) (max l m) s := by
  simp only [increment,V,Certificate.sorted_pair_norm,zero_mul,zero_add]
  ring

theorem increment_U (l m s : ℝ) :
    increment l m s (phi s-1) 0=U R (min l m) (max l m) s := by
  simp only [increment,U,Certificate.sorted_pair_norm,zero_mul,add_zero]
  ring

theorem increment_M (l m t : ℝ) :
    increment l m (-t) (phi (frameCap-t)-1) (Real.cos frameCap-1)=
      M R (min l m) (max l m) t := by
  simp only [increment,M,Certificate.sorted_pair_norm]
  ring

theorem cos_cap_le {s : ℝ} (hs : s∈Icc 0 frameCap) :
    Real.cos frameCap≤Real.cos s :=
  Real.cos_le_cos_of_nonneg_of_le_pi hs.1
    (by dsimp [frameCap]; linarith [Real.pi_gt_three]) hs.2

theorem phi_ge_one {s : ℝ} (hs : s∈Icc 0 frameCap) : 1≤phi s := by
  have hp : s∈Icc 0 (Real.pi/2) := ⟨hs.1,by dsimp [frameCap] at hs; linarith [hs.2,Real.pi_gt_three]⟩
  have hsin := Real.sin_nonneg_of_nonneg_of_le_pi hp.1 (by linarith [hp.2,Real.pi_pos])
  have hcos := (transport_trig hs).1
  have hprod := mul_nonneg hsin hcos.le
  dsimp [phi]
  nlinarith [Real.sin_sq_add_cos_sq s]

end Split

def pureScalar (k l c t : ℝ) (j : Fin 4) (a : ℝ) : ℝ :=
  splitBase k l c t a+
    V R (pWeights k l (tilted c (t-a)) j) (qWeights k l (tilted c (t-a)) j) t

def sameScalar (k l c t : ℝ) (i : Fin 4) (a : ℝ) : ℝ :=
  splitBase k l c t a+
    Hybrid.saturated R (diagonal-1/2)
      (pWeights k l (tilted c (t-a))) (qWeights k l (tilted c (t-a))) 3 i t

def separatedScalar (k l c t : ℝ) (i j : Fin 4) (a : ℝ) : ℝ :=
  splitBase k l c t a+
    Hybrid.positive R (diagonal-1/2)
      (pWeights k l (tilted c (t-a))) (qWeights k l (tilted c (t-a))) 3 i (frameCap-t)+
    V R (pWeights k l (tilted c (t-a)) j) (qWeights k l (tilted c (t-a)) j) frameCap

theorem positive_independent {i : Fin 4} (hi : i≠2) (k l m b : ℝ) :
    Hybrid.positive R (diagonal-1/2) (pWeights k l m) (qWeights k l m) 3 i b=
      Hybrid.positive R (diagonal-1/2) (pWeights k l 0) (qWeights k l 0) 3 i b := by
  fin_cases i <;> simp_all [Hybrid.positive,pWeights,qWeights]

theorem negative_independent {j : Fin 4} (hj : j≠2) (k l m t : ℝ) :
    V R (pWeights k l m j) (qWeights k l m j) t=
      V R (pWeights k l 0 j) (qWeights k l 0 j) t := by
  fin_cases j <;> simp_all [pWeights,qWeights]

theorem low_base_concave {k l c t : ℝ}
    (hc : 0<c) (hl : 0<l) (hcl : c≤(3/2)*l)
    (ht : t∈Icc 0 (1/6:ℝ))
    (hm : ∀a∈Icc 0 t,tilted c (t-a)≤(3/2)*l) :
    ConcaveOn ℝ (Icc 0 t) (splitBase k l c t) := by
  simpa only [Split.increment_zero,add_zero] using
    Split.low_increment_concave (k:=k) (s:=0) (g:=0) (e:=0)
      hc hl hcl ht (by norm_num [frameCap]) le_rfl le_rfl
      (by linarith [Real.cos_le_one frameCap]) (by simp) hm

theorem low_pure_concave {k l c t : ℝ}
    (hc : 0<c) (hl : 0<l) (hcl : c≤(3/2)*l)
    (ht : t∈Icc 0 (1/6:ℝ))
    (hm : ∀a∈Icc 0 t,tilted c (t-a)≤(3/2)*l) (j : Fin 4) :
    ConcaveOn ℝ (Icc 0 t) (pureScalar k l c t j) := by
  have ht' : t∈Icc 0 frameCap := ⟨ht.1,by norm_num [frameCap]; linarith [ht.2]⟩
  by_cases hj : j=2
  · subst j
    have hh := Split.low_increment_concave (k:=k) (s:=-t) (g:=0) (e:=Real.cos t-1)
      hc hl hcl ht (by rw [abs_neg,abs_of_nonneg ht.1]; exact ht'.2)
      le_rfl (sub_nonpos.mpr (Real.cos_le_one t))
      (by linarith [Split.cos_cap_le ht']) (by intro hh; linarith [ht.1]) hm
    simpa only [Split.increment_V,pureScalar,pWeights,qWeights,
      Matrix.cons_val_succ,Matrix.cons_val_zero] using hh
  · have hh := Split.add_constant (low_base_concave hc hl hcl ht hm)
      (V R (pWeights k l 0 j) (qWeights k l 0 j) t)
    apply Split.congr_on hh
    intro a _
    simp only [pureScalar,negative_independent hj]

theorem low_same_concave {k l c t : ℝ}
    (hc : 0<c) (hl : 0<l) (hcl : c≤(3/2)*l)
    (ht : t∈Icc 0 (1/6:ℝ))
    (hm : ∀a∈Icc 0 t,tilted c (t-a)≤(3/2)*l) (i : Fin 4) :
    ConcaveOn ℝ (Icc 0 t) (sameScalar k l c t i) := by
  have ht' : t∈Icc 0 frameCap := ⟨ht.1,by norm_num [frameCap]; linarith [ht.2]⟩
  have hb : frameCap-t∈Icc 0 frameCap := ⟨by linarith [ht'.2],by linarith [ht.1]⟩
  fin_cases i
  · exact Split.add_constant (low_base_concave hc hl hcl ht hm) (M R k 1 t)
  · exact Split.add_constant (low_base_concave hc hl hcl ht hm) (M R k l t)
  · have hh := Split.low_increment_concave (k:=k) (s:=-t)
      (g:=phi (frameCap-t)-1) (e:=Real.cos frameCap-1)
      hc hl hcl ht (by rw [abs_neg,abs_of_nonneg ht.1]; exact ht'.2)
      (sub_nonneg.mpr (Split.phi_ge_one hb))
      (sub_nonpos.mpr (Real.cos_le_one frameCap)) le_rfl
      (by intro hh; linarith [ht.1]) hm
    simpa only [Split.increment_M,sameScalar,Hybrid.saturated,pWeights,qWeights,
      Matrix.cons_val_succ,Matrix.cons_val_zero,show (2:Fin 4)≠3 by decide,if_false] using hh
  · exact Split.add_constant (low_base_concave hc hl hcl ht hm)
      (-(diagonal-1/2)*(frameCap-t)+V R k 1 frameCap)

theorem low_separated_concave {k l c t : ℝ}
    (hc : 0<c) (hl : 0<l) (hcl : c≤(3/2)*l)
    (ht : t∈Icc 0 (1/6:ℝ))
    (hm : ∀a∈Icc 0 t,tilted c (t-a)≤(3/2)*l)
    (i j : Fin 4) (hij : i≠j) :
    ConcaveOn ℝ (Icc 0 t) (separatedScalar k l c t i j) := by
  have ht' : t∈Icc 0 frameCap := ⟨ht.1,by norm_num [frameCap]; linarith [ht.2]⟩
  have hb : frameCap-t∈Icc 0 frameCap := ⟨by linarith [ht'.2],by linarith [ht.1]⟩
  by_cases hi : i=2
  · subst i
    have hj : j≠2 := Ne.symm hij
    have hh := Split.low_increment_concave (k:=k) (s:=frameCap-t)
      (g:=phi (frameCap-t)-1) (e:=0) hc hl hcl ht
      (by rw [abs_of_nonneg hb.1]; exact hb.2)
      (sub_nonneg.mpr (Split.phi_ge_one hb)) le_rfl
      (by linarith [Real.cos_le_one frameCap]) (by simp) hm
    have h := Split.add_constant hh
      (V R (pWeights k l 0 j) (qWeights k l 0 j) frameCap)
    apply Split.congr_on h
    intro a _
    simp only [Split.increment_U,separatedScalar,Hybrid.positive,
      show (2:Fin 4)≠3 by decide,if_false,pWeights,qWeights,
      Matrix.cons_val_succ,Matrix.cons_val_zero,negative_independent hj]
  · by_cases hj : j=2
    · subst j
      have hh := Split.low_increment_concave (k:=k) (s:=-frameCap)
        (g:=0) (e:=Real.cos frameCap-1) hc hl hcl ht
        (by norm_num [frameCap]) le_rfl (sub_nonpos.mpr (Real.cos_le_one frameCap))
        le_rfl (by norm_num [frameCap]) hm
      have h := Split.add_constant hh
        (Hybrid.positive R (diagonal-1/2) (pWeights k l 0) (qWeights k l 0) 3 i (frameCap-t))
      apply Split.congr_on h
      intro a _
      simp only [Split.increment_V,separatedScalar,pWeights,qWeights,
        Matrix.cons_val_succ,Matrix.cons_val_zero,positive_independent hi]
      ring
    · have hh := Split.add_constant
        (Split.add_constant (low_base_concave hc hl hcl ht hm)
          (Hybrid.positive R (diagonal-1/2) (pWeights k l 0) (qWeights k l 0) 3 i (frameCap-t)))
        (V R (pWeights k l 0 j) (qWeights k l 0 j) frameCap)
      apply Split.congr_on hh
      intro a _
      simp only [separatedScalar,positive_independent hi,negative_independent hj]

theorem scalar_le_pure (k l c t a : ℝ) (i j : Fin 4) :
    splitScalar k l c t a i j≤pureScalar k l c t j a := by
  exact add_le_add_left (min_le_left _ _) _

theorem scalar_le_same (k l c t a : ℝ) (i : Fin 4) :
    splitScalar k l c t a i i≤sameScalar k l c t i a := by
  simpa only [splitScalar,endpoint,sameScalar,if_pos rfl] using
    add_le_add_left (min_le_right
      (V R (pWeights k l (tilted c (t-a)) i) (qWeights k l (tilted c (t-a)) i) t)
      (Hybrid.saturated R (diagonal-1/2)
        (pWeights k l (tilted c (t-a))) (qWeights k l (tilted c (t-a))) 3 i t))
      (splitBase k l c t a)

theorem scalar_le_separated (k l c t a : ℝ) (i j : Fin 4) (hij : i≠j) :
    splitScalar k l c t a i j≤separatedScalar k l c t i j a := by
  have hh := add_le_add_left (min_le_right
    (V R (pWeights k l (tilted c (t-a)) j) (qWeights k l (tilted c (t-a)) j) t)
    (Hybrid.positive R (diagonal-1/2)
      (pWeights k l (tilted c (t-a))) (qWeights k l (tilted c (t-a))) 3 i (frameCap-t)+
    V R (pWeights k l (tilted c (t-a)) j) (qWeights k l (tilted c (t-a)) j) frameCap))
      (splitBase k l c t a)
  simpa only [splitScalar,endpoint,separatedScalar,if_neg hij,add_assoc] using hh

theorem low_split_positive {t a : ℝ} (ht : t∈Icc 0 (1/6:ℝ)) (ha : a∈Icc 0 t)
    (i j : Fin 4) :
    0<splitScalar (Explicit.lowK t) (Explicit.lowL t) (Explicit.lowC t) t a i j := by
  let k := Explicit.lowK t
  let l := Explicit.lowL t
  let c := Explicit.lowC t
  have hd := low_split_domain ht (show (0:ℝ)∈Icc 0 t from ⟨le_rfl,ht.1⟩)
  have hl : 0<l := by dsimp [l]; linarith [hd.1.1,hd.2.1.1]
  have hc : 0<c := by dsimp [c]; linarith [hd.1.1,hd.2.2.1.1]
  have hcl : c≤(3/2)*l := hd.2.2.2.2.1
  have hm (x : ℝ) (hx : x∈Icc 0 t) : tilted c (t-x)≤(3/2)*l :=
    (low_split_domain ht ⟨by linarith [hx.2],by linarith [hx.1]⟩).2.2.2.2.2
  have hpure : 0<pureScalar k l c t j a :=
    concave_gt_of_endpoints (low_pure_concave hc hl hcl ht hm j) ha
      ((low_T_endpoint_positive ht i j).trans_le (scalar_le_pure k l c t 0 i j))
      ((low_A_endpoint_positive ht i j).trans_le (scalar_le_pure k l c t t i j))
  by_cases hij : i=j
  · subst j
    have hsame : 0<sameScalar k l c t i a :=
      concave_gt_of_endpoints (low_same_concave hc hl hcl ht hm i) ha
        ((low_T_endpoint_positive ht i i).trans_le (scalar_le_same k l c t 0 i))
        ((low_A_endpoint_positive ht i i).trans_le (scalar_le_same k l c t t i))
    simpa only [splitScalar,endpoint,pureScalar,sameScalar,if_pos rfl,add_min]
      using lt_min hpure hsame
  · have hsep : 0<separatedScalar k l c t i j a :=
      concave_gt_of_endpoints (low_separated_concave hc hl hcl ht hm i j hij) ha
        ((low_T_endpoint_positive ht i j).trans_le (scalar_le_separated k l c t 0 i j hij))
        ((low_A_endpoint_positive ht i j).trans_le (scalar_le_separated k l c t t i j hij))
    simpa only [splitScalar,endpoint,pureScalar,separatedScalar,if_neg hij,add_min,add_assoc]
      using lt_min hpure hsep

theorem high_coefficient_range {t a : ℝ} (ht : t∈Icc (1/6:ℝ) frameCap)
    (ha : a∈Icc 0 t) :
    tilted (highC t) (t-a)∈Icc (highC t/2) ((23/20)*highL t) := by
  have hr := high_ranges ht
  have hc : 0<highC t := by linarith [hr.2.2.2.2.1]
  have hl : 0<highL t := by linarith [hr.2.2.1]
  have hz : t-a∈Icc 0 frameCap := ⟨by linarith [ha.2],by linarith [ht.2,ha.1]⟩
  have hlow := mul_lt_mul_of_pos_left (Explicit.factor_lower hz) hc
  have hu := mul_lt_mul_of_pos_left (Explicit.factor_upper (t-a)) hc
  have hcHigh := hr.2.2.2.2.2.2.2
  dsimp [tilted]
  constructor <;> nlinarith only [hl,hc,hlow,hu,hcHigh]

theorem high_pure_concave {t : ℝ} (ht : t∈Icc (1/6:ℝ) frameCap) (j : Fin 4) :
    ConcaveOn ℝ (Icc 0 t) (pureScalar (highK t) (highL t) (highC t) t j) := by
  have hr := high_ranges ht
  have hl : 0<highL t := by linarith [hr.2.2.1]
  have hc : 0<highC t := by linarith [hr.2.2.2.2.1]
  have hcLow := hr.2.2.2.2.2.2.1.le
  have hcHigh := hr.2.2.2.2.2.2.2.le
  have ht' : t∈Icc 0 frameCap := ⟨by linarith [ht.1],ht.2⟩
  by_cases hj : j=2
  · subst j
    have hh := Split.high_increment_concave (k:=highK t) (s:=t) (g:=0)
      (e:=Real.cos t-1) hl hcLow hcHigh ht' ht'
      (show 0<highC t/2 by positivity) le_rfl
      (sub_nonpos.mpr (Real.cos_le_one t)) le_rfl (high_coefficient_range ht)
    simpa only [pureScalar,Split.increment_V,pWeights,qWeights,
      Matrix.cons_val_succ,Matrix.cons_val_zero] using hh
  · have hbase : ConcaveOn ℝ (Icc 0 t) (splitBase (highK t) (highL t) (highC t) t) := by
      have hh := Split.high_increment_concave (k:=highK t) (s:=0) (g:=0) (e:=0)
        hl hcLow hcHigh ht' (by norm_num [frameCap])
        (show 0<highC t/2 by positivity) le_rfl le_rfl (by simp) (high_coefficient_range ht)
      simpa only [neg_zero,Split.increment_zero,add_zero] using hh
    apply Split.congr_on (Split.add_constant hbase
      (V R (pWeights (highK t) (highL t) 0 j) (qWeights (highK t) (highL t) 0 j) t))
    intro a _
    simp only [pureScalar,negative_independent hj]

theorem high_pure_positive {t a : ℝ} (ht : t∈Icc (1/6:ℝ) frameCap)
    (ha : a∈Icc 0 t) (j : Fin 4) :
    0<pureScalar (highK t) (highL t) (highC t) t j a := by
  have hzero : 0<pureScalar (highK t) (highL t) (highC t) t j 0 := by
    have hh := Certificate.high_six_scalars_positive .atT ht
    fin_cases j
    · simpa only [pureScalar,splitBase,sub_zero,ASupport.charge_zero,mul_zero,add_zero,highK,highL,highC,Certificate.endpointBase,Certificate.mAt,Certificate.aAt,Certificate.zAt,pWeights,qWeights,Matrix.cons_val_succ,Matrix.cons_val_zero] using hh.1
    · simpa only [pureScalar,splitBase,sub_zero,ASupport.charge_zero,mul_zero,add_zero,highK,highL,highC,Certificate.endpointBase,Certificate.mAt,Certificate.aAt,Certificate.zAt,pWeights,qWeights,Matrix.cons_val_succ,Matrix.cons_val_zero] using hh.2.1
    · simpa only [pureScalar,splitBase,sub_zero,ASupport.charge_zero,mul_zero,add_zero,highK,highL,highC,Certificate.endpointBase,Certificate.mAt,Certificate.aAt,Certificate.zAt,pWeights,qWeights,Matrix.cons_val_succ,Matrix.cons_val_zero] using hh.2.2
    · simpa only [pureScalar,splitBase,sub_zero,ASupport.charge_zero,mul_zero,add_zero,highK,highL,highC,Certificate.endpointBase,Certificate.mAt,Certificate.aAt,Certificate.zAt,pWeights,qWeights,Matrix.cons_val_succ,Matrix.cons_val_zero] using hh.1
  have htotal : 0<pureScalar (highK t) (highL t) (highC t) t j t := by
    have hh := Certificate.high_six_scalars_positive .atA ht
    fin_cases j
    · simpa only [pureScalar,splitBase,sub_self,highK,highL,highC,Certificate.endpointBase,Certificate.mAt,Certificate.aAt,Certificate.zAt,pWeights,qWeights,Matrix.cons_val_succ,Matrix.cons_val_zero] using hh.1
    · simpa only [pureScalar,splitBase,sub_self,highK,highL,highC,Certificate.endpointBase,Certificate.mAt,Certificate.aAt,Certificate.zAt,pWeights,qWeights,Matrix.cons_val_succ,Matrix.cons_val_zero] using hh.2.1
    · simpa only [pureScalar,splitBase,sub_self,highK,highL,highC,Certificate.endpointBase,Certificate.mAt,Certificate.aAt,Certificate.zAt,pWeights,qWeights,Matrix.cons_val_succ,Matrix.cons_val_zero] using hh.2.2
    · simpa only [pureScalar,splitBase,sub_self,highK,highL,highC,Certificate.endpointBase,Certificate.mAt,Certificate.aAt,Certificate.zAt,pWeights,qWeights,Matrix.cons_val_succ,Matrix.cons_val_zero] using hh.1
  exact concave_gt_of_endpoints (high_pure_concave ht j) ha hzero htotal

theorem high_split_positive {t a : ℝ} (ht : t∈Icc (1/6:ℝ) frameCap)
    (ha : a∈Icc 0 t) (i j : Fin 4) :
    0<splitScalar (highK t) (highL t) (highC t) t a i j := by
  have hz : t-a∈Icc 0 t := ⟨by linarith [ha.2],by linarith [ha.1]⟩
  have hd := high_split_domain ht hz
  have hb := high_balanced ht hz
  have hc := coefficient_domain hd.1 hd.2.1 hd.2.2.1
    (show t-a∈Icc 0 frameCap from ⟨hz.1,hz.2.trans ht.2⟩) hd.2.2.2.1
  have he := balanced_endpoint_lower (fun i => (hc i).1) (fun i => (hc i).2.1)
    hb.1 hb.2 (Certificate.high_frame_domain ht) i j
  have hp : 0<splitBase (highK t) (highL t) (highC t) t a+
      balancedEnvelope (highK t) (highL t) (tilted (highC t) (t-a)) t := by
    unfold balancedEnvelope
    rw [add_min,add_min]
    exact lt_min (high_pure_positive ht ha 0)
      (lt_min (high_pure_positive ht ha 1) (high_pure_positive ht ha 2))
  exact hp.trans_le (add_le_add_left he _)

/-- The continuous coefficients are constructed at the actual total;
there are no endpoint reserves or split-positivity premises. -/
theorem explicit_split_positive {t a : ℝ} (ht : t∈Icc 0 frameCap)
    (ha : a∈Icc 0 t) :
    ∃k l c : ℝ,k∈Icc (1/2:ℝ) (17/20) ∧ l∈Icc k (2*k) ∧ c∈Icc k 2 ∧
      (l≤2*tilted c (t-a) ∧ tilted c (t-a)≤2*l) ∧
      ∀i j : Fin 4,0<splitScalar k l c t a i j := by
  have hz : t-a∈Icc 0 t := ⟨by linarith [ha.2],by linarith [ha.1]⟩
  by_cases hlo : t≤1/6
  · have htlo : t∈Icc 0 (1/6:ℝ) := ⟨ht.1,hlo⟩
    have hd := low_split_domain htlo hz
    exact ⟨Explicit.lowK t,Explicit.lowL t,Explicit.lowC t,
      hd.1,hd.2.1,hd.2.2.1,hd.2.2.2.1,low_split_positive htlo ha⟩
  · have hthi : t∈Icc (1/6:ℝ) frameCap := ⟨(lt_of_not_ge hlo).le,ht.2⟩
    have hd := high_split_domain hthi hz
    exact ⟨highK t,highL t,highC t,hd.1,hd.2.1,hd.2.2.1,hd.2.2.2.1,
      high_split_positive hthi ha⟩

end SquaresInCircles.Eight.TableFree.GlobalGA.TwoPositive
