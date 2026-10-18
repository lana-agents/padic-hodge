/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.AdicEval
import PadicHodge.FormalGroup.LayerFree

/-!
# The coefficient filtration of `R[[T]]` and `⋂_v [p^v]_F(I) = 0`

Towards [Hong, Lemma 2.2.15] (`R[[T]] ≅ lim_v A_v`) and the full faithfulness part of
[Hong, Thm. 2.2.16] (Serre–Tate).

* `coeffFilt 𝔪 w`: power series whose coefficient of each monomial `T^m` lies in
  `𝔪^{w − |m|}`; an ideal with `N_a N_b ⊆ N_{a+b}` (`coeffFilt_mul_le`), containing the
  maximal ideal `𝔪 A + (T)` in degree `1` (`maxPS_le_coeffFilt`); `⋂_w N_w = 0` if `R` is
  `𝔪`-adically separated (`eq_zero_of_mem_coeffFilt`). No noetherianity is used.
* `coeff_eq_zero_of_mem_pow_span_X`: elements of `(T)^n` have no monomials of degree `< n`
  (the converse of `AdicEval.mem_pow_span_X`);
* `coeff_single_subst`: the linear part of `f(g)` is the product of the linear parts;
* **[Hong, Lemma 2.2.14]**: `Φ(T, U) ≡ T + U` and `[n]_F(T) ≡ nT` modulo degree `≥ 2`
  (`coeff_single_Φ`, `coeff_single_mulPS`, `mulPS_sub_mem`);
* `layerIdeal_le_pow`: `J_v = [p^v]_F(I) A ⊆ (𝔪A + I)^v` if `p ∈ 𝔪` (from
  `[p]_F(I) ⊆ 𝔪 I + I^2`, as in the proof of [Hong, Lemma 2.2.15]); hence
  **`⋂_v J_v = 0`** (`eq_zero_of_mem_layerIdeal`).
-/

noncomputable section

open MvPowerSeries

namespace PadicHodge

theorem Finsupp.eq_single_of_degree_eq_one {σ : Type*} (m : σ →₀ ℕ) (h : m.degree = 1) :
    ∃ j, m = Finsupp.single j 1 := by
  have hm : m ≠ 0 := by
    rintro rfl
    simp at h
  obtain ⟨j, hj⟩ := Finsupp.ne_iff.mp hm
  have hle : m j ≤ 1 := h ▸ Finsupp.le_degree j m
  have h1 : m j = 1 := by simp only [Finsupp.coe_zero, Pi.zero_apply] at hj; omega
  refine ⟨j, ?_⟩
  have hs : Finsupp.single j 1 ≤ m := by
    intro i
    by_cases hi : i = j
    · subst hi; simp [h1]
    · simp [Ne.symm hi]
  have e : m = (m - Finsupp.single j 1) + Finsupp.single j 1 := (tsub_add_cancel_of_le hs).symm
  have h0 : (m - Finsupp.single j 1).degree = 0 := by
    have := congrArg Finsupp.degree e
    rw [map_add, Finsupp.degree_single, h] at this
    omega
  rw [Finsupp.degree_eq_zero_iff] at h0
  rw [e, h0, zero_add]

namespace FGL

variable {R : Type*} [CommRing R]

section Filt

variable {σ : Type*} (𝔪 : Ideal R)

/-- **The coefficient filtration** `N_w = {f | coeff_m f ∈ 𝔪^{w − |m|}}`. -/
def coeffFilt (w : ℕ) : Ideal (MvPowerSeries σ R) where
  carrier := {f | ∀ m, coeff m f ∈ 𝔪 ^ (w - m.degree)}
  add_mem' {f g} hf hg m := by
    rw [Set.mem_setOf_eq] at hf hg
    rw [map_add]
    exact add_mem (hf m) (hg m)
  zero_mem' m := by simp
  smul_mem' c f hf m := by
    classical
    rw [smul_eq_mul, coeff_mul]
    refine Ideal.sum_mem _ fun x hx => Ideal.mul_mem_left _ _ ?_
    have hle : x.2.degree ≤ m.degree := by
      rw [← Finset.mem_antidiagonal.mp hx, map_add]
      omega
    exact Ideal.pow_le_pow_right (by omega) (hf x.2)

variable {𝔪}

theorem mem_coeffFilt {w : ℕ} {f : MvPowerSeries σ R} :
    f ∈ coeffFilt 𝔪 w ↔ ∀ m, coeff m f ∈ 𝔪 ^ (w - m.degree) := Iff.rfl

theorem coeffFilt_mul_le (a b : ℕ) :
    coeffFilt (σ := σ) 𝔪 a * coeffFilt 𝔪 b ≤ coeffFilt 𝔪 (a + b) := by
  classical
  rw [Ideal.mul_le]
  intro f hf g hg m
  rw [coeff_mul]
  refine Ideal.sum_mem _ fun x hx => ?_
  have hdeg : x.1.degree + x.2.degree = m.degree := by
    rw [← Finset.mem_antidiagonal.mp hx, map_add]
  have := Ideal.mul_mem_mul (hf x.1) (hg x.2)
  rw [← pow_add] at this
  exact Ideal.pow_le_pow_right (by omega) this

theorem coeffFilt_pow_le (v : ℕ) : coeffFilt (σ := σ) 𝔪 1 ^ v ≤ coeffFilt 𝔪 v := by
  induction v with
  | zero => simp only [pow_zero, Ideal.one_eq_top]; exact fun f _ m => by simp
  | succ v ih =>
    rw [pow_succ]
    exact (Ideal.mul_mono_left ih).trans (coeffFilt_mul_le v 1)

theorem coeffFilt_antitone {a b : ℕ} (h : a ≤ b) :
    coeffFilt (σ := σ) 𝔪 b ≤ coeffFilt 𝔪 a :=
  fun f hf m => Ideal.pow_le_pow_right (by omega) (hf m)

theorem X_mem_coeffFilt (s : σ) : (X s : MvPowerSeries σ R) ∈ coeffFilt 𝔪 1 := by
  classical
  intro m
  rw [coeff_X]
  split_ifs with h
  · subst h; simp
  · exact zero_mem _

theorem C_mem_coeffFilt {r : R} (hr : r ∈ 𝔪) : (C r : MvPowerSeries σ R) ∈ coeffFilt 𝔪 1 := by
  classical
  intro m
  rw [coeff_C]
  split_ifs with h
  · subst h; simpa using hr
  · exact zero_mem _

theorem span_X_le_coeffFilt :
    Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ≤ coeffFilt 𝔪 1 := by
  rw [Ideal.span_le]
  rintro _ ⟨s, rfl⟩
  exact X_mem_coeffFilt s

theorem pow_span_X_le_coeffFilt (n : ℕ) :
    Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ n ≤ coeffFilt 𝔪 n :=
  (Ideal.pow_right_mono span_X_le_coeffFilt n).trans (coeffFilt_pow_le n)

variable (σ 𝔪) in
/-- The ideal `𝔪 A + (T)` of `A = R[[T]]` (the maximal ideal if `𝔪` is maximal). -/
def maxPS : Ideal (MvPowerSeries σ R) :=
  Ideal.map (C (σ := σ) (R := R)) 𝔪 ⊔ Ideal.span (Set.range X)

theorem maxPS_le_coeffFilt : maxPS σ 𝔪 ≤ coeffFilt 𝔪 1 := by
  refine sup_le ?_ span_X_le_coeffFilt
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  exact C_mem_coeffFilt hr

theorem span_X_le_maxPS :
    Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ≤ maxPS σ 𝔪 := le_sup_right

theorem C_mem_maxPS {r : R} (hr : r ∈ 𝔪) : (C r : MvPowerSeries σ R) ∈ maxPS σ 𝔪 :=
  Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hr)

/-- **`⋂_w N_w = 0`** for `𝔪`-adically separated `R`. -/
theorem eq_zero_of_mem_coeffFilt [IsHausdorff 𝔪 R] {f : MvPowerSeries σ R}
    (hf : ∀ w, f ∈ coeffFilt 𝔪 w) : f = 0 := by
  ext m
  rw [map_zero]
  refine IsHausdorff.haus' (I := 𝔪) _ fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  have := hf (n + m.degree) m
  rwa [Nat.add_sub_cancel] at this

/-- **Elements of `(T)^n` have no monomials of degree `< n`.** -/
theorem coeff_eq_zero_of_mem_pow_span_X {n : ℕ} {f : MvPowerSeries σ R}
    (hf : f ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ n) {m : σ →₀ ℕ}
    (hm : m.degree < n) : coeff m f = 0 := by
  have := pow_span_X_le_coeffFilt (𝔪 := (⊥ : Ideal R)) n hf m
  obtain ⟨k, hk⟩ : ∃ k, n - m.degree = k + 1 := ⟨n - m.degree - 1, by omega⟩
  rwa [hk, pow_succ, Ideal.mul_bot, Ideal.mem_bot] at this

end Filt

/-! ### Linear parts -/

section Linear

variable {σ τ : Type*}

/-- The linear part `∑_s (∂f/∂T_s(0)) T_s`. -/
def linPS [Fintype σ] (f : MvPowerSeries σ R) : MvPowerSeries σ R :=
  ∑ s, C (coeff (Finsupp.single s 1) f) * X s

open Classical in
theorem coeff_linPS [Fintype σ] (f : MvPowerSeries σ R) (m : σ →₀ ℕ) :
    coeff m (linPS f) = ∑ s, if m = Finsupp.single s 1 then coeff (Finsupp.single s 1) f
      else 0 := by
  classical
  rw [linPS, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [coeff_C_mul, coeff_X]
  split_ifs <;> simp

theorem coeff_single_linPS [Fintype σ] (f : MvPowerSeries σ R) (s : σ) :
    coeff (Finsupp.single s 1) (linPS f) = coeff (Finsupp.single s 1) f := by
  classical
  rw [coeff_linPS, Finset.sum_eq_single s (fun t _ ht => if_neg fun h => ht ?_) (by simp),
    if_pos rfl]
  have := congrArg (fun m : σ →₀ ℕ => m t) h
  simp only [Finsupp.single_eq_same] at this
  by_contra hne
  rw [Finsupp.single_eq_of_ne hne] at this
  exact zero_ne_one this

/-- **`f − lin(f) ∈ (T)^2`** for `f` without constant term. -/
theorem sub_linPS_mem [Fintype σ] {f : MvPowerSeries σ R} (hf : constantCoeff f = 0) :
    f - linPS f ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ 2 := by
  classical
  refine AdicEval.mem_pow_span_X 2 _ fun m hm => ?_
  rw [map_sub]
  rcases Nat.lt_succ_iff.mp hm |>.lt_or_eq with h0 | h1
  · have hm0 : m = 0 := (Finsupp.degree_eq_zero_iff m).mp (by omega)
    subst hm0
    rw [coeff_zero_eq_constantCoeff_apply, hf, coeff_linPS, zero_sub, neg_eq_zero]
    refine Finset.sum_eq_zero fun j _ => if_neg fun h => ?_
    have := congrArg (fun m : σ →₀ ℕ => m j) h
    simp at this
  · obtain ⟨j0, rfl⟩ := Finsupp.eq_single_of_degree_eq_one m h1
    rw [coeff_single_linPS, sub_self]

/-- Substitution of a family without constant terms maps `(T_σ)` into `(T_τ)`. -/
theorem map_span_X_subst_le [Finite σ] [Finite τ] {g : σ → MvPowerSeries τ R}
    (hg : ∀ s, constantCoeff (g s) = 0) :
    Ideal.map (substAlgHom (hasSubst_of_constantCoeff_zero hg))
      (Ideal.span (Set.range (X : σ → MvPowerSeries σ R))) ≤
      Ideal.span (Set.range (X : τ → MvPowerSeries τ R)) := by
  rw [Ideal.map_span, Ideal.span_le]
  rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, coe_substAlgHom, subst_X (hasSubst_of_constantCoeff_zero hg)]
  have := AdicEval.mem_pow_span_X 1 (g s) fun m hm => by
    rw [(Finsupp.degree_eq_zero_iff m).mp (by omega), coeff_zero_eq_constantCoeff_apply, hg s]
  rwa [pow_one] at this

/-- **The linear part of `f(g)`** is the composite of the linear parts. -/
theorem coeff_single_subst [Fintype σ] [Finite τ] {f : MvPowerSeries σ R}
    (hf : constantCoeff f = 0) {g : σ → MvPowerSeries τ R} (hg : ∀ s, constantCoeff (g s) = 0)
    (t : τ) :
    coeff (Finsupp.single t 1) (f.subst g) =
      ∑ s, coeff (Finsupp.single s 1) f * coeff (Finsupp.single t 1) (g s) := by
  have hG := hasSubst_of_constantCoeff_zero hg
  have h2 : (substAlgHom hG) (f - linPS f) ∈
      Ideal.span (Set.range (X : τ → MvPowerSeries τ R)) ^ 2 := by
    have := Ideal.mem_map_of_mem (substAlgHom hG) (sub_linPS_mem hf)
    rw [Ideal.map_pow] at this
    exact Ideal.pow_right_mono (map_span_X_subst_le hg) 2 this
  have h0 := coeff_eq_zero_of_mem_pow_span_X h2 (m := Finsupp.single t 1)
    (by rw [Finsupp.degree_single]; omega)
  rw [map_sub, map_sub, sub_eq_zero, coe_substAlgHom] at h0
  rw [h0, linPS, ← coe_substAlgHom hG, map_sum, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_mul]
  have hX : (substAlgHom hG) (X s : MvPowerSeries σ R) = g s := by
    rw [coe_substAlgHom, subst_X hG]
  rw [hX]
  have : (substAlgHom hG) (C (coeff (Finsupp.single s 1) f)) =
      C (coeff (Finsupp.single s 1) f) := by
    have := (substAlgHom hG).commutes (coeff (Finsupp.single s 1) f)
    rwa [MvPowerSeries.algebraMap_apply, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply] at this
  rw [this, coeff_C_mul]

end Linear

/-! ### [Hong, Lemma 2.2.14] and `⋂_v J_v = 0` -/

section Layers

variable {d : ℕ} (F : FGL R d)

theorem coeff_single_X (i j : Fin d) :
    coeff (Finsupp.single j 1) (X i : MvPowerSeries (Fin d) R) = if i = j then 1 else 0 := by
  classical
  rw [coeff_X]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg, if_neg h]
    intro h'
    have := congrArg (fun m : Fin d →₀ ℕ => m j) h'
    rw [Finsupp.single_eq_same, Finsupp.single_apply, if_neg h] at this
    exact one_ne_zero this

theorem noConst_pairFam {τ : Type*} {f g : Fin d → MvPowerSeries τ R}
    (hf : ∀ j, constantCoeff (f j) = 0) (hg : ∀ j, constantCoeff (g j) = 0) :
    ∀ v, constantCoeff (pairFam f g v) = 0 := fun v => by
  unfold pairFam; split_ifs; exacts [hf _, hg _]

/-- The linear part of `Φ` is `T + U` ([Hong, Lemma 2.2.14, proof]). -/
theorem coeff_single_Φ (i : Fin d) (a : Fin 2) (j : Fin d) :
    coeff (Finsupp.single (a, j) 1) (F.Φ i) = if i = j then 1 else 0 := by
  have key : ∀ (g : Fin 2 × Fin d → MvPowerSeries (Fin d) R)
      (hg : ∀ v, constantCoeff (g v) = 0) (j : Fin d),
      coeff (Finsupp.single j 1) ((F.Φ i).subst g) =
        ∑ k, coeff (Finsupp.single ((0 : Fin 2), k) 1) (F.Φ i) *
            coeff (Finsupp.single j 1) (g (0, k)) +
          ∑ k, coeff (Finsupp.single ((1 : Fin 2), k) 1) (F.Φ i) *
            coeff (Finsupp.single j 1) (g (1, k)) := by
    intro g hg j
    rw [coeff_single_subst (F.constantCoeff_Φ i) hg, Fintype.sum_prod_type, Fin.sum_univ_two]
  have hX : ∀ j : Fin d, constantCoeff (X j : MvPowerSeries (Fin d) R) = 0 :=
    fun j => constantCoeff_X j
  have h0 : ∀ j : Fin d, constantCoeff (0 : MvPowerSeries (Fin d) R) = 0 := fun _ => map_zero _
  obtain rfl | rfl : a = 0 ∨ a = 1 := by fin_cases a <;> simp
  · have := key (pairFam (fun j => (X j : MvPowerSeries (Fin d) R)) 0) (noConst_pairFam hX h0) j
    rw [F.unit_right i, coeff_single_X] at this
    simp only [pairFam_zero, pairFam_one, coeff_single_X, mul_zero, mul_ite, mul_one,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    simpa using this.symm
  · have := key (pairFam 0 (fun j => (X j : MvPowerSeries (Fin d) R))) (noConst_pairFam h0 hX) j
    rw [F.unit_left i, coeff_single_X] at this
    simp only [pairFam_zero, pairFam_one, coeff_single_X, mul_zero, mul_ite, mul_one,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    simpa using this.symm

/-- **[Hong, Lemma 2.2.14]**: the linear part of `[n]_F` is `n T`. -/
theorem coeff_single_mulPS (n : ℕ) (i j : Fin d) :
    coeff (Finsupp.single j 1) (F.mulPS n i) = if i = j then (n : R) else 0 := by
  induction n generalizing i with
  | zero => simp [mulPS_zero]
  | succ n ih =>
    rw [mulPS_succ, addPS, coeff_single_subst (F.constantCoeff_Φ i)
      (noConst_pairFam (F.noConst_mulPS n) (fun j => constantCoeff_X j)),
      Fintype.sum_prod_type, Fin.sum_univ_two]
    simp only [coeff_single_Φ, pairFam_zero, pairFam_one, ih, coeff_single_X, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    split_ifs <;> push_cast <;> ring

/-- **[Hong, Lemma 2.2.14]**: `[n]_F(T) − nT ∈ (T)^2`. -/
theorem mulPS_sub_mem (n : ℕ) (i : Fin d) :
    F.mulPS n i - C (n : R) * X i ∈
      Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) R)) ^ 2 := by
  have hlin : linPS (F.mulPS n i) = C (n : R) * X i := by
    rw [linPS]
    simp only [coeff_single_mulPS, apply_ite C, map_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [← hlin]
  exact sub_linPS_mem (F.constantCoeff_mulPS n i)

variable (p : ℕ) {𝔪 : Ideal R}

theorem layerIdeal_zero : F.layerIdeal p 0 = Ideal.span (Set.range X) := by
  rw [layerIdeal, pow_zero, mulPS_one]

/-- `J_{v+1} ⊆ (𝔪A + I) J_v` if `p ∈ 𝔪`: `[p]_F(T) ∈ pT + (T)^2`. -/
theorem layerIdeal_succ_le_mul (hp : (p : R) ∈ 𝔪) (v : ℕ) :
    F.layerIdeal p (v + 1) ≤
      maxPS (Fin d) 𝔪 * F.layerIdeal p v + F.layerIdeal p v ^ 2 := by
  rw [show F.layerIdeal p (v + 1) = Ideal.span (Set.range (F.mulPS (p ^ (v + 1)))) from rfl,
    Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  have e : F.mulPS (p ^ (v + 1)) i =
      C (p : R) * F.mulPS (p ^ v) i + F.psiV p v (F.mulPS p i - C (p : R) * X i) := by
    rw [map_sub, map_mul, psiV_C, psiV_X, psiV_apply, mulPS_pow_succ]
    ring
  rw [SetLike.mem_coe, e]
  refine Submodule.add_mem_sup
    (Ideal.mul_mem_mul (C_mem_maxPS hp) (F.mulPS_mem_layerIdeal p v i)) ?_
  have := Ideal.mem_map_of_mem (F.psiV p v) (F.mulPS_sub_mem p i)
  rwa [Ideal.map_pow, map_span_X_psiV] at this

/-- **`J_v ⊆ (𝔪A + I)^{v+1}`** if `p ∈ 𝔪` ([Hong, Lemma 2.2.15, proof]). -/
theorem layerIdeal_le_pow (hp : (p : R) ∈ 𝔪) (v : ℕ) :
    F.layerIdeal p v ≤ maxPS (Fin d) 𝔪 ^ (v + 1) := by
  induction v with
  | zero => rw [layerIdeal_zero, zero_add, pow_one]; exact span_X_le_maxPS
  | succ v ih =>
    refine (F.layerIdeal_succ_le_mul p hp v).trans (sup_le ?_ ?_)
    · rw [pow_succ']
      exact Ideal.mul_mono_right ih
    · refine (Ideal.pow_right_mono ih 2).trans ?_
      rw [← pow_mul]
      exact Ideal.pow_le_pow_right (by nlinarith)

theorem layerIdeal_le_coeffFilt (hp : (p : R) ∈ 𝔪) (v : ℕ) :
    F.layerIdeal p v ≤ coeffFilt 𝔪 v :=
  (F.layerIdeal_le_pow p hp v).trans ((Ideal.pow_right_mono maxPS_le_coeffFilt _).trans
    ((coeffFilt_pow_le _).trans (coeffFilt_antitone (Nat.le_succ v))))

/-- **`⋂_v [p^v]_F(I) A = 0`** if `p ∈ 𝔪` and `R` is `𝔪`-adically separated: the map
`R[[T]] → lim_v A_v` is injective ([Hong, Lemma 2.2.15]). -/
theorem eq_zero_of_mem_layerIdeal [IsHausdorff 𝔪 R] (hp : (p : R) ∈ 𝔪)
    {f : MvPowerSeries (Fin d) R} (hf : ∀ v, f ∈ F.layerIdeal p v) : f = 0 :=
  eq_zero_of_mem_coeffFilt fun w => F.layerIdeal_le_coeffFilt p hp w (hf w)

end Layers


end FGL

end PadicHodge
