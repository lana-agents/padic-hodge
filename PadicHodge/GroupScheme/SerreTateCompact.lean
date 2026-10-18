/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.Zp
import PadicHodge.FormalGroup.FrobKernel
import PadicHodge.FormalGroup.LayerLimitBase
import Mathlib.NumberTheory.Padics.ProperSpace

/-!
# Power series over `ℤ_p` and limits of finite free `ℤ_p`-algebras

Tools for the essential surjectivity half of Serre–Tate ([Hong, Thm. 2.2.16]): for a family of
`ℤ_p`-algebra maps `e_v : ℤ_p[[X_σ]] → B_v` (`σ` finite) sending the variables to topologically
nilpotent elements,

* `coeffFilt_le_comap`: `e_v` is continuous for the coefficient filtration `N_w`
  (`FGL.coeffFilt`) and the `𝔪`-adic topology of `B_v` (as in `PDivFGL.coeffFilt_le_comap`);
* **compactness** (`ℤ_p[[X_σ]] = ℤ_p^{ℕ^σ}` is compact for the product topology, `ofPi`):
  `exists_forall_eq`: if every `e_v` hits `b_v` and `e_{v+1}(g) = b_{v+1} → e_v(g) = b_v`, then
  one `g` hits all `b_v` (Hong uses Chevalley's theorem [Mat87, Ex. 8.7] instead);
  `exists_ker_le_coeffFilt`: if `⋂_v ker e_v = 0` (decreasing), then `ker e_v ⊆ N_w` for
  `v ≫ w`;
* **reduction mod `𝔪`** (`eq_zero_of_forall_red`): if the `B_v` are `ℤ_p`-torsion free and the
  reductions of the kernels lie in `boxIdeal (N v)` with `N v` unbounded, then
  `⋂_v ker e_v = 0` (divide by the largest power of `p` dividing all coefficients);
* `map_coeffFilt_le`: algebra maps `R[[X_σ]] → R[[X_τ]]` with `X_i ↦ (X)` preserve `N_w`.
-/

noncomputable section

open MvPowerSeries IsLocalRing PadicHodge.AdicEval

namespace PadicHodge

namespace SerreTate

/-! ### Continuity of evaluation maps -/

section Cont

variable {R : Type*} [CommRing R] (𝔪 : Ideal R) {S : Type*} [CommRing S] [Algebra R S]
  {σ : Type*} [Finite σ]

omit [Finite σ] in
theorem C_eq_algebraMap (r : R) : (C r : MvPowerSeries σ R) = algebraMap R _ r := by
  rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

/-- **`N_w ⊆ e^{-1}(𝔪^k S)` for `w ≫ k`** if `e` sends the variables to topologically nilpotent
elements. -/
theorem coeffFilt_le_comap (e : MvPowerSeries σ R →ₐ[R] S) (he : ∀ i, TopNil 𝔪 (e (X i)))
    (k : ℕ) : ∃ w, FGL.coeffFilt (σ := σ) 𝔪 w ≤ Ideal.comap e ((𝔪.map (algebraMap R S)) ^ k) := by
  set K := Ideal.comap e (𝔪.map (algebraMap R S))
  have hrad : Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ≤ K.radical := by
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨N, hN⟩ := he j
    exact ⟨N, by rw [Ideal.mem_comap, map_pow]; exact hN⟩
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad
    (Submodule.fg_span (Set.finite_range _))
  have hKk : K ^ k ≤ Ideal.comap e ((𝔪.map (algebraMap R S)) ^ k) := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono (Ideal.map_comap_le) k
  refine ⟨N * k + k, fun f hf => ?_⟩
  have e1 := AdicEval.sub_truncTotal_mem (N * k) f
  rw [pow_mul] at e1
  have h1 : f - (truncTotal (N * k) f : MvPowerSeries σ R) ∈ _ :=
    hKk (Ideal.pow_right_mono hN k e1)
  have h2 : (truncTotal (N * k) f : MvPowerSeries σ R) ∈
      Ideal.comap e ((𝔪.map (algebraMap R S)) ^ k) := by
    have hc := MvPolynomial.coe_mem_map_C (J := 𝔪 ^ k) (truncTotal (N * k) f) fun m => by
      rw [coeff_truncTotal_eq_ite]
      split_ifs with hm
      · exact Ideal.pow_le_pow_right (by omega) (hf m)
      · exact zero_mem _
    have hle : Ideal.map (C (σ := σ) (R := R)) (𝔪 ^ k) ≤
        Ideal.comap e ((𝔪.map (algebraMap R S)) ^ k) := by
      rw [Ideal.map_le_iff_le_comap]
      intro s hs
      rw [Ideal.mem_comap, Ideal.mem_comap, C_eq_algebraMap, e.commutes, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hs
    exact hle hc
  have := add_mem h1 h2
  rwa [sub_add_cancel] at this

omit [Finite σ] in
theorem C_mem_coeffFilt_of_mem_pow {r : R} {j : ℕ} (hr : r ∈ 𝔪 ^ j) :
    (C r : MvPowerSeries σ R) ∈ FGL.coeffFilt 𝔪 j := by
  classical
  intro m
  rw [coeff_C]
  split_ifs with h
  · subst h; simpa using hr
  · exact zero_mem _

/-- **Algebra maps `R[[X_σ]] → R[[X_τ]]` with `X_i ↦ (X)` preserve the coefficient
filtration.** -/
theorem map_coeffFilt_le {τ : Type*} (ψ : MvPowerSeries σ R →ₐ[R] MvPowerSeries τ R)
    (hψ : ∀ i, ψ (X i) ∈ Ideal.span (Set.range (X : τ → MvPowerSeries τ R))) (c : ℕ) :
    (FGL.coeffFilt (σ := σ) 𝔪 c).map ψ ≤ FGL.coeffFilt 𝔪 c := by
  classical
  have hX : ∀ j, Ideal.map ψ (Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ j) ≤
      FGL.coeffFilt (σ := τ) 𝔪 j := by
    intro j
    rw [Ideal.map_pow, Ideal.map_span]
    refine (Ideal.pow_right_mono ?_ j).trans (FGL.pow_span_X_le_coeffFilt j)
    rw [Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact hψ i
  rw [Ideal.map_le_iff_le_comap]
  intro g hg
  rw [Ideal.mem_comap]
  have h1 : ψ (g - (truncTotal c g : MvPowerSeries σ R)) ∈ FGL.coeffFilt (σ := τ) 𝔪 c :=
    hX c (Ideal.mem_map_of_mem _ (AdicEval.sub_truncTotal_mem c g))
  have h2 : ψ (truncTotal c g : MvPowerSeries σ R) ∈ FGL.coeffFilt (σ := τ) 𝔪 c := by
    set q := truncTotal c g
    rw [q.as_sum, ← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_sum, map_sum]
    refine Ideal.sum_mem _ fun m _ => ?_
    rw [MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_monomial]
    have e : MvPowerSeries.monomial m (q.coeff m) =
        C (q.coeff m) * MvPowerSeries.monomial m 1 := by
      rw [← monomial_zero_eq_C_apply, monomial_mul_monomial, zero_add, mul_one]
    rw [e, map_mul, C_eq_algebraMap, ψ.commutes, ← C_eq_algebraMap]
    by_cases hm : m.degree < c
    · have hq : q.coeff m ∈ 𝔪 ^ (c - m.degree) := by
        rw [coeff_truncTotal _ hm]
        exact hg m
      have hmon : (MvPowerSeries.monomial m (1 : R)) ∈
          Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ m.degree := by
        refine AdicEval.mem_pow_span_X _ _ fun m' hm' => ?_
        rw [coeff_monomial, if_neg]
        rintro rfl
        exact lt_irrefl _ hm'
      have := FGL.coeffFilt_mul_le (c - m.degree) m.degree
        (Ideal.mul_mem_mul (C_mem_coeffFilt_of_mem_pow 𝔪 hq)
          (hX _ (Ideal.mem_map_of_mem ψ hmon)))
      rwa [Nat.sub_add_cancel hm.le] at this
    · rw [coeff_truncTotal_eq_zero _ (not_lt.mp hm), map_zero, zero_mul]
      exact zero_mem _
  have := add_mem h1 h2
  rwa [map_sub, sub_add_cancel] at this

end Cont

/-! ### Compactness of `ℤ_p[[X_σ]]` -/

section Compact

variable {p : ℕ} [hp : Fact p.Prime] {σ : Type*} [Fintype σ]

local notation "𝔪p" => maximalIdeal (ZpD p)

/-- The power series with coefficients `c`. -/
def ofPi (c : (σ →₀ ℕ) → ℤ_[p]) : MvPowerSeries σ (ZpD p) := c

/-- The coefficients of `g`, a point of the compact space `ℤ_p^{ℕ^σ}`. -/
def toPi (g : MvPowerSeries σ (ZpD p)) : (σ →₀ ℕ) → ℤ_[p] := g

omit [Fintype σ] in
theorem ofPi_toPi (g : MvPowerSeries σ (ZpD p)) : ofPi (toPi g) = g := rfl

omit [Fintype σ] in
theorem mem_pow_iff (r : ZpD p) (w : ℕ) :
    r ∈ 𝔪p ^ w ↔ ‖ZpD.val r‖ ≤ (p : ℝ) ^ (-(w : ℤ)) := by
  rw [ZpD.maximalIdeal_eq, Ideal.span_singleton_pow, PadicInt.norm_le_pow_iff_mem_span_pow]
  exact Iff.rfl

/-- The open neighbourhood `{c' | c'_m ≡ c_m mod p^w for m in the box}` of `c`. -/
def ballSet (c : (σ →₀ ℕ) → ℤ_[p]) (w : ℕ) : Set ((σ →₀ ℕ) → ℤ_[p]) :=
  {c' | ∀ M : σ → Fin w, ‖c' (boxExp M) - c (boxExp M)‖ ≤ (p : ℝ) ^ (-(w : ℤ))}

theorem isOpen_ballSet (c : (σ →₀ ℕ) → ℤ_[p]) (w : ℕ) : IsOpen (ballSet c w) := by
  have e : ballSet c w = ⋂ M : σ → Fin w, (fun c' : (σ →₀ ℕ) → ℤ_[p] => c' (boxExp M)) ⁻¹'
      Metric.closedBall (c (boxExp M)) ((p : ℝ) ^ (-(w : ℤ))) := by
    ext c'
    simp [ballSet, Metric.mem_closedBall, dist_eq_norm]
  rw [e]
  have hr : ((p : ℝ) ^ (-(w : ℤ))) ≠ 0 :=
    (zpow_pos (by exact_mod_cast hp.out.pos) _).ne'
  exact isOpen_iInter_of_finite fun M =>
    (IsUltrametricDist.isOpen_closedBall (c (boxExp M)) hr).preimage
      (continuous_apply (boxExp M))

theorem mem_ballSet (c : (σ →₀ ℕ) → ℤ_[p]) (w : ℕ) : c ∈ ballSet c w := fun M => by
  rw [sub_self, norm_zero]
  exact (zpow_pos (by exact_mod_cast hp.out.pos) _).le

theorem sub_mem_coeffFilt {c c' : (σ →₀ ℕ) → ℤ_[p]} {w : ℕ} (h : c' ∈ ballSet c w) :
    ofPi c' - ofPi c ∈ FGL.coeffFilt (σ := σ) 𝔪p w := by
  intro m
  by_cases hw : w ≤ m.degree
  · rw [Nat.sub_eq_zero_of_le hw, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  · let M : σ → Fin w := fun j => ⟨m j, lt_of_le_of_lt (Finsupp.le_degree j m) (by omega)⟩
    have hM : boxExp M = m := by
      ext j
      rfl
    have := h M
    rw [hM] at this
    refine Ideal.pow_le_pow_right (Nat.sub_le _ _) ?_
    rw [mem_pow_iff]
    exact this

end Compact

section Closed

variable {p : ℕ} [hp : Fact p.Prime] {σ : Type*} [Finite σ]

local notation "𝔪p" => maximalIdeal (ZpD p)

theorem isOpen_coeffFilt (w : ℕ) :
    IsOpen {c : (σ →₀ ℕ) → ℤ_[p] | ofPi c ∈ FGL.coeffFilt (σ := σ) 𝔪p w} := by
  letI := Fintype.ofFinite σ
  rw [isOpen_iff_forall_mem_open]
  intro c hc
  have hc0 : ofPi c ∈ FGL.coeffFilt (σ := σ) 𝔪p w := hc
  refine ⟨ballSet c w, fun c' hc' => ?_, isOpen_ballSet c w, mem_ballSet c w⟩
  have := add_mem (sub_mem_coeffFilt hc') hc0
  rw [sub_add_cancel] at this
  exact this

/-- **Fibres of continuous evaluation maps are closed.** -/
theorem isClosed_fibre {B : Type*} [CommRing B] [Algebra (ZpD p) B]
    [IsHausdorff ((𝔪p).map (algebraMap (ZpD p) B)) B] (e : MvPowerSeries σ (ZpD p) →ₐ[ZpD p] B)
    (he : ∀ i, TopNil 𝔪p (e (X i))) (b : B) :
    IsClosed {c : (σ →₀ ℕ) → ℤ_[p] | e (ofPi c) = b} := by
  letI := Fintype.ofFinite σ
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro c hc
  have hne : e (ofPi c) - b ≠ 0 := sub_ne_zero.mpr hc
  obtain ⟨k, hk⟩ : ∃ k, e (ofPi c) - b ∉ ((𝔪p).map (algebraMap (ZpD p) B)) ^ k := by
    by_contra h
    push Not at h
    refine hne (IsHausdorff.haus' (I := (𝔪p).map (algebraMap (ZpD p) B)) _ fun k => ?_)
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    exact h k
  obtain ⟨w, hw⟩ := coeffFilt_le_comap 𝔪p e he k
  refine ⟨ballSet c w, fun c' hc' heq => hk ?_, isOpen_ballSet c w, mem_ballSet c w⟩
  have h1 := hw (sub_mem_coeffFilt hc')
  rw [Ideal.mem_comap, map_sub] at h1
  change e (ofPi c') = b at heq
  rw [heq] at h1
  have := neg_mem h1
  rwa [neg_sub] at this

end Closed

section Limits

variable {p : ℕ} [hp : Fact p.Prime] {σ : Type*} [Finite σ]

local notation "𝔪p" => maximalIdeal (ZpD p)

/-- **Compactness**: compatible targets of continuous evaluation maps are hit by a single power
series. -/
theorem exists_forall_eq {B : ℕ → Type*} [∀ v, CommRing (B v)]
    [∀ v, Algebra (ZpD p) (B v)] [∀ v, IsHausdorff ((𝔪p).map (algebraMap (ZpD p) (B v))) (B v)]
    (e : ∀ v, MvPowerSeries σ (ZpD p) →ₐ[ZpD p] B v)
    (he : ∀ v i, TopNil 𝔪p (e v (X i))) (b : ∀ v, B v) (hsurj : ∀ v, ∃ g, e v g = b v)
    (hmono : ∀ v g, e (v + 1) g = b (v + 1) → e v g = b v) :
    ∃ g, ∀ v, e v g = b v := by
  let t : ℕ → Set ((σ →₀ ℕ) → ℤ_[p]) := fun v => {c | e v (ofPi c) = b v}
  have hcl : ∀ v, IsClosed (t v) := fun v => isClosed_fibre (e v) (he v) (b v)
  obtain ⟨c, hc⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t
    (fun v c hc => hmono v _ hc) (fun v => let ⟨g, hg⟩ := hsurj v; ⟨toPi g, hg⟩)
    (hcl 0).isCompact hcl
  exact ⟨ofPi c, fun v => Set.mem_iInter.mp hc v⟩

/-- **The kernels go to `0`**: if `⋂_v ker e_v = 0` (decreasing), then `ker e_v ⊆ N_w` for some
`v`. -/
theorem exists_ker_le_coeffFilt {B : ℕ → Type*} [∀ v, CommRing (B v)]
    [∀ v, Algebra (ZpD p) (B v)] [∀ v, IsHausdorff ((𝔪p).map (algebraMap (ZpD p) (B v))) (B v)]
    (e : ∀ v, MvPowerSeries σ (ZpD p) →ₐ[ZpD p] B v)
    (he : ∀ v i, TopNil 𝔪p (e v (X i))) (hmono : ∀ v g, e (v + 1) g = 0 → e v g = 0)
    (hinj : ∀ g, (∀ v, e v g = 0) → g = 0) (w : ℕ) :
    ∃ v, ∀ g, e v g = 0 → g ∈ FGL.coeffFilt 𝔪p w := by
  by_contra hcon
  push Not at hcon
  let t : ℕ → Set ((σ →₀ ℕ) → ℤ_[p]) := fun v =>
    {c | e v (ofPi c) = 0} ∩ {c | ofPi c ∈ FGL.coeffFilt (σ := σ) 𝔪p w}ᶜ
  have hcl : ∀ v, IsClosed (t v) := fun v =>
    (isClosed_fibre (e v) (he v) 0).inter (isOpen_coeffFilt w).isClosed_compl
  obtain ⟨c, hc⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t
    (fun v c hc => ⟨hmono v _ hc.1, hc.2⟩)
    (fun v => let ⟨g, hg, hg'⟩ := hcon v; ⟨toPi g, hg, hg'⟩) (hcl 0).isCompact hcl
  have h0 : ofPi c = 0 := hinj _ fun v => (Set.mem_iInter.mp hc v).1
  exact (Set.mem_iInter.mp hc 0).2 (by rw [Set.mem_setOf_eq, h0]; exact zero_mem _)

end Limits

/-! ### Reduction modulo `𝔪` -/

section Reduction

variable {p : ℕ} [hp : Fact p.Prime] {σ : Type*}

local notation "𝔪p" => maximalIdeal (ZpD p)

/-- `ℤ_p` is a domain. -/
theorem isDomain_zpD : IsDomain (ZpD p) := inferInstanceAs (IsDomain ℤ_[p])

attribute [local instance] isDomain_zpD

theorem p_ne_zero : (p : ZpD p) ≠ 0 := fun h => by
  have h' : (p : ℤ_[p]) = 0 := h
  exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) h'

/-- Free `ℤ_p`-modules are torsion free. -/
theorem eq_zero_of_smul_eq_zero {M : Type*} [AddCommGroup M] [Module (ZpD p) M]
    [Module.Free (ZpD p) M] {r : ZpD p} (hr : r ≠ 0) {x : M} (hx : r • x = 0) : x = 0 := by
  let b := Module.Free.chooseBasis (ZpD p) M
  refine b.repr.injective ?_
  ext i
  have := congrArg (fun y => b.repr y i) hx
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero,
    Pi.zero_apply] at this
  rw [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  exact (mul_eq_zero.mp this).resolve_left hr

variable {k : Type*} [Field k] [Algebra (ZpD p) k]
  {B : ℕ → Type*} [∀ v, CommRing (B v)] [∀ v, Algebra (ZpD p) (B v)]

/-- **Injectivity from the special fibre**: if the reduction of every element of `ker e_v` lies
in `boxIdeal (N v)` and `N` is unbounded, then `⋂_v ker e_v = 0` (for torsion free `B_v`). -/
theorem eq_zero_of_forall_red (hker : ∀ r, algebraMap (ZpD p) k r = 0 → r ∈ 𝔪p)
    (htf : ∀ v (r : ZpD p) (x : B v), r ≠ 0 → r • x = 0 → x = 0)
    (e : ∀ v, MvPowerSeries σ (ZpD p) →ₐ[ZpD p] B v) (N : ℕ → ℕ) (hN : ∀ n, ∃ v, n ≤ N v)
    (hred : ∀ v g, e v g = 0 → MvPowerSeries.map (algebraMap (ZpD p) k) g ∈ boxIdeal σ k (N v))
    {g : MvPowerSeries σ (ZpD p)} (hg : ∀ v, e v g = 0) : g = 0 := by
  by_contra hne
  obtain ⟨m0, hm0⟩ : ∃ m, coeff m g ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (MvPowerSeries.ext fun m => by rw [h m, map_zero])
  obtain ⟨n0, hn0⟩ : ∃ n, coeff m0 g ∉ 𝔪p ^ n := by
    by_contra h
    push Not at h
    refine hm0 (IsHausdorff.haus' (I := 𝔪p) _ fun n => ?_)
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    exact h n
  let P : ℕ → Prop := fun n => ∀ m, coeff m g ∈ 𝔪p ^ n
  have hP : ∀ n, P n → n < n0 := fun n hn => by
    by_contra h
    exact hn0 (Ideal.pow_le_pow_right (not_lt.mp h) (hn m0))
  have hP0 : P 0 := fun m => by rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
  classical
  set n := Nat.findGreatest P n0
  have hPn : P n := Nat.findGreatest_spec (P := P) (Nat.zero_le _) hP0
  have hdiv : ∀ m, ∃ c, coeff m g = (p : ZpD p) ^ n * c := by
    intro m
    have := hPn m
    rw [ZpD.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at this
    obtain ⟨c, hc⟩ := this
    exact ⟨c, by rw [← hc, mul_comm]⟩
  choose c hc using hdiv
  let g' : MvPowerSeries σ (ZpD p) := fun m => c m
  have hgg : g = ((p : ZpD p) ^ n) • g' := by
    ext m
    rw [coeff_smul, hc]
    rfl
  have hg' : ∀ v, e v g' = 0 := fun v =>
    htf v _ _ (pow_ne_zero _ p_ne_zero) (by rw [← map_smul, ← hgg, hg v])
  have hred' : ∀ m, c m ∈ 𝔪p := fun m => by
    obtain ⟨v, hv⟩ := hN (m.degree + 1)
    have := hred v g' (hg' v) m (fun j => lt_of_le_of_lt (Finsupp.le_degree j m) (by omega))
    rw [coeff_map] at this
    exact hker _ this
  have hP1 : P (n + 1) := fun m => by
    rw [hc, pow_succ]
    refine Ideal.mul_mem_mul ?_ (hred' m)
    rw [ZpD.maximalIdeal_eq, Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton_self _
  exact Nat.findGreatest_is_greatest (Nat.lt_succ_self n) (hP (n + 1) hP1).le hP1

end Reduction

end SerreTate

end PadicHodge
