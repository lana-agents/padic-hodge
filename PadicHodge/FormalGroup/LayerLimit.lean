/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.Filtration
import PadicHodge.FormalGroup.LayerHopf

/-!
# `R[[T]] ≅ lim_v A_v` ([Hong, Lemma 2.2.15])

Let `P` be a `p`-divisible formal group law over a complete local ring `R` with `p ∈ 𝔪_R`, and
`A_v = R[[T]]/[p^v]_F(I)`. Then the natural map `R[[T]] → lim_v A_v` is bijective:

* injective: `⋂_v J_v = 0` (`FGL.eq_zero_of_mem_layerIdeal`);
* surjective (`PDivFGL.exists_mk_eq`): lift a compatible family `(a_v)` to `g_v ∈ R[[T]]`; then
  `g_w − g_v ∈ J_v ⊆ N_v` (the coefficient filtration), so the coefficients converge in `R`; the
  limit `f` satisfies `f − g_v ∈ N_w + J_v` for all `w`, and `N_w ⊆ J_v + 𝔪^k A` for `w ≫ k`
  (`coeffFilt_le_comap`: the images of the `t_j` in `A_v / 𝔪 A_v` are nilpotent), so
  `f ≡ g_v` modulo `⋂_k 𝔪^k A_v = 0` (`A_v` is finite free over `R`).

The argument follows [Hong, Lemma 2.2.15] but uses the coefficient filtration instead of the
`(𝔪, T)`-adic topology, so that no noetherianity of `R` or `R[[T]]` is needed.
-/

noncomputable section

open MvPowerSeries IsLocalRing PadicHodge.AdicEval

namespace PadicHodge

/-- A polynomial with coefficients in `J` lies in `J · R[[T]]`. -/
theorem MvPolynomial.coe_mem_map_C {R σ : Type*} [CommRing R] {J : Ideal R}
    (q : MvPolynomial σ R) (hq : ∀ m, q.coeff m ∈ J) :
    (q : MvPowerSeries σ R) ∈ Ideal.map (MvPowerSeries.C (σ := σ) (R := R)) J := by
  classical
  rw [q.as_sum, ← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_sum]
  refine Ideal.sum_mem _ fun m _ => ?_
  rw [MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_monomial]
  have : MvPowerSeries.monomial m (q.coeff m) =
      MvPowerSeries.C (q.coeff m) * MvPowerSeries.monomial m 1 := by
    rw [← monomial_zero_eq_C_apply, monomial_mul_monomial, zero_add, mul_one]
  rw [this]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hq m))

namespace PDivFGL

universe u

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
  {d p : ℕ} [hp : Fact p.Prime] (P : PDivFGL R d p)

attribute [local instance] isAdicComplete_free

local notation "𝔪R" => maximalIdeal R

omit [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] hp in
/-- `mk_v ∘ C = algebraMap R A_v`. -/
theorem mk_C (v : ℕ) (r : R) :
    Ideal.Quotient.mk (P.F.layerIdeal p v) (C r) = algebraMap R (P.A v) r := by
  rw [IsScalarTower.algebraMap_apply R (MvPowerSeries (Fin d) R) (P.A v),
    Ideal.Quotient.algebraMap_eq, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply]

omit [IsAdicComplete (maximalIdeal R) R] in
/-- **`N_w ⊆ J_v + 𝔪^k A` for `w ≫ k`**: the coefficient filtration is finer than the
`𝔪`-adic topology of `A_v`. -/
theorem coeffFilt_le_comap (v k : ℕ) : ∃ w, FGL.coeffFilt (σ := Fin d) 𝔪R w ≤
    Ideal.comap (Ideal.Quotient.mk (P.F.layerIdeal p v))
      ((𝔪R).map (algebraMap R (P.A v)) ^ k) := by
  set K := Ideal.comap (Ideal.Quotient.mk (P.F.layerIdeal p v))
    ((𝔪R).map (algebraMap R (P.A v)))
  have hrad : Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) R)) ≤ K.radical := by
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨N, hN⟩ := P.tnf_t v j
    exact ⟨N, by rw [Ideal.mem_comap, map_pow]; exact hN⟩
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad
    (Submodule.fg_span (Set.finite_range _))
  have hKk : K ^ k ≤ Ideal.comap (Ideal.Quotient.mk (P.F.layerIdeal p v))
      ((𝔪R).map (algebraMap R (P.A v)) ^ k) := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono (Ideal.map_comap_le) k
  refine ⟨N * k + k, fun f hf => ?_⟩
  have e := AdicEval.sub_truncTotal_mem (N * k) f
  rw [pow_mul] at e
  have h1 : f - (truncTotal (N * k) f : MvPowerSeries (Fin d) R) ∈ _ :=
    hKk (Ideal.pow_right_mono hN k e)
  have h2 : (truncTotal (N * k) f : MvPowerSeries (Fin d) R) ∈ Ideal.comap
      (Ideal.Quotient.mk (P.F.layerIdeal p v)) ((𝔪R).map (algebraMap R (P.A v)) ^ k) := by
    have hc := MvPolynomial.coe_mem_map_C (J := 𝔪R ^ k) (truncTotal (N * k) f) fun m => by
      rw [coeff_truncTotal_eq_ite]
      split_ifs with hm
      · exact Ideal.pow_le_pow_right (by omega) (hf m)
      · exact zero_mem _
    have := Ideal.mem_map_of_mem (Ideal.Quotient.mk (P.F.layerIdeal p v)) hc
    rw [Ideal.map_map] at this
    have hc' : (Ideal.Quotient.mk (P.F.layerIdeal p v)).comp C = algebraMap R (P.A v) := by
      ext r; exact P.mk_C v r
    rw [hc', Ideal.map_pow] at this
    exact this
  have := add_mem h1 h2
  rwa [sub_add_cancel] at this

/-- **The map `R[[T]] → lim_v A_v` is surjective** ([Hong, Lemma 2.2.15]). -/
theorem exists_mk_eq (hpm : (p : R) ∈ 𝔪R) (a : ∀ v, P.A v)
    (ha : ∀ v, P.F.layerIncl p v (a (v + 1)) = a v) :
    ∃ f : MvPowerSeries (Fin d) R, ∀ v, Ideal.Quotient.mk (P.F.layerIdeal p v) f = a v := by
  choose g hg using fun v => Ideal.Quotient.mk_surjective (I := P.F.layerIdeal p v) (a v)
  -- `g_w − g_v ∈ J_v`
  have hJ : ∀ v n, g (v + n) - g v ∈ P.F.layerIdeal p v := by
    intro v n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 : g (v + n + 1) - g (v + n) ∈ P.F.layerIdeal p (v + n) := by
        rw [← Ideal.Quotient.eq, hg, ← ha, ← hg, FGL.layerIncl, Ideal.Quotient.factorₐ_apply_mk]
      have h2 : P.F.layerIdeal p (v + n) ≤ P.F.layerIdeal p v := by
        clear ih h1
        induction n with
        | zero => exact le_rfl
        | succ n ihn => exact (P.F.layerIdeal_succ_le p (v + n)).trans ihn
      have := add_mem (h2 h1) ih
      rw [sub_add_sub_cancel] at this
      rwa [← add_assoc]
  have hN : ∀ v n, g (v + n) - g v ∈ FGL.coeffFilt (σ := Fin d) 𝔪R v :=
    fun v n => P.F.layerIdeal_le_coeffFilt p hpm v (hJ v n)
  -- the limit coefficients
  have hlim : ∀ m : Fin d →₀ ℕ, ∃ L : R, ∀ k,
      coeff m (g (k + m.degree)) - L ∈ 𝔪R ^ k := by
    intro m
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := 𝔪R) (fun k => coeff m (g (k + m.degree)))
      (fun {k l} hkl => by
        rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
        obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hkl
        have := hN (k + m.degree) n m
        rw [show k + n + m.degree = k + m.degree + n by ring, ← neg_sub, ← map_sub]
        refine neg_mem ?_
        simpa using this)
    refine ⟨L, fun k => ?_⟩
    have := hL k
    rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
  choose L hL using hlim
  let f : MvPowerSeries (Fin d) R := fun m => L m
  have hf : ∀ v, f - g v ∈ FGL.coeffFilt (σ := Fin d) 𝔪R v := by
    intro v m
    by_cases hv : v ≤ m.degree
    · rw [Nat.sub_eq_zero_of_le hv, pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
    · obtain ⟨k, rfl⟩ : ∃ k, v = k + m.degree := ⟨v - m.degree, by omega⟩
      rw [Nat.add_sub_cancel, map_sub, ← neg_sub]
      exact neg_mem (hL m k)
  refine ⟨f, fun v => ?_⟩
  rw [← hg, ← sub_eq_zero, ← map_sub]
  refine IsHausdorff.haus' (I := (𝔪R).map (algebraMap R (P.A v))) _ fun k => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  obtain ⟨w, hw⟩ := P.coeffFilt_le_comap v k
  have h1 : f - g (v + w) ∈ FGL.coeffFilt (σ := Fin d) 𝔪R w :=
    FGL.coeffFilt_antitone (by omega) (hf (v + w))
  have h2 := hw h1
  rw [Ideal.mem_comap] at h2
  have h3 : Ideal.Quotient.mk (P.F.layerIdeal p v) (g (v + w) - g v) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (hJ v w)
  rw [← sub_add_sub_cancel f (g (v + w)) (g v), map_add, h3, add_zero]
  exact h2

end PDivFGL

end PadicHodge
