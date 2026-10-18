/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.InvDeriv

/-!
# `R[[T_1, …, T_d]]/(T_1^N, …, T_d^N)` is free of rank `N^d`

For a commutative ring `R` and `J_N = (X_j^N)_j ⊆ R[[X_σ]]` (`σ` finite):

* `coeff_eq_zero_of_mem_spanXPow`: elements of `J_N` have no monomials `X^m` with all `m_j < N`;
* `truncBox`: the polynomial part `∑_{m_j < N} c_m X^m` of `f`; `f − truncBox f ∈ J_N`
  (`MvPowerSeries.mem_span_X_pow`);
* **`boxBasis`**: the monomials `X^m`, `m : σ → Fin N`, form an `R`-basis of `R[[X]]/J_N`;
  **`finrank_quot_spanXPow`**: its rank is `N^{#σ}`.

Combined with `FGL.mulPS_p_mem` (`[p]_F(T) ∈ J_p` in characteristic `p`), this computes the
order `p^d` of the Frobenius kernel `Spec k[[T]]/([p]_F(T), T^p) = Spec k[[T]]/J_p` of
`F[p] = Spec k[[T]]/([p]_F(T))` ([Hong, Cor. 1.5.11, Cor. 2.2.18], `frobKernel_finrank`).
-/

noncomputable section

open MvPowerSeries

namespace MvPowerSeries

variable {σ R : Type*} [CommRing R]

/-- The ideal `(X_j^N)_j`. -/
abbrev spanXPow (σ R : Type*) [CommRing R] (N : ℕ) : Ideal (MvPowerSeries σ R) :=
  Ideal.span (Set.range fun j => (X j : MvPowerSeries σ R) ^ N)

/-- Power series without monomials in the box `{m | ∀ j, m_j < N}`: an ideal. -/
def boxIdeal (σ R : Type*) [CommRing R] (N : ℕ) : Ideal (MvPowerSeries σ R) where
  carrier := {f | ∀ m : σ →₀ ℕ, (∀ j, m j < N) → coeff m f = 0}
  add_mem' := fun {f g} hf hg m hm => by rw [map_add, hf m hm, hg m hm, add_zero]
  zero_mem' := fun m _ => by rw [map_zero]
  smul_mem' := fun g {f} hf m hm => by
    classical
    rw [smul_eq_mul, coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.mem_antidiagonal] at hx
    rw [hf x.2 fun j => lt_of_le_of_lt (by rw [← hx]; exact Nat.le_add_left _ _) (hm j),
      mul_zero]

theorem spanXPow_le_boxIdeal (N : ℕ) : spanXPow σ R N ≤ boxIdeal σ R N := by
  classical
  rw [Ideal.span_le]
  rintro _ ⟨j, rfl⟩ m hm
  change coeff m ((X j : MvPowerSeries σ R) ^ N) = 0
  rw [X_pow_eq, coeff_monomial, if_neg]
  intro h
  have := hm j
  rw [h, Finsupp.single_eq_same] at this
  exact lt_irrefl _ this

theorem coeff_eq_zero_of_mem_spanXPow {N : ℕ} {f : MvPowerSeries σ R} (hf : f ∈ spanXPow σ R N)
    {m : σ →₀ ℕ} (hm : ∀ j, m j < N) : coeff m f = 0 :=
  spanXPow_le_boxIdeal N hf m hm

variable [Fintype σ]

/-- The exponent `m : σ → Fin N` as a finitely supported function. -/
def boxExp {N : ℕ} (m : σ → Fin N) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun j => (m j : ℕ)

@[simp] theorem boxExp_apply {N : ℕ} (m : σ → Fin N) (j : σ) : boxExp m j = m j := rfl

theorem boxExp_injective {N : ℕ} : Function.Injective (boxExp (σ := σ) (N := N)) := by
  intro m m' h
  funext j
  exact Fin.ext (by simpa using DFunLike.congr_fun h j)

/-- The linear combination `∑_m c_m X^m` over the box. -/
def boxComb [DecidableEq σ] (N : ℕ) : ((σ → Fin N) → R) →ₗ[R] MvPowerSeries σ R where
  toFun c := ∑ m, monomial (boxExp m) (c m)
  map_add' c c' := by simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' r c := by simp only [Pi.smul_apply, map_smul, RingHom.id_apply, Finset.smul_sum]

theorem coeff_boxComb [DecidableEq σ] {N : ℕ} (c : (σ → Fin N) → R) (m : σ → Fin N) :
    coeff (boxExp m) (boxComb N c) = c m := by
  classical
  change coeff (boxExp m) (∑ m', monomial (boxExp m') (c m')) = c m
  rw [map_sum]
  simp only [coeff_monomial, boxExp_injective.eq_iff, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]

theorem coeff_boxComb_of_not [DecidableEq σ] {N : ℕ} (c : (σ → Fin N) → R) {a : σ →₀ ℕ}
    (ha : ∀ m : σ → Fin N, a ≠ boxExp m) : coeff a (boxComb N c) = 0 := by
  classical
  change coeff a (∑ m', monomial (boxExp m') (c m')) = 0
  rw [map_sum]
  exact Finset.sum_eq_zero fun m _ => by rw [coeff_monomial, if_neg (ha m)]

theorem mem_box_iff {N : ℕ} (a : σ →₀ ℕ) : (∀ j, a j < N) ↔ ∃ m : σ → Fin N, a = boxExp m := by
  constructor
  · intro h
    exact ⟨fun j => ⟨a j, h j⟩, Finsupp.ext fun j => rfl⟩
  · rintro ⟨m, rfl⟩ j
    exact (m j).isLt

variable [LinearOrder σ]

/-- The `R`-linear map `c ↦ ∑ c_m X^m mod J_N`. -/
def boxQuot [DecidableEq σ] (N : ℕ) : ((σ → Fin N) → R) →ₗ[R] MvPowerSeries σ R ⧸ spanXPow σ R N :=
  (Ideal.Quotient.mkₐ R (spanXPow σ R N)).toLinearMap ∘ₗ boxComb N

theorem boxQuot_bijective [DecidableEq σ] (N : ℕ) :
    Function.Bijective (boxQuot (σ := σ) (R := R) N) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have hmem : boxComb N c ∈ spanXPow σ R N := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      exact hc
    funext m
    rw [← coeff_boxComb c m]
    exact coeff_eq_zero_of_mem_spanXPow hmem fun j => (m j).isLt
  · intro y
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨fun m => coeff (boxExp m) f, ?_⟩
    change Ideal.Quotient.mk _ (boxComb N _) = _
    rw [Ideal.Quotient.eq]
    refine mem_span_X_pow N _ fun a ha => ?_
    by_contra hlt
    push Not at hlt
    obtain ⟨m, rfl⟩ := (mem_box_iff a).mp hlt
    simp [coeff_boxComb] at ha

/-- **The monomials `X^m`, `m_j < N`, form an `R`-basis of `R[[X]]/(X_j^N)`.** -/
def boxBasis [DecidableEq σ] (N : ℕ) :
    Module.Basis (σ → Fin N) R (MvPowerSeries σ R ⧸ spanXPow σ R N) :=
  Module.Basis.ofEquivFun (LinearEquiv.ofBijective _ (boxQuot_bijective N)).symm

/-- **`R[[X]]/(X_j^N)` has rank `N^{#σ}`.** -/
theorem finrank_quot_spanXPow [Nontrivial R] (N : ℕ) :
    Module.finrank R (MvPowerSeries σ R ⧸ spanXPow σ R N) = N ^ Fintype.card σ := by
  classical
  rw [Module.finrank_eq_card_basis (boxBasis N), Fintype.card_fun, Fintype.card_fin]

end MvPowerSeries

namespace PadicHodge

namespace FGL

variable {k : Type*} [CommRing k] {d : ℕ} (F : FGL k d)

/-- `([p]_F(T)) ⊆ (T_j^p)` in characteristic `p`. -/
theorem layerIdeal_one_le (p : ℕ) [Fact p.Prime] [CharP k p] :
    F.layerIdeal p 1 ≤ MvPowerSeries.spanXPow (Fin d) k p := by
  rw [layerIdeal, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  simpa using F.mulPS_p_mem p i

/-- **The Frobenius kernel of `F[p]` has order `p^d`** ([Hong, Cor. 1.5.11, Cor. 2.2.18]): in
characteristic `p`, the closed subscheme `Spec k[[T]]/([p]_F(T), T_1^p, …, T_d^p)` of
`F[p] = Spec k[[T]]/([p]_F(T))` cut out by the `p`-th powers of the coordinates is
`Spec k[[T]]/(T^p)`, free of rank `p^d`. -/
theorem finrank_frobKernel [Nontrivial k] (p : ℕ) [Fact p.Prime] [CharP k p] :
    Module.finrank k (MvPowerSeries (Fin d) k ⧸
      (F.layerIdeal p 1 ⊔ MvPowerSeries.spanXPow (Fin d) k p)) = p ^ d := by
  rw [sup_eq_right.mpr (F.layerIdeal_one_le p), MvPowerSeries.finrank_quot_spanXPow,
    Fintype.card_fin]

end FGL

end PadicHodge

