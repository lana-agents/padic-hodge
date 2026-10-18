/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.Layers

/-!
# Finiteness of the layers `A_v` of a `p`-divisible formal group law

[Hong, Def. 2.2.9 (2)]: a formal group law `F` over `R` is `p`-divisible if `[p]_F : A → A`
(`A = R[[t_1, …, t_d]]`, `f ↦ f([p]_F)`) makes `A` a free module of finite rank over itself. We
fix the rank to be `p^h` (`IsPDivisible F p h`; [Hong] deduces that the rank is a power of `p`
from [Hong, Prop. 1.5.10], which we do not formalise: the height is part of the datum).

* `FreeVia ψ n`: `A` is free of rank `n` over itself via `ψ : A → A`, with an explicit basis;
  `FreeVia.comp`: freeness in towers (rank `n m`);
* `psiV F p v`: `f ↦ f([p^v]_F)`, equal to `([p]_F)^v` (`psiV_succ`), free of rank `p^{hv}`
  (`freeVia_psiV`);
* **[Hong, Prop. 2.2.10, proof, (2.1)]**: `A_v = A/[p^v]_F(I) ≅ R ⊗_{A, [p^v]} A` is free of rank
  `p^{hv}` over `R` (`layerBasis`, `finrank_layer`): the images of an `A`-basis of `A` over
  `[p^v]_F(A)` form an `R`-basis of `A_v`.
-/

noncomputable section

open MvPowerSeries

namespace PadicHodge

namespace FGL

section FreeVia

variable {A : Type*} [CommRing A]

/-- `A` is free of rank `n` over itself via the ring endomorphism `ψ`. -/
def FreeVia (ψ : A →+* A) (n : ℕ) : Prop :=
  ∃ b : Fin n → A, Function.Bijective fun c : Fin n → A => ∑ i, ψ (c i) * b i

theorem freeVia_id : FreeVia (RingHom.id A) 1 :=
  ⟨fun _ => 1, ⟨fun c c' h => funext fun i => by
      simpa [Fin.eq_zero i] using h,
    fun y => ⟨fun _ => y, by simp⟩⟩⟩

/-- **Freeness in towers.** -/
theorem FreeVia.comp {φ ψ : A →+* A} {n m : ℕ} (hφ : FreeVia φ n) (hψ : FreeVia ψ m) :
    FreeVia (φ.comp ψ) (n * m) := by
  obtain ⟨b, hb⟩ := hφ
  obtain ⟨b', hb'⟩ := hψ
  let e : Fin n × Fin m ≃ Fin (n * m) := finProdFinEquiv
  refine ⟨fun k => φ (b' (e.symm k).2) * b (e.symm k).1, ?_⟩
  have h1 : Function.Bijective
      fun (c : Fin n → Fin m → A) (i : Fin n) => ∑ j, ψ (c i j) * b' j :=
    ⟨fun c c' h => funext fun i => hb'.1 (congrFun h i),
      fun y => ⟨fun i => (hb'.2 (y i)).choose, funext fun i => (hb'.2 (y i)).choose_spec⟩⟩
  let E : (Fin (n * m) → A) ≃ (Fin n → Fin m → A) :=
    (e.symm.arrowCongr (Equiv.refl A)).trans (Equiv.curry _ _ _)
  have hc := (hb.comp h1).comp E.bijective
  convert hc using 1
  funext c
  simp only [Function.comp_apply, E, Equiv.trans_apply, Equiv.arrowCongr_apply,
    Equiv.refl_apply, Equiv.curry_apply, Function.curry_apply, Equiv.symm_symm, map_sum,
    map_mul, RingHom.comp_apply, Finset.sum_mul]
  rw [← e.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Equiv.symm_apply_apply]
  ring

end FreeVia

variable {R : Type*} [CommRing R] {d : ℕ} (F : FGL R d) (p : ℕ)

/-- `f ↦ f([p^v]_F)`. -/
def psiV (v : ℕ) : MvPowerSeries (Fin d) R →ₐ[R] MvPowerSeries (Fin d) R :=
  substAlgHom (hasSubst_of_noConst (F.noConst_mulPS (p ^ v)))

theorem psiV_apply (v : ℕ) (f : MvPowerSeries (Fin d) R) :
    F.psiV p v f = f.subst (F.mulPS (p ^ v)) := by
  rw [psiV, coe_substAlgHom]

theorem psiV_X (v : ℕ) (j : Fin d) : F.psiV p v (X j) = F.mulPS (p ^ v) j := by
  rw [psiV_apply, subst_X (hasSubst_of_noConst (F.noConst_mulPS _))]

theorem psiV_C (v : ℕ) (r : R) : F.psiV p v (C r) = C r := by
  have := (F.psiV p v).commutes r
  rwa [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] at this

theorem psiV_zero : F.psiV p 0 = AlgHom.id R _ := by
  ext1 f
  rw [psiV_apply, pow_zero, mulPS_one, AlgHom.id_apply]
  exact congrFun subst_self f

theorem pSubst_apply (f : MvPowerSeries (Fin d) R) :
    F.pSubst p f = f.subst (F.mulPS p) := by
  rw [pSubst, coe_substAlgHom]

/-- `[p^{v+1}]^* = [p]^* ∘ [p^v]^*`. -/
theorem psiV_succ (v : ℕ) : F.psiV p (v + 1) = (F.pSubst p).comp (F.psiV p v) := by
  ext1 f
  rw [AlgHom.comp_apply, psiV_apply, psiV_apply, pSubst_apply,
    subst_comp_subst_apply (hasSubst_of_noConst (F.noConst_mulPS _))
      (hasSubst_of_noConst (F.noConst_mulPS _))]
  congr 1
  funext i
  rw [subst_mulPS, ← pow_succ]

/-- **`p`-divisible formal group law of height `h`** ([Hong, Def. 2.2.9 (2)], with the rank
`p^h` of `A` over `[p]_F(A)` fixed). -/
def IsPDivisible (h : ℕ) : Prop := FreeVia (F.pSubst p).toRingHom (p ^ h)

theorem freeVia_psiV {h : ℕ} (hF : F.IsPDivisible p h) (v : ℕ) :
    FreeVia (F.psiV p v).toRingHom (p ^ (h * v)) := by
  induction v with
  | zero =>
    rw [psiV_zero, mul_zero, pow_zero]
    exact freeVia_id
  | succ v ih =>
    rw [psiV_succ, mul_add, mul_one, pow_add, mul_comm]
    exact hF.comp ih

/-! ### The layers are free over `R` -/

theorem map_span_X_psiV (v : ℕ) :
    Ideal.map (F.psiV p v) (Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) R))) =
      F.layerIdeal p v := by
  rw [Ideal.map_span, layerIdeal, ← Set.range_comp]
  congr 2
  funext j
  exact F.psiV_X p v j

theorem psiV_sub_C_mem (v : ℕ) (c : MvPowerSeries (Fin d) R) :
    F.psiV p v c - C (constantCoeff c) ∈ F.layerIdeal p v := by
  have h1 : c - C (constantCoeff c) ∈
      Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) R)) :=
    mem_span_X (by simp)
  have h2 := Ideal.mem_map_of_mem (F.psiV p v) h1
  rw [map_span_X_psiV, map_sub] at h2
  rwa [psiV_C] at h2

/-- The `R`-linear map `(r_i) ↦ ∑ r_i b_i mod J_v`. -/
def layerComb (v : ℕ) {n : ℕ} (b : Fin n → MvPowerSeries (Fin d) R) :
    (Fin n → R) →ₗ[R] F.Layer p v :=
  Fintype.linearCombination R (fun i => Ideal.Quotient.mk (F.layerIdeal p v) (b i))

theorem layerComb_apply (v : ℕ) {n : ℕ} (b : Fin n → MvPowerSeries (Fin d) R) (c : Fin n → R) :
    F.layerComb p v b c =
      Ideal.Quotient.mk (F.layerIdeal p v) (∑ i, C (c i) * b i) := by
  rw [layerComb, Fintype.linearCombination_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, Algebra.smul_def,
    IsScalarTower.algebraMap_apply R (MvPowerSeries (Fin d) R) (F.Layer p v),
    Ideal.Quotient.algebraMap_eq, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply]

/-- **[Hong, Prop. 2.2.10, (2.1)]**: if `A` is free over itself via `[p^v]^*` with basis `b`,
then the images of the `b_i` form an `R`-basis of `A_v`. -/
theorem layerComb_bijective (v : ℕ) {n : ℕ} (b : Fin n → MvPowerSeries (Fin d) R)
    (hb : Function.Bijective fun c : Fin n → MvPowerSeries (Fin d) R =>
      ∑ i, F.psiV p v (c i) * b i) :
    Function.Bijective (F.layerComb p v b) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro r hr
    rw [layerComb_apply, Ideal.Quotient.eq_zero_iff_mem, layerIdeal] at hr
    obtain ⟨a, ha⟩ := (Ideal.mem_span_range_iff_exists_fun).mp hr
    choose c hc using fun k => hb.2 (a k)
    have e : ∑ i, F.psiV p v (C (r i)) * b i =
        ∑ i, F.psiV p v (∑ k, c k i * X k) * b i := by
      simp only [psiV_C, ← ha, ← hc, map_sum, map_mul, psiV_X, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
      ring
    have := congrFun (hb.1 e)
    funext i
    have hi := congrArg constantCoeff (this i)
    simpa [map_sum] using hi
  · intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨c, hc⟩ := hb.2 a
    refine ⟨fun i => constantCoeff (c i), ?_⟩
    rw [layerComb_apply, ← hc, Ideal.Quotient.eq, ← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [← sub_mul]
    refine Ideal.mul_mem_right _ _ ?_
    have := F.psiV_sub_C_mem p v (c i)
    rw [← neg_mem_iff, neg_sub]
    exact this

variable {F p}

/-- **An `R`-basis of `A_v`** for a `p`-divisible formal group law of height `h`. -/
def layerBasis {h : ℕ} (hF : F.IsPDivisible p h) (v : ℕ) :
    Module.Basis (Fin (p ^ (h * v))) R (F.Layer p v) :=
  Module.Basis.ofEquivFun
    (LinearEquiv.ofBijective _ (F.layerComb_bijective p v _
      (F.freeVia_psiV p hF v).choose_spec)).symm

theorem layer_free {h : ℕ} (hF : F.IsPDivisible p h) (v : ℕ) : Module.Free R (F.Layer p v) :=
  Module.Free.of_basis (layerBasis hF v)

theorem layer_finite {h : ℕ} (hF : F.IsPDivisible p h) (v : ℕ) :
    Module.Finite R (F.Layer p v) :=
  Module.Finite.of_basis (layerBasis hF v)

/-- **`A_v` has rank `p^{hv}`** ([Hong, Prop. 2.2.10, proof]). -/
theorem finrank_layer [Nontrivial R] {h : ℕ} (hF : F.IsPDivisible p h) (v : ℕ) :
    Module.finrank R (F.Layer p v) = p ^ (h * v) := by
  rw [Module.finrank_eq_card_basis (layerBasis hF v), Fintype.card_fin]

end FGL

end PadicHodge
