/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.SerreTateHom

/-!
# `S[[T]] ≅ lim_v S ⊗_R A_v` for complete `R`-algebras `S`

Let `P` be a `p`-divisible formal group law over a complete local ring `R` with `p ∈ 𝔪_R`, and
let `S` be an `R`-algebra which is complete for `𝔞 = 𝔪_R S` (e.g. `S = O_{ℂ_p}` over `ℤ_p`).
The base change `S ⊗_R A_v` of the layers is the coordinate ring of `F[p^v]_S`, and

* `evB v : S[[T]] → S ⊗_R A_v`, `T ↦ 1 ⊗ t` (`t` is topologically nilpotent), is surjective
  (`evB_surjective`) and compatible with the closed immersions (`map_evB_succ`);
* **`S[[T]] → lim_v S ⊗_R A_v` is bijective** (`eq_zero_of_evB`, `exists_evB_eq`): this is
  [Hong, Lemma 2.2.15] for the base change `F_S`, without assuming that `F_S` is
  `p`-divisible over `S` (only the layers over `R` are used).

Injectivity: comparing `S[[T]] → S ⊗ A_v → S[[T]]/K_v` (`K_v = J_v S[[T]]`) with the quotient
map shows `ker(evB v) ⊆ K_v + (T)^D` for all `D` (`mem_sup_pow_of_comp_eq_mk`), and
`K_v ⊆ N_v` (coefficient filtration). Surjectivity: as in `LayerLimit.lean`.
This is the input for identifying `T_p(G^∨)` with formal homomorphisms `F_{O_C} → Ĝ_m`
([Hong, Prop. 3.4.9, proof, (3.7)]).
-/

noncomputable section

open MvPowerSeries IsLocalRing PadicHodge.AdicEval TensorProduct

namespace PadicHodge

/-- **The kernel of a map `S[[T]] → Q` into `S[[T]]/K` sending `T ↦ T` lies in `K + (T)^D`.** -/
theorem MvPowerSeries.mem_sup_pow_of_comp_eq_mk {S σ : Type*} [CommRing S] [Finite σ]
    {K : Ideal (MvPowerSeries σ S)} (ψ : MvPowerSeries σ S →ₐ[S] MvPowerSeries σ S ⧸ K)
    (hψ : ∀ x, ψ (X x) = Ideal.Quotient.mk K (X x)) {g : MvPowerSeries σ S} (hg : ψ g = 0)
    (D : ℕ) : g ∈ K ⊔ Ideal.span (Set.range X) ^ D := by
  set φ2 := Ideal.Quotient.mkₐ S K
  have hpoly : ∀ q : MvPolynomial σ S, ψ q = φ2 q := by
    intro q
    have : ψ.toRingHom.comp MvPolynomial.coeToMvPowerSeries.ringHom =
        φ2.toRingHom.comp MvPolynomial.coeToMvPowerSeries.ringHom := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) fun x => ?_
      · simp only [RingHom.comp_apply, MvPolynomial.coeToMvPowerSeries.ringHom_apply,
          MvPolynomial.coe_C]
        have e : (C r : MvPowerSeries σ S) = algebraMap S (MvPowerSeries σ S) r := by
          rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
        rw [e]
        exact (ψ.commutes r).trans (φ2.commutes r).symm
      · simp only [RingHom.comp_apply, MvPolynomial.coeToMvPowerSeries.ringHom_apply,
          MvPolynomial.coe_X]
        exact hψ x
    exact congrArg (fun φ => φ q) this
  have hI : Ideal.map ψ (Ideal.span (Set.range (X : σ → MvPowerSeries σ S)) ^ D) =
      Ideal.map φ2 (Ideal.span (Set.range (X : σ → MvPowerSeries σ S)) ^ D) := by
    rw [Ideal.map_pow, Ideal.map_pow, Ideal.map_span, Ideal.map_span, ← Set.range_comp,
      ← Set.range_comp]
    congr 3
    funext x
    exact hψ x
  have hr := AdicEval.sub_truncTotal_mem D g
  have h1 := Ideal.mem_map_of_mem ψ hr
  rw [hI] at h1
  have h2 := Ideal.mem_map_of_mem φ2 hr
  rw [map_sub, hg, hpoly, zero_sub, neg_mem_iff] at h1
  have h3 := sub_mem h2 (neg_mem h1)
  rw [map_sub, sub_neg_eq_add, sub_add_cancel] at h3
  obtain ⟨x, hx, hxg⟩ := (Ideal.mem_map_iff_of_surjective φ2
    (Ideal.Quotient.mkₐ_surjective S K)).mp h3
  have hgx : g - x ∈ K := by
    rw [← Ideal.Quotient.eq]
    exact hxg.symm
  have := Submodule.add_mem_sup hgx hx
  rwa [sub_add_cancel] at this

theorem Ideal.map_map_algebraMap {R S B : Type*} [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] [Algebra S B] [IsScalarTower R S B] (I : Ideal R) :
    (I.map (algebraMap R S)).map (algebraMap S B) = I.map (algebraMap R B) := by
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]

namespace PDivFGL

universe u

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
  {d p : ℕ} [hp : Fact p.Prime] (P : PDivFGL R d p)
  (S : Type*) [CommRing S] [Algebra R S]
  [IsAdicComplete ((maximalIdeal R).map (algebraMap R S)) S]

attribute [local instance] isAdicComplete_free

local notation "𝔪R" => maximalIdeal R

instance isAdicComplete_baseChange (v : ℕ) :
    IsAdicComplete (((𝔪R).map (algebraMap R S)).map (algebraMap S (S ⊗[R] P.A v)))
      (S ⊗[R] P.A v) :=
  isAdicComplete_of_free _ _

instance isHausdorff_baseChange_R (v : ℕ) :
    IsHausdorff ((𝔪R).map (algebraMap R (S ⊗[R] P.A v))) (S ⊗[R] P.A v) := by
  rw [← Ideal.map_map_algebraMap (S := S)]
  infer_instance

omit [IsAdicComplete (maximalIdeal R) R]
  [IsAdicComplete ((maximalIdeal R).map (algebraMap R S)) S] in
/-- `1 ⊗ t_j` is topologically nilpotent in `S ⊗_R A_v`. -/
theorem tnfB (v : ℕ) (j : Fin d) :
    TopNil ((𝔪R).map (algebraMap R S)) ((1 : S) ⊗ₜ[R] P.t v j) := by
  obtain ⟨N, hN⟩ := (P.tnf_t v j).map (Algebra.TensorProduct.includeRight (R := R) (A := S)
    (B := P.A v))
  refine ⟨N, ?_⟩
  rw [Ideal.map_map_algebraMap]
  simpa using hN

/-- `S[[T]] → S ⊗_R A_v`, `T ↦ 1 ⊗ t`. -/
def evB (v : ℕ) : MvPowerSeries (Fin d) S →ₐ[S] S ⊗[R] P.A v :=
  evalT (𝔪 := (𝔪R).map (algebraMap R S)) (fun j => (1 : S) ⊗ₜ[R] P.t v j) (P.tnfB S v)

omit [IsAdicComplete (maximalIdeal R) R] in
theorem evB_X (v : ℕ) (j : Fin d) : P.evB S v (X j) = (1 : S) ⊗ₜ[R] P.t v j := by
  rw [evB, evalT_X]

omit [IsAdicComplete (maximalIdeal R) R] hp in
/-- `S`-algebra maps `S[[T]] → S ⊗ A_v` are determined by the images of the `T_j`. -/
theorem algHom_ext_B (v : ℕ) {φ ψ : MvPowerSeries (Fin d) S →ₐ[S] S ⊗[R] P.A v}
    (hφ : ∀ j, TopNil ((𝔪R).map (algebraMap R S)) (φ (X j))) (h : ∀ j, φ (X j) = ψ (X j)) :
    φ = ψ :=
  algHom_ext_topNil (𝔪 := (𝔪R).map (algebraMap R S)) hφ h

omit [IsAdicComplete (maximalIdeal R) R] in
/-- `evB v (f) = 1 ⊗ (f mod J_v)` for `f ∈ R[[T]]`. -/
theorem evB_map (v : ℕ) (f : MvPowerSeries (Fin d) R) :
    P.evB S v (MvPowerSeries.map (algebraMap R S) f) =
      (1 : S) ⊗ₜ[R] Ideal.Quotient.mk (P.F.layerIdeal p v) f := by
  have key : ((P.evB S v).restrictScalars R).comp (mapAlgHom (Algebra.ofId R S)) =
      (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := P.A v)).comp
        (Ideal.Quotient.mkₐ R (P.F.layerIdeal p v)) := by
    refine algHom_ext_topNil (𝔪 := 𝔪R) (fun j => ?_) fun j => ?_
    · simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, mapAlgHom_apply, map_X]
      rw [evB_X]
      obtain ⟨N, hN⟩ := P.tnfB S v j
      exact ⟨N, by rwa [Ideal.map_map_algebraMap] at hN⟩
    · simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, mapAlgHom_apply, map_X,
        evB_X, Algebra.TensorProduct.includeRight_apply, Ideal.Quotient.mkₐ_eq_mk]
      rfl
  exact congrArg (fun φ => φ f) key

omit [IsAdicComplete (maximalIdeal R) R] in
theorem evB_C (v : ℕ) (s : S) : P.evB S v (C s) = algebraMap S (S ⊗[R] P.A v) s := by
  have e : (C s : MvPowerSeries (Fin d) S) = algebraMap S (MvPowerSeries (Fin d) S) s := by
    rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  rw [e, AlgHom.commutes]

omit [IsAdicComplete (maximalIdeal R) R] in
theorem evB_surjective (v : ℕ) : Function.Surjective (P.evB S v) := by
  intro y
  induction y with
  | zero => exact ⟨0, map_zero _⟩
  | tmul s a =>
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
    refine ⟨C s * MvPowerSeries.map (algebraMap R S) f, ?_⟩
    rw [map_mul, evB_C, evB_map, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  | add x y hx hy =>
    obtain ⟨f, rfl⟩ := hx
    obtain ⟨g, rfl⟩ := hy
    exact ⟨f + g, map_add _ _ _⟩

/-- The transition maps `S ⊗ A_{v+1} ↠ S ⊗ A_v`. -/
def inclB (v : ℕ) : S ⊗[R] P.A (v + 1) →ₐ[S] S ⊗[R] P.A v :=
  Algebra.TensorProduct.map (AlgHom.id S S) (P.F.layerIncl p v)

omit [IsAdicComplete (maximalIdeal R) R] in
theorem map_evB_succ (v : ℕ) :
    (P.inclB S v).comp (P.evB S (v + 1)) = P.evB S v := by
  refine P.algHom_ext_B S v (fun j => ?_) fun j => ?_
  · rw [AlgHom.comp_apply, evB_X, inclB, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    have := P.tnfB S v j
    rwa [← P.layerIncl_t v j] at this
  · rw [AlgHom.comp_apply, evB_X, evB_X, inclB, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      P.layerIncl_t v j]

/-! ### Injectivity -/

/-- `K_v = J_v S[[T]]`. -/
def idealB (v : ℕ) : Ideal (MvPowerSeries (Fin d) S) :=
  Ideal.map (MvPowerSeries.map (algebraMap R S)) (P.F.layerIdeal p v)

/-- `A_v → S[[T]]/K_v`. -/
def toQuotB (v : ℕ) : P.A v →ₐ[R] MvPowerSeries (Fin d) S ⧸ P.idealB S v :=
  P.liftL v (((Ideal.Quotient.mkₐ S (P.idealB S v)).restrictScalars R).comp
      (mapAlgHom (Algebra.ofId R S))) fun j => by
    rw [AlgHom.comp_apply, AlgHom.restrictScalars_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem, mapAlgHom_apply]
    exact Ideal.mem_map_of_mem _ (P.F.mulPS_mem_layerIdeal p v j)

/-- `S ⊗ A_v → S[[T]]/K_v`. -/
def quotB (v : ℕ) : S ⊗[R] P.A v →ₐ[S] MvPowerSeries (Fin d) S ⧸ P.idealB S v :=
  Algebra.TensorProduct.lift (Algebra.ofId S _) (P.toQuotB S v) fun _ _ => Commute.all _ _

omit [IsAdicComplete (maximalIdeal R) R] in
theorem quotB_evB_X (v : ℕ) (j : Fin d) :
    P.quotB S v (P.evB S v (X j)) = Ideal.Quotient.mk (P.idealB S v) (X j) := by
  rw [evB_X, quotB, Algebra.TensorProduct.lift_tmul, map_one, one_mul, toQuotB, t, liftL_mk,
    AlgHom.comp_apply, AlgHom.restrictScalars_apply, mapAlgHom_apply, map_X]
  rfl

omit [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] hp
  [IsAdicComplete ((maximalIdeal R).map (algebraMap R S)) S] in
/-- Change of coefficients preserves the coefficient filtration. -/
theorem map_mem_coeffFilt {σ : Type*} {𝔪 : Ideal R} {w : ℕ} {f : MvPowerSeries σ R}
    (hf : f ∈ FGL.coeffFilt 𝔪 w) :
    MvPowerSeries.map (algebraMap R S) f ∈ FGL.coeffFilt (𝔪.map (algebraMap R S)) w := by
  intro m
  rw [coeff_map, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ (hf m)

omit [IsAdicComplete (maximalIdeal R) R] hp
  [IsAdicComplete ((maximalIdeal R).map (algebraMap R S)) S] in
theorem idealB_le_coeffFilt (hpm : (p : R) ∈ 𝔪R) (v : ℕ) :
    P.idealB S v ≤ FGL.coeffFilt ((𝔪R).map (algebraMap R S)) v := by
  rw [idealB, Ideal.map_le_iff_le_comap]
  intro f hf
  exact map_mem_coeffFilt S (P.F.layerIdeal_le_coeffFilt p hpm v hf)

omit [IsAdicComplete (maximalIdeal R) R] in
theorem ker_evB_le (hpm : (p : R) ∈ 𝔪R) (v : ℕ) {g : MvPowerSeries (Fin d) S}
    (hg : P.evB S v g = 0) : g ∈ FGL.coeffFilt ((𝔪R).map (algebraMap R S)) v := by
  have := MvPowerSeries.mem_sup_pow_of_comp_eq_mk ((P.quotB S v).comp (P.evB S v))
    (fun j => P.quotB_evB_X S v j) (g := g) (by rw [AlgHom.comp_apply, hg, map_zero]) v
  exact sup_le (P.idealB_le_coeffFilt S hpm v) (FGL.pow_span_X_le_coeffFilt v) this

omit [IsAdicComplete (maximalIdeal R) R] in
/-- **`S[[T]] → lim_v S ⊗_R A_v` is injective.** -/
theorem eq_zero_of_evB (hpm : (p : R) ∈ 𝔪R) {g : MvPowerSeries (Fin d) S}
    (hg : ∀ v, P.evB S v g = 0) : g = 0 :=
  FGL.eq_zero_of_mem_coeffFilt fun v => P.ker_evB_le S hpm v (hg v)

/-! ### Surjectivity -/

omit [IsAdicComplete (maximalIdeal R) R] in
/-- `N_w ⊆ evB_v^{-1}(𝔞^k (S ⊗ A_v))` for `w ≫ k`. -/
theorem coeffFilt_le_comap_evB (v k : ℕ) : ∃ w,
    FGL.coeffFilt (σ := Fin d) ((𝔪R).map (algebraMap R S)) w ≤
      Ideal.comap (P.evB S v)
        ((((𝔪R).map (algebraMap R S)).map (algebraMap S (S ⊗[R] P.A v))) ^ k) := by
  set 𝔞 := (𝔪R).map (algebraMap R S)
  set K := Ideal.comap (P.evB S v) (𝔞.map (algebraMap S (S ⊗[R] P.A v)))
  have hrad : Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) S)) ≤ K.radical := by
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨N, hN⟩ := P.tnfB S v j
    exact ⟨N, by rw [Ideal.mem_comap, map_pow, evB_X]; exact hN⟩
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad
    (Submodule.fg_span (Set.finite_range _))
  have hKk : K ^ k ≤ Ideal.comap (P.evB S v) (𝔞.map (algebraMap S (S ⊗[R] P.A v)) ^ k) := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono (Ideal.map_comap_le) k
  refine ⟨N * k + k, fun f hf => ?_⟩
  have e := AdicEval.sub_truncTotal_mem (N * k) f
  rw [pow_mul] at e
  have h1 : f - (truncTotal (N * k) f : MvPowerSeries (Fin d) S) ∈ _ :=
    hKk (Ideal.pow_right_mono hN k e)
  have h2 : (truncTotal (N * k) f : MvPowerSeries (Fin d) S) ∈ Ideal.comap (P.evB S v)
      (𝔞.map (algebraMap S (S ⊗[R] P.A v)) ^ k) := by
    have hc := MvPolynomial.coe_mem_map_C (J := 𝔞 ^ k) (truncTotal (N * k) f) fun m => by
      rw [coeff_truncTotal_eq_ite]
      split_ifs with hm
      · exact Ideal.pow_le_pow_right (by omega) (hf m)
      · exact zero_mem _
    have hle : Ideal.map (C (σ := Fin d) (R := S)) (𝔞 ^ k) ≤ Ideal.comap (P.evB S v)
        (𝔞.map (algebraMap S (S ⊗[R] P.A v)) ^ k) := by
      rw [Ideal.map_le_iff_le_comap]
      intro s hs
      rw [Ideal.mem_comap, Ideal.mem_comap, evB_C, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hs
    exact hle hc
  have := add_mem h1 h2
  rwa [sub_add_cancel] at this

omit [IsAdicComplete (maximalIdeal R) R] in
theorem evB_eq_of_le (b : ∀ v, S ⊗[R] P.A v) (hb : ∀ v, P.inclB S v (b (v + 1)) = b v)
    {g : MvPowerSeries (Fin d) S} {w : ℕ} (hg : P.evB S w g = b w) :
    ∀ n v, v + n = w → P.evB S v g = b v := by
  intro n
  induction n with
  | zero => intro v hv; rw [add_zero] at hv; subst hv; exact hg
  | succ n ih =>
    intro v hv
    have := ih (v + 1) (by omega)
    rw [← P.map_evB_succ S v, AlgHom.comp_apply, this, hb]

omit [IsAdicComplete (maximalIdeal R) R] in
/-- **`S[[T]] → lim_v S ⊗_R A_v` is surjective** ([Hong, Lemma 2.2.15] for `F_S`). -/
theorem exists_evB_eq (hpm : (p : R) ∈ 𝔪R) (b : ∀ v, S ⊗[R] P.A v)
    (hb : ∀ v, P.inclB S v (b (v + 1)) = b v) :
    ∃ f : MvPowerSeries (Fin d) S, ∀ v, P.evB S v f = b v := by
  set 𝔞 := (𝔪R).map (algebraMap R S)
  choose g hg using fun v => P.evB_surjective S v (b v)
  have hK : ∀ v n, P.evB S v (g (v + n) - g v) = 0 := fun v n => by
    rw [map_sub, P.evB_eq_of_le S b hb (hg (v + n)) n v rfl, hg, sub_self]
  have hN : ∀ v n, g (v + n) - g v ∈ FGL.coeffFilt (σ := Fin d) 𝔞 v :=
    fun v n => P.ker_evB_le S hpm v (hK v n)
  have hlim : ∀ m : Fin d →₀ ℕ, ∃ L : S, ∀ k,
      coeff m (g (k + m.degree)) - L ∈ 𝔞 ^ k := by
    intro m
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := 𝔞) (fun k => coeff m (g (k + m.degree)))
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
  let f : MvPowerSeries (Fin d) S := fun m => L m
  have hf : ∀ v, f - g v ∈ FGL.coeffFilt (σ := Fin d) 𝔞 v := by
    intro v m
    by_cases hv : v ≤ m.degree
    · rw [Nat.sub_eq_zero_of_le hv, pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
    · obtain ⟨k, rfl⟩ : ∃ k, v = k + m.degree := ⟨v - m.degree, by omega⟩
      rw [Nat.add_sub_cancel, map_sub, ← neg_sub]
      exact neg_mem (hL m k)
  refine ⟨f, fun v => ?_⟩
  rw [← hg, ← sub_eq_zero, ← map_sub]
  refine IsHausdorff.haus' (I := 𝔞.map (algebraMap S (S ⊗[R] P.A v))) _ fun k => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  obtain ⟨w, hw⟩ := P.coeffFilt_le_comap_evB S v k
  have h1 : f - g (v + w) ∈ FGL.coeffFilt (σ := Fin d) 𝔞 w :=
    FGL.coeffFilt_antitone (by omega) (hf (v + w))
  have h2 := hw h1
  rw [Ideal.mem_comap] at h2
  rw [← sub_add_sub_cancel f (g (v + w)) (g v), map_add, hK v w, add_zero]
  exact h2

/-! ### Two variables and group-like elements -/

/-- `K_v^{(2)} = ([p^v](T), [p^v](U)) S[[T, U]]`. -/
def idealB2 (v : ℕ) : Ideal (MvPowerSeries (Fin 2 × Fin d) S) :=
  Ideal.map (MvPowerSeries.map (algebraMap R S)) (P.pairIdeal v)

omit [IsAdicComplete (maximalIdeal R) R] hp
  [IsAdicComplete ((maximalIdeal R).map (algebraMap R S)) S] in
theorem idealB2_le_coeffFilt (hpm : (p : R) ∈ 𝔪R) (v : ℕ) :
    P.idealB2 S v ≤ FGL.coeffFilt ((𝔪R).map (algebraMap R S)) v := by
  rw [idealB2, Ideal.map_le_iff_le_comap]
  intro f hf
  exact map_mem_coeffFilt S (P.pairIdeal_le_coeffFilt hpm v hf)

instance isAdicComplete_baseChange2 (v : ℕ) :
    IsAdicComplete (((𝔪R).map (algebraMap R S)).map
      (algebraMap S (S ⊗[R] (P.A v ⊗[R] P.A v)))) (S ⊗[R] (P.A v ⊗[R] P.A v)) :=
  isAdicComplete_of_free _ _

instance isHausdorff_baseChange2_R (v : ℕ) :
    IsHausdorff ((𝔪R).map (algebraMap R (S ⊗[R] (P.A v ⊗[R] P.A v))))
      (S ⊗[R] (P.A v ⊗[R] P.A v)) := by
  rw [← Ideal.map_map_algebraMap (S := S)]
  infer_instance

omit [IsAdicComplete (maximalIdeal R) R]
  [IsAdicComplete ((maximalIdeal R).map (algebraMap R S)) S] in
theorem tnfB2 (v : ℕ) (x : Fin 2 × Fin d) :
    TopNil ((𝔪R).map (algebraMap R S)) ((1 : S) ⊗ₜ[R] FGL.pairS (P.tL v) (P.tR v) x) := by
  obtain ⟨N, hN⟩ := (FGL.tnf_pairS (P.tnf_tL v) (P.tnf_tR v) x).map
    (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := P.A v ⊗[R] P.A v))
  refine ⟨N, ?_⟩
  rw [Ideal.map_map_algebraMap]
  simpa using hN

/-- `S[[T, U]] → S ⊗_R (A_v ⊗_R A_v)`, `(T, U) ↦ (1 ⊗ t ⊗ 1, 1 ⊗ 1 ⊗ t)`. -/
def evB2 (v : ℕ) : MvPowerSeries (Fin 2 × Fin d) S →ₐ[S] S ⊗[R] (P.A v ⊗[R] P.A v) :=
  evalT (𝔪 := (𝔪R).map (algebraMap R S))
    (fun x => (1 : S) ⊗ₜ[R] FGL.pairS (P.tL v) (P.tR v) x) (P.tnfB2 S v)

omit [IsAdicComplete (maximalIdeal R) R] in
theorem evB2_X (v : ℕ) (x : Fin 2 × Fin d) :
    P.evB2 S v (X x) = (1 : S) ⊗ₜ[R] FGL.pairS (P.tL v) (P.tR v) x := by
  rw [evB2, evalT_X]

/-- `R[[T,U]]/K_v → S[[T,U]]/K_v^{(2)}`. -/
def quotMap2 (v : ℕ) : (MvPowerSeries (Fin 2 × Fin d) R ⧸ P.pairIdeal v) →ₐ[R]
    (MvPowerSeries (Fin 2 × Fin d) S ⧸ P.idealB2 S v) :=
  Ideal.quotientMapₐ (P.idealB2 S v) (mapAlgHom (Algebra.ofId R S))
    fun _ hx => Ideal.mem_map_of_mem _ hx

/-- `S ⊗ (A_v ⊗ A_v) → S[[T, U]]/K_v^{(2)}`. -/
def quotB2 (v : ℕ) : S ⊗[R] (P.A v ⊗[R] P.A v) →ₐ[S]
    MvPowerSeries (Fin 2 × Fin d) S ⧸ P.idealB2 S v :=
  Algebra.TensorProduct.lift (Algebra.ofId S _) ((P.quotMap2 S v).comp (P.pairQuot v))
    fun _ _ => Commute.all _ _

theorem quotB2_evB2_X (v : ℕ) (x : Fin 2 × Fin d) :
    P.quotB2 S v (P.evB2 S v (X x)) = Ideal.Quotient.mk (P.idealB2 S v) (X x) := by
  have h := P.pairQuot_evPair_X v x
  rw [evPair, evalT_X] at h
  rw [evB2_X, quotB2, Algebra.TensorProduct.lift_tmul, map_one, one_mul, AlgHom.comp_apply, h,
    quotMap2, Ideal.quotient_map_mkₐ, mapAlgHom_apply, map_X]
  rfl

/-- **A power series in `(T, U)` over `S` vanishing in all `S ⊗ A_v ⊗ A_v` is zero.** -/
theorem eq_zero_of_evB2 (hpm : (p : R) ∈ 𝔪R) {g : MvPowerSeries (Fin 2 × Fin d) S}
    (hg : ∀ v, P.evB2 S v g = 0) : g = 0 :=
  FGL.eq_zero_of_mem_coeffFilt fun v =>
    sup_le (P.idealB2_le_coeffFilt S hpm v) (FGL.pow_span_X_le_coeffFilt v)
      (MvPowerSeries.mem_sup_pow_of_comp_eq_mk ((P.quotB2 S v).comp (P.evB2 S v))
        (fun x => P.quotB2_evB2_X S v x) (by rw [AlgHom.comp_apply, hg, map_zero]) v)

/-- `evB2 ∘ (change of coefficients) = 1 ⊗ evPair`. -/
theorem evB2_map (v : ℕ) (f : MvPowerSeries (Fin 2 × Fin d) R) :
    P.evB2 S v (MvPowerSeries.map (algebraMap R S) f) = (1 : S) ⊗ₜ[R] P.evPair v f := by
  have key : ((P.evB2 S v).restrictScalars R).comp (mapAlgHom (Algebra.ofId R S)) =
      (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := P.A v ⊗[R] P.A v)).comp
        (P.evPair v) := by
    refine algHom_ext_topNil (𝔪 := 𝔪R) (fun x => ?_) fun x => ?_
    · simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, mapAlgHom_apply, map_X]
      rw [evB2_X]
      obtain ⟨N, hN⟩ := P.tnfB2 S v x
      exact ⟨N, by rwa [Ideal.map_map_algebraMap] at hN⟩
    · simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, mapAlgHom_apply, map_X,
        evB2_X, Algebra.TensorProduct.includeRight_apply, evPair, evalT_X]
  exact congrArg (fun φ => φ f) key

/-- `S ⊗ Δ : S ⊗ A_v → S ⊗ (A_v ⊗ A_v)`. -/
def comulB (v : ℕ) : S ⊗[R] P.A v →ₐ[S] S ⊗[R] (P.A v ⊗[R] P.A v) :=
  Algebra.TensorProduct.map (AlgHom.id S S) (P.comul v)

/-- `b ↦ b ⊗ 1`. -/
def inlB (v : ℕ) : S ⊗[R] P.A v →ₐ[S] S ⊗[R] (P.A v ⊗[R] P.A v) :=
  Algebra.TensorProduct.map (AlgHom.id S S) (Algebra.TensorProduct.includeLeft (S := R))

/-- `b ↦ 1 ⊗ b`. -/
def inrB (v : ℕ) : S ⊗[R] P.A v →ₐ[S] S ⊗[R] (P.A v ⊗[R] P.A v) :=
  Algebra.TensorProduct.map (AlgHom.id S S) Algebra.TensorProduct.includeRight

omit [IsAdicComplete (maximalIdeal R) R] in
theorem evF_evB (v : ℕ) (U : MvPowerSeries (Fin d) S) :
    FGL.evF ((𝔪R).map (algebraMap R S)) (fun j => (1 : S) ⊗ₜ[R] P.t v j) U = P.evB S v U := by
  rw [FGL.evF_of (P.tnfB S v)]
  rfl

/-- `U(Φ(T, U'))` evaluated in `S ⊗ A_v ⊗ A_v` is `Δ(U(t))`. -/
theorem evB2_subst_Φ (v : ℕ) (U : MvPowerSeries (Fin d) S) :
    P.evB2 S v (U.subst fun j => MvPowerSeries.map (algebraMap R S) (P.F.Φ j)) =
      P.comulB S v (P.evB S v U) := by
  have hx := P.tnfB2 S v
  have h0 : ∀ j, constantCoeff (MvPowerSeries.map (algebraMap R S) (P.F.Φ j)) = 0 := by
    intro j; rw [← coeff_zero_eq_constantCoeff_apply, coeff_map,
      coeff_zero_eq_constantCoeff_apply, P.F.constantCoeff_Φ, map_zero]
  have e1 : P.evB2 S v (U.subst fun j => MvPowerSeries.map (algebraMap R S) (P.F.Φ j)) =
      FGL.evF ((𝔪R).map (algebraMap R S)) (fun x => (1 : S) ⊗ₜ[R] FGL.pairS (P.tL v) (P.tR v) x)
        (U.subst fun j => MvPowerSeries.map (algebraMap R S) (P.F.Φ j)) := by
    rw [FGL.evF_of hx]; rfl
  rw [e1, FGL.evF_subst hx h0]
  have hev : ∀ f, FGL.evF ((𝔪R).map (algebraMap R S))
      (fun x => (1 : S) ⊗ₜ[R] FGL.pairS (P.tL v) (P.tR v) x) f = P.evB2 S v f := by
    intro f; rw [FGL.evF_of hx]; rfl
  have e2 : (fun j => FGL.evF ((𝔪R).map (algebraMap R S))
      (fun x => (1 : S) ⊗ₜ[R] FGL.pairS (P.tL v) (P.tR v) x)
        (MvPowerSeries.map (algebraMap R S) (P.F.Φ j))) =
      fun j => P.comulB S v ((1 : S) ⊗ₜ[R] P.t v j) := by
    funext j
    rw [hev, evB2_map, evPair_eq, comulB, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      comul_t, wΔ]
    rfl
  rw [e2, ← FGL.evF_comp (P.comulB S v) (P.tnfB S v), evF_evB]

omit [IsAdicComplete (maximalIdeal R) R] in
/-- `U(T)` (resp. `U(U')`) evaluated in `S ⊗ A_v ⊗ A_v` is `U(t) ⊗ 1` (resp. `1 ⊗ U(t)`). -/
theorem evB2_subst_Xv (v : ℕ) (U : MvPowerSeries (Fin d) S) (a : Fin 2) :
    P.evB2 S v (U.subst (Xv (R := S) (d := d) (n := 2) a)) =
      if a = 0 then P.inlB S v (P.evB S v U) else P.inrB S v (P.evB S v U) := by
  have hx := P.tnfB2 S v
  have e1 : P.evB2 S v (U.subst (Xv (R := S) (d := d) (n := 2) a)) =
      FGL.evF ((𝔪R).map (algebraMap R S)) (fun x => (1 : S) ⊗ₜ[R] FGL.pairS (P.tL v) (P.tR v) x)
        (U.subst (Xv (R := S) (d := d) (n := 2) a)) := by
    rw [FGL.evF_of hx]; rfl
  rw [e1, FGL.evF_subst hx (FGL.noConst_Xv a)]
  simp only [Xv, FGL.evF_X hx]
  split_ifs with ha
  · subst ha
    rw [← evF_evB, FGL.evF_comp (P.inlB S v) (P.tnfB S v)]
    congr 1
  · rw [← evF_evB, FGL.evF_comp (P.inrB S v) (P.tnfB S v)]
    congr 1
    funext j
    simp [inrB, FGL.pairS, tR, ha]

/-- **Compatible group-like families give formal homomorphisms `F_S → Ĝ_m`**: if
`b_v ∈ S ⊗ A_v` are compatible and group-like (`Δ b_v = b_v ⊗ b_v`), the power series
`U ∈ S[[T]]` with `U(t) = b_v` satisfies `U(Φ(T, T')) = U(T) U(T')`. This is the step
`lim_v Hom(G_v ⊗ S, μ_{p^v}) = Hom(F_S, Ĝ_m)` of [Hong, Prop. 3.4.9, proof, (3.7)]
(`Ĝ_m` written multiplicatively, `1 + u ↦ u`). -/
theorem exists_groupLike (hpm : (p : R) ∈ 𝔪R) (b : ∀ v, S ⊗[R] P.A v)
    (hb : ∀ v, P.inclB S v (b (v + 1)) = b v)
    (hgl : ∀ v, P.comulB S v (b v) = P.inlB S v (b v) * P.inrB S v (b v)) :
    ∃ U : MvPowerSeries (Fin d) S, (∀ v, P.evB S v U = b v) ∧
      U.subst (fun j => MvPowerSeries.map (algebraMap R S) (P.F.Φ j)) =
        U.subst (Xv (R := S) (d := d) (n := 2) 0) * U.subst (Xv (R := S) (d := d) (n := 2) 1) := by
  obtain ⟨U, hU⟩ := P.exists_evB_eq S hpm b hb
  refine ⟨U, hU, sub_eq_zero.mp (P.eq_zero_of_evB2 S hpm fun v => ?_)⟩
  rw [map_sub, map_mul, evB2_subst_Φ, evB2_subst_Xv, evB2_subst_Xv, if_pos rfl,
    if_neg (by decide), hU, hgl, sub_self]

end PDivFGL

end PadicHodge
