/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.TateRep

/-!
# Continuity of the Galois action on `V_p G`

For a `p`-divisible group `G` over `ℚ_p` and a finite extension `L / ℚ_p` inside `ℚ̄_p`, the
representation `V_p G = ℚ_p ⊗_{ℤ_p} T_p G(ℚ̄_p)` of `G_L` is continuous (Krull topology on
`G_L`, `p`-adic topology on `ℚ_p`): `continuous_tateRep`, in the form
`∀ φ v, Continuous (σ ↦ φ(σ v))` used by `HodgeTate/Splitting.lean`.

* `galPoints_eq_of_fixed`: a point `x : A → ℚ̄_p` of a finite `ℚ_p`-group scheme is fixed by
  every `σ` fixing the finitely many values `x(b_i)` on a basis of `A`; these generate a finite
  extension of `L`, whose fixing subgroup is open (`eventually_galTate_val_eq`);
* `exists_eq_p_pow_smul`: `ker(T_p G → G_n(ℚ̄_p)) = p^n T_p G` (from the coordinates
  `ℤ_p^h ≅ T_p G`, `exists_tateBasis`);
* `exists_norm_le`: a `ℤ_p`-linear form `T_p G → ℚ_p` is bounded (`T_p G` is finitely
  generated);
* hence `σ ↦ φ(σ t)` is continuous: if `τ` fixes the level-`n` point of `t`, then
  `σ τ t − σ t ∈ p^n T_p G`.
-/

noncomputable section

open TensorProduct Filter Topology

namespace PadicHodge

namespace PDivGroup

open FFGroupScheme

variable {p : ℕ} [hp : Fact p.Prime]

local notation "K" => PadicAlgCl p

/-- **Points over `ℚ̄_p` are fixed by an open subgroup**: `σ ∘ x = x` for all `σ ∈ G_L` in a
neighbourhood of `1`. -/
theorem eventually_galPoints_eq (L : IntermediateField ℚ_[p] K) (G : FFGroupScheme ℚ_[p])
    (x : G.points K) :
    ∀ᶠ σ in 𝓝 (1 : K ≃ₐ[L] K), galPoints G (σ.restrictScalars ℚ_[p]) x = x := by
  classical
  let b := Module.Free.chooseBasis ℚ_[p] G.A
  set S : Set K := Set.range fun i => WithConv.ofConv x (b i)
  have hint : ∀ s ∈ S, IsIntegral L s := fun s _ =>
    (Algebra.IsIntegral.isIntegral (R := ℚ_[p]) s).tower_top
  haveI : FiniteDimensional L (IntermediateField.adjoin L S) :=
    IntermediateField.finiteDimensional_adjoin hint
  have hU : ((IntermediateField.adjoin L S).fixingSubgroup : Set (K ≃ₐ[L] K)) ∈
      𝓝 (1 : K ≃ₐ[L] K) :=
    (krullTopology_mem_nhds_one_iff L K _).mpr ⟨_, inferInstance, le_rfl⟩
  filter_upwards [hU] with σ hσ
  apply WithConv.ofConv_injective
  apply AlgHom.toLinearMap_injective
  refine b.ext fun i => ?_
  have hs : WithConv.ofConv x (b i) ∈ IntermediateField.adjoin L S :=
    IntermediateField.subset_adjoin L S ⟨i, rfl⟩
  exact (IntermediateField.mem_fixingSubgroup_iff _ σ).mp hσ _ hs

variable (H : PDivGroup ℚ_[p] p)

local instance : NeZero p := ⟨hp.out.ne_zero⟩

/-- **`ker(T_p G → G_n(ℚ̄_p)) = p^n T_p G`.** -/
theorem exists_eq_p_pow_smul (n : ℕ) (s : Additive (H.TateModule K))
    (hs : (Additive.toMul s).1 n = 1) : ∃ s', s = (p : ℤ_[p]) ^ n • s' := by
  classical
  obtain ⟨t, hlev, hphi⟩ := H.exists_tateBasis
  obtain ⟨c, hc⟩ := hphi.2 (Additive.toMul s)
  have h1 : (Multiplicative.ofAdd fun i => PadicInt.toZModPow n (Multiplicative.toAdd c i)) =
      (1 : Multiplicative (Fin H.height → ZMod (p ^ n))) := by
    apply (hlev n).1
    rw [map_one, ← phi_apply, hc]
    exact hs
  have h2 : ∀ i, ∃ c' : ℤ_[p], Multiplicative.toAdd c i = (p : ℤ_[p]) ^ n * c' := by
    intro i
    have h3 : PadicInt.toZModPow n (Multiplicative.toAdd c i) = 0 :=
      congrFun (congrArg Multiplicative.toAdd h1) i
    have h4 : Multiplicative.toAdd c i ∈ RingHom.ker (PadicInt.toZModPow n : ℤ_[p] →+* _) := h3
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton'] at h4
    obtain ⟨a, ha⟩ := h4
    exact ⟨a, by rw [← ha, mul_comm]⟩
  choose c' hc' using h2
  refine ⟨H.phiLin _ t c', ?_⟩
  rw [← map_smul]
  change s = Additive.ofMul (H.phi K t (Multiplicative.ofAdd ((p : ℤ_[p]) ^ n • c')))
  have : Multiplicative.ofAdd ((p : ℤ_[p]) ^ n • c') = c := by
    apply Multiplicative.toAdd.injective
    funext i
    rw [toAdd_ofAdd, Pi.smul_apply, smul_eq_mul, ← hc' i]
  rw [this, hc]
  rfl

/-- **`ℤ_p`-linear forms on `T_p G` are bounded.** -/
theorem exists_norm_le (φ : Additive (H.TateModule K) →ₗ[ℤ_[p]] ℚ_[p]) :
    ∃ M : ℝ, ∀ s, ‖φ s‖ ≤ M := by
  classical
  obtain ⟨t, -, hphi⟩ := H.exists_tateBasis
  refine ⟨∑ i, ‖φ (H.phiLin K t (Pi.single i 1))‖, fun s => ?_⟩
  obtain ⟨c, hc⟩ := hphi.2 (Additive.toMul s)
  have hs : s = H.phiLin K t (Multiplicative.toAdd c) := by
    change s = Additive.ofMul (H.phi K t (Multiplicative.ofAdd (Multiplicative.toAdd c)))
    rw [ofAdd_toAdd, hc]
    rfl
  have hsum : Multiplicative.toAdd c = ∑ i, Multiplicative.toAdd c i • Pi.single i 1 := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hs, hsum, map_sum, map_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [map_smul, map_smul, ← algebraMap_smul ℚ_[p], smul_eq_mul, norm_mul]
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  exact PadicInt.norm_le_one (Multiplicative.toAdd c i)

/-- `σ ↦ φ(σ t)` is continuous on `G_L`. -/
theorem continuous_galLin (L : IntermediateField ℚ_[p] K)
    (φ : Additive (H.TateModule K) →ₗ[ℤ_[p]] ℚ_[p]) (t : Additive (H.TateModule K)) :
    Continuous fun σ : K ≃ₐ[L] K => φ (H.galLin (σ.restrictScalars ℚ_[p]) t) := by
  obtain ⟨M, hM⟩ := H.exists_norm_le φ
  rw [continuous_iff_continuousAt]
  intro σ₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (p : ℝ)⁻¹ ^ n * M < ε := by
    have h1 : Tendsto (fun n : ℕ => (p : ℝ)⁻¹ ^ n * M) atTop (𝓝 (0 * M)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
        (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt))).mul_const M
    rw [zero_mul] at h1
    exact (h1.eventually (gt_mem_nhds hε)).exists
  rw [← map_mul_left_nhds_one σ₀, eventually_map]
  filter_upwards [eventually_galPoints_eq L (H.G n) ((Additive.toMul t).1 n)] with τ hτ
  set σ := σ₀ * τ
  have hlev : (Additive.toMul (H.galLin (τ.restrictScalars ℚ_[p]) t - t)).1 n = 1 := by
    change (Additive.toMul (H.galLin (τ.restrictScalars ℚ_[p]) t)).1 n *
      ((Additive.toMul t).1 n)⁻¹ = 1
    change galPoints (H.G n) (τ.restrictScalars ℚ_[p]) ((Additive.toMul t).1 n) * _ = 1
    rw [hτ, mul_inv_cancel]
  obtain ⟨s', hs'⟩ := H.exists_eq_p_pow_smul n _ hlev
  have hdiff : H.galLin (σ.restrictScalars ℚ_[p]) t - H.galLin (σ₀.restrictScalars ℚ_[p]) t =
      (p : ℤ_[p]) ^ n • H.galLin (σ₀.restrictScalars ℚ_[p]) s' := by
    have e : H.galLin (σ.restrictScalars ℚ_[p]) t =
        H.galLin (σ₀.restrictScalars ℚ_[p]) (H.galLin (τ.restrictScalars ℚ_[p]) t) := rfl
    rw [e, ← map_sub, hs', map_smul]
  rw [dist_eq_norm, ← map_sub, hdiff, map_smul, ← algebraMap_smul ℚ_[p], smul_eq_mul, norm_mul]
  refine lt_of_le_of_lt ?_ hn
  have hp' : ‖algebraMap ℤ_[p] ℚ_[p] ((p : ℤ_[p]) ^ n)‖ = (p : ℝ)⁻¹ ^ n := by
    rw [map_pow, map_natCast, norm_pow, Padic.norm_p]
  rw [hp']
  exact mul_le_mul_of_nonneg_left (hM _) (by positivity)

/-- **The Galois representation `V_p G` is continuous.** -/
theorem continuous_tateRep (L : IntermediateField ℚ_[p] K)
    (φ : Module.Dual ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] Additive (H.TateModule K)))
    (v : ℚ_[p] ⊗[ℤ_[p]] Additive (H.TateModule K)) :
    Continuous fun σ => φ (H.tateRep L σ v) := by
  induction v using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero]
    exact continuous_const
  | tmul a t =>
    set φ' : Additive (H.TateModule K) →ₗ[ℤ_[p]] ℚ_[p] :=
      ((φ.restrictScalars ℤ_[p]).comp (TensorProduct.mk ℤ_[p] ℚ_[p] _ 1))
    have h : ∀ σ : K ≃ₐ[L] K, φ (H.tateRep L σ (a ⊗ₜ t)) =
        a * φ' (H.galLin (σ.restrictScalars ℚ_[p]) t) := by
      intro σ
      change φ (a ⊗ₜ H.galLin (σ.restrictScalars ℚ_[p]) t) = _
      rw [show (a ⊗ₜ[ℤ_[p]] H.galLin (σ.restrictScalars ℚ_[p]) t :
          ℚ_[p] ⊗[ℤ_[p]] Additive (H.TateModule K)) =
          a • ((1 : ℚ_[p]) ⊗ₜ H.galLin (σ.restrictScalars ℚ_[p]) t) by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul, smul_eq_mul]
      rfl
    simp_rw [h]
    exact continuous_const.mul (H.continuous_galLin L φ' t)
  | add x y hx hy =>
    simp only [map_add]
    exact hx.add hy

end PDivGroup

end PadicHodge
