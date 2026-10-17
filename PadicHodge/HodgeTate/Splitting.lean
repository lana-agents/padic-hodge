/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.HodgeTate.Basic
import PadicHodge.TateSen.TateH1

/-!
# Extensions of Hodge–Tate representations with distinct weights

Let `0 → V' → V → V'' → 0` be a short exact sequence of continuous `ℚ_p`-representations of
`G_L` (`L / ℚ_p` finite) with `V'` and `V''` Hodge–Tate, and assume that no Hodge–Tate weight of
`V''` is a weight of `V'`. Then `V` is Hodge–Tate (`isHodgeTate_of_exact_of_disjoint`): the
extension `ℂ_p ⊗ V` of `ℂ_p ⊗ V''` by `ℂ_p ⊗ V'` splits, `ℂ_p ⊗ V ≅ ⊕ ℂ_p(-q_i)`.

The key point (`exists_DHT_lift`) is the surjectivity of `D_q(V) → D_q(V'')` for every `q` which
is not a weight of `V'`: lifting `w'' ∈ D_q(V'')` to `w ∈ ℂ_p ⊗ V`, the defect
`σ ↦ χ(σ)^q σ w − w` is a continuous cocycle with values in `ℂ_p ⊗ V' ≅ ⊕ ℂ_p(q − q_i)`
(Hodge–Tate decomposition of `V'`), and each coordinate is a coboundary by **Tate's theorem**
`H¹(G_L, ℂ_p(j)) = 0` for `j ≠ 0` (`subsingleton_H1_twist`, transported from `L.fixingSubgroup`
to `G_L` in `exists_twist_coboundary_GL`). The uniqueness half (`Hom_{G_L}(ℂ_p(a), ℂ_p(b)) = 0`)
is `eq_zero_of_twist_equivariant` in `HodgeTate/Basic.lean`.

Continuity of `ρ` is expressed by `hcont : ∀ φ v, Continuous (σ ↦ φ (ρ σ v))` (for the Krull
topology on `G_L` and the `p`-adic topology on `ℚ_p`).
-/

noncomputable section

open Module TensorProduct Topology

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### From `L.fixingSubgroup` to `G_L` -/

section Transfer

variable {L : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] L]

/-- The identification `L.fixingSubgroup ≅ G_L` is continuous. -/
theorem continuous_fixingSubgroupEquiv : Continuous (IntermediateField.fixingSubgroupEquiv L) := by
  refine continuous_of_continuousAt_one (IntermediateField.fixingSubgroupEquiv L) ?_
  intro U hU
  rw [map_one] at hU
  obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff L (PadicAlgCl p) U).mp hU
  haveI : FiniteDimensional ℚ_[p] (E.restrictScalars ℚ_[p]) := by
    haveI : FiniteDimensional ℚ_[p] E := Module.Finite.trans (↥L) (↥E)
    exact this
  have h1 : ((E.restrictScalars ℚ_[p]).fixingSubgroup : Set (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p))
      ∈ 𝓝 (1 : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :=
    (krullTopology_mem_nhds_one_iff ℚ_[p] (PadicAlgCl p) _).mpr ⟨_, inferInstance, le_rfl⟩
  rw [Filter.mem_map, mem_nhds_subtype]
  refine ⟨_, h1, fun g hg => hEU ?_⟩
  change IntermediateField.fixingSubgroupEquiv L g ∈ E.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hg x hx

omit [FiniteDimensional ℚ_[p] L] in
theorem galCp_fixingSubgroupEquiv (g : L.fixingSubgroup) (x : ℂ_[p]) :
    galCp L (IntermediateField.fixingSubgroupEquiv L g) x = autCp (g : _) x := rfl

omit [FiniteDimensional ℚ_[p] L] in
theorem chiL_fixingSubgroupEquiv (j : ℤ) (g : L.fixingSubgroup) :
    chiL L j (IntermediateField.fixingSubgroupEquiv L g) =
      ((chiPow j (g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) : ℚ_[p]ˣ) : ℚ_[p]) := rfl

/-- **Tate's theorem on `G_L`**: a crossed homomorphism `G_L → ℂ_p(j)`, `j ≠ 0`, continuous on
`L.fixingSubgroup`, is a coboundary. -/
theorem exists_twist_coboundary_GL {j : ℤ} (hj : j ≠ 0)
    (c : (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) → ℂ_[p])
    (hc : Continuous (c ∘ IntermediateField.fixingSubgroupEquiv L))
    (hco : ∀ σ τ, c (σ * τ) = c σ + chiL L j σ • galCp L σ (c τ)) :
    ∃ y : ℂ_[p], ∀ σ, c σ = chiL L j σ • galCp L σ y - y := by
  set e := IntermediateField.fixingSubgroupEquiv L
  have hmem : (c ∘ e) ∈ ContH1.cocycles (rhoK L j) := by
    refine ⟨hc, fun g h => ?_⟩
    simp only [Function.comp_apply, map_mul]
    rw [hco]
    rfl
  haveI := subsingleton_H1_twist (K := L) hj
  have h0 : ContH1.mk (rhoK L j) ⟨c ∘ e, hmem⟩ = 0 := Subsingleton.elim _ _
  obtain ⟨y, hy⟩ := (ContH1.mk_eq_zero_iff _).mp h0
  refine ⟨y, fun σ => ?_⟩
  have := hy (e.symm σ)
  simp only [Function.comp_apply, MulEquiv.apply_symm_apply] at this
  rw [this]
  have h2 : e (e.symm σ) = σ := MulEquiv.apply_symm_apply e σ
  conv_rhs => rw [← h2]
  rfl

end Transfer

section Split

variable {L : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] L]

/-- `κ_q(σ) = χ(σ)^{-q} ∈ ℂ_p`, the eigenvalue on `D_q`. -/
abbrev kap (q : ℤ) (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) : ℂ_[p] :=
  algebraMap ℚ_[p] ℂ_[p] (chiL L (-q) σ)

omit [FiniteDimensional ℚ_[p] L] in
theorem chiL_ne_zero (j : ℤ) (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) : chiL L j σ ≠ 0 :=
  Units.ne_zero _

omit [FiniteDimensional ℚ_[p] L] in
theorem kap_ne_zero (q : ℤ) (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) : kap q σ ≠ 0 :=
  (map_ne_zero_iff _ (algebraMap ℚ_[p] ℂ_[p]).injective).mpr (chiL_ne_zero _ σ)

omit [FiniteDimensional ℚ_[p] L] in
theorem kap_mul (q : ℤ) (σ τ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) :
    kap q (σ * τ) = kap q σ * kap q τ := by
  rw [kap, chiL_mul, map_mul]

omit [FiniteDimensional ℚ_[p] L] in
theorem kap_inv_mul (q a : ℤ) (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) :
    (kap q σ)⁻¹ * kap a σ = algebraMap ℚ_[p] ℂ_[p] (chiL L (q - a) σ) := by
  have h1 : chiL L q σ * chiL L (-q) σ = 1 := by rw [← chiL_add, add_neg_cancel, chiL_zero]
  have h2 : chiL L (q - a) σ = chiL L q σ * chiL L (-a) σ := by rw [sub_eq_add_neg, chiL_add]
  rw [h2, map_mul, kap, kap, inv_mul_eq_iff_eq_mul₀ (kap_ne_zero q σ), ← mul_assoc, ← map_mul,
    mul_comm (chiL L (-q) σ), h1, map_one, one_mul]

omit [FiniteDimensional ℚ_[p] L] in
theorem galCp_kap (σ τ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (q : ℤ) :
    galCp L σ (kap q τ) = kap q τ := galCp_algebraMap σ _

variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
  {ρ : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) V}

theorem psi_smul (q : ℤ) (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (w : CpTensor ρ) :
    (htSetup L).ψ q σ • w = kap q σ • w := by
  change algebraMap L ℂ_[p] (algebraMap ℚ_[p] L (chiL L (-q) σ)) • w = _
  rw [algebraMap_L_cp_algebraMap]

theorem mem_DHT_iff_kap {q : ℤ} {w : CpTensor ρ} :
    w ∈ DHT ρ q ↔ ∀ σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p, σ • w = kap q σ • w := by
  rw [mem_DHT]
  simp only [psi_smul]

omit [FiniteDimensional ℚ_[p] L] in
theorem gal_smul_cp_smul (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (c : ℂ_[p]) (w : CpTensor ρ) :
    σ • c • w = galCp L σ c • σ • w :=
  smul_distrib_cpTensor ρ σ c w

omit [FiniteDimensional ℚ_[p] L] in
theorem gal_smul_kap_smul (σ τ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (q : ℤ) (w : CpTensor ρ) :
    σ • kap q τ • w = kap q τ • σ • w := by
  rw [gal_smul_cp_smul, galCp_kap]

/-- Coordinates of `σ w` in an eigenbasis. -/
theorem repr_gal_smul {ι : Type} [Finite ι] (b : Basis ι ℂ_[p] (CpTensor ρ)) (qs : ι → ℤ)
    (hb : ∀ i, b i ∈ DHT ρ (qs i)) (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (m : CpTensor ρ)
    (i : ι) : b.repr (σ • m) i = galCp L σ (b.repr m i) * kap (qs i) σ := by
  haveI := Fintype.ofFinite ι
  have h : σ • m = ∑ k, (galCp L σ (b.repr m k) * kap (qs k) σ) • b k := by
    conv_lhs => rw [← b.sum_repr m]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [gal_smul_cp_smul, (mem_DHT_iff_kap.mp (hb k)) σ, smul_smul]
  rw [h, b.repr_sum_self]

omit [FiniteDimensional ℚ_[p] L] in
/-- Continuity of the matrix coefficients of `ρ` along `L.fixingSubgroup`. -/
theorem continuous_linear_rho [FiniteDimensional ℚ_[p] V]
    (hcont : ∀ (φ : Module.Dual ℚ_[p] V) (v : V), Continuous fun σ => φ (ρ σ v))
    (μ : V →ₗ[ℚ_[p]] ℂ_[p]) (v : V) : Continuous fun σ => μ (ρ σ v) := by
  set B := Module.finBasis ℚ_[p] V
  have h : ∀ σ, μ (ρ σ v) = ∑ l, B.coord l (ρ σ v) • μ (B l) := by
    intro σ
    conv_lhs => rw [← B.sum_repr (ρ σ v)]
    rw [map_sum]
    simp only [map_smul, Basis.coord_apply]
  simp_rw [h]
  exact continuous_finsetSum _ fun l _ => (hcont (B.coord l) v).smul continuous_const

/-- Continuity of `g ↦ Λ(g w)` on `L.fixingSubgroup` for a `ℂ_p`-linear form `Λ`. -/
theorem continuous_form_gal [FiniteDimensional ℚ_[p] V]
    (hcont : ∀ (φ : Module.Dual ℚ_[p] V) (v : V), Continuous fun σ => φ (ρ σ v))
    (Λ : ℂ_[p] ⊗[ℚ_[p]] V →ₗ[ℂ_[p]] ℂ_[p]) (w : ℂ_[p] ⊗[ℚ_[p]] V) :
    Continuous fun g : L.fixingSubgroup =>
      Λ (TensorProduct.map (galCpLin L (IntermediateField.fixingSubgroupEquiv L g))
        (ρ (IntermediateField.fixingSubgroupEquiv L g)) w) := by
  induction w using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero]
    exact continuous_const
  | tmul x v =>
    set μ : V →ₗ[ℚ_[p]] ℂ_[p] :=
      (Λ.restrictScalars ℚ_[p]).comp (TensorProduct.mk ℚ_[p] ℂ_[p] V 1) with hμ
    have h : ∀ g : L.fixingSubgroup,
        Λ (TensorProduct.map (galCpLin L (IntermediateField.fixingSubgroupEquiv L g))
          (ρ (IntermediateField.fixingSubgroupEquiv L g)) (x ⊗ₜ v)) =
        autCp (g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) x *
          μ (ρ (IntermediateField.fixingSubgroupEquiv L g) v) := by
      intro g
      rw [TensorProduct.map_tmul, galCpLin_apply, galCp_fixingSubgroupEquiv]
      have e : (autCp (g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) x ⊗ₜ[ℚ_[p]]
          ρ (IntermediateField.fixingSubgroupEquiv L g) v : ℂ_[p] ⊗[ℚ_[p]] V) =
          autCp (g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) x •
            ((1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] ρ (IntermediateField.fixingSubgroupEquiv L g) v) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [e, map_smul, smul_eq_mul]
      rfl
    simp_rw [h]
    exact ((continuous_autCp_apply x).comp continuous_subtype_val).mul
      ((continuous_linear_rho hcont μ v).comp continuous_fixingSubgroupEquiv)
  | add x y hx hy =>
    simp only [map_add]
    exact hx.add hy

end Split

section Exact

variable {L : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] L]
  {V' V V'' : Type*} [AddCommGroup V'] [Module ℚ_[p] V'] [AddCommGroup V] [Module ℚ_[p] V]
  [AddCommGroup V''] [Module ℚ_[p] V'']
  {ρ' : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) V'}
  {ρ : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) V}
  {ρ'' : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) V''}
  {f : V' →ₗ[ℚ_[p]] V} {g : V →ₗ[ℚ_[p]] V''}
  (hf : ∀ σ, f ∘ₗ ρ' σ = ρ σ ∘ₗ f) (hg : ∀ σ, g ∘ₗ ρ σ = ρ'' σ ∘ₗ g)
  (hfi : Function.Injective f) (hgs : Function.Surjective g) (hfg : Function.Exact f g)
include hf hg hfi hgs hfg

/-- **Lifting `D_q`**: if `q` is not a Hodge–Tate weight of `V'`, every `w'' ∈ D_q(V'')` lifts to
`D_q(V)` (by Tate's `H¹(G_L, ℂ_p(j)) = 0`, `j ≠ 0`). -/
theorem exists_DHT_lift [FiniteDimensional ℚ_[p] V'] [FiniteDimensional ℚ_[p] V]
    (hcont : ∀ (φ : Module.Dual ℚ_[p] V) (v : V), Continuous fun σ => φ (ρ σ v))
    (h' : IsHodgeTate ρ') {q : ℤ} (hq : DHT ρ' q = ⊥) {w'' : CpTensor ρ''}
    (hw'' : w'' ∈ DHT ρ'' q) : ∃ w ∈ DHT ρ q, tensorMap (ρ' := ρ'') g w = w'' := by
  classical
  -- `ℂ_p`-linear version of `1 ⊗ f` and a left inverse
  set Fc : CpTensor ρ' →ₗ[ℂ_[p]] CpTensor ρ :=
    { toFun := tensorMap (ρ := ρ') (ρ' := ρ) f
      map_add' := tensorMap_add f
      map_smul' := fun c w => tensorMap_smul f c w } with hFc
  have hFcapp : ∀ m, Fc m = tensorMap (ρ := ρ') (ρ' := ρ) f m := fun m => rfl
  set Gc : CpTensor ρ →ₗ[ℂ_[p]] CpTensor ρ'' :=
    { toFun := tensorMap (ρ := ρ) (ρ' := ρ'') g
      map_add' := tensorMap_add g
      map_smul' := fun c w => tensorMap_smul g c w } with hGc
  have hGcapp : ∀ m, Gc m = tensorMap (ρ := ρ) (ρ' := ρ'') g m := fun m => rfl
  obtain ⟨Ψ, hΨ⟩ := LinearMap.exists_leftInverse_of_injective Fc
    (LinearMap.ker_eq_bot.mpr (tensorMap_injective hfi))
  have hΨapp : ∀ m, Ψ (Fc m) = m := fun m => LinearMap.congr_fun hΨ m
  -- lift `w''`
  obtain ⟨w, hw⟩ : ∃ w : CpTensor ρ, tensorMap (ρ' := ρ'') g w = w'' :=
    LinearMap.lTensor_surjective ℂ_[p] hgs w''
  -- a Hodge–Tate eigenbasis of `ℂ_p ⊗ V'`
  obtain ⟨ι, hι, b, qs, hb⟩ := (isHodgeTate_iff_exists_basis ρ').mp h'
  have hqs : ∀ i, q - qs i ≠ 0 := by
    intro i h
    have hbi := hb i
    rw [show qs i = q by omega, hq] at hbi
    exact b.ne_zero i ((Submodule.mem_bot L).mp hbi)
  have hex : Function.Exact (f.lTensor ℂ_[p]) (g.lTensor ℂ_[p]) :=
    Module.Flat.lTensor_exact ℂ_[p] hfg
  have hexc : ∀ y, Gc y = 0 → ∃ x, Fc x = y := fun y hy => (hex y).mp hy
  have hGF : ∀ x, Gc (Fc x) = 0 := fun x => hex.apply_apply_eq_zero x
  -- the defect `σ w - κ_q(σ) w` comes from `ℂ_p ⊗ V'`
  have hdef : ∀ σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p,
      ∃ c' : CpTensor ρ', Fc c' = σ • w - kap q σ • w := by
    intro σ
    apply hexc
    rw [map_sub, Gc.map_smul (kap q σ) w, hGcapp, hGcapp, tensorMap_gal g hg, hw,
      (mem_DHT_iff_kap.mp hw'') σ, sub_self]
  choose c' hc' using hdef
  -- cocycle identity
  have hcoc : ∀ σ τ, c' (σ * τ) = σ • c' τ + kap q τ • c' σ := by
    intro σ τ
    apply tensorMap_injective (ρ := ρ') (ρ' := ρ) hfi
    rw [← hFcapp, ← hFcapp, map_add, Fc.map_smul (kap q τ) (c' σ), hFcapp (σ • c' τ),
      tensorMap_gal f hf, ← hFcapp, hc', hc', hc', mul_smul, kap_mul, smul_sub, smul_sub,
      gal_smul_kap_smul, smul_smul, smul_smul, mul_comm (kap q σ)]
    abel
  -- the normalised defect and its coordinates
  set e' : (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) → CpTensor ρ' := fun σ => (kap q σ)⁻¹ • c' σ
    with he'
  have hkinv : ∀ σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p,
      (kap q σ)⁻¹ = algebraMap ℚ_[p] ℂ_[p] (chiL L q σ) := by
    intro σ
    have := kap_inv_mul q 0 σ
    simp only [kap, neg_zero, chiL_zero, map_one, mul_one, sub_zero] at this
    exact this
  have he'coc : ∀ σ τ, e' (σ * τ) = e' σ + (kap q σ)⁻¹ • σ • e' τ := by
    intro σ τ
    have hA : σ • ((kap q τ)⁻¹ • c' τ) = (kap q τ)⁻¹ • σ • c' τ := by
      rw [gal_smul_cp_smul, hkinv τ, galCp_algebraMap]
    simp only [he']
    rw [hcoc, hA, kap_mul, mul_inv, smul_add, ← smul_smul, ← smul_smul,
      smul_smul (kap q τ)⁻¹ (kap q τ), inv_mul_cancel₀ (kap_ne_zero q τ), one_smul, add_comm]
  set E : ι → (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) → ℂ_[p] := fun i σ => b.repr (e' σ) i with hE
  have hEcoc : ∀ i σ τ, E i (σ * τ) = E i σ + chiL L (q - qs i) σ • galCp L σ (E i τ) := by
    intro i σ τ
    simp only [hE]
    rw [he'coc, map_add, Finsupp.add_apply, b.repr.map_smul (kap q σ)⁻¹ (σ • e' τ),
      Finsupp.smul_apply,
      repr_gal_smul b qs hb, smul_eq_mul, Algebra.smul_def, ← kap_inv_mul]
    ring
  -- continuity of the coordinates on `L.fixingSubgroup`
  have hEcont : ∀ i, Continuous (E i ∘ IntermediateField.fixingSubgroupEquiv L) := by
    intro i
    set Λ : CpTensor ρ →ₗ[ℂ_[p]] ℂ_[p] := (b.coord i).comp Ψ
    have hform : ∀ σ, E i σ = (kap q σ)⁻¹ * Λ (σ • w) - Λ w := by
      intro σ
      simp only [hE, he', b.repr.map_smul, Finsupp.smul_apply, smul_eq_mul]
      have : b.repr (c' σ) i = Λ (σ • w - kap q σ • w) := by
        rw [← hc']; simp [Λ, hΨapp]
      rw [this, Λ.map_sub, Λ.map_smul, smul_eq_mul, mul_sub, ← mul_assoc,
        inv_mul_cancel₀ (kap_ne_zero q σ), one_mul]
    have h1 : Continuous fun g : L.fixingSubgroup =>
        (kap q (IntermediateField.fixingSubgroupEquiv L g))⁻¹ := by
      simp_rw [hkinv, chiL_fixingSubgroupEquiv]
      exact (continuous_algebraMap ℚ_[p] ℂ_[p]).comp
        ((continuous_chiPow q).comp continuous_subtype_val)
    have h2 := continuous_form_gal hcont Λ w
    have : E i ∘ IntermediateField.fixingSubgroupEquiv L = fun g =>
        (kap q (IntermediateField.fixingSubgroupEquiv L g))⁻¹ *
          Λ (TensorProduct.map (galCpLin L (IntermediateField.fixingSubgroupEquiv L g))
            (ρ (IntermediateField.fixingSubgroupEquiv L g)) w) - Λ w := by
      funext g
      rw [Function.comp_apply, hform]
      rfl
    rw [this]
    exact (h1.mul h2).sub continuous_const
  -- Tate's theorem on each coordinate
  choose y hy using fun i => exists_twist_coboundary_GL (hqs i) (E i) (hEcont i) (hEcoc i)
  set m' : CpTensor ρ' := ∑ i, y i • b i with hm'
  have hrepr_m' : ∀ i, b.repr m' i = y i := fun i => by rw [hm', b.repr_sum_self]
  have he'eq : ∀ σ, e' σ = (kap q σ)⁻¹ • σ • m' - m' := by
    intro σ
    apply b.repr.injective
    ext i
    rw [map_sub, b.repr.map_smul (kap q σ)⁻¹ (σ • m'), Finsupp.sub_apply, Finsupp.smul_apply,
      repr_gal_smul b qs hb,
      hrepr_m', smul_eq_mul, ← mul_assoc, mul_right_comm, kap_inv_mul, ← Algebra.smul_def]
    exact hy i σ
  have hc'eq : ∀ σ, c' σ = σ • m' - kap q σ • m' := by
    intro σ
    have h1 : c' σ = kap q σ • e' σ := by
      simp only [he', smul_smul, mul_inv_cancel₀ (kap_ne_zero q σ), one_smul]
    rw [h1, he'eq, smul_sub, smul_smul, mul_inv_cancel₀ (kap_ne_zero q σ), one_smul]
  -- the lift
  refine ⟨w - Fc m', ?_, ?_⟩
  · rw [mem_DHT_iff_kap]
    intro σ
    have h1 : σ • Fc m' = Fc (σ • m') := by rw [hFcapp, hFcapp, tensorMap_gal f hf]
    have h2 := hc' σ
    rw [hc'eq, map_sub, Fc.map_smul, ← h1] at h2
    rw [smul_sub, smul_sub, sub_eq_sub_iff_sub_eq_sub]
    exact h2.symm
  · rw [← hGcapp, map_sub, hGF, sub_zero, hGcapp]
    exact hw

/-- **Extensions with distinct Hodge–Tate weights are Hodge–Tate**: in a short exact sequence
`0 → V' → V → V'' → 0` of continuous representations with `V'`, `V''` Hodge–Tate and no common
weight (every weight of `V''` is not a weight of `V'`), `V` is Hodge–Tate, i.e.
`ℂ_p ⊗ V ≅ (ℂ_p ⊗ V') ⊕ (ℂ_p ⊗ V'')` as semilinear representations. -/
theorem isHodgeTate_of_exact_of_disjoint [FiniteDimensional ℚ_[p] V']
    [FiniteDimensional ℚ_[p] V] [FiniteDimensional ℚ_[p] V'']
    (hcont : ∀ (φ : Module.Dual ℚ_[p] V) (v : V), Continuous fun σ => φ (ρ σ v))
    (h' : IsHodgeTate ρ') (h'' : IsHodgeTate ρ'')
    (hdisj : ∀ q, DHT ρ'' q ≠ ⊥ → DHT ρ' q = ⊥) : IsHodgeTate ρ := by
  classical
  have hq : ∀ q, finrank L (DHT ρ' q) + finrank L (DHT ρ'' q) ≤ finrank L (DHT ρ q) := by
    intro q
    by_cases h0 : DHT ρ'' q = ⊥
    · rw [h0, finrank_bot, add_zero]
      exact LinearMap.finrank_le_finrank_of_injective (f := DHTmap f hf q) fun a b h =>
        Subtype.ext (tensorMap_injective (ρ := ρ') (ρ' := ρ) hfi (congrArg Subtype.val h))
    · rw [hdisj q h0, finrank_bot, zero_add]
      refine LinearMap.finrank_le_finrank_of_surjective (f := DHTmap g hg q) fun w'' => ?_
      obtain ⟨w, hw, hgw⟩ :=
        exists_DHT_lift hf hg hfi hgs hfg hcont h' (hdisj q h0) w''.2
      exact ⟨⟨w, hw⟩, Subtype.ext hgw⟩
  set S := (finite_support_DHT ρ').toFinset ∪ (finite_support_DHT ρ).toFinset ∪
    (finite_support_DHT ρ'').toFinset with hS
  have hS' : Function.support (fun q => finrank L (DHT ρ' q)) ⊆ S := by
    intro q hq; simp [hS, hq]
  have hSV : Function.support (fun q => finrank L (DHT ρ q)) ⊆ S := by
    intro q hq; simp [hS, hq]
  have hS'' : Function.support (fun q => finrank L (DHT ρ'' q)) ⊆ S := by
    intro q hq; simp [hS, hq]
  have hdim : finrank ℚ_[p] V = finrank ℚ_[p] V' + finrank ℚ_[p] V'' := by
    have h1 := LinearMap.finrank_range_add_finrank_ker g
    rw [LinearMap.range_eq_top.mpr hgs, finrank_top] at h1
    have h2 : LinearMap.ker g = LinearMap.range f := (LinearMap.exact_iff.mp hfg)
    rw [h2, LinearMap.finrank_range_of_inj hfi] at h1
    omega
  have hsum : ∑ q ∈ S, finrank L (DHT ρ' q) + ∑ q ∈ S, finrank L (DHT ρ'' q) ≤
      ∑ q ∈ S, finrank L (DHT ρ q) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun q _ => hq q
  have e := htDim_eq_sum ρ hSV
  have e' := htDim_eq_sum ρ' hS'
  have e'' := htDim_eq_sum ρ'' hS''
  have hle := htDim_le ρ
  unfold IsHodgeTate at h' h'' ⊢
  omega

end Exact

end PadicHodge
