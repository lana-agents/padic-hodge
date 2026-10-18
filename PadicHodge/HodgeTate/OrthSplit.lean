/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.HodgeTate.Splitting
import PadicHodge.HodgeTate.Orthogonal
import PadicHodge.GroupScheme.TateDualRep

/-!
# Hodge–Tate from orthogonal invariants ([Hong, proof of Thm. 3.4.12])

Let `V` be a finite-dimensional continuous `ℚ_p`-representation of `G_L` and `q + q' ≠ 0`.
By the orthogonality (3.11) (`finrank_DHT_add_finrank_DHT_dual_le`),
`dim D_q(V) + dim D_{q'}(V^∨) ≤ dim V`. In Tate's situation equality holds
(`V = V_p G`, `q = -1`, `q' = 0`, [Hong, Thm. 3.4.10]), and then [Hong, Thm. 3.4.12] says that
`ℂ_p ⊗ V^∨` is the direct sum of `ℂ_p ⊗ D_{q'}(V^∨)` and of `ℂ_p ⊗ D_{-q}(V^∨)`, whose
dimension is `dim D_q(V)`: the exact sequence
`0 → ℂ_p D_{q'}(V^∨) → ℂ_p ⊗ V^∨ → (ℂ_p D_q(V))^* → 0` (the first term is the orthogonal
complement of `ℂ_p D_q(V)` by dimension count) splits by Tate's `H¹(G_L, ℂ_p(j)) = 0`, `j ≠ 0`.

* `exists_DHT_of_defect`: **lifting along a span of eigenvectors**: if `u_1, …, u_k ∈ ℂ_p ⊗ V`
  are `ℂ_p`-linearly independent with `u_i ∈ D_{q_i}(V)`, `q ≠ q_i`, and `w` satisfies
  `σ w − χ(σ)^{-q} w ∈ ⟨u_i⟩` for all `σ`, then `w − m ∈ D_q(V)` for some `m ∈ ⟨u_i⟩`
  (the coordinates of the defect are continuous crossed homomorphisms into `ℂ_p(q − q_i)`,
  hence coboundaries, `exists_twist_coboundary_GL`);
* `isHodgeTate_dual_of_finrank_add_eq`: **if `dim D_q(V) + dim D_{q'}(V^∨) = dim V`, then `V^∨`
  is Hodge–Tate** with `dim D_{-q}(V^∨) = dim D_q(V)`; lifting the dual basis of a basis of
  `D_q(V)` from `(ℂ_p D_q(V))^*` gives `dim D_q(V)` independent elements of `D_{-q}(V^∨)`;
* `isHodgeTate_of_dual`: `V` is Hodge–Tate if `V^∨` is (`V ≅ V^{∨∨}`).

## References

* [Hong] S. Hong, *Notes on p-adic Hodge theory*, Thm. 3.1.12, Thm. 3.4.10, Thm. 3.4.12.
-/

noncomputable section

open Module TensorProduct

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime]

/-- Coordinate forms of a linearly independent family of a vector space. -/
theorem exists_coordForms {k : Type*} [Field k] {ι : Type*} [Finite ι] [DecidableEq ι]
    {W : Type*} [AddCommGroup W] [Module k W] {u : ι → W} (hu : LinearIndependent k u) :
    ∃ Λ : W →ₗ[k] (ι → k), ∀ i, Λ (u i) = Pi.single i 1 := by
  haveI := Fintype.ofFinite ι
  let b := Basis.span hu
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (b.equivFun.toLinearMap)
  refine ⟨g, fun i => ?_⟩
  have h1 : u i = (Submodule.span k (Set.range u)).subtype (b i) := by
    simp [b, Basis.span_apply]
  rw [h1, ← LinearMap.comp_apply, hg]
  simp [Finsupp.single_eq_pi_single]

theorem coordForms_sum {k : Type*} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι] {W : Type*}
    [AddCommGroup W] [Module k W] {u : ι → W} {Λ : W →ₗ[k] (ι → k)}
    (hΛ : ∀ i, Λ (u i) = Pi.single i 1) (a : ι → k) : Λ (∑ i, a i • u i) = a := by
  rw [map_sum]
  simp only [map_smul, hΛ]
  ext j
  simp [Finset.sum_apply, Pi.single_apply]

theorem eq_sum_coordForms {k : Type*} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {W : Type*} [AddCommGroup W] [Module k W] {u : ι → W} {Λ : W →ₗ[k] (ι → k)}
    (hΛ : ∀ i, Λ (u i) = Pi.single i 1) {x : W} (hx : x ∈ Submodule.span k (Set.range u)) :
    x = ∑ i, Λ x i • u i := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp hx
  rw [coordForms_sum hΛ]

section Lift

variable {L : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] L]
  {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] [FiniteDimensional ℚ_[p] V]
  {ρ : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) V}

/-- **Lifting along a span of eigenvectors** ([Hong, proof of Thm. 3.4.12]): if
`σ w − χ(σ)^{-q} w` lies in the `ℂ_p`-span of independent eigenvectors `u_i ∈ D_{q_i}(V)`,
`q ≠ q_i`, then `w` is congruent modulo that span to an element of `D_q(V)`. -/
theorem exists_DHT_of_defect
    (hcont : ∀ (φ : Module.Dual ℚ_[p] V) (v : V), Continuous fun σ => φ (ρ σ v))
    {ι : Type} [Finite ι] {u : ι → CpTensor ρ} (hu : LinearIndependent ℂ_[p] u)
    {qs : ι → ℤ} (hub : ∀ i, u i ∈ DHT ρ (qs i)) {q : ℤ} (hq : ∀ i, q - qs i ≠ 0)
    {w : CpTensor ρ}
    (hw : ∀ σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p,
      σ • w - kap q σ • w ∈ Submodule.span ℂ_[p] (Set.range u)) :
    ∃ m ∈ Submodule.span ℂ_[p] (Set.range u), w - m ∈ DHT ρ q := by
  classical
  haveI := Fintype.ofFinite ι
  set U := Submodule.span ℂ_[p] (Set.range u) with hU
  obtain ⟨Λ, hΛ⟩ := exists_coordForms hu
  have hsum : ∀ x ∈ U, x = ∑ i, Λ x i • u i := fun x hx => eq_sum_coordForms hΛ hx
  have hmemU : ∀ a : ι → ℂ_[p], ∑ i, a i • u i ∈ U := fun a =>
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hΛinj : ∀ x ∈ U, ∀ y ∈ U, (∀ i, Λ x i = Λ y i) → x = y := by
    intro x hx y hy h
    rw [hsum x hx, hsum y hy]
    simp only [h]
  have hgalU : ∀ σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p, ∀ x ∈ U,
      σ • x = ∑ i, (galCp L σ (Λ x i) * kap (qs i) σ) • u i := by
    intro σ x hx
    conv_lhs => rw [hsum x hx]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [gal_smul_cp_smul, (mem_DHT_iff_kap.mp (hub i)) σ, smul_smul]
  have hkinv : ∀ σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p,
      (kap q σ)⁻¹ = algebraMap ℚ_[p] ℂ_[p] (chiL L q σ) := by
    intro σ
    have := kap_inv_mul q 0 σ
    simp only [kap, neg_zero, chiL_zero, map_one, mul_one, sub_zero] at this
    exact this
  -- the normalised defect
  set c : (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) → CpTensor ρ :=
    fun σ => (kap q σ)⁻¹ • (σ • w) - w with hc
  have hcU : ∀ σ, c σ ∈ U := by
    intro σ
    have : c σ = (kap q σ)⁻¹ • (σ • w - kap q σ • w) := by
      simp only [hc, smul_sub, smul_smul, inv_mul_cancel₀ (kap_ne_zero q σ), one_smul]
    rw [this]
    exact U.smul_mem _ (hw σ)
  have hcoc : ∀ σ τ, c (σ * τ) = c σ + (kap q σ)⁻¹ • σ • c τ := by
    intro σ τ
    have hA : σ • ((kap q τ)⁻¹ • τ • w) = (kap q τ)⁻¹ • σ • τ • w := by
      rw [gal_smul_cp_smul, hkinv τ, galCp_algebraMap]
    simp only [hc]
    rw [mul_smul σ τ w, kap_mul, mul_inv, mul_smul (kap q σ)⁻¹ (kap q τ)⁻¹, smul_sub σ, hA,
      smul_sub]
    abel
  -- coordinates
  set E : ι → (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) → ℂ_[p] := fun i σ => Λ (c σ) i with hE
  have hΛgal : ∀ σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p, ∀ x ∈ U, ∀ i,
      Λ (σ • x) i = galCp L σ (Λ x i) * kap (qs i) σ := by
    intro σ x hx i
    rw [hgalU σ x hx, coordForms_sum hΛ]
  have hEcoc : ∀ i σ τ, E i (σ * τ) = E i σ + chiL L (q - qs i) σ • galCp L σ (E i τ) := by
    intro i σ τ
    simp only [hE]
    rw [hcoc, map_add, Pi.add_apply, map_smul, Pi.smul_apply, hΛgal σ _ (hcU τ), smul_eq_mul,
      Algebra.smul_def, ← kap_inv_mul]
    ring
  have hEcont : ∀ i, Continuous (E i ∘ IntermediateField.fixingSubgroupEquiv L) := by
    intro i
    set Λ' : CpTensor ρ →ₗ[ℂ_[p]] ℂ_[p] := (LinearMap.proj i).comp Λ
    have hform : ∀ σ, E i σ = (kap q σ)⁻¹ * Λ' (σ • w) - Λ' w := by
      intro σ
      simp only [hE, hc, Λ', map_sub, map_smul, LinearMap.comp_apply, LinearMap.coe_proj,
        Function.eval, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have h1 : Continuous fun g : L.fixingSubgroup =>
        (kap q (IntermediateField.fixingSubgroupEquiv L g))⁻¹ := by
      simp_rw [hkinv, chiL_fixingSubgroupEquiv]
      exact (continuous_algebraMap ℚ_[p] ℂ_[p]).comp
        ((continuous_chiPow q).comp continuous_subtype_val)
    have h2 := continuous_form_gal hcont Λ' w
    have : E i ∘ IntermediateField.fixingSubgroupEquiv L = fun g =>
        (kap q (IntermediateField.fixingSubgroupEquiv L g))⁻¹ *
          Λ' (TensorProduct.map (galCpLin L (IntermediateField.fixingSubgroupEquiv L g))
            (ρ (IntermediateField.fixingSubgroupEquiv L g)) w) - Λ' w := by
      funext g
      rw [Function.comp_apply, hform]
      rfl
    rw [this]
    exact (h1.mul h2).sub continuous_const
  -- Tate's theorem on each coordinate
  choose y hy using fun i => exists_twist_coboundary_GL (hq i) (E i) (hEcont i) (hEcoc i)
  set m : CpTensor ρ := ∑ i, y i • u i with hm
  have hmU : m ∈ U := hmemU y
  have hΛm : Λ m = y := coordForms_sum hΛ y
  have hσmU : ∀ σ, σ • m ∈ U := fun σ => by
    rw [hgalU σ m hmU]
    exact hmemU _
  have hceq : ∀ σ, c σ = (kap q σ)⁻¹ • σ • m - m := by
    intro σ
    refine hΛinj _ (hcU σ) _ (U.sub_mem (U.smul_mem _ (hσmU σ)) hmU) fun i => ?_
    change E i σ = _
    rw [hy i σ, map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, hΛgal σ m hmU, hΛm, smul_eq_mul,
      Algebra.smul_def, ← kap_inv_mul]
    ring
  refine ⟨m, hmU, mem_DHT_iff_kap.mpr fun σ => ?_⟩
  have h1 : (kap q σ)⁻¹ • (σ • (w - m)) = w - m := by
    have h := hceq σ
    simp only [hc] at h
    rw [smul_sub, smul_sub]
    exact sub_eq_sub_iff_sub_eq_sub.mp h
  calc σ • (w - m) = kap q σ • ((kap q σ)⁻¹ • (σ • (w - m))) := by
        rw [smul_smul, mul_inv_cancel₀ (kap_ne_zero q σ), one_smul]
    _ = kap q σ • (w - m) := by rw [h1]

end Lift

section Dual

variable {L : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] L]
  {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] [FiniteDimensional ℚ_[p] V]
  {ρ : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) V}

omit [FiniteDimensional ℚ_[p] L] in
/-- Continuity of the contragredient. -/
theorem continuous_dual
    (hcont : ∀ (φ : Module.Dual ℚ_[p] V) (v : V), Continuous fun σ => φ (ρ σ v))
    (Φ : Module.Dual ℚ_[p] (Module.Dual ℚ_[p] V)) (f : Module.Dual ℚ_[p] V) :
    Continuous fun σ => Φ (ρ.dual σ f) := by
  obtain ⟨v, rfl⟩ := (Module.evalEquiv ℚ_[p] V).surjective Φ
  have h : (fun σ => (Module.evalEquiv ℚ_[p] V v) (ρ.dual σ f)) = fun σ => f (ρ σ⁻¹ v) := by
    funext σ
    rfl
  rw [h]
  exact (hcont f v).comp continuous_inv

omit [FiniteDimensional ℚ_[p] L] in
theorem kap_inv_eq (q : ℤ) (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) : kap q σ⁻¹ = kap (-q) σ := by
  rw [kap, kap, chiL_inv, neg_neg]

set_option maxHeartbeats 800000 in
-- the proof is long and elaborates many large `ℂ_p ⊗ V^∨` terms
/-- **[Hong, proof of Thm. 3.4.12]**: if `dim D_q(V) + dim D_{q'}(V^∨) = dim V` with
`q + q' ≠ 0`, then `V^∨` is Hodge–Tate and `dim D_{-q}(V^∨) = dim D_q(V)`. -/
theorem isHodgeTate_dual_of_finrank_add_eq
    (hcont : ∀ (φ : Module.Dual ℚ_[p] V) (v : V), Continuous fun σ => φ (ρ σ v))
    {q q' : ℤ} (hqq' : q + q' ≠ 0)
    (h : finrank L (DHT ρ q) + finrank L (DHT ρ.dual q') = finrank ℚ_[p] V) :
    IsHodgeTate ρ.dual ∧ finrank L (DHT ρ.dual (-q)) = finrank L (DHT ρ q) := by
  classical
  set n := finrank L (DHT ρ q)
  set n' := finrank L (DHT ρ.dual q')
  set b := Module.finBasis L (DHT ρ q)
  set b' := Module.finBasis L (DHT ρ.dual q')
  set e : Fin n → CpTensor ρ := fun i => ((b i : DHT ρ q) : CpTensor ρ)
  set u : Fin n' → CpTensor ρ.dual := fun j => ((b' j : DHT ρ.dual q') : CpTensor ρ.dual)
  have he : LinearIndependent ℂ_[p] e :=
    SerreTate.linearIndependent_of_eigen_single (htSetup L) (smul_distrib_cpTensor ρ) q e
      (fun i => (b i).2) (b.linearIndependent.map' (DHT ρ q).subtype (Submodule.ker_subtype _))
  have hu : LinearIndependent ℂ_[p] u :=
    SerreTate.linearIndependent_of_eigen_single (htSetup L) (smul_distrib_cpTensor ρ.dual) q' u
      (fun j => (b' j).2)
      (b'.linearIndependent.map' (DHT ρ.dual q').subtype (Submodule.ker_subtype _))
  set P := cpDualEquiv ρ
  obtain ⟨Λ, hΛ⟩ := exists_coordForms he
  set wv : Fin n → CpTensor ρ.dual := fun j => P.symm ((LinearMap.proj j).comp Λ)
  have hwv : ∀ i j, P (wv j) (e i) = Pi.single (M := fun _ => ℂ_[p]) i 1 j := by
    intro i j
    simp only [wv, LinearEquiv.apply_symm_apply, LinearMap.comp_apply, hΛ, LinearMap.coe_proj,
      Function.eval]
  -- the orthogonal complement of `ℂ_p D_q(V)`
  set Ue := Submodule.span ℂ_[p] (Set.range e)
  set X : Submodule ℂ_[p] (CpTensor ρ.dual) := Ue.dualAnnihilator.comap P.toLinearMap
  have hX : ∀ x, x ∈ X ↔ ∀ i, P x (e i) = 0 := by
    intro x
    change P x ∈ Ue.dualAnnihilator ↔ _
    rw [Submodule.mem_dualAnnihilator]
    constructor
    · intro hx i
      exact hx _ (Submodule.subset_span ⟨i, rfl⟩)
    · intro hx w hw
      refine Submodule.span_induction (p := fun w _ => P x w = 0) ?_ ?_ ?_ ?_ hw
      · rintro _ ⟨i, rfl⟩
        exact hx i
      · exact map_zero _
      · intro a b _ _ ha hb
        rw [map_add, ha, hb, add_zero]
      · intro a b _ hb
        rw [map_smul, hb, smul_zero]
  set Uu := Submodule.span ℂ_[p] (Set.range u)
  have hle : Uu ≤ X := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact (hX _).mpr fun i => dualEquiv_eq_zero_of_mem_DHT ρ hqq' (b i).2 (b' j).2
  have hfX : finrank ℂ_[p] X = finrank ℚ_[p] V - n := by
    have h1 : X = Ue.dualAnnihilator.map P.symm.toLinearMap :=
      Submodule.comap_equiv_eq_map_symm P Ue.dualAnnihilator
    have h2 : finrank ℂ_[p] X = finrank ℂ_[p] Ue.dualAnnihilator := by
      rw [h1]
      exact LinearEquiv.finrank_map_eq P.symm _
    have h3 := Subspace.finrank_add_finrank_dualAnnihilator_eq Ue
    rw [finrank_cpTensor, finrank_span_eq_card he, Fintype.card_fin] at h3
    omega
  have hfU : finrank ℂ_[p] Uu = n' := by
    rw [finrank_span_eq_card hu, Fintype.card_fin]
  have hUX : Uu = X := Submodule.eq_of_le_of_finrank_eq hle (by rw [hfU, hfX]; omega)
  -- the defect lies in `X = ℂ_p D_{q'}(V^∨)`
  have hPgal : ∀ (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) x i,
      P (σ • x) (e i) = kap (-q) σ * galCp L σ (P x (e i)) := by
    intro σ x i
    have hei : e i = σ • (σ⁻¹ • e i) := (tensorAct_inv_cancel ρ σ (e i)).symm
    have hinv : σ⁻¹ • e i = kap q σ⁻¹ • e i := (mem_DHT_iff_kap.mp (b i).2) σ⁻¹
    have hg := dualEquiv_gal ρ σ x (σ⁻¹ • e i)
    change P (σ • x) (σ • (σ⁻¹ • e i)) = galCp L σ (P x (σ⁻¹ • e i)) at hg
    rw [← hei, hinv, (P x).map_smul, smul_eq_mul, map_mul, galCp_kap, kap_inv_eq] at hg
    exact hg
  have hdef : ∀ j, ∀ σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p, σ • wv j - kap (-q) σ • wv j ∈ Uu := by
    intro j σ
    rw [hUX, hX]
    intro i
    rw [map_sub, LinearMap.sub_apply, hPgal, P.map_smul, LinearMap.smul_apply, hwv, smul_eq_mul]
    have : galCp L σ (Pi.single (M := fun _ => ℂ_[p]) i 1 j) =
        Pi.single (M := fun _ => ℂ_[p]) i 1 j := by
      by_cases hij : j = i
      · subst hij
        rw [Pi.single_eq_same, map_one]
      · rw [Pi.single_eq_of_ne hij, map_zero]
    rw [this, sub_self]
  have hqs : ∀ _j : Fin n', -q - q' ≠ 0 := fun _ => by omega
  have hlift := fun j => exists_DHT_of_defect (continuous_dual hcont) hu
    (qs := fun _ => q') (fun j => (b' j).2) hqs (hdef j)
  choose m hmU hmD using hlift
  set W : Fin n → CpTensor ρ.dual := fun j => wv j - m j
  have hW : ∀ i j, P (W j) (e i) = Pi.single (M := fun _ => ℂ_[p]) i 1 j := by
    intro i j
    have hm0 : P (m j) (e i) = 0 := (hX _).mp (hUX ▸ hmU j) i
    simp only [W, map_sub, LinearMap.sub_apply, hm0, sub_zero, hwv]
  -- the `W_j` are independent elements of `D_{-q}(V^∨)`
  set ev : CpTensor ρ.dual →ₗ[ℂ_[p]] (Fin n → ℂ_[p]) :=
    LinearMap.pi fun i => (LinearMap.applyₗ (e i)).comp P.toLinearMap
  have hev : ∀ j, ev (W j) = Pi.basisFun ℂ_[p] (Fin n) j := by
    intro j
    ext i
    simp only [ev, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.applyₗ_apply_apply,
      LinearEquiv.coe_coe, hW, Pi.basisFun_apply]
    simp [Pi.single_apply, eq_comm]
  have hWC : LinearIndependent ℂ_[p] W := by
    refine LinearIndependent.of_comp ev ?_
    have : ev ∘ W = Pi.basisFun ℂ_[p] (Fin n) := funext hev
    rw [this]
    exact (Pi.basisFun ℂ_[p] (Fin n)).linearIndependent
  have hWL : LinearIndependent L W :=
    hWC.restrict_scalars' L
  set Wd : Fin n → DHT ρ.dual (-q) := fun j => ⟨W j, hmD j⟩
  have hWd : LinearIndependent L Wd :=
    LinearIndependent.of_comp (DHT ρ.dual (-q)).subtype hWL
  have hn : n ≤ finrank L (DHT ρ.dual (-q)) := by
    have := hWd.fintype_card_le_finrank
    rwa [Fintype.card_fin] at this
  -- dimension count
  have hne : q' ≠ -q := by omega
  set S := (finite_support_DHT ρ.dual).toFinset ∪ {q', -q}
  have hS : Function.support (fun q => finrank L (DHT ρ.dual q)) ⊆ S := by
    intro x hx
    exact Finset.mem_union_left _ ((Set.Finite.mem_toFinset _).mpr hx)
  have hsum := htDim_eq_sum ρ.dual hS
  have hsub : ∑ x ∈ ({q', -q} : Finset ℤ), finrank L (DHT ρ.dual x) ≤
      ∑ x ∈ S, finrank L (DHT ρ.dual x) :=
    Finset.sum_le_sum_of_subset (Finset.subset_union_right)
  rw [Finset.sum_pair hne] at hsub
  have hle' := htDim_le ρ.dual
  rw [Subspace.dual_finrank_eq] at hle'
  refine ⟨?_, ?_⟩
  · unfold IsHodgeTate
    rw [Subspace.dual_finrank_eq]
    omega
  · omega

/-- **`V` is Hodge–Tate if `V^∨` is** (`V ≅ V^{∨∨}`). -/
theorem isHodgeTate_of_dual (h : IsHodgeTate ρ.dual) : IsHodgeTate ρ := by
  have h2 := isHodgeTate_dual ρ.dual h
  refine (isHodgeTate_iff_of_equiv (Module.evalEquiv ℚ_[p] V) (fun σ => ?_)).mpr h2
  refine LinearMap.ext fun v => LinearMap.ext fun f => ?_
  change f (ρ σ v) = f (ρ (σ⁻¹)⁻¹ v)
  rw [inv_inv]

end Dual

end PadicHodge
