/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.HodgeTate.Dual
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Orthogonality of Hodge–Tate invariants of `V` and `V^∨`

This is the linear-algebra step (3.11) of Tate's proof of [Hong, Thm. 3.4.10].
Let `V` be a finite-dimensional `ℚ_p`-representation of `G_L` and `V^∨ = Hom_{ℚ_p}(V, ℚ_p)` the
contragredient (`Representation.dual`). The natural `ℂ_p`-bilinear perfect pairing
`(ℂ_p ⊗ V^∨) × (ℂ_p ⊗ V) → ℂ_p` (`dualEquiv`, `HodgeTate/Dual.lean`) is `G_L`-equivariant
(`dualEquiv_gal`). Hence if `x ∈ D_{q'}(V^∨)` and `w ∈ D_q(V)` then `c = ⟨x, w⟩` satisfies
`σ c = χ(σ)^{-(q+q')} c`, so `c = 0` for `q + q' ≠ 0` by Tate's theorem
`ℂ_p(j)^{G_L} = 0`, `j ≠ 0` ([Hong, Thm. 3.1.12], `htSetup.tate`) (`dualEquiv_eq_zero_of_mem_DHT`).
By the Serre–Tate lemma ([Hong, Lemma 3.1.13], [BC, Lemma 2.3.1];
`SerreTate.linearIndependent_of_eigen_single`) an `L`-basis of `D_q(V)` stays
`ℂ_p`-linearly independent, so the `ℂ_p`-spans of `D_q(V)` and of `D_{q'}(V^∨)` are orthogonal
subspaces of dimensions `dim_L D_q(V)` and `dim_L D_{q'}(V^∨)` under a perfect pairing:

* `finrank_DHT_add_finrank_DHT_dual_le`: for `q + q' ≠ 0`,
  `dim_L D_q(V) + dim_L D_{q'}(V^∨) ≤ dim_{ℚ_p} V`. For `(q, q') = (-1, 0)` this is the bound
  `dim (V ⊗ ℂ_p(-1))^{G_L} + dim (V^∨ ⊗ ℂ_p)^{G_L} ≤ dim V` of [Hong, proof of Thm. 3.4.10],
  after (3.11).
* `bijective_of_finrank_le_add` (and `bijective_of_finrank_le_add_fin` for `L^d`, `L^{d'}`):
  if `M ↪ D_q(V)` and `M' ↪ D_{q'}(V^∨)` are `L`-linear injections with
  `dim V ≤ dim M + dim M'`, both are bijective; this is "equality in (3.10), hence in (3.9)" of
  [Hong, proof of Thm. 3.4.10].
-/

noncomputable section

open Module TensorProduct

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime] {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
  [FiniteDimensional ℚ_[p] L] {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
  [FiniteDimensional ℚ_[p] V] (ρ : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) V)

/-- `dualEquiv` viewed on the type synonyms: `ℂ_p ⊗ V^∨ ≃ Hom_{ℂ_p}(ℂ_p ⊗ V, ℂ_p)`. -/
def cpDualEquiv : CpTensor ρ.dual ≃ₗ[ℂ_[p]] Dual ℂ_[p] (CpTensor ρ) :=
  dualEquiv (V := V)

omit [FiniteDimensional ℚ_[p] L] in
theorem dualEquiv_smul_smul (a b : ℂ_[p]) (x : ℂ_[p] ⊗[ℚ_[p]] Dual ℚ_[p] V)
    (w : ℂ_[p] ⊗[ℚ_[p]] V) : dualEquiv (V := V) (a • x) (b • w) = a * (b * dualEquiv x w) := by
  rw [LinearEquiv.map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul]

/-- **Equivariance kills the pairing**: for `q + q' ≠ 0`, the pairing of `D_{q'}(V^∨)` with
`D_q(V)` vanishes, as it lands in `ℂ_p(-(q+q'))^{G_L} = 0` ([Hong, Thm. 3.1.12]). -/
theorem dualEquiv_eq_zero_of_mem_DHT {q q' : ℤ} (hqq' : q + q' ≠ 0) {w : CpTensor ρ}
    (hw : w ∈ DHT ρ q) {x : CpTensor ρ.dual} (hx : x ∈ DHT ρ.dual q') :
    cpDualEquiv ρ x w = 0 := by
  refine (htSetup L).tate (q + q') hqq' _ fun σ => ?_
  have h := dualEquiv_gal ρ σ x w
  have hx' : TensorProduct.map (galCpLin L σ) (ρ.dual σ) x =
      algebraMap L ℂ_[p] ((htSetup L).ψ q' σ) • x := hx σ
  have hw' : TensorProduct.map (galCpLin L σ) (ρ σ) w =
      algebraMap L ℂ_[p] ((htSetup L).ψ q σ) • w := hw σ
  have e : dualEquiv (V := V) (algebraMap L ℂ_[p] ((htSetup L).ψ q' σ) • x)
      (algebraMap L ℂ_[p] ((htSetup L).ψ q σ) • w) = algebraMap L ℂ_[p] ((htSetup L).ψ q' σ) *
        (algebraMap L ℂ_[p] ((htSetup L).ψ q σ) * dualEquiv (V := V) x w) :=
    dualEquiv_smul_smul _ _ _ _
  rw [hx', hw', e] at h
  change galCp L σ (dualEquiv (V := V) x w) =
    algebraMap L ℂ_[p] ((htSetup L).ψ (q + q') σ) * dualEquiv (V := V) x w
  rw [← h, (htSetup L).ψ_add, map_mul]
  ring

/-- **Orthogonality bound** (step (3.11) of [Hong, proof of Thm. 3.4.10]): for `q + q' ≠ 0`,
`dim_L D_q(V) + dim_L D_{q'}(V^∨) ≤ dim_{ℚ_p} V`. -/
theorem finrank_DHT_add_finrank_DHT_dual_le {q q' : ℤ} (hqq' : q + q' ≠ 0) :
    finrank L (DHT ρ q) + finrank L (DHT ρ.dual q') ≤ finrank ℚ_[p] V := by
  classical
  set b := Module.finBasis L (DHT ρ q)
  set b' := Module.finBasis L (DHT ρ.dual q')
  set e : Fin (finrank L (DHT ρ q)) → CpTensor ρ := fun i => ((b i : DHT ρ q) : CpTensor ρ)
  set φ : Fin (finrank L (DHT ρ.dual q')) → Dual ℂ_[p] (CpTensor ρ) :=
    fun j => cpDualEquiv ρ ((b' j : DHT ρ.dual q') : CpTensor ρ.dual)
  -- Serre–Tate: `L`-bases of the invariants stay `ℂ_p`-linearly independent
  have he : LinearIndependent ℂ_[p] e :=
    SerreTate.linearIndependent_of_eigen_single (htSetup L) (smul_distrib_cpTensor ρ) q e
      (fun i => (b i).2) (b.linearIndependent.map' (DHT ρ q).subtype (Submodule.ker_subtype _))
  have hx : LinearIndependent ℂ_[p] (fun j => ((b' j : DHT ρ.dual q') : CpTensor ρ.dual)) :=
    SerreTate.linearIndependent_of_eigen_single (htSetup L) (smul_distrib_cpTensor ρ.dual) q' _
      (fun j => (b' j).2)
      (b'.linearIndependent.map' (DHT ρ.dual q').subtype (Submodule.ker_subtype _))
  have hφ : LinearIndependent ℂ_[p] φ :=
    hx.map' (cpDualEquiv ρ).toLinearMap (cpDualEquiv ρ).ker
  -- the spans are orthogonal
  set U := Submodule.span ℂ_[p] (Set.range e)
  have hle : Submodule.span ℂ_[p] (Set.range φ) ≤ U.dualAnnihilator := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_dualAnnihilator]
    intro w hw
    have hU : U ≤ LinearMap.ker (φ j) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact dualEquiv_eq_zero_of_mem_DHT ρ hqq' (b i).2 (b' j).2
    exact hU hw
  have h1 : finrank ℂ_[p] U = Fintype.card (Fin (finrank L (DHT ρ q))) :=
    finrank_span_eq_card he
  have h2 : finrank ℂ_[p] (Submodule.span ℂ_[p] (Set.range φ)) =
      Fintype.card (Fin (finrank L (DHT ρ.dual q'))) := finrank_span_eq_card hφ
  have h3 := Submodule.finrank_mono hle
  have h4 := Subspace.finrank_add_finrank_dualAnnihilator_eq U
  rw [finrank_cpTensor] at h4
  simp only [Fintype.card_fin] at h1 h2
  omega

/-- **Equality case** ("equality in (3.10), hence in (3.9)", [Hong, proof of Thm. 3.4.10]):
if `M ↪ D_q(V)` and `M' ↪ D_{q'}(V^∨)` are `L`-linear injections, `q + q' ≠ 0`, and
`dim_{ℚ_p} V ≤ dim_L M + dim_L M'`, then both injections are bijective, and
`dim_L D_q(V) + dim_L D_{q'}(V^∨) = dim_{ℚ_p} V`. -/
theorem bijective_of_finrank_le_add {q q' : ℤ} (hqq' : q + q' ≠ 0) {M M' : Type*}
    [AddCommGroup M] [Module L M] [AddCommGroup M'] [Module L M']
    (f : M →ₗ[L] DHT ρ q) (f' : M' →ₗ[L] DHT ρ.dual q') (hf : Function.Injective f)
    (hf' : Function.Injective f') (h : finrank ℚ_[p] V ≤ finrank L M + finrank L M') :
    Function.Bijective f ∧ Function.Bijective f' ∧
      finrank L (DHT ρ q) + finrank L (DHT ρ.dual q') = finrank ℚ_[p] V := by
  haveI : FiniteDimensional L M := FiniteDimensional.of_injective f hf
  haveI : FiniteDimensional L M' := FiniteDimensional.of_injective f' hf'
  have b := finrank_DHT_add_finrank_DHT_dual_le ρ hqq'
  have i1 := LinearMap.finrank_le_finrank_of_injective hf
  have i2 := LinearMap.finrank_le_finrank_of_injective hf'
  have e1 : finrank L M = finrank L (DHT ρ q) := by omega
  have e2 : finrank L M' = finrank L (DHT ρ.dual q') := by omega
  exact ⟨⟨hf, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank e1).mp hf⟩,
    ⟨hf', (LinearMap.injective_iff_surjective_of_finrank_eq_finrank e2).mp hf'⟩, by omega⟩

/-- The form used in Tate's proof ([Hong, (3.9)–(3.11)]): `L`-linear injections
`L^d ↪ D_{-1}(V) = (V ⊗ ℂ_p(-1))^{G_L}` and `L^{d'} ↪ D_0(V^∨) = (V^∨ ⊗ ℂ_p)^{G_L}` with
`dim V ≤ d + d'` are bijective, and `dim D_{-1}(V) = d`, `dim D_0(V^∨) = d'`. -/
theorem bijective_of_finrank_le_add_fin {d d' : ℕ}
    (f : (Fin d → L) →ₗ[L] DHT ρ (-1)) (f' : (Fin d' → L) →ₗ[L] DHT ρ.dual 0)
    (hf : Function.Injective f) (hf' : Function.Injective f') (h : finrank ℚ_[p] V ≤ d + d') :
    Function.Bijective f ∧ Function.Bijective f' ∧
      finrank L (DHT ρ (-1)) = d ∧ finrank L (DHT ρ.dual 0) = d' := by
  have h' : finrank ℚ_[p] V ≤ finrank L (Fin d → L) + finrank L (Fin d' → L) := by
    simpa only [Module.finrank_fin_fun] using h
  obtain ⟨b1, b2, -⟩ := bijective_of_finrank_le_add ρ (by norm_num) f f' hf hf' h'
  refine ⟨b1, b2, ?_, ?_⟩
  · rw [← (LinearEquiv.ofBijective f b1).finrank_eq, Module.finrank_fin_fun]
  · rw [← (LinearEquiv.ofBijective f' b2).finrank_eq, Module.finrank_fin_fun]

end PadicHodge
