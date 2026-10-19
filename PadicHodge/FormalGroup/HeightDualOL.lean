/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.CartierDualOL
import PadicHodge.FormalGroup.DiscFormula
import PadicHodge.HodgeTate.OrthSplit

/-!
# `h = d + d^∨` and Tate's Hodge–Tate decomposition for non-connected `G` over `O_{K'}`

Let `G` be a `p`-divisible group of height `h` over `O_L = O_{K'}` (not necessarily connected),
`G⁰ ≅ F[p^∞]` with `F` of dimension `d`, `G^∨ = G.dualPDivGen` its Cartier dual
(`GroupScheme/CartierDualGen.lean`) and `(G^∨)⁰ ≅ F'[p^∞]` with `F'` of dimension `d^∨`
(Serre–Tate over `O_L`, `PDivGroup.exists_connPart_iso_OL`). Write `V = V_p(G_L)`.

* `dim_L D_0(V^∨) = d^∨` (`finrank_DHT_dual_zero_OL`): [Hong, Cor. 3.4.11] for `G^∨`
  (`TateNonConnOL`) and `V_p(G^∨) ≅ V^∨ ⊗ ℚ_p(1)` (`tateRepDualEquivOL`), via the abstract
  `finrank_DHT_dual_zero_eq` (`D_{-1}(W^∨(1)) ≅ D_0(W^∨)`).
* **`h ≤ d + d^∨` from integrals** (`height_le_add_OL`): `G_1` has an integral `Λ` with
  `ε(Λ) = p^d` and `G_1^∨` one, `λ`, with `ε(λ) = λ(1) = p^{d^∨}` (from the connected parts,
  [Hong, remark after Prop. 3.5.1]; `exists_isIntegral_counit_OL`). The trace formula
  `(Tr ⊗ id)((x ⊗ 1)Δ(Λ)) = ε(Λ) S(x)` (`G_1` is étale over `ℚ̄_p`) gives
  `ε(Λ) λ(1) = λ(Λ) · |G_1|` (`FFGroupScheme.counit_mul_eq_of_dual_integral`), i.e.
  `p^{d + d^∨} = λ(Λ) p^h` with `λ(Λ) ∈ O_L`; as `p` is not a unit, `h ≤ d + d^∨`. (This replaces
  the Frobenius/Verschiebung argument of [Hong, proof of Thm. 2.2.19] on the special fibre.)
* `d + d^∨ ≤ h` (orthogonality (3.11) of [Hong, proof of Thm. 3.4.10],
  `finrank_DHT_add_finrank_DHT_dual_le`), hence **[Hong, Thm. 2.2.19] `h = d + d^∨`**
  (`height_eq_add_OL`, `exists_height_eq_add_OL`).
* **Tate's Hodge–Tate decomposition for non-connected `G`** ([Hong, Thm. 3.4.12, Cor. 3.4.14],
  `hodgeTate_decomposition_nonconn_OL`): `V^∨` (and `V`) is Hodge–Tate,
  `dim D_0(V^∨) = d^∨ = h - d`,  `dim D_1(V^∨) = d` (`isHodgeTate_dual_of_finrank_add_eq`).

## References

* [Hong] S. Hong, *Notes on p-adic Hodge theory*, Thm. 2.2.19, Prop. 3.4.6, Thm. 3.4.10,
  Cor. 3.4.11, Thm. 3.4.12, Cor. 3.4.14, Prop. 3.5.1.
-/

noncomputable section

open Module TensorProduct

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### `ε(Λ) λ(1) = λ(Λ) |G|` -/

namespace FFGroupScheme

variable {R : Type} [CommRing R] [Nontrivial R] (G : FFGroupScheme R)

/-- **`ε(Λ) λ(1) = λ(Λ) N`** under the trace formula `(Tr ⊗ id)((x ⊗ 1)Δ(Λ)) = c S(x)`, for a
dual integral `λ` (`(id ⊗ λ)Δ(a) = λ(a)`), `N = |G|`. -/
theorem counit_mul_eq_of_dual_integral {Λ : G.A} {c : R}
    (h1 : ∀ x : G.A, G.trL ((x ⊗ₜ 1) * Coalgebra.comul (R := R) Λ) = c • HopfAlgebra.antipode R x)
    (l : G.A →ₗ[R] R)
    (hl : ∀ a, TensorProduct.rid R G.A (l.lTensor G.A (Coalgebra.comul (R := R) a)) =
      algebraMap R G.A (l a)) :
    c * l 1 = l Λ * finrank R G.A := by
  have := congrArg l (h1 1)
  rw [map_smul, smul_eq_mul, trace_trL, rid_lTensor_mul, hl, mul_comm (1 : G.A),
    ← Algebra.smul_def, map_smul, smul_eq_mul, HopfAlgebra.antipode_one] at this
  have htr : Algebra.trace R G.A 1 = finrank R G.A := by
    rw [← map_one (algebraMap R G.A), Algebra.trace_algebraMap, nsmul_eq_mul, mul_one]
  rw [htr] at this
  exact this.symm

end FFGroupScheme

/-! ### `D_{-1}(W^∨(1)) ≅ D_0(W^∨)` -/

section Abstract

variable {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
  {V W : Type*} [AddCommGroup V] [Module ℚ_[p] V] [AddCommGroup W] [Module ℚ_[p] W]
  {ρV : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) V}
  {ρW : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) W}
  (e : V ≃ₗ[ℚ_[p]] Dual ℚ_[p] W ⊗[ℚ_[p]] ℚ_[p])
  (he : ∀ σ, (e : V →ₗ[ℚ_[p]] _) ∘ₗ ρV σ = (ρW.dual.tprod (charRep L 1) σ) ∘ₗ e)

/-- `V ≅ W^∨` (forgetting the twist). -/
def untwistEquiv : V ≃ₗ[ℚ_[p]] Dual ℚ_[p] W := e ≪≫ₗ TensorProduct.rid ℚ_[p] _

include he in
theorem untwistEquiv_gal (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (x : V) :
    untwistEquiv e (ρV σ x) = chiL L 1 σ • ρW.dual σ (untwistEquiv e x) := by
  change TensorProduct.rid ℚ_[p] _ (e (ρV σ x)) = _
  rw [show e (ρV σ x) = (ρW.dual.tprod (charRep L 1) σ) (e x) from
    LinearMap.congr_fun (he σ) x, rid_tprod_charRep]
  rfl

include he in
theorem untwistEquiv_gal' (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (x : V) :
    ρW.dual σ (untwistEquiv e x) = chiL L (-1) σ • untwistEquiv e (ρV σ x) := by
  rw [untwistEquiv_gal e he, smul_smul, ← chiL_add, neg_add_cancel, chiL_zero, one_smul]

include he in
theorem untwistEquiv_symm_gal (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (y : Dual ℚ_[p] W) :
    ρV σ ((untwistEquiv e).symm y) = chiL L 1 σ • (untwistEquiv e).symm (ρW.dual σ y) := by
  apply (untwistEquiv e).injective
  rw [untwistEquiv_gal e he, LinearEquiv.apply_symm_apply, map_smul,
    LinearEquiv.apply_symm_apply]

include he in
/-- **`dim D_0(W^∨) = dim D_{-1}(V)`** for `V ≅ W^∨ ⊗ ℚ_p(1)`. -/
theorem finrank_DHT_dual_zero_eq [FiniteDimensional ℚ_[p] L] [FiniteDimensional ℚ_[p] V]
    [FiniteDimensional ℚ_[p] W] :
    finrank L (DHT ρW.dual 0) = finrank L (DHT ρV (-1)) :=
  le_antisymm
    (LinearMap.finrank_le_finrank_of_injective
      (DHTtwistMap_injective 1 (f := ((untwistEquiv e).symm : _ →ₗ[ℚ_[p]] _))
        (fun σ y => untwistEquiv_symm_gal e he σ y) (q := 0) (q' := -1) (by norm_num)
        (untwistEquiv e).symm.injective))
    (LinearMap.finrank_le_finrank_of_injective
      (DHTtwistMap_injective (-1) (f := ((untwistEquiv e) : _ →ₗ[ℚ_[p]] _))
        (fun σ x => untwistEquiv_gal' e he σ x) (q := -1) (q' := 0) (by norm_num)
        (untwistEquiv e).injective))

/-- `dim D_1(V^∨) = dim D_{-1}(V)` if `dim D_{-1}(V) + dim D_0(V^∨) = dim V`. -/
theorem finrank_DHT_dual_one_of_add_eq [FiniteDimensional ℚ_[p] L] [FiniteDimensional ℚ_[p] V]
    {ρ : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) V}
    (hcont : ∀ (φ : Module.Dual ℚ_[p] V) (v : V), Continuous fun σ => φ (ρ σ v))
    (h : finrank L (DHT ρ (-1)) + finrank L (DHT ρ.dual 0) = finrank ℚ_[p] V) :
    finrank L (DHT ρ.dual 1) = finrank L (DHT ρ (-1)) := by
  have := (isHodgeTate_dual_of_finrank_add_eq hcont (q := -1) (q' := 0) (by norm_num) h).2
  exact this

end Abstract

namespace PDivGroup

open FFGroupScheme

variable {L : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] L]

local notation "K" => PadicAlgCl p

-- the shortcut instances of `TateNonConnOL`, so that its statements match syntactically
attribute [local instance high] instAddCommGroupTateL instModuleTateL

omit [FiniteDimensional ℚ_[p] L] in
/-- Shortcut instance (avoids a slow search through normed-space instances on `L`). -/
local instance (priority := high) instModuleDHT' {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
    (ρ : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) V) (q : ℤ) :
    Module L (DHT ρ q) :=
  (DHT ρ q).module

omit [FiniteDimensional ℚ_[p] L] in
/-- Shortcut instance (avoids a slow search through normed-space instances on `L`). -/
local instance (priority := high) instAddCommGroupDHT' {V : Type*} [AddCommGroup V]
    [Module ℚ_[p] V] (ρ : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) V) (q : ℤ) :
    AddCommGroup (DHT ρ q) :=
  (DHT ρ q).addCommGroup

variable (G : PDivGroup (OL L) p)

/-! ### `dim D_0(V^∨) = d^∨` -/

/-- **`dim_L D_0(V_p(G_L)^∨) = d^∨`**, the dimension of the connected part of the Cartier dual
`G^∨` ([Hong, Cor. 3.4.11] for `G^∨` and [Hong, Prop. 3.4.6]). -/
theorem finrank_DHT_dual_zero_OL {d' : ℕ} (P' : PDivFGL (OL L) d' p)
    (φ' : Hom G.dualPDivGen.connPart P'.pdivGroup) (ψ' : Hom P'.pdivGroup G.dualPDivGen.connPart)
    (h1 : φ'.comp ψ' = Hom.id _) (h2 : ψ'.comp φ' = Hom.id _) :
    finrank L (DHT (G.baseChange L).tateRepOver.dual 0) = d' := by
  have h := finrank_DHT_dual_zero_eq (ρV := (G.dualPDivGen.baseChange L).tateRepOver)
    (ρW := (G.baseChange L).tateRepOver) G.tateRepDualEquivOL G.tateRepDualEquivOL_gal
  rw [h]
  exact G.dualPDivGen.finrank_DHT_tateRepOver_neg_one_of_iso_OL P' φ' ψ' h1 h2

/-- **`d + d^∨ ≤ h`** (orthogonality, step (3.11) of [Hong, proof of Thm. 3.4.10]). -/
theorem add_le_height_OL {d d' : ℕ} (P : PDivFGL (OL L) d p)
    (φ : Hom G.connPart P.pdivGroup) (ψ : Hom P.pdivGroup G.connPart)
    (hφψ : φ.comp ψ = Hom.id _) (hψφ : ψ.comp φ = Hom.id _) (P' : PDivFGL (OL L) d' p)
    (φ' : Hom G.dualPDivGen.connPart P'.pdivGroup) (ψ' : Hom P'.pdivGroup G.dualPDivGen.connPart)
    (h1 : φ'.comp ψ' = Hom.id _) (h2 : ψ'.comp φ' = Hom.id _) :
    d + d' ≤ G.height := by
  have h := finrank_DHT_add_finrank_DHT_dual_le (G.baseChange L).tateRepOver
    (q := -1) (q' := 0) (by norm_num)
  have e1 := G.finrank_DHT_tateRepOver_neg_one_of_iso_OL P φ ψ hφψ hψφ
  have e2 := G.finrank_DHT_dual_zero_OL P' φ' ψ' h1 h2
  have e3 := (G.baseChange L).finrank_tateRep
  have e4 : (G.baseChange L).height = G.height := rfl
  omega

/-! ### `h ≤ d + d^∨` via integrals -/

/-- **An integral of `G_v` with counit `p^{vd}`**, `d` the dimension of `G⁰ ≅ F[p^∞]`. -/
theorem exists_isIntegral_counit_OL {d : ℕ} (P : PDivFGL (OL L) d p)
    (φ : Hom G.connPart P.pdivGroup) (ψ : Hom P.pdivGroup G.connPart)
    (hφψ : φ.comp ψ = Hom.id _) (hψφ : ψ.comp φ = Hom.id _) (v : ℕ) :
    ∃ Λ : (G.G v).A, (G.G v).IsIntegral Λ ∧
      Coalgebra.counit (R := OL L) Λ = ((p ^ v : ℕ) : OL L) ^ d := by
  have hbij : Function.Bijective (φ.f v) := by
    refine ⟨fun x y hxy => ?_, fun y => ⟨ψ.f v y, ?_⟩⟩
    · have h1 := congrArg (fun f : PDivGroup.Hom _ _ => f.f v x) hφψ
      have h2 := congrArg (fun f : PDivGroup.Hom _ _ => f.f v y) hφψ
      simp only at h1 h2
      change (ψ.f v) ((φ.f v) x) = x at h1
      change (ψ.f v) ((φ.f v) y) = y at h2
      rw [← h1, ← h2, hxy]
    · exact congrArg (fun f : PDivGroup.Hom _ _ => f.f v y) hψφ
  have hΛ0 := FFGroupScheme.IsIntegral.map (φ.f v) hbij.2 (P.isIntegral_layerDet v)
  obtain ⟨Λ, hΛ, hΛc⟩ := (G.G v).exists_isIntegral_of_connectedComponent hΛ0
  exact ⟨Λ, hΛ, hΛc.trans ((counit_map _ _).trans (P.counit_layerDet v))⟩

/-- **`h ≤ d + d^∨`** ([Hong, Thm. 2.2.19], one inequality), from integrals of `G_1` and `G_1^∨`:
`p^{d + d^∨} = λ(Λ) p^h` with `λ(Λ) ∈ O_L`. -/
theorem height_le_add_OL {d d' : ℕ} (P : PDivFGL (OL L) d p)
    (φ : Hom G.connPart P.pdivGroup) (ψ : Hom P.pdivGroup G.connPart)
    (hφψ : φ.comp ψ = Hom.id _) (hψφ : ψ.comp φ = Hom.id _) (P' : PDivFGL (OL L) d' p)
    (φ' : Hom G.dualPDivGen.connPart P'.pdivGroup) (ψ' : Hom P'.pdivGroup G.dualPDivGen.connPart)
    (h1 : φ'.comp ψ' = Hom.id _) (h2 : ψ'.comp φ' = Hom.id _) :
    G.height ≤ d + d' := by
  obtain ⟨Λ, hΛ, hΛc⟩ := G.exists_isIntegral_counit_OL P φ ψ hφψ hψφ 1
  obtain ⟨l, hl, hlc⟩ := G.dualPDivGen.exists_isIntegral_counit_OL P' φ' ψ' h1 h2 1
  have hl' : (G.G 1).dual.IsIntegral l := hl
  have key := (G.G 1).counit_mul_eq_of_dual_integral
    ((G.G 1).trL_mul_comul_integral OL.algebraMap_qbar_injective (G.isEtale_layer_qbar 1) hΛ)
    (WithConv.ofConv l) ((G.G 1).rid_lTensor_comul_of_isIntegral hl')
  have hl1 : WithConv.ofConv l (1 : (G.G 1).A) = ((p ^ 1 : ℕ) : OL L) ^ d' := by
    rw [← hlc]
    rfl
  rw [hΛc, hl1, show finrank (OL L) (G.G 1).A = p ^ (G.height * 1) from G.order_eq 1] at key
  simp only [pow_one, mul_one] at key
  by_contra hlt
  push Not at hlt
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hlt
  have hp0 : ((p : ℕ) : OL L) ^ (d + d') ≠ 0 :=
    pow_ne_zero _ (OL.natCast_ne_zero hp.out.ne_zero)
  have key' : ((p : ℕ) : OL L) ^ (d + d') * 1 =
      ((p : ℕ) : OL L) ^ (d + d') * (WithConv.ofConv l Λ * (p : OL L) ^ (k + 1)) := by
    calc ((p : ℕ) : OL L) ^ (d + d') * 1 = (p : OL L) ^ d * (p : OL L) ^ d' := by
          rw [mul_one, pow_add]
      _ = WithConv.ofConv l Λ * ((p ^ G.height : ℕ) : OL L) := key
      _ = _ := by rw [hk, Nat.cast_pow]; ring
  have hu := mul_left_cancel₀ hp0 key'
  have hunit : IsUnit (p : OL L) := by
    refine isUnit_iff_exists_inv.mpr ⟨WithConv.ofConv l Λ * (p : OL L) ^ k, ?_⟩
    rw [hu]
    ring
  exact (IsLocalRing.mem_maximalIdeal _).mp OL.p_mem hunit

/-- **[Hong, Thm. 2.2.19] for non-connected `G` over `O_{K'}`**: `h = d + d^∨`. -/
theorem height_eq_add_OL {d d' : ℕ} (P : PDivFGL (OL L) d p)
    (φ : Hom G.connPart P.pdivGroup) (ψ : Hom P.pdivGroup G.connPart)
    (hφψ : φ.comp ψ = Hom.id _) (hψφ : ψ.comp φ = Hom.id _) (P' : PDivFGL (OL L) d' p)
    (φ' : Hom G.dualPDivGen.connPart P'.pdivGroup) (ψ' : Hom P'.pdivGroup G.dualPDivGen.connPart)
    (h1 : φ'.comp ψ' = Hom.id _) (h2 : ψ'.comp φ' = Hom.id _) :
    G.height = d + d' :=
  le_antisymm (G.height_le_add_OL P φ ψ hφψ hψφ P' φ' ψ' h1 h2)
    (G.add_le_height_OL P φ ψ hφψ hψφ P' φ' ψ' h1 h2)

/-- **[Hong, Thm. 2.2.19] for every `p`-divisible group over `O_{K'}`**: with
`G⁰ ≅ F[p^∞]`, `(G^∨)⁰ ≅ F'[p^∞]` of dimensions `d`, `d^∨`, `h = d + d^∨`. -/
theorem exists_height_eq_add_OL :
    ∃ (d d' : ℕ) (P : PDivFGL (OL L) d p) (P' : PDivFGL (OL L) d' p)
      (φ : Hom G.connPart P.pdivGroup) (ψ : Hom P.pdivGroup G.connPart)
      (φ' : Hom G.dualPDivGen.connPart P'.pdivGroup)
      (ψ' : Hom P'.pdivGroup G.dualPDivGen.connPart),
      φ.comp ψ = Hom.id _ ∧ ψ.comp φ = Hom.id _ ∧ φ'.comp ψ' = Hom.id _ ∧
        ψ'.comp φ' = Hom.id _ ∧ G.height = d + d' := by
  obtain ⟨d, P, φ, ψ, h1, h2⟩ := G.exists_connPart_iso_OL
  obtain ⟨d', P', φ', ψ', h1', h2'⟩ := G.dualPDivGen.exists_connPart_iso_OL
  exact ⟨d, d', P, P', φ, ψ, φ', ψ', h1, h2, h1', h2',
    G.height_eq_add_OL P φ ψ h1 h2 P' φ' ψ' h1' h2'⟩

/-! ### Tate's Hodge–Tate decomposition for non-connected `G` -/

/-- `dim D_{-1}(V) + dim D_0(V^∨) = dim V` (from `h = d + d^∨`). -/
theorem finrank_DHT_add_eq_OL {d : ℕ} (P : PDivFGL (OL L) d p)
    (φ : Hom G.connPart P.pdivGroup) (ψ : Hom P.pdivGroup G.connPart)
    (hφψ : φ.comp ψ = Hom.id _) (hψφ : ψ.comp φ = Hom.id _) :
    finrank L (DHT (G.baseChange L).tateRepOver (-1)) +
      finrank L (DHT (G.baseChange L).tateRepOver.dual 0) =
      finrank ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] Additive ((G.baseChange L).TateModule K)) := by
  have hex := G.dualPDivGen.exists_connPart_iso_OL
  obtain ⟨d', P', φ', ψ', h1, h2⟩ := hex
  have hh := G.height_eq_add_OL P φ ψ hφψ hψφ P' φ' ψ' h1 h2
  have e1 := G.finrank_DHT_tateRepOver_neg_one_of_iso_OL P φ ψ hφψ hψφ
  have e2 := G.finrank_DHT_dual_zero_OL P' φ' ψ' h1 h2
  have e3 := (G.baseChange L).finrank_tateRep
  have e4 : (G.baseChange L).height = G.height := rfl
  omega

/-- **`dim D_0(V^∨) = h - d`**: the `G_L`-equivariant maps `T_p G → ℂ_p` form an `L`-space of
dimension `h - d` (Tate). -/
theorem finrank_DHT_dual_zero_eq_sub_OL {d : ℕ} (P : PDivFGL (OL L) d p)
    (φ : Hom G.connPart P.pdivGroup) (ψ : Hom P.pdivGroup G.connPart)
    (hφψ : φ.comp ψ = Hom.id _) (hψφ : ψ.comp φ = Hom.id _) :
    finrank L (DHT (G.baseChange L).tateRepOver.dual 0) = G.height - d := by
  have h := G.finrank_DHT_add_eq_OL P φ ψ hφψ hψφ
  have e1 := G.finrank_DHT_tateRepOver_neg_one_of_iso_OL P φ ψ hφψ hψφ
  have e3 := (G.baseChange L).finrank_tateRep
  have e4 : (G.baseChange L).height = G.height := rfl
  omega

/-- `V_p(G_L)^∨` is Hodge–Tate (non-connected `G` over `O_{K'}`). -/
theorem isHodgeTate_dual_nonconn_OL {d : ℕ} (P : PDivFGL (OL L) d p)
    (φ : Hom G.connPart P.pdivGroup) (ψ : Hom P.pdivGroup G.connPart)
    (hφψ : φ.comp ψ = Hom.id _) (hψφ : ψ.comp φ = Hom.id _) :
    IsHodgeTate (G.baseChange L).tateRepOver.dual :=
  (isHodgeTate_dual_of_finrank_add_eq (ρ := (G.baseChange L).tateRepOver)
    (fun φ v => (G.baseChange L).continuous_tateRepOver φ v) (q := -1) (q' := 0) (by norm_num)
    (G.finrank_DHT_add_eq_OL P φ ψ hφψ hψφ)).1

/-- `dim D_1(V_p(G_L)^∨) = d` (non-connected `G` over `O_{K'}`). -/
theorem finrank_DHT_dual_one_nonconn_OL {d : ℕ} (P : PDivFGL (OL L) d p)
    (φ : Hom G.connPart P.pdivGroup) (ψ : Hom P.pdivGroup G.connPart)
    (hφψ : φ.comp ψ = Hom.id _) (hψφ : ψ.comp φ = Hom.id _) :
    finrank L (DHT (G.baseChange L).tateRepOver.dual 1) = d := by
  have h2 := finrank_DHT_dual_one_of_add_eq (ρ := (G.baseChange L).tateRepOver)
    (fun φ v => (G.baseChange L).continuous_tateRepOver φ v)
    (G.finrank_DHT_add_eq_OL P φ ψ hφψ hψφ)
  have e1 := G.finrank_DHT_tateRepOver_neg_one_of_iso_OL P φ ψ hφψ hψφ
  omega

/-- **Tate's Hodge–Tate decomposition for non-connected `G` over `O_{K'}`** ([Hong, Thm. 3.4.12,
Cor. 3.4.14]): if `G⁰ ≅ F[p^∞]` with `F` of dimension `d`, then `V_p(G_L)^∨` is Hodge–Tate with
`dim D_0(V^∨) = h - d` (the `G_L`-equivariant maps `T_p G → ℂ_p`) and `dim D_1(V^∨) = d`, and
`V_p(G_L)` is Hodge–Tate. -/
theorem hodgeTate_decomposition_nonconn_OL {d : ℕ} (P : PDivFGL (OL L) d p)
    (φ : Hom G.connPart P.pdivGroup) (ψ : Hom P.pdivGroup G.connPart)
    (hφψ : φ.comp ψ = Hom.id _) (hψφ : ψ.comp φ = Hom.id _) :
    IsHodgeTate (G.baseChange L).tateRepOver.dual ∧
      finrank L (DHT (G.baseChange L).tateRepOver.dual 0) = G.height - d ∧
      finrank L (DHT (G.baseChange L).tateRepOver.dual 1) = d ∧
      IsHodgeTate (G.baseChange L).tateRepOver :=
  ⟨G.isHodgeTate_dual_nonconn_OL P φ ψ hφψ hψφ, G.finrank_DHT_dual_zero_eq_sub_OL P φ ψ hφψ hψφ,
    G.finrank_DHT_dual_one_nonconn_OL P φ ψ hφψ hψφ,
    isHodgeTate_of_dual (G.isHodgeTate_dual_nonconn_OL P φ ψ hφψ hψφ)⟩

end PDivGroup

end PadicHodge
