/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.DAlphaHTOL
import PadicHodge.FormalGroup.HodgeTateFGL
import PadicHodge.GroupScheme.SerreTateOL

/-!
# Tate's theorem and the Hodge–Tate decomposition for `F[p^∞]` over `O_{K'}`

Let `L = K'` be a finite extension of `ℚ_p` inside `ℚ̄_p`, `P` a `p`-divisible formal group law
of dimension `d` and height `h` over `O_L` (`OL L`), `G = F[p^∞]`, `G_L` its generic fibre
(`genericFibreOL`) and `V = V_p(G_L)` as a representation of `G_L = Gal(ℚ̄_p/L)` (`tateRepOL`,
i.e. `tateRepOver`). By Serre–Tate over `O_L` (`exists_connPart_dual_iso_height_le_OL`)
`(G^∨)⁰ ≅ F'[p^∞]` with `F'` of dimension `d'` and `h ≤ d + d'`. The general-coefficient-ring
forms of [Hong, (3.9)–(3.11)] (`dalphaKGen`, `dalphaDualGen`, `tate_dalphaGen`) then give:

* **[Hong, Thm. 3.4.10] over `K'`** (`PDivFGL.tate_dalphaOL`, `PDivFGL.dalphaKOL_bijective`):
  `dα_K : t_G(L) = L^d → Hom_{ℤ_p[G_L]}(T_p(G^∨), ℂ_p)` is bijective, and so is the dual map
  `L^{d'} → D_0(V^∨)`; `h = d + d'`;
* **[Hong, Cor. 3.4.11] over `K'`** (`PDivFGL.finrank_DHT_tateRepOL_neg_one`):
  `dim_L (V ⊗ ℂ_p(-1))^{G_L} = d`;
* **[Hong, Thm. 3.4.12] over `K'`** (`PDivFGL.hodgeTate_decompositionOL`): `ℂ_p ⊗ V^∨` is
  Hodge–Tate with `dim D_0(V^∨) = d'`, `dim D_1(V^∨) = d`;
* **[Hong, Cor. 3.4.14] over `K'`** (`PDivFGL.isHodgeTate_tateRepOL`): `V_p G_L` is Hodge–Tate.

`V` is continuous by `PDivGroup.continuous_tateRepOver` (`TateCont.lean`).

## References

* [Hong] S. Hong, *Notes on p-adic Hodge theory*, Thm. 3.4.10, Cor. 3.4.11, Thm. 3.4.12,
  Cor. 3.4.14, Thm. 2.2.19.
-/

noncomputable section

open Module TensorProduct

namespace PadicHodge

namespace PDivFGL

open PDivGroup

variable {p : ℕ} [hp : Fact p.Prime] {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
  [FiniteDimensional ℚ_[p] L] {d : ℕ} (P : PDivFGL (OL L) d p)

omit [FiniteDimensional ℚ_[p] L] in
/-- Shortcut instance (avoids a slow search through normed-space instances on `L`). -/
local instance (priority := high) instModuleDHT {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
    (ρ : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) V) (q : ℤ) :
    Module L (DHT ρ q) :=
  (DHT ρ q).module

omit [FiniteDimensional ℚ_[p] L] in
/-- Shortcut instance (avoids a slow search through normed-space instances on `L`). -/
local instance (priority := high) instAddCommGroupDHT {V : Type*} [AddCommGroup V]
    [Module ℚ_[p] V] (ρ : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) V) (q : ℤ) :
    AddCommGroup (DHT ρ q) :=
  (DHT ρ q).addCommGroup

/-- `V_p(G_L)` as a representation of `G_L = Gal(ℚ̄_p/L)`, `G = F[p^∞]` over `O_L`. -/
abbrev tateRepOL : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p)
    (ℚ_[p] ⊗[ℤ_[p]] Additive (P.genericFibreOL.TateModule (PadicAlgCl p))) :=
  P.genericFibreOL.tateRepOver

variable {d' : ℕ} (P' : PDivFGL (OL L) d' p)
  (ψ : PDivGroup.Hom P'.pdivGroup P.dualPDiv.connPart)

/-- **Step (3.10)** ([Hong, proof of Thm. 3.4.10]) over `O_L`:
`L^{d'} → D_0(V^∨) = Hom_{ℤ_p}(T_p G, ℂ_p)^{G_L}`. -/
def dalphaDualOL : (Fin d' → L) →ₗ[L] DHT P.tateRepOL.dual 0 :=
  P.dalphaDualGen L P' ψ L (fun σ => σ) (fun _ _ => rfl) P.tateRepOL (fun _ _ _ => rfl)
    P.tateRepDualOL (fun _ _ _ => rfl) P'.tateRepOL (fun _ _ _ => rfl) P'.tateRepDualOL
    (fun _ _ _ => rfl) OL.p_mem OL.algebraMap_qbar_cp OL.galFixedOver

/-- **Tate's theorem** ([Hong, Thm. 3.4.10], the `dα_K` half, and the dual statement) for
`G = F[p^∞]` over `O_L`: with `(G^∨)⁰ ≅ F'[p^∞]`, `F'` of dimension `d'`,
`dα_K : L^d → D_{-1}(V_p G_L)` and `L^{d'} → D_0(V_p(G_L)^∨)` are bijective,
`dim_L D_{-1}(V_p G_L) = d`, `dim_L D_0(V_p(G_L)^∨) = d'` and `h = d + d'`. -/
theorem tate_dalphaOL :
    ∃ (d' : ℕ) (P' : PDivFGL (OL L) d' p)
      (ψ : PDivGroup.Hom P'.pdivGroup P.dualPDiv.connPart),
      Function.Bijective P.dalphaKTwistOL ∧ Function.Bijective (P.dalphaDualOL P' ψ) ∧
      finrank L (DHT P.tateRepOL (-1)) = d ∧ finrank L (DHT P.tateRepOL.dual 0) = d' ∧
      P.height = d + d' := by
  have h0 := P.exists_connPart_dual_iso_height_le_OL
  obtain ⟨d', P', φ, ψ, hφψ, -, hle⟩ := h0
  exact ⟨d', P', ψ, P.tate_dalphaGen L P' φ ψ L (fun σ => σ) (fun _ _ => rfl) P.tateRepOL
    (fun _ _ _ => rfl) P.tateRepDualOL (fun _ _ _ => rfl) P'.tateRepOL (fun _ _ _ => rfl)
    P'.tateRepDualOL (fun _ _ _ => rfl) OL.p_mem OL.algebraMap_qbar_cp OL.galFixedOver
    OL.norm_lt_one hφψ hle⟩

/-- **[Hong, Thm. 3.4.10]** (`dα_K` half) over `O_L`:
`dα_K : t_G(L) = L^d → Hom_{ℤ_p[G_L]}(T_p(G^∨), ℂ_p) = D_0(V_p(G_L^∨)^∨)` is bijective. -/
theorem dalphaKOL_bijective : Function.Bijective P.dalphaKOL := by
  have h0 := P.tate_dalphaOL
  obtain ⟨d', P', ψ, b1, -⟩ := h0
  refine ⟨P.dalphaKOL_injective, fun y => ?_⟩
  have hy := b1.2 (P.DHTdualTateEquivMapOL y)
  obtain ⟨z, hz⟩ := hy
  exact ⟨z, (DHTdualDualMap_injective _ P.genericFibreOL.tateRepDualEquiv_galOver) hz⟩

/-- `dα_K` over `O_L` with values in `D_{-1}(V_p G_L)` is bijective. -/
theorem dalphaKTwistOL_bijective : Function.Bijective P.dalphaKTwistOL := by
  have h0 := P.tate_dalphaOL
  obtain ⟨d', P', ψ, b1, -⟩ := h0
  exact b1

/-- **[Hong, Cor. 3.4.11]** over `O_L`, first equality:
`d = dim_L Hom_{ℤ_p[G_L]}(T_p(G^∨), ℂ_p)`. -/
theorem finrank_DHT_tateRepDualOL_dual : finrank L (DHT P.tateRepDualOL.dual 0) = d := by
  rw [← (LinearEquiv.ofBijective _ P.dalphaKOL_bijective).finrank_eq, Module.finrank_fin_fun]

/-- **[Hong, Cor. 3.4.11]** over `O_L`, second equality:
`d = dim_L (T_p G ⊗ ℂ_p(-1))^{G_L} = dim_L D_{-1}(V_p G_L)`. -/
theorem finrank_DHT_tateRepOL_neg_one : finrank L (DHT P.tateRepOL (-1)) = d := by
  have h0 := P.tate_dalphaOL
  obtain ⟨d', P', ψ, -, -, e1, -⟩ := h0
  exact e1

/-- **The Hodge–Tate decomposition** ([Hong, Thm. 3.4.12]) for `G = F[p^∞]` over `O_L`:
`ℂ_p ⊗ V_p(G_L)^∨` is Hodge–Tate, the weight-`0` part has dimension `d' = dim (G^∨)⁰ = h − d`
(the image of `t_{G^∨}(L) = L^{d'}` under `dα`), the weight-`1` part has dimension `d`. -/
theorem hodgeTate_decompositionOL :
    ∃ (d' : ℕ) (P' : PDivFGL (OL L) d' p)
      (ψ : PDivGroup.Hom P'.pdivGroup P.dualPDiv.connPart),
      Function.Bijective (P.dalphaDualOL P' ψ) ∧
      IsHodgeTate P.tateRepOL.dual ∧
      finrank L (DHT P.tateRepOL.dual 0) = d' ∧
      finrank L (DHT P.tateRepOL.dual 1) = d ∧
      P.height = d + d' := by
  have h0 := P.tate_dalphaOL
  obtain ⟨d', P', ψ, -, b2, e1, e2, hh⟩ := h0
  have hV : finrank L (DHT P.tateRepOL (-1)) + finrank L (DHT P.tateRepOL.dual 0) =
      finrank ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] Additive (P.genericFibreOL.TateModule (PadicAlgCl p))) := by
    rw [e1, e2, PDivGroup.finrank_tateRep]
    exact hh.symm
  have hS := isHodgeTate_dual_of_finrank_add_eq
    (fun φ v => P.genericFibreOL.continuous_tateRepOver φ v) (q := -1) (q' := 0) (by norm_num) hV
  obtain ⟨hHT, hdim⟩ := hS
  refine ⟨d', P', ψ, b2, hHT, e2, ?_, hh⟩
  have h1 : finrank L (DHT P.tateRepOL.dual 1) = finrank L (DHT P.tateRepOL (-1)) := hdim
  exact h1.trans e1

/-- **[Hong, Cor. 3.4.14]** over `O_L`: `V_p G_L` is Hodge–Tate for `G = F[p^∞]` over `O_L`,
and `dim_L (V_p G_L ⊗ ℂ_p(-1))^{G_L} = d`. -/
theorem isHodgeTate_tateRepOL :
    IsHodgeTate P.tateRepOL ∧ finrank L (DHT P.tateRepOL (-1)) = d := by
  have h0 := P.hodgeTate_decompositionOL
  obtain ⟨d', P', ψ, -, hHT, -⟩ := h0
  exact ⟨isHodgeTate_of_dual hHT, P.finrank_DHT_tateRepOL_neg_one⟩

end PDivFGL

end PadicHodge
