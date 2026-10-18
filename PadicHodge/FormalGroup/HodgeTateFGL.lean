/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.DAlphaDual
import PadicHodge.HodgeTate.OrthSplit
import PadicHodge.GroupScheme.TateCont

/-!
# The Hodge–Tate decomposition for `F[p^∞]` over `ℤ_p` ([Hong, Thm. 3.4.12, Cor. 3.4.14])

Let `P` be a `p`-divisible formal group law of dimension `d` and height `h` over `ℤ_p`,
`G = F[p^∞]`, `V = V_p(G_{ℚ_p})` and `(G^∨)⁰ ≅ F'[p^∞]` with `F'` of dimension `d'`.
By Tate's theorem (`PDivFGL.tate_dalpha`, `DAlphaDual.lean`) `dim D_{-1}(V) = d`,
`dim D_0(V^∨) = d'` and `h = d + d'`. The orthogonal-splitting argument of
[Hong, proof of Thm. 3.4.12] (`isHodgeTate_dual_of_finrank_add_eq`, `HodgeTate/OrthSplit.lean`;
`V` is continuous by `continuous_tateRep`) then gives:

* **[Hong, Thm. 3.4.12]** (`PDivFGL.hodgeTate_decomposition`):
  `Hom_{ℤ_p}(T_p G, ℂ_p) = ℂ_p ⊗ V^∨` is Hodge–Tate with
  `D_0(V^∨) = Hom_{ℤ_p[Γ]}(T_p G, ℂ_p) ≅ t_{G^∨}(ℚ_p)` of dimension `d' = h − d` (via `dα` for
  `F'`, `PDivFGL.dalphaDual`) and `D_1(V^∨)` (the part `t_G^*(ℂ_p)(-1)`) of dimension `d`; i.e.
  `ℂ_p ⊗ V^∨ ≅ ℂ_p^{h-d} ⊕ ℂ_p(-1)^d`;
* **[Hong, Cor. 3.4.14]** (`PDivFGL.isHodgeTate_tateRep`): `V_p G` is Hodge–Tate, with
  `dim (V_p G ⊗ ℂ_p(-1))^Γ = d`.

## References

* [Hong] S. Hong, *Notes on p-adic Hodge theory*, Thm. 3.4.10, Cor. 3.4.11, Thm. 3.4.12,
  Cor. 3.4.14.
-/

noncomputable section

open Module TensorProduct

namespace PadicHodge

namespace PDivFGL

variable {p : ℕ} [hp : Fact p.Prime] {d : ℕ} (P : PDivFGL (ZpD p) d p)

attribute [local instance] SerreTate.algebraZModD SerreTate.isDomain_zpD isPrincipalIdealRing_zpD

/-- **The Hodge–Tate decomposition** ([Hong, Thm. 3.4.12]) for `G = F[p^∞]` over `ℤ_p`:
`ℂ_p ⊗ V_p(G)^∨ = Hom_{ℤ_p}(T_p G, ℂ_p)` is Hodge–Tate, the weight-`0` part
`Hom_{ℤ_p[Γ]}(T_p G, ℂ_p)` has dimension `d' = dim (G^∨)⁰ = h − d` (and is the image of
`t_{G^∨}(ℚ_p) = ℚ_p^{d'}` under `dα`), the weight-`1` part (`t_G^*(ℂ_p)(-1)`) has dimension `d`. -/
theorem hodgeTate_decomposition :
    ∃ (d' : ℕ) (P' : PDivFGL (ZpD p) d' p)
      (ψ : PDivGroup.Hom P'.pdivGroup P.dualPDiv.connPart),
      Function.Bijective (P.dalphaDual P' ψ ⊥) ∧
      IsHodgeTate (P.genericFibre.tateRep ⊥).dual ∧
      finrank (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p))
        (DHT (P.genericFibre.tateRep ⊥).dual 0) = d' ∧
      finrank (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p))
        (DHT (P.genericFibre.tateRep ⊥).dual 1) = d ∧
      P.height = d + d' := by
  obtain ⟨d', P', ψ, -, b2, e1, e2, hh⟩ := P.tate_dalpha
  have hV : finrank (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p))
      (DHT (P.genericFibre.tateRep ⊥) (-1)) + finrank (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p))
      (DHT (P.genericFibre.tateRep ⊥).dual 0) =
      finrank ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] Additive (P.genericFibre.TateModule (PadicAlgCl p))) := by
    rw [e1, e2, PDivGroup.finrank_tateRep]
    exact hh.symm
  obtain ⟨hHT, hdim⟩ := isHodgeTate_dual_of_finrank_add_eq
    (fun φ v => P.genericFibre.continuous_tateRep ⊥ φ v) (q := -1) (q' := 0) (by norm_num) hV
  rw [neg_neg, e1] at hdim
  exact ⟨d', P', ψ, b2, hHT, e2, hdim, hh⟩

/-- **[Hong, Cor. 3.4.14]**: `V_p G` is Hodge–Tate for `G = F[p^∞]` over `ℤ_p`, and
`dim (V_p G ⊗ ℂ_p(-1))^Γ = d`. -/
theorem isHodgeTate_tateRep :
    IsHodgeTate (P.genericFibre.tateRep ⊥) ∧
      finrank (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p))
        (DHT (P.genericFibre.tateRep ⊥) (-1)) = d := by
  obtain ⟨d', P', ψ, -, hHT, -⟩ := P.hodgeTate_decomposition
  exact ⟨isHodgeTate_of_dual hHT, P.finrank_DHT_tateRep_neg_one⟩

end PDivFGL

end PadicHodge
