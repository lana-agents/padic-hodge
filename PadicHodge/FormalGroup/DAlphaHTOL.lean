/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.DAlphaHT
import PadicHodge.FormalGroup.OK

/-!
# `dα_K` over `O_{K'}` ([Hong, (3.9)] for `K'`)

Let `L = K'` be a finite extension of `ℚ_p` inside `ℚ̄_p` and `P` a `p`-divisible formal group
law of dimension `d` over `O_L` (`OL L`), `G = P.pdivGroup` and `G_L` its generic fibre
(`genericFibreOL`, a `p`-divisible group over the field `↥L`). This file is the `O_{K'}`-case of
`DAlphaHT.lean`:

* `OL.toL : O_L →+* L` and the algebra structures `O_L → L → ℚ̄_p` (`OL.algebraMap_qbar_cp`:
  compatible with `O_L ⊆ O_{ℂ_p}`), so `T_p(G^∨)(O_{ℂ_p}) ≃ T_p(G_L^∨)(ℚ̄_p)`
  (`dualTateGenEquiv`) is available;
* `tateRepDualOL`: `V_p(G_L^∨)` as a representation of `G_L = Gal(ℚ̄_p/L)` (`tateRepOver`);
* **`dalphaKOL : L^d ↪ D_0(V_p(G_L^∨)^∨)`** (`dalphaKGen` with `ι = id`, injective by
  `dalpha_injective_K`, [Hong, Prop. 3.4.9]) and **`le_finrank_DHT_tateRepDualOL`**:
  `d ≤ dim_L Hom_{ℤ_p}(T_p(G^∨), ℂ_p)^{G_L}` ([Hong, (3.9)]);
* **`dalphaKTwistOL : L^d ↪ D_{-1}(V_p G_L)`** via `V_p(G_L^∨)^∨ ≅ V_p(G_L)(-1)`
  (`tateRepDualEquiv_galOver`, `DHTdualDualMap`) and **`le_finrank_DHT_tateRepOL`**:
  `d ≤ dim_L D_{-1}(V_p G_L)`.

## References

* [Hong] S. Hong, *Notes on p-adic Hodge theory*, Prop. 3.4.6, Prop. 3.4.9, Thm. 3.4.10 (3.9).
-/

noncomputable section

open Module TensorProduct IsLocalRing

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime]

namespace OL

variable {L : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem exists_coe_eq (x : OL L) :
    ∃ a : L, ((a : PadicAlgCl p) : ℂ_[p]) = ((toOC x : OC p) : ℂ_[p]) := by
  obtain ⟨a, ha, hax⟩ := mem_cpSubmodule.mp (mem x)
  exact ⟨⟨a, ha⟩, hax⟩

/-- `L → ℂ_p`. -/
def coeL : L →+* ℂ_[p] := (algebraMap (PadicAlgCl p) ℂ_[p]).comp (algebraMap L (PadicAlgCl p))

theorem coeL_injective : Function.Injective (coeL (L := L)) :=
  (algebraMap (PadicAlgCl p) ℂ_[p]).injective.comp Subtype.val_injective

/-- `x ∈ O_L` as an element of `L`. -/
def toLFun (x : OL L) : L := (exists_coe_eq x).choose

theorem coe_toLFun (x : OL L) :
    ((toLFun x : PadicAlgCl p) : ℂ_[p]) = ((toOC x : OC p) : ℂ_[p]) :=
  (exists_coe_eq x).choose_spec

theorem coeL_toLFun (x : OL L) : coeL (toLFun x) = ((toOC x : OC p) : ℂ_[p]) :=
  coe_toLFun x

/-- **`O_L → L`.** -/
def toL : OL L →+* L where
  toFun := toLFun
  map_one' := coeL_injective (by rw [map_one, coeL_toLFun, map_one, OneMemClass.coe_one])
  map_mul' x y := coeL_injective (by
    rw [map_mul, coeL_toLFun, coeL_toLFun, coeL_toLFun, map_mul, Subring.coe_mul])
  map_zero' := coeL_injective (by rw [map_zero, coeL_toLFun, map_zero, ZeroMemClass.coe_zero])
  map_add' x y := coeL_injective (by
    rw [map_add, coeL_toLFun, coeL_toLFun, coeL_toLFun, map_add, Subring.coe_add])

instance algebraL : Algebra (OL L) L := toL.toAlgebra

instance algebraQbar : Algebra (OL L) (PadicAlgCl p) :=
  ((algebraMap L (PadicAlgCl p)).comp toL).toAlgebra

instance : IsScalarTower (OL L) L (PadicAlgCl p) := IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- `O_L → L → ℚ̄_p → ℂ_p` is `O_L ⊆ O_{ℂ_p} ⊆ ℂ_p`. -/
theorem algebraMap_qbar_cp (r : OL L) :
    ((algebraMap (OL L) (PadicAlgCl p) r : PadicAlgCl p) : ℂ_[p]) =
      ((algebraMap (OL L) (OC p) r : OC p) : ℂ_[p]) :=
  coe_toLFun r

end OL

namespace PDivFGL

open PDivGroup

variable {L : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] L] {d : ℕ}
  (P : PDivFGL (OL L) d p)

/-- The generic fibre `G_L` of `G = F[p^∞]` over `O_L`. -/
abbrev genericFibreOL : PDivGroup L p := P.pdivGroup.baseChange L

/-- `V_p(G_L^∨)`, as a representation of `G_L = Gal(ℚ̄_p/L)`. -/
abbrev tateRepDualOL :
    Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (ℚ_[p] ⊗[ℤ_[p]] P.TateDualF L) :=
  P.genericFibreOL.dualPDiv.tateRepOver

/-- **`dα_K : L^d → D_0(V_p(G_L^∨)^∨) = Hom_{ℤ_p}(T_p(G^∨), ℂ_p)^{G_L}`** for `G` over `O_L`
([Hong, Prop. 3.4.9, Thm. 3.4.10]). -/
def dalphaKOL : (Fin d → L) →ₗ[L] DHT P.tateRepDualOL.dual 0 :=
  P.dalphaKGen OL.p_mem L OL.algebraMap_qbar_cp L OL.galFixedOver (fun σ => σ)
    (fun _ _ => rfl) P.tateRepDualOL (fun _ _ _ => rfl)

/-- **`dα_K` is injective over `O_L`** ([Hong, Prop. 3.4.9], `dalpha_injective_OL`). -/
theorem dalphaKOL_injective : Function.Injective P.dalphaKOL :=
  P.dalphaKGen_injective _ _ _ L _ _ _ _ _ OL.norm_lt_one

/-- **[Hong, (3.9)] over `O_L`**: `d ≤ dim_L Hom_{ℤ_p}(T_p(G^∨), ℂ_p)^{G_L}`. -/
theorem le_finrank_DHT_tateRepDualOL : d ≤ finrank L (DHT P.tateRepDualOL.dual 0) := by
  have h := LinearMap.finrank_le_finrank_of_injective P.dalphaKOL_injective
  rwa [Module.finrank_fin_fun] at h

/-- `D_0(V_p(G_L^∨)^∨) → D_{-1}(V_p G_L)`, induced by `V_p(G_L^∨)^∨ ≅ V_p(G_L)(-1)`. -/
def DHTdualTateEquivMapOL :
    DHT P.tateRepDualOL.dual 0 →ₗ[L] DHT P.genericFibreOL.tateRepOver (-1) :=
  DHTdualDualMap P.genericFibreOL.tateRepDualEquiv P.genericFibreOL.tateRepDualEquiv_galOver

/-- **`dα_K` with values in `D_{-1}(V_p G_L) = (V_p G_L ⊗ ℂ_p(-1))^{G_L}`** over `O_L`. -/
def dalphaKTwistOL : (Fin d → L) →ₗ[L] DHT P.genericFibreOL.tateRepOver (-1) :=
  P.DHTdualTateEquivMapOL ∘ₗ P.dalphaKOL

theorem dalphaKTwistOL_injective : Function.Injective P.dalphaKTwistOL :=
  (DHTdualDualMap_injective _ P.genericFibreOL.tateRepDualEquiv_galOver).comp
    P.dalphaKOL_injective

/-- **[Hong, (3.9)] for `V_p G_L`**: `d ≤ dim_L D_{-1}(V_p G_L)`. -/
theorem le_finrank_DHT_tateRepOL : d ≤ finrank L (DHT P.genericFibreOL.tateRepOver (-1)) := by
  have h := LinearMap.finrank_le_finrank_of_injective P.dalphaKTwistOL_injective
  rwa [Module.finrank_fin_fun] at h

end PDivFGL

end PadicHodge
