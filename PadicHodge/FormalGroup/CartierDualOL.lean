/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.CartierDualGen
import PadicHodge.FormalGroup.TateNonConnOL

/-!
# The Cartier dual of a `p`-divisible group over `O_{K'}` and over `ℤ_p`

For a (not necessarily connected) `p`-divisible group `G` over `O_L = O_{K'}` (`OL L`), the
Cartier dual `G^∨ = G.dualPDivGen` (`GroupScheme/CartierDualGen.lean`) is a `p`-divisible group
over `O_L` of the same height. Here:

* **compatibility**: for `G = F[p^∞]` it is the dual `PDivFGL.dualPDiv` built from the explicit
  freeness data of `FormalGroup/DualPDivFGL.lean` (`PDivFGL.dualPDiv_eq_dualPDivGen`, by
  definition); over `ℤ_p` (`ZpD p`) the same construction applies
  (`PDivGroup.dualPDivGen_height_zp`);
* **generic fibre**: `T_p((G^∨)_L) ≅ T_p((G_L)^∨)` (`dualGenTateEquivOL`), `ℤ_p`-linear and
  `G_L`-equivariant (`dualGenTateEquivOL_galLin`);
* **[Hong, Prop. 3.4.6] over `O_{K'}`**: `T_p(G^∨) ≅ Hom_{ℤ_p}(T_p G, ℤ_p(1))`
  (`dualTateHomOL`, bijective, `dualTateHomOL_gal`: `⟨σy, σx⟩ = χ(σ)⟨y, x⟩`), and
  `V_p(G^∨) ≅ V_p(G)^∨ ⊗ ℚ_p(1)` as representations of `G_L` (`tateRepDualEquivOL`,
  `tateRepDualEquivOL_gal`).

## References

* [Hong] S. Hong, *Notes on p-adic Hodge theory*, Prop. 2.1.7, Prop. 3.4.6.
-/

noncomputable section

open Module TensorProduct WithConv

namespace PadicHodge

open FFGroupScheme

attribute [local instance] isPrincipalIdealRing_zpD

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Compatibility with the dual of `F[p^∞]` -/

namespace PDivFGL

variable {L : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] L] {d : ℕ}

/-- For `G = F[p^∞]` over `O_L`, the general Cartier dual is the dual of `DualPDivFGL.lean`. -/
theorem dualPDiv_eq_dualPDivGen (P : PDivFGL (OL L) d p) :
    P.dualPDiv = P.pdivGroup.dualPDivGen := rfl

/-- For `G = F[p^∞]` over `ℤ_p`, the general Cartier dual is the dual of `DualPDivFGL.lean`. -/
theorem dualPDiv_eq_dualPDivGen_zp (P : PDivFGL (ZpD p) d p) :
    P.dualPDiv = P.pdivGroup.dualPDivGen := rfl

end PDivFGL

namespace PDivGroup

/-- The Cartier dual over `ℤ_p` (`ZpD p`) has the same height. -/
theorem dualPDivGen_height_zp (G : PDivGroup (ZpD p) p) :
    G.dualPDivGen.height = G.height := rfl

variable {L : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] L]

local notation "K" => PadicAlgCl p

/-- Shortcut instance (avoids slow searches through normed-space instances on `L`). -/
local instance (priority := high) instAddCommGroupTateL' (H : PDivGroup L p) :
    AddCommGroup (Additive (H.TateModule K)) := Additive.addCommGroup

/-- Shortcut instance (avoids slow searches through normed-space instances on `L`). -/
local instance (priority := high) instModuleTateL' (H : PDivGroup L p) :
    Module ℤ_[p] (Additive (H.TateModule K)) := PDivGroup.instModuleZp H K

variable (G : PDivGroup (OL L) p)

/-! ### `T_p((G^∨)_L) ≅ T_p((G_L)^∨)` -/

/-- Galois equivariance of the levelwise comparison `(G_v^∨)_L ≅ ((G_v)_L)^∨` on
`ℚ̄_p`-points. -/
theorem dualPDivOfBaseChangePointsEquiv_galPoints (σ : K ≃ₐ[L] K) (v : ℕ)
    (y : ((G.dualPDivGen.baseChange L).G v).points K) :
    dualPDivOfBaseChangePointsEquiv L G.dualPDivDataGen K v (galPoints _ σ y) =
      galPoints _ σ (dualPDivOfBaseChangePointsEquiv L G.dualPDivDataGen K v y) := by
  set E1 := (G.G v).dual.baseChangePointsEquiv (S := L) K
  set E2 := (G.G v).dualBaseChangePointsEquiv (S := L) (T := K)
  let σ' : K →ₐ[OL L] K := (σ : K →ₐ[L] K).restrictScalars (OL L)
  have hE1 : ∀ y, E1 (galPoints _ σ y) = (G.G v).dual.postComp σ' (E1 y) := fun _ => rfl
  have hE2 : ∀ w, E2 (galPoints _ σ w) = (G.G v).dual.postComp σ' (E2 w) := fun _ => rfl
  change E2.symm (E1 (galPoints _ σ y)) = galPoints _ σ (E2.symm (E1 y))
  apply E2.injective
  rw [MulEquiv.apply_symm_apply, hE1, hE2, MulEquiv.apply_symm_apply]

/-- **`T_p((G^∨)_L) ≅ T_p((G_L)^∨)`**, `ℤ_p`-linearly. -/
def dualGenTateEquivOL : Additive ((G.dualPDivGen.baseChange L).TateModule K) ≃ₗ[ℤ_[p]]
    Additive (((G.baseChange L).dualPDiv).TateModule K) where
  __ := (dualPDivOfBaseChangeTateEquiv L G.dualPDivDataGen K).toAdditive
  map_smul' a x := ((G.baseChange L).dualPDiv).addTate_ext K fun v => by
    change dualPDivOfBaseChangePointsEquiv L G.dualPDivDataGen K v
        ((Additive.toMul x).1 v ^ expo a v) =
      (dualPDivOfBaseChangePointsEquiv L G.dualPDivDataGen K v ((Additive.toMul x).1 v)) ^
        expo a v
    rw [map_pow]

theorem dualGenTateEquivOL_apply (x : Additive ((G.dualPDivGen.baseChange L).TateModule K))
    (v : ℕ) :
    (Additive.toMul (G.dualGenTateEquivOL x)).1 v =
      dualPDivOfBaseChangePointsEquiv L G.dualPDivDataGen K v ((Additive.toMul x).1 v) := rfl

/-- **`T_p((G^∨)_L) ≅ T_p((G_L)^∨)` is `G_L`-equivariant.** -/
theorem dualGenTateEquivOL_galLin (σ : K ≃ₐ[L] K)
    (x : Additive ((G.dualPDivGen.baseChange L).TateModule K)) :
    G.dualGenTateEquivOL ((G.dualPDivGen.baseChange L).galLin σ x) =
      ((G.baseChange L).dualPDiv).galLin σ (G.dualGenTateEquivOL x) :=
  ((G.baseChange L).dualPDiv).addTate_ext K fun v =>
    G.dualPDivOfBaseChangePointsEquiv_galPoints σ v ((Additive.toMul x).1 v)

/-! ### [Hong, Prop. 3.4.6] over `O_{K'}` -/

/-- **The Cartier pairing over `O_{K'}`**: `T_p(G^∨) → Hom_{ℤ_p}(T_p G, ℤ_p)`, both Tate modules
of the generic fibres, `G^∨ = G.dualPDivGen`. -/
def dualTateHomOL : Additive ((G.dualPDivGen.baseChange L).TateModule K) →ₗ[ℤ_[p]]
    (Additive ((G.baseChange L).TateModule K) →ₗ[ℤ_[p]] ℤ_[p]) :=
  (G.baseChange L).tateDualHom ∘ₗ G.dualGenTateEquivOL.toLinearMap

/-- **[Hong, Prop. 3.4.6] over `O_{K'}`**: `T_p(G^∨) ≅ Hom_{ℤ_p}(T_p G, ℤ_p)`. -/
theorem dualTateHomOL_bijective : Function.Bijective G.dualTateHomOL :=
  (G.baseChange L).tateDualHom_bijective.comp G.dualGenTateEquivOL.bijective

/-- **The twist by `ℤ_p(1)`**: `⟨σ y, σ x⟩ = χ(σ) ⟨y, x⟩` for `σ ∈ G_L`, i.e.
`T_p(G^∨) ≅ Hom_{ℤ_p}(T_p G, ℤ_p(1))` as `G_L`-modules. -/
theorem dualTateHomOL_gal (σ : K ≃ₐ[L] K)
    (y : Additive ((G.dualPDivGen.baseChange L).TateModule K))
    (x : Additive ((G.baseChange L).TateModule K)) :
    G.dualTateHomOL ((G.dualPDivGen.baseChange L).galLin σ y) ((G.baseChange L).galLin σ x) =
      ((chi (σ.restrictScalars ℚ_[p]) : ℤ_[p]ˣ) : ℤ_[p]) * G.dualTateHomOL y x := by
  change (G.baseChange L).tateDualHom (G.dualGenTateEquivOL _) _ = _
  rw [dualGenTateEquivOL_galLin]
  exact (G.baseChange L).tateDualHom_galOver σ _ x

/-- `T_p(G^∨) ≃ Hom_{ℤ_p}(T_p G, ℤ_p)` over `O_{K'}`. -/
def tateDualEquivOL : Additive ((G.dualPDivGen.baseChange L).TateModule K) ≃ₗ[ℤ_[p]]
    Module.Dual ℤ_[p] (Additive ((G.baseChange L).TateModule K)) :=
  LinearEquiv.ofBijective G.dualTateHomOL G.dualTateHomOL_bijective

/-- **`V_p(G^∨) ≅ V_p(G)^∨ ⊗ ℚ_p(1)`** as `ℚ_p`-vector spaces (`G` over `O_{K'}`,
`G^∨ = G.dualPDivGen`, generic fibres over `L = K'`). -/
def tateRepDualEquivOL : (ℚ_[p] ⊗[ℤ_[p]] Additive ((G.dualPDivGen.baseChange L).TateModule K))
    ≃ₗ[ℚ_[p]] Module.Dual ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] Additive ((G.baseChange L).TateModule K)) ⊗[ℚ_[p]]
      ℚ_[p] :=
  baseChangeDualEquiv G.tateDualEquivOL

/-- **`V_p(G^∨) ≅ V_p(G)^∨ ⊗ ℚ_p(1)` as representations of `G_L`.** -/
theorem tateRepDualEquivOL_gal (σ : K ≃ₐ[L] K) :
    (G.tateRepDualEquivOL : _ →ₗ[ℚ_[p]] _) ∘ₗ (G.dualPDivGen.baseChange L).tateRepOver σ =
      ((G.baseChange L).tateRepOver.dual.tprod (charRep L 1) σ) ∘ₗ G.tateRepDualEquivOL :=
  baseChangeDualEquiv_gal _ L (fun σ => (G.baseChange L).galLin σ)
    (fun σ => (G.dualPDivGen.baseChange L).galLin σ)
    (fun σ => ((chi (σ.restrictScalars ℚ_[p]) : ℤ_[p]ˣ) : ℤ_[p])) (fun _ => rfl) (fun _ => rfl)
    (fun σ x => (G.baseChange L).galLin_galLin_inv σ x) (fun σ y x => G.dualTateHomOL_gal σ y x)
    (chiL_one_eq L) σ

end PDivGroup

end PadicHodge
