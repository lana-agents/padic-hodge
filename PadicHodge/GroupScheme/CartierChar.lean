/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.TatePairing

/-!
# Points of the Cartier dual as group-like elements, over an arbitrary base change

For `G = Spec A` finite flat over `R` and an `R`-algebra `S`, a point `ψ ∈ G^∨(S)` is a
character `G_S → 𝔾_{m,S}`, i.e. a group-like element `χ_ψ ∈ S ⊗_R A`
([Hong, Prop. 3.4.9, proof, (3.7)]: `G_v^∨(O_C) = Hom(G_v ⊗ O_C, μ_{p^v})`). We define
`χ_ψ = ⟨u, ψ_{S ⊗ A}⟩` as the Cartier pairing of the universal point `u = (a ↦ 1 ⊗ a)` of `G`
over `S ⊗_R A` with `ψ` pushed to `S ⊗_R A` (`charOf`). From the properties of the pairing:

* `charOf_mul`: `χ_{ψψ'} = χ_ψ χ_{ψ'}`;
* `charOf_comul`: `(S ⊗ Δ)(χ_ψ) = (χ_ψ ⊗ 1)(1 ⊗ χ_ψ)` (**group-like**);
* `productMap_charOf`: evaluating `χ_ψ` at a point `φ ∈ G(S)` gives `⟨φ, ψ⟩`;
* `charOf_dual`: for `f : G → H`, `χ_{f^∨ ψ} = (S ⊗ f^*)(χ_ψ)` (naturality);
* `charOf_postComp`: `χ_{σ ∘ ψ} = (σ ⊗ A)(χ_ψ)` for `σ : S → S'`.
-/

noncomputable section

open Coalgebra WithConv TensorProduct

namespace PadicHodge

universe u

namespace FFGroupScheme

variable {R : Type u} [CommRing R] (G : FFGroupScheme R) (S : Type*) [CommRing S] [Algebra R S]

/-- `S → S ⊗_R A`. -/
abbrev inS : S →ₐ[R] S ⊗[R] G.A := Algebra.TensorProduct.includeLeft (S := R)

/-- `A → S ⊗_R A`. -/
abbrev inA : G.A →ₐ[R] S ⊗[R] G.A := Algebra.TensorProduct.includeRight

/-- **The character `χ_ψ ∈ S ⊗_R A` of a point `ψ ∈ G^∨(S)`.** -/
def charOf (ψ : G.dual.points S) : S ⊗[R] G.A :=
  G.pairing (S ⊗[R] G.A) (toConv (G.inA S)) (G.dual.postComp (G.inS S) ψ)

theorem charOf_mul (ψ ψ' : G.dual.points S) :
    G.charOf S (ψ * ψ') = G.charOf S ψ * G.charOf S ψ' := by
  simp only [charOf, map_mul, pairing_mul_right]

theorem charOf_one : G.charOf S 1 = 1 := by
  simp only [charOf, map_one, pairing_one_right]

/-- **Evaluating `χ_ψ` at `φ ∈ G(S)` gives the Cartier pairing `⟨φ, ψ⟩`.** -/
theorem productMap_charOf (φ : G.points S) (ψ : G.dual.points S) :
    Algebra.TensorProduct.productMap (AlgHom.id R S) (ofConv φ) (G.charOf S ψ) =
      G.pairing S φ ψ := by
  rw [charOf, ← pairing_postComp]
  congr 1
  · exact congrArg toConv (Algebra.TensorProduct.productMap_right _ _)
  · apply WithConv.ofConv_injective
    change (Algebra.TensorProduct.productMap (AlgHom.id R S) (ofConv φ)).comp
      ((G.inS S).comp (ofConv ψ)) = ofConv ψ
    rw [← AlgHom.comp_assoc, Algebra.TensorProduct.productMap_left]
    rfl

/-- **Naturality**: `χ_{f^∨ ψ} = (S ⊗ f^*)(χ_ψ)` for `f : G → H`. -/
theorem charOf_dual {H : FFGroupScheme R} (f : Hom G H) (ψ : H.dual.points S) :
    G.charOf S (f.dual.mapPoints S ψ) =
      Algebra.TensorProduct.map (AlgHom.id R S) (f : H.A →ₐ[R] G.A) (H.charOf S ψ) := by
  have e : G.dual.postComp (G.inS S) (f.dual.mapPoints S ψ) = f.dual.mapPoints _
      (H.dual.postComp ((Algebra.TensorProduct.map (AlgHom.id R S)
        (f : H.A →ₐ[R] G.A)).comp (H.inS S)) ψ) := by
    apply WithConv.ofConv_injective
    change (G.inS S).comp ((ofConv ψ).comp _) =
      (((Algebra.TensorProduct.map (AlgHom.id R S) (f : H.A →ₐ[R] G.A)).comp
        (H.inS S)).comp (ofConv ψ)).comp _
    rw [Algebra.TensorProduct.map_comp_includeLeft]
    rfl
  rw [charOf, charOf, ← pairing_postComp, e, ← pairing_dual]
  congr 1

/-- **Change of coefficients**: `χ_{σ ∘ ψ} = (σ ⊗ A)(χ_ψ)` for `σ : S → S'`. -/
theorem charOf_postComp {S' : Type*} [CommRing S'] [Algebra R S'] (σ : S →ₐ[R] S')
    (ψ : G.dual.points S) :
    G.charOf S' (G.dual.postComp σ ψ) =
      Algebra.TensorProduct.map σ (AlgHom.id R G.A) (G.charOf S ψ) := by
  rw [charOf, charOf, ← pairing_postComp]
  congr 1
  apply WithConv.ofConv_injective
  change G.inA S' = (Algebra.TensorProduct.map σ (AlgHom.id R G.A)).comp (G.inA S)
  rw [Algebra.TensorProduct.map_comp_includeRight, AlgHom.comp_id]

/-- `S ⊗ Δ : S ⊗ A → S ⊗ (A ⊗ A)`. -/
abbrev comulS : S ⊗[R] G.A →ₐ[R] S ⊗[R] (G.A ⊗[R] G.A) :=
  Algebra.TensorProduct.map (AlgHom.id R S) (Bialgebra.comulAlgHom R G.A)

/-- `b ↦ b ⊗ 1`. -/
abbrev inlS : S ⊗[R] G.A →ₐ[R] S ⊗[R] (G.A ⊗[R] G.A) :=
  Algebra.TensorProduct.map (AlgHom.id R S) Algebra.TensorProduct.includeLeft

/-- `b ↦ 1 ⊗ b`. -/
abbrev inrS : S ⊗[R] G.A →ₐ[R] S ⊗[R] (G.A ⊗[R] G.A) :=
  Algebra.TensorProduct.map (AlgHom.id R S) Algebra.TensorProduct.includeRight

/-- **`χ_ψ` is group-like**: `(S ⊗ Δ)(χ_ψ) = (χ_ψ ⊗ 1)(1 ⊗ χ_ψ)`. -/
theorem charOf_comul (ψ : G.dual.points S) :
    G.comulS S (G.charOf S ψ) = G.inlS S (G.charOf S ψ) * G.inrS S (G.charOf S ψ) := by
  set T := S ⊗[R] (G.A ⊗[R] G.A)
  let ι : G.A ⊗[R] G.A →ₐ[R] T := Algebra.TensorProduct.includeRight
  have hψ : ∀ σ : S ⊗[R] G.A →ₐ[R] T, σ.comp (G.inS S) = Algebra.TensorProduct.includeLeft →
      G.dual.postComp σ (G.dual.postComp (G.inS S) ψ) =
        G.dual.postComp (Algebra.TensorProduct.includeLeft (S := R)) ψ := by
    intro σ hσ
    apply WithConv.ofConv_injective
    change σ.comp ((G.inS S).comp (ofConv ψ)) = _
    rw [← AlgHom.comp_assoc, hσ]
    rfl
  have h1 : G.postComp (G.comulS S) (toConv (G.inA S)) =
      G.postComp ι (toConv (Bialgebra.comulAlgHom R G.A)) := by
    apply WithConv.ofConv_injective
    exact Algebra.TensorProduct.map_comp_includeRight _ _
  have hl : G.postComp (G.inlS S) (toConv (G.inA S)) =
      G.postComp ι (toConv (Algebra.TensorProduct.includeLeft (S := R))) := by
    apply WithConv.ofConv_injective
    exact Algebra.TensorProduct.map_comp_includeRight _ _
  have hr : G.postComp (G.inrS S) (toConv (G.inA S)) =
      G.postComp ι (toConv Algebra.TensorProduct.includeRight) := by
    apply WithConv.ofConv_injective
    exact Algebra.TensorProduct.map_comp_includeRight _ _
  rw [charOf, ← pairing_postComp, ← pairing_postComp, ← pairing_postComp, h1, hl, hr,
    hψ _ (Algebra.TensorProduct.map_comp_includeLeft _ _),
    hψ _ (Algebra.TensorProduct.map_comp_includeLeft _ _),
    hψ _ (Algebra.TensorProduct.map_comp_includeLeft _ _), ← pairing_mul_left, ← map_mul,
    inl_mul_inr]

end FFGroupScheme

end PadicHodge
