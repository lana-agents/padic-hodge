/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.OC
import PadicHodge.GroupScheme.PDivisibleHom
import PadicHodge.GroupScheme.EtaleUnramified

/-!
# Points of finite flat group schemes with values in `O_{ℂ_p}` and in `ℂ_p`

* `norm_le_one_of_algHom` (by `norm_le_one_of_isIntegral` of `EtaleUnramified.lean`): every
  `R`-algebra map `A → ℂ_p` from a finite `R`-algebra
  (`R → O_{ℂ_p}`) takes values in `O_{ℂ_p}`;
* **`FFGroupScheme.pointsOCEquiv : G(O_{ℂ_p}) ≃* G(ℂ_p)`** for finite flat `G` over such `R`
  (e.g. the layers `G_v` and their Cartier duals `G_v^∨` over `ℤ_p`): this identifies the
  points used for `α` ([Hong, Prop. 3.4.9]: `G_v(O_{C_K}) = G_v(C_K)`, Lemma 3.4.1) with the
  points over the field `ℂ_p`, where the Cartier pairing is perfect (`CartierPerfect.lean`).
-/

noncomputable section

open WithConv

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime]

/-- `R → O_{ℂ_p} ⊆ ℂ_p` as an algebra structure on `ℂ_p`. -/
abbrev algebraCpOfOC (R : Type*) [CommRing R] [Algebra R (OC p)] : Algebra R ℂ_[p] :=
  ((OC p).subtype.comp (algebraMap R (OC p))).toAlgebra

/-- **Algebra maps from a finite `R`-algebra to `ℂ_p` take values in `O_{ℂ_p}`.** -/
theorem norm_le_one_of_algHom {R A : Type*} [CommRing R] [Algebra R (OC p)] [CommRing A]
    [Algebra R A] [Module.Finite R A] :
    letI := algebraCpOfOC (p := p) R
    ∀ (φ : A →ₐ[R] ℂ_[p]) (a : A), ‖φ a‖ ≤ 1 := by
  letI := algebraCpOfOC (p := p) R
  intro φ a
  exact norm_le_one_of_isIntegral (fun r => (algebraMap R (OC p) r).2) φ
    (Algebra.IsIntegral.isIntegral a)

namespace FFGroupScheme

variable {R : Type*} [CommRing R] [Algebra R (OC p)] (G : FFGroupScheme R)

/-- The `O_{ℂ_p}`-valued point with the same values as a `ℂ_p`-valued point. -/
def toOCPoint :
    letI := algebraCpOfOC (p := p) R
    (G.A →ₐ[R] ℂ_[p]) → (G.A →ₐ[R] OC p) := by
  letI := algebraCpOfOC (p := p) R
  exact fun φ =>
    { toFun := fun a => ⟨φ a, norm_le_one_of_algHom φ a⟩
      map_one' := Subtype.ext (map_one φ)
      map_mul' := fun a b => Subtype.ext (map_mul φ a b)
      map_zero' := Subtype.ext (map_zero φ)
      map_add' := fun a b => Subtype.ext (map_add φ a b)
      commutes' := fun r => Subtype.ext (φ.commutes r) }

/-- **`G(O_{ℂ_p}) ≃* G(ℂ_p)`** for finite flat `G` over `R → O_{ℂ_p}`. -/
def pointsOCEquiv :
    letI := algebraCpOfOC (p := p) R
    G.points (OC p) ≃* G.points ℂ_[p] := by
  letI := algebraCpOfOC (p := p) R
  let ι : OC p →ₐ[R] ℂ_[p] :=
    { (OC p).subtype with commutes' := fun _ => rfl }
  exact
    { toFun := G.postComp ι
      invFun := fun φ => toConv (G.toOCPoint (ofConv φ))
      left_inv := fun φ => rfl
      right_inv := fun φ => rfl
      map_mul' := map_mul (G.postComp ι) }

theorem pointsOCEquiv_apply (φ : G.points (OC p)) (a : G.A) :
    letI := algebraCpOfOC (p := p) R
    ofConv (G.pointsOCEquiv φ) a = ((ofConv φ a : OC p) : ℂ_[p]) := rfl

end FFGroupScheme

end PadicHodge
