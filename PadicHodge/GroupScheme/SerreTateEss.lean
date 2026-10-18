/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.SerreTateLift
import PadicHodge.GroupScheme.SerreTateSpecial

/-!
# Serre–Tate over `ℤ_p`: essential surjectivity ([Hong, Thm. 2.2.16])

**`PDivGroup.exists_pdivFGL_iso`**: every connected `p`-divisible group `H` over `ℤ_p` (all
layers `G_v` connected) is isomorphic to `F[p^∞]` for a `p`-divisible formal group law `F`
(`PDivFGL`): there are homomorphisms `H → F[p^∞]` and `F[p^∞] → H` inverse to each other.
Together with full faithfulness (`FGL.Hom.pdivEquiv`, `FormalGroup/SerreTateHom.lean`) this is
[Hong, Thm. 2.2.16] over `R = ℤ_p`.

Proof: the special fibre `H ⊗ 𝔽_p` is connected (`A_v ⊗ 𝔽_p = A_v/pA_v` is a quotient of the
local ring `A_v`), so it has coordinates `ρ̄_v : 𝔽_p[[t]] ↠ A_v ⊗ 𝔽_p` with
`ker ρ̄_v ⊆ (t_j^{p^v})` (`PDivGroup.exists_coords`, [Hong, Prop. 2.2.13]); these lift to
coordinates on `H` (`SerreTate.SpecialFibreData.coords`), which give the formal group law and the
isomorphism (`SerreTate.exists_iso_of_specialFibre`).
-/

noncomputable section

open IsLocalRing TensorProduct

namespace PadicHodge

namespace SerreTate

variable {p : ℕ} [hp : Fact p.Prime]

/-- Reduction `ℤ_p → 𝔽_p`. -/
def toZModD : ZpD p →+* ZMod p := PadicInt.toZMod

/-- `𝔽_p` as a `ℤ_p`-algebra. -/
abbrev algebraZModD : Algebra (ZpD p) (ZMod p) := toZModD.toAlgebra

attribute [local instance] algebraZModD

theorem algebraMap_zmod_surjective : Function.Surjective (algebraMap (ZpD p) (ZMod p)) :=
  ZMod.ringHom_surjective toZModD

theorem algebraMap_zmod_eq_zero_iff (r : ZpD p) :
    algebraMap (ZpD p) (ZMod p) r = 0 ↔ r ∈ maximalIdeal (ZpD p) := by
  rw [← RingHom.mem_ker]
  exact (Set.ext_iff.mp (congrArg SetLike.coe (PadicInt.ker_toZMod (p := p))) r)

/-- The special fibre of a connected `p`-divisible group over `ℤ_p` is connected. -/
theorem isConnected_baseChange {H : PDivGroup (ZpD p) p} (hconn : ∀ v, (H.G v).IsConnected)
    (v : ℕ) : ((H.baseChange (ZMod p)).G v).IsConnected := by
  haveI : IsLocalRing (H.G v).A := hconn v
  haveI : Nontrivial (ZMod p ⊗[ZpD p] (H.G v).A) :=
    Module.nontrivial_of_finrank_pos (R := ZMod p) (by
      rw [Module.finrank_baseChange]
      have : Module.finrank (ZpD p) (H.G v).A = p ^ (H.height * v) := H.order_eq v
      rw [this]
      exact pow_pos hp.out.pos _)
  change IsLocalRing (ZMod p ⊗[ZpD p] (H.G v).A)
  exact IsLocalRing.of_surjective' (Algebra.TensorProduct.includeRight (R := ZpD p)
    (A := ZMod p) (B := (H.G v).A)).toRingHom
    (SpecialFibreData.π_surjective (k := ZMod p) algebraMap_zmod_surjective v)

/-- **The special-fibre data** of a connected `p`-divisible group over `ℤ_p`. -/
theorem exists_specialFibreData {H : PDivGroup (ZpD p) p} (hconn : ∀ v, (H.G v).IsConnected) :
    ∃ d, Nonempty (SpecialFibreData H (ZMod p) d) := by
  obtain ⟨d, ρ, hsurj, hcompat, hker, -⟩ :=
    (H.baseChange (ZMod p)).exists_coords (isConnected_baseChange hconn)
  exact ⟨d, ⟨{
    ρ := ρ
    surj := hsurj
    compat := fun v g => congrArg (fun φ => φ g) (hcompat v)
    ker_le := fun v => hker v v le_rfl }⟩⟩

end SerreTate

namespace PDivGroup

/-- **Serre–Tate, essential surjectivity** ([Hong, Thm. 2.2.16]): a connected `p`-divisible group
`H` over `ℤ_p` is isomorphic to `F[p^∞]` for a `p`-divisible formal group law `F`. -/
theorem exists_pdivFGL_iso {p : ℕ} [Fact p.Prime] (H : PDivGroup (ZpD p) p)
    (hconn : ∀ v, (H.G v).IsConnected) :
    ∃ (d : ℕ) (P : PDivFGL (ZpD p) d p) (φ : PDivGroup.Hom H P.pdivGroup)
      (ψ : PDivGroup.Hom P.pdivGroup H),
      φ.comp ψ = PDivGroup.Hom.id _ ∧ ψ.comp φ = PDivGroup.Hom.id _ := by
  letI := SerreTate.algebraZModD (p := p)
  obtain ⟨d, ⟨S⟩⟩ := SerreTate.exists_specialFibreData hconn
  exact ⟨d, SerreTate.exists_iso_of_specialFibre hconn SerreTate.algebraMap_zmod_surjective
    SerreTate.algebraMap_zmod_eq_zero_iff S⟩

end PDivGroup

end PadicHodge
