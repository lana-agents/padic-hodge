/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.SerreTateLift
import PadicHodge.GroupScheme.SerreTateSpecial

/-!
# Serre–Tate over a coefficient ring: essential surjectivity ([Hong, Thm. 2.2.16])

**`PDivGroup.exists_pdivFGL_iso_of_coeffRing`**: over a coefficient ring `R`
(`SerreTate.CoeffRing`: e.g. `ℤ_p`, or `O_{K'}` for `K'/ℚ_p` finite, `OL L`) with `p ∈ 𝔪_R`,
every connected `p`-divisible group `H` (all layers `G_v` connected) is isomorphic to `F[p^∞]`
for a `p`-divisible formal group law `F` (`PDivFGL`): there are homomorphisms `H → F[p^∞]` and
`F[p^∞] → H` inverse to each other. **`PDivGroup.exists_pdivFGL_iso`** is the case `R = ℤ_p`.
Together with full faithfulness (`FGL.Hom.pdivEquiv`, `FormalGroup/SerreTateHom.lean`) this is
[Hong, Thm. 2.2.16].

Proof: the residue field `k = R/𝔪` is finite (`SerreTate.finite_residueField`, by compactness),
hence perfect, of characteristic `p`. The special fibre `H ⊗ k` is connected (`A_v ⊗ k` is a
quotient of the local ring `A_v`), so it has coordinates `ρ̄_v : k[[t]] ↠ A_v ⊗ k` with
`ker ρ̄_v ⊆ (t_j^{p^v})` (`PDivGroup.exists_coords`, [Hong, Prop. 2.2.13], over any perfect
field); these lift to coordinates on `H` (`SerreTate.SpecialFibreData.coords`), which give the
formal group law and the isomorphism (`SerreTate.exists_iso_of_specialFibre`).
-/

noncomputable section

open IsLocalRing TensorProduct

namespace PadicHodge

namespace SerreTate

section General

variable {R : Type} [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
  {p : ℕ} [hp : Fact p.Prime]

omit [IsAdicComplete (maximalIdeal R) R] in
/-- The special fibre of a connected `p`-divisible group is connected. -/
theorem isConnected_baseChange_of_surjective {k : Type} [Field k] [Algebra R k]
    (hsurj : Function.Surjective (algebraMap R k)) {H : PDivGroup R p}
    (hconn : ∀ v, (H.G v).IsConnected) (v : ℕ) : ((H.baseChange k).G v).IsConnected := by
  haveI : IsLocalRing (H.G v).A := hconn v
  haveI : Nontrivial (k ⊗[R] (H.G v).A) :=
    Module.nontrivial_of_finrank_pos (R := k) (by
      rw [Module.finrank_baseChange]
      have : Module.finrank R (H.G v).A = p ^ (H.height * v) := H.order_eq v
      rw [this]
      exact pow_pos hp.out.pos _)
  change IsLocalRing (k ⊗[R] (H.G v).A)
  exact IsLocalRing.of_surjective' (Algebra.TensorProduct.includeRight (R := R)
    (A := k) (B := (H.G v).A)).toRingHom
    (SpecialFibreData.π_surjective (k := k) hsurj v)

omit [IsAdicComplete (maximalIdeal R) R] in
/-- **The special-fibre data** of a connected `p`-divisible group, over a perfect field `k` of
characteristic `p` with `R ↠ k`. -/
theorem exists_specialFibreData_of_surjective {k : Type} [Field k] [Algebra R k] [CharP k p]
    [PerfectRing k p] (hsurj : Function.Surjective (algebraMap R k)) {H : PDivGroup R p}
    (hconn : ∀ v, (H.G v).IsConnected) :
    ∃ d, Nonempty (SpecialFibreData H k d) := by
  obtain ⟨d, ρ, hsurj', hcompat, hker, -⟩ :=
    (H.baseChange k).exists_coords (isConnected_baseChange_of_surjective hsurj hconn)
  exact ⟨d, ⟨{
    ρ := ρ
    surj := hsurj'
    compat := fun v g => congrArg (fun φ => φ g) (hcompat v)
    ker_le := fun v => hker v v le_rfl }⟩⟩

omit [IsAdicComplete (maximalIdeal R) R] in
/-- The residue field of `R` has characteristic `p` if `p ∈ 𝔪`. -/
theorem charP_residueField (hpm : (p : R) ∈ maximalIdeal R) : CharP (ResidueField R) p :=
  (CharP.charP_iff_prime_eq_zero hp.out).mpr (by
    rw [← map_natCast (IsLocalRing.residue R), IsLocalRing.residue_eq_zero_iff]
    exact hpm)

variable [IsDomain R] [CoeffRing R]

omit [IsAdicComplete (maximalIdeal R) R] [IsDomain R] in
/-- The residue field of a coefficient ring is perfect. -/
theorem perfectRing_residueField (hpm : (p : R) ∈ maximalIdeal R) :
    PerfectRing (ResidueField R) p := by
  haveI := charP_residueField hpm
  haveI : Finite (ResidueField R) := finite_residueField
  infer_instance

end General

end SerreTate

namespace PDivGroup

/-- **Serre–Tate, essential surjectivity** ([Hong, Thm. 2.2.16]) over a coefficient ring `R`
with `p ∈ 𝔪_R` (e.g. `O_{K'}`): a connected `p`-divisible group `H` over `R` is isomorphic to
`F[p^∞]` for a `p`-divisible formal group law `F`. -/
theorem exists_pdivFGL_iso_of_coeffRing {R : Type} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] [IsDomain R] [SerreTate.CoeffRing R] {p : ℕ}
    [Fact p.Prime] (hpm : (p : R) ∈ maximalIdeal R) (H : PDivGroup R p)
    (hconn : ∀ v, (H.G v).IsConnected) :
    ∃ (d : ℕ) (P : PDivFGL R d p) (φ : PDivGroup.Hom H P.pdivGroup)
      (ψ : PDivGroup.Hom P.pdivGroup H),
      φ.comp ψ = PDivGroup.Hom.id _ ∧ ψ.comp φ = PDivGroup.Hom.id _ := by
  haveI := SerreTate.charP_residueField hpm
  haveI := SerreTate.perfectRing_residueField hpm
  have hsurj : Function.Surjective (algebraMap R (ResidueField R)) :=
    IsLocalRing.residue_surjective
  obtain ⟨d, ⟨S⟩⟩ := SerreTate.exists_specialFibreData_of_surjective hsurj hconn
  exact ⟨d, SerreTate.exists_iso_of_specialFibre hconn hsurj
    (fun r => IsLocalRing.residue_eq_zero_iff r) S⟩

end PDivGroup

namespace SerreTate

/-! ### `ℤ_p` -/

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
    (v : ℕ) : ((H.baseChange (ZMod p)).G v).IsConnected :=
  isConnected_baseChange_of_surjective algebraMap_zmod_surjective hconn v

/-- **The special-fibre data** of a connected `p`-divisible group over `ℤ_p`. -/
theorem exists_specialFibreData {H : PDivGroup (ZpD p) p} (hconn : ∀ v, (H.G v).IsConnected) :
    ∃ d, Nonempty (SpecialFibreData H (ZMod p) d) :=
  exists_specialFibreData_of_surjective algebraMap_zmod_surjective hconn

end SerreTate

namespace PDivGroup

/-- **Serre–Tate, essential surjectivity** ([Hong, Thm. 2.2.16]): a connected `p`-divisible group
`H` over `ℤ_p` is isomorphic to `F[p^∞]` for a `p`-divisible formal group law `F`. -/
theorem exists_pdivFGL_iso {p : ℕ} [Fact p.Prime] (H : PDivGroup (ZpD p) p)
    (hconn : ∀ v, (H.G v).IsConnected) :
    ∃ (d : ℕ) (P : PDivFGL (ZpD p) d p) (φ : PDivGroup.Hom H P.pdivGroup)
      (ψ : PDivGroup.Hom P.pdivGroup H),
      φ.comp ψ = PDivGroup.Hom.id _ ∧ ψ.comp φ = PDivGroup.Hom.id _ :=
  exists_pdivFGL_iso_of_coeffRing ZpD.p_mem H hconn

end PDivGroup

end PadicHodge
