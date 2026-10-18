/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.Divisible

/-!
# `0 → Φ_p(G) → G(O_{ℂ_p}) → ℂ_p^d → 0` for `G = F[p^∞]` ([Hong, Prop. 3.4.7])

Let `F` be a `p`-divisible formal group law over a local ring `R` (discrete topology,
`R → O_{ℂ_p}` sending `𝔪_R` into the open disc) and `G = F[p^∞]` (`PDivFGL.pdivGroup`), so that
`G(O_{ℂ_p}) = F(m_{ℂ_p})` ([Hong, Lemma 3.4.1, Prop. 3.2.3] in the connected case are built into
the definition). The Tate comodule `Φ_p(G) = lim→ G_v(O_{ℂ_p})` is the union of the `G_v(O_{ℂ_p})`
along the closed immersions `G_v ↪ G_{v+1}`:

* `phiPt v : G_v(O_{ℂ_p}) → F(m_{ℂ_p})`, the inverse of `layerPtEquiv` followed by the inclusion
  of `F(m)[p^v]`; injective (`phiPt_injective`), compatible with `G_v ↪ G_{v+1}`
  (`phiPt_incl`);
* **[Hong, Prop. 3.4.7]** (`exact_logHom`): the image of `Φ_p(G)` is exactly the kernel of
  `log_F`, and `log_F` is surjective.
-/

noncomputable section

open MvPowerSeries IsLocalRing PadicHodge.AdicEval

namespace PadicHodge

namespace PDivFGL

universe u

variable {p : ℕ} [hp : Fact p.Prime] {R : Type u} [CommRing R] [IsLocalRing R] [UniformSpace R]
  [DiscreteUniformity R] [Algebra R (OC p)] {d : ℕ} (P : PDivFGL R d p)
  (hR : ∀ r ∈ maximalIdeal R, ‖(algebraMap R (OC p) r : ℂ_[p])‖ < 1)

/-- `G_v(O_{ℂ_p}) → F(m_{ℂ_p})`: the torsion point with the given layer point. -/
def phiPt (v : ℕ) (y : P.A v →ₐ[R] OC p) : P.F.Pt p := ((P.layerPtEquiv hR v).symm y).1

theorem phiPt_mem (v : ℕ) (y : P.A v →ₐ[R] OC p) : P.phiPt hR v y ∈ P.F.torsionBy v :=
  ((P.layerPtEquiv hR v).symm y).2

theorem layerPt_phiPt (v : ℕ) (y : P.A v →ₐ[R] OC p) :
    P.F.layerPt v ⟨P.phiPt hR v y, P.phiPt_mem hR v y⟩ = y :=
  (P.layerPtEquiv hR v).apply_symm_apply y

theorem phiPt_layerPt (v : ℕ) (x : P.F.torsionBy (p := p) v) :
    P.phiPt hR v (P.F.layerPt v x) = x.1 := by
  rw [phiPt]
  exact congrArg Subtype.val ((P.layerPtEquiv hR v).symm_apply_apply x)

theorem phiPt_injective (v : ℕ) : Function.Injective (P.phiPt hR v) := fun _ _ h =>
  (P.layerPtEquiv hR v).symm.injective (Subtype.ext h)

/-- **Compatibility with `G_v ↪ G_{v+1}`.** -/
theorem phiPt_incl (v : ℕ) (y : P.A v →ₐ[R] OC p) :
    P.phiPt hR (v + 1) (y.comp (P.F.layerIncl p v)) = P.phiPt hR v y := by
  conv_lhs => rw [← P.layerPt_phiPt hR v y, FGL.layerPt_comp_layerIncl, phiPt_layerPt]

omit [IsLocalRing R] in
/-- The torsion points are the union of the `F(m)[p^v]`. -/
theorem mem_torsion_iff (x : P.F.Pt p) :
    x ∈ AddCommGroup.torsion (P.F.Pt p) ↔ ∃ v, x ∈ P.F.torsionBy v := by
  rw [AddCommGroup.mem_torsion]
  exact P.F.isOfFinAddOrder_iff x

/-- **[Hong, Prop. 3.4.7] for `G = F[p^∞]`**: `0 → Φ_p(G) → G(O_{ℂ_p}) → ℂ_p^d → 0` is exact:
the points coming from some `G_v(O_{ℂ_p})` are exactly the kernel of `log_F`, and `log_F` is
surjective. -/
theorem exact_logHom :
    (∀ x : P.F.Pt p, P.F.logHom x = 0 ↔ ∃ v, ∃ y : P.A v →ₐ[R] OC p, P.phiPt hR v y = x) ∧
      Function.Surjective (P.F.logHom (p := p)) := by
  refine ⟨fun x => ?_, fun τ => ?_⟩
  · rw [← AddMonoidHom.mem_ker, FGL.ker_logHom, mem_torsion_iff]
    constructor
    · rintro ⟨v, hv⟩
      exact ⟨v, P.F.layerPt v ⟨x, hv⟩, P.phiPt_layerPt hR v ⟨x, hv⟩⟩
    · rintro ⟨v, y, rfl⟩
      exact ⟨v, P.phiPt_mem hR v y⟩
  · obtain ⟨x, hx⟩ := P.logF_surjective hR τ
    exact ⟨x, funext hx⟩

end PDivFGL

end PadicHodge
