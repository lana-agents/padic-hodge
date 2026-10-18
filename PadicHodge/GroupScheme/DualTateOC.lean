/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.DualTateField
import PadicHodge.GroupScheme.CartierPerfectOC
import PadicHodge.GroupScheme.Faithful

/-!
# The dual Tate module over `O_{ℂ_p}`

Let `G` be a `p`-divisible group over a nontrivial ring `R` with `R → O_{ℂ_p}` (e.g. `R = ℤ_p`).
Over the algebraically closed field `ℂ_p` we have `#G_v(ℂ_p) = #G_v^∨(ℂ_p) = |G_v|`
(`card_points_sepClosed`, `card_dual_points_Cp`), so `DualTateField.lean` applies, and
`G_v(O_{ℂ_p}) = G_v(ℂ_p)` (`pointsOCEquiv`, [Hong, Lemma 3.4.1]) transports it to `O_{ℂ_p}`:

* `dual_incl_surjective_OC`, **`DualTate.proj_surjective_OC`**: `T_p(G^∨)(O_{ℂ_p}) → G_v^∨(O_{ℂ_p})`
  is surjective;
* **`DualTate.exists_pow_eq_OC`**: `y ∈ T_p(G^∨)(O_{ℂ_p})` with `y_1 = 1` is a `p`-th power;
* **`exists_pairing_eq_OC`** (perfectness over `O_{ℂ_p}`, surjective half; the injective half is
  `eq_one_of_pairing_OC`): every character `G_v^∨(O_{ℂ_p}) → O_{ℂ_p}` is `⟨t, ·⟩` for some
  `t ∈ G_v(O_{ℂ_p})` ([Hong, Prop. 3.4.6], (3.6)).
-/

noncomputable section

open WithConv

namespace PadicHodge

namespace PDivGroup

open FFGroupScheme

variable {p : ℕ} [hp : Fact p.Prime] {R : Type} [CommRing R] [Nontrivial R] [Algebra R (OC p)]
  (G : PDivGroup R p)

theorem p_ne_zero_Cp : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero

/-- `#G_v(ℂ_p) = |G_v|`. -/
theorem card_points_Cp (w : ℕ) :
    letI := algebraCpOfOC (p := p) R
    Nat.card ((G.G w).points ℂ_[p]) = (G.G w).order := by
  letI := algebraCpOfOC (p := p) R
  rw [G.card_points_sepClosed ℂ_[p] p_ne_zero_Cp, G.order_eq]

omit [Nontrivial R] [Algebra R (OC p)] hp in
theorem univPt_pow_eq_one (w : ℕ) : (G.G w).univPt ^ (p ^ w) = 1 :=
  G.pow_eq_one w _ _

/-- `#G_v^∨(ℂ_p) = |G_v|`. -/
theorem card_dual_points_Cp' (w : ℕ) :
    letI := algebraCpOfOC (p := p) R
    Nat.card ((G.G w).dual.points ℂ_[p]) = (G.G w).order :=
  (G.G w).card_dual_points_Cp (pow_ne_zero w hp.out.ne_zero) (G.univPt_pow_eq_one w)

omit [Nontrivial R] in
/-- `O_{ℂ_p} → ℂ_p` commutes with the maps on points. -/
theorem pointsOCEquiv_mapPoints {H H' : FFGroupScheme R} (f : FFGroupScheme.Hom H H')
    (φ : H.points (OC p)) :
    letI := algebraCpOfOC (p := p) R
    H'.pointsOCEquiv (f.mapPoints (OC p) φ) = f.mapPoints ℂ_[p] (H.pointsOCEquiv φ) := rfl

/-- **`i_v^∨ : G_{v+1}^∨(O_{ℂ_p}) → G_v^∨(O_{ℂ_p})` is surjective.** -/
theorem dual_incl_surjective_OC (v : ℕ) :
    Function.Surjective ((G.incl v).dual.mapPoints (OC p)) := by
  letI := algebraCpOfOC (p := p) R
  intro ψ
  obtain ⟨ψ', hψ'⟩ := G.dual_incl_surjective_of_card ℂ_[p] G.card_points_Cp G.card_dual_points_Cp'
    v ((G.G v).dual.pointsOCEquiv ψ)
  refine ⟨(G.G (v + 1)).dual.pointsOCEquiv.symm ψ', (G.G v).dual.pointsOCEquiv.injective ?_⟩
  rw [pointsOCEquiv_mapPoints, MulEquiv.apply_symm_apply, hψ']

/-- **`T_p(G^∨)(O_{ℂ_p}) → G_v^∨(O_{ℂ_p})` is surjective.** -/
theorem DualTate.proj_surjective_OC (v : ℕ) (y : (G.G v).dual.points (OC p)) :
    ∃ z : G.DualTate (OC p), z.1 v = y :=
  DualTate.proj_surjective G G.dual_incl_surjective_OC v y

/-- `T_p(G^∨)(O_{ℂ_p}) ≃ T_p(G^∨)(ℂ_p)`. -/
def dualTateOCEquiv :
    letI := algebraCpOfOC (p := p) R
    G.DualTate (OC p) ≃* G.DualTate ℂ_[p] := by
  letI := algebraCpOfOC (p := p) R
  exact
    { toFun := fun y => ⟨fun v => (G.G v).dual.pointsOCEquiv (y.1 v), fun v => by
        beta_reduce; rw [y.2 v]; rfl⟩
      invFun := fun y => ⟨fun v => (G.G v).dual.pointsOCEquiv.symm (y.1 v), fun v => by
        beta_reduce
        apply (G.G v).dual.pointsOCEquiv.injective
        rw [MulEquiv.apply_symm_apply, pointsOCEquiv_mapPoints, MulEquiv.apply_symm_apply,
          y.2 v]⟩
      left_inv := fun y => Subtype.ext (funext fun v => MulEquiv.symm_apply_apply _ _)
      right_inv := fun y => Subtype.ext (funext fun v => MulEquiv.apply_symm_apply _ _)
      map_mul' := fun y y' => Subtype.ext (funext fun v => map_mul _ _ _) }

/-- **A point `y ∈ T_p(G^∨)(O_{ℂ_p})` with `y_1 = 1` is a `p`-th power.** -/
theorem DualTate.exists_pow_eq_OC (y : G.DualTate (OC p)) (hy : y.1 1 = 1) :
    ∃ w : G.DualTate (OC p), w ^ p = y := by
  letI := algebraCpOfOC (p := p) R
  obtain ⟨w, hw⟩ := DualTate.exists_pow_eq_of_card G ℂ_[p] G.card_points_Cp
    G.card_dual_points_Cp' (G.dualTateOCEquiv y) (by
      change (G.G 1).dual.pointsOCEquiv (y.1 1) = 1
      rw [hy, map_one])
  refine ⟨G.dualTateOCEquiv.symm w, G.dualTateOCEquiv.injective ?_⟩
  rw [map_pow, MulEquiv.apply_symm_apply, hw]

end PDivGroup

namespace FFGroupScheme

variable {p : ℕ} [hp : Fact p.Prime] {R : Type} [CommRing R] [Nontrivial R] [Algebra R (OC p)]

/-- **Every character of `G^∨(O_{ℂ_p})` is `⟨t, ·⟩` for some `t ∈ G(O_{ℂ_p})`**, for `G` killed
by `n ≠ 0` with `#G(ℂ_p) = |G|`. -/
theorem exists_pairing_eq_OC (G : FFGroupScheme R) {n : ℕ} (hn : n ≠ 0)
    (hG : G.univPt ^ n = 1)
    (hcard : letI := algebraCpOfOC (p := p) R; Nat.card (G.points ℂ_[p]) = G.order)
    (χ : G.dual.points (OC p) →* OC p) :
    ∃ t : G.points (OC p), ∀ ψ, G.pairing (OC p) t ψ = χ ψ := by
  letI := algebraCpOfOC (p := p) R
  let ι : OC p →ₐ[R] ℂ_[p] := { (OC p).subtype with commutes' := fun _ => rfl }
  let χ' : G.dual.points ℂ_[p] →* ℂ_[p] :=
    ι.toMonoidHom.comp (χ.comp G.dual.pointsOCEquiv.symm.toMonoidHom)
  obtain ⟨t', ht'⟩ := (G.pairingHom'_bijective (S := ℂ_[p]) hcard
    (G.card_dual_points_Cp hn hG)).2 χ'
  refine ⟨G.pointsOCEquiv.symm t', fun ψ => Subtype.ext ?_⟩
  have h1 := DFunLike.congr_fun ht' (G.dual.pointsOCEquiv ψ)
  have h2 := G.pairing_postComp (OC p) ι (G.pointsOCEquiv.symm t') ψ
  change G.pairing ℂ_[p] (G.pointsOCEquiv (G.pointsOCEquiv.symm t'))
    (G.dual.pointsOCEquiv ψ) = ι _ at h2
  rw [MulEquiv.apply_symm_apply] at h2
  change ι (G.pairing (OC p) _ ψ) = ι (χ ψ)
  rw [← h2]
  change G.cartierPairingBase ℂ_[p] t' _ = _ at h1
  rw [cartierPairingBase_apply] at h1
  rw [h1]
  change ι (χ (G.dual.pointsOCEquiv.symm (G.dual.pointsOCEquiv ψ))) = _
  rw [MulEquiv.symm_apply_apply]

end FFGroupScheme

end PadicHodge
