/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.HodgeTateOL
import PadicHodge.FormalGroup.LayerIntegral
import PadicHodge.GroupScheme.HopfDisc
import PadicHodge.GroupScheme.IntegralConn

/-!
# The discriminant formula [Hong, Prop. 3.5.1] over `O_{K'}`

Let `G` be a `p`-divisible group of height `h` over `O_L` (`L = K'` finite over `ℚ_p`), with
connected part `G⁰ ≅ F[p^∞]`, `F` of dimension `d`, and `G_v = Spec A_v`. Then
**`disc(A_v / O_L) = (p^{d v p^{hv}})`** (`PDivGroup.discIdeal_eq_OL`).

Proof (via integrals instead of Tate's trace formula for complete intersections):

1. *Connected case* `G = F[p^∞]` (`PDivFGL.exists_trace_eq_smul_OL`, `PDivFGL.discIdeal_eq_OL`):
   `Λ = det b ∈ A_v` is an integral with `ε(Λ) = c := (p^v)^d` (Cramer, `LayerIntegral.lean`).
   The Cartier dual `G^∨` has connected part `F'[p^∞]` with `h = d + d'` (Serre–Tate over `O_L`
   and Tate's theorem [Hong, Thm. 3.4.10], `tate_dalphaGen`), so `A_v^∨` has an integral `λ`
   with `λ(1) = (p^v)^{d'}` (Cramer for `F'`, lifted from the connected component). The trace
   formula `(Tr ⊗ id)((x ⊗ 1)Δ(Λ)) = c S(x)` (`trL_mul_comul_integral`, over `ℚ̄_p`, where
   `G_v` is étale) and `c λ(1) = (p^v)^h = |G_v|` give `Tr = c (λ ∘ S)`
   (`trace_eq_smul_of_dual_integral`), hence `disc(A_v) = (c^{p^{hv}})`
   (`discIdeal_eq_of_trace_eq_smul`).
2. *General case*: `Λ` and `Tr(A_v⁰) ⊆ (c)` are transported along `G⁰_v ≅ F[p^v]`, `Λ` is lifted
   to `A_v` by the idempotent `e₀`, and `Tr(A_v) ⊆ (c)` by the connected–étale reduction
   `trace_mem_of_connectedComponent`.

## References

* [Hong] S. Hong, *Notes on p-adic Hodge theory*, Prop. 3.5.1 (stated there without proof), and
  the sketch in the remark after it.
* [Tate] J. Tate, *p-divisible groups*, §(2.2), Prop. 2 (the statement; Tate's proof uses
  multiplicativity in exact sequences and his Lemma 1 on Jacobians, cf. [Haines, §2.3],
  [Lipnowski, App.]).
-/

noncomputable section

open Module TensorProduct Coalgebra HopfAlgebra WithConv

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime] {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
  [FiniteDimensional ℚ_[p] L]

namespace OL

omit [FiniteDimensional ℚ_[p] L] in
theorem algebraMap_qbar_injective : Function.Injective (algebraMap (OL L) (PadicAlgCl p)) := by
  intro x y h
  have h1 : ((algebraMap (OL L) (PadicAlgCl p) x : PadicAlgCl p) : ℂ_[p]) =
      ((algebraMap (OL L) (PadicAlgCl p) y : PadicAlgCl p) : ℂ_[p]) := by rw [h]
  rw [algebraMap_qbar_cp, algebraMap_qbar_cp] at h1
  exact toOC_injective (Subtype.val_injective h1)

omit [FiniteDimensional ℚ_[p] L] in
theorem natCast_ne_zero {n : ℕ} (hn : n ≠ 0) : (n : OL L) ≠ 0 := by
  intro h
  have := congrArg (algebraMap (OL L) (PadicAlgCl p)) h
  rw [map_natCast, map_zero, Nat.cast_eq_zero] at this
  exact hn this

end OL

omit [FiniteDimensional ℚ_[p] L] in
/-- Layers of a `p`-divisible group over `O_L` are étale over `ℚ̄_p`. -/
theorem PDivGroup.isEtale_layer_qbar (G : PDivGroup (OL L) p) (v : ℕ) :
    ((G.G v).baseChange (PadicAlgCl p)).IsEtale := by
  have hu : IsUnit (p : PadicAlgCl p) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  exact (G.baseChange (PadicAlgCl p)).isEtale_of_isUnit hu v

namespace PDivFGL

open PDivGroup FFGroupScheme

variable {d : ℕ} (P : PDivFGL (OL L) d p)

/-- `(G^∨)⁰ ≅ F'[p^∞]` over `O_L` with `h = d + d'` ([Hong, Thm. 2.2.19] via Tate's
theorem [Hong, Thm. 3.4.10]). -/
theorem exists_connPart_dual_iso_height_eq_OL :
    ∃ (d' : ℕ) (P' : PDivFGL (OL L) d' p)
      (φ : PDivGroup.Hom P.dualPDiv.connPart P'.pdivGroup)
      (ψ : PDivGroup.Hom P'.pdivGroup P.dualPDiv.connPart),
      φ.comp ψ = PDivGroup.Hom.id _ ∧ ψ.comp φ = PDivGroup.Hom.id _ ∧ P.height = d + d' := by
  obtain ⟨d', P', φ, ψ, hφψ, hψφ, hle⟩ := P.exists_connPart_dual_iso_height_le_OL
  refine ⟨d', P', φ, ψ, hφψ, hψφ, ?_⟩
  exact (P.tate_dalphaGen L P' φ ψ L (fun σ => σ) (fun _ _ => rfl) P.tateRepOL
    (fun _ _ _ => rfl) P.tateRepDualOL (fun _ _ _ => rfl) P'.tateRepOL (fun _ _ _ => rfl)
    P'.tateRepDualOL (fun _ _ _ => rfl) OL.p_mem OL.algebraMap_qbar_cp OL.galFixedOver
    OL.norm_lt_one hφψ hle).2.2.2.2

/-- **The trace of `F[p^v]` over `O_L` is divisible by `(p^v)^d`.** -/
theorem trace_mem_OL (v : ℕ) (x : P.A v) :
    Algebra.trace (OL L) (P.A v) x ∈ Ideal.span {((p ^ v : ℕ) : OL L) ^ d} := by
  obtain ⟨d', P', φ, ψ, -, hψφ, hh⟩ := P.exists_connPart_dual_iso_height_eq_OL
  -- the integral of `A_v^∨`, from `F'[p^v]`
  have hsurj : Function.Surjective (φ.f v) := fun y =>
    ⟨ψ.f v y, congrArg (fun f : PDivGroup.Hom _ _ => f.f v y) hψφ⟩
  have hΛ1 := FFGroupScheme.IsIntegral.map (φ.f v) hsurj (P'.isIntegral_layerDet v)
  obtain ⟨l, hl, hlc⟩ :=
    ((P.groupScheme v).dual).exists_isIntegral_of_connectedComponent hΛ1
  replace hlc : ofConv l 1 = ((p ^ v : ℕ) : OL L) ^ d' :=
    hlc.trans ((counit_map _ _).trans (P'.counit_layerDet v))
  have hN : ((Module.finrank (OL L) (P.A v) : ℕ) : OL L) = ((p ^ v : ℕ) : OL L) ^ d *
      ((p ^ v : ℕ) : OL L) ^ d' := by
    rw [← pow_add, ← hh, FGL.finrank_layer P.isPDivisible v]
    push_cast
    ring
  have hT := (P.groupScheme v).trace_eq_smul_of_integrals OL.algebraMap_qbar_injective
    (P.pdivGroup.isEtale_layer_qbar v) (P.isIntegral_layerDet v) hl
    ((congrArg₂ (· * ·) (P.counit_layerDet v) hlc).trans hN.symm)
    (fun h0 => mul_ne_zero (pow_ne_zero _ (OL.natCast_ne_zero (pow_ne_zero _ hp.out.ne_zero)))
      (pow_ne_zero _ (OL.natCast_ne_zero (pow_ne_zero _ hp.out.ne_zero))) (hN.symm.trans h0))
  have hx := LinearMap.congr_fun hT x
  rw [LinearMap.smul_apply, smul_eq_mul] at hx
  rw [show Algebra.trace (OL L) (P.A v) x = _ from
    hx.trans (congrArg (· * _) (P.counit_layerDet v))]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

/-- **[Hong, Prop. 3.5.1] for `F[p^∞]` over `O_L`**:
`disc(A_v / O_L) = ((p^v)^{d p^{hv}})`. -/
theorem discIdeal_eq_OL (v : ℕ) :
    discIdeal (OL L) (P.A v) =
      Ideal.span {(((p ^ v : ℕ) : OL L) ^ d) ^ (p ^ (P.height * v))} := by
  have hc0 : ((p ^ v : ℕ) : OL L) ^ d ≠ 0 :=
    pow_ne_zero _ (OL.natCast_ne_zero (pow_ne_zero _ hp.out.ne_zero))
  have h := (P.groupScheme v).discIdeal_eq_of_integral_of_trace_mem
    OL.algebraMap_qbar_injective (P.pdivGroup.isEtale_layer_qbar v) (P.isIntegral_layerDet v)
    ((P.counit_layerDet v).trans_ne hc0)
    (fun x => (congrArg (fun c => _ ∈ Ideal.span {c}) (P.counit_layerDet v)).mpr
      (P.trace_mem_OL v x))
  refine h.trans ?_
  rw [show Module.finrank (OL L) (P.groupScheme v).A = p ^ (P.height * v) from
    FGL.finrank_layer P.isPDivisible v]
  exact congrArg (fun c => Ideal.span {c ^ _}) (P.counit_layerDet v)

end PDivFGL

namespace PDivGroup

open FFGroupScheme

variable (G : PDivGroup (OL L) p)

/-- **[Hong, Prop. 3.5.1] over `O_L`** (the discriminant formula): if `G⁰ ≅ F[p^∞]` with `F` of
dimension `d`, then `disc(A_v / O_L) = ((p^v)^{d p^{hv}})` for `G_v = Spec A_v`. -/
theorem discIdeal_eq_of_iso_OL {d : ℕ} (P : PDivFGL (OL L) d p)
    (φ : PDivGroup.Hom G.connPart P.pdivGroup) (ψ : PDivGroup.Hom P.pdivGroup G.connPart)
    (hφψ : φ.comp ψ = PDivGroup.Hom.id _) (hψφ : ψ.comp φ = PDivGroup.Hom.id _) (v : ℕ) :
    discIdeal (OL L) (G.G v).A =
      Ideal.span {(((p ^ v : ℕ) : OL L) ^ d) ^ (p ^ (G.height * v))} := by
  set c : OL L := ((p ^ v : ℕ) : OL L) ^ d with hc_def
  have hc : c ≠ 0 := pow_ne_zero _ (OL.natCast_ne_zero (pow_ne_zero _ hp.out.ne_zero))
  -- `φ_v : A(F[p^v]) → A(G_v⁰)` is bijective
  have hbij : Function.Bijective (φ.f v) := by
    refine ⟨fun x y hxy => ?_, fun y => ⟨ψ.f v y, ?_⟩⟩
    · have h1 := congrArg (fun f : PDivGroup.Hom _ _ => f.f v x) hφψ
      have h2 := congrArg (fun f : PDivGroup.Hom _ _ => f.f v y) hφψ
      simp only at h1 h2
      change (ψ.f v) ((φ.f v) x) = x at h1
      change (ψ.f v) ((φ.f v) y) = y at h2
      rw [← h1, ← h2, hxy]
    · exact congrArg (fun f : PDivGroup.Hom _ _ => f.f v y) hψφ
  -- the integral
  have hΛ0 := FFGroupScheme.IsIntegral.map (φ.f v) hbij.2 (P.isIntegral_layerDet v)
  obtain ⟨Λ, hΛ, hΛc⟩ := (G.G v).exists_isIntegral_of_connectedComponent hΛ0
  replace hΛc : Coalgebra.counit (R := OL L) Λ = c :=
    hΛc.trans ((counit_map _ _).trans (P.counit_layerDet v))
  -- traces of `G_v⁰`, then of `G_v`
  have htr0 : ∀ y : (G.G v).connectedComponent.A,
      Algebra.trace (OL L) (G.G v).connectedComponent.A y ∈ Ideal.span {c} := by
    intro y
    obtain ⟨z, rfl⟩ := hbij.2 y
    have := trace_map_of_bijective (R := OL L)
      ((φ.f v : (P.groupScheme v).A →ₐ[OL L] (G.connPart.G v).A)) hbij z
    change Algebra.trace (OL L) (G.connPart.G v).A _ ∈ _
    erw [this]
    exact P.trace_mem_OL v z
  have h := (G.G v).discIdeal_eq_of_integral_of_trace_mem OL.algebraMap_qbar_injective
    (G.isEtale_layer_qbar v) hΛ (by rw [hΛc]; exact hc)
    (fun x => by rw [hΛc]; exact (G.G v).trace_mem_of_connectedComponent htr0 x)
  rw [hΛc, show finrank (OL L) (G.G v).A = p ^ (G.height * v) from G.order_eq v] at h
  exact h

/-- **[Hong, Prop. 3.5.1] over `O_L`**: there are `d` (the dimension of `G⁰ ≅ F[p^∞]`) such
that `disc(A_v / O_L) = ((p^v)^{d p^{hv}})` for all `v`. -/
theorem exists_discIdeal_eq_OL :
    ∃ (d : ℕ) (P : PDivFGL (OL L) d p) (φ : PDivGroup.Hom G.connPart P.pdivGroup)
      (ψ : PDivGroup.Hom P.pdivGroup G.connPart),
      φ.comp ψ = PDivGroup.Hom.id _ ∧ ψ.comp φ = PDivGroup.Hom.id _ ∧
      ∀ v, discIdeal (OL L) (G.G v).A =
        Ideal.span {(((p ^ v : ℕ) : OL L) ^ d) ^ (p ^ (G.height * v))} := by
  obtain ⟨d, P, φ, ψ, h1, h2⟩ := G.exists_connPart_iso_OL
  exact ⟨d, P, φ, ψ, h1, h2, G.discIdeal_eq_of_iso_OL P φ ψ h1 h2⟩

end PDivGroup

end PadicHodge
