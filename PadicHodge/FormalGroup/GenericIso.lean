/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.DiscFormula
import PadicHodge.FormalGroup.TateNonConnOL

/-!
# [Hong, Lemma 3.5.2] over `O_{K'}`: a homomorphism which is an isomorphism on generic fibres is an
isomorphism

Let `f : G → H` be a homomorphism of `p`-divisible groups over `O_L` (`L = K'`) inducing
bijections `G_v(ℚ̄_p) → H_v(ℚ̄_p)` for all `v` (i.e. an isomorphism `T_p G ≅ T_p H`; this holds if
`f` is an isomorphism on generic fibres). Then every `α_v : B_v → A_v` is bijective
(**`PDivGroup.Hom.bijective_of_mapPoints_bijective_OL`**, [Hong, Lemma 3.5.2]).

Proof ([Hong]): `ℚ̄_p ⊗ α_v` is a map of split étale `ℚ̄_p`-algebras inducing a bijection on
points, hence bijective (`bijective_of_bijective_comp_algHom`); `G`, `H` have the same height
(count points) and the same dimension (`V_p(G_L) ≅ V_p(H_L)` and [Hong, Cor. 3.4.11] over `L`,
`finrank_DHT_tateRepOver_neg_one_of_iso_OL`); by the discriminant formula [Hong, Prop. 3.5.1]
(`discIdeal_eq_of_iso_OL`) `disc(A_v) = disc(B_v) ≠ 0`, and `bijective_of_discIdeal_eq` applies.

## References

* [Hong] S. Hong, *Notes on p-adic Hodge theory*, Lemma 3.5.2, Cor. 3.4.11, Prop. 3.5.1.
-/

noncomputable section

open Module TensorProduct WithConv

namespace PadicHodge

universe u

/-- `dim_Ω B = #Hom_Ω(B, Ω)` for a finite étale algebra over a separably closed field. -/
theorem finrank_eq_card_algHom {Ω B : Type*} [Field Ω] [IsSepClosed Ω] [CommRing B]
    [Algebra Ω B] [Module.Finite Ω B] [Algebra.Etale Ω B] :
    finrank Ω B = Nat.card (B →ₐ[Ω] Ω) := by
  have : IsArtinianRing B := IsArtinianRing.of_finite Ω B
  classical
  let X := PrimeSpectrum B
  have : Fintype X := Fintype.ofFinite X
  let e : B ≃ₐ[Ω] (X → Ω) := Algebra.FormallyEtale.equivPiOfIsSepClosed Ω B
  rw [e.toLinearEquiv.finrank_eq, Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card,
    ← card_algHom_pi Ω X]
  exact Nat.card_congr
    { toFun := fun ψ => ψ.comp (e : B →ₐ[Ω] (X → Ω))
      invFun := fun φ => φ.comp (e.symm : (X → Ω) →ₐ[Ω] B)
      left_inv := fun ψ => AlgHom.ext fun a => by simp
      right_inv := fun φ => AlgHom.ext fun b => by simp }

/-- **A map of finite étale algebras over a separably closed field inducing a bijection on
points is bijective.** -/
theorem bijective_of_bijective_comp_algHom {Ω A B : Type*} [Field Ω] [IsSepClosed Ω]
    [CommRing A] [Algebra Ω A] [Module.Finite Ω A] [Algebra.Etale Ω A]
    [CommRing B] [Algebra Ω B] [Module.Finite Ω B] [Algebra.Etale Ω B] (α : B →ₐ[Ω] A)
    (h : Function.Bijective fun x : A →ₐ[Ω] Ω => x.comp α) : Function.Bijective α := by
  have hinj : Function.Injective α := by
    intro a b hab
    refine eq_of_forall_algHom_eq (Ω := Ω) fun y => ?_
    obtain ⟨x, rfl⟩ := h.2 y
    simp [hab]
  have hfin : finrank Ω B = finrank Ω A := by
    rw [finrank_eq_card_algHom, finrank_eq_card_algHom]
    exact (Nat.card_eq_of_bijective _ h).symm
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin
    (f := α.toLinearMap)).mp hinj⟩

namespace FFGroupScheme

variable {R : Type u} [CommRing R] (Ω : Type u) [Field Ω] [IsSepClosed Ω] [Algebra R Ω]

/-- **`Ω ⊗ f` is bijective if `f` is bijective on `Ω`-points** (`G_Ω`, `H_Ω` étale). -/
theorem bijective_baseChange_of_mapPoints {G H : FFGroupScheme R} (f : Hom G H)
    (hG : (G.baseChange Ω).IsEtale) (hH : (H.baseChange Ω).IsEtale)
    (hf : Function.Bijective (f.mapPoints Ω)) :
    Function.Bijective (Algebra.TensorProduct.map (AlgHom.id Ω Ω) (f : H.A →ₐ[R] G.A)) := by
  have : Algebra.Etale Ω (Ω ⊗[R] G.A) := hG
  have : Algebra.Etale Ω (Ω ⊗[R] H.A) := hH
  refine bijective_of_bijective_comp_algHom _ ?_
  let EG := (WithConv.equiv _).symm.trans (G.baseChangePointsEquiv (S := Ω) Ω).toEquiv
  let EH := (WithConv.equiv _).symm.trans (H.baseChangePointsEquiv (S := Ω) Ω).toEquiv
  have hcomm : ∀ x : Ω ⊗[R] G.A →ₐ[Ω] Ω,
      EH (x.comp (Algebra.TensorProduct.map (AlgHom.id Ω Ω) (f : H.A →ₐ[R] G.A))) =
        f.mapPoints Ω (EG x) := fun x => rfl
  have : (fun x : Ω ⊗[R] G.A →ₐ[Ω] Ω =>
      x.comp (Algebra.TensorProduct.map (AlgHom.id Ω Ω) (f : H.A →ₐ[R] G.A))) =
      EH.symm ∘ f.mapPoints Ω ∘ EG := by
    funext x
    simp only [Function.comp_apply, ← hcomm, Equiv.symm_apply_apply]
  rw [this]
  exact EH.symm.bijective.comp (hf.comp EG.bijective)

end FFGroupScheme

namespace PDivGroup

variable {R : Type u} [CommRing R] {p : ℕ} {G H : PDivGroup R p}

/-- Levelwise bijections on points give a bijection on Tate modules. -/
theorem Hom.mapTate_bijective (φ : Hom G H) (S : Type u) [CommRing S] [Algebra R S]
    (hφ : ∀ v, Function.Bijective ((φ.f v).mapPoints S)) : Function.Bijective (φ.mapTate S) := by
  refine ⟨fun x y hxy => Subtype.ext (funext fun v => (hφ v).1 ?_), fun y => ?_⟩
  · exact congrArg (fun z : H.TateModule S => z.1 v) hxy
  · choose x hx using fun v => (hφ v).2 (y.1 v)
    refine ⟨⟨x, fun v => (hφ (v + 1)).1 ?_⟩, Subtype.ext (funext hx)⟩
    rw [← φ.incl_mapPoints, hx, map_pow, hx]
    exact y.2 v

end PDivGroup

variable {p : ℕ} [hp : Fact p.Prime] {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
  [FiniteDimensional ℚ_[p] L]

local notation "K" => PadicAlgCl p

namespace PDivGroup

open FFGroupScheme

/-- `V_p(G_L) ≅ V_p(H_L)` (equivariantly) if `f` is bijective on `ℚ̄_p`-points: the dimensions of
`G⁰` and `H⁰` agree ([Hong, Cor. 3.4.11] over `L`). -/
theorem Hom.dim_eq_of_mapPoints_bijective_OL {G H : PDivGroup (OL L) p} (f : Hom G H)
    (hf : ∀ v, Function.Bijective ((f.f v).mapPoints K))
    {d : ℕ} (P : PDivFGL (OL L) d p) (φ : Hom G.connPart P.pdivGroup)
    (ψ : Hom P.pdivGroup G.connPart) (hφψ : φ.comp ψ = Hom.id _) (hψφ : ψ.comp φ = Hom.id _)
    {d' : ℕ} (P' : PDivFGL (OL L) d' p) (φ' : Hom H.connPart P'.pdivGroup)
    (ψ' : Hom P'.pdivGroup H.connPart) (hφψ' : φ'.comp ψ' = Hom.id _)
    (hψφ' : ψ'.comp φ' = Hom.id _) : d = d' := by
  have hb : Function.Bijective (Hom.baseChange (S := L) f).tateLin := by
    have hb0 := Hom.mapTate_bijective (Hom.baseChange (S := L) f) K fun v => by
      have : ⇑(((Hom.baseChange (S := L) f).f v).mapPoints K) =
          ((H.G v).baseChangePointsEquiv (S := L) K).symm ∘ (f.f v).mapPoints K ∘
            ((G.G v).baseChangePointsEquiv (S := L) K) := by
        funext x
        simp only [Function.comp_apply]
        rw [← baseChangePointsEquiv_mapPoints, MulEquiv.symm_apply_apply]
        rfl
      rw [this]
      exact ((H.G v).baseChangePointsEquiv (S := L) K).symm.bijective.comp
        ((hf v).comp ((G.G v).baseChangePointsEquiv (S := L) K).bijective)
    exact ⟨fun x y h => Additive.toMul.injective (hb0.1 (Additive.ofMul.injective h)),
      fun y => let ⟨x, hx⟩ := hb0.2 (Additive.toMul y)
        ⟨Additive.ofMul x, Additive.toMul.injective hx⟩⟩
  let e := (LinearEquiv.ofBijective _ hb).baseChange ℤ_[p] ℚ_[p] _ _
  have he : ∀ σ, (e : _ →ₗ[ℚ_[p]] _) ∘ₗ (G.baseChange L).tateRepOver σ =
      (H.baseChange L).tateRepOver σ ∘ₗ e := fun σ => by
    change (Hom.baseChange (S := L) f).tateLin.baseChange ℚ_[p] ∘ₗ
        ((G.baseChange L).galLin σ).baseChange ℚ_[p] =
      ((H.baseChange L).galLin σ).baseChange ℚ_[p] ∘ₗ
        (Hom.baseChange (S := L) f).tateLin.baseChange ℚ_[p]
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
    rfl
  rw [← G.finrank_DHT_tateRepOver_neg_one_of_iso_OL P φ ψ hφψ hψφ,
    ← H.finrank_DHT_tateRepOver_neg_one_of_iso_OL P' φ' ψ' hφψ' hψφ']
  exact finrank_DHT_eq_of_equiv e he (-1)

/-- **[Hong, Lemma 3.5.2] over `O_L`**: a homomorphism `f : G → H` of `p`-divisible groups over
`O_L` which is bijective on `ℚ̄_p`-points at every level (e.g. an isomorphism on generic fibres)
is an isomorphism: every `α_v = f_v : B_v → A_v` is bijective. -/
theorem Hom.bijective_of_mapPoints_bijective_OL {G H : PDivGroup (OL L) p} (f : Hom G H)
    (hf : ∀ v, Function.Bijective ((f.f v).mapPoints K)) (v : ℕ) :
    Function.Bijective (f.f v) := by
  have hpK : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  -- heights
  have hcard : ∀ w, p ^ (G.height * w) = p ^ (H.height * w) := fun w => by
    rw [← G.card_points_sepClosed K hpK w, ← H.card_points_sepClosed K hpK w]
    exact Nat.card_eq_of_bijective _ (hf w)
  have hh : G.height = H.height := by
    have := hcard 1
    rw [mul_one, mul_one] at this
    exact Nat.pow_right_injective hp.out.two_le this
  -- dimensions
  obtain ⟨d, P, φ, ψ, h1, h2⟩ := G.exists_connPart_iso_OL
  obtain ⟨d', P', φ', ψ', h1', h2'⟩ := H.exists_connPart_iso_OL
  have hd : d = d' := f.dim_eq_of_mapPoints_bijective_OL hf P φ ψ h1 h2 P' φ' ψ' h1' h2'
  subst hd
  -- discriminants
  have hdA := G.discIdeal_eq_of_iso_OL P φ ψ h1 h2 v
  have hdB := H.discIdeal_eq_of_iso_OL P' φ' ψ' h1' h2' v
  rw [hh] at hdA
  have hrank : finrank (OL L) (G.G v).A = finrank (OL L) (H.G v).A := by
    change (G.G v).order = (H.G v).order
    rw [G.order_eq, H.order_eq, hh]
  have hK := FFGroupScheme.bijective_baseChange_of_mapPoints K (f.f v) (G.isEtale_layer_qbar v)
    (H.isEtale_layer_qbar v) (hf v)
  have h0 : discIdeal (OL L) (H.G v).A ≠ ⊥ := by
    rw [hdB, Ne, Ideal.span_singleton_eq_bot]
    exact pow_ne_zero _ (pow_ne_zero _ (OL.natCast_ne_zero (pow_ne_zero _ hp.out.ne_zero)))
  exact bijective_of_discIdeal_eq K hrank OL.algebraMap_qbar_injective
    (f.f v : (H.G v).A →ₐ[OL L] (G.G v).A) hK (hdA.trans hdB.symm) h0

/-- **[Hong, Lemma 3.5.2] over `O_L`, generic-fibre form**: if `f_L : G_L → H_L` has an inverse
homomorphism of `p`-divisible groups over `L`, then `f` is an isomorphism. -/
theorem Hom.bijective_of_baseChange_inverse_OL {G H : PDivGroup (OL L) p} (f : Hom G H)
    (g : Hom (H.baseChange L) (G.baseChange L))
    (h1 : (Hom.baseChange (S := L) f).comp g = Hom.id _)
    (h2 : g.comp (Hom.baseChange (S := L) f) = Hom.id _) (v : ℕ) :
    Function.Bijective (f.f v) := by
  refine f.bijective_of_mapPoints_bijective_OL (fun w => ?_) v
  let EG := (G.G w).baseChangePointsEquiv (S := L) K
  let EH := (H.G w).baseChangePointsEquiv (S := L) K
  have hf : ⇑((f.f w).mapPoints K) =
      EH ∘ ((Hom.baseChange (S := L) f).f w).mapPoints K ∘ EG.symm := by
    funext x
    change _ = (f.f w).mapPoints K (EG (EG.symm x))
    rw [MulEquiv.apply_symm_apply]
  have hl : Function.LeftInverse ((g.f w).mapPoints K)
      (((Hom.baseChange (S := L) f).f w).mapPoints K) := fun x => by
    have := congrArg (fun φ : Hom _ _ => (φ.f w).mapPoints K x) h2
    exact this
  have hr : Function.RightInverse ((g.f w).mapPoints K)
      (((Hom.baseChange (S := L) f).f w).mapPoints K) := fun x => by
    have := congrArg (fun φ : Hom _ _ => (φ.f w).mapPoints K x) h1
    exact this
  rw [hf]
  have hb : Function.Bijective (((Hom.baseChange (S := L) f).f w).mapPoints K) :=
    ⟨hl.injective, hr.surjective⟩
  exact EH.bijective.comp (hb.comp EG.symm.bijective)

end PDivGroup

end PadicHodge
