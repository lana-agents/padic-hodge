/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.Fontaine.ThmOne
import PadicHodge.Cyclotomic.Character

/-!
# The Galois action on `Ω_{O_K̄/O_L}` and the equivariance of `ξ` ([Fo, Thm 1′])

* `KaehlerDifferential.galΩ σ : Ω_{B/R} →ₛₗ[σ] Ω_{B/R}` for an `R`-algebra automorphism `σ` of
  `B` (from the presentation `(B →₀ B) / kerTotal`), with `galΩ σ (y · dz) = σ(y) · d(σ z)`;
* `OL.galOK σ : O_K̄ ≃ₐ[O_L] O_K̄` for `σ ∈ G_L = Aut(ℚ̄_p/L)` (`σ` is an isometry);
* **`OL.galΩ_xi`** ([Fo, Thm 1′], `G`-equivariance): `σ(ξ(a)) = ξ(χ(σ) σ(a))`, `χ` the
  cyclotomic character — i.e. `ξ : K̄(1) → Ω` is `G_L`-equivariant.
-/

noncomputable section

open IsLocalRing Polynomial Module KaehlerDifferential IntermediateField

namespace PadicHodge

namespace KaehlerUnion

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] (σ : B ≃ₐ[R] B)

/-- `∑ b_i [x_i] ↦ ∑ σ(b_i) [σ x_i]` on `B →₀ B` (semilinear over `σ`). -/
def twistFin : (B →₀ B) →ₛₗ[(σ : B →+* B)] (B →₀ B) where
  toFun g := (g.mapDomain σ).mapRange σ (map_zero σ)
  map_add' g h := by
    rw [Finsupp.mapDomain_add, Finsupp.mapRange_add (map_add σ)]
  map_smul' c g := by
    ext i
    simp only [Finsupp.mapDomain_smul, Finsupp.mapRange_apply, Finsupp.smul_apply, smul_eq_mul,
      map_mul, RingHom.coe_coe]

theorem twistFin_single (x c : B) :
    twistFin σ (Finsupp.single x c) = Finsupp.single (σ x) (σ c) := by
  simp [twistFin]

theorem twistFin_mem {g : B →₀ B} (hg : g ∈ KaehlerDifferential.kerTotal R B) :
    twistFin σ g ∈ KaehlerDifferential.kerTotal R B := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
    apply Submodule.subset_span
    rcases hg with (⟨⟨x1, x2⟩, rfl⟩ | ⟨⟨x1, x2⟩, rfl⟩) | ⟨r, rfl⟩
    · refine Or.inl (Or.inl ⟨(σ x1, σ x2), ?_⟩)
      simp only [map_sub, map_add, twistFin_single, map_one]
    · refine Or.inl (Or.inr ⟨(σ x1, σ x2), ?_⟩)
      simp only [map_sub, map_add, twistFin_single, map_one, map_mul]
    · refine Or.inr ⟨r, ?_⟩
      simp only [twistFin_single, map_one, AlgEquiv.commutes]
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hx

/-- **The action of `σ ∈ Aut_R(B)` on `Ω_{B/R}`** (`σ`-semilinear). -/
def galΩ : Ω[B⁄R] →ₛₗ[(σ : B →+* B)] Ω[B⁄R] :=
  (KaehlerDifferential.quotKerTotalEquiv R B).toLinearMap ∘ₛₗ
    ((KaehlerDifferential.kerTotal R B).mapQ (KaehlerDifferential.kerTotal R B) (twistFin σ)
      fun _ hg => twistFin_mem σ hg) ∘ₛₗ
    (KaehlerDifferential.quotKerTotalEquiv R B).symm.toLinearMap

theorem quotKerTotalEquiv_symm_D (z : B) :
    (KaehlerDifferential.quotKerTotalEquiv R B).symm (KaehlerDifferential.D R B z) =
      (KaehlerDifferential.kerTotal R B).mkQ (Finsupp.single z 1) :=
  Derivation.congr_fun (KaehlerDifferential.quotKerTotalEquiv_symm_comp_D R B) z

theorem galΩ_D (z : B) :
    galΩ σ (KaehlerDifferential.D R B z) = KaehlerDifferential.D R B (σ z) := by
  have h := quotKerTotalEquiv_symm_D (R := R) (σ z)
  rw [LinearEquiv.symm_apply_eq] at h
  simp only [galΩ, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    quotKerTotalEquiv_symm_D]
  rw [Submodule.mkQ_apply, Submodule.mapQ_apply, twistFin_single, map_one,
    ← Submodule.mkQ_apply]
  exact h.symm

theorem galΩ_smul (c : B) (ω : Ω[B⁄R]) : galΩ σ (c • ω) = σ c • galΩ σ ω :=
  LinearMap.map_smulₛₗ _ _ _

end KaehlerUnion

variable {p : ℕ} [hp : Fact p.Prime]

namespace OL

variable {L : IntermediateField ℚ_[p] (PadicAlgCl p)}

/-- `σ ∈ G_L` as an `O_L`-algebra automorphism of `O_K̄`. -/
def galOK (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) : OKbar p ≃ₐ[OL L] OKbar p where
  toFun y := ⟨σ y, by change ‖σ y‖ ≤ 1; rw [norm_gal_apply]; exact y.2⟩
  invFun y := ⟨σ.symm y, by change ‖σ.symm y‖ ≤ 1; rw [norm_gal_apply]; exact y.2⟩
  left_inv y := Subtype.ext (σ.symm_apply_apply _)
  right_inv y := Subtype.ext (σ.apply_symm_apply _)
  map_mul' x y := Subtype.ext (map_mul σ _ _)
  map_add' x y := Subtype.ext (map_add σ _ _)
  commutes' x := Subtype.ext (by
    change σ (algebraMap (OL L) (PadicAlgCl p) x) = algebraMap (OL L) (PadicAlgCl p) x
    rw [algebraMap_qbar_eq]
    exact σ.commutes (toL x))

theorem coe_galOK (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (y : OKbar p) :
    ((galOK σ y : OKbar p) : PadicAlgCl p) = σ y := rfl

/-! ### Equivariance of `ξ` -/

variable {ε : ℕ → PadicAlgCl p} (hε : ∀ n, IsPrimitiveRoot (ε (n + 1)) (p ^ (n + 1)))
  (hεp : ∀ n, ε (n + 2) ^ p = ε (n + 1))

/-- `p^{n+1} · dlog ε_{n+1} = 0`. -/
theorem pow_smul_dlogε (n : ℕ) : ((p : OKbar p) ^ (n + 1)) • dlogε L hε n = 0 := by
  have h1 : epsK hε n ^ (p ^ (n + 1)) = 1 := Subtype.ext (by
    rw [SubmonoidClass.coe_pow, coe_epsK, OneMemClass.coe_one]
    exact (hε n).pow_eq_one)
  have h2 := congrArg (D (OL L) (OKbar p)) h1
  rw [Derivation.leibniz_pow, Derivation.map_one_eq_zero, ← Nat.cast_smul_eq_nsmul (OKbar p),
    smul_smul] at h2
  have h3 := congrArg (fun ω => (epsInvK hε n) ^ (p ^ (n + 1)) • ω) h2
  simp only [smul_zero, smul_smul, Nat.cast_pow] at h3
  rw [dlogε, smul_smul, ← h3]
  congr 1
  apply Subtype.ext
  simp only [Subring.coe_mul, SubmonoidClass.coe_pow, Subring.coe_natCast, epsInvK, coe_epsK]
  have h0 := eps_ne_zero hε n
  have hpow : ε (n + 1) ^ (p ^ (n + 1)) = ε (n + 1) ^ (p ^ (n + 1) - 1) * ε (n + 1) := by
    rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ hp.out.pos)]
  rw [inv_pow, hpow]
  field_simp

/-- `σ(dlog ε_{n+1}) = c · dlog ε_{n+1}` if `σ ε_{n+1} = ε_{n+1}^c`. -/
theorem galΩ_dlogε (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (n c : ℕ)
    (hc : σ (ε (n + 1)) = ε (n + 1) ^ c) :
    KaehlerUnion.galΩ (galOK σ) (dlogε L hε n) = (c : OKbar p) • dlogε L hε n := by
  have he : galOK σ (epsK hε n) = epsK hε n ^ c := Subtype.ext (by
    rw [coe_galOK, SubmonoidClass.coe_pow]; exact hc)
  rw [dlogε, KaehlerUnion.galΩ_smul, KaehlerUnion.galΩ_D, he, Derivation.leibniz_pow,
    ← Nat.cast_smul_eq_nsmul (OKbar p), smul_smul, smul_smul, smul_smul]
  congr 1
  apply Subtype.ext
  simp only [Subring.coe_mul, SubmonoidClass.coe_pow, Subring.coe_natCast, epsInvK, coe_epsK,
    coe_galOK, map_inv₀, hc]
  have h0 := eps_ne_zero hε n
  rcases c with _ | c
  · simp
  · rw [Nat.add_sub_cancel, pow_succ]
    field_simp

include hεp in
/-- **[Fo, Thm 1′], `G_L`-equivariance of `ξ`**: `σ(ξ(a)) = ξ(χ(σ) · σ(a))`. -/
theorem galΩ_xi (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (a : PadicAlgCl p) :
    KaehlerUnion.galΩ (galOK σ) (xi L hε a) =
      xi L hε (algebraMap ℚ_[p] (PadicAlgCl p)
        ((chi (σ.restrictScalars ℚ_[p]) : ℤ_[p]ˣ) : ℤ_[p]) * σ a) := by
  set χ : ℤ_[p] := ((chi (σ.restrictScalars ℚ_[p]) : ℤ_[p]ˣ) : ℤ_[p])
  obtain ⟨n, h⟩ := exists_norm_pow_mul_le a
  set c := (χ.toZModPow (n + 1)).val
  have hc : σ (ε (n + 1)) = ε (n + 1) ^ c := chi_spec (σ.restrictScalars ℚ_[p]) (hε n).pow_eq_one
  have hχ1 : ‖algebraMap ℚ_[p] (PadicAlgCl p) χ‖ ≤ 1 := by
    rw [norm_algebraMap']; exact χ.2
  have hσa : ‖(p : PadicAlgCl p) ^ (n + 1) * σ a‖ ≤ 1 := by
    have : σ ((p : PadicAlgCl p) ^ (n + 1) * a) = (p : PadicAlgCl p) ^ (n + 1) * σ a := by
      rw [map_mul, map_pow, map_natCast]
    rw [← this, norm_gal_apply]; exact h
  have h' : ‖(p : PadicAlgCl p) ^ (n + 1) * (algebraMap ℚ_[p] (PadicAlgCl p) χ * σ a)‖ ≤ 1 := by
    rw [mul_left_comm, norm_mul]; exact mul_le_one₀ hχ1 (norm_nonneg _) hσa
  rw [xi_eq hε hεp a h, xi_eq hε hεp _ h', KaehlerUnion.galΩ_smul, galΩ_dlogε hε σ n c hc,
    smul_smul]
  -- `χ - c ∈ p^{n+1} ℤ_p`
  have hker : χ - (c : ℤ_[p]) ∈ RingHom.ker (PadicInt.toZModPow (p := p) (n + 1)) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hker
  obtain ⟨t, ht⟩ := hker
  have hχ : algebraMap ℚ_[p] (PadicAlgCl p) χ =
      (c : PadicAlgCl p) + (p : PadicAlgCl p) ^ (n + 1) * algebraMap ℚ_[p] (PadicAlgCl p) t := by
    have := congrArg (fun z : ℤ_[p] => algebraMap ℚ_[p] (PadicAlgCl p) z) ht
    simp only [PadicInt.coe_sub, PadicInt.coe_natCast, PadicInt.coe_mul, PadicInt.coe_pow,
      map_sub, map_natCast, map_mul, map_pow] at this
    linear_combination this
  have ht1 : ‖(p : PadicAlgCl p) ^ (n + 1) * σ a * algebraMap ℚ_[p] (PadicAlgCl p) t‖ ≤ 1 := by
    rw [norm_mul]
    exact mul_le_one₀ hσa (norm_nonneg _) (by rw [norm_algebraMap']; exact t.2)
  have hsplit : pa (algebraMap ℚ_[p] (PadicAlgCl p) χ * σ a) (n + 1) h' =
      galOK σ (pa a (n + 1) h) * (c : OKbar p) +
        (⟨_, ht1⟩ : OKbar p) * (p : OKbar p) ^ (n + 1) := by
    apply Subtype.ext
    simp only [pa, Subring.coe_add, Subring.coe_mul, coe_galOK, Subring.coe_natCast,
      SubmonoidClass.coe_pow, map_mul, map_pow, map_natCast, hχ]
    ring
  rw [hsplit, add_smul, mul_smul (⟨_, ht1⟩ : OKbar p), pow_smul_dlogε hε n, smul_zero, add_zero]

end OL

end PadicHodge
