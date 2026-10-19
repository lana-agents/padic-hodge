/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.Fontaine.PropNine
import PadicHodge.FormalGroup.TpMul
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# (FoInt) (b), first part: `ℤ_p`-linearity of Fontaine's map and injectivity of `ρ ⊗ ℂ_p`

* `PadicHodge.map_zp_smul_of_norm_le`: a bounded additive map `M → ℂ_p` on a `ℤ_p`-module is
  `ℤ_p`-linear; `PadicHodge.map_zp_smul_of_sep`: an additive map into a `p`-adically separated
  `ℤ_p`-module is `ℤ_p`-linear.
* `PDivFGL.tpLinEquiv`: `T_p F ≃ₗ[ℤ_p] T_p(F[p^∞]_L)(ℚ̄_p)`; hence `T_p F` is free of rank `h`.
* `PDivFGL.rhoZp`: `ρ(ω_l) : T_p F →ₗ[ℤ_p] ℂ_p`.
* `PDivFGL.rhoLin_eq_zero`, `PDivFGL.rhoLin_injective`, `PDivFGL.linearIndependent_rhoZp`:
  `ρ ⊗ ℂ_p : ℂ_p^d → Hom_{ℤ_p}(T_p F, ℂ_p)` is injective ([Fo, §5.7 (i)] from Prop. 9,
  Ax–Sen–Tate and Galois descent).
-/

noncomputable section

open Module

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime]

section General

/-- **Galois descent of linear relations** (Artin's minimal-support argument): if every relation
`∑ c_i f_i = 0` stays a relation after applying any `s ∈ S` to the coefficients, and there is no
nonzero relation with `S`-fixed coefficients, then the `f_i` are linearly independent. -/
theorem eq_zero_of_relation_descent {ι X K : Type*} [Fintype ι] [Field K] (f : ι → X → K)
    (S : Set (K ≃+* K))
    (hS : ∀ s ∈ S, ∀ c : ι → K, (∀ x, ∑ i, c i * f i x = 0) → ∀ x, ∑ i, s (c i) * f i x = 0)
    (hF : ∀ c : ι → K, (∀ i, ∀ s ∈ S, s (c i) = c i) → (∀ x, ∑ i, c i * f i x = 0) → c = 0)
    (c : ι → K) (hc : ∀ x, ∑ i, c i * f i x = 0) : c = 0 := by
  classical
  by_contra hne
  let P : ℕ → Prop := fun n => ∃ c : ι → K, c ≠ 0 ∧ (∀ x, ∑ i, c i * f i x = 0) ∧
    (Finset.univ.filter fun i => c i ≠ 0).card = n
  have hP : ∃ n, P n := ⟨_, c, hne, hc, rfl⟩
  obtain ⟨c, hc0, hcr, hcard⟩ := Nat.find_spec hP
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hc0
  -- normalise `c i₀ = 1`
  set c' : ι → K := fun i => (c i₀)⁻¹ * c i with hc'
  have hc'r : ∀ x, ∑ i, c' i * f i x = 0 := fun x => by
    simp only [hc', mul_assoc, ← Finset.mul_sum, hcr x, mul_zero]
  have hc'i : c' i₀ = 1 := by simp [hc', inv_mul_cancel₀ hi₀]
  have hsupp : ∀ i, c' i ≠ 0 ↔ c i ≠ 0 := fun i => by
    simp [hc', inv_ne_zero hi₀]
  have hc'card : (Finset.univ.filter fun i => c' i ≠ 0).card = Nat.find hP := by
    rw [← hcard]; congr 1; ext i; simp only [Finset.mem_filter, hsupp]
  apply hc0
  have hfix : ∀ i, ∀ s ∈ S, s (c' i) = c' i := by
    intro i s hs
    by_contra hdiff
    set e : ι → K := fun i => s (c' i) - c' i with he
    have her : ∀ x, ∑ i, e i * f i x = 0 := fun x => by
      simp only [he, sub_mul, Finset.sum_sub_distrib, hS s hs c' hc'r x, hc'r x, sub_self]
    have he0 : e ≠ 0 := fun h => hdiff (sub_eq_zero.mp (congrFun h i))
    have hsub : (Finset.univ.filter fun i => e i ≠ 0) ⊂
        (Finset.univ.filter fun i => c' i ≠ 0) := by
      refine Finset.ssubset_iff_of_subset (fun j hj => ?_) |>.mpr ⟨i₀, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        intro h0
        apply hj
        simp [he, h0]
      · simp [hc'i]
      · simp [he, hc'i]
    have hlt := Finset.card_lt_card hsub
    rw [hc'card] at hlt
    exact Nat.find_min hP hlt ⟨e, he0, her, rfl⟩
  have := hF c' hfix hc'r
  exact absurd (congrFun this i₀) (by rw [hc'i]; exact one_ne_zero)

theorem norm_p_cp_lt_one : ‖(p : ℂ_[p])‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap', Padic.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)

theorem norm_p_cp_pos : 0 < ‖(p : ℂ_[p])‖ :=
  norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.out.ne_zero)

theorem norm_zp_smul_cp_le (c : ℤ_[p]) (z : ℂ_[p]) : ‖c • z‖ ≤ ‖z‖ := by
  rw [← algebraMap_smul ℚ_[p] c z, Algebra.smul_def, norm_mul, norm_algebraMap']
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  rw [PadicInt.algebraMap_apply]
  exact PadicInt.norm_le_one c

theorem exists_nat_add_pow_mul (c : ℤ_[p]) (n : ℕ) :
    ∃ (a : ℕ) (u : ℤ_[p]), c = a + (p : ℤ_[p]) ^ n * u := by
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp (PadicInt.appr_spec n c)
  exact ⟨PadicInt.appr c n, u, by rw [mul_comm, hu]; ring⟩

theorem zp_smul_decomp {M : Type*} [AddCommGroup M] [Module ℤ_[p] M] (a n : ℕ) (u : ℤ_[p])
    (x : M) : ((a : ℤ_[p]) + (p : ℤ_[p]) ^ n * u) • x = a • x + (p ^ n : ℕ) • (u • x) := by
  rw [add_smul, mul_smul, Nat.cast_smul_eq_nsmul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]

/-- A **bounded additive map** `M → ℂ_p` on a `ℤ_p`-module is `ℤ_p`-linear. -/
theorem map_zp_smul_of_norm_le {M : Type*} [AddCommGroup M] [Module ℤ_[p] M] (f : M →+ ℂ_[p])
    {R : ℝ} (hf : ∀ x, ‖f x‖ ≤ R) (c : ℤ_[p]) (x : M) : f (c • x) = c • f x := by
  set C := max R ‖f x‖
  have key : ∀ n : ℕ, ‖f (c • x) - c • f x‖ ≤ ‖(p : ℂ_[p])‖ ^ n * C := by
    intro n
    obtain ⟨a, u, rfl⟩ := exists_nat_add_pow_mul c n
    rw [zp_smul_decomp, zp_smul_decomp, map_add, map_nsmul, map_nsmul, add_sub_add_left_eq_sub,
      ← smul_sub, nsmul_eq_mul, norm_mul, Nat.cast_pow, norm_pow]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hu : ‖f (u • x) - u • f x‖ ≤ max ‖f (u • x)‖ ‖u • f x‖ := by
      simpa [sub_eq_add_neg, norm_neg] using
        IsUltrametricDist.norm_add_le_max (f (u • x)) (-(u • f x))
    exact hu.trans (max_le_max (hf _) (norm_zp_smul_cp_le _ _))
  by_contra hne
  have hpos : 0 < ‖f (c • x) - c • f x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have h0 := key 0
  rw [pow_zero, one_mul] at h0
  have hC : 0 < C := lt_of_lt_of_le hpos h0
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hpos hC) (norm_p_cp_lt_one (p := p))
  rw [lt_div_iff₀ hC] at hn
  linarith [key n]

/-- An additive map into a `p`-adically separated `ℤ_p`-module is `ℤ_p`-linear. -/
theorem map_zp_smul_of_sep {M N : Type*} [AddCommGroup M] [Module ℤ_[p] M] [AddCommGroup N]
    [Module ℤ_[p] N] (f : M →+ N)
    (hN : ∀ y : N, (∀ n : ℕ, ∃ z, y = (p ^ n : ℕ) • z) → y = 0) (c : ℤ_[p]) (x : M) :
    f (c • x) = c • f x := by
  refine sub_eq_zero.mp (hN _ fun n => ?_)
  obtain ⟨a, u, rfl⟩ := exists_nat_add_pow_mul c n
  refine ⟨f (u • x) - u • f x, ?_⟩
  rw [zp_smul_decomp, zp_smul_decomp, map_add, map_nsmul, map_nsmul, smul_sub]
  abel

/-- A free `ℤ_p`-module is `p`-adically separated. -/
theorem eq_zero_of_forall_dvd {N : Type*} [AddCommGroup N] [Module ℤ_[p] N] [Module.Free ℤ_[p] N]
    (y : N) (hy : ∀ n : ℕ, ∃ z, y = (p ^ n : ℕ) • z) : y = 0 := by
  let b := Module.Free.chooseBasis ℤ_[p] N
  refine b.repr.injective (Finsupp.ext fun i => ?_)
  rw [map_zero, Finsupp.zero_apply]
  have hp1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
  have key : ∀ n : ℕ, ‖b.repr y i‖ ≤ (p : ℝ)⁻¹ ^ n := by
    intro n
    obtain ⟨z, hz⟩ := hy n
    rw [hz, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul, norm_mul, Nat.cast_pow, norm_pow,
      PadicInt.norm_p]
    exact mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one _)
  by_contra hne
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.mpr hne) hp1
  linarith [key n]

end General

variable {L : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem galCp_galCp_inv (τ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (z : ℂ_[p]) :
    galCp L τ (galCp L τ⁻¹ z) = z := by
  change (galCp L τ * galCp L τ⁻¹) z = z
  rw [← map_mul, mul_inv_cancel, map_one]
  rfl

namespace PDivFGL

variable [FiniteDimensional ℚ_[p] L] {d : ℕ} (P : PDivFGL (OL L) d p)

/-- **`T_p F ≅ T_p(F[p^∞]_L)(ℚ̄_p)` as `ℤ_p`-modules** (`tpToQbarEquiv` is automatically
`ℤ_p`-linear). -/
def tpLinEquiv :
    Kummer.Tp (P.F.Pt p) p ≃ₗ[ℤ_[p]] Additive (P.genericFibreOL.TateModule (PadicAlgCl p)) :=
  { P.tpToQbarEquiv with
    map_smul' := fun c x =>
      map_zp_smul_of_sep P.tpToQbarEquiv.toAddMonoidHom (fun y hy => eq_zero_of_forall_dvd y hy)
        c x }

theorem tpLinEquiv_apply (x : Kummer.Tp (P.F.Pt p) p) : P.tpLinEquiv x = P.tpToQbarEquiv x :=
  rfl

theorem tpLinEquiv_tpRep (σ : L.fixingSubgroup) (x : Kummer.Tp (P.F.Pt p) p) :
    P.tpLinEquiv (Kummer.tpRep P.galRepOL p σ x) =
      P.genericFibreOL.galLin (IntermediateField.fixingSubgroupEquiv L σ) (P.tpLinEquiv x) :=
  Additive.toMul.injective (P.tpToQbarEquiv_tpRep σ x)

instance : Module.Free ℤ_[p] (Kummer.Tp (P.F.Pt p) p) := Module.Free.of_equiv P.tpLinEquiv.symm

instance : Module.Finite ℤ_[p] (Kummer.Tp (P.F.Pt p) p) := Module.Finite.equiv P.tpLinEquiv.symm

/-- `T_p F` is free of rank `h` over `ℤ_p`. -/
theorem finrank_tp : finrank ℤ_[p] (Kummer.Tp (P.F.Pt p) p) = P.height := by
  rw [P.tpLinEquiv.finrank_eq, PDivGroup.finrank_tate]
  rfl

variable {ε : ℕ → PadicAlgCl p} (hε : ∀ n, IsPrimitiveRoot (ε (n + 1)) (p ^ (n + 1)))
  (hεp : ∀ n, ε (n + 2) ^ p = ε (n + 1))

/-- `ρ(ω_l)` as an additive map. -/
def rhoHom (l : Fin d) : Kummer.Tp (P.F.Pt p) p →+ ℂ_[p] :=
  AddMonoidHom.mk' (P.rho hε l) (P.rho_add hεp l)

include hεp in
/-- **`ℤ_p`-linearity of `ρ(ω_l)`** (from additivity and the bound of [Fo, Thm 1′]). -/
theorem rho_smul (l : Fin d) (c : ℤ_[p]) (x : Kummer.Tp (P.F.Pt p) p) :
    P.rho hε l (c • x) = c • P.rho hε l x :=
  map_zp_smul_of_norm_le (P.rhoHom hε hεp l) (P.norm_rho_le hεp l) c x

include hεp in
theorem rho_pow_smul (l : Fin d) (n : ℕ) (x : Kummer.Tp (P.F.Pt p) p) :
    P.rho hε l ((p : ℤ_[p]) ^ n • x) = (p : ℂ_[p]) ^ n * P.rho hε l x := by
  rw [P.rho_smul hε hεp, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, nsmul_eq_mul, Nat.cast_pow]

/-- **Fontaine's map `ρ(ω_l) : T_p F →ₗ[ℤ_p] ℂ_p`.** -/
def rhoZp (l : Fin d) : Kummer.Tp (P.F.Pt p) p →ₗ[ℤ_[p]] ℂ_[p] where
  toFun := P.rho hε l
  map_add' := P.rho_add hεp l
  map_smul' := P.rho_smul hε hεp l

@[simp] theorem rhoZp_apply (l : Fin d) (x : Kummer.Tp (P.F.Pt p) p) :
    P.rhoZp hε hεp l x = P.rho hε l x := rfl

variable {hε}

omit [FiniteDimensional ℚ_[p] L] in
theorem chi_cp_ne_zero (σ : L.fixingSubgroup) :
    algebraMap ℚ_[p] ℂ_[p] ((chi ((IntermediateField.fixingSubgroupEquiv L σ).restrictScalars
      ℚ_[p]) : ℤ_[p]ˣ) : ℤ_[p]) ≠ 0 := by
  rw [ne_eq, map_eq_zero_iff _ (algebraMap ℚ_[p] ℂ_[p]).injective, PadicInt.coe_eq_zero]
  exact Units.ne_zero _

include hεp in
/-- **Injectivity of `ρ ⊗ ℂ_p`** ([Fo, §5.7 (i)]): if `∑_l c_l ρ(ω_l) = 0` on `T_p F` with
`c ∈ ℂ_p^d`, then `c = 0`. From [Fo, Prop. 9] (`exists_rho_ne_zero_of_ne_zero`) for
`c ∈ O_L^d`, by scaling, Ax–Sen–Tate (`galCp_eq_self_iff_mem`) and Galois descent. -/
theorem rhoLin_eq_zero (c : Fin d → ℂ_[p]) (hc : ∀ x, P.rhoLin (hε := hε) c x = 0) : c = 0 := by
  refine eq_zero_of_relation_descent (fun l x => P.rho hε l x) (Set.range (galCp L)) ?_ ?_ c hc
  · rintro _ ⟨τ, rfl⟩ c hc x
    set σ : L.fixingSubgroup := (IntermediateField.fixingSubgroupEquiv L).symm τ⁻¹
    have h := hc (Kummer.tpRep P.galRepOL p σ x)
    simp only [P.rho_tpRep hεp] at h
    have hστ : IntermediateField.fixingSubgroupEquiv L σ = τ⁻¹ := MulEquiv.apply_symm_apply _ _
    simp only [hστ, mul_left_comm (c _), ← Finset.mul_sum] at h
    have h' := (mul_eq_zero.mp h).resolve_left (by rw [← hστ]; exact chi_cp_ne_zero σ)
    have h'' := congrArg (galCp L τ) h'
    simp only [map_sum, map_mul, galCp_galCp_inv, map_zero] at h''
    exact h''
  · intro c hfix hc
    have hmem : ∀ l, c l ∈ cpSubmodule L := fun l =>
      (galCp_eq_self_iff_mem (c l)).mp fun σ => hfix l _ ⟨σ, rfl⟩
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ l, ‖(p : ℂ_[p]) ^ N * c l‖ ≤ 1 := by
      set M := ∑ l, ‖c l‖ + 1
      have hM : 0 < M := by positivity
      obtain ⟨N, hNM⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hM) (norm_p_cp_lt_one (p := p))
      refine ⟨N, fun l => ?_⟩
      have hl : ‖c l‖ ≤ M := by
        have := Finset.single_le_sum (f := fun l => ‖c l‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_univ l)
        linarith
      rw [norm_mul, norm_pow]
      calc ‖(p : ℂ_[p])‖ ^ N * ‖c l‖ ≤ M⁻¹ * M :=
            mul_le_mul hNM.le hl (norm_nonneg _) (inv_pos.mpr hM).le
        _ = 1 := inv_mul_cancel₀ hM.ne'
    have hmem' : ∀ l, (p : ℂ_[p]) ^ N * c l ∈ cpSubmodule L := by
      intro l
      have := (cpSubmodule L).smul_mem ((p : ℚ_[p]) ^ N) (hmem l)
      rwa [Algebra.smul_def, map_pow, map_natCast] at this
    let c' : Fin d → OL L := fun l => OL.mk ⟨(p : ℂ_[p]) ^ N * c l, hN l⟩ (hmem' l)
    have hc' : ∀ l, (((algebraMap (OL L) (OKbar p) (c' l) : OKbar p) : PadicAlgCl p) : ℂ_[p]) =
        (p : ℂ_[p]) ^ N * c l := by
      intro l
      rw [← OL.coe_incOK (p := p) (L := L), AlgHom.commutes]
      rfl
    have hpN : (p : ℂ_[p]) ^ N ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.out.ne_zero)
    by_contra hne
    have hne' : c' ≠ 0 := by
      intro h0
      apply hne
      funext l
      have := hc' l
      rw [h0, Pi.zero_apply, map_zero] at this
      exact ((mul_eq_zero.mp (by rw [← this]; rfl)).resolve_left hpN)
    obtain ⟨x, hx⟩ := P.exists_rho_ne_zero_of_ne_zero hεp c' hne'
    apply hx
    simp only [hc', mul_assoc, ← Finset.mul_sum]
    rw [show ∑ l, c l * P.rho hε l x = 0 from hc x, mul_zero]

include hεp in
theorem rhoLin_injective :
    Function.Injective (fun c : Fin d → ℂ_[p] => P.rhoLin (hε := hε) c) := by
  intro c c' h
  refine sub_eq_zero.mp (P.rhoLin_eq_zero (hε := hε) hεp _ fun x => ?_)
  have hx := congrFun h x
  simp only [rhoLin] at hx ⊢
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, hx, sub_self]

variable (hε)

/-- The `ρ(ω_l)` are `ℂ_p`-linearly independent in `Hom_{ℤ_p}(T_p F, ℂ_p)`. -/
theorem linearIndependent_rhoZp : LinearIndependent ℂ_[p] (P.rhoZp hε hεp) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h := P.rhoLin_eq_zero hεp g fun x => by
    have := LinearMap.congr_fun hg x
    simpa [rhoLin, smul_eq_mul] using this
  exact fun i => congrFun h i

end PDivFGL

end PadicHodge
