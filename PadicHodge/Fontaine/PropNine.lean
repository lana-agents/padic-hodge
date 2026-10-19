/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.Fontaine.Pullback
import PadicHodge.Fontaine.LemmeFour
import PadicHodge.FormalGroup.Kummer
import PadicHodge.FormalGroup.Invariants
import PadicHodge.TateSen.Invariants

/-!
# A nonzero pairing at an algebraic point gives a nonzero value of `ρ`

[Fo] J.-M. Fontaine, *Formes différentielles et modules de Tate des variétés abéliennes sur les
corps locaux*, Invent. Math. 65 (1982), §3.5 Lemme 2, §5.6 Prop. 9 (the reduction step).

Let `F` be a `p`-divisible formal group law over `O_L` (`L/ℚ_p` finite), `Ω = Ω_{O_K̄/O_L}`,
`ω_c = ∑_l c_l ω_l` (`c ∈ O_L^d`) and `x₀ ∈ F(m_{O_K̄})` with `x₀^* ω_c ≠ 0`. Then
`ρ(ω_c)(x) = ∑_l c_l ρ(ω_l)(x) ≠ 0` for some `x ∈ T_p F` (**`PDivFGL.exists_rho_ne_zero`**).

Proof. Choose a finite `E ⊇ L` containing the coordinates of `x₀`, so `x₀` is `G_E`-invariant,
and a compatible system of `p`-power roots `s_k` of `x₀` with open stabilisers
(`Kummer.exists_isDivSeq`); these are algebraic points (`FGL.isAlg_of_isOpen_stab`: an open
subgroup of `G_{ℚ_p}` contains some `G_{E'}`, `E'` finite, and Ax–Sen–Tate). Then
`f = (s_k^* ω_c)_k ∈ V_p(Ω)` has `f_0 ≠ 0`, so `τ f ≠ 0` (`OL.tau_eq_zero_iff`). For `σ ∈ G_E`,
`σ s_k = s_k + t_k` with `t = (σ s_k - s_k)_k ∈ T_p F` (the Kummer cocycle), hence
`σ f = f + ρ_c(t)` in `V_p(Ω)` and `χ(σ) σ(τ f) = τ f + ρ(ω_c)(t)`. If `ρ(ω_c)` vanished on `T_p F`,
`τ f` would lie in `ℂ_p(-1)^{G_E} = 0` (Tate, `eq_zero_of_galCp_eq_chi_smul`).

* `OL.tau_sum`: `τ` commutes with finite sums;
* `FGL.isAlg_of_fixed`, **`FGL.isAlg_of_isOpen_stab`**: points with open stabiliser are algebraic;
* **`PDivFGL.exists_rho_ne_zero`**.
-/

noncomputable section

open KaehlerDifferential IntermediateField

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime]

namespace OL

variable {L : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] L]
  {ε : ℕ → PadicAlgCl p} {hε : ∀ n, IsPrimitiveRoot (ε (n + 1)) (p ^ (n + 1))}
  (hεp : ∀ n, ε (n + 2) ^ p = ε (n + 1))

include hεp in
/-- `τ` commutes with finite sums. -/
theorem tau_sum {ι : Type*} (s : Finset ι) {z : ι → ℕ → Ω[OKbar p⁄OL L]}
    (hz : ∀ i k, (p : OKbar p) • z i (k + 1) = z i k) :
    tau L hε (∑ i ∈ s, z i) = ∑ i ∈ s, tau L hε (z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact tau_zero hεp
  | insert a s ha ih =>
    have hs : ∀ k, (p : OKbar p) • (∑ i ∈ s, z i) (k + 1) = (∑ i ∈ s, z i) k := fun k => by
      simp only [Finset.sum_apply, Finset.smul_sum, hz]
    rw [Finset.sum_insert ha, Finset.sum_insert ha, tau_add hεp (hz a) hs, ih]

end OL

namespace FGL

open OL

variable {L : IntermediateField ℚ_[p] (PadicAlgCl p)} {d : ℕ} (F : FGL (OL L) d)

/-- A point fixed by `G_{E'}` for a finite `E'/ℚ_p` is algebraic (Ax–Sen–Tate). -/
theorem isAlg_of_fixed (E' : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E']
    {x : F.Pt p} (hx : ∀ σ ∈ E'.fixingSubgroup, galPt σ x = x) : F.IsAlg x := by
  have h := (F.galPt_fixed_iff E' x).mp fun σ => hx _ ((fixingSubgroupEquiv E').symm σ).2
  choose a haE ha using fun j => mem_cpSubmodule.mp (h j)
  refine ⟨fun j => ⟨a j, ?_⟩, fun j => Subtype.ext ?_⟩
  · change ‖a j‖ ≤ 1
    rw [← PadicComplex.norm_extends, ha j]
    exact (x.2 j).le
  · rw [coe_incOK]
    exact ha j

/-- **Points with open stabiliser are algebraic**: for an open subgroup `Γ` of `G_{ℚ_p}` acting on
`F(m_{ℂ_p})`, a point whose stabiliser is open in `Γ` has coordinates in `O_K̄` (the stabiliser is
open in `G_{ℚ_p}`, hence contains `G_{E'}` for a finite `E'`, `krullTopology_mem_nhds_one_iff`). -/
theorem isAlg_of_isOpen_stab {Γ : Subgroup (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)}
    (hΓo : IsOpen (Γ : Set (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)))
    (hΓ : ∀ σ ∈ Γ, CoeffFixed p (OL L) σ) {x : F.Pt p}
    (hx : IsOpen (Kummer.stab (F.galRep Γ hΓ) x : Set Γ)) : F.IsAlg x := by
  have h1 : (Subtype.val '' (Kummer.stab (F.galRep Γ hΓ) x : Set Γ)) ∈
      nhds (1 : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :=
    (hΓo.isOpenMap_subtype_val _ hx).mem_nhds ⟨1, (Kummer.stab (F.galRep Γ hΓ) x).one_mem, rfl⟩
  obtain ⟨E', hE', hsub⟩ := (krullTopology_mem_nhds_one_iff ℚ_[p] (PadicAlgCl p) _).mp h1
  haveI := hE'
  refine F.isAlg_of_fixed E' fun σ hσ => ?_
  obtain ⟨τ, hτ, rfl⟩ := hsub hσ
  exact hτ

end FGL

namespace PDivFGL

open OL FGL

variable {L : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] L] {d : ℕ}
  (P : PDivFGL (OL L) d p)
  {ε : ℕ → PadicAlgCl p} {hε : ∀ n, IsPrimitiveRoot (ε (n + 1)) (p ^ (n + 1))}
  (hεp : ∀ n, ε (n + 2) ^ p = ε (n + 1))

include hεp in
/-- **[Fo, §3.5 Lemme 2, §5.6 Prop. 9] (reduction)**: if the pairing `x₀^* ω_c` of an algebraic
point `x₀` with `ω_c = ∑_l c_l ω_l` (`c ∈ O_L^d`) is nonzero in `Ω_{O_K̄/O_L}`, then
`ρ(ω_c) = ∑_l c_l ρ(ω_l)` does not vanish on `T_p F`. -/
theorem exists_rho_ne_zero (c : Fin d → OL L) {x0 : P.F.Pt p} (hx0 : P.F.IsAlg x0)
    (h : ∑ l, algebraMap (OL L) (OKbar p) (c l) • P.F.pairing l x0 ≠ 0) :
    ∃ x : Kummer.Tp (P.F.Pt p) p,
      ∑ l, (((algebraMap (OL L) (OKbar p) (c l) : OKbar p) : PadicAlgCl p) : ℂ_[p]) *
        P.rho hε l x ≠ 0 := by
  classical
  -- a finite `E ⊇ L` containing the coordinates of `x₀`
  obtain ⟨E, hLE, hFD, hE⟩ := exists_extend (E := L)
    (Finset.univ.image fun j => (P.F.coordK x0 j : PadicAlgCl p))
  haveI := hFD
  have hΓ : ∀ σ ∈ E.fixingSubgroup, CoeffFixed p (OL L) σ := fun σ hσ =>
    coeffFixed_OL σ (fixingSubgroup_antitone hLE hσ)
  have hinv : x0 ∈ (P.F.galRep E.fixingSubgroup hΓ).invariants := by
    have h1 : ∀ j, ((x0.1 j : OC p) : ℂ_[p]) ∈ cpSubmodule E := fun j => by
      rw [← P.F.incOK_coordK hx0 j, coe_incOK]
      exact coe_mem_cpSubmodule (hE _ (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
    intro σ
    exact (P.F.galPt_fixed_iff E x0).mpr h1 (fixingSubgroupEquiv E σ)
  -- `p`-power roots with open stabilisers; they are algebraic
  obtain ⟨s, hs⟩ := Kummer.exists_isDivSeq (P.divisible OL.norm_lt_one)
    (P.stabHyp E.fixingSubgroup hΓ) hinv
  have halg : ∀ k, P.F.IsAlg (s k) := fun k =>
    P.F.isAlg_of_isOpen_stab (fixingSubgroup_isOpen E) hΓ (hs.isOpen k)
  -- `f = (s_k^* ω_c)_k ∈ V_p(Ω)` and `τ f ≠ 0`
  set f : ℕ → Ω[OKbar p⁄OL L] := fun k =>
    ∑ l, algebraMap (OL L) (OKbar p) (c l) • P.F.pairing l (s k) with hf
  have hfp : ∀ k, (p : OKbar p) • f (k + 1) = f k := fun k => by
    simp only [hf, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_comm, Nat.cast_smul_eq_nsmul, ← P.F.pairing_nsmul l (halg (k + 1)), hs.succ]
  have hτ : tau L hε f ≠ 0 := by
    rw [Ne, tau_eq_zero_iff hεp hfp]
    intro h0
    apply h
    have := congrFun h0 0
    simpa only [hf, hs.zero, Pi.zero_apply] using this
  by_contra hcon
  push Not at hcon
  apply hτ
  refine eq_zero_of_galCp_eq_chi_smul (L := E) (j := -1) (by norm_num) fun σ => ?_
  set σ0 : E.fixingSubgroup := (fixingSubgroupEquiv E).symm σ with hσ0
  have hσL : (σ0 : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) ∈ L.fixingSubgroup :=
    fixingSubgroup_antitone hLE σ0.2
  set σL := fixingSubgroupEquiv L ⟨σ0, hσL⟩ with hσL'
  set t := Kummer.cocycleFun hinv hs σ0 with ht
  have hst : ∀ k, galPt (σ0 : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (s k) =
      s k + Kummer.val _ p t k := fun k => by
    rw [ht, Kummer.val_cocycleFun, add_sub_cancel]
    rfl
  -- `σ f = f + ρ_c(t)`
  have e1 : ∀ l k, KaehlerUnion.galΩ (galOK σL) (P.F.pairing l (s k)) =
      P.F.pairing l (s k) + P.rhoSeq l t k := fun l k => by
    have e2 : KaehlerUnion.galΩ (galOK σL) (P.F.pairing l (s k)) =
        P.F.pairing l (galPt (σ0 : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (s k)) := by
      rw [FGL.pairing, galΩ_pullback _ _ _ (P.F.small_coordK _),
        ← P.coordK_galPt ⟨σ0, hσL⟩ (halg k)]
      rfl
    rw [e2, hst, P.F.pairing_add l (halg k) (P.isAlg_val t k)]
    rfl
  have hg : ∀ l k, (p : OKbar p) • (algebraMap (OL L) (OKbar p) (c l) • P.rhoSeq l t) (k + 1) =
      (algebraMap (OL L) (OKbar p) (c l) • P.rhoSeq l t) k := fun l k => by
    rw [Pi.smul_apply, Pi.smul_apply, smul_comm, P.rhoSeq_succ]
  have hgs : ∀ k, (p : OKbar p) •
      (∑ l, algebraMap (OL L) (OKbar p) (c l) • P.rhoSeq l t) (k + 1) =
      (∑ l, algebraMap (OL L) (OKbar p) (c l) • P.rhoSeq l t) k := fun k => by
    simp only [Finset.sum_apply, Finset.smul_sum, hg]
  have hgal : (fun k => KaehlerUnion.galΩ (galOK σL) (f k)) =
      f + ∑ l, algebraMap (OL L) (OKbar p) (c l) • P.rhoSeq l t := by
    funext k
    simp only [hf, map_sum, KaehlerUnion.galΩ_smul, AlgEquiv.commutes, e1, smul_add,
      Finset.sum_add_distrib, Pi.add_apply, Finset.sum_apply, Pi.smul_apply]
  have htg : tau L hε (∑ l, algebraMap (OL L) (OKbar p) (c l) • P.rhoSeq l t) = 0 := by
    rw [tau_sum hεp _ hg]
    simp_rw [tau_smul hεp (P.rhoSeq_succ _ t)]
    exact hcon t
  have key := tau_galΩ (hε := hε) hεp hfp σL
  rw [hgal, tau_add hεp hfp hgs, htg, add_zero] at key
  have he : σL.restrictScalars ℚ_[p] = σ.restrictScalars ℚ_[p] := AlgEquiv.ext fun _ => rfl
  rw [he] at key
  have key' : tau L hε f = algebraMap ℚ_[p] ℂ_[p]
      ((chi (σ.restrictScalars ℚ_[p]) : ℤ_[p]ˣ) : ℤ_[p]) * galCp E σ (tau L hε f) := key
  rw [chiPow_apply, zpow_neg_one]
  conv_rhs => rw [key']
  rw [Algebra.smul_def, ← mul_assoc, ← map_mul, ← PadicInt.coe_mul, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, PadicInt.coe_one, map_one, one_mul]

include hεp in
/-- **[Fo, §5.6 Prop. 9]** for invariant differentials: `ρ(ω_c) ≠ 0` on `T_p F` for every nonzero
`c ∈ O_L^d` (`ω_c = ∑_l c_l ω_l`; Lemme 4 `FGL.exists_pairing_ne_zero` and
`exists_rho_ne_zero`). -/
theorem exists_rho_ne_zero_of_ne_zero (c : Fin d → OL L) (hc : c ≠ 0) :
    ∃ x : Kummer.Tp (P.F.Pt p) p,
      ∑ l, (((algebraMap (OL L) (OKbar p) (c l) : OKbar p) : PadicAlgCl p) : ℂ_[p]) *
        P.rho hε l x ≠ 0 := by
  obtain ⟨x0, hx0, h⟩ := P.F.exists_pairing_ne_zero hε hεp c hc
  exact P.exists_rho_ne_zero hεp c hx0 h

end PDivFGL

end PadicHodge
