/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.Fontaine.Cyclotomic

/-!
# [Fo, Lemme 7] for `Ĝ_m` and [Fo, Thm 1′]

Let `L/ℚ_p` be finite inside `ℚ̄_p`, `Ω = Ω_{O_K̄/O_L}`, `d_L = ‖𝔇_{L/ℚ_p}‖ = p^{-v(𝔇_{L/ℚ_p})}`.

* **`OL.smul_D_zeta_eq_zero_iff`** ([Fo, Lemme 7] for `Γ = Ĝ_m`): for a primitive `p^{m+1}`-th
  root of unity `ζ` and `y ∈ O_K̄`, `y · dζ = 0` in `Ω` iff `|y| d_L ≤ ‖𝔇_{ℚ_p(ζ)/ℚ_p}‖`, i.e.
  `v(Ann(dζ/ζ)) = max(0, m + 1 - 1/(p-1) - v(𝔇_{L/ℚ_p}))`. (Fontaine reduces to `K = K₀` with
  Lemme 6; here the change of base `ℤ_p → O_L` is the multiplicativity of the different with a
  common generator of `O_E` over `ℤ_p` and over `O_L`.)
* For a compatible system `ε = (ε_n)` of primitive `p^n`-th roots of unity (`ε_{n+1}^p = ε_n`):
  `OL.dlogε ε n = ε_{n+1}^{-1} dε_{n+1}` with `dlogε n = p · dlogε (n+1)`;
  **`OL.xi`** `: ℚ̄_p → Ω`, `a ↦ (p^{n+1} a) · dlogε n` for any `n` with `|p^{n+1} a| ≤ 1`
  (this is Fontaine's `ξ(p^{-r} a ⊗ ε) = a · dε_r/ε_r`, with the generator `ε` of `T_p(μ)` fixed).
* **[Fo, Thm 1′]**: `ξ` is additive and `O_K̄`-linear (`OL.xi_add`, `OL.xi_smul`), surjective
  (`OL.xi_surjective`, via Lemme 5), with kernel
  `𝔞_L = {a | |a| d_L |ε_1 - 1| ≤ 1} = {v(a) ≥ -v(𝔇_{L/ℚ_p}) - 1/(p-1)}` (`OL.xi_eq_zero_iff`;
  `|ε_1 - 1|^{p-1} = p^{-1}`, `norm_sub_one_pow_totient`).

## References

* [Fo] J.-M. Fontaine, *Formes différentielles et modules de Tate des variétés abéliennes sur
  les corps locaux*, Invent. Math. 65 (1982), §2.7–2.8, Thm 1′ (p. 383).
-/

noncomputable section

open IsLocalRing Polynomial Module KaehlerDifferential IntermediateField

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime]

namespace OL

variable {L : IntermediateField ℚ_[p] (PadicAlgCl p)}

/-- `‖𝔇_{L/ℚ_p}‖`. -/
abbrev dL (L : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] L] : ℝ :=
  dnorm (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p)) L

/-! ### [Fo, Lemme 7] -/

section Lemme7

variable [FiniteDimensional ℚ_[p] L]

variable {ζ : PadicAlgCl p} {m : ℕ} (hζ : IsPrimitiveRoot ζ (p ^ (m + 1)))

include hζ in
/-- **[Fo, Lemme 7] for `Ĝ_m`**: `y · dζ = 0` in `Ω_{O_K̄/O_L}` iff
`|y| · ‖𝔇_{L/ℚ_p}‖ ≤ ‖𝔇_{ℚ_p(ζ)/ℚ_p}‖`. -/
theorem smul_D_zeta_eq_zero_iff (y : OKbar p) :
    y • D (OL L) (OKbar p) (zetaK hζ) = 0 ↔
      ‖(y : PadicAlgCl p)‖ * dL L ≤
        dnorm (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p)) ℚ_[p]⟮ζ⟯ := by
  classical
  set B := (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p))
  obtain ⟨E, hLE, hFD, hE⟩ := exists_extend (E := L) {ζ}
  have hζE : ζ ∈ E := hE ζ (Finset.mem_singleton_self _)
  haveI : Fact (L ≤ E) := ⟨hLE⟩
  -- a generator of `O_E` over `ℤ_p`, hence over `O_L`
  obtain ⟨b, hb⟩ := exists_adjoin_eq_top' B E
  have hbL : Algebra.adjoin (OL L) {b} = ⊤ := adjoin_eq_top_of_tower (L := B) (E := L) hb
  obtain ⟨ζE, hζE'⟩ := exists_algebraMap_eq (E := E) (y := zetaK hζ) hζE
  obtain ⟨x, hx⟩ := exists_eq_smul_D (L := B) hb (D (OL B) (OL E) ζE)
  have hxL : x • D (OL L) (OL E) b = D (OL L) (OL E) ζE := by
    have := congrArg (map (OL B) (OL L) (OL E) (OL E)) hx
    rwa [map_smul, map_D, map_D, Algebra.algebraMap_self, RingHom.id_apply,
      RingHom.id_apply] at this
  -- the two descriptions of the annihilator of `dζ` over `ℤ_p`
  have hB : ∀ y' : OKbar p, ‖(y' : PadicAlgCl p)‖ ≤ dnorm B ℚ_[p]⟮ζ⟯ ↔
      ‖(y' : PadicAlgCl p)‖ * nrm x ≤ dnorm B E := by
    intro y'
    rw [← smul_D_zeta_eq_zero_iff_bot hζ, ← smul_mapOK_smul_D_eq_zero_iff hb, hx, map_D, hζE']
  -- over `O_L`
  have hLx : y • D (OL L) (OKbar p) (zetaK hζ) = 0 ↔ ‖(y : PadicAlgCl p)‖ * nrm x ≤ dnorm L E := by
    rw [← smul_mapOK_smul_D_eq_zero_iff hbL, hxL, map_D, hζE']
  rw [hLx]
  set δ : OKbar p := algebraMap (OL L) (OKbar p) (dgen B L)
  have hδ : ‖(δ : PadicAlgCl p)‖ = dL L := (nrm_eq_norm_OKbar (dgen B L)).symm
  have hdL : 0 < dL L := dnorm_pos
  have key := hB (y * δ)
  rw [Subring.coe_mul, norm_mul, hδ] at key
  rw [key, dnorm_tower (L := B) (E := L) (E' := E), mul_right_comm _ (dL L),
    mul_le_mul_iff_of_pos_right hdL]

end Lemme7

/-! ### [Fo, Thm 1′] -/

section ThmOne

variable {ε : ℕ → PadicAlgCl p} (hε : ∀ n, IsPrimitiveRoot (ε (n + 1)) (p ^ (n + 1)))
  (hεp : ∀ n, ε (n + 2) ^ p = ε (n + 1))

include hε in
theorem norm_eps (n : ℕ) : ‖ε (n + 1)‖ = 1 := norm_zeta (hε n)

/-- `ε_{n+1} ∈ O_K̄`. -/
def epsK (n : ℕ) : OKbar p := zetaK (hε n)

/-- `ε_{n+1}^{-1} ∈ O_K̄`. -/
def epsInvK (n : ℕ) : OKbar p :=
  ⟨(ε (n + 1))⁻¹, by
    change ‖(ε (n + 1))⁻¹‖ ≤ 1
    rw [norm_inv, norm_eps hε, inv_one]⟩

theorem coe_epsK (n : ℕ) : ((epsK hε n : OKbar p) : PadicAlgCl p) = ε (n + 1) := rfl

include hε in
theorem eps_ne_zero (n : ℕ) : ε (n + 1) ≠ 0 :=
  (hε n).ne_zero (pow_ne_zero _ hp.out.ne_zero)

theorem epsInvK_mul (n : ℕ) : epsInvK hε n * epsK hε n = 1 :=
  Subtype.ext (inv_mul_cancel₀ (eps_ne_zero hε n))

variable (L) in
/-- `dlog ε_{n+1} = ε_{n+1}^{-1} dε_{n+1} ∈ Ω_{O_K̄/O_L}`. -/
def dlogε (n : ℕ) : Ω[OKbar p⁄OL L] := epsInvK hε n • D (OL L) (OKbar p) (epsK hε n)

include hεp in
/-- `dlog ε_{n+1} = p · dlog ε_{n+2}`. -/
theorem dlogε_eq_p_smul (n : ℕ) : dlogε L hε n = (p : OKbar p) • dlogε L hε (n + 1) := by
  have he : epsK hε n = epsK hε (n + 1) ^ p := Subtype.ext (by
    rw [SubmonoidClass.coe_pow, coe_epsK, coe_epsK, hεp])
  rw [dlogε, dlogε, he, Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul (OKbar p), smul_smul,
    smul_smul, smul_smul]
  congr 1
  apply Subtype.ext
  simp only [Subring.coe_mul, SubmonoidClass.coe_pow, Subring.coe_natCast, epsInvK, coe_epsK]
  have h0 := eps_ne_zero hε (n + 1)
  have hε' : ε (n + 1 + 1) ^ p = ε (n + 1) := hεp n
  have hpow : ε (n + 1 + 1) ^ p = ε (n + 1 + 1) ^ (p - 1) * ε (n + 1 + 1) := by
    rw [← pow_succ, Nat.sub_add_cancel hp.out.one_le]
  rw [← hε', hpow]
  field_simp

include hεp in
theorem dlogε_eq_pow_smul (n k : ℕ) :
    dlogε L hε n = ((p : OKbar p) ^ k) • dlogε L hε (n + k) := by
  induction k with
  | zero => rw [pow_zero, one_smul, add_zero]
  | succ k ih =>
    rw [ih, dlogε_eq_p_smul hε hεp (n + k), smul_smul, ← pow_succ, add_assoc]

include hεp in
theorem eps_pow (n : ℕ) : ε (n + 1) ^ p ^ n = ε 1 := by
  induction n with
  | zero => rw [pow_zero, pow_one]
  | succ n ih => rw [pow_succ', pow_mul, hεp, ih]

/-- `p^{n} a` as an element of `O_K̄` when `|p^n a| ≤ 1`. -/
def pa (a : PadicAlgCl p) (n : ℕ) (h : ‖(p : PadicAlgCl p) ^ n * a‖ ≤ 1) : OKbar p :=
  ⟨(p : PadicAlgCl p) ^ n * a, h⟩

theorem exists_norm_pow_mul_le (a : PadicAlgCl p) :
    ∃ n : ℕ, ‖(p : PadicAlgCl p) ^ (n + 1) * a‖ ≤ 1 := by
  have hp1 : ‖(p : PadicAlgCl p)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)), norm_algebraMap', Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
  rcases (norm_nonneg a).eq_or_lt with h0 | h0
  · exact ⟨0, by rw [norm_mul, ← h0, mul_zero]; exact zero_le_one⟩
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr h0) hp1
  refine ⟨n, ?_⟩
  rw [norm_mul, norm_pow, pow_succ]
  calc ‖(p : PadicAlgCl p)‖ ^ n * ‖(p : PadicAlgCl p)‖ * ‖a‖
        ≤ ‖(p : PadicAlgCl p)‖ ^ n * ‖a‖ := by
        gcongr; exact mul_le_of_le_one_right (by positivity) hp1.le
    _ ≤ ‖a‖⁻¹ * ‖a‖ := by gcongr
    _ = 1 := inv_mul_cancel₀ h0.ne'

theorem norm_pow_mul_le_of_le {c : PadicAlgCl p} {k n : ℕ}
    (hk : ‖(p : PadicAlgCl p) ^ (k + 1) * c‖ ≤ 1) (hkn : k ≤ n) :
    ‖(p : PadicAlgCl p) ^ (n + 1) * c‖ ≤ 1 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkn
  rw [show k + j + 1 = j + (k + 1) by ring, pow_add, mul_assoc, norm_mul]
  exact mul_le_one₀ (by
    rw [norm_pow, ← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)), norm_algebraMap']
    exact pow_le_one₀ (norm_nonneg _) (Padic.norm_p_lt_one.le))
    (norm_nonneg _) hk

variable (L) in
/-- **Fontaine's map `ξ`** ([Fo, Thm 1′]): `a ↦ (p^{n+1} a) · dlog ε_{n+1}` for `n` minimal with
`|p^{n+1} a| ≤ 1` (any such `n` gives the same value, `xi_eq`). -/
def xi (a : PadicAlgCl p) : Ω[OKbar p⁄OL L] :=
  pa a (Nat.find (exists_norm_pow_mul_le a) + 1) (Nat.find_spec (exists_norm_pow_mul_le a)) •
    dlogε L hε (Nat.find (exists_norm_pow_mul_le a))

include hεp in
theorem pa_smul_dlogε_eq (a : PadicAlgCl p) {n k : ℕ} (h : ‖(p : PadicAlgCl p) ^ (n + 1) * a‖ ≤ 1)
    (h' : ‖(p : PadicAlgCl p) ^ (n + k + 1) * a‖ ≤ 1) :
    pa a (n + k + 1) h' • dlogε L hε (n + k) = pa a (n + 1) h • dlogε L hε n := by
  rw [dlogε_eq_pow_smul hε hεp n k, smul_smul]
  congr 1
  apply Subtype.ext
  simp only [pa, Subring.coe_mul, SubmonoidClass.coe_pow, Subring.coe_natCast]
  ring

include hεp in
theorem xi_eq (a : PadicAlgCl p) {n : ℕ} (h : ‖(p : PadicAlgCl p) ^ (n + 1) * a‖ ≤ 1) :
    xi L hε a = pa a (n + 1) h • dlogε L hε n := by
  set N := Nat.find (exists_norm_pow_mul_le a)
  have hN : N ≤ n := Nat.find_min' _ h
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  exact (pa_smul_dlogε_eq hε hεp a _ h).symm

include hεp in
theorem xi_add (a b : PadicAlgCl p) : xi L hε (a + b) = xi L hε a + xi L hε b := by
  obtain ⟨na, ha⟩ := exists_norm_pow_mul_le a
  obtain ⟨nb, hb⟩ := exists_norm_pow_mul_le b
  set n := max na nb
  have hle : ∀ c : PadicAlgCl p, ∀ k, ‖(p : PadicAlgCl p) ^ (k + 1) * c‖ ≤ 1 → k ≤ n →
      ‖(p : PadicAlgCl p) ^ (n + 1) * c‖ ≤ 1 := fun c k hk hkn => norm_pow_mul_le_of_le hk hkn
  have ha' := hle a na ha (le_max_left _ _)
  have hb' := hle b nb hb (le_max_right _ _)
  have hab : ‖(p : PadicAlgCl p) ^ (n + 1) * (a + b)‖ ≤ 1 := by
    rw [mul_add]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha' hb')
  rw [xi_eq hε hεp a ha', xi_eq hε hεp b hb', xi_eq hε hεp (a + b) hab, ← add_smul]
  congr 1
  exact Subtype.ext (mul_add _ _ _)

include hεp in
theorem xi_smul (y : OKbar p) (a : PadicAlgCl p) :
    xi L hε ((y : PadicAlgCl p) * a) = y • xi L hε a := by
  obtain ⟨n, h⟩ := exists_norm_pow_mul_le a
  have h' : ‖(p : PadicAlgCl p) ^ (n + 1) * ((y : PadicAlgCl p) * a)‖ ≤ 1 := by
    rw [mul_left_comm, norm_mul]
    exact mul_le_one₀ y.2 (norm_nonneg _) h
  rw [xi_eq hε hεp a h, xi_eq hε hεp _ h', smul_smul]
  congr 1
  exact Subtype.ext (mul_left_comm _ _ _)

include hε in
/-- `|ε_1 - 1|` (`= p^{-1/(p-1)}`). -/
theorem norm_eps_one_sub_one_pow : ‖ε 1 - 1‖ ^ (p - 1) = (p : ℝ)⁻¹ := by
  have h := norm_sub_one_pow_totient (hε 0)
  rwa [zero_add, pow_one, Nat.totient_prime hp.out] at h

include hεp in
/-- **[Fo, Thm 1′], the kernel of `ξ`**: `ξ(a) = 0` iff `|a| · ‖𝔇_{L/ℚ_p}‖ · |ε_1 - 1| ≤ 1`,
i.e. `v(a) ≥ -v(𝔇_{L/ℚ_p}) - 1/(p-1)`. -/
theorem xi_eq_zero_iff [FiniteDimensional ℚ_[p] L] (a : PadicAlgCl p) :
    xi L hε a = 0 ↔ ‖a‖ * dL L * ‖ε 1 - 1‖ ≤ 1 := by
  obtain ⟨n, h⟩ := exists_norm_pow_mul_le a
  rw [xi_eq hε hεp a h, dlogε, smul_smul, epsK, smul_D_zeta_eq_zero_iff (hε n)]
  have hd := dnorm_bot_cyc (hε n)
  rw [eps_pow hεp n] at hd
  have hp0 : 0 < ‖(p : PadicAlgCl p)‖ ^ (n + 1) := by
    have : (p : PadicAlgCl p) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    positivity
  have he0 : 0 < ‖ε 1 - 1‖ := by
    rcases (norm_nonneg (ε 1 - 1)).eq_or_lt with h0 | h0
    · have := norm_eps_one_sub_one_pow hε
      rw [← h0, zero_pow (by have := hp.out.two_le; omega)] at this
      exact absurd this.symm (inv_ne_zero (by exact_mod_cast hp.out.ne_zero))
    · exact h0
  have hn : ‖((pa a (n + 1) h * epsInvK hε n : OKbar p) : PadicAlgCl p)‖ =
      ‖(p : PadicAlgCl p)‖ ^ (n + 1) * ‖a‖ := by
    simp only [pa, epsInvK, Subring.coe_mul, norm_mul, norm_pow, norm_inv, norm_eps hε, inv_one,
      mul_one]
  rw [hn, ← mul_le_mul_iff_of_pos_right he0, hd,
    show ‖(p : PadicAlgCl p)‖ ^ (n + 1) * ‖a‖ * dL L * ‖ε 1 - 1‖ =
      ‖a‖ * dL L * ‖ε 1 - 1‖ * ‖(p : PadicAlgCl p)‖ ^ (n + 1) by ring,
    mul_le_iff_le_one_left hp0]

include hεp in
/-- **[Fo, Thm 1′], surjectivity of `ξ`** (via [Fo, Lemme 5]). -/
theorem xi_surjective [FiniteDimensional ℚ_[p] L] : Function.Surjective (xi L hε) := by
  classical
  intro ω
  obtain ⟨s, hs⟩ := exists_finset_mapOK_eq ω
  obtain ⟨E, hLE, hFD, hE⟩ := exists_extend (E := L) s
  haveI : Fact (L ≤ E) := ⟨hLE⟩
  obtain ⟨η, rfl⟩ := hs E hE
  obtain ⟨b, hb⟩ := exists_adjoin_eq_top' L E
  obtain ⟨x, rfl⟩ := exists_eq_smul_D hb η
  -- choose `n` with `|p|^{n+1} ≤ ‖𝔇_{E/L}‖ d_L |ε_1 - 1|`
  have he0 : 0 < ‖ε 1 - 1‖ := by
    rcases (norm_nonneg (ε 1 - 1)).eq_or_lt with h0 | h0
    · have := norm_eps_one_sub_one_pow hε
      rw [← h0, zero_pow (by have := hp.out.two_le; omega)] at this
      exact absurd this.symm (inv_ne_zero (by exact_mod_cast hp.out.ne_zero))
    · exact h0
  have hdL : 0 < dL L := dnorm_pos
  have hpos : 0 < dnorm L E * dL L * ‖ε 1 - 1‖ :=
    mul_pos (mul_pos dnorm_pos hdL) he0
  have hp1 : ‖(p : PadicAlgCl p)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)), norm_algebraMap', Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos hp1
  -- `Ann(dlog ε_{n+1}) ⊆ Ann(ω)`
  have hann : ∀ y : OKbar p, y • dlogε L hε n = 0 →
      y • map (OL L) (OL L) (OL E) (OKbar p) (x • D (OL L) (OL E) b) = 0 := by
    intro y hy
    rw [dlogε, smul_smul, epsK, smul_D_zeta_eq_zero_iff (hε n)] at hy
    have hd := dnorm_bot_cyc (hε n)
    rw [eps_pow hεp n] at hd
    rw [smul_mapOK_smul_D_eq_zero_iff hb]
    simp only [Subring.coe_mul, epsInvK, norm_mul, norm_inv, norm_eps hε, inv_one,
      mul_one] at hy
    have h2 : ‖(y : PadicAlgCl p)‖ * (dL L * ‖ε 1 - 1‖) <
        dnorm L E * (dL L * ‖ε 1 - 1‖) := by
      calc ‖(y : PadicAlgCl p)‖ * (dL L * ‖ε 1 - 1‖)
          = (‖(y : PadicAlgCl p)‖ * dL L) * ‖ε 1 - 1‖ := by ring
        _ ≤ dnorm (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p)) ℚ_[p]⟮ε (n + 1)⟯ * ‖ε 1 - 1‖ :=
          mul_le_mul_of_nonneg_right hy he0.le
        _ = ‖(p : PadicAlgCl p)‖ ^ (n + 1) := hd
        _ ≤ ‖(p : PadicAlgCl p)‖ ^ n := pow_le_pow_of_le_one (norm_nonneg _) hp1.le n.le_succ
        _ < dnorm L E * dL L * ‖ε 1 - 1‖ := hn
        _ = dnorm L E * (dL L * ‖ε 1 - 1‖) := by ring
    have h3 := lt_of_mul_lt_mul_right h2 (by positivity)
    calc ‖(y : PadicAlgCl p)‖ * nrm x ≤ ‖(y : PadicAlgCl p)‖ * 1 :=
          mul_le_mul_of_nonneg_left (nrm_le_one x) (norm_nonneg _)
      _ ≤ dnorm L E := by rw [mul_one]; exact h3.le
  obtain ⟨c, hc⟩ := exists_smul_eq_of_annihilator_le hann
  refine ⟨(c : PadicAlgCl p) * ((p : PadicAlgCl p) ^ (n + 1))⁻¹, ?_⟩
  have h1 : ‖(p : PadicAlgCl p) ^ (n + 1) * ((c : PadicAlgCl p) *
      ((p : PadicAlgCl p) ^ (n + 1))⁻¹)‖ ≤ 1 := by
    rw [mul_left_comm, mul_inv_cancel₀ (pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)),
      mul_one]
    exact c.2
  rw [xi_eq hε hεp _ h1, ← hc]
  congr 1
  apply Subtype.ext
  change (p : PadicAlgCl p) ^ (n + 1) * ((c : PadicAlgCl p) * ((p : PadicAlgCl p) ^ (n + 1))⁻¹) = c
  rw [mul_left_comm, mul_inv_cancel₀ (pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)), mul_one]

end ThmOne

end OL

end PadicHodge
