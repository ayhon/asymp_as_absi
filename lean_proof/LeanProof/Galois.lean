import Mathlib.Order.SetNotation
import Mathlib.Data.EReal.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Order.GaloisConnection.Basic
import LeanProof.Domain

open Set NNReal Dd Dc Da

/-!
# Abstraction and concretization functions

This file defines the Galois connection between concrete and abstract domains:
- `α : Dc → Da` (abstraction)
- `γ : Da → Dc` (concretization)

## Main definitions

* `α1`: Helper computing the infimum of growth exponents
* `α2`: Helper computing the infimum of coefficients for a fixed exponent
* `α`: Abstraction function from concrete to abstract domain
* `γ`: Concretization function from abstract to concrete domain

## Main results

* `α_monotone`: α is monotone
* `γ_monotone`: γ is monotone
* `γα_inflation`: S ⊑c γ(α(S)) for all S
* `αγ_deflation`: α(γ(a)) ⊑a a for all a
* `galois_connection`: α and γ form a Galois connection
-/

/-- The set of real exponents r such that every function in S is asymptotically
    dominated by n^r. -/
def growth_exponents (S : Dc) : Set ℝ :=
  {r : ℝ | ∀ f ∈ S, f ⊑d fun n => n^r}

theorem growth_exponents_le_growth_exponents (X Y : Dc)
: X ⊆ Y → growth_exponents Y ⊆ growth_exponents X
:= by
  intros X_Y
  dsimp [growth_exponents]
  intros e
  dsimp only [mem_setOf_eq]
  intros hY f f_X ε ε_pos
  apply X_Y at f_X
  obtain ⟨N, hN⟩ :=  hY f f_X ε ε_pos
  exists N

/-- Abstraction helper: computes the infimum growth exponent for a set of functions.

    For a set S ⊆ Dd, this returns inf{r ∈ ℝ | ∀f ∈ S, f ⊑d n^r} as an extended
    real number. This represents the "tightest" polynomial bound on the growth
    rate of functions in S. Returns ⊤ if no such bound exists, ⊥ if all functions
    grow slower than any polynomial. -/
noncomputable def α1 (S : Dc) : EReal :=
  sInf ((↑) '' growth_exponents S)

theorem α1_monotone(X Y: Dc)
: X ⊆ Y → α1 X ≤ α1 Y
:= by
  intros X_Y
  have := growth_exponents_le_growth_exponents _ _ X_Y
  dsimp [α1]
  apply sInf_le_sInf
  dsimp [image]
  intros e
  dsimp only [mem_setOf_eq]
  rintro ⟨a, a_Y, rfl⟩
  exists a
  apply this at a_Y
  grind

/-- The set of non-negative real coefficients c such that every function in S
    is asymptotically dominated by c·n^r. -/
def growth_coefficients (S : Dc) (r : ℝ) : Set ℝ≥0 :=
  {c : ℝ≥0 | ∀ f ∈ S, f ⊑d fun n => (c : ℝ) * n^r}

theorem growth_coefficients_le_growth_coefficients (X Y : Dc)
: X ⊆ Y → growth_coefficients Y ≤ growth_coefficients X
:= by
  intros X_Y r
  dsimp [growth_coefficients]
  intros e
  dsimp only [mem_setOf_eq]
  intros hY f f_X ε ε_pos
  apply X_Y at f_X
  obtain ⟨N, hN⟩ :=  hY f f_X ε ε_pos
  exists N


/-- Abstraction helper: computes the infimum coefficient for a fixed exponent.

    For a set S and exponent r, returns inf{c ≥ 0 | ∀f ∈ S, f ⊑d c·n^r}.
    Returns a dummy value (0) if the exponent is ⊤ or ⊥. -/
noncomputable def α2 (S : Dc) : ℝ → ENNReal := fun r =>
  sInf ((↑) '' growth_coefficients S r)

theorem α2_monotone(X Y: Dc)
: X ⊆ Y → α2 X ≤ α2 Y
:= by
  intros X_Y r
  have := growth_coefficients_le_growth_coefficients _ _ X_Y
  dsimp [α2]
  apply sInf_le_sInf
  dsimp [image]
  intros e
  dsimp only [mem_setOf_eq]
  rintro ⟨a, a_Y, rfl⟩
  exists a
  apply this at a_Y
  grind

/-- Abstraction function from concrete to abstract domain.

    Maps a set S ⊆ Dd to the tightest abstract bound (c, r) such that
    all functions in S are dominated by c·n^r. Returns ⊤ or ⊥ for
    super-polynomial or sub-polynomial growth. -/
noncomputable def α (S : Dc) : Da :=
  match α1 S with
  | ⊥ => ⊥
  | ⊤ => ⊤
  | (r : ℝ) => Da.elem (r, α2 S r)

/-- Concretization function: maps an abstract element to the set of functions
    asymptotically dominated by it.

    - `bot` maps to functions dominated by all polynomials (sub-polynomial)
    - `top` maps to all functions (super-polynomial or no bound)
    - `elem (c, r)` behavior depends on c:
      * c = 0: functions dominated by a·n^r for all a > 0
      * c = ∞: functions dominated by n^s for all s > r
      * otherwise: functions dominated by c·n^r -/
def γ : Da → Dc
  | ⊥ => {f | ∀ s : ℝ, f ⊑d fun n => n^s}
  | ⊤ =>   univ
  | .elem (r, c) =>
      if c = 0 then
        {f | ∀ a > 0, f ⊑d fun n => a * n^r}
      else if c = ⊤ then
        {f | ∀ s > r, f ⊑d fun n => n^s}
      else
        {f | f ⊑d fun n => c.toReal * n^r}

/-- α is monotone: if S₁ ⊆ S₂ then α(S₁) ⊑a α(S₂). -/
theorem α_monotone : Monotone α := by
  intro x y x_y
  have α1_xy := α1_monotone _ _ x_y
  dsimp only [α] at *
  match hx: α1 x, hy: α1 y with
  | ⊥, _ => simp only [bot_le]
  | ⊤, _ =>
    change (α1 x = ⊤) at hx
    simp only [hx, top_le_iff] at α1_xy
    simp only [←hy, α1_xy, _root_.le_refl]
  | (r: ℝ), ⊥ =>
    change (α1 x = (r: ℝ)) at hx
    change (α1 y = ⊥) at hy
    simp only [hx, hy] at *
    simp only [le_bot_iff, EReal.coe_ne_bot] at α1_xy
  | (r: ℝ), ⊤  =>
    simp only [le_top]
  | (r: ℝ), (r': ℝ) =>
    change (α1 x = (r: ℝ)) at hx
    change (α1 y = (r': ℝ)) at hy
    simp only [hx, hy] at α1_xy
    dsimp only [Real.toEReal, Function.comp_apply, elem, Coe.coe]
    simp only [WithTop.coe_le_coe, WithBot.coe_le_coe, Lex]
    apply Lean.Grind.PartialOrder.le_iff_lt_or_eq.mp at α1_xy
    obtain r_lt_r' | r_eq_r' :=  α1_xy
    · left
      assumption
    · simp only [EReal.coe_eq_coe_iff] at r_eq_r'
      subst r'
      right
      apply α2_monotone
      assumption

/-- γ is monotone: if a₁ ⊑a a₂ then γ(a₁) ⊆ γ(a₂). -/
theorem γ_monotone : Monotone γ := by
  intros x y x_y
  match hx: x, hy: y with
  | _, ⊤  =>
    change (y = ⊤) at hy
    simp only [γ, le_eq_subset, subset_univ]
  | _, ⊥  =>
    change (y = ⊥) at hy
    conv => rhs; dsimp [γ]
    sorry
  | _, Da.elem (r', c') =>
    change (y = Da.elem (r', c')) at hy
    sorry

/-- Inflation property: S is contained in γ(α(S)). -/
theorem γα_inflation (S : Dc) : S ⊑c γ (α S) := sorry

/-- Deflation property: α(γ(a)) is at most a. -/
theorem αγ_deflation (a : Da) : α (γ a) ≤ a := sorry

/-- α and γ form a Galois connection: α(S) ⊑a a ⟺ S ⊑c γ(a). -/
theorem galois_connection : GaloisConnection α γ := by
  sorry
