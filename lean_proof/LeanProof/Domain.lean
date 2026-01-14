import Mathlib.Tactic
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.EReal.Basic
import Mathlib.Data.ENNReal.Basic

-- Probably deprecated when https://github.com/leanprover-community/mathlib4/pull/33876
-- is merged
instance {α : Type} : Coe α (WithTop (WithBot α)) where
  coe x := (Coe.coe x : WithBot α)

/-!
# Domain definitions for asymptotic analysis

This file defines the three semantic domains used in asymptotic analysis:
  * Denotational domain `Dd : ℕ+ → ℝ`
  * Concrete domain `Dc : Set Dd`
  * Abstract domain `Da : ℝ≥0∞ × ℝ` with ⊥ and ⊤

They are equipped with the respective orderings:
  * `Dd`: f ⊑d g iff ∀ ε > 0, ∃ N, ∀ n ≥ N, |f n| ≤ (1 + ε) * |g n|
    - Preorder (reflexive and transitive)
  * `Dc`: A ⊑c B iff A ⊆ B
    - Partial order (reflexive, transitive, and antisymmetric)
  * `Da`: lexicographic order with second component prioritized
    - Partial order (reflexive, transitive, and antisymmetric)

## Main definitions
* `Dd`: Functions from positive naturals to reals
* `Dc`: Sets of functions (powerset of Dd)
* `Da`: Abstract domain with bottom and top elements

## Main results
* `Dd.le_refl`, `Dd.le_trans`: `⊑d` is a preorder
* `Dc.le_refl`, `Dc.le_trans`, `Dc.le_antisymm`: `⊑c` is a partial order
* `Da.le_refl`, `Da.le_trans`, `Da.le_antisymm`: `⊑a` is a partial order
-/

open Real ENNReal

/-- Denotational domain: functions from positive naturals to reals. -/
def Dd := ℕ+ → ℝ

/-- Concrete domain: sets of denotational functions. -/
abbrev Dc := Set Dd

/-- Abstract domain: extended non-negative reals paired with reals,
    plus top and bottom elements. -/
abbrev Da := WithTop (WithBot (ℝ ×ₗ ℝ≥0∞))

@[match_pattern] def Da.elem : ℝ ×ₗ ℝ≥0∞ → Da := Coe.coe

@[cases_eliminator, elab_as_elim]
def Da.rec {motive : Da → Prop}
  (onBot : motive ⊥)
  (onElem : ∀ (x : ℝ ×ₗ ℝ≥0∞), motive (↑x))
  (onTop : motive ⊤)
  (a : Da) : motive a
:= match a with
   | ⊤  => onTop
   | ⊥  => onBot
   | .elem x => onElem x


/-- Signed abstract domain: extended reals paired with reals,
    plus top and bottom elements. -/
abbrev Dastar := WithTop (WithBot (ℝ ×ₗ EReal))

@[match_pattern] def Dastar.elem : ℝ ×ₗ EReal → Dastar := Coe.coe

@[cases_eliminator, elab_as_elim]
def Dastar.rec {motive : Dastar → Prop}
  (onBot : motive ⊥)
  (onElem : ∀ (x : ℝ ×ₗ EReal), motive (↑x))
  (onTop : motive ⊤)
  (a : Dastar) : motive a
:= match a with
   | ⊤  => onTop
   | ⊥  => onBot
   | .elem x => onElem x


namespace Dd

/-- Denotational ordering: f ⊑d g means f is asymptotically dominated by g.
    Formally, for every ε > 0, there exists N such that for all n ≥ N,
    |f n| ≤ (1 + ε) * |g n|. -/
def le (f g : Dd) : Prop :=
  ∀ ε > 0, ∃ N : ℕ+, ∀ n ≥ N, |f n| ≤ (1 + ε) * |g n|

/-- Notation for denotational ordering. -/
scoped infix:50 " ⊑d " => le

/-- Every function is asymptotically dominated by itself. -/
lemma le_refl (f : Dd) : f ⊑d f := by
  intro ε hε
  use 1
  intro n _
  calc |f n| = 1 * |f n| := by ring
           _ ≤ (1 + ε) * |f n| := by
               apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
               linarith

/-- For δ ∈ [0,1], we have (1 + δ)² ≤ 1 + 3δ.
    This inequality is used to control error accumulation in transitivity. -/
private lemma sq_le_one_add_three_mul {δ : ℝ} (hδ_nonneg : 0 ≤ δ) (hδ_le1 : δ ≤ 1) :
    (1 + δ) ^ 2 ≤ 1 + 3 * δ := by
  have h_sq_le : δ ^ 2 ≤ δ := by
    calc δ ^ 2 = δ * δ := by rw[sq]
             _ ≤ 1 * δ := mul_le_mul_of_nonneg_right hδ_le1 hδ_nonneg
             _ = δ := one_mul δ
  calc (1 + δ) ^ 2 = 1 + 2 * δ + δ ^ 2 := by ring
                 _ ≤ 1 + 2 * δ + δ := add_le_add_left h_sq_le _
                 _ = 1 + 3 * δ := by ring

/-- Asymptotic dominance is transitive: if f ⊑d g and g ⊑d h, then f ⊑d h. -/
lemma le_trans {f g h : Dd} (hfg : f ⊑d g) (hgh : g ⊑d h) : f ⊑d h := by
  intro ε hε
  -- Choose δ = min(1, ε/3) to ensure (1 + δ)² ≤ 1 + 3δ ≤ 1 + ε
  set δ := min 1 (ε / 3) with hδ_def
  have hδ_pos : 0 < δ := lt_min (by norm_num) (by linarith)

  -- Get witnesses from both hypotheses
  obtain ⟨N1, hN1⟩ := hfg δ hδ_pos
  obtain ⟨N2, hN2⟩ := hgh δ hδ_pos
  refine ⟨max N1 N2, fun n hn => ?_⟩

  -- Establish key bounds on δ
  have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
  have hδ_le1 : δ ≤ 1 := min_le_left ..
  have h3δ : 3 * δ ≤ ε := by
    calc 3 * δ ≤ 3 * (ε / 3) := by apply mul_le_mul_of_nonneg_left (min_le_right ..) (by norm_num)
             _ = ε := by ring

  -- Chain the inequalities
  calc |f n| ≤ (1 + δ) * |g n| := by apply hN1 n (le_of_max_le_left hn)
           _ ≤ (1 + δ) * ((1 + δ) * |h n|) :=
               mul_le_mul_of_nonneg_left (hN2 n (le_of_max_le_right hn)) (by linarith)
           _ = (1 + δ) ^ 2 * |h n| := by ring
           _ ≤ (1 + 3 * δ) * |h n| :=
               mul_le_mul_of_nonneg_right (sq_le_one_add_three_mul hδ_nonneg hδ_le1) (abs_nonneg _)
           _ ≤ (1 + ε) * |h n| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)

end Dd

namespace Dc
-- TODO: This is probably just the default LE for (Set _)
#synth LE (Set _)
#check Set.instLE
#check Set.Subset

/-- Concrete ordering: subset inclusion. -/
def le (A B : Dc) : Prop := ∀ f : Dd, A f → B f

/-- Notation for concrete ordering. -/
scoped infix:50 " ⊑c " => le

/-- Subset inclusion is reflexive. -/
lemma le_refl (A : Dc) : A ⊑c A := fun _ hf => hf

/-- Subset inclusion is antisymmetric. -/
lemma le_antisymm {A B : Dc} (hAB : A ⊑c B) (hBA : B ⊑c A) : A = B :=
  Set.ext fun f => ⟨hAB f, hBA f⟩

/-- Subset inclusion is transitive. -/
lemma le_trans {A B C : Dc} (hAB : A ⊑c B) (hBC : B ⊑c C) : A ⊑c C :=
  fun f hfA => hBC f (hAB f hfA)

end Dc

instance : PartialOrder Dc where
  le := Dc.le
  le_refl := Dc.le_refl
  le_trans := @Dc.le_trans
  le_antisymm := @Dc.le_antisymm
