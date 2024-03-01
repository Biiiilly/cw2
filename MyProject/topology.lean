import Mathlib.Tactic

/-

# Topological Spaces

In this project, we firstly talk about the toplogical spaces and relevent properties here.
At the same time, we give some simple examples of topological spaces such as coarse topology.
Then we formalize the convergence, Hausdorff property and the closed sets in the topological spaces.
Finally, we talk about the continuous maps and homeomorphism in the topological spaces.

-/

universe u
open Set

namespace MyProject

/--
Topological Spaces consider the open sets which contains the whole set, closed under finite
intersections and closed under countable unions
-/
class TopologicalSpace (X : Type u) where
  Open_set : Set (Set X)
  Open_univ : univ ∈ Open_set
  Open_inter : ∀ s t, s ∈ Open_set → t ∈ Open_set → (s ∩ t) ∈ Open_set
  Open_sUnion : ∀ s, (∀ t ∈ s, t ∈ Open_set) → (⋃₀ s) ∈ Open_set

variable {X : Type u} [TopologicalSpace X]

def IsOpen : Set X → Prop := λ s ↦ s ∈ TopologicalSpace.Open_set

lemma IsOpen_def {s : Set X} : IsOpen s ↔ s ∈ TopologicalSpace.Open_set := by rfl

@[simp] lemma IsOpen_univ' : (univ : Set X) ∈ TopologicalSpace.Open_set := TopologicalSpace.Open_univ
@[simp] lemma IsOpen_univ : IsOpen (univ : Set X) := TopologicalSpace.Open_univ

lemma IsOpen_inter' {s t : Set X} (hs : s ∈ TopologicalSpace.Open_set) (ht : t ∈ TopologicalSpace.Open_set) :
  (s ∩ t) ∈ TopologicalSpace.Open_set :=
TopologicalSpace.Open_inter s t hs ht
lemma IsOpen_inter {s t : Set X} (hs : IsOpen s) (ht : IsOpen t) :
  IsOpen (s ∩ t) :=
TopologicalSpace.Open_inter s t hs ht

lemma IsOpen_sUnion' {s : Set (Set X)} (h : ∀ t ∈ s, t ∈ TopologicalSpace.Open_set) :
  (⋃₀ s) ∈ TopologicalSpace.Open_set :=
TopologicalSpace.Open_sUnion s h
lemma IsOpen_sUnion {s : Set (Set X)} (h : ∀ t ∈ s, IsOpen t) :
  IsOpen (⋃₀ s) :=
TopologicalSpace.Open_sUnion s h

/-
The empty set is open.
-/
lemma IsOpen_empty : IsOpen (∅ : Set X) :=
by
  rw [← sUnion_empty]
  apply IsOpen_sUnion
  exact fun t a => a.elim

lemma IsOpen_union {s t : Set X} (hs : IsOpen s) (ht : IsOpen t) :
  IsOpen (s ∪ t) :=
by
  let S : Set (Set X) := {s, t}
  have h₁ : (⋃₀ S) = s ∪ t := by simp only [sUnion_insert, sUnion_singleton]
  rw [← h₁]
  apply IsOpen_sUnion
  intro x hx
  simp only [mem_insert_iff, mem_singleton_iff] at hx
  cases' hx with hx₁ hx₂
  · rw [hx₁]
    exact hs
  · rw [hx₂]
    exact ht

/--
CoarseTopology is the collection of the empty set and the whole set.
-/
class CoarseTopology (X : Type u) [TopologicalSpace X] : Prop where
  Open_eq_empty_univ : @TopologicalSpace.Open_set X _ = {∅, univ}

lemma CoarseTopology_open_eq_empty_univ (X : Type u) [TopologicalSpace X] [CoarseTopology X] :
  @TopologicalSpace.Open_set X _ = {∅, univ} := CoarseTopology.Open_eq_empty_univ

lemma CoarseTopology_IsOpen_iff {X : Type u} [TopologicalSpace X] [CoarseTopology X] (s : Set X) :
  IsOpen s ↔ s = ∅ ∨ s = univ :=by rw [IsOpen_def, CoarseTopology_open_eq_empty_univ]; rfl

/--
DiscreteTopology is the collection of the power set.
-/
class DiscreteTopology (X : Type u) [TopologicalSpace X] : Prop where
  Open_eq_pow : @TopologicalSpace.Open_set X _ = 𝒫 univ

lemma DiscreteTopology_open_eq_pot (X : Type u) [TopologicalSpace X] [DiscreteTopology X] :
  @TopologicalSpace.Open_set X _ = 𝒫 univ := DiscreteTopology.Open_eq_pow

lemma DiscreteTopology_IsOpen {X : Type u} [TopologicalSpace X] [DiscreteTopology X] (s : Set X) :
  IsOpen s :=
by
  rw [IsOpen_def, DiscreteTopology_open_eq_pot X]
  exact fun ⦃a⦄ _ => trivial

section Convergence

/--
A sequence (uₙ) converges to a point t if for any open sets containing t, the sequence
would eventually lie in this open set.
-/
def Convergent_to (u : ℕ → X) (t : X) : Prop :=
∀ G : Set X, IsOpen G → t ∈ G → ∃ (N : ℕ), ∀ n, N ≤ n → u n ∈ G

lemma Convergent_to_def (u : ℕ → X) (t : X) :
  Convergent_to u t ↔ ∀ G : Set X, IsOpen G → t ∈ G → ∃ (N : ℕ), ∀ n, N ≤ n → u n ∈ G := by rfl

def Convergent (u : ℕ → X) : Prop :=
∃ t : X, Convergent_to u t

/--
Any convergent sequence in the discrete topology would be eventually constant.
-/
lemma DiscreteTopology_Convergent [DiscreteTopology X] (u : ℕ → X) (t : X) (h : Convergent_to u t) :
  ∃ N : ℕ, ∀ n, N ≤ n → u n = t :=
by
  rw [Convergent_to_def u t] at h
  specialize h {t} (DiscreteTopology_IsOpen {t})
  simp only [mem_singleton_iff, forall_true_left] at h
  exact h

/--
Any sequence in the coarse topology is convergent.
-/
lemma CoarseTopology_Convergent [CoarseTopology X] (u : ℕ → X) (t : X) :
  Convergent_to u t :=
by
  rw [Convergent_to_def u t]
  intro G hG htG
  rw [CoarseTopology_IsOpen_iff] at hG
  cases' hG with hG hG
  · rw [hG] at htG
    simp only [mem_empty_iff_false] at htG
  · rw [hG]
    exact Exists.intro Nat.zero fun n _ => trivial

end Convergence

section HausdorffTopology

/--
Hausdorff means for every two distinct points, we can find two disjoint open sets containing each of them.
Sometimes it's also called "separatable".
-/
class HausdorffTopology (X : Type u) [TopologicalSpace X] : Prop where
  Hausdorff : ∀ x y : X, x ≠ y → ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ U ∩ V = ∅

lemma HausdorffTopology_def :
  HausdorffTopology X ↔
    ∀ x y : X, x ≠ y → ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ U ∩ V = ∅ :=
by
  constructor
  · intro h
    exact HausdorffTopology.Hausdorff
  · intro h
    use h

variable {X : Type} [TopologicalSpace X] [HausdorffTopology X]

lemma HausdorffTopology_Hasudorff (X : Type u) [TopologicalSpace X] [HausdorffTopology X] :
  ∀ x y : X, x ≠ y → ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ U ∩ V = ∅ := HausdorffTopology.Hausdorff

/--
The Hausdorff topology has unique limit.
-/
theorem HausdorffTopology_unique_limit {u : ℕ → X} {t₁ : X} (ht₁ : Convergent_to u t₁) (ht₂ : Convergent_to u t₂) :
  t₁ = t₂ :=
by
  by_contra ht₃
  obtain ⟨U, V, hU, hV, hxU, hyU, hUv⟩ := HausdorffTopology_Hasudorff X t₁ t₂ ht₃
  rw [Convergent_to_def] at ht₁ ht₂
  obtain ⟨N₁, ht₁⟩ := ht₁ U hU hxU
  obtain ⟨N₂, ht₂⟩ := ht₂ V hV hyU
  let N : ℕ := max N₁ N₂
  specialize ht₁ N
  specialize ht₂ N
  simp only [ge_iff_le, le_max_iff, le_refl, true_or, forall_true_left, or_true] at ht₁ ht₂
  suffices : u N ∈ U ∩ V
  · rw [hUv] at this
    exact this
  · exact { left := ht₁, right := ht₂ }

end HausdorffTopology

section Closed_set

variable {X : Type u} [TopologicalSpace X]

/--
A set is closed iff the complement of this set is open.
-/
def IsClosed (V : Set X) : Prop := IsOpen Vᶜ

lemma IsClosed_def (V : Set X) : IsClosed V ↔ IsOpen Vᶜ := by rfl
lemma IsClosed_def' (V : Set X) : IsClosed Vᶜ ↔ IsOpen V :=
by
  constructor
  · intro h
    rw [IsClosed_def, compl_compl] at h
    exact h
  · intro h
    rw [IsClosed_def, compl_compl]
    exact h


lemma IsClosed_Empty : IsClosed (∅ : Set X) :=
by
  rw [IsClosed_def]
  simp only [compl_empty, IsOpen_univ]

lemma IsClosed_Univ : IsClosed (univ : Set X) :=
by
  rw [IsClosed_def]
  simp only [compl_univ]
  exact IsOpen_empty

lemma IsClosed_union (s t : Set X) (hs : IsClosed s) (ht : IsClosed t) :
  IsClosed (s ∩ t) :=
by
  rw [IsClosed_def] at hs ht ⊢
  rw [compl_inter]
  exact IsOpen_union hs ht

lemma IsClosed_sInter (s : Set (Set X)) (hs : ∀ t ∈ s, IsClosed t) :
  IsClosed (⋂₀ s) :=
by
  rw [IsClosed_def, compl_sInter]
  apply IsOpen_sUnion
  intro t ht
  simp only [mem_image] at ht
  obtain ⟨x, ht₁, ht₂⟩ := ht
  specialize hs x ht₁
  rw [← ht₂]
  exact hs

end Closed_set

section Continuous_Maps

variable [Nonempty X] {Y : Type u} [Nonempty Y] [TopologicalSpace Y]

/--
A function f : X → Y is continuous if the preimage of the open sets are also open.
-/
def Continuous {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) : Prop :=
  ∀ (s : Set Y), IsOpen s → IsOpen (f ⁻¹' s)

lemma Continuous_def (f : X → Y) :
  Continuous f ↔ ∀ (s : Set Y), IsOpen s → IsOpen (f ⁻¹' s) := by rfl

lemma CoarseTopology_Continuous [CoarseTopology Y] (f : X → Y) :
  Continuous f :=
by
  rw [Continuous_def]
  intro s hs
  rw [CoarseTopology_IsOpen_iff] at hs
  cases' hs with hs₁ hs₂
  · subst hs₁
    simp only [preimage_empty]
    exact IsOpen_empty
  · subst hs₂
    simp only [preimage_univ, IsOpen_univ]

lemma DiscreteTopology_Continuous [DiscreteTopology X] (f : X → Y) :
  Continuous f :=
by
  rw [Continuous_def]
  intro s _
  exact DiscreteTopology_IsOpen _

theorem Continuous_iff_preimage_closed (f : X → Y) :
  Continuous f ↔ ∀ (s : Set Y), IsClosed s → IsClosed (f ⁻¹' s) :=
by
  constructor
  · intro hf s hs
    rw [IsClosed_def] at hs ⊢
    rw [← preimage_compl]
    exact hf sᶜ hs
  · intro h
    rw [Continuous_def]
    intro s hs
    specialize h sᶜ ((IsClosed_def' s).2 hs)
    rw [preimage_compl] at h
    exact (IsClosed_def' _).1 h

theorem Continuous_comp {Z : Type u} [TopologicalSpace Z] {f : X → Y} {g : Y → Z} (hf : Continuous f) (hg : Continuous g) :
  Continuous ((g ∘ f) : X → Z) :=
by
  rw [Continuous_def] at hf hg ⊢
  intro s hs
  specialize hg s hs
  specialize hf (g ⁻¹' s) hg
  rw [preimage_comp]
  exact hf

lemma Continuous_constant (y : Y) :
  Continuous (fun (_ : X) ↦ (y : Y)) :=
by
  rw [Continuous_def]
  intro s _
  suffices : (fun (_ : X) ↦ (y : Y)) ⁻¹' s = ∅ ∨ (fun (_ : X) ↦ (y : Y)) ⁻¹' s = univ
  · cases' this with h₁ h₂
    · rw [h₁]
      exact IsOpen_empty
    · rw [h₂]
      exact IsOpen_univ
  have goal : range (fun (_ : X) ↦ (y : Y)) = {y}
  · ext x₁
    simp only [mem_range, mem_singleton_iff]
    constructor
    · intro h₁
      obtain ⟨_, hz⟩ := h₁
      rw [← hz]
    · intro h₁
      exact (exists_const X).mpr (id h₁.symm)
  by_cases h : y ∈ s
  · right
    simp only [preimage_eq_univ_iff]
    rw [goal]
    simp only [singleton_subset_iff]
    exact h
  · left
    simp only [preimage_eq_empty_iff]
    rw [goal]
    exact disjoint_singleton_right.mpr h

/--
A function f : X → Y is homeomorphism if it's bijective, and both f and f⁻¹ are continuous.
-/
def Homeomorphism (f : X → Y) : Prop :=
  Function.Bijective f ∧ Continuous f ∧ Continuous (Function.invFun f)

lemma Homeomorphism_def (f : X → Y) :
  Homeomorphism f ↔ Function.Bijective f ∧ Continuous f ∧ Continuous (Function.invFun f) := by rfl

/-
The reason why we prove this lemma is for the next theorem.
And I can't find this lemma in mathlib :(.
A similar version for this lemma is 'bijective_bijInv' but that seems not correct.
-/
lemma Function.bijective_invFun {X Y : Type u} [Nonempty X] [Nonempty Y] {f : X → Y} (hf : Function.Bijective f) :
  Function.Bijective (Function.invFun f) :=
by
  constructor
  · intros y₁ y₂ hy
    apply_fun f at hy
    have hf₁ := hf
    rw [Function.bijective_iff_existsUnique] at hf hf₁
    specialize hf y₁
    specialize hf₁ y₂
    rwa [Function.invFun_eq (ExistsUnique.exists hf), Function.invFun_eq (ExistsUnique.exists hf₁)] at hy
  · exact Function.invFun_surjective hf.1

/--
If X and Y are homeomorphic, then X is Hausdorff iff Y is Hausdorff.
-/
theorem Homeomorphism_Hausdorff {f : X → Y} (hf : Homeomorphism f) :
  HausdorffTopology X ↔ HausdorffTopology Y :=
by
  rw [HausdorffTopology_def, HausdorffTopology_def]
  obtain ⟨hf₁, hf₂, hf₃⟩ := hf
  constructor
  · intro hX
    intro y₁ y₂ hy
    have h₁ : Function.invFun f y₁ ≠ Function.invFun f y₂
    · have hf₄ : Function.Injective (Function.invFun f)
      · exact (Function.bijective_invFun hf₁).1
      exact fun a => hy (hf₄ a)
    obtain ⟨U, V, hU, hV, hy₁, hy₂, hUV⟩ := hX (Function.invFun f y₁) (Function.invFun f y₂) h₁
    rw [Continuous_def] at hf₃
    use (Function.invFun f ⁻¹' U)
    use (Function.invFun f ⁻¹' V)
    simp only [hf₃ U hU, hf₃ V hV, mem_preimage, hy₁, hy₂, true_and]
    rw [← preimage_inter, hUV]
    simp only [preimage_empty]
  · intro hY
    intro x₁ x₂ hx
    have h₁ : f x₁ ≠ f x₂
    · have hf₄ : Function.Injective f := by exact Function.Bijective.injective hf₁
      exact fun a => hx (hf₄ a)
    obtain ⟨U, V, hU, hV, hx₁, hx₂, hUV⟩ := hY (f x₁) (f x₂) h₁
    use (f ⁻¹' U)
    use (f ⁻¹' V)
    rw [Continuous_def] at hf₂
    simp only [hf₂ U hU, hf₂ V hV, mem_preimage, hx₁, hx₂, true_and]
    rw [← preimage_inter, hUV]
    simp only [preimage_empty]

end Continuous_Maps
end MyProject
