-- 1
section

variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := 
 ⟨fun h => ⟨fun x => (h x).left, fun x => (h x).right⟩, 
  fun h => fun x => ⟨h.left x, h.right x⟩⟩

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := 
 fun h => fun h₁ => fun x => (h x) (h₁ x)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := 
 fun h => fun x => h.elim (fun h₁ => Or.inl (h₁ x)) (fun h₁ => Or.inr (h₁ x))

end

-- 2
section

open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) := 
  fun x => ⟨fun h => h x, fun h => fun y => h⟩

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := 
  ⟨fun h => ((em r).elim (fun h₁ => Or.inr h₁) (fun h₁ => 
    have h₂ : ∀ x, p x := fun x => (h x).elim id (fun h₄ => absurd h₄ h₁) 
    Or.inl h₂)), 
   fun h => fun x => h.elim (fun h₁ => Or.inl (h₁ x)) (fun hr => Or.inr hr)⟩

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := 
  ⟨fun h => fun hr => fun x => h x hr, fun h => fun x => fun hr => h hr x⟩

end

-- 3
section

variable (men : Type) (barber : men)
variable  (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := 
  have h₁ : shaves barber barber ↔ ¬ shaves barber barber := h barber
  have h₂ : ¬ shaves barber barber := fun h₃ => h₁.mp h₃ h₃
  h₂ (h₁.mpr h₂)

end

-- 4
section

def even (n : Nat) : Prop := ∃ m, n = 2 * m

def prime (n : Nat) : Prop := ∀ m, (∃ x, n = m * x) → m = 1 ∨ m = n

def infinitely_many_primes : Prop := ∀ N, ∃ p, p > N ∧ prime p

def Fermat_prime (n : Nat) : Prop := prime n ∧ ∃ m : Nat, n = 2 ^ (2 ^ m) + 1

def infinitely_many_Fermat_primes : Prop := ∀ N, ∃ p, p > N ∧ Fermat_prime p

def goldbach_conjecture : Prop := 
  ∀ n, (n > 2) → (even n) → ∃ x y, prime x ∧ prime y ∧ n = x + y 

def Goldbach's_weak_conjecture : Prop := 
  ∀ n, (n > 5) → (¬even n) → ∃ x y z, prime x ∧ prime y ∧ prime z ∧ n = x + y + z

def Fermat's_last_theorem : Prop :=
  ∀ a b c n : Nat, n > 2 → ¬(a ^ n + b ^ n = c ^ n)

end

-- 5
section 

open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r := 
  fun ⟨x, hr⟩ => hr

example (a : α) : r → (∃ x : α, r) := 
  fun hr => ⟨a, hr⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := 
  ⟨fun ⟨x, hp, hr⟩ => ⟨⟨x, hp⟩, hr⟩, fun ⟨⟨x, hp⟩, hr⟩ => ⟨x, hp, hr⟩⟩

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := 
  ⟨fun ⟨x, h⟩ => h.elim (fun hp => Or.inl ⟨x, hp⟩) (fun hq => Or.inr ⟨x, hq⟩), 
   fun h => h.elim (fun ⟨x, hp⟩ => ⟨x, Or.inl hp⟩) (fun ⟨x, hq⟩ => ⟨x, Or.inr hq⟩)⟩


example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := 
  ⟨fun h₁ => fun h₂ => let ⟨x, hp⟩ := h₂; hp (h₁ x), 
   fun h₁ => fun x => byContradiction fun h₂ => h₁ ⟨x, h₂⟩⟩

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := 
  ⟨fun ⟨x, h₁⟩ => fun h₂ => absurd h₁ (h₂ x), 
   fun h₁ => byContradiction fun h₂ => 
   have h₃ : ∀ (x : α), ¬p x := fun x => fun h₄ => h₂ ⟨x, h₄⟩; h₁ h₃⟩

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := 
  ⟨fun h₁ => fun x => fun h₂ => h₁ ⟨x, h₂⟩, fun h₁ => fun h₂ => 
    let ⟨x, h₃⟩ := h₂; h₁ x h₃⟩

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := 
  ⟨fun h₁ => byContradiction fun h₂ => 
    have h₃ : ∀ x, p x := fun x => byContradiction fun h₄ => h₂ ⟨x, h₄⟩; h₁ h₃, 
  fun h₁ => fun h₂ => let ⟨x, h₃⟩ := h₁; h₃ (h₂ x)⟩


example : (∀ x, p x → r) ↔ (∃ x, p x) → r := 
  ⟨fun h₁ => fun ⟨x, h₂⟩ => h₁ x h₂, fun h => fun x => fun h₂ => h ⟨x, h₂⟩⟩

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := 
  ⟨fun ⟨x, h₁⟩ => fun h₂ => h₁ (h₂ x), fun h₁ => byContradiction fun h₂ => 
    have h₃ : ∀ x, p x := fun x => byContradiction fun h₄ => h₂ ⟨x, fun h₅ => absurd h₅ h₄⟩; 
    h₂ ⟨a, fun h₄ => h₁ h₃⟩⟩

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := 
  ⟨fun ⟨x, h₁⟩ => fun h₂ => ⟨x, h₁ h₂⟩, 
    fun h₁ => byContradiction fun h₂ => 
    have h₃ : ∀ x : α , r := fun x => byContradiction fun h₅ => h₂ ⟨x, fun h₆ => absurd h₆ h₅⟩;
    let ⟨x, h₄⟩ := h₁ (h₃ a); h₂ ⟨x, fun h₅ => h₄⟩⟩

end
