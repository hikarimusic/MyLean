 -- 1
 variable (α : Type) (p q : α → Prop)

 example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := 
  ⟨fun h => ⟨fun x => (h x).left, fun x => (h x).right⟩, 
   fun h => fun x => ⟨h.left x, h.right x⟩⟩

 example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := 
  fun h => fun h₁ => fun x => (h x) (h₁ x)

 example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := 
  fun h => fun x => h.elim (fun h₁ => Or.inl (h₁ x)) (fun h₁ => Or.inr (h₁ x))


-- 2
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

-- 3
variable (men : Type) (barber : men)
variable  (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := 
  have h₁ : shaves barber barber ↔ ¬ shaves barber barber := h barber
  have h₂ : ¬ shaves barber barber := fun h₃ => h₁.mp h₃ h₃
  h₂ (h₁.mpr h₂)

-- 4
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



