variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  ⟨fun h : p ∧ q => ⟨h.right, h.left⟩, 
   fun h : q ∧ p => ⟨h.right, h.left⟩⟩

example : p ∨ q ↔ q ∨ p :=
  ⟨fun h : p ∨ q => h.elim (fun hp : p => Or.inr hp) (fun hq : q => Or.inl hq), 
   fun h : q ∨ p => h.elim (fun hq : q => Or.inr hq) (fun hp : p => Or.inl hp)⟩

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  ⟨fun h : (p ∧ q) ∧ r => ⟨h.left.left, h.left.right, h.right⟩, 
   fun h : p ∧ q ∧ r => ⟨⟨h.left, h.right.left⟩, h.right.right⟩⟩

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  ⟨fun h : (p ∨ q) ∨ r => h.elim 
    (fun h₁ : p ∨ q => h₁.elim (fun hp : p => Or.inl hp) (fun hq : q => Or.inr (Or.inl hq))) 
     fun hr : r => Or.inr (Or.inr hr), 
   fun h : p ∨ q ∨ r => h.elim 
    (fun hp : p => Or.inl (Or.inl hp)) 
     fun h₁ : q ∨ r => h₁.elim (fun hq : q => Or.inl (Or.inr hq)) (fun hr : r => Or.inr hr)⟩

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  ⟨fun h : p ∧ (q ∨ r) => h.right.elim 
    (fun hq : q => Or.inl ⟨h.left, hq⟩)
     fun hr : r => Or.inr ⟨h.left, hr⟩, 
   fun h : p ∧ q ∨ p ∧ r => h.elim 
    (fun hpq : p ∧ q => ⟨hpq.left, Or.inl hpq.right⟩) 
     fun hpr : p ∧ r => ⟨hpr.left, Or.inr hpr.right⟩⟩

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  ⟨fun h : p ∨ q ∧ r => h.elim 
    (fun hp : p => ⟨Or.inl hp, Or.inl hp⟩) 
     fun hqr : q ∧ r => ⟨Or.inr hqr.left, Or.inr hqr.right⟩, 
   fun h : (p ∨ q) ∧ (p ∨ r) => h.left.elim 
    (fun hp : p => Or.inl hp) 
     fun hq : q => h.right.elim (fun hp : p => Or.inl hp) (fun hr : r => Or.inr ⟨hq, hr⟩)⟩ 

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := 
  ⟨fun h : p → q → r => (fun hpq : p ∧ q => h hpq.left hpq.right), 
   fun h : p ∧ q → r => (fun hp : p => (fun hq : q => h ⟨hp, hq⟩))⟩ 

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  ⟨fun h : p ∨ q → r => ⟨fun hp : p => h (Or.inl hp), (fun hq : q => h (Or.inr hq))⟩, 
   fun h : (p → r) ∧ (q → r) => 
    (fun hpq : p ∨ q => hpq.elim (fun hp : p => h.left hp) (fun hq : q => h.right hq))⟩

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := 
  ⟨fun h : ¬(p ∨ q) => ⟨fun hp : p => h (Or.inl hp), (fun hq : q => h (Or.inr hq))⟩, 
   fun h : ¬p ∧ ¬q => (fun hpq : p ∨ q => hpq.elim h.left h.right)⟩

example : ¬p ∨ ¬q → ¬(p ∧ q) := 
  fun h : ¬p ∨ ¬q => fun hpq : p ∧ q => h.elim 
    (fun hnp : ¬p => hnp hpq.left) (fun hnq : ¬q => hnq hpq.right)

example : ¬(p ∧ ¬p) := 
  fun h : p ∧ ¬p => h.right h.left 

example : p ∧ ¬q → ¬(p → q) := 
  fun h : p ∧ ¬q => fun h₁ : p → q => h.right (h₁ h.left)

example : ¬p → (p → q) := 
  fun hnp : ¬p => fun hp : p => absurd hp hnp

example : (¬p ∨ q) → (p → q) := 
  fun h : ¬p ∨ q => fun hp : p => h.elim (fun hnp : ¬p => absurd hp hnp) id

example : p ∨ False ↔ p := 
  ⟨fun h : p ∨ False => h.elim id False.elim, fun hp : p => Or.inl hp⟩ 

example : p ∧ False ↔ False := 
  ⟨fun h : p ∧ False => h.right, False.elim⟩

example : (p → q) → (¬q → ¬p) := 
  fun h : p → q => fun hnq : ¬q => fun hp : p => hnq (h hp)


-- classical
open Classical

variable (p q r s : Prop)

example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := 
  fun h : p → r ∨ s => (em p).elim 
    (fun hp : p => (h hp).elim 
      (fun hr : r => Or.inl fun hpp : p => hr) (fun hs : s => Or.inr fun hpp : p => hs)) 
    (fun hnp : ¬p => Or.inl fun hp : p => absurd hp hnp)

example : ¬(p ∧ q) → ¬p ∨ ¬q := 
  fun h : ¬(p ∧ q) => (em p).elim 
    ((em q).elim (fun hq : q => fun hp : p => absurd ⟨hp, hq⟩ h) 
      (fun hnq : ¬q => fun hp : p => Or.inr hnq)) 
    (fun hnp : ¬p => Or.inl hnp)

example : ¬(p → q) → p ∧ ¬q :=
  fun h : ¬(p → q) => 
    ⟨(em p).elim id (fun hnp : ¬p => absurd (fun hp : p => absurd hp hnp) h), 
     (em q).elim (fun hq : q => absurd (fun hp : p => hq) h) id⟩

example : (p → q) → (¬p ∨ q) :=
  fun h : p → q => (em p).elim (fun hp : p => Or.inr (h hp)) (fun hnp : ¬p => Or.inl hnp)

example : (¬q → ¬p) → (p → q) :=
  fun h : ¬q → ¬p => fun hp : p => (em q).elim id (fun hnq : ¬q => absurd hp (h hnq))

example : p ∨ ¬p :=
  (em p).elim (fun hp : p => Or.inl hp) (fun hnp : ¬p => Or.inr hnp)

example : (((p → q) → p) → p) :=
  fun h : (p → q) → p => (em p).elim id (fun hnp : ¬p => 
    (em q).elim (fun hq : q => h fun hp : p => hq) 
    (fun hnq : ¬q => absurd (h fun hp : p => absurd hp hnp) hnp))


-- iff not self (not classical)
example : ¬(p ↔ ¬p) :=
  fun h : p ↔ ¬p => 
  have hnp : ¬p := fun hp : p => h.mp hp hp
  hnp (h.mpr hnp) 
