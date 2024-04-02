import LFTCM2024.Common
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

attribute [-instance] Prod.instAdd
open BigOperators Finset Real MeasureTheory ENNReal
noncomputable section
set_option linter.unusedVariables false
set_option autoImplicit false


/- # Instances and Classes -/

/-
## Structures

Learning about structures is the next step towards doing sophisticated mathematics.

Structures are used to build data and properties together.
For example in the structure below `Point` bundles three coordinates together.
-/

@[ext]
structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

#check Point


/- **Projections**: Given a point, we get access to its coordinates / projections. -/
variable (a : Point)
#check Point.x a
#check a.x
#check a.y
#check a.z


/- **Constructors**: There are multiple ways to define a point.

Tip: if you write `_` or `sorry` as the definition of a Point, a blue lightbulb will appear.
Clicking it will give you the skeleton -/

def myPoint1 : Point where
  x := 1
  y := 2
  z := 3

def myPoint2 :=
  { x := 1, y := 2, z := 3 : Point }

def myPoint3 : Point :=
  { x := 1
    y := 2
    z := 3 }

def myPoint4 : Point := ⟨1, 2, 3⟩

def myPoint5 := Point.mk 1 2 3




/- **Proving equality**:
We can prove that two points are equal using the `ext` tactic. -/

example (a b : Point) (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) :
    a = b := by
  ext
  all_goals assumption

example (a b : Point) (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) :
  a = b := by ext <;> assumption




namespace Point

/- **Operations**
We can define operations on points, like addition. -/

def add (a b : Point) : Point :=
  { x := a.x + b.x, y := a.y + b.y, z := a.z + b.z }

def add' : Point → Point → Point :=
  fun ⟨ux, uy, uz⟩ ⟨vx, vy, vz⟩ ↦ ⟨ux + vx, uy + vy, uz + vz⟩

/-
**Projection Notation**
We define these operations in `namespace Point`.
This means that if this namespace is open we can write `add p q`,
but if the namespace isn't open, we have to write `Point.add p q`.
In either case, we can use the *projection notation*, `p.add q`
where `p q : Point`.
Lean knows that we mean the function `Point.add`,
by looking at the type of `p`, which is `Point`. -/

#check add myPoint1 myPoint2
#check myPoint1.add myPoint2

end Point

#check Point.add myPoint1 myPoint2
#check myPoint1.add myPoint2

open Point

#check add myPoint1 myPoint2


namespace Point

/- We can prove properties about points.
`protected` means that even in the namespace `Point`
we still have to write `Point.add_commutative` -/

protected lemma add_commutative (a b : Point) : add a b = add b a := by
  simp_rw [add, add_comm]

#check Point.add_commutative

/- We can also state that we want to use the `+` notation here.
In that case, we have to write lemmas stating how `+` computes. -/

instance : Add Point := ⟨add⟩

@[simp] lemma add_x (a b : Point) : (a + b).x = a.x + b.x := by rfl
@[simp] lemma add_y (a b : Point) : (a + b).y = a.y + b.y := by rfl
@[simp] lemma add_z (a b : Point) : (a + b).z = a.z + b.z := by rfl

example (a b : Point) : a + b = b + a := by ext <;> simp [add_comm]

end Point





/- ### Structures with properties -/

structure PosPoint where
  x : ℝ
  y : ℝ
  z : ℝ
  x_pos : 0 < x
  y_pos : 0 < y
  z_pos : 0 < z

def PointPoint.add (a b : PosPoint) : PosPoint :=
{ x := a.x + b.x
  y := a.y + b.y
  z := a.z + b.z
  x_pos := by linarith [a.x_pos, b.x_pos]
  y_pos := by linarith [a.y_pos, b.y_pos]
  z_pos := by linarith [a.z_pos, b.z_pos] }

/- **extends**:
We can use the `extends` keyword to remove some code duplication. -/

structure PosPoint' extends Point where
  x_pos : 0 < x
  y_pos : 0 < y
  z_pos : 0 < z

def PointPoint'.add (a b : PosPoint') : PosPoint' :=
{ a.toPoint + b.toPoint with
  x_pos := by dsimp; linarith [a.x_pos, b.x_pos]
  y_pos := by dsimp; linarith [a.y_pos, b.y_pos]
  z_pos := by dsimp; linarith [a.z_pos, b.z_pos] }

/- **subtypes**
For simple types we can use subtype. The notation is `{x : α // p x}`.
This consists of pairs `⟨x, h⟩` where `x : α` and `h : p x`.
Note: there is similar notation `{x : α | p x}` to define an element of `Set α`. -/

def PosReal : Type :=
  { x : ℝ // x > 0 }

/- Elements here are pairs of
  (1) a real number
  (2) a proof that this real number is positive. -/

example (x : ℝ) (hx : x > 0) : PosReal := ⟨x, hx⟩

example (x : PosReal) : x.1 > 0 := x.2






/- ### Structures with parameters -/

@[ext] structure Triple (α : Type*) where
  x : α
  y : α
  z : α

#check Triple.mk 1 2 3

#check Triple.mk sin cos tan




/- # First introduction to classes: Abelian groups

Let's define abelian groups.
We say that a type `G` has the structure of an abelian group
if it has an addition, a zero and a negation with the usual group axioms.

We write it as a *class*, and for specific abelian groups we write
*instance* instead of *def*.
-/

class AbelianGroup (G : Type*) where
  add (x : G) (y : G) : G
  zero : G
  neg (x : G) : G
  comm (x y : G) : add x y = add y x
  assoc (x y z : G) : add (add x y) z = add x (add y z)
  add_zero : ∀ x : G, add x zero = x
  add_neg : ∀ x : G, add x (neg x) = zero

def MyIntegers := ℤ

example (x y : MyIntegers) : MyIntegers := x + y -- error


instance IntGroup : AbelianGroup MyIntegers := by
  unfold MyIntegers
  exact
  { add := fun a b ↦ a + b
    comm := add_comm
    assoc := add_assoc
    zero := 0
    add_zero := by simp
    neg := fun a ↦ -a
    add_neg := by simp }


/-
Using `class` + `instance` tells Lean to make a database of abelian groups.
If you write a lemma with argument `[AbelianGroup G]`
("instance-implicit arguments"),
When applying such a lemma, Lean will search
through in this database to fill this argument.
-/

/- The following lines say that we want to use the
notation `+`, `0`, and `-` for abelian groups. -/

instance {G : Type*} [AbelianGroup G] : Add G := ⟨AbelianGroup.add⟩
instance {G : Type*} [AbelianGroup G] : Zero G := ⟨AbelianGroup.zero⟩
instance {G : Type*} [AbelianGroup G] : Neg G := ⟨AbelianGroup.neg⟩

/- Note that we write `{G : Type*} [AbelianGroup G]`
to say "let G be an abelian group".
So **not** `(G : AbelianGroup)` -/

lemma my_add_comm {G : Type*} [AbelianGroup G] (x y : G) :
    x + y = y + x := AbelianGroup.comm x y
lemma my_add_assoc {G : Type*} [AbelianGroup G] (x y z : G) :
    (x + y) + z = x + (y + z) := AbelianGroup.assoc x y z
lemma my_add_zero {G : Type*} [AbelianGroup G] (x : G) :
    x + 0 = x := AbelianGroup.add_zero x
lemma my_add_neg {G : Type*} [AbelianGroup G] (x : G) :
    x + -x = 0 := AbelianGroup.add_neg x

lemma zero_unique {G : Type*} [AbelianGroup G] {z : G}
    (h : ∀ x, z + x = x) : z = 0 := by
  rw [← my_add_zero z, h]


/- Instances can be recursive and depend on other classes. -/

instance AbelianGroup.prod (G G' : Type*) [AbelianGroup G] [AbelianGroup G'] :
    AbelianGroup (G × G') where
  add := fun a b ↦ (a.1 + b.1, a.2 + b.2)
  zero := (0, 0)
  neg := fun a ↦ (- a.1, - a.2)
  comm := by intros; ext <;> exact?
  assoc := by intros; ext <;> exact?
  add_zero := by intros; ext <;> exact?
  add_neg := by intros; ext <;> exact?


/- If you want, you can ask Lean for a trace of the search it does to find an instance. -/

variable (x y z : MyIntegers) in
set_option trace.Meta.synthInstance true in
#check (x, y) + (z, x)



/- ## Overview of parentheses

We use `(...)` for explicit arguments and all other parenthesis for implicit arguments. -/

lemma lemma1 {G : Type*} [Group G] {x y : G} (h : x⁻¹ = y) : x * y = 1 :=
  mul_eq_one_iff_inv_eq.mpr h

lemma lemma2 {M : Type*} [OrderedAddCommMonoid M] (x : M) {y z : M} (h : y ≤ z) : x + y ≤ x + z :=
  add_le_add_left h x

/- A summary of parentheses around arguments:
* explicit argument (x : α)
  -> Use when you want to give `x` explicitly when applying your lemma
* implicit argument {x : α}
  -> Lean will figure out this implicit argument from the expected type and/or later arguments.
  -> Use when a later argument depends on this argument
* instance-implicit arguments [x : α]
  -> implicit argument filled by type class inference
  -> use this when `α` is a class
* arguments with default value (x : α := x₀)
  -> This is an optional argument. It is an explicit argument,
     but if you don't give it, `x₀` will be used automatically
* arguments with default tactic (x : α := by tac)
  -> This is an optional argument. It is an explicit argument,
     but if you don't give it, the tactic `tac` will be used automatically to find the argument.
* strict-implicit argument {{x : α}} / ⦃x : α⦄
  -> This is basically the same as {x : α}, just use that instead.
  -> (See bottom of this file to see how this differs from {x : α})

(there are some exceptions to these usage rules)
-/

def mySum (f : ℕ → ℕ) (stop : ℕ) (start : ℕ := 0) : ℕ :=
  ∑ i in Finset.Icc start stop, f i

#eval mySum (fun x ↦ x ^ 2) 5
#eval mySum (fun x ↦ x ^ 2) 5 3

lemma lemma3 (X : Type*) [MeasurableSpace X] (μ : Measure X := by volume_tac) : μ ∅ = 0 :=
  measure_empty

#check lemma3 ℝ -- volume is used for `μ`
#check lemma3 ℝ ((2 : ℝ≥0∞) • volume) -- I provide a measure manually





/- ## Short overview of classes in Lean -/

/- In mathlib, there are two notions of abelian groups,
one written using `(*, 1, ⁻¹)` and one using `(+, 0, -)`. -/

example {G : Type*} [CommGroup G] (x y z : G) : x⁻¹ * y = z ↔ y = x * z :=
  inv_mul_eq_iff_eq_mul

example {G : Type*} [AddCommGroup G] (x y z : G) : -x + y = z ↔ y = x + z :=
  neg_add_eq_iff_eq_add


/- To explain this distinction, consider monoids (groups without inverses).
`(ℝ, +, 0)` and `(ℝ, *, 1)` are both monoids,
and we want to have a distinction in notation and
lemma names of these two structures. -/

example : Monoid ℝ := by infer_instance
example : AddMonoid ℝ := by infer_instance
example (x : ℝ) : x + 0 = x := add_zero x
example (x : ℝ) : x * 1 = x := mul_one x


/- We have many algebraic classes that you will be familiar with -/

#check Ring
#check CommRing
#check EuclideanDomain
#check Field

/- We also have classes are properties on an existing class,
so you have to write multiple classes to specify them.
-/
#check IsDomain
#check IsDedekindDomain
#check UniqueFactorizationMonoid
#check IsPrincipalIdealRing

example {R : Type*} [Ring R] [IsDomain R] (x y : R) :
    x * y = 0 ↔ x = 0 ∨ y = 0 := mul_eq_zero

/- and we use classes for much more than algebraic objects -/

#check TopologicalSpace
#check NormedAddCommGroup
#check MeasureSpace

/- Some classes have more than one argument, like `Module`.
Notice that `Module` in the example below means "vector space". -/

example {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (v : V) :
  (1 : K) • v = v := by exact?




/- ## Exercises -/

/- 1. Define the structure of "strict bipointed types", i.e. a type together with 2 unequal points
`x₀ ≠ x₁` in it.
Then state and prove the lemma that for any object in this class we have `∀ z, z ≠ x₀ ∨ z ≠ x₁.` -/



/- 2. Define scalar multiplication of a real number and a `Point`.
Also define scalar multiplication of a positive real number and a `PosPoint`. -/



/- 3. Define Pythagorean triples, i.e. triples `a b c : ℕ` with `a^2 + b^2 = c^2`.
Give an example of a Pythagorean triple, and show that multiplying a Pythagorean triple by a
constant gives another Pythagorean triple. -/



/- 4. Prove that triples of equivalent types are equivalent.
`≃` is the type of equivalences / bijections between two types. -/

example (α β : Type*) (e : α ≃ β) : Triple α ≃ Triple β := sorry


/- 5. Show that if `G` is an abelian group then triples with elements of `G` is an abelian group. -/

example (G : Type*) [AbelianGroup G] : AbelianGroup (Triple G) := sorry






/- # Difference between {x : α} and {{x : α}}

Don't read this unless you really want to know, this is not important.

The only difference between `h : ∀ {x : α} (y : β), p x y` and `h : ∀ {{x : α}} (y : β), p x y`
is when you *don't* apply `h` to an argument.
If you apply `h` to `y : β`, then in both cases `h y` will be interpreted as `@h _ y`.
However, in the first case `h` (without application) will be the same as `@h _`,
and in the second case `h` will be `@h`. (Note that `@h` and `@h _` is the same in both cases)

As a quick rule: if a hypothesis to a lemma or the body of a definition starts with one or more implicit
quantifiers, followed by one or more explicit quantifiers, you want to make the implicit quantifier strict-implicit.
-/
variable {α β : Type*} {p : α → β → Prop} (h : ∀ {x : α} (y : β), p x y) (x : α) (y : β)
#check h y -- same as `@h _ y`
#check h (x := x) y -- same as `@h x y`
#check h -- same as `@h _`
#check @h
#check @h _

variable {α β : Type*} {p : α → β → Prop} (h : ∀ ⦃x : α⦄ (y : β), p x y) (x : α) (y : β)
#check h y -- same as `@h _ y`
#check h (x := x) y -- same as `@h x y`
#check h -- same as `@h`
#check @h
#check @h _

def injective1 {α β : Type*} (f : α → β) : Prop := ∀ {x y : α}, f x = f y → x = y
def injective2 {α β : Type*} (f : α → β) : Prop := ∀ ⦃x y : α⦄, f x = f y → x = y

variable {α : Type*} {f1 : α → α} (hf1 : injective1 f1) {f2 : α → α} (hf2 : injective2 f2)
#check hf1
#check hf2

lemma injective1.comp_self : injective1 (f1 ∘ f1) := fun {x y} hfxy ↦ hf1 (hf1 hfxy)
lemma injective2.comp_self : injective2 (f2 ∘ f2) := fun {x y} hfxy ↦ hf2 (hf2 hfxy)

/- The following lemmas show why ⦃x : α⦄ is more useful in this case. -/
lemma injective1.comp4_self : injective1 (f1 ∘ f1 ∘ f1 ∘ f1) := hf1.comp_self.comp_self -- error
lemma injective2.comp4_self : injective2 (f2 ∘ f2 ∘ f2 ∘ f2) := hf2.comp_self.comp_self -- fine
