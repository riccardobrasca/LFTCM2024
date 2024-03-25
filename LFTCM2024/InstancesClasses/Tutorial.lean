import LFTCM2024.Common

open BigOperators Finset Real
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

section

/- Given a point, we get access to its coordinates / projections. -/
variable (a : Point)
#check Point.x a
#check a.x
#check a.y
#check a.z

end





/- We can prove that two points are equal using the `ext` tactic. -/

example (a b : Point) (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) :
    a = b := by
  ext
  all_goals assumption

example (a b : Point) (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) :
  a = b := by ext <;> assumption


/- There are multiple ways to define a point (or more generally an instance of a structure).

Tip: if you write `_` for a Point, a lightbulb 💡 will appear.
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



namespace Point

/- We can define operations on points, like addition. -/

def add (a b : Point) : Point :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

def add' : Point → Point → Point :=
  fun ⟨ux, uy, uz⟩ ⟨vx, vy, vz⟩ ↦ ⟨ux + vx, uy + vy, uz + vz⟩

/- We define these operations in `namespace Point`. This means that if this namespace is open
we can write `add p q`, but if the namespace isn't open, we have to write `Point.add p q`.
In either case, we can use the *projection notation*, `p.add q` where `p q : Point`.
Lean knows that we mean the function `Point.add`, since the type of `p` is `Point`. -/

#check add myPoint1 myPoint2
#check myPoint1.add myPoint2

end Point

#check Point.add myPoint1 myPoint2
#check myPoint1.add myPoint2

open Point

#check add myPoint1 myPoint2


namespace Point

/- We can prove properties about points. `protected` in the line below means that
even in the namespace `Point` we still have to write `Point.add_commutative` -/

protected lemma add_commutative (a b : Point) : add a b = add b a := by simp [add, add_comm]

#check Point.add_commutative

/- We can also state that we want to use the `+` notation here.
In that case, we have to write lemmas stating how `+` computes. -/

instance : Add Point := ⟨add⟩

@[simp] lemma add_x (a b : Point) : (a + b).x = a.x + b.x := by rfl
@[simp] lemma add_y (a b : Point) : (a + b).y = a.y + b.y := by rfl
@[simp] lemma add_z (a b : Point) : (a + b).z = a.z + b.z := by rfl

example (a b : Point) : a + b = b + a := by ext <;> simp [add_comm]

end Point





/- We can bundle properties in structures -/

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

/- Going from `Point` to `PosPoint` has code duplication.
We don't want this when defining monoids, groups, rings, fields. -/

structure PosPoint' extends Point where
  x_pos : 0 < x
  y_pos : 0 < y
  z_pos : 0 < z

def PointPoint'.add (a b : PosPoint') : PosPoint' :=
{ a.toPoint + b.toPoint with
  x_pos := by dsimp; linarith [a.x_pos, b.x_pos]
  y_pos := by dsimp; linarith [a.y_pos, b.y_pos]
  z_pos := by dsimp; linarith [a.z_pos, b.z_pos] }

/- We could also define a type like this using a subtype. The notation is `{x : α // p x}`
(not to be confused with the notation `{x : α | p x}` to define a set). -/

def PosReal : Type :=
  { x : ℝ // x > 0 }

/- Elements here are pairs of
  (1) a real number
  (2) a proof that this real number is postive. -/

example (x : ℝ) (hx : x > 0) : PosReal := ⟨x, hx⟩

example (x : PosReal) : x.1 > 0 := x.2






/- Structures can have parameters -/

@[ext] structure Triple (α : Type*) where
  x : α
  y : α
  z : α

#check Triple.mk 1 2 3

#check Triple.mk sin cos tan




/- # Abelian groups

Let's define abelian groups.
We say that a type `G` has the structure of an abelian group
if there are `add`, `zero`, `neg`, with some axioms.

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

/-
example (x y : MyIntegers) : MyIntegers := x + y -- error
-/

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

#check AbelianGroup.add

instance AbelianGroup.prod (G G' : Type*) [AbelianGroup G] [AbelianGroup G'] :
    AbelianGroup (G × G') where
  add := fun a b ↦ (a.1 + b.1, a.2 + b.2)
  zero := (0, 0)
  neg := fun a ↦ (- a.1, - a.2)
  comm := by intros; ext <;> exact?
  assoc := by intros; ext <;> exact?
  add_zero := by intros; ext <;> exact?
  add_neg := by intros; ext <;> exact?


variable (x y z : MyIntegers) in
#check (x, y) + (z, x)




/- In mathlib, there are two notions of abelian groups,
one written using `(*, 1, ⁻¹)` and one using `(+, 0, -)`. -/

#check CommGroup
#check AddCommGroup


/- To explain this distinction, consider monoids (groups without inverses).
`(ℝ, +, 0)` and `(ℝ, *, 1)` are both monoids, and we want to have a distinction in notation and
lemma names of these two structures. -/

example : Monoid ℝ := by infer_instance
example : AddMonoid ℝ := by infer_instance
example (x : ℝ) : x + 0 = x := add_zero x
example (x : ℝ) : x * 1 = x := mul_one x

#check Monoid
#check AddMonoid







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


/- 5. Show that if `G` is an abelian group then triples from elements of `G` is an abelian group. -/

example (G : Type*) [AbelianGroup G] : AbelianGroup (Triple G) := sorry














/- ## Coercions

You can specify *coercions* to say that an element of one type can be silently coerced to an element
of another type. We've already seen the coercions
`ℕ → ℤ → ℚ → ℝ → ℂ`
for numbers.
-/

recall PosReal := {x : ℝ // x > 0}

instance : Coe PosReal Real := ⟨fun x ↦ x.1⟩

def diff (x y : PosReal) : ℝ := x - y

#check fun (x : PosReal) ↦ (x : ℂ)




/-
* We use `CoeSort` to coerce to `Type _` (or `Sort _`)
* We use `CoeFun` to coerce to functions.
-/
structure PointedType where
  carrier : Type*
  pt : carrier

instance : CoeSort PointedType Type* := ⟨fun α ↦ α.carrier⟩

structure PointedFunction (X Y : PointedType) where
  toFun : X → Y
  toFun_pt : toFun X.pt = Y.pt

infix:50 " →. " => PointedFunction

instance {X Y : PointedType} : CoeFun (X →. Y) (fun _ ↦ X → Y) := ⟨fun e ↦ e.toFun⟩

-- these two are hints to the pretty printer to print these operations a bit nicer.
attribute [pp_dot] PointedType.pt
attribute [coe] PointedFunction.toFun

namespace PointedFunction

variable {X Y Z : PointedType}

@[simp] lemma coe_pt (f : X →. Y) : f X.pt = Y.pt := f.toFun_pt

lemma comp (g : Y →. Z) (f : X →. Y) : X →. Z :=
{ toFun := g ∘ f
  toFun_pt := by sorry }

end PointedFunction
