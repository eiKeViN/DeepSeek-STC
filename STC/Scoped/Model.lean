module

/-!
# Typed realm model and realm references

The ADR-10 scoped-coeffect model layer.  A `RealmModel` relates physical realm
tokens to logical keys through an explicit `keyOf`, with a total default realm
per key.  A `RealmRef` packages a physical token with the witness that its
model key is the logical key, so dependent values are transported only through
that visible proof: there is no unchecked cast from `V (keyOf token)` to `V k`.

This module carries no store, resolver, or context machinery; it is the shared
typed foundation of the `STC.Scoped` family.

## Main declarations

* `RealmModel`: logical keys, physical realms, `keyOf`, and total defaults;
* `RealmRef`: a physical token plus its `keyOf` preservation witness;
* `RealmRef.cast`, `RealmRef.castInv`, `RealmRef.defaultRef`;
* `RealmRef.ext`: references agree exactly when their tokens agree;
* `cast_castInv`, `castInv_cast`: the checked transport round-trips;
* `ToyKey`/`ToyValue`/`ToyRealm`/`toyModel`: a finite model with two logical
  keys and two distinct realms under one key.
-/

universe u v w

namespace STC.Scoped

@[expose] public section

/-! ### Realm model -/

section RealmModel

variable {K : Type u} {V : K → Type v}

/-- A model relates physical realm tokens to logical keys, with a total default per key. -/
structure RealmModel (K : Type u) (V : K → Type v) where
  Realm : Type w
  keyOf : Realm → K
  default : (k : K) → Realm
  default_key : ∀ k, keyOf (default k) = k

end RealmModel

/-! ### Realm references and dependent transport -/

section RealmRef

variable {K : Type u} {V : K → Type v}
variable {M : RealmModel K V} {k : K}

/-- A resolved realm carries the equality needed to transport dependent values. -/
structure RealmRef (M : RealmModel K V) (k : K) where
  token : M.Realm
  key_eq : M.keyOf token = k

namespace RealmRef

/-- Transport a value from the physical key of a token to its logical key. -/
def cast (r : RealmRef M k) : V (M.keyOf r.token) → V k :=
  fun value => Eq.mp (congrArg V r.key_eq) value

/-- Transport a logical value back to the physical value type of a token. -/
def castInv (r : RealmRef M k) : V k → V (M.keyOf r.token) :=
  fun value => Eq.mpr (congrArg V r.key_eq) value

/-- The model-provided default reference for a logical key. -/
def defaultRef (M : RealmModel K V) (k : K) : RealmRef M k :=
  { token := M.default k
    key_eq := M.default_key k }

/-- References agree exactly when their physical tokens agree; the witnesses are proofs. -/
theorem ext {r r' : RealmRef M k} (h : r.token = r'.token) : r = r' := by
  cases r
  cases r'
  subst h
  rfl

/-- Casting back and forth along the same witness is the identity on `V k`. -/
theorem cast_castInv (r : RealmRef M k) (v : V k) : r.cast (r.castInv v) = v := by
  cases r with
  | mk token key_eq =>
    cases key_eq
    rfl

/-- Casting forth and back along the same witness is the identity on the physical type. -/
theorem castInv_cast (r : RealmRef M k) (v : V (M.keyOf r.token)) : r.castInv (r.cast v) = v := by
  cases r with
  | mk token key_eq =>
    cases key_eq
    rfl

/-- The default reference's physical token is the model's default realm. -/
theorem defaultRef_token (M : RealmModel K V) (k : K) : (defaultRef M k).token = M.default k :=
  rfl

/-- Casting along the default reference is exactly transport along the model's default law. -/
theorem cast_defaultRef (M : RealmModel K V) (k : K) :
    (defaultRef M k).cast = Eq.mp (congrArg V (M.default_key k)) :=
  rfl

/-- Casting backward along the default reference is exactly transport along the default law. -/
theorem castInv_defaultRef (M : RealmModel K V) (k : K) :
    (defaultRef M k).castInv = Eq.mpr (congrArg V (M.default_key k)) :=
  rfl

end RealmRef

end RealmRef

/-! ### Finite toy model -/

section Toy

/-- Two logical keys for the finite realm toy. -/
inductive ToyKey : Type
  | dep
  | cache
  deriving DecidableEq, Repr

/-- A genuinely dependent toy value family: `Nat` for `dep`, `Bool` for `cache`. -/
abbrev ToyValue : ToyKey → Type
  | .dep => Nat
  | .cache => Bool

/-- Three physical realms; `depA` and `depB` both back the `dep` key. -/
inductive ToyRealm : Type
  | depA
  | depB
  | cacheR
  deriving DecidableEq, Repr

/-- The finite toy model: one key has two realms, the other a single default realm. -/
abbrev toyModel : RealmModel ToyKey ToyValue where
  Realm := ToyRealm
  keyOf
    | .depA => .dep
    | .depB => .dep
    | .cacheR => .cache
  default
    | .dep => .depA
    | .cache => .cacheR
  default_key := by
    intro k
    cases k <;> rfl

/-- The default reference for `dep` resolves to the `depA` realm. -/
def toyDepARef : RealmRef toyModel .dep :=
  RealmRef.defaultRef toyModel .dep

/-- A non-default reference for `dep` resolving to the `depB` realm. -/
def toyDepBRef : RealmRef toyModel .dep :=
  { token := .depB
    key_eq := rfl }

/-- Two realms under one logical key remain distinct physical tokens. -/
theorem toy_same_key_realms_distinct :
    toyDepARef.token ≠ toyDepBRef.token := by
  intro h
  cases h

/-- The toy model does not collapse: `dep` and `cache` are distinct logical keys. -/
theorem toy_keys_distinct : .dep ≠ (.cache : ToyKey) := by
  decide

/-- The toy value family is genuinely dependent: `dep` carries `Nat`, not `Bool`. -/
theorem toy_value_dep : ToyValue .dep = Nat := rfl

end Toy

end

end STC.Scoped
