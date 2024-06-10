# Directed type theory

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Directed contexts and dependent directed types

We have a type (in the ambient type theory) `DCtx` of **directed contexts** (=
absolute directed types) For each `Γ : DCtx` we have a type `DType Γ` of
**dependent types in context** `A`.

In our implementation these are just wrappers around `Rezk` and `IsoType`,
respectively.

```rzk
#def DCtx
  : U
  := Rezk

#def type-DCtx
  : DCtx → U
  := type-Rezk

#def DType
  ( Γ : DCtx)
  : U
  := IsoType Γ

#def family-DType
  ( Γ : DCtx)
  ( A : DType Γ)
  : type-DCtx Γ → U
  := family-IsoType Γ A
```
Each fiber of a dependent directed type is again a directed type.

```rzk
#def DCtx-family-DType
  ( Γ : DCtx)
  ( A : DType Γ)
  : type-DCtx Γ → DCtx
  := rezk-family-IsoType Γ A
```

## Rules for directed contexts
These are the existence of the empty context, which corresponds to the unit type, and context extension.

```rzk
#def DUnit
  : DCtx
  := (Unit , is-rezk-Unit extext)

#def DCtx-ext
  ( Γ : DCtx)
  : DType Γ → DCtx
  := rezk-total-IsoType Γ
```

## Typing terms
```rzk
-- Does this name makes sense???
#def DTerm
  ( Γ : DCtx)
  ( A : DType Γ)
  : U
  := (γ : type-DCtx Γ) → family-DType Γ A γ
```

## Structural rules
These are the variable, substitution and weakening rule, but the latter two are admissible. Hence, only the first rule is implemented. See A.2.2 in the HoTT Book.

### Variable rule
TODO Prove that weak-DVar is (equivalent to) a special of DVar.
```rzk
-- Here, the key ingredient is that A is a type in the extended context.
#def weak-DVar
  ( Γ : DCtx)
  ( A : DType Γ)
  : DTerm (DCtx-ext Γ A) (independent-family Γ A A)
  := \ (γ , a) → a

#def DVar
  ( Γ : DCtx)
  ( A : DType Γ)
  ( Λ : DType (DCtx-ext Γ A))
  : DTerm
    ( DCtx-ext (DCtx-ext Γ A) Λ)
    ( independent-family (DCtx-ext Γ A) Λ (independent-family Γ A A))
  := \ ((γ , a) , λ) → a
```

### Substitution rule
```rzk
#def DSub
  ( Γ : DCtx)
  ( A : DType Γ)
  ( a : DTerm Γ A)
  ( Λ : DType (DCtx-ext Γ A))
  ( B : DType (DCtx-ext (DCtx-ext Γ A) Λ))
  ( b : DTerm (DCtx-ext (DCtx-ext Γ A) Λ) B)
  : DTerm (DCtx-ext Γ (comp-IsoType Γ A Λ)) ()
  -- We need here something like associativity of composing IsoType!
```

### Weakening rule
```rzk
-- This does not type check yet because there is no proof that (independent-family Γ A Λ) and (independent-family Γ Λ A) are equivalent in context Γ.
#postulate DWkn
  ( Γ : DCtx)
  ( A Λ : DType Γ)
  ( B : DType (DCtx-ext Γ Λ))
  ( b : DTerm (DCtx-ext Γ Λ) B)
  : DTerm
    ( DCtx-ext (DCtx-ext Γ A) (independent-family Γ A Λ))
    ( independent-family (DCtx-ext Γ Λ) (independent-family Γ Λ A) B)
```

## Σ-types
See A.2.5 in the HoTT Book.

```rzk
#def DΣ
  ( Γ : DCtx)
  ( A : DType Γ)
  ( B : DType (DCtx-ext Γ A))
  : DType Γ
  := comp-IsoType Γ A B
```

TODO Implement substitution and weakening rule because they are used implicitly here!
```rzk
#def DΣ-intro
  ( Γ : DCtx)
  ( A : DType Γ)
  ( B : DType (DCtx-ext Γ A))
  ( a : (γ : type-DCtx Γ) → family-DType Γ A γ)
  ( b : (γ : type-DCtx Γ) → family-DType (DCtx-ext Γ A) B (γ , a γ))
  : ( γ : type-DCtx Γ) → family-DType Γ (DΣ Γ A B) γ
  := \ γ → (a γ , b γ)
```

TODO Write wrappers for first and second.
```rzk
-- Check the formatting.
#def DΣ-elim
  ( Γ : DCtx)
  ( A : DType Γ)
  ( B : DType (DCtx-ext Γ A))
  ( C : DType (DCtx-ext (DCtx-ext Γ A) B))
  ( g :
    ( ( ( γ , a) , b) : type-DCtx (DCtx-ext (DCtx-ext Γ A) B))
    → ( family-DType (DCtx-ext (DCtx-ext Γ A) B) C ((γ , a) , b)))
  ( p :
    ( γ' : type-DCtx Γ)
    → ( family-DType Γ (DΣ Γ A B) γ'))
  : ( γ'' : type-DCtx Γ)
    → ( family-DType (DCtx-ext (DCtx-ext Γ A) B) C ((γ'' , first (p γ'')) , second (p γ'')))
  := \ γ'' → g ((γ'' , first (p γ'')) , second (p γ''))

#def DΣ-comp
  ( Γ : DCtx)
  ( A : DType Γ)
  ( B : DType (DCtx-ext Γ A))
  ( C : DType (DCtx-ext (DCtx-ext Γ A) B))
  ( g :
    ( ( ( γ , a) , b) : type-DCtx (DCtx-ext (DCtx-ext Γ A) B))
    → ( family-DType (DCtx-ext (DCtx-ext Γ A) B) C ((γ , a) , b)))
  ( a : (γ : type-DCtx Γ) → family-DType Γ A γ)
  ( b : (γ : type-DCtx Γ) → family-DType (DCtx-ext Γ A) B (γ , a γ))
  : ( γ : type-DCtx Γ)
  → ( DΣ-elim Γ A B C g (DΣ-intro Γ A B a b) γ) =_{family-DType (DCtx-ext (DCtx-ext Γ A) B) C ((γ , a γ) , b γ)} g ((γ , a γ) , b γ)
  := \ γ → refl_{g ((γ , a γ) , b γ) : family-DType (DCtx-ext (DCtx-ext Γ A) B) C ((γ , a γ) , b γ)}

-- #def Dproduct
--   ( Γ : DCtx)
--   ( A B : DType Γ)
--   : DCtx
```

## Groupoids

```rzk

#def DGrpd
  ( Γ : DCtx)
  : U
  :=
  Σ ( A : DType Γ)
  , ( ( x : type-DCtx Γ) → is-discrete (type-DCtx ((DCtx-family-DType Γ A) x)))

#def GrpdCtx
  : U
  := Σ (Γ : U) , is-discrete Γ

#def type-GrpdCtx
  ( ( Γ , is-discrete-Γ) : GrpdCtx)
  : U
  := Γ

#def is-discrete-GrpdCtx
  ( ( Γ , is-discrete-Γ) : GrpdCtx)
  : is-discrete Γ
  := is-discrete-Γ

#def DCtx-GrpdCtx
  ( ( Γ , is-discrete-Γ) : GrpdCtx)
  : DCtx
  := (Γ , is-rezk-is-discrete extext Γ is-discrete-Γ)

#def DType-GrpdCtx
  ( Γ : GrpdCtx)
  : U
  := DType (DCtx-GrpdCtx Γ)
```

## Pi types

```rzk
#def type-DΠ-GrpdCtx
  ( Γ : GrpdCtx)
  ( A : DType-GrpdCtx Γ)
  ( B : DType (DCtx-ext (DCtx-GrpdCtx Γ) A))
  : ( type-GrpdCtx Γ) → U
  := Π-type
    ( type-GrpdCtx Γ)
    ( family-IsoType (DCtx-GrpdCtx Γ) A)
    ( family-IsoType (DCtx-ext (DCtx-GrpdCtx Γ) A) B)

#def is-rezk-DΠ-GrpdCtx
  ( Γ : GrpdCtx)
  ( A : DType-GrpdCtx Γ)
  ( B : DType (DCtx-ext (DCtx-GrpdCtx Γ) A))
  : is-rezk (total-type (type-GrpdCtx Γ) (type-DΠ-GrpdCtx Γ A B))
  := is-rezk-Π-type-are-rezk-total-types-is-discrete
    ( type-GrpdCtx Γ) (is-discrete-GrpdCtx Γ) A B

#def DΠ-GrpdCtx
  ( Γ : GrpdCtx)
  ( A : DType-GrpdCtx Γ)
  ( B : DType (DCtx-ext (DCtx-GrpdCtx Γ) A))
  : DType-GrpdCtx Γ
  := (type-DΠ-GrpdCtx Γ A B , is-rezk-DΠ-GrpdCtx Γ A B)
```
