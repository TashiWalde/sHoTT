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

# Rules for directed contexts
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

## Structural rules
These are the variable, weakening and substitution rule, but the latter two are admissible. Hence, only the first rule is implemented.

```rzk
#def weak-DVar
  ( Γ : DCtx)
  ( A : DType Γ)
  : DType (DCtx-ext Γ A)
  := independent-family Γ A A

#def DVar
  ( Γ : DCtx)
  ( A : DType Γ)
  ( Λ : DType (DCtx-ext Γ A))
  : DType (DCtx-ext (DCtx-ext Γ A) Λ)
  := independent-family (DCtx-ext Γ A) Λ (weak-DVar Γ A)
```

## Σ-types

```rzk
#def DΣ
  ( Γ : DCtx)
  ( A : DType Γ)
  ( B : DType (DCtx-ext Γ A))
  : DType Γ
  := comp-IsoType Γ A B

-- #def DΣ-intro
--   ( Γ : DCtx)
--   ( A : DType Γ)
--   ( B : DType (DCtx-ext Γ A))

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
