# Directed type theory

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Directed contexts and types

We have a type (in the ambient type theory) `DCtx`
of **directed contexts** (= absolute directed types)
For each `Γ : DCtx` we have a type `DType Γ` of **dependent types in context** `A`.

In our implementation these are just wrappers around `Rezk` and `IsoType`,
respectively.

```rzk
#def DCtx : U
  := Rezk

#def type-DCtx
  : DCtx → U
  := type-Rezk

#def DType
  ( Γ : DCtx)
  : U
  := IsoType Γ
```

Note that a term of type `A : DType Γ` is more than just a family `A : Γ₀ → DCtx`
(where `Γ₀` denotes the underlying type of `Γ` in the ambient type theory).

```rzk
#def DCtx-family-DType
  ( Γ : DCtx)
  ( A : DType Γ)
  : type-DCtx Γ → DCtx
  := rezk-family-IsoType Γ A
```

## Sigma types

We have context extensions and sigma types.

```rzk
#def DCtx-extension
  ( Γ : DCtx)
  : DType Γ → DCtx
  := rezk-total-IsoType Γ

#def DΣ
  ( Γ : DCtx)
  ( A : DType Γ)
  : DType (DCtx-extension Γ A) → DType Γ
  := comp-IsoType Γ A
```
