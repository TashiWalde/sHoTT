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

## Directed terms
```rzk
#def DTerm
  ( Γ : DCtx)
  ( A : DType Γ)
  : U
  := (γ : type-DCtx Γ) → family-DType Γ A γ

#def DTermEqu
  ( Γ : DCtx)
  ( A : DType Γ)
  ( a a' : DTerm Γ A)
  : U
  := (γ : type-DCtx Γ) → a γ =_{family-DType Γ A γ} a' γ

#def reflexivity-DTermEqu
  ( Γ : DCtx)
  ( A : DType Γ)
  ( a : DTerm Γ A)
  : DTermEqu Γ A a a
  := \ γ → refl_{a γ}

#def symmetry-DTermEqu
  ( Γ : DCtx)
  ( A : DType Γ)
  ( a b : DTerm Γ A)
  ( e : DTermEqu Γ A a b)
  : DTermEqu Γ A b a
  := \ γ → rev (family-DType Γ A γ) (a γ) (b γ) (e γ)

#def transitivity-DTermEqu
  ( Γ : DCtx)
  ( A : DType Γ)
  ( a b c : DTerm Γ A)
  ( e : DTermEqu Γ A a b)
  ( f : DTermEqu Γ A b c)
  : DTermEqu Γ A a c
  := \ γ → concat (family-DType Γ A γ) (a γ) (b γ) (c γ) (e γ) (f γ)
```

## Structural rules
These are the variable, substitution and weakening rule, but the latter two are admissible. See A.2.2 in the HoTT Book. It should be noted that the latter two rules are admissible and will only be implement in their weak forms.

### Variable rule
TODO Prove that weak-DVar is (equivalent to) a special case of DVar.
```rzk
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
TODO Prove (is-rezk-DType-Sub Γ A B a). Observe the similiarity between family-DType-Sub and comp-IsoType.
```rzk
#def family-DType-Sub
  ( Γ : DCtx)
  ( A : DType Γ)
  ( B : DType (DCtx-ext Γ A))
  ( a : DTerm Γ A)
  : type-Rezk Γ → U
  := \ γ → (family-DType (DCtx-ext Γ A) B) (γ , a γ)

#postulate is-rezk-DType-Sub
  ( Γ : DCtx)
  ( A : DType Γ)
  ( B : DType (DCtx-ext Γ A))
  ( a : DTerm Γ A)
  : is-rezk (total-type (type-Rezk Γ) (family-DType-Sub Γ A B a))

#def DType-Sub
  ( Γ : DCtx)
  ( A : DType Γ)
  ( B : DType (DCtx-ext Γ A))
  ( a : DTerm Γ A)
  : DType Γ
  := (family-DType-Sub Γ A B a , is-rezk-DType-Sub Γ A B a)


#def weak-DSub
  ( Γ : DCtx)
  ( A : DType Γ)
  ( B : DType (DCtx-ext Γ A))
  ( a : DTerm Γ A)
  ( b : DTerm (DCtx-ext Γ A) B)
  : DTerm Γ (DType-Sub Γ A B a)
  := \ γ → b (γ , a γ)
```

### Weakening rule
```rzk
#def weak-DWkn
  ( Γ : DCtx)
  ( A B : DType Γ)
  ( b : DTerm Γ B)
  : DTerm (DCtx-ext Γ A) (independent-family Γ A B)
  := \ (γ , a) → b γ
```

## Σ-types
We deviate from the HoTT book and implement directed Σ-types as negative types. See the nlab-article to Martin-Löf dependent type theory.

```rzk
#def DΣ
  ( Γ : DCtx)
  ( A : DType Γ)
  ( B : DType (DCtx-ext Γ A))
  : DType Γ
  := comp-IsoType Γ A B

#def DΣ-intro
  ( Γ : DCtx)
  ( A : DType Γ)
  ( B : DType (DCtx-ext Γ A))
  ( a : DTerm Γ A)
  ( b : DTerm Γ (DType-Sub Γ A B a))
  : DTerm Γ (DΣ Γ A B)
  := \ γ → (a γ , b γ)

#def DΣ-elim1
  ( Γ : DCtx)
  ( A : DType Γ)
  ( B : DType (DCtx-ext Γ A))
  ( z : DTerm Γ (DΣ Γ A B))
  : DTerm Γ A
  := \ γ → first (z γ)

#def DΣ-elim2
  ( Γ : DCtx)
  ( A : DType Γ)
  ( B : DType (DCtx-ext Γ A))
  ( z : DTerm Γ (DΣ Γ A B))
  : DTerm Γ (DType-Sub Γ A B (DΣ-elim1 Γ A B z))
  := \ γ → second (z γ)

#def DΣ-comp1
  ( Γ : DCtx)
  ( A : DType Γ)
  ( B : DType (DCtx-ext Γ A))
  ( a : DTerm Γ A)
  ( b : DTerm Γ (DType-Sub Γ A B a))
  : DTermEqu Γ A (DΣ-elim1 Γ A B (DΣ-intro Γ A B a b)) a
  := \ γ → refl_{a γ}

#def DTerm-transport
  ( Γ : DCtx)
  ( A : DType Γ)
  ( B : DType (DCtx-ext Γ A))
  ( x y : DTerm Γ A)
  ( e : DTermEqu Γ A x y)
  ( b : DTerm Γ (DType-Sub Γ A B x))
  : DTerm Γ (DType-Sub Γ A B y)
  := \ γ → transport (family-DType Γ A γ) (\ a → family-DType (DCtx-ext Γ A) B (γ , a)) (x γ) (y γ) (e γ) (b γ)

#def DΣ-comp2
  ( Γ : DCtx)
  ( A : DType Γ)
  ( B : DType (DCtx-ext Γ A))
  ( a : DTerm Γ A)
  ( b : DTerm Γ (DType-Sub Γ A B a))
  : DTermEqu
    Γ
    ( DType-Sub Γ A B (DΣ-elim1 Γ A B (DΣ-intro Γ A B a b)))
    ( DΣ-elim2 Γ A B (DΣ-intro Γ A B a b))
    ( DTerm-transport Γ A B a (DΣ-elim1 Γ A B (DΣ-intro Γ A B a b)) (DΣ-comp1 Γ A B a b) b)
  := \ γ → refl

#def DΣ-uniq
  ( Γ : DCtx)
  ( A : DType Γ)
  ( B : DType (DCtx-ext Γ A))
  ( z : DTerm Γ (DΣ Γ A B))
  : DTermEqu Γ (DΣ Γ A B) z (DΣ-intro Γ A B (DΣ-elim1 Γ A B z) (DΣ-elim2 Γ A B z))
  := \ γ → refl
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
