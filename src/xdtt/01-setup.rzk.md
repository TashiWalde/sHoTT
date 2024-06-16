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
TODO Prove (is-rezk-DTypeSub Γ A B a). Observe the similiarity between family-DTypeSub and comp-IsoType.
```rzk
#def family-DTypeSub
  ( Γ : DCtx)
  ( A : DType Γ)
  ( B : DType (DCtx-ext Γ A))
  ( a : DTerm Γ A)
  : type-Rezk Γ → U
  := \ γ → (family-DType (DCtx-ext Γ A) B) (γ , a γ)

#postulate is-rezk-DTypeSub
  ( Γ : DCtx)
  ( A : DType Γ)
  ( B : DType (DCtx-ext Γ A))
  ( a : DTerm Γ A)
  : is-rezk (total-type (type-Rezk Γ) (family-DTypeSub Γ A B a))

#def DTypeSub
  ( Γ : DCtx)
  ( A : DType Γ)
  ( B : DType (DCtx-ext Γ A))
  ( a : DTerm Γ A)
  : DType Γ
  := (family-DTypeSub Γ A B a , is-rezk-DTypeSub Γ A B a)


#def DSub
  ( Γ : DCtx)
  ( A : DType Γ)
  ( B : DType (DCtx-ext Γ A))
  ( a : DTerm Γ A)
  ( b : DTerm (DCtx-ext Γ A) B)
  : DTerm Γ (DTypeSub Γ A B a)
  := \ γ → b (γ , a γ)
```

### Weakening rule
```rzk
#def DWkn
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
  ( b : DTerm Γ (DTypeSub Γ A B a))
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
  : DTerm Γ (DTypeSub Γ A B (DΣ-elim1 Γ A B z))
  := \ γ → second (z γ)

#def DΣ-comp1
  ( Γ : DCtx)
  ( A : DType Γ)
  ( B : DType (DCtx-ext Γ A))
  ( a : DTerm Γ A)
  ( b : DTerm Γ (DTypeSub Γ A B a))
  : DTermEqu Γ A (DΣ-elim1 Γ A B (DΣ-intro Γ A B a b)) a
  := \ γ → refl_{a γ}

#def DTerm-transport
  ( Γ : DCtx)
  ( A : DType Γ)
  ( B : DType (DCtx-ext Γ A))
  ( x y : DTerm Γ A)
  ( e : DTermEqu Γ A x y)
  ( b : DTerm Γ (DTypeSub Γ A B x))
  : DTerm Γ (DTypeSub Γ A B y)
  := \ γ → transport (family-DType Γ A γ) (\ a → family-DType (DCtx-ext Γ A) B (γ , a)) (x γ) (y γ) (e γ) (b γ)

#def DΣ-comp2
  ( Γ : DCtx)
  ( A : DType Γ)
  ( B : DType (DCtx-ext Γ A))
  ( a : DTerm Γ A)
  ( b : DTerm Γ (DTypeSub Γ A B a))
  : DTermEqu
    Γ
    ( DTypeSub Γ A B (DΣ-elim1 Γ A B (DΣ-intro Γ A B a b)))
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

## Independent Types
Given a type A in context Γ, any type B in context Γ can be considered in context (DCtx-ext Γ A). This is implemented as (independent-family Γ A B). One would expect that one gets back B in context Γ by substituting any term a of type A in (independent-family Γ A B), but the proofs that the total spaces of B and (DTypeSub Γ A (independent-family Γ A B) a) are currently different as the later is postulated. We believe this is a bug, resolved once (is-rezk-DTypeSub Γ A B a) is proven.

```rzk
#def independent-DTerm
  ( Γ : DCtx)
  ( A B : DType Γ)
  ( a : DTerm Γ A)
  ( b : DTerm Γ B)
  : DTerm Γ (DTypeSub Γ A (independent-family Γ A B) a)
  := (DSub Γ A (independent-family Γ A B) a (DWkn Γ A B b))

#def DTerm-independent-DTerm
  ( Γ : DCtx)
  ( A B : DType Γ)
  ( a : DTerm Γ A)
  ( b : DTerm Γ (DTypeSub Γ A (independent-family Γ A B) a))
  : DTerm Γ B
  := \ γ → b γ
```

## Cartesian Product types
We implement cartesian product types as special cases of Σ-types where the second factors does not dependent on the first.

```rzk
#def DCartProd
  ( Γ : DCtx)
  ( A B : DType Γ)
  : DType Γ
  := DΣ Γ A (independent-family Γ A B)

#def DCartProd-intro
  ( Γ : DCtx)
  ( A B : DType Γ)
  ( a : DTerm Γ A)
  ( b : DTerm Γ B)
  : DTerm Γ (DCartProd Γ A B)
  := DΣ-intro Γ A (independent-family Γ A B) a (independent-DTerm Γ A B a b)

#def DCartProd-elim1
  ( Γ : DCtx)
  ( A B : DType Γ)
  ( z : DTerm Γ (DCartProd Γ A B))
  : DTerm Γ A
  := DΣ-elim1 Γ A (independent-family Γ A B) z

#def DCartProd-elim2
  ( Γ : DCtx)
  ( A B : DType Γ)
  ( z : DTerm Γ (DCartProd Γ A B))
  : DTerm Γ B
  := DTerm-independent-DTerm Γ A B (DCartProd-elim1 Γ A B z)
    ( DΣ-elim2 Γ A (independent-family Γ A B) z)

#def DCartProd-comp1
  ( Γ : DCtx)
  ( A B : DType Γ)
  ( a : DTerm Γ A)
  ( b : DTerm Γ B)
  : DTermEqu Γ A (DCartProd-elim1 Γ A B (DCartProd-intro Γ A B a b)) a
  := DΣ-comp1 Γ A (independent-family Γ A B) a (independent-DTerm Γ A B a b)

#def DCartProd-comp2
  ( Γ : DCtx)
  ( A B : DType Γ)
  ( a : DTerm Γ A)
  ( b : DTerm Γ B)
  : DTermEqu Γ B (DCartProd-elim2 Γ A B (DCartProd-intro Γ A B a b)) b
  := DΣ-comp2 Γ A (independent-family Γ A B) a (independent-DTerm Γ A B a b)

#postulate DCartProd-uniq
  ( Γ : DCtx)
  ( Γ : DCtx)
  ( A B : DType Γ)
  ( z : DTerm Γ (DCartProd Γ A B))
  : DTermEqu Γ (DCartProd Γ A B) z (DCartProd-intro Γ A B (DCartProd-elim1 Γ A B z) (DCartProd-elim2 Γ A B z))
```

## Coproduct types
To be implemented.

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
```

## Pi types

```rzk
#def type-DΠ
  ( Γ : GrpdCtx)
  ( A : DType (DCtx-GrpdCtx Γ))
  ( B : DType (DCtx-ext (DCtx-GrpdCtx Γ) A))
  : ( type-GrpdCtx Γ) → U
  := Π-type
    ( type-GrpdCtx Γ)
    ( family-IsoType (DCtx-GrpdCtx Γ) A)
    ( family-IsoType (DCtx-ext (DCtx-GrpdCtx Γ) A) B)

#def is-rezk-DΠ
  ( Γ : GrpdCtx)
  ( A : DType (DCtx-GrpdCtx Γ))
  ( B : DType (DCtx-ext (DCtx-GrpdCtx Γ) A))
  : is-rezk (total-type (type-GrpdCtx Γ) (type-DΠ Γ A B))
  := is-rezk-Π-type-are-rezk-total-types-is-discrete
    ( type-GrpdCtx Γ) (is-discrete-GrpdCtx Γ) A B

#def DΠ
  ( Γ : GrpdCtx)
  ( A : DType (DCtx-GrpdCtx Γ))
  ( B : DType (DCtx-ext (DCtx-GrpdCtx Γ) A))
  : DType (DCtx-GrpdCtx Γ)
  := (type-DΠ Γ A B , is-rezk-DΠ Γ A B)

#def DΠ-intro
  ( Γ : GrpdCtx)
  ( A : DType (DCtx-GrpdCtx Γ))
  ( B : DType (DCtx-ext (DCtx-GrpdCtx Γ) A))
  ( b : DTerm (DCtx-ext (DCtx-GrpdCtx Γ) A) B)
  : DTerm (DCtx-GrpdCtx Γ) (DΠ Γ A B)
  := \ γ a → b (γ , a)

#def DΠ-elim
  ( Γ : GrpdCtx)
  ( A : DType (DCtx-GrpdCtx Γ))
  ( B : DType (DCtx-ext (DCtx-GrpdCtx Γ) A))
  ( f : DTerm (DCtx-GrpdCtx Γ) (DΠ Γ A B))
  ( a : DTerm (DCtx-GrpdCtx Γ) A)
  : DTerm (DCtx-GrpdCtx Γ) (DTypeSub (DCtx-GrpdCtx Γ) A B a)
  := \ γ → f γ (a γ)

#def DΠ-comp
  ( Γ : GrpdCtx)
  ( A : DType (DCtx-GrpdCtx Γ))
  ( B : DType (DCtx-ext (DCtx-GrpdCtx Γ) A))
  ( a : DTerm (DCtx-GrpdCtx Γ) A)
  ( b : DTerm (DCtx-ext (DCtx-GrpdCtx Γ) A) B)
  : DTermEqu
    ( DCtx-GrpdCtx Γ)
    ( DTypeSub (DCtx-GrpdCtx Γ) A B a)
    ( DSub (DCtx-GrpdCtx Γ) A B a b)
    ( DΠ-elim Γ A B (DΠ-intro Γ A B b) a)
  := \ γ → refl

-- We need this variation of the elimination rule to formulate the uniqueness rules.
#def DΠ-varelim
  ( Γ : GrpdCtx)
  ( A : DType (DCtx-GrpdCtx Γ))
  ( B : DType (DCtx-ext (DCtx-GrpdCtx Γ) A))
  ( f : DTerm (DCtx-GrpdCtx Γ) (DΠ Γ A B))
  : DTerm (DCtx-ext (DCtx-GrpdCtx Γ) A) B
  := \ (γ , a) → f γ a

#def DΠ-uniq
  ( Γ : GrpdCtx)
  ( A : DType (DCtx-GrpdCtx Γ))
  ( B : DType (DCtx-ext (DCtx-GrpdCtx Γ) A))
  ( f : DTerm (DCtx-GrpdCtx Γ) (DΠ Γ A B))
  : DTermEqu (DCtx-GrpdCtx Γ) (DΠ Γ A B) f (DΠ-intro Γ A B (DΠ-varelim Γ A B f))
  := \ γ → refl
```

## Function types
We implement function types as special cases of Π-types where the second factors does not dependent on the first.

```rzk
#def DFun
  ( Γ : GrpdCtx)
  ( A B : DType (DCtx-GrpdCtx Γ))
  : DType (DCtx-GrpdCtx Γ)
  := DΠ Γ A (independent-family (DCtx-GrpdCtx Γ) A B)

#def DFun-intro
  ( Γ : GrpdCtx)
  ( A B : DType (DCtx-GrpdCtx Γ))
  ( b : DTerm
      ( DCtx-ext (DCtx-GrpdCtx Γ) A)
      ( independent-family (DCtx-GrpdCtx Γ) A B))
  : DTerm (DCtx-GrpdCtx Γ) (DFun Γ A B)
  := DΠ-intro
    Γ
    A
    ( independent-family (DCtx-GrpdCtx Γ) A B)
    b

#def DFun-elim
  ( Γ : GrpdCtx)
  ( A B : DType (DCtx-GrpdCtx Γ))
  ( f : DTerm (DCtx-GrpdCtx Γ) (DFun Γ A B))
  ( a : DTerm (DCtx-GrpdCtx Γ) A)
  : DTerm (DCtx-GrpdCtx Γ) B
  := DΠ-elim Γ A (independent-family (DCtx-GrpdCtx Γ) A B) f a

#def DFun-comp
  ( Γ : GrpdCtx)
  ( A B : DType (DCtx-GrpdCtx Γ))
  ( a : DTerm (DCtx-GrpdCtx Γ) A)
  ( b : DTerm
      ( DCtx-ext (DCtx-GrpdCtx Γ) A)
      ( independent-family (DCtx-GrpdCtx Γ) A B))
  : DTermEqu
    ( DCtx-GrpdCtx Γ)
    B
    ( DSub (DCtx-GrpdCtx Γ) A (independent-family (DCtx-GrpdCtx Γ) A B) a b)
    ( DFun-elim Γ A B (DFun-intro Γ A B b) a)
  := DΠ-comp Γ A (independent-family (DCtx-GrpdCtx Γ) A B) a b

#def DFun-varelim
  ( Γ : GrpdCtx)
  ( A B : DType (DCtx-GrpdCtx Γ))
  ( f : DTerm (DCtx-GrpdCtx Γ) (DFun Γ A B))
  : DTerm
    ( DCtx-ext (DCtx-GrpdCtx Γ) A)
    ( independent-family (DCtx-GrpdCtx Γ) A B)
  := DΠ-varelim Γ A (independent-family (DCtx-GrpdCtx Γ) A B) f

#def DFun-uniq
  ( Γ : GrpdCtx)
  ( A B : DType (DCtx-GrpdCtx Γ))
  ( f : DTerm (DCtx-GrpdCtx Γ) (DFun Γ A B))
  : DTermEqu
    ( DCtx-GrpdCtx Γ)
    ( DFun Γ A B)
    f
    ( DFun-intro Γ A B (DFun-varelim Γ A B f))
  := DΠ-uniq Γ A (independent-family (DCtx-GrpdCtx Γ) A B) f
```
