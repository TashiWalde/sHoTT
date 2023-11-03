# Setup

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

Some of the definitions in this file rely on function extensionality and weak
function extensionality:

```rzk
#assume funext : FunExt
#assume weakfunext : WeakFunExt
```

## Universes

A universe is simply a class of type families which is stable under pullbacks.

```rzk
#def pre-universe
  : U
  := (A : U) → (A → U) → U

#def allows-pullbacks
  ( V : pre-universe)
  : U
  :=
    ( (((A',A),α) : Map) → (B : A → U) → V A B → V A' (pullback A' A α B))

#def universe
  : U
  :=
  Σ (V : pre-universe)
  , allows-pullbacks V
```

We call it a sub-universe if additionally `V` is a predicate.

```rzk
#def is-sub-universe
  ( V : pre-universe)
  : U
  :=
  product
    ( (A : U) → (B : A → U) → is-prop (V A B))
    ( allows-pullbacks V)

#def sub-universe
  : U
  :=
  Σ (V : (A : U) → (A → U) → U)
  , is-sub-universe V

#def universe-sub-universe
  : sub-universe → universe
  := \ (V , (_ , allows-pullbacks-V)) → (V , allows-pullbacks-V)
```


### Representable universes

A pre-universe is representable if it admits a universal family.

```rzk
#def is-strong-pullback-of
  ( A' : U)
  ( B' : A' → U)
  ( A : U)
  ( B : A → U)
  : U
  := Σ (α : A' → A) , B' = pullback A' A α B

#def is-strong-pullback-of-pullback
  ( A'' : U)
  ( A' : U)
  ( α' : A'' → A')
  ( B' : A' → U)
  ( A : U)
  ( B : A → U)
  ( (α , e) : is-strong-pullback-of A' B' A B)
  : is-strong-pullback-of A'' (pullback A'' A' α' B') A B
  :=
    ( comp A'' A' A α α'
    , ( ap (A' → U) (A'' → U) (B') (pullback A' A α B)
        ( \ C' a'' → C' (α' a''))
        ( e)))

#def is-universal-family-for
  ( V : pre-universe)
  ( W : U)
  ( W* : W → U)
  : U
  := ( (A : U) → (B : A → U) → ( iff ( V A B) ( is-strong-pullback-of A B W W*)))

#def is-universal-family-for-criterion
  ( (V , allows-pb-V) : universe)
  ( W : U)
  ( W* : W → U)
  ( V-W : V W W*)
  ( is-univ-V-W-1 : (A : U) → (B : A → U) → V A B → is-strong-pullback-of A B W W*)
  : is-universal-family-for V W W*
  :=
    \ A B →
    ( is-univ-V-W-1 A B
    , ( \ (α , e) →
        transport-rev (A → U) (\ C → V A C)
        ( B) (pullback A W α W*) (e)
        ( allows-pb-V ((A,W), α) W* V-W)))
```

Every representable pre-universe is a universe.

```rzk
#def allows-pullbacks-has-universal-family
  ( V : (A : U) → (A → U) → U)
  ( W : U)
  ( W* : W → U)
  ( is-univ-V-W : is-universal-family-for V W W*)
  : allows-pullbacks V
  :=
    \ ((A',A) , α) B V-B →
    ( second (is-univ-V-W A' (pullback A' A α B))
      ( is-strong-pullback-of-pullback A' A α B W W*
        ( first (is-univ-V-W A B) V-B)))
```

### Fiberwise universes

Every predicate on types gives rise to a sub-universe.

```rzk
#section fiberwise-universes

#assume V : U → U

#def pre-universe-fiberwise
  : pre-universe
  := \ A B → (a : A) → V (B a)

#def allows-pullbacks-fiberwise uses (V)
  : allows-pullbacks pre-universe-fiberwise
  := \ ((A',A),α) B V-B a' → V-B (α a')

#def universe-fiberwise uses (V)
  : universe
  := (pre-universe-fiberwise , allows-pullbacks-fiberwise)

#def is-sub-universe-fiberwise uses (funext weakfunext)
  ( is-prop-V : (A : U) → is-prop (V A))
  : is-sub-universe ( \ A B → (a : A) → V (B a) )
  :=
    ( \ A B →
      is-prop-fiberwise-prop funext weakfunext
        A (\ a → V (B a)) ( \ a → is-prop-V (B a))
    , allows-pullbacks-fiberwise)
```

Every fiberwise (sub-)universe has a canonical candidate for a representing type
family.

```rzk
#def universal-base-fiberwise
  : U
  := Σ (A : U) , V A

#def universal-family-fiberwise uses (V)
  : universal-base-fiberwise → U
  := \ (A , _) → A

#def is-admissible-universal-family-fiberwise uses (V)
  : (pre-universe-fiberwise) universal-base-fiberwise universal-family-fiberwise
  := \ (_ , V-A) → V-A

#def classifying-map-family-fiberwise uses (V)
  ( A : U)
  ( B : A → U)
  ( V-B : pre-universe-fiberwise A B)
  : A → universal-base-fiberwise
  := \ a → (B a , V-B a)

#def is-universal-family-for-fiberwise uses (V)
  : is-universal-family-for (pre-universe-fiberwise)
    universal-base-fiberwise
    universal-family-fiberwise
  :=
    is-universal-family-for-criterion (universe-fiberwise)
    universal-base-fiberwise
    universal-family-fiberwise
    is-admissible-universal-family-fiberwise
    ( \ A B V-B → (classifying-map-family-fiberwise A B V-B, refl))

#end fiberwise-universes
```

### The universes of Rezk types

We have the fiberwise universe of Resk types.

```rzk
#def Rezk
  : U
  := Σ (A : U) , (is-rezk A)

#def type-Rezk
  : Rezk → U
  := \ (A , _) → A

#def is-rezk-Rezk
  ( (A , is-rezk-A) : Rezk)
  : is-rezk A
  := is-rezk-A

#def universe-Rezk
  : universe
  := universe-fiberwise (is-rezk)

#def compute-universal-base-Rezk
  : universal-base-fiberwise (is-rezk) = Rezk
  := refl
```

### Isoinner families

Our basic type families correspond to isofibrations.
Over a rezk type these are just type families whose total type is itself rezk.

```rzk
#def IsoType
  ( (A , _) : Rezk)
  : U
  :=
  Σ ( B : A → U)
  , (is-rezk (total-type A B))

#def family-IsoType
  ( (A , is-rezk-A) : Rezk)
  ( (B , _) : IsoType (A , is-rezk-A))
  : A → U
  := B

#def rezk-total-IsoType
  ( (A , is-rezk-A) : Rezk)
  ( (B , is-rezk-Σ-B) : IsoType (A , is-rezk-A))
  : Rezk
  := (total-type A B , is-rezk-Σ-B)
```

One can prove that an IsoType family has Rezk fibers. Until that is done, we just assume it.

```rzk
#postulate is-rezk-family-IsoType
  : ( A : Rezk)
  → ( B : IsoType A)
  → ( a : type-Rezk A)
  → is-rezk (family-IsoType A B a)

#def rezk-family-IsoType
  ( A : Rezk)
  ( B : IsoType A)
  : type-Rezk A → Rezk
  :=
    \ a → (family-IsoType A B a , is-rezk-family-IsoType A B a)
```

IsoType families can be composed. Again, we postulate this until it is proven in
the ambient theory.

```rzk
#def family-comp-IsoType
  ( A : Rezk)
  ( B : IsoType A)
  ( C : IsoType (rezk-total-IsoType A B))
  : type-Rezk A → U
  :=
  \ a →
    ( Σ ( b : family-IsoType A B a)
      , family-IsoType (rezk-total-IsoType A B) C (a , b))

#postulate is-rezk-total-comp-IsoType
  : ( A : Rezk)
  → ( B : IsoType A)
  → ( C : IsoType (rezk-total-IsoType A B))
  → is-rezk (total-type (type-Rezk A) (family-comp-IsoType A B C))

#def comp-IsoType
  ( A : Rezk)
  ( B : IsoType A)
  ( C : IsoType (rezk-total-IsoType A B))
  : IsoType A
  :=
    (family-comp-IsoType A B C , is-rezk-total-comp-IsoType A B C)
```

## Directed type theory

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

### Sigma types

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
