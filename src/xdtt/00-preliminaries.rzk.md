# Preliminaries in the ambient type theory

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

From now on we just postulate function extensionality

```rzk
#postulate funext : FunExt

#def weakfunext : WeakFunExt
  := weakfunext-funext funext
```

and extension extensionality

```rzk
#postulate extext : ExtExt

#def weakextext : WeakExtExt
  := weakextext-extext extext

#def naiveextext : NaiveExtExt
  := naiveextext-extext extext
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
  := Σ (α : A' → A) , B' =_{ A' → U} pullback A' A α B

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

#def is-sub-universe-fiberwise
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

## The universes of Rezk types

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

`is-rezk` is a predicate. This should be proved in the ambient type theory.

```rzk

#postulate is-predicate-is-rezk
  ( A : U)
  : is-prop (is-rezk A)
```

### Isoinner families

Our basic type families correspond to isofibrations. Over a rezk type these are
just type families whose total type is itself rezk.

```rzk
#def IsoType
  ( (A , _) : Rezk)
  : U
  :=
  Σ ( B : A → U)
  , ( is-rezk (total-type A B))

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

One can prove that an IsoType family has Rezk fibers. Until that is done, we
just assume it.

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

## Incarnation of shapes as types

For each shape `ψ`, we have a canonical type `incarnate ψ` equipped with a
tautological diagram `ψ → incarnate ψ`.

```rzk
#def incarnate
  ( I : CUBE)
  ( ψ : I → TOPE)
  : U
  := (A : U) → (ψ → A) → A

#def map-incarnate
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  : incarnate I (\ t → ϕ t) → incarnate I ψ
  := \ ev-t A τ → ev-t A ( \ t → τ t)

#def universal-shape
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( t : ψ)
  : incarnate I ψ
  := \ A σ → σ t
```

This tautological diagram gives rise to a tautological comparison map.

```rzk
#def represent-incarnate
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( A : U)
  : ( incarnate I ψ → A) → (ψ → A)
  := \ iσ t → iσ (universal-shape I ψ t)
```

This map has section judgmentally.

```rzk
#def section-represent-incarnate
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( A : U)
  : (ψ → A) → (incarnate I ψ → A)
  := \ σ ev-t → ev-t A σ

#def has-section-represent-incarnate
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( A : U)
  : has-section (incarnate I ψ → A) (ψ → A) (represent-incarnate I ψ A)
  :=
    (section-represent-incarnate I ψ A , \ _ → refl)
```

As an axiom, we require that the `universal-shape` is indeed universal.

```rzk
#postulate is-universal-shape
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( A : U)
  : is-equiv (incarnate I ψ → A) (ψ → A) (represent-incarnate I ψ A)
```

We can also incarnate maps between shapes.

```rzk
#def incarnate-map
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( J : CUBE)
  ( ϕ : J → TOPE)
  ( f : (A : U) → (ϕ → A) → (ψ → A))
  : incarnate I ψ → incarnate J ϕ
  := \ ev-t A σ → ev-t A (f A σ)

#def incarnate-map-2
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( J : CUBE)
  ( ϕ : J → TOPE)
  ( K : CUBE)
  ( χ : K → TOPE)
  ( f : (A : U) → (ϕ → A) → (χ → (ψ → A)))
  : incarnate K χ → incarnate I ψ → incarnate J ϕ
  := \ ev-t ev-s A σ → ev-s A (ev-t (ψ → A) (f A σ))
```

### The walking arrow

We define the walking arrow `𝕀` as the incarnation of `Δ¹`.

```rzk
#def 𝕀 : U
  := incarnate 2 Δ¹

#def universal-arrow : Δ¹ → 𝕀
  := universal-shape 2 Δ¹
```

It comes equipped with two points `0 , 1 : 𝕀` and the two maps
`min, max : 𝕀 × 𝕀 → 𝕀`.

```rzk
#def 0_𝕀 : 𝕀
  := universal-arrow 0₂

#def 1_𝕀 : 𝕀
  := universal-arrow 1₂

#def min'
  ( A : U)
  ( σ : 2 → A)
  : 2 → (2 → A)
  := \ t s → recOR ( t ≤ s ↦ σ t , s ≤ t ↦ σ s)

#def min : 𝕀 → 𝕀 → 𝕀
  := incarnate-map-2 2 Δ¹ 2 Δ¹ 2 Δ¹ min'

#def max'
  ( A : U)
  ( σ : 2 → A)
  : 2 → (2 → A)
  := \ t s → recOR ( t ≤ s ↦ σ s , s ≤ t ↦ σ t)

#def max : 𝕀 → 𝕀 → 𝕀
  := incarnate-map-2 2 Δ¹ 2 Δ¹ 2 Δ¹ max'
```
