\documentclass{article}

% The following packages are needed because unicode
% is translated (using the next set of packages) to
% latex commands. You may need more packages if you
% use more unicode characters:

\usepackage{amssymb}
\usepackage{bbm}
\usepackage[greek,english]{babel}

% This handles the translation of unicode to latex:

\usepackage{ucs}
\usepackage[utf8x]{inputenc}
\usepackage{autofe}

% Some characters that are not automatically defined
% (you figure out by the latex compilation errors you get),
% and you need to define:

\DeclareUnicodeCharacter{8988}{\ensuremath{\ulcorner}}
\DeclareUnicodeCharacter{8989}{\ensuremath{\urcorner}}
\DeclareUnicodeCharacter{8803}{\ensuremath{\overline{\equiv}}}

% Add more as you need them (shouldn't happen often).

% Using "\newenvironment" to redefine verbatim to
% be called "code" doesn't always work properly. 
% You can more reliably use:

\usepackage{fancyvrb}

\DefineVerbatimEnvironment
  {code}{Verbatim}
  {} % Add fancy options here if you like.

\begin{document}

In .NET, replacing a empty substring of any with any other string throws a
runtime exception. This is unpleasant; but is this a case of $0/0$, i.e. is it a
case where, without dependent types, the best thing to do \textit{is} to throw?
Let us investigate.

First, observe that splitting on a substring is a more primitive operation than
replacing: replacing could be defined in terms of splitting, intercalating, and
then concating the results. Then, observe that to split on all non-overlapping
occurrences of a substring (from left to right) can be define recursively in
terms of applying a ``split on first'' function to the remainder until nothing
of interest is left. Thus, we begin with an attempt to specify the behavior of
split on first. In order to do that, we need a model of expressing the
mathematical properties of prefixes and suffixes of strings. We will use
singly-linked lists of characters to encode strings, except that we don't
particularly care what character type is used; and so we will use parametric
lists.

\begin{code}
module Replace where

open import Data.List.Base
open import Relation.Binary.PropositionalEquality using (_≡_)
import Relation.Binary.PropositionalEquality as PropEq
\end{code}

We begin with a definition of what it means for one list to be a prefix of
another, working with the principle that in .NET the index of an empty string in
any string is 0.

\begin{code}

data NETIsPrefixOf : ∀ {A : Set} → List A → List A → Set where
  NilPrefixAll : ∀ {A : Set} {xs : List A} → NETIsPrefixOf [] xs
  NETSuccPrefix : ∀ {A : Set} {x : A} {xs ys : List A}
                → NETIsPrefixOf xs ys → NETIsPrefixOf (x ∷ xs) (x ∷ ys)

\end{code}

And we give an analogous definition of what it is to be a suffix.

\begin{code}

data NETIsSuffixOf : ∀ {A : Set} → List A → List A → Set where
  NETSuffixRefl : ∀ {A : Set} {xs : List A} → NETIsSuffixOf xs xs
  NETSuccSuffix : ∀ {A : Set} {x : A} {xs ys : List A}
                → NETIsSuffixOf xs ys → NETIsSuffixOf xs (x ∷ ys)

\end{code}

We notice that these ought to be partial orders. Let's try to prove it. We start
by defining what it is to be a partial order. Were I better at Agda, I'm sure I
could use what they have already under the Relation namespace. A partial order
requires three laws: reflexivity, antisymmetry, and transitivity.

\begin{code}

record PartialOrder {A : Set} (R : A → A → Set) : Set where
  constructor partialOrder
  field
    refl : (a : A) → R a a
    antisym : (a : A) → (b : A) → R a b → R b a → a ≡ b
    trans : (a : A) → (b : A) → (c : A) → R a b → R b c → R a c

\end{code}

Let's prove the necessary laws for prefix.

\begin{code}

prefixRefl : ∀{A} → (a : List A) → NETIsPrefixOf a a
prefixRefl [] = NilPrefixAll
prefixRefl (x ∷ x₁) = NETSuccPrefix (prefixRefl x₁)

prefixAntisym : ∀{A} → (a : List A) → (b : List A)
              → NETIsPrefixOf a b → NETIsPrefixOf b a → a ≡ b
prefixAntisym [] [] _ _ = PropEq.refl
prefixAntisym [] (_ ∷ _) NilPrefixAll ()
prefixAntisym (_ ∷ _) [] () _
prefixAntisym (x ∷ a) (.x ∷ b) (NETSuccPrefix p) (NETSuccPrefix q) =
  PropEq.cong (_∷_ x) (prefixAntisym a b p q)

prefixTrans : ∀{A} → (a : List A) → (b : List A) → (c : List A)
            → NETIsPrefixOf a b → NETIsPrefixOf b c → NETIsPrefixOf a c
prefixTrans [] _ _ _ _ = NilPrefixAll
prefixTrans (_ ∷ _) [] [] p _ = p
prefixTrans (_ ∷ _) [] (_ ∷ _) () _
prefixTrans (_ ∷ _) (_ ∷ _) [] (NETSuccPrefix _) ()
prefixTrans (x ∷ a) (.x ∷ b) (.x ∷ c) (NETSuccPrefix p) (NETSuccPrefix q) =
  NETSuccPrefix (prefixTrans a b c p q)

NETPrefixIsPartialOrder : ∀{A} → PartialOrder (NETIsPrefixOf {List A})
NETPrefixIsPartialOrder = partialOrder prefixRefl prefixAntisym prefixTrans

\end{code}

Let's prove the necessary laws for suffix.

\begin{code}

nilSuffixAll : ∀{A} → (a : List A) → NETIsSuffixOf [] a
nilSuffixAll [] = NETSuffixRefl
nilSuffixAll (_ ∷ a) = NETSuccSuffix (nilSuffixAll a)

suffixRefl : ∀{A} → (a : List A) → NETIsSuffixOf a a
suffixRefl _ = NETSuffixRefl

suffixAntisym :  ∀{A} → (a : List A) → (b : List A)
              → NETIsSuffixOf a b → NETIsSuffixOf b a → a ≡ b
suffixAntisym [] [] _ _ = PropEq.refl
suffixAntisym [] (_ ∷ _) (NETSuccSuffix _) ()
suffixAntisym (_ ∷ _) [] () _
suffixAntisym (x ∷ a) (.x ∷ .a) NETSuffixRefl _ = PropEq.refl
suffixAntisym (x ∷ a) (.x ∷ .a) (NETSuccSuffix _) NETSuffixRefl = PropEq.refl
suffixAntisym (x ∷ a) (x₁ ∷ b) (NETSuccSuffix p) (NETSuccSuffix q) = {!!}

suffixTrans : ∀{A} → (a : List A) → (b : List A) → (c : List A)
            → NETIsSuffixOf a b → NETIsSuffixOf b c → NETIsSuffixOf a c
suffixTrans [] [] _ _ q = q
suffixTrans [] (_ ∷ _) [] (NETSuccSuffix _) ()
suffixTrans [] (x ∷ b) (.x ∷ .b) (NETSuccSuffix p) NETSuffixRefl =
  NETSuccSuffix p
suffixTrans [] (x ∷ b) (x₁ ∷ c) (NETSuccSuffix p) (NETSuccSuffix q) =
  NETSuccSuffix (nilSuffixAll c)
suffixTrans (_ ∷ _) [] [] () _
suffixTrans (_ ∷ _) [] (_ ∷ _) () _
suffixTrans (_ ∷ _) (_ ∷ _) [] _ ()
suffixTrans (x ∷ a) (.x ∷ .a) (x₂ ∷ c) NETSuffixRefl q = q
suffixTrans (x ∷ a) (x₁ ∷ b) (.x₁ ∷ .b) (NETSuccSuffix p) NETSuffixRefl =
  NETSuccSuffix p
suffixTrans (x ∷ a) (x₁ ∷ b) (x₂ ∷ c) (NETSuccSuffix p) (NETSuccSuffix q) = {!!}

--NETSuffixIsPartialOrder : ∀{A} → PartialOrder (NETIsSuffixOf {List A})
--NETSuffixIsPartialOrder = partialOrder NETSuffixRefl

\end{code}

\end{document}
