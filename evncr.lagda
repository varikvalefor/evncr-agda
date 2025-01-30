\documentclass{report}

\usepackage{ar}
\usepackage[bw]{agda}
\usepackage{ifsym}
\usepackage{xcolor}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{parskip}
\usepackage{mathabx}
\usepackage{unicode-math}
\usepackage{newunicodechar}

\newunicodechar{λ}{\ensuremath{\mathnormal\lambda}}
\newunicodechar{∃}{\ensuremath{\mathnormal\exists}}
\newunicodechar{∄}{\ensuremath{\mathnormal\nexists}}
\newunicodechar{∷}{\ensuremath{\mathnormal\Colon}}
\newunicodechar{∨}{\ensuremath{\mathnormal\vee}}
\newunicodechar{ℕ}{\ensuremath{\mathnormal{\mathbb{N}}}}
\newunicodechar{∈}{\ensuremath{\mathnormal\in}}
\newunicodechar{∉}{\ensuremath{\mathnormal\notin}}
\newunicodechar{∋}{\ensuremath{\mathnormal\ni}}
\newunicodechar{≡}{\ensuremath{\mathnormal\equiv}}
\newunicodechar{≟}{\ensuremath{\stackrel{?}{=}}}
\newunicodechar{⟨}{\ensuremath{\mathnormal\langle}}
\newunicodechar{⟩}{\ensuremath{\mathnormal\rangle}}
\newunicodechar{∎}{\ensuremath{\mathnormal\blacksquare}}
\newunicodechar{∶}{\ensuremath{\mathnormal\colon\!\!}}
\newunicodechar{⊹}{\ensuremath{\mathnormal\dag}}
\newunicodechar{▹}{\ensuremath{\mathnormal\triangleright}}
\newunicodechar{𝕗}{\ensuremath{\mathnormal{\mathbb{f}}}}
\newunicodechar{ℙ}{\ensuremath{\mathnormal{\mathbb{P}}}}
\newunicodechar{𝔽}{\ensuremath{\mathnormal{\mathbb{F}}}}
\newunicodechar{𝕊}{\ensuremath{\mathnormal{\mathbb{S}}}}
\newunicodechar{𝕄}{\ensuremath{\mathnormal{\mathbb{M}}}}
\newunicodechar{𝔹}{\ensuremath{\mathnormal{\mathbb{B}}}}
\newunicodechar{ν}{\ensuremath{\mathnormal{\nu}}}
\newunicodechar{μ}{\ensuremath{\mathnormal{\mu}}}
\newunicodechar{◆}{\ensuremath{\mathnormal\blackdiamond}}
\newunicodechar{∸}{\ensuremath{\mathnormal\dotdiv}}
\newunicodechar{ᵇ}{\ensuremath{\mathnormal{^\AgdaFontStyle{b}}}}
\newunicodechar{≥}{\ensuremath{\mathnormal{\geq}}}
\newunicodechar{ϕ}{\ensuremath{\mathnormal{\phi}}}
\newunicodechar{χ}{\ensuremath{\mathnormal{\chi}}}
\newunicodechar{∧}{\ensuremath{\mathnormal{\wedge}}}
\newunicodechar{∅}{\ensuremath{\mathnormal{\emptyset}}}
\newunicodechar{∣}{\ensuremath{\mathnormal{|}}}
\newunicodechar{⁇}{\ensuremath{\mathnormal{\mathrm{?\!?}}}}
\newunicodechar{∘}{\ensuremath{\mathnormal{\circ}}}
\newunicodechar{∀}{\ensuremath{\mathnormal{\forall}}}
\newunicodechar{ℓ}{\ensuremath{\mathnormal{\ell}}}
\newunicodechar{σ}{\ensuremath{\mathnormal{\sigma}}}
\newunicodechar{₁}{\ensuremath{\mathnormal{_1}}}
\newunicodechar{₂}{\ensuremath{\mathnormal{_2}}}
\newunicodechar{ₘ}{\ensuremath{\mathnormal{_\mathsf{m}}}}
\newunicodechar{ₛ}{\ensuremath{\mathnormal{_\mathsf{s}}}}
\newunicodechar{⊤}{\ensuremath{\mathnormal{\top}}}
\newunicodechar{≤}{\ensuremath{\mathnormal{\leq}}}
\newunicodechar{⍉}{\ensuremath{\mathnormal{∘\hspace{-0.455em}\backslash}}}
\newunicodechar{⦃}{\ensuremath{\mathnormal{\lbrace\!\lbrace}}}
\newunicodechar{⦄}{\ensuremath{\mathnormal{\rbrace\!\rbrace}}}
\newunicodechar{ᵢ}{\ensuremath{\mathnormal{_i}}}
\newunicodechar{ₗ}{\ensuremath{\mathnormal{_l}}}
\newunicodechar{ₒ}{\ensuremath{\mathnormal{_o}}}
\newunicodechar{ₚ}{\ensuremath{\mathnormal{_p}}}
\newunicodechar{ₙ}{\ensuremath{\mathnormal{_n}}}
\newunicodechar{ᵥ}{\ensuremath{\mathnormal{_v}}}
\newunicodechar{′}{\ensuremath{\mathnormal{'}}}
\newunicodechar{⊎}{\ensuremath{\mathnormal{\uplus}}}
\newunicodechar{≗}{\ensuremath{\mathnormal{\circeq}}}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound
\newcommand\IC\AgdaInductiveConstructor
\newcommand\OpF[1]{\AgdaOperator{\F{#1}}}

\newcommand\filrihavelcki[1]{ni'o la .varik.\ cu jinvi le du'u lo nu jimpe fi la'oi .\D{Lerfu}.\ cu filri'a lo nu jimpe fi la'oi .\D{#1}.}

\newcommand\selsnap[2]{lo nu drani .uniks.\ bo co'e la'o zoi.\ #1\ .zoi.\ cu rinka lo nu lo srana be lo skami cu selsnapra lo velski be #2}
\newcommand\sopa{\colorbox{black!90}{sopa}}

\title{le me'oi .Agda.\ velcki be la'oi .EVANNOUNCER.}
\author{la .varik.\ .VALefor.}

\begin{document}
\maketitle

\chapter{le me'oi .preamble.}
\begin{code}
{-# OPTIONS --guardedness #-}

open import IO
  renaming (
    _<$>_ to _<$>ᵢₒ_;
    _>>=_ to _>>=ᵢₒ_;
    lift to liftᵢₒ
  )
open import Data.Fin
  as 𝔽
  using (
    fromℕ<;
    toℕ;
    Fin
  )
open import Data.Nat
  as ℕ
  using (
    _∸_;
    _*_;
    suc;
    ℕ
  )
open import Data.Vec
  using (
    fromList;
    toList;
    Vec
  )
  renaming (
    map to mapᵥ;
    _∷_ to _∷ᵥ_;
    [] to []ᵥ
  )
open import Function
  using (
    _∘₂_;
    _∋_;
    flip;
    _$_;
    _∘_;
    id
  )
  renaming (
    _|>_ to _▹_
  )
open import Data.Bool
  using (
    false;
    Bool;
    true
  )
  renaming (
    if_then_else_ to if
  )
open import Data.Char
  using (
    Char
  )
open import Data.List
  using (
    List;
    upTo;
    drop
  )
  renaming (
    [] to []ₗ;
    map to mapₗ;
    _∷_ to _∷ₗ_
  )
open import Data.Float
  using (
    Float
  )
open import Data.Maybe
  using (
    decToMaybe;
    Is-nothing;
    is-just;
    nothing;
    Maybe;
    maybe;
    just
  )
  renaming (
    map to mapₘ
  )
open import Data.String
  as 𝕊
  using (
    String
  )
open import Data.Product
  using (
    proj₂;
    proj₁;
    _×_;
    _,_;
    ∃
  )
open import IO.Primitive
  using (
  )
  renaming (
    IO to PIO;
    _>>=_ to _>>=ₚᵢₒ_
  )
open import Data.Nat.DivMod
  using (
    _%_
  )
open import Relation.Nullary
  using (
    Dec;
    yes;
    ¬_;
    no
  )
open import Truthbrary.Data.Fin
  using (
    mink
  )
open import Truthbrary.Record.Eq
  using (
    _≟_;
    Eq
  )
open import Truthbrary.Record.SR
  using (
    readMaybe;
    Show;
    show
  )
open import Data.Unit.Polymorphic
  using (
    tt;
    ⊤
  )
open import Truthbrary.Record.LLC
  using (
    liliString;
    length;
    _++_;
    _∷_;
    _∉_;
    _∈_;
    map
  )
open import Relation.Nullary.Negation
  renaming (
    contradiction to _⇒⇐_
  )
open import Relation.Nullary.Decidable
  using (
    isYes≗does;
    isYes
  )
open import Relation.Binary.PropositionalEquality
  using (
    module ≡-Reasoning;
    subst₂;
    subst;
    cong;
    refl;
    sym;
    _≡_
  )

import Agda.Builtin.Unit
  as ABU
import Data.Fin.Properties
  as DFP
import Data.Nat.Properties
  as DNP
import Data.Vec.Properties
  as DVP
import Data.List.Properties
  as DLP
import Data.List.Relation.Unary.All
  as DLA
import Data.List.Relation.Unary.Any
  as DLAny
import Data.Maybe.Relation.Unary.All
  as DMA
import Data.Maybe.Relation.Unary.Any
  as DMAny
\end{code}

\chapter{le srana be lo nu tcimi'e}

\section{la'oi .\F{selsniduXiPa}.}
ni'o la'oi .\F{selsniduXiPa}.\ bitmu fo lo ctaipe be la'oi .\D{Lerfu}.

\begin{code}
postulate selsniduXiPa : Float
\end{code}

\section{la'oi .\F{selsniduXiRe}.}
ni'o la'oi .\F{selsniduXiRe}.\ bitmu fo lo ctaipe be la'oi glibau.\ \D{List} \D{Lerfu} .glibau.

\begin{code}
postulate selsniduXiRe : Float
\end{code}

\section{la'oi .\F{ddvs}.}
ni'o la'oi .\F{ddvs}.\ me'oi .path.\ lo datnyveiste be lo'i sance pe la'oi .EVANNOUNCER.

.i zo'oi .ddvs.\ cmavlaka'i lu datni datnyveiste li'u

\begin{code}
ddvs : String
ddvs = "/usr/local/share/evannouncer/"
\end{code}

\chapter{le zo'oi .\AgdaKeyword{data}.\ co'e}

\section{la'oi .\D{Midnoi}.}
ni'o ro da poi ke'a ctaipe la'oi .\D{Midnoi}.\ zo'u da sinxa lo .uniks.\ midnoi

\begin{code}
Midnoi : Set
Midnoi = String
\end{code}

\section{la'oi .\D{Case}.}
\filrihavelcki{Case}

\begin{code}
data Case : Set
  where
  Barda : Case
  Cmalu : Case
  Namcu : Case
  Tcekr : Case
  Kurfa : Case
  Cukla : Case
  Jganu : Case
  Snile'u : Case
\end{code}

\subsection{le me'oi .\AgdaKeyword{instance}.}

\begin{code}
instance
  shockAndAwe : Show Case
  shockAndAwe = record {show = f}
    where
    f : Case → String
    f Barda = "Barda"
    f Cmalu = "Cmalu"
    f Namcu = "Namcu"
    f Cukla = "Cukla"
    f Tcekr = "Tcekr"
    f Kurfa = "Kurfa"
    f Jganu = "Jganu"
    f Snile'u = "Snile'u"
\end{code}

\section{la'oi .\D{LTyp}.}
\filrihavelcki{LTyp}

\begin{code}
data LTyp : Set
  where
  Latmo : LTyp
  Xrabo : LTyp
  Vrici : LTyp
  Kalri : LTyp
  Ganlo : LTyp
\end{code}

\subsection{le me'oi .\AgdaKeyword{instance}.}

\begin{code}
instance
  showUsYourBoobs : Show LTyp
  showUsYourBoobs = record {show = f}
    where
    f : LTyp → String
    f Latmo = "Latmo"
    f Xrabo = "Xrabo"
    f Vrici = "Vrici"
    f Kalri = "Kalri"
    f Ganlo = "Ganlo"
\end{code}

\section{la'oi .\D{Lerfu}.}
ni'o sinxa lo lerfu be la'oi .ASCII.\ fa lo ro ctaipe be la'oi .\D{Lerfu}.\ be'o poi ke'a drani

.i ga jo fo'a goi la'oi .\B x.\ drani gi\ldots
\begin{itemize}
	\item ga jonai ga je ko'a goi la'o zoi.\ \AgdaField{Lerfu.ctyp} \B x .zoi.\ du la'oi .\IC{Xrabo}.\ gi ga je fo'a sinxa lo nacle'u gi ga je ko'e goi la'o zoi.\ \AgdaField{Lerfu.case} \B x .zoi.\ du la'oi .\IC{Namcu}.\ gi ko'i goi la'o zoi.\ \AgdaField{Lerfu.bnam} \B x .zoi.\ sumji lo namcu poi selsni la'oi .\B x.\ ku'o li vobi gi
	\item ga jonai ga je ko'a du la'oi .\IC{Latmo}.\ gi\ldots
	\begin{itemize}
		\item ga jonai ga je ko'e du la'oi .\IC{Barda}.\ gi ga je la'oi .\B x.\ sinxa lo me'oi .majuscule.\ lerfu gi ko'i sumji lo mu'oi glibau.\ 0-indexed .glibau.\ se meirmoi be lo me'oi .caseless.\ versiio be lo selsni be la'oi .\B x.\ li xamu gi
		\item ga je ko'e du la'oi .\IC{Cmalu}.\ gi ga je la'oi .\B x.\ sinxa lo me'oi .minuscule.\ lerfu gi ko'i sumji lo mu'oi glibau.\ 0-indexed .glibau.\ se meirmoi be lo me'oi .caseless.\ versiio be lo selsni be la'oi .\B x.\ li soze gi
	\end{itemize}
	\item ga jonai ga je ko'a du la'oi .\IC{Kalri}.\ gi ga je ko'i du li \sopa\ gi\ldots
	\begin{itemize}
		\item ga jonai ga je ko'e du la'oi .\IC{Tcekr}.\ gi fo'a sinxa lo tolsti me'oi .curly.\ bo me'oi .bracket.\ noi ke'a selsni li pareci pe la .asycy'i'is.\ gi
		\item ga jonai ga je ko'e du la'oi .\IC{Kurfa}.\ gi fo'a sinxa lo tolsti kurfa bo me'oi .bracket.\ noi ke'a selsni li \sopa\ pe la .asycy'i'is.\ gi
		\item ga je ko'e du la'oi .\IC{Cukla}.\ gi fo'a sinxa lo tolsti cukla bo me'oi .bracket.\ noi ke'a selsni li vono pe la .asycy'i'is.\ gi
	\end{itemize}
	\item ga je ko'a du la'oi .\IC{Ganlo}.\ gi ga je ko'i du li soci gi\ldots
	\begin{itemize}
		\item ga jonai ga je ko'e du la'oi .\IC{Tcekr}.\ gi fo'a sinxa lo sisti me'oi .curly.\ bo me'oi .bracket.\ noi ke'a selsni li paremu pe la .asycy'i'is.\ gi
		\item ga jonai ga je ko'e du la'oi .\IC{Kurfa}.\ gi fo'a sinxa lo sisti kurfa bo me'oi .bracket.\ noi ke'a selsni li soci pe la .asycy'i'is.\ gi
		\item ga jonai ga je ko'e du la'oi .\IC{Cukla}.\ gi fo'a sinxa lo sisti cukla bo me'oi .bracket.\ noi ke'a selsni li vopa pe la .asycy'i'is.\ gi
	\end{itemize}
	\item ga je ko'a du la'oi .\IC{Vrici}.\ gi ga je ko'e du la'oi .\IC{Snile'u}.\ gi ko'i .asycy'i'is.\ sinxa lo selsni be fo'a
\end{itemize}

\begin{code}
record Lerfu : Set
  where
  field
    ctyp : LTyp
    case : Case
    bnam : Fin 128
\end{code}

\chapter{le vrici je fancu}
\section{la .\F{pamoin}.}
ni'o la .varik. na jinvi le du'u sarcu fa lo nu ciksi bau la .lojban.

\begin{code}
pamoin : ∀ {a} → {A : Set a}
       → ⦃ _ : Eq A ⦄
       → (x : A)
       → (xs : List A)
       → x ∈_ $ x ∷ₗ xs
pamoin x xs = sym $ begin
  length (take 1 $ filter (_≟_ x) $ x ∷ cevec xs) ≡⟨ refl ⟩
  LT (cevec xs) ≡⟨ DVP.toList∘fromList xs ▹ cong LT ⟩
  LT xs ≡⟨ refl ⟩
  length (take 1 $ filter (_≟_ x) $ x ∷ xs) ≡⟨ refl ⟩
  _ ≡⟨ DLP.filter-accept (x ≟_) refl ▹ cong (length ∘ take 1) ⟩
  length (take 1 $ x ∷ filter (_≟_ x) xs) ≡⟨ refl ⟩
  length (x ∷ []ₗ) ≡⟨ refl ⟩
  1 ∎
  where
  cevec = toList ∘ fromList
  open Data.List
    using (
      filter;
      take
    )
  LT = length ∘ take 1 ∘ filter (_≟_ x) ∘ (x ∷_)
  open ≡-Reasoning
\end{code}

\section{la'oi .\F{liftx}.}
ni'o lo jalge be tu'a la'oi .\B x.\ cu jalge tu'a la'o zoi.\ \F{liftx} \B x\ .zoi.

\begin{code}
liftx : ∀ {a} → PIO ABU.⊤ → IO {a} ⊤
liftx q = liftᵢₒ $ q >>=ₚᵢₒ λ _ → IO.Primitive.return _
\end{code}

\section{la'oi .\F{intersperse}.}
ni'o la .varik.\ na birti lo du'u ciksi la'oi .\F{intersperse}.\ bau la .lojban.\ fo ma kau poi ke'a zabna

\begin{code}
intersperse : ∀ {a} → {n : ℕ} → {A : Set a}
            → (t : A) → (q : Vec A n)
            → Vec A $ n * 2 ∸ 1
intersperse _ []ᵥ = []ᵥ
intersperse _ q@(_ ∷ᵥ []ᵥ) = q
intersperse t (x ∷ᵥ y ∷ᵥ z) = x ∷ t ∷ intersperse t (y ∷ᵥ z)
\end{code}

\subsection{le ctaipe be le su'u la'oi .\F{intersperse}.\ mapti}

\begin{code}
module IntersperseVeritas where
  nada : ∀ {a} → {A : Set a}
       → (t : A)
       → (x : Vec A 0)
       → intersperse t x ≡ x
  nada _ []ᵥ = refl

  pav : ∀ {a} → {A : Set a}
      → (t : A)
      → (x : Vec A 1)
      → intersperse t x ≡ x
  pav _ (_ ∷ᵥ []ᵥ) = refl

  module Snaredunli where
    mlecavu'u : (m n : ℕ)
              → m ℕ.< n
              → m * 2 ℕ.< n * 2 ∸ 1
    mlecavu'u m n (ℕ.s≤s ℕ.z≤n) = {!!}
    mlecavu'u m n (ℕ.s≤s s) = {!!}

    snaredunli : ∀ {a} → {n : ℕ} → {A : Set a}
               → 2 ℕ.≤ n
               → (t : A)
               → (q : Vec A n)
               → (x : Fin n)
               → (_≡_
                   (Data.Vec.lookup q x)
                   (Data.Vec.lookup
                     (intersperse t q)
                     (fromℕ<
                       {toℕ x * 2}
                       (mlecavu'u _ _ $ DFP.toℕ<n x))))
    snaredunli _ t (q₁ ∷ᵥ q₂ ∷ᵥ []ᵥ) x = {!!}
    snaredunli M t (q₁ ∷ᵥ xs) x = {!!}

  snaredunli = Snaredunli.snaredunli

  even : ∀ {a} → {n : ℕ} → {A : Set a}
       → 2 ℕ.≤ n
       → (t : A)
       → (q : Vec A n)
       → (x : Fin $ n * 2 ∸ 1)
       → 1 ≡ toℕ x % 2
       → t ≡ flip Data.Vec.lookup x (intersperse t q)
  even _ t (_ ∷ᵥ _ ∷ᵥ _) (Fin.suc Fin.zero) d = refl
  even z t (_ ∷ᵥ _ ∷ᵥ x) (Fin.suc (Fin.suc n)) d = {!!}
\end{code}

\section{la'oi .\F{plicu'a}.}
ni'o ga jonai ga je ga je la'oi .\B K.\ vasru la'o zoi.\ \B x \OpF , \B z .zoi.\ gi la'oi .\B q.\ selvau la'oi .\B x.\ gi\ldots
\begin{itemize}
	\item ko'a goi la'o zoi.\ \F{plicu'a} \B q \B n \B K .zoi.\ du la'oi .\B z.\ gi
	\item ga jonai ko'a du la'oi .\B n.\ gi ga je li pa mleca lo nilzilcmi be la'oi .\B k.\ gi ko'a du la'o zoi.\ \F{plicu'a} \B q \B n \OpF \$ \F{tail} \B K .zoi.
\end{itemize}

\begin{code}
plicu'a : ∀ {a b} → {A : Set a} → {B : Set b}
        → ⦃ Eq B ⦄
        → B → A → List $ List B × A → A
plicu'a _ d []ₗ = d
plicu'a q d ((a , b) ∷ₗ xs) = if (q ∈ᵇ a) b $ plicu'a q d xs
  where
  _∈ᵇ_ = λ x z → isYes $ Dec (x ∈ z) ∋ _ ≟ _
\end{code}

\subsection{le ctaipe be le su'u la \F{plicu'a}\ cu mapti}

\begin{code}
module Plicu'aVeritas where
  non : ∀ {a b} → {A : Set a} → {B : Set b}
      → ⦃ _ : Eq B ⦄
      → (x : B)
      → (d : A)
      → d ≡ plicu'a x d []ₗ
  non _ _ = refl

  nin : ∀ {a b} → {A : Set a} → {B : Set b}
      → ⦃ _ : Eq B ⦄
      → (x : B)
      → (d : A)
      → (L : List $ List B × A)
      → x ∉_ $ Data.List.concat $ mapₗ proj₁ L
      → d ≡ plicu'a x d L
  nin x d []ₗ n = {!!}
  nin x d (L₀ ∷ₗ Lₓ) n = {!!}

  pamois : ∀ {a b} → {A : Set a} → {B : Set b}
         → ⦃ _ : Eq B ⦄
         → (q : B)
         → (d z : A)
         → (L : List B)
         → (M : List $ List B × A)
         → q ∈ L
         → z ≡_ $ plicu'a q d $ (L , z) ∷ M
  pamois q d z L M j = sym $ begin
    plicu'a q d ((L , z) ∷ M) ≡⟨ refl ⟩
    if (isYes P) z c ≡⟨ isYes≗does P ▹ cong k ⟩
    if (Dec.does P) z c ≡⟨ dec-true P j ▹ cong k ⟩
    if true z c ≡⟨ refl ⟩
    z ∎
    where
    P = _ ≟ _
    c = plicu'a q d M
    k = λ n → if n z c
    dec-true = Relation.Nullary.Decidable.dec-true
    open ≡-Reasoning

  napamois : ∀ {a b} → {A : Set a} → {B : Set b}
           → ⦃ _ : Eq B ⦄
           → (q : B)
           → (d : A)
           → (L : List B × A)
           → (M : List $ List B × A)
           → ¬ (q ∈ proj₁ L)
           → plicu'a q d M ≡ plicu'a q d (L ∷ M)
  napamois q d L M j = sym $ begin
    plicu'a q d (L ∷ M) ≡⟨ refl ⟩
    if (isYes P) (proj₂ L) c ≡⟨ isYes≗does P ▹ cong k ⟩
    if (Dec.does P) (proj₂ L) c ≡⟨ dec-false P j ▹ cong k ⟩
    if false (proj₂ L) c ≡⟨ refl ⟩
    c ≡⟨ refl ⟩
    plicu'a q d M ∎
    where
    c = plicu'a q d M
    k = λ n → if n (proj₂ L) c
    P = Dec (q ∈ proj₁ L) ∋ _ ≟ _
    dec-false = Relation.Nullary.Decidable.dec-false
    open ≡-Reasoning
\end{code}

\chapter{le skicu fancu}
\section{la'oi .\F{intdMm}.}
ni'o la'o zoi.\ \F{intdMm} \B a \B b .zoi.\ porsi lo'i ro kacna'u poi ke'a dubjavmau la'oi .\B a.\ je cu dubjavme'a la'oi .\B b.

\begin{code}
intdMm : ℕ → ℕ → List ℕ
intdMm a = drop a ∘ upTo ∘ suc
\end{code}

\subsection{le ctaipe be le su'u la'oi .\F{intdMm}.\ mapti}

\begin{code}
module IntdMmVeritas where
  open ≡-Reasoning

  zmadu : (x z : ℕ)
        → x ℕ.> z
        → intdMm x z ≡ []ₗ
  zmadu x z zm = begin
    intdMm x z ≡⟨ refl ⟩
    drop x (upTo $ suc z) ≡⟨ drolen x _ zm₂ ⟩
    []ₗ ∎
    where
    zm₂ : x ℕ.≥_ $ length $ upTo $ suc z
    zm₂ = zm ▹ subst (x ℕ.≥_) (DLP.length-upTo _ ▹ sym)
    drolen : ∀ {a} → {A : Set a}
           → (n : ℕ)
           → (L : List A)
           → n ℕ.≥ length L
           → drop n L ≡ []ₗ
    drolen 0 List.[] _ = refl
    drolen (suc n) List.[] _ = refl
    drolen (suc n) (_ List.∷ xs) (ℕ.s≤s s) = drolen n xs s

  mlesuk : {x z : ℕ}
         → x ℕ.≤ z
         → ∃ $ _≡_ (length $ intdMm x z) ∘ ℕ.suc
  mlesuk = {!!}

  nymois : (x z : ℕ)
         → x ℕ.≤ z
         → (f : Fin $ length $ intdMm x z)
         → (_≡_
             (Data.List.lookup (intdMm x z) f)
             (toℕ f ℕ.+ x))
  nymois x z s f with mink f $ mlesuk s ▹ proj₂
  ... | 𝔽.zero = {!!}
  ... | 𝔽.suc f = {!!}

  pamois : (x z : ℕ)
         → x ℕ.≤ z
         → Data.List.head (intdMm x z) ≡ just x
  pamois x z djm =  nymoij 0' ▹ subst₂ _≡_ (x!0'≡⊃x _ _ {!!} ▹ sym) (0'+x≡x ▹ cong just)
    where
    0' = mink 𝔽.zero $ mlesuk djm ▹ proj₂ ▹ sym
    nymoij = cong just ∘ nymois x z djm
    0'+x≡x : toℕ 0' ℕ.+ x ≡ x
    0'+x≡x = begin
      toℕ 0' ℕ.+ x ≡⟨ {!!} ⟩
      x ∎
    x!0'≡⊃x : ∀ {a} → {A : Set a}
            → (x : List A)
            → (f : Fin $ length x)
            → toℕ f ≡ 0
            → (_≡_
                (Data.List.head x)
                (just $ Data.List.lookup x f))
    x!0'≡⊃x = {!!}

  romois : (x z : ℕ)
         → x ℕ.≤ z
         → Data.List.last (intdMm x z) ≡ just z
  romois x z djm = nymoij oz ▹ subst₂ _≡_ {!!} {!!}
    where
    nymoij = cong just ∘ nymois x z djm
    oz = 𝔽.opposite $ mink 𝔽.zero $ mlesuk djm ▹ sp₂
      where
      sp₂ = sym ∘ proj₂

  drodun : (m n : ℕ)
         → (_≡_
             (intdMm m n)
             (drop m $ upTo $ suc n))
  drodun _ _ = refl
\end{code}

\section{la'oi .\F{toBnam}.}

\begin{code}
toBnam : Fin 128 → ℕ
toBnam q = plicu'a q' q' ns
  where
  q' = toℕ q
  ns : List $ List ℕ × ℕ
  ns = (du40 , 40) ∷ (cmalu , q' ∸ 32) ∷ []ₗ
    where
    du40 = 40 ∷ 41 ∷ 60 ∷ 62 ∷ 91 ∷ 93 ∷ 123 ∷ 125 ∷ []ₗ
    cmalu = intdMm 97 122
\end{code}

\section{la'oi .\F{toCase}.}
\newcommand\BQ{la'oi .\B q.}
\newcommand\toCase{la'o zoi.\ \F{toCase} \B q .zoi.}

ni'o ga jonai \toCase\ du la'oi .\IC{Snile'u}.\ gi\ldots
\begin{itemize}
	\item ga jonai ga je \BQ\ dubjavmau li vobi je cu mleca li mubi gi \toCase\ du la'oi .\IC{Namcu}.\ gi
        \item ga jonai ga je \BQ\ dubjavmau li xamu je cu mleca li \sopa\ gi \toCase\ du la'oi .\IC{Barda}.\ gi
        \item ga jonai ga je \BQ\ dubjavmau li soze je cu mleca li pareci gi \toCase\ du la'oi .\IC{Cmalu}.\ gi
        \item ga jonai ga je \BQ\ du li vono ja li vopa gi \toCase\ du la'oi .\IC{Cukla}.\ gi
        \item ga jonai ga je \BQ\ du li xano ja li xare gi \toCase\ du la'oi .\IC{Jganu}.\ gi
        \item ga jonai ga je \BQ\ du li \sopa\ ja li soci gi \toCase\ du la'oi .\F{Kurfa}.\ gi
        \item ga je \BQ\ du li pareci ja li paremu gi \toCase\ du la'oi .\F{Curly}.
\end{itemize}

\begin{code}
toCase : Fin 128 → Case
toCase q = plicu'a (toℕ q) Snile'u ns
  where
  ns : List $ List ℕ × Case
  ns = (cukla , Cukla) ∷ (namcu , Namcu) ∷
       (jganu , Jganu) ∷ (barda , Barda) ∷
       (kurfa , Kurfa) ∷ (tcekr , Tcekr) ∷
       (cmalu , Cmalu) ∷ []ₗ
    where
    namcu = intdMm 48 57
    barda = intdMm 65 90
    cmalu = intdMm 97 122
    cukla = 40 ∷ 41 ∷ []ₗ
    jganu = 60 ∷ 62 ∷ []ₗ
    kurfa = 91 ∷ 93 ∷ []ₗ
    tcekr = 123 ∷ 125 ∷ []ₗ
\end{code}

\section{la'oi .\F{toLtyp}.}

\begin{code}
toLtyp : Fin 128 → LTyp
toLtyp q = plicu'a (toℕ q) Vrici ns
  where
  ns : List $ List ℕ × LTyp
  ns = (kalri , Kalri) ∷ (ganlo , Ganlo) ∷
       (xrabo , Xrabo) ∷ (latmo , Latmo) ∷ []ₗ
    where
    kalri = 40 ∷ 60 ∷ 91 ∷ 123 ∷ []ₗ
    ganlo = 41 ∷ 61 ∷ 93 ∷ 125 ∷ []ₗ
    latmo = intdMm 65 90 ++ intdMm 97 122
    xrabo = intdMm 48 57
\end{code}

\section{la'oi .\F{toLerfu}.}
ni'o ga jonai ga je la'oi .\B n.\ mleca li parebi gi ko'a goi la'o zoi.\ \F{toLerfu} \B n .zoi.\ me'oi .\IC{just}.\ be lo sinxa lo .asycy'i'is.\ lerfu poi ke'a meirmoi la'oi .\B n.\ fo le'i ro .asyci'is.\ lerfu gi ko'a me'oi .\IC{nothing}.

\begin{code}
module ToLerfu where
  _<?'_ : (m n : ℕ) → Maybe $ m ℕ.< n
  _<?'_ = decToMaybe ∘₂ ℕ._<?_

  finToLerfu : Fin 128 → Lerfu
  finToLerfu a = record {ctyp = toLtyp a; case = toCase a; bnam = a}

  toLerfu : ℕ → Maybe Lerfu
  toLerfu n = Data.Maybe.map (finToLerfu ∘ fromℕ<) $ n <?' _

open ToLerfu
  using (
    toLerfu
  )
\end{code}

\subsection{le ctaipe be le su'u la'oi .\F{toLerfu}.\ mapti}

\begin{code}
module ToLerfuVeritas where
  open ToLerfu

  module _<?'_ where
    nada : {m n : ℕ} → ¬_ $ m ℕ.< n → m <?' n ≡ nothing
    nada {m} {n} N = begin
      m <?' n ≡⟨ refl ⟩
      decToMaybe (m ℕ.<? n) ≡⟨ DN ▹ proj₂ ▹ cong decToMaybe ⟩
      decToMaybe (no $ proj₁ DN) ≡⟨ refl ⟩
      nothing ∎
      where
      DN = Relation.Nullary.Decidable.dec-no (m ℕ.<? n) N
      open ≡-Reasoning

    jus : {m n : ℕ} → (ml : m ℕ.< n) → m <?' n ≡ just ml
    jus {m} {n} ml = begin
      m <?' n ≡⟨ refl ⟩
      decToMaybe (m ℕ.<? n) ≡⟨ DY ▹ proj₂ ▹ cong decToMaybe ⟩
      decToMaybe (yes $ proj₁ DY) ≡⟨ refl ⟩
      _ ≡⟨ <≡< _ _ ▹ cong (decToMaybe ∘ yes) ⟩
      decToMaybe (yes ml) ≡⟨ refl ⟩
      just ml ∎
      where
      open ≡-Reasoning
      DY = Relation.Nullary.Decidable.dec-yes _ ml
      <≡< : {m n : ℕ} → (x z : m ℕ.< n) → x ≡ z
      <≡< = DNP.≤-irrelevant

  mleca : {n : ℕ}
        → n ℕ.< 128
        → ∃ $ (toLerfu n ≡_) ∘ just
  mleca {n} m = _ , d
    where
    open ≡-Reasoning
    d = begin
      toLerfu n ≡⟨ refl ⟩
      mapₘ (finToLerfu ∘ fromℕ<) (n <?' _) ≡⟨ refl ⟩
      _ ≡⟨ DY ▹ proj₂ ▹ cong (mapₘ fℕ< ∘ decToMaybe) ⟩
      mapₘ (finToLerfu ∘ fromℕ< {m = n}) (just _) ≡⟨ refl ⟩
      just (finToLerfu $ fromℕ< {m = n} _) ≡⟨ refl ⟩
      just _ ∎
      where
      fℕ< = finToLerfu ∘ fromℕ<
      DY = Relation.Nullary.Decidable.dec-yes (_ ℕ.<? _) m

  dubjavmau : {n : ℕ}
            → n ℕ.≥ 128
            → toLerfu n ≡ nothing
  dubjavmau {n} djz = begin
    toLerfu n ≡⟨ refl ⟩
    mapₘ (finToLerfu ∘ fromℕ<) (n <?' _) ≡⟨ {!!} ⟩
    nothing ∎
    where
    open ≡-Reasoning
\end{code}

\section{la'oi .\F{lerste}.}
ni'o ga jonai la'oi .\IC{nothing}.\ du ko'a goi la'o zoi.\ \F{lerste} \B x.\ .zoi.\ gi ga je la'oi .\B x.\ .aski gi ga je nilzilcmi ko'a fa lo nilzilcmi be la'oi .\B x.\ gi ro da poi ke'a kacna'u je cu mleca lo nilzilcmi be ko'a zo'u lo meirmoi be da bei fo ko'a cu sinxa lo meirmoi be da bei la'oi .\B x.

\begin{code}
module Lerste where
  sikh : ∀ {a} → {A : Set a} → List $ Maybe A → Maybe $ List A
  sikh []ₗ = just []ₗ
  sikh (nothing ∷ₗ _) = nothing
  sikh (just x ∷ₗ xs) = Data.Maybe.map (x ∷_) $ sikh xs

  f : Char → Maybe Lerfu
  f = toLerfu ∘ Data.Char.toℕ

  lerste : String → Maybe $ List Lerfu
  lerste = sikh ∘ mapₗ f ∘ 𝕊.toList

open Lerste
  using (
    lerste
  )
\end{code}

\subsection{le ctaipe be le su'u la'oi .\F{lerste}.\ mapti}

\begin{code}
module LersteVeritas where
  open Lerste

  module Sikh where
    faivos : ∀ {a} → {A : Set a}
           → (j : List A)
           → just j ≡ sikh (mapₗ just j)
    faivos []ₗ = refl
    faivos (x ∷ₗ y) = faivos y ▹ cong (Data.Maybe.map $ x ∷_)

    faivuyn : ∀ {a} → {A : Set a}
            → (x z : List $ Maybe A)
            → nothing ≡ sikh (x ++ nothing ∷ₗ z)
    faivuyn []ₗ _ = refl
    faivuyn (nothing ∷ₗ _) _ = refl
    faivuyn (just x ∷ₗ xs) t = faivuyn xs t ▹ cong (mapₘ $ x ∷_)

    em : ∀ {a} → {A : Set a}
       → (x : Maybe A)
       → (xs : List $ Maybe A)
       → let _∷ₘ_ = Data.Maybe.ap ∘ mapₘ _∷_ in
         sikh (x ∷ xs) ≡ x ∷ₘ sikh xs
    em (just x) xs = {!!}
    em nothing xs = {!!}

  private
    toList-∷ : {x : Char}
             → (z : String)
             → 𝕊.toList (x ∷ z) ≡ x ∷ 𝕊.toList z
    toList-∷ = {!!}

  kunti : lerste "" ≡ just []ₗ
  kunti = refl

  module F where
    nada : (c : Char)
         → Data.Char.toℕ c ℕ.≥ 128
         → Is-nothing $ f c
    nada c djz = x≡nothing→Is-nothing[x] $ begin
      f c ≡⟨ refl ⟩
      toLerfu c' ≡⟨ refl ⟩
      Data.Maybe.map f2l< (c' <?' _) ≡⟨ refl ⟩
      _ ≡⟨ _<?'_≡nothing ▹ cong (Data.Maybe.map f2l<) ⟩
      Data.Maybe.map f2l< (nothing {A = c' ℕ.< 128}) ≡⟨ refl ⟩
      nothing ∎
      where
      c' = Data.Char.toℕ c
      _<?'_ = ToLerfu._<?'_
      f2l< : {n : ℕ} → n ℕ.< 128 → Lerfu
      f2l< = ToLerfu.finToLerfu ∘ fromℕ<
      x≡nothing→Is-nothing[x] : ∀ {a} → {A : Set a}
                              → {x : Maybe A}
                              → x ≡ nothing
                              → Is-nothing x
      x≡nothing→Is-nothing[x] refl = DMA.All.nothing
      open ≡-Reasoning
      _<?'_≡nothing : c' <?' _ ≡ nothing
      _<?'_≡nothing = begin
        c' <?' _ ≡⟨ refl ⟩
        decToMaybe (c' ℕ.<? _) ≡⟨ proj₂ DN ▹ cong decToMaybe ⟩
        decToMaybe (no $ proj₁ DN) ≡⟨ refl ⟩
        nothing ∎
        where
        DN = dec-no (c' ℕ.<? _) $ DNP.≤⇒≯ djz
          where
          dec-no = Relation.Nullary.Decidable.dec-no

    mleca-just : (c : Char)
               → Data.Char.toℕ c ℕ.< 128
               → Data.Maybe.Is-just $ f c
    mleca-just c s = x≡j→J[x] $ ToLerfuVeritas.mleca s
      where
      x≡j→J[x] : ∀ {a} → {A : Set a}
               → {x : Maybe A}
               → ∃ $ _≡_ x ∘ just
               → Data.Maybe.Is-just x
      x≡j→J[x] (_ , refl) = DMAny.just _

    nada₂ : (c : Char)
          → Is-nothing $ f c
          → Data.Char.toℕ c ℕ.≥ 128
    nada₂ c n with Data.Char.toℕ c ℕ.≥? 128
    ... | yes z = z
    ... | no m = n ⇒⇐ J→¬N (ToLerfuVeritas.mleca $ ≱⇒< m)
      where
      J→¬N : ∀ {a} → {A : Set a}
           → {x : Maybe A}
           → ∃ $ _≡_ x ∘ just
           → ¬_ $ Is-nothing x
      J→¬N = {!!}
      ≱⇒< : {m n : ℕ} → ¬_ $ m ℕ.≥ n → m ℕ.< n
      ≱⇒< = DNP.≰⇒>

  naljmina : (x : Char)
           → (xs : String)
           → Is-nothing $ f x
           → lerste (x ∷ xs) ≡ nothing
  naljmina x xs N = begin
    lerste (x ∷ xs) ≡⟨ refl ⟩
    sikh (mapₗ f $ 𝕊.toList $ x ∷ xs) ≡⟨ refl ⟩
    _ ≡⟨ toList-∷ xs ▹ cong (sikh ∘ mapₗ f) ⟩
    sikh (mapₗ f $ x ∷ 𝕊.toList xs) ≡⟨ refl ⟩
    sikh (mapₗ f $ x ∷ xs') ≡⟨ refl ⟩
    _ ≡⟨ DLP.map-++-commute f (x ∷ []ₗ) xs' ▹ cong sikh ⟩
    sikh (f x ∷ mapₗ f xs') ≡⟨ refl ⟩
    _ ≡⟨ apin N ▹ cong (λ i → sikh $ i ∷ mapₗ f _ ) ⟩
    sikh (nothing ∷ mapₗ f xs') ≡⟨ refl ⟩
    sikh (nothing ∷ mapₗ f (𝕊.toList xs)) ≡⟨ refl ⟩
    nothing ∷ₘ lerste xs ≡⟨ refl ⟩
    nothing ∎
    where
    xs' = 𝕊.toList xs
    _∷ₘ_ = Data.Maybe.ap ∘ mapₘ _∷_
    apin : ∀ {a} → {A : Set a}
         → {x : Maybe A}
         → Is-nothing x
         → x ≡ nothing
    apin DMA.nothing = refl
    open ≡-Reasoning

  jmina : (x : Char)
        → (xs : String)
        → (j : Data.Maybe.Is-just $ f x)
        → let j' = Data.Maybe.to-witness j in
          lerste (x ∷ xs) ≡ mapₘ (j' ∷ₗ_) (lerste xs)
  jmina x xs j = begin
    lerste (x ∷ xs) ≡⟨ refl ⟩
    sikh (mapₗ f $  𝕊.toList $ x ∷ xs) ≡⟨ refl ⟩
    _ ≡⟨ toList-∷ xs ▹ cong (sikh ∘ mapₗ f) ⟩
    sikh (mapₗ f $  x ∷ 𝕊.toList xs) ≡⟨ refl ⟩
    sikh (f x ∷_ $ mapₗ f $ 𝕊.toList xs) ≡⟨ Sikh.em (f x) _ ⟩
    f x ∷ₘ sikh (mapₗ f $ 𝕊.toList xs) ≡⟨ refl ⟩
    f x ∷ₘ lerste xs ≡⟨ tuig j ▹ cong (_∷ₘ lerste xs) ⟩
    just j' ∷ₘ lerste xs ≡⟨ refl ⟩
    mapₘ (j' ∷ₗ_) (lerste xs) ∎
    where
    _∷ₘ_ = Data.Maybe.ap ∘ mapₘ _∷_
    j' = Data.Maybe.to-witness j
    open ≡-Reasoning
    tuig : ∀ {a} → {A : Set a}
         → {x : Maybe A}
         → (j : Data.Maybe.Is-just x)
         → x ≡ just (Data.Maybe.to-witness j)
    tuig (DMAny.just x) = refl

  nada : (xs : String)
       → lerste xs ≡ nothing
       → ∃ $ λ x → x ∈ xs × Is-nothing (f x)
  nada "" ()
  nada s d with 𝕊.toList s
  ... | (x ∷ₗ xs) with D $ f x
    where
    D : ∀ {a} → {A : Set a}
      → (x : Maybe A)
      → Dec $ Is-nothing x
    D nothing = yes DMA.All.nothing
    D (just j) = no {!!}
  ... | yes n = x , pamoin x xs , n
  ... | no j = {!!} ▹ nada₂
    where
    F : List Char → Set
    F xs = ∃ $ λ x → x ∈ xs × Is-nothing (f x)
    nada₂ : {x : Char} → {xs : List Char} → F xs → F $ x ∷ xs
    nada₂ {x} {xs} (x₁ , c , N) = x₁ , jminin x xs c , N
      where
      jminin : ∀ {a} → {A : Set a}
             → ⦃ _ : Eq A ⦄
             → (x : A)
             → (xs : List A)
             → {z : A}
             → z ∈ xs
             → z ∈_ $ x ∷ xs
      jminin x xs {z} d with x ≟ z
      ... | yes d₂ = pamoin z xs ▹ subst _ (sym d₂)
      ... | no j = d ▹ subst (_ ≡_) {!!}

  kunti₂ : (s : String)
         → lerste s ≡ just []ₗ
         → s ≡ ""
  kunti₂ s d with s ≟ ""
  ... | yes k = k
  ... | no n = d ⇒⇐ ¬d
    where
    ¬d : ¬_ $ lerste s ≡ just []ₗ
    ¬d with 𝕊.toList s
    ... | []ₗ = {!!} ⇒⇐ (n ∘ strikun s)
      where
      strikun : (s : String) → 𝕊.toList s ≡ []ₗ → s ≡ ""
      strikun = {!!}
    ... | (x ∷ₗ xs) with f x
    ... | nothing = λ ()
    ... | just x' = {!!}
\end{code}

\chapter{le fancu poi ke'a srana lo .uniks.\ midnoi}

\section{la'oi .\F{spkCL}.}
ni'o \selsnap{\F{spkCL} \B x}{lo me'oi .\AgdaField{Lerfu.ctyp}.\ be la'oi .\B x.}

\begin{code}
spkCL : Lerfu → Midnoi
spkCL q = "mplayer " ++ ddvs ++ f (Lerfu.ctyp q)
  where
  f : LTyp → String
  f = map ⦃ liliString ⦄ ⦃ liliString ⦄ Data.Char.toLower ∘ show
\end{code}

\section{la'oi .\F{spkCC}.}
ni'o \selsnap{\F{spkCC} \B x}{lo me'oi .case.\ be la'oi .\B x.}

\begin{code}
spkCC : Lerfu → Midnoi
spkCC q = "mplayer " ++ ddvs ++ f (Lerfu.case q)
  where
  f : Case → String
  f = map ⦃ liliString ⦄ ⦃ liliString ⦄ Data.Char.toLower ∘ show
\end{code}

\section{la'oi .\F{spkCF}.}
ni'o \selsnap{\F{spkCF} \B x}{lo me'oi .\AgdaField{Lerfu.bnam}.\ be la'oi .\B x.}

\begin{code}
spkCF : Lerfu → Midnoi
spkCF q = "mplayer " ++ ddvs ++ f (Lerfu.bnam q)
  where
  f : Fin 128 → String
  f = show ∘ toℕ
\end{code}

\section{la \F{denpa}}
ni'o lo nu drani .uniks.\ bo co'e la'o zoi.\ \F{denpa}\ \B f\ .zoi.\ cu rinka lo nu snidu la'oi .\B f.\ fa lo nu denpa

\begin{code}
denpa : Float → Midnoi
denpa = ("sleep " ++_) ∘ show
\end{code}

\section{la'oi .\F{sequin}.}
ni'o ga jonai la'oi .\IC{nothing}.\ du ko'e goi la'o zoi.\ \F{sequin} \B n .zoi.\ gi ga je ko'a goi la'oi .\B n.\ vasru lo me'oi .\IC{just}.\ gi ko'e pa moi lo'i ro me'oi .\IC{just}.\ poi ke'a selvau ko'a

\begin{code}
sequin : ∀ {a} → {A : Set a} → List $ Maybe A → Maybe A
sequin = Data.List.head ∘ Data.List.mapMaybe id

module SequinVeritas where
  pamoi : ∀ {a} → {A : Set a}
        → (x : List $ Maybe A)
        → (z : A)
        → just z ≡ sequin (just z ∷ x)
  pamoi _ _ = refl

  nymois : ∀ {a} → {A : Set a}
         → (m : ℕ)
         → (x : List $ Maybe A)
         → (z : A)
         → (_≡_
             (just z)
             (sequin $ Data.List.replicate m nothing ++ just z ∷ₗ x))
  nymois 0 _ _ = refl
  nymois (suc n) = nymois n

  nada : ∀ {a} → {A : Set a}
       → sequin []ₗ ≡ nothing {A = A}
  nada = refl

  pamoi-nada : ∀ {a} → {A : Set a}
             → {x : Maybe A}
             → {xs : List $ Maybe A}
             → sequin (x ∷ xs) ≡ nothing
             → Is-nothing x
  pamoi-nada {x = nothing} _ = DMA.All.nothing
  pamoi-nada {x = just x} = λ ()

  pamoi-nada-just : ∀ {a} → {A : Set a}
                  → {x : Maybe A}
                  → {xs : List $ Maybe A}
                  → Data.Maybe.Is-just $ sequin $ x ∷ xs
                  → Data.Maybe.Is-nothing x
                  → Data.Maybe.Is-just $ sequin xs
  pamoi-nada-just {xs = just _ ∷ₗ _} j DMA.nothing = DMAny.just _
  pamoi-nada-just {xs = nothing ∷ₗ xs} j DMA.nothing = P
    where
    P = pamoi-nada-just {xs = xs} j DMA.nothing

  nada₂ : ∀ {a} → {A : Set a}
        → (x : List $ Maybe A)
        → sequin x ≡ nothing
        → DLA.All Is-nothing x
  nada₂ []ₗ d = DLA.All.[]
  nada₂ (x ∷ₗ xs) d = pamoi-nada d DLA.All.∷ nada₂ xs (romoi-nada x xs d)
    where
    romoi-nada : ∀ {a} → {A : Set a}
               → (x : Maybe A)
               → (xs : List $ Maybe A)
               → sequin (x ∷ xs) ≡ nothing
               → sequin xs ≡ nothing
    romoi-nada x []ₗ d = nada
    romoi-nada x xs@(just z ∷ₗ zs) d = J ⇒⇐ N→¬J x xs (x≡N→N[x] d)
      where
      J : Data.Maybe.Is-just $ sequin $ just z ∷ₗ zs
      J = DMAny.just _
      x≡N→N[x] : ∀ {a} → {A : Set a}
               → {x : Maybe A}
               → x ≡ nothing
               → Is-nothing x
      x≡N→N[x] refl = DMA.nothing
      N→¬J : ∀ {a} → {A : Set a}
           → (x : Maybe A)
           → (xs : List $ Maybe A)
           → Is-nothing $ sequin $ x ∷ xs
           → ¬_ $ Data.Maybe.Is-just $ sequin xs
      N→¬J x []ₗ N ()
      N→¬J x (just z ∷ₗ zs) N = N ⇒⇐ J→¬N {!!}
        where
        J→¬N : ∀ {a} → {A : Set a}
             → {x : Maybe A}
             → Data.Maybe.Is-just x
             → ¬_ $ Is-nothing x
        J→¬N {x = just x} J N = J→∃ (just x) J ⇒⇐ {!!}
          where
          J→∃ : ∀ {a} → {A : Set a}
              → (x : Maybe A)
              → Data.Maybe.Is-just x
              → ∃ $ (x ≡_) ∘ just
          J→∃ (just _) (DMAny.just _) = _ , refl
        J→¬N {x = nothing} = λ ()
      N→¬J x (nothing ∷ₗ zs) N = N→¬J nothing zs {!!}
    romoi-nada x (nothing ∷ₗ zs) d = romoi-nada x zs {!!}

  anis : ∀ {a} → {A : Set a}
       → (x : List $ Maybe A)
       → Data.Maybe.Is-just $ sequin x
       → DLAny.Any Data.Maybe.Is-just x
  anis []ₗ ()
  anis (just x ∷ₗ xs) j = DLAny.here $ DMAny.just _
  anis (nothing ∷ₗ xs) = DLAny.there ∘ anis xs
\end{code}

\section{la'oi .\F{doit}.}
ni'o tu'a la'o zoi.\ \F{doit} \B s\ .zoi.\ rinka lo nu .uniks.\ co'e la'oi .\B s.\  .i ga jonai ga je .indika lo du'u snada fa tu'a ko'a goi la'o zoi.\ \F{doit} \B s\ .zoi.\ gi ko'a me'oi .\F{pure}.\ la'oi .\IC{nothing}.\ gi ko'a me'oi .\F{pure}.\ lo me'oi .\IC{just}.\ be lo mu'oi glibau.\ exit code .glibau.\ poi tu'a ko'a rinka tu'a ke'a

\begin{code}
doit : String → IO $ Maybe ℕ
doit = _<$>ᵢₒ_ bixygau ∘ liftᵢₒ ∘ doit'
  where
  bixygau = λ n → if (n ℕ.<ᵇ 127) nothing $ just n
  postulate doit' : String → PIO ℕ
  {-# FOREIGN GHC import System.IO #-}
  {-# FOREIGN GHC import Data.Text #-}
  {-# FOREIGN GHC import System.Exit #-}
  {-# FOREIGN GHC import System.Process #-}
  {-# COMPILE GHC
    doit' = fmap (fromIntegral . g . f) . rpwec . unpack
      where {
        f (a, _, _) = a;
        g (ExitFailure t) = t;
        g _ = 128;
        rpwec a = readProcessWithExitCode a [] [];
      }
  #-}
\end{code}

\section{la'oi .\F{spk}.}
ni'o \selsnap{\F{spk} \B q}{la'oi .\B q.}

\begin{code}
spk : Lerfu → IO $ Maybe ℕ
spk = mvm doit ∘ intersperse (denpa selsniduXiPa) ∘ spks
  where
  mvm : ∀ {a b} → {n : ℕ} → {A : Set a} → {B : Set b}
      → (A → IO $ Maybe B) → Vec A n → IO $ Maybe B
  mvm f = _<$>ᵢₒ_ sequin ∘ IO.List.mapM f ∘ toList
  spks : Lerfu → Vec Midnoi 3
  spks l = mapᵥ (_$ l) $ spkCL ∷ spkCC ∷ spkCF ∷ []ᵥ
\end{code}

\section{la'oi .\F{bacru}.}
ni'o \selsnap{\F{bacru} \B q}{la'oi .\B q.}

\begin{code}
bacru : List Lerfu → IO $ Maybe ℕ
bacru = _<$>ᵢₒ_ sequin ∘ IO.List.mapM spkJaDnp ∘ dej
  where
  denpaXiRe : IO $ Maybe ℕ
  denpaXiRe = doit $ "sleep " ++ show selsniduXiRe
  -- | ni'o zo .dej. cmavlaka'i lu denpa jmina li'u
  dej : List Lerfu → List $ Maybe Lerfu
  dej = Data.List.intersperse nothing ∘ mapₗ just
  spkJaDnp : Maybe Lerfu → IO $ Maybe ℕ
  spkJaDnp = maybe spk $ doit $ denpa selsniduXiRe
\end{code}

\section{la'oi .\F{main}.}

\begin{code}
main : Main
main = run $ getLine >>=ᵢₒ maybe evnc spojaPe'aRu'e ∘ lerste
  where
  postulate erroy : String → PIO ABU.⊤
  {-# COMPILE GHC erroy = hPutStrLn stderr . unpack #-}
  spojaPe'aRu'e : ∀ {a} → IO {a} ⊤
  spojaPe'aRu'e = liftx $ erroy $ jbo ++ "\n\n" ++ eng
    where
    jbo = "ni'o pruce lo lerfu poi \
          \ke'a tolmapti la .asycy'i'is."
    eng = "A non-ASCII character is input."
  -- | ni'o zo'oi .evnc. cmavlaka'i zo'oi .EVANNOUNCE.
  evnc : List Lerfu → IO ⊤
  evnc a = bacru a >>=ᵢₒ maybe (liftx ∘ erroy ∘ show) (pure tt)
\end{code}
\end{document}
