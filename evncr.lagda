\documentclass{article}

\usepackage{ar}
\usepackage{stix}
\usepackage[bw]{agda}
\usepackage{ifsym}
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
\newunicodechar{ℕ}{\ensuremath{\mathbb{N}}}
\newunicodechar{∈}{\ensuremath{\mathnormal\in}}
\newunicodechar{≡}{\ensuremath{\mathnormal\equiv}}
\newunicodechar{⟩}{\ensuremath{\mathnormal\rangle}}
\newunicodechar{∶}{\ensuremath{\mathnormal\colon\!\!}}
\newunicodechar{⊹}{\ensuremath{\mathnormal\dag}}
\newunicodechar{𝕗}{\ensuremath{\mathbb{f}}}
\newunicodechar{ℙ}{\ensuremath{\mathbb{P}}}
\newunicodechar{𝔽}{\ensuremath{\mathbb{F}}}
\newunicodechar{𝕄}{\ensuremath{\mathbb{M}}}
\newunicodechar{𝔹}{\ensuremath{\mathbb{B}}}
\newunicodechar{ν}{\ensuremath{\nu}}
\newunicodechar{μ}{\ensuremath{\mu}}
\newunicodechar{◆}{\ensuremath{\mathnormal\blackdiamond}}
\newunicodechar{∸}{\ensuremath{\mathnormal\dotdiv}}
\newunicodechar{ᵇ}{\ensuremath{^\mathrm{b}}}
\newunicodechar{≥}{\ensuremath{\mathnormal{\geq}}}
\newunicodechar{ϕ}{\ensuremath{\mathnormal{\phi}}}
\newunicodechar{χ}{\ensuremath{\mathnormal{\chi}}}
\newunicodechar{∧}{\ensuremath{\mathnormal{\wedge}}}
\newunicodechar{∅}{\ensuremath{\mathnormal{\emptyset}}}
\newunicodechar{∣}{\ensuremath{\mathnormal{|}}}
\newunicodechar{⁇}{\ensuremath{\mathrm{?\!?}}}
\newunicodechar{∘}{\ensuremath{\mathnormal{\circ}}}
\newunicodechar{∀}{\ensuremath{\forall}}
\newunicodechar{ℓ}{\ensuremath{\ell}}
\newunicodechar{σ}{\ensuremath{\sigma}}
\newunicodechar{₁}{\ensuremath{_1}}
\newunicodechar{₂}{\ensuremath{_2}}
% \newunicodechar{′}{\ensuremath{\mathnormal{'}}}
\newunicodechar{ₘ}{\ensuremath{_\mathsf{m}}}
\newunicodechar{ₛ}{\ensuremath{_\mathsf{s}}}
\newunicodechar{⊤}{\ensuremath{\mathnormal{\top}}}
\newunicodechar{◈}{\ensuremath{\diamond\hspace{-0.39em}\cdot}}
\newunicodechar{≤}{\ensuremath{\mathnormal{\leq}}}
\newunicodechar{⍉}{\ensuremath{∘\hspace{-0.455em}\backslash}}
\newunicodechar{⦃}{\ensuremath{\mathnormal{\lBrace}}}
\newunicodechar{⦄}{\ensuremath{\mathnormal{\rBrace}}}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound

\begin{document}
\begin{code}
{-# OPTIONS --guardedness #-}

open import IO
open import Data.Fin
open import Data.Nat
open import Data.Vec
  hiding (
    _++_;
    drop
  )
open import Function
open import Data.Bool
open import Data.List
  using (
    List;
    _++_;
    [];
    upTo;
    drop;
    _∷_
  )
open import Data.Float
  using (
    Float;
    show
  )
open import Data.Maybe
  renaming (
    map to mapₘ
  )
open import Data.String
  renaming (
    _++_ to _++ₛ_
  )
  using (
    String
  )
open import Data.Product
  using (
    _×_;
    _,_
  )
open import Data.List.NonEmpty
open import Category.Applicative
open import Data.Maybe.Instances
open import Data.Unit.Polymorphic
open import Relation.Binary.PropositionalEquality

postulate selsniduXiPa : Float
\end{code}

\section{le me'oi .\AgdaKeyword{data}.}

\subsection{la'oi .\D{Midnoi}.}
ni'o ro da poi me'oi .\D{Midnoi}.\ zo'u da sinxa lo .uniks.\ midnoi

\begin{code}
Midnoi : Set
Midnoi = String
\end{code}

\subsection{la'oi .\D{Case}.}

\begin{code}
data Case : Set
  where
  Barda : Case
  Cmalu : Case
  Namcu : Case
  Curly : Case
  Kurfa : Case
  Cukla : Case
  Jganu : Case
  Snile'u : Case
\end{code}

\subsection{la'oi .\F{LTyp}.}

\subsubsection{le ctaipe}
% ni'o gonai ge la'oi .\B t.\ sinxa lo me'oi .digit.\ gi ko'a goi la'o zoi.\ \F{LTyp} \B t .zoi.\ du la'oi .\F{Xrabo}.\ gi gonai ge la'oi .\B t.\ sinxa lo selvau be le latmo ke glibau se lu'erfu gi ko'a du la'oi .\F{Latmo}.\ gi ko'a du la'oi .\F{Vrici}. la'oi la'oi .\F{Latmo}.\ srana lo lerfu poi na jj
% ni'o gonai ge sinxa lo me'oi .digit.\ gi la'oi .\F{Xrabo}.\ mapti gi gonai ge sinxa lo selvau be le latmo ke glibau se lu'erfu gi la'oi .\F{Latmo}.\ mapti gi la'oi .\F{Vrici}. mapti

\begin{code}
data LTyp : Set
  where
  Latmo : LTyp
  Xrabo : LTyp
  Vrici : LTyp
  Kalri : LTyp
  Ganlo : LTyp
\end{code}

\begin{code}
\end{code}

\subsection{la'oi .\D{Lerfu}.}
ni'o ro da poi me'oi .\D{Lerfu}.\ je poi toldra zo'u da sinxa lo selvau be la'oi .ASCII.

.i go fo'a goi la'oi .\B x.\ toldra gi\ldots
\begin{itemize}
	\item gonai ge ko'a goi la'o zoi.\ \F{ctyp} \B x .zoi.\ du la'oi .\F{Xrabo}.\ gi ge fo'a sinxa lo me'oi .digit.\ lerfu gi ge ko'e goi la'o zoi.\ \F{case} \B x .zoi.\ du la'oi .\F{Namcu}.\ gi ko'i goi la'o zoi.\ \F{bnam} \B x .zoi.\ sumji lo namcu poi selsni la'oi .\B x.\ ku'o livobi gi
  \item gonai ge ko'a du la'oi .\F{Latmo}.\ gi\ldots
  \begin{itemize}
    \item gonai ge ko'e du la'oi .\F{Barda}.\ gi ge la'oi .\B x.\ sinxa lo me'oi .majuscule.\ lerfu gi ko'i sumji lo mu'oi glibau.\ 0-indexed .glibau.\ se meirmoi be lo me'oi .caseless.\ versiio be lo selsni be la'oi .\B x.\ li xamu gi
    \item ge ko'e du la'oi .\F{Cmalu}.\ gi ge la'oi .\B x.\ sinxa lo me'oi .minuscule.\ lerfu gi ko'i sumji lo mu'oi glibau.\ 0-indexed .glibau.\ se meirmoi be lo me'oi .caseless.\ versiio be lo selsni be la'oi .\B x.\ li soze gi
  \end{itemize}
  \item gonai ge ko'a du la'oi .\F{Kalri}.\ gi ge ko'i du li sopa gi\ldots
  \begin{itemize}
    \item gonai ge ko'e du la'oi .\F{Curly}.\ gi fo'a sinxa lo tolsti me'oi .curly.\ bo me'oi .bracket.\ noi ke'a selsni li pareci pe la .asycy'i'is.\ gi
    \item gonai ge ko'e du la'oi .\F{Kurfa}.\ gi fo'a sinxa lo tolsti kurfa bo me'oi .bracket.\ noi ke'a selsni li sopa pe la .asycy'i'is.\ gi
    \item ge ko'e du la'oi .\F{Cukla}.\ gi fo'a sinxa lo tolsti cukla bo me'oi .bracket.\ noi ke'a selsni li vono pe la .asycy'i'is.\ gi
  \end{itemize}
  \item ge ko'a du la'oi .\F{Ganlo}.\ gi ge ko'i du li soci gi\ldots
  \begin{itemize}
    \item gonai ge ko'e du la'oi .\F{Curly}.\ gi fo'a sinxa lo sisti me'oi .curly.\ bo me'oi .bracket.\ noi ke'a selsni li paremu pe la .asycy'i'is.\ gi
    \item gonai ge ko'e du la'oi .\F{Kurfa}.\ gi fo'a sinxa lo sisti kurfa bo me'oi .bracket.\ noi ke'a selsni li soci pe la .asycy'i'is.\ gi
    \item gonai ge ko'e du la'oi .\F{Cukla}.\ gi fo'a sinxa lo sisti cukla bo me'oi .bracket.\ noi ke'a selsni li vopa pe la .asycy'i'is.\ gi
  \end{itemize}
  \item ge ko'a du la'oi .\F{Vrici}.\ gi ge ko'e du la'oi .\F{Snile'u}.\ gi ko'i .asycy'i'is.\ sinxa lo selsni be fo'a
\end{itemize}

\begin{code}
record Lerfu : Set
  where
  field
    ctyp : LTyp
    case : Case
    bnam : ℕ
\end{code}

\chapter{le vrici je fancu}

\section{la'oi .\Sym{◈}.}
ni'o lakne fa lo nu le mu'oi glibau.\ type signature .glibau.\ cu banzuka

\begin{code}
_◈_ : ∀ {a} → {A B C : Set a}
    → {M : Set a → Set _} → ⦃ _ : RawApplicative M ⦄
    → (B → C) → (A → M B) → A → M C
_◈_ ⦃ Q ⦄ g f = RawApplicative._<$>_ Q g ∘ f
\end{code}

\chapter{le skicu fancu}
ni'o ga jonai ga je ga je la'oi .\B K.\ vasru la'o zoi.\ (\B x \Sym, \B y) .zoi.\ gi la'oi .\B q.\ mleca la'oi .\B x.\ gi ko'a goi la'o zoi.\ \F{plicu'a} \B q \B n \B K .zoi.\ du la'oi .\B y.\ gi ga jonai ga je lo nilzilcmi be la'oi .\B k.\ cu zmadu li pa gi ko'a du la'o zoi.\ \F{plicu'a} \B q \B n \Sym\$ \F{tail} \B K .zoi.\ gi ko'a du la'oi .\B n.

to .i li renoreci pi'e pa pi'e pare cu detri le nu le mu'oi glibau.\ parsing expression .glibau.\ gerna cu na mapti di'u\ldots noi ke'a drani  .i lo skami cu mabla .u'e nai toi

\begin{code}
plicu'a : ∀ {a} {A : Set a} → ℕ → A → List $ List ℕ × A → A
plicu'a _ d [] = d
plicu'a q x ((a , b) ∷ xs) = if q elem a then b else plicu'a q x xs
  where
  _elem_ : ℕ → List ℕ → Bool
  _elem_ _ [] = false
  _elem_ x (y ∷ ys) = (x ≡ᵇ y) ∨ (x elem ys)
\end{code}

\section{la'oi .\F{toBnam}.}

\begin{code}
toBnam : Fin 128 → ℕ
toBnam q = plicu'a q' q' ns
  where
  q' : ℕ
  q' = toℕ q
  du40 = 40 ∷ 41 ∷ 60 ∷ 62 ∷ 91 ∷ 93 ∷ 123 ∷ 125 ∷ []
  barda = drop 97 $ upTo 123
  ns : List $ List ℕ × ℕ
  ns = (du40 , 40) ∷ (barda , q' ∸ 32) ∷ []
\end{code}

\section{la'oi .\F{toCase}.}
\newcommand\BQ{la'oi .\B q.}
\newcommand\toCase{la'o zoi.\ \F{toCase \B q} .zoi.}
ni'o ga jonai ga je \B q .asycy'i'is.\ sinxa lo latmo glibau lerfu gi \toCase\ du la'oi .\F{Latmo}.\ gi ga jonai ga je la'oi .\B q.\ 

\begin{code}
toCase : Fin 128 → Case
toCase q = plicu'a (toℕ q) Snile'u ns
  where
  f : ℕ → Case → Case → Case
  f a b c = if (toℕ q) <ᵇ a then b else c
  namcu = drop 48 $ upTo 58
  barda = drop 65 $ upTo 91
  cmalu = drop 97 $ upTo 123
  cukla = 40 ∷ 41 ∷ []
  jganu = 60 ∷ 62 ∷ []
  kurfa = 91 ∷ 93 ∷ []
  curly = 123 ∷ 125 ∷ []
  ns : List $ List ℕ × Case
  ns = (cukla , Cukla) ∷ (namcu , Namcu) ∷
       (jganu , Jganu) ∷ (barda , Barda) ∷
       (kurfa , Kurfa) ∷ (curly , Curly) ∷ []
\end{code}

\section{la'oi .\F{toLtyp}.}

\begin{code}
toLtyp : Fin 128 → LTyp
toLtyp q = plicu'a q' Vrici ns
  where
  q' : ℕ
  q' = toℕ q
  kalri = 40 ∷ 60 ∷ 91 ∷ 123 ∷ []
  ganlo = 41 ∷ 61 ∷ 93 ∷ 125 ∷ []
  latmo = (drop 65 $ upTo 91) ++ (drop 97 $ upTo 123)
  xrabo = drop 48 $ upTo 58
  ns : List $ List ℕ × LTyp
  ns = (kalri , Kalri) ∷ (ganlo , Ganlo) ∷
       (xrabo , Xrabo) ∷ (latmo , Latmo) ∷ []
\end{code}

\section{la'oi .\F{toLerfu}.}
ni'o gonai ge la'oi .\B n.\ mleca li panobi gi ko'a goi la'o zoi.\ \F{toLerfu} \B n .zoi.\ me'oi .\F{just}.\ be lo sinxa lo .asycy'i'is.\ lerfu poi meirmoi la'oi .\B n.\ fo le'i ro .asyci'is.\ lerfu gi ko'a me'oi .\F{nothing}.

\begin{code}
toLerfu : ℕ → Maybe Lerfu
toLerfu = finToLerfu ◈ toFin
  where
  postulate
    -- | ni'o gonai ge la'oi .n. mleca li parebi gi la'o
    -- zoi. toFin n .zoi. me'oi .just. lo sinxa be la'oi
    -- .n. gi la'o zoi. toFin n .zoi. me'oi .nothing.
    toFin : ℕ → Maybe $ Fin 128
  finToLerfu : Fin 128 → Lerfu
  finToLerfu a = record {ctyp = lt; case = cs; bnam = bn}
    where
    lt : LTyp
    lt = toLtyp a
    cs : Case
    cs = toCase a
    bn : ℕ
    bn = toBnam a
\end{code}

\section{le vrici je fancu}

\begin{code}
postulate
  intersperse : ∀ {a} → {n : ℕ} → {A : Set a}
              → A → Vec A n → Vec A $ n * 2 ∸ 1
\end{code}

\section{le fancu be fi lo .uniks.\ midnoi}

\subsection{la'oi .\F{spkCL}.}
ni'o lo nu xamgu .uniks.\ bo co'e la'o zoi.\ \F{spkCL} \B x .zoi.\ cu rinka lo nu selsnapra lo velski be lo me'oi .\F{ltyp}.\ be la'oi .\B x.

\begin{code}
postulate spkCL : Lerfu → Midnoi
\end{code}

\subsection{la'oi .\F{spkCC}.}
ni'o lo nu xamgu .uniks.\ bo co'e la'o zoi.\ \F{spkCC} \B x .zoi.\ cu rinka lo nu selsnapra lo velski be lo me'oi .case.\ be la'oi .\B x.

\begin{code}
postulate spkCC : Lerfu → Midnoi
\end{code}

\subsection{la'oi .\F{spkCF}.}
ni'o lo nu xamgu .uniks.\ bo co'e la'o zoi.\ \F{spkCL} \B x .zoi.\ cu rinka lo nu selsnapra lo velski be lo me'oi .\F{ltyp}.\ be la'oi .\B x.

\begin{code}
postulate spkCF : Lerfu → Midnoi
\end{code}

\subsection{la'oi .\F{doit}.}

\begin{code}
doit : ∀ {a} → String → IO {a} ⊤
doit = pure ∘ doit'
  where
  postulate doit' : String → ⊤
  {-# FOREIGN GHC import Control.Monad #-}
  {-# FOREIGN GHC import System.Process #-}
  {-# FOREIGN GHC import System.IO.Unsafe #-}
  {-# COMPILE GHC doit' =
      \_ -> unsafePerformIO . void . runProcess #-}
\end{code}

\section{la'oi .\F{spk}.}
ni'o gonai co'e zoi zoi.\ \F{spk} \B q .zoi.\ gi lo skami cu bacru pe'a ru'e la'oi .\B q.

\begin{code}
spk : ∀ {a} → Lerfu → IO {a} ⊤
spk l = vecMapM′ doit $ intersperse denpuXipa $ spks l
  where
  vecMapM′ : ∀ {a b} → {n : ℕ} → {A : Set a}
           → (A → IO {b} ⊤) → Vec A n → IO {b} ⊤
  vecMapM′ f = IO.List.mapM′ f ∘ Data.Vec.toList
  denpuXipa : Midnoi
  denpuXipa = "sleep " ++ₛ Data.Float.show selsniduXiPa
  spks : Lerfu → Vec Midnoi 3
  spks l = Data.Vec.map (flip _$_ l) $ spkCL ∷ spkCC ∷ spkCF ∷ []
\end{code}
\end{document}
