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
\newunicodechar{≡}{\ensuremath{\mathnormal\equiv}}
\newunicodechar{⟨}{\ensuremath{\mathnormal\langle}}
\newunicodechar{⟩}{\ensuremath{\mathnormal\rangle}}
\newunicodechar{∎}{\ensuremath{\mathnormal\blacksquare}}
\newunicodechar{∶}{\ensuremath{\mathnormal\colon\!\!}}
\newunicodechar{⊹}{\ensuremath{\mathnormal\dag}}
\newunicodechar{𝕗}{\ensuremath{\mathnormal{\mathbb{f}}}}
\newunicodechar{ℙ}{\ensuremath{\mathnormal{\mathbb{P}}}}
\newunicodechar{𝔽}{\ensuremath{\mathnormal{\mathbb{F}}}}
\newunicodechar{𝕄}{\ensuremath{\mathnormal{\mathbb{M}}}}
\newunicodechar{𝔹}{\ensuremath{\mathnormal{\mathbb{B}}}}
\newunicodechar{ν}{\ensuremath{\mathnormal{\nu}}}
\newunicodechar{μ}{\ensuremath{\mathnormal{\mu}}}
\newunicodechar{◆}{\ensuremath{\mathnormal\blackdiamond}}
\newunicodechar{∸}{\ensuremath{\mathnormal\dotdiv}}
\newunicodechar{ᵇ}{\ensuremath{\mathnormal{^\mathrm{b}}}}
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
  using (
    toℕ;
    Fin
  )
open import Data.Nat
  using (
    _≡ᵇ_;
    _∸_;
    _*_;
    suc;
    ℕ
  )
  renaming (
    _+_ to _+ₙ_
  )
open import Data.Sum
  using (
    [_,_];
    inj₁;
    inj₂;
    _⊎_
  )
open import Data.Vec
  using (
    fromList;
    toList;
    Vec
  )
  renaming (
    _++_ to _++ᵥ_;
    map to mapᵥ;
    _∷_ to _∷ᵥ_;
    [] to []ᵥ
  )
open import Function
open import Data.Bool
  using (
    if_then_else_;
    false;
    Bool;
    true;
    _∨_
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
    _∷_ to _∷ₗ_;
    length to lengthₗ
  )
open import Data.Float
  using (
    Float
  )
open import Data.Maybe
  using (
    nothing;
    Maybe;
    maybe;
    just
  )
open import Data.String
  renaming (
    _++_ to _++ₛ_;
    toList to toListₛ
  )
  using (
    String
  )
open import Data.Product
  using (
    _×_;
    _,_
  )
open import IO.Primitive
  using (
  )
  renaming (
    IO to PIO;
    _>>=_ to _>>=ₚᵢₒ_
  )
open import Category.Applicative
open import Data.Maybe.Instances
open import Truthbrary.Record.SR
open import Data.Unit.Polymorphic
  using (
    tt;
    ⊤
  )
open import Truthbrary.Record.LLC
open import Relation.Binary.PropositionalEquality
  using (
    subst;
    cong;
    refl;
    sym;
    _≡_
  )

import Agda.Builtin.Unit as ABU
\end{code}

\chapter{le srana be lo nu tcimi'e}

\section{la'oi .\F{selsniduXiPa}.}
ni'o la'oi .\F{selsniduXiPa}.\ bitmu fo lo me'oi .\D{Lerfu}.

\begin{code}
postulate selsniduXiPa : Float
\end{code}

\section{la'oi .\F{selsniduXiRe}.}
ni'o la'oi .\F{selsniduXiRe}.\ bitmu fo lo mu'oi glibau.\ \D{List} \D{Lerfu} .glibau.

\begin{code}
postulate selsniduXiRe : Float
\end{code}

\section{la'oi .\F{ddvs}.}
ni'o la'oi .\F{ddvs}.\ me'oi .path.\ lo datnyveiste poi ke'a vasru lo sance datnyvei pe la'oi .EVANNOUNCER.

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
ni'o sinxa lo selvau be la'oi .ASCII.\ fa lo ro ctaipe la'oi .\D{Lerfu}.\ be'o poi ke'a drani

.i go fo'a goi la'oi .\B x.\ drani gi\ldots
\begin{itemize}
	\item gonai ge ko'a goi la'o zoi.\ \AgdaField{Lerfu.ctyp} \B x .zoi.\ du la'oi .\IC{Xrabo}.\ gi ge fo'a sinxa lo nacle'u gi ge ko'e goi la'o zoi.\ \AgdaField{Lerfu.case} \B x .zoi.\ du la'oi .\IC{Namcu}.\ gi ko'i goi la'o zoi.\ \AgdaField{Lerfu.bnam} \B x .zoi.\ sumji lo namcu poi selsni la'oi .\B x.\ ku'o li vobi gi
	\item gonai ge ko'a du la'oi .\IC{Latmo}.\ gi\ldots
	\begin{itemize}
		\item gonai ge ko'e du la'oi .\IC{Barda}.\ gi ge la'oi .\B x.\ sinxa lo me'oi .majuscule.\ lerfu gi ko'i sumji lo mu'oi glibau.\ 0-indexed .glibau.\ se meirmoi be lo me'oi .caseless.\ versiio be lo selsni be la'oi .\B x.\ li xamu gi
		\item ge ko'e du la'oi .\IC{Cmalu}.\ gi ge la'oi .\B x.\ sinxa lo me'oi .minuscule.\ lerfu gi ko'i sumji lo mu'oi glibau.\ 0-indexed .glibau.\ se meirmoi be lo me'oi .caseless.\ versiio be lo selsni be la'oi .\B x.\ li soze gi
	\end{itemize}
	\item gonai ge ko'a du la'oi .\IC{Kalri}.\ gi ge ko'i du li \sopa\ gi\ldots
	\begin{itemize}
		\item gonai ge ko'e du la'oi .\IC{Tcekr}.\ gi fo'a sinxa lo tolsti me'oi .curly.\ bo me'oi .bracket.\ noi ke'a selsni li pareci pe la .asycy'i'is.\ gi
		\item gonai ge ko'e du la'oi .\IC{Kurfa}.\ gi fo'a sinxa lo tolsti kurfa bo me'oi .bracket.\ noi ke'a selsni li \sopa\ pe la .asycy'i'is.\ gi
		\item ge ko'e du la'oi .\IC{Cukla}.\ gi fo'a sinxa lo tolsti cukla bo me'oi .bracket.\ noi ke'a selsni li vono pe la .asycy'i'is.\ gi
	\end{itemize}
	\item ge ko'a du la'oi .\IC{Ganlo}.\ gi ge ko'i du li soci gi\ldots
	\begin{itemize}
		\item gonai ge ko'e du la'oi .\IC{Tcekr}.\ gi fo'a sinxa lo sisti me'oi .curly.\ bo me'oi .bracket.\ noi ke'a selsni li paremu pe la .asycy'i'is.\ gi
		\item gonai ge ko'e du la'oi .\IC{Kurfa}.\ gi fo'a sinxa lo sisti kurfa bo me'oi .bracket.\ noi ke'a selsni li soci pe la .asycy'i'is.\ gi
		\item gonai ge ko'e du la'oi .\IC{Cukla}.\ gi fo'a sinxa lo sisti cukla bo me'oi .bracket.\ noi ke'a selsni li vopa pe la .asycy'i'is.\ gi
	\end{itemize}
	\item ge ko'a du la'oi .\IC{Vrici}.\ gi ge ko'e du la'oi .\IC{Snile'u}.\ gi ko'i .asycy'i'is.\ sinxa lo selsni be fo'a
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

\section{la'oi .\F{liftx}.}
ni'o cadga fa lo nu le velcki be le se ctaipe cu banzu lo nu jimpe

\begin{code}
liftx : ∀ {a} → PIO ABU.⊤ → IO {a} ⊤
liftx q = liftᵢₒ $ q >>=ₚᵢₒ λ _ → IO.Primitive.return _
\end{code}

\section{la'oi .\F{intersperse}.}
ni'o la .varik.\ cu na djuno lo du'u ma kau zabna je cu velcki la'oi .\F{intersperse}.\ bau la .lojban.

\begin{code}
intersperse : ∀ {a} → {n : ℕ} → {A : Set a}
            → (t : A) → (q : Vec A n)
            → Vec A $ n * 2 ∸ 1
intersperse _ []ᵥ = []ᵥ
intersperse _ q@(_ ∷ᵥ []ᵥ) = q
intersperse {n = n} t (x ∷ᵥ y ∷ᵥ z) = x ∷ᵥ t ∷ᵥ intersperse t (y ∷ᵥ z)
\end{code}

\chapter{le skicu fancu}
\section{la'oi .\F{plicu'a}.}
ni'o ga jonai ga je ga je la'oi .\B K.\ vasru la'o zoi.\ \B x \OpF, \B z .zoi.\ gi la'oi .\B q.\ selvau la'oi .\B x.\ gi\ldots
\begin{itemize}
	\item ko'a goi la'o zoi.\ \F{plicu'a} \B q \B n \B K .zoi.\ du la'oi .\B z.\ gi
	\item ga jonai ga je lo nilzilcmi be la'oi .\B k.\ cu zmadu li pa gi ko'a du la'o zoi.\ \F{plicu'a} \B q \B n \OpF\$ \F{tail} \B K .zoi.\ gi ko'a du la'oi .\B n.
\end{itemize}

\begin{code}
plicu'a : ∀ {a} → {A : Set a} → ℕ → A → List $ List ℕ × A → A
plicu'a _ d []ₗ = d
plicu'a q d ((a , b) ∷ₗ xs) = if q elem a then b else plicu'a q d xs
  where
  _elem_ : ℕ → List ℕ → Bool
  _elem_ _ []ₗ = false
  _elem_ x (y ∷ₗ ys) = (x ≡ᵇ y) ∨ (x elem ys)
\end{code}

\section{la'oi .\F{intdMm}.}
ni'o la'o zoi.\ \F{intdMm} \B a \B b .zoi.\ porsi lo'i ro kacna'u poi ke'a dubjavmau la'oi .\B a.\ je cu mleca la'oi .\B b.

\begin{code}
intdMm : ℕ → ℕ → List ℕ
intdMm a = drop a ∘ upTo
\end{code}

\section{la'oi .\F{toBnam}.}

\begin{code}
toBnam : Fin 128 → ℕ
toBnam q = plicu'a q' q' ns
  where
  q' = toℕ q
  du40 = 40 ∷ 41 ∷ 60 ∷ 62 ∷ 91 ∷ 93 ∷ 123 ∷ 125 ∷ []ₗ
  cmalu = intdMm 97 123
  ns : List $ List ℕ × ℕ
  ns = (du40 , 40) ∷ (cmalu , q' ∸ 32) ∷ []ₗ
\end{code}

\section{la'oi .\F{toCase}.}
\newcommand\BQ{la'oi .\B q.}
\newcommand\toCase{la'o zoi.\ \F{toCase} \B q .zoi.}

ni'o ga jonai \toCase\ du la'oi .\IC{Snile'u}.\ gi\ldots
\begin{itemize}
	\item gonai ge \BQ\ dubjavmau li vobi je cu mleca li mubi gi \toCase\ du la'oi .\IC{Namcu}.\ gi
        \item gonai ge \BQ\ dubjavmau li xamu je cu mleca li \sopa\ gi \toCase\ du la'oi .\IC{Barda}.\ gi
        \item gonai ge \BQ\ dubjavmau li soze je cu mleca li pareci gi \toCase\ du la'oi .\IC{Cmalu}.\ gi
        \item gonai ge \BQ\ du li vono ja li vopa gi \toCase\ du la'oi .\IC{Cukla}.\ gi
        \item gonai ge \BQ\ du li xano ja li xare gi \toCase\ du la'oi .\IC{Jganu}.\ gi
        \item gonai ge \BQ\ du li \sopa\ ja li soci gi \toCase\ du la'oi .\F{Kurfa}.\ gi
        \item ge \BQ\ du li pareci ja li paremu gi \toCase\ du la'oi .\F{Curly}.
\end{itemize}

\begin{code}
toCase : Fin 128 → Case
toCase q = plicu'a (toℕ q) Snile'u ns
  where
  namcu = intdMm 48 58
  barda = intdMm 65 91
  cmalu = intdMm 97 123
  cukla = 40 ∷ 41 ∷ []ₗ
  jganu = 60 ∷ 62 ∷ []ₗ
  kurfa = 91 ∷ 93 ∷ []ₗ
  tcekr = 123 ∷ 125 ∷ []ₗ
  ns : List $ List ℕ × Case
  ns = (cukla , Cukla) ∷ (namcu , Namcu) ∷
       (jganu , Jganu) ∷ (barda , Barda) ∷
       (kurfa , Kurfa) ∷ (tcekr , Tcekr) ∷
       (cmalu , Cmalu) ∷ []ₗ
\end{code}

\section{la'oi .\F{toLtyp}.}

\begin{code}
toLtyp : Fin 128 → LTyp
toLtyp q = plicu'a (toℕ q) Vrici ns
  where
  kalri = 40 ∷ 60 ∷ 91 ∷ 123 ∷ []ₗ
  ganlo = 41 ∷ 61 ∷ 93 ∷ 125 ∷ []ₗ
  latmo = intdMm 65 91 ++ intdMm 97 123
  xrabo = intdMm 48 58
  ns : List $ List ℕ × LTyp
  ns = (kalri , Kalri) ∷ (ganlo , Ganlo) ∷
       (xrabo , Xrabo) ∷ (latmo , Latmo) ∷ []ₗ
\end{code}

\section{la'oi .\F{toLerfu}.}
ni'o ga jonai ga je la'oi .\B n.\ mleca li parebi gi ko'a goi la'o zoi.\ \F{toLerfu} \B n .zoi.\ me'oi .\IC{just}.\ be lo sinxa lo .asycy'i'is.\ lerfu poi meirmoi la'oi .\B n.\ fo le'i ro .asyci'is.\ lerfu gi ko'a me'oi .\IC{nothing}.

\begin{code}
toLerfu : ℕ → Maybe Lerfu
toLerfu = Data.Maybe.map finToLerfu ∘ readMaybe ∘ show
  where
  finToLerfu : Fin 128 → Lerfu
  finToLerfu a = record {ctyp = lt; case = cs; bnam = a}
    where
    lt = toLtyp a
    cs = toCase a
\end{code}

\section{la'oi .\F{lerste}.}
ni'o ga jonai ko'a goi la'o zoi.\ \F{lerste} \B x.\ .zoi.\ me'oi .\IC{nothing}.\ gi ga je la'oi .\B x.\ .aski gi ga je ko'a du la'oi .\B x.\ lo ni ce'u vasru gi ro da poi ke'a kacna'u je cu mleca lo nilzilcmi be ko'a zo'u lo meirmoi be da bei fo ko'a cu sinxa lo meirmoi be da bei la'oi .\B x.

\begin{code}
lerste : String → Maybe $ List Lerfu
lerste = sikh ∘ map (toLerfu ∘ Data.Char.toℕ) ∘ toListₛ
  where
  sikh : ∀ {a} → {A : Set a} → List $ Maybe A → Maybe $ List A
  sikh []ₗ = just []ₗ
  sikh (nothing ∷ₗ _) = nothing
  sikh (just x ∷ₗ xs) = Data.Maybe.map (_∷_ x) $ sikh xs

  module Veritas
    where
    faivos : ∀ {a} → {A : Set a}
           → (j : List A)
           → just j ≡ sikh (map just j)
    faivos []ₗ = refl
    faivos (x ∷ₗ y) = cong (Data.Maybe.map $ _∷_ x) $ faivos y

    faivuyn : ∀ {a} → {A : Set a}
            → (x z : List $ Maybe A)
            → nothing ≡ sikh (x ++ nothing ∷ₗ z)
    faivuyn []ₗ _ = refl
    faivuyn (nothing ∷ₗ _) _ = refl
    faivuyn (just x ∷ₗ xs) = cong (mapₘ $ _∷_ x) ∘ faivuyn xs
      where
      mapₘ = Data.Maybe.map
\end{code}

\chapter{le fancu poi ke'a srana lo .uniks.\ midnoi}

\section{la'oi .\F{spkCL}.}
ni'o \selsnap{\F{spkCL} \B x}{lo me'oi .\AgdaField{Lerfu.ctyp}.\ be la'oi .\B x.}

\begin{code}
spkCL : Lerfu → Midnoi
spkCL q = "mplayer " ++ ddvs ++ f (Lerfu.ctyp q)
  where
  f : LTyp → String
  f = map Data.Char.toLower ∘ show
\end{code}

\section{la'oi .\F{spkCC}.}
ni'o \selsnap{\F{spkCC} \B x}{lo me'oi .case.\ be la'oi .\B x.}

\begin{code}
spkCC : Lerfu → Midnoi
spkCC q = "mplayer " ++ ddvs ++ f (Lerfu.case q)
  where
  f : Case → String
  f = map Data.Char.toLower ∘ show
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

\section{la \F{denpa}.}
ni'o lo nu drani .uniks.\ bo co'e la'o zoi.\ \F{denpa}\ \B f\ .zoi.\ cu rinka lo nu snidu la'o zoi.\ \B f\ .zoi.\ fa lo nu denpa

\begin{code}
denpa : Float → Midnoi
denpa = _++_ "sleep " ∘ show
\end{code}

\section{la'oi .\F{doit}.}
ni'o tu'a la'o zoi.\ \F{doit} \B s\ .zoi.\ rinka lo nu .uniks.\ co'e la'o zoi.\ \B s\ .zoi.  .i ga jonai ga je .indika lo du'u snada fa tu'a ko'a goi la'o zoi.\ \F{doit} \B s\ .zoi.\ snada gi ko'a me'oi .\F{pure}.\ la'oi .\F{nothing}.\ gi ko'a me'oi .\F{pure}.\ lo mu'oi glibau.\ exit code .glibau.\ poi tu'a ko'a rinka tu'a ke'a tu'a ke'a selri'a tu'a ko'a

\begin{code}
doit : String → IO $ Maybe ℕ
doit = _<$>ᵢₒ_ bixygau ∘ liftᵢₒ ∘ doit'
  where
  bixygau : ℕ → Maybe ℕ
  bixygau n = if n Data.Nat.<ᵇ 127 then nothing else just n
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

\section{la'oi .\F{sequin}.}
ni'o ga jonai ga je ko'a goi la'o zoi.\ \B n .zoi.\ vasru lo me'oi .\IC{just}.\ gi ko'e goi la'o zoi.\ \F{sequin} \B n .zoi.\ pa moi lo'i ro me'oi .\F{just}.\ poi ke'a selvau ko'a gi ko'e du la'oi .\IC{nothing}.

\begin{code}
sequin : ∀ {a} → {n : ℕ} → {A : Set a}
       → Vec (Maybe A) n → Maybe A
sequin = Data.List.head ∘ Data.List.mapMaybe id ∘ toList

module SequinVeritas where
  pamoi : ∀ {a} → {A : Set a} → {n : ℕ}
        → (x : Vec (Maybe A) n)
        → (z : A)
        → just z ≡ sequin (just z ∷ x)
  pamoi _ _ = refl

  nymois : ∀ {a} → {A : Set a} → {n : ℕ}
         → (m : ℕ)
         → (x : Vec (Maybe A) n)
         → (z : A)
         → (_≡_
             (just z)
             (sequin
               (_++ᵥ_
                 (Data.Vec.replicate {n = m} nothing)
                 (just z ∷ᵥ x))))
  nymois 0 _ _ = refl
  nymois (suc n) = nymois n
\end{code}

\section{la'oi .\F{spk}.}
ni'o tu'a zoi zoi.\ \F{spk} \B q .zoi.\ cu rinka lo nu lo skami cu bacru pe'a ru'e la'oi .\B q.

\begin{code}
spk : Lerfu → IO $ Maybe ℕ
spk = mvm doit ∘ intersperse (denpa selsniduXiPa) ∘ spks
  where
  mvm : ∀ {a b} → {n : ℕ} → {A : Set a} → {B : Set b}
      → (A → IO $ Maybe B) → Vec A n → IO $ Maybe B
  mvm f = _<$>ᵢₒ_ (sequin ∘ fromList) ∘ IO.List.mapM f ∘ toList
  spks : Lerfu → Vec Midnoi 3
  spks l = mapᵥ (_$ l) $ spkCL ∷ spkCC ∷ spkCF ∷ []ᵥ
\end{code}

\section{la'oi .\F{bacru}.}
ni'o tu'a la'o zoi.\ \F{bacru} \B q .zoi.\ rinka lo nu lo srana be lo skami cu selsnapra lo sinxa be la'o zoi.\ \B q .zoi.

\begin{code}
bacru : List Lerfu → IO $ Maybe ℕ
bacru = _<$>ᵢₒ_ (sequin ∘ fromList) ∘ IO.List.mapM spkJaDnp ∘ dej
  where
  denpaXiRe : IO $ Maybe ℕ
  denpaXiRe = doit $ "sleep " ++ show selsniduXiRe
  -- | ni'o zo .dej. cmavlaka'i lu denpa jmina li'u
  dej : List Lerfu → List $ Fin 1 ⊎ Lerfu
  dej = Data.List.intersperse (inj₁ Fin.zero) ∘ map inj₂
  spkJaDnp : Fin 1 ⊎ Lerfu → IO $ Maybe ℕ
  spkJaDnp = [_,_] (const $ doit $ denpa selsniduXiRe) spk
\end{code}

\section{la'oi .\F{main}.}

\begin{code}
main : Main
main = run $ getLine >>=ᵢₒ maybe bjsf spojaPe'aRu'e ∘ lerste
  where
  postulate erroy : String → PIO ABU.⊤
  {-# COMPILE GHC erroy = hPutStrLn stderr . unpack #-}
  spojaPe'aRu'e : ∀ {a} → IO {a} ⊤
  spojaPe'aRu'e = liftx $ erroy $ jbo ++ "\n\n" ++ eng
    where
    jbo = "ni'o pruce lo lerfu poi \
          \ke'a tolmapti la .asycy'i'is."
    eng = "Inputs a non-ASCII character."
  -- | ni'o zo'oi .bjsf. cmavlaka'i lu bacru ja
  -- samfli li'u
  --
  -- .i la .varik. cu na djuno lo du'u cadga fa lo nu
  -- ma kau basti zo'oi .bjsf.
  bjsf : List Lerfu → IO ⊤
  bjsf a = bacru a >>=ᵢₒ camki'a
    where
    camki'a : Maybe ℕ → IO ⊤
    camki'a = maybe (liftx ∘ erroy ∘ show) $ pure tt
\end{code}
\end{document}
