\documentclass{report}

\usepackage{ar}
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
\newunicodechar{ₘ}{\ensuremath{_\mathsf{m}}}
\newunicodechar{ₛ}{\ensuremath{_\mathsf{s}}}
\newunicodechar{⊤}{\ensuremath{\mathnormal{\top}}}
\newunicodechar{◈}{\ensuremath{\diamond\hspace{-0.39em}\cdot}}
\newunicodechar{≤}{\ensuremath{\mathnormal{\leq}}}
\newunicodechar{⍉}{\ensuremath{∘\hspace{-0.455em}\backslash}}
\newunicodechar{⦃}{\ensuremath{\mathnormal{\lbrace\!\lbrace}}}
\newunicodechar{⦄}{\ensuremath{\mathnormal{\rbrace\!\rbrace}}}
\newunicodechar{ᵢ}{\ensuremath{\mathnormal{_i}}}
\newunicodechar{ₗ}{\ensuremath{\mathnormal{_l}}}
\newunicodechar{ₒ}{\ensuremath{\mathnormal{_o}}}
\newunicodechar{ₚ}{\ensuremath{\mathnormal{_p}}}
\newunicodechar{ₙ}{\ensuremath{\mathnormal{_n}}}
\newunicodechar{ᵥ}{\ensuremath{\mathnormal{_v}}}
\newunicodechar{′}{\ensuremath{\mathnormal{'}}}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound

\title{le me'oi .Agda.\ me'oi .implementation.\ be la'oi .EVANNOUNCER.}
\author{la .varik.\ .VALefor.}

\begin{document}
\maketitle

\chapter{le me'oi .preamble.}
\begin{code}
{-# OPTIONS --guardedness #-}

open import IO
  renaming (
    lift to liftᵢₒ;
    _>>=_ to _>>=ᵢₒ_
  )
  hiding (
    _<$>_
  )
open import Level
open import Data.Fin
open import Data.Nat
  renaming (
    suc to sucₙ;
    _+_ to _+ₙ_
  )
open import Data.Sum
  hiding (
    map
  )
open import Data.Vec
  hiding (
    drop
  )
  renaming (
    [] to []ᵥ;
    _++_ to _++ᵥ_;
    map to mapᵥ;
    _∷_ to _∷ᵥ_
  )
open import Function
open import Data.Bool
open import Data.Char
  using (
    Char
  )
  renaming (
    toℕ to C2N
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
    _++_ to _++ₗ_;
    intersperse to intersperseₗ;
    length to lengthₗ
  )
open import Data.Float
  using (
    Float
  )
open import Data.Maybe
  renaming (
    map to mapₘ
  )
open import Data.String
  renaming (
    _++_ to _++ₛ_;
    fromList to fromListₗ;
    toList to toListₗ
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
  renaming (
    IO to PIO;
    _>>=_ to _>>=ₚᵢₒ_;
    return to returnₚᵢₒ
  )
open import Category.Monad
open import Agda.Builtin.Unit
  renaming (
    ⊤ to Unit
  )
open import Category.Applicative
open import Data.Maybe.Instances
open import Data.Unit.Polymorphic
open import Relation.Binary.PropositionalEquality
open import Data.Nat.Show
  using ()
open import Data.Fin.Show
  using (
    readMaybe
  )
\end{code}

\chapter{le srana be lo nu tcimi'e}

\section{la'oi .\F{selsniduXiPa}.}
ni'o la'oi .\F{selsniduXiPa}.\ bitmu fo lo me'oi .\F{Lerfu}.

\begin{code}
postulate selsniduXiPa : Float
\end{code}

\section{la'oi .\F{selsniduXiRe}.}
ni'o la'oi .\F{selsniduXiRe}.\ bitmu fo lo mu'oi glibau.\ \F{List} \F{Lerfu} .glibau.

\begin{code}
postulate selsniduXiRe : Float
\end{code}

\section{la'oi .\F{ddvs}.}
ni'o la'oi .\F{ddvs}.\ me'oi .path. lo datnyveiste poi ke'a vasru lo sance datnyvei pe la'oi .EVANNOUNCER.

.i zo'oi .ddvs.\ cmavlaka'i lu datni datnyveiste li'u

\begin{code}
ddvs : String
ddvs = "/usr/local/share/evannouncer/"
\end{code}

\chapter{le me'oi .\AgdaKeyword{record}.\ je le me'oi .\AgdaKeyword{instance}.\ je zo'e}

\section{la'oi .\F{Showable}.}
ni'o la .varik.\ cu na jinvi le du'u sarcu fa lo nu jmina lo velcki\ldots kei kei je cu na djuno lo du'u ma kau zabna velcki la'oi .\F{Showable}.

\begin{code}
record Showable {a} (A : Set a) : Set a
  where
  field
    show : A → String
\end{code}

\subsection{le me'oi .\AgdaKeyword{instance}.\ pe zo'e poi la'oi .EVANNOUNCER.\ cu na vasru lo vlavelcki be ke'a}

\begin{code}
instance
  showableℕ : Showable ℕ
  showableℕ = record {show = Data.Nat.Show.show}
  showableFloat : Showable Float
  showableFloat = record {show = Data.Float.show}
\end{code}

\section{la'oi .\F{LL}.}
ni'o ga go zasti fa lo selvau be la'o zoi.\ \F{LL} \B x .zoi.\ gi la'oi .\B x.\ cu simsa la'oi .\F{List}.

.i ga go la'oi .\B q.\ zasti je cu ctaipe la'o zoi.\ \F{LL} \B t .zoi.\ je cu ba'e drani gi\ldots
\begin{itemize}
  \item ga je la'o zoi.\ \F{LL.e} \B q .zoi.\ se ctaipe lo selvau be lo ctaipe be la'oi .\B t.\ gi
  \item ga je ga jo la'oi .\B n.\ selvau la'oi .\D{ℕ}.\ gi la'o zoi.\ \F{LL.olen} \B q \B n .zoi.\ se ctaipe lo ro lazmi'u pe'a be la'oi .\B t.\ be'o poi la'oi .\B n.\ nilzilcmi ke'a gi
  \item ga je la'o zoi.\ \F{LL.[]} \B q .zoi.\ ctaipe la'o zoi.\ \F{LL.olen} \B q 0 .zoi\ldots je cu kunti gi
  \item ga je ga jonai ga je cumki fa lo nu lo nilzilcmi be ko'a goi lo ctaipe be la'oi .\B t.\ cu na du lo nilzilcmi be lo ctaipe be la'oi .\B t.\ be'o poi ke'a na du ko'a gi la'o zoi.\ \F{LL.l} \B q .zoi.\ je la'o zoi.\ \F{LL.n} \B q.\ cu du li no gi ga je la'o zoi.\ \F{LL.l} \B q .zoi.\ nilzilcmi lo ctaipe be la'oi .\B t.\ gi la'o zoi.\ \F{LL.n} \B q .zoi.\ nilzilcmi lo remoi be lo'i ro sumti be la'oi .\F{\_++\_}.\ gi
  \item ga je la'o zoi.\ \B a \Sym{++} \B b .zoi.\ konkatena la'oi .\B a.\ la'oi .\B b.\ gi
  \item ga je pilno la'oi .\F{\_∷\_}.\ lo nu me'oi .prepend.\ gi
  \item la'o zoi.\ \F{LL.etsil} \Sym∘ \F{LL.liste} .zoi.\ dunli la'oi .\F{id}.
\end{itemize}

\begin{code}
record LL {a} (A : Set a) : Set (Level.suc a)
  where
  field
    e : Set a
    olen : ℕ → Set a
    [] : olen 0
    l n : ℕ
  olenn = olen n
  olenl+n = olen $ l +ₙ n
  field
    _++_ : A → olen n → olen $ l +ₙ n
    _∷_ : e → A → olen $ sucₙ l
    liste : A → List e
    etsil : (q : List e) → olen $ Data.List.length q
\end{code}

\subsection{le me'oi .\AgdaKeyword{instance}.\ pe zo'e poi la'oi .EVANNOUNCER.\ cu na vasru lo vlavelcki be ke'a}

\begin{code}
instance
  liliList : ∀ {a} → {A : Set a} → LL $ List A
  liliList {_} {A} = record {
    e = A;
    olen = const $ List A;
    [] = []ₗ;
    l = 0;
    n = 0;
    _++_ = _++ₗ_;
    _∷_ = _∷ₗ_;
    liste = id;
    etsil = id}
  liliString : LL String
  liliString = record {
    e = Char;
    olen = const String;
    [] = "";
    l = 0;
    n = 0;
    _++_ = _++ₛ_;
    _∷_ = λ a → fromListₗ ∘ _∷ₗ_ a ∘ toListₗ;
    liste = Data.String.toList;
    etsil = Data.String.fromList}
  liliVec : ∀ {a} → {A : Set a} → {n m : ℕ} → LL $ Vec A n
  liliVec {_} {A} {n'} {m'} = record {
    [] = []ᵥ;
    olen = Vec A;
    e = A;
    l = n';
    n = m';
    _++_ = _++ᵥ_;
    _∷_ = _∷ᵥ_;
    liste = Data.Vec.toList;
    etsil = Data.Vec.fromList}
\end{code}

\chapter{le me'oi .\AgdaKeyword{data}.}

\section{la'oi .\D{Midnoi}.}
ni'o ro da poi me'oi .\D{Midnoi}.\ zo'u da sinxa lo .uniks.\ midnoi

\begin{code}
Midnoi : Set
Midnoi = String
\end{code}

\section{la'oi .\D{Case}.}

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

\subsection{le me'oi .\AgdaKeyword{instance}.}

\begin{code}
instance
  shockAndAwe : Showable Case
  shockAndAwe = record {show = f}
    where
    f : Case → String
    f Barda = "Barda"
    f Cmalu = "Cmalu"
    f Namcu = "Namcu"
    f Cukla = "Cukla"
    f Curly = "Curly"
    f Kurfa = "Kurfa"
    f Jganu = "Jganu"
    f Snile'u = "Snile'u"
\end{code}

\section{la'oi .\F{LTyp}.}

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
  showUsYourBoobs : Showable LTyp
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
    bnam : Fin 128
\end{code}

\chapter{le vrici je fancu}

\section{la'oi .\F{show}.}
ni'o la'o zoi.\ \F{show} \B q .zoi.\ me'oi .String.\ je cu sinxa la'oi .\B q.

\begin{code}
show : ∀ {a} → {A : Set a} → ⦃ Showable A ⦄
     → A → String
show ⦃ Q ⦄ = Showable.show Q
\end{code}

\section{la'oi .\F{\_++\_}.}
ni'o la .varik.\ cu sorpa'a lo nu le se ctaipe je zo'e cu banzuka

\begin{code}
infixr 5 _++_

_++_ : ∀ {a} → {Bean : Set a}
     → ⦃ T : LL Bean ⦄
     → Bean → LL.olenn T → LL.olenl+n T
_++_ ⦃ Q ⦄ = LL._++_ Q
\end{code}

\section{la'oi .\F{\_∷\_}.}
ni'o la .varik.\ cu sorpa'a lo nu le se ctaipe je zo'e cu banzuka

\begin{code}
infixr 5 _∷_

_∷_ : ∀ {a} → {A : Set a}
     → ⦃ ALL : LL A ⦄
     → LL.e ALL → A → LL.olen ALL $ sucₙ $ LL.l ALL
_∷_ ⦃ Q ⦄ = LL._∷_ Q
\end{code}

\section{la'oi .\F{[]}.}
ni'o la .varik.\ cu sorpa'a lo nu le se ctaipe je zo'e cu banzuka

\begin{code}
[] : ∀ {a} → {A : Set a}
   → ⦃ Q : LL A ⦄
   → LL.olen Q 0
[] ⦃ Q ⦄ = LL.[] Q
\end{code}

\section{la'oi .\F{map}.}
ni'o la .varik.\ cu sorpa'a lo nu le se ctaipe je zo'e cu banzuka  .i ku'i la'oi .\F{map}.\ cu smimlu la'oi .\texttt{map}.\ pe la'oi .Haskell.

\begin{code}
map : ∀ {a b} → {A : Set a} → {B : Set b}
    → ⦃ Q : LL A ⦄ → ⦃ R : LL B ⦄
    → (f : LL.e Q → LL.e R) → (x : A)
    → LL.olen R $ lengthₗ $ Data.List.map f $ LL.liste Q x
map ⦃ Q ⦄ ⦃ R ⦄ f = etsil ∘ Data.List.map f ∘ liste
  where
  liste = LL.liste Q
  etsil = LL.etsil R
\end{code}

\section{la'oi .\Sym{◈}.}
ni'o lakne fa lo nu le mu'oi glibau.\ type signature .glibau.\ cu banzuka

\begin{code}
_◈_ : ∀ {a} → {A B C : Set a}
    → {M : Set a → Set _} → ⦃ RawApplicative M ⦄
    → (B → C) → (A → M B) → A → M C
_◈_ ⦃ Q ⦄ g f = RawApplicative._<$>_ Q g ∘ f
\end{code}

\section{la'oi .\F{liftx}.}
ni'o cadga fa lo nu le se ctaipe cu banzu lo nu jimpe

\begin{code}
liftx : ∀ {a} → PIO Unit → IO {a} ⊤
liftx q = liftᵢₒ (q >>=ₚᵢₒ λ _ → returnₚᵢₒ _)
\end{code}

\section{la'oi .\F{intersperse}.}
ni'o cadga fa lo nu le se ctaipe cu xamgu velcki

.i la .varik.\ cu milxe le ka ce'u sorpa'a lo nu jdikygau le se ctaipe lo ni ce'u vasru lo lerpinsle\ldots je lo lerfu

.i lo nu jdikygau le se ctaipe lo nu ce'u vasru lo lerfu cu cumki lo nu ciska lo lojysra ja co'e be la'o zoi.\ (\D{Vec} \B A \Sym\$ \F{lengthₗ} \Sym\$ \F{intersperseₗ} \B t \Sym\$ \F{toList} \B q) \Sym ≡ (\B n \Sym * 2 \Sym ∸ 1) .zoi.

\begin{code}
intersperse : ∀ {a} → {n : ℕ} → {A : Set a}
            → (t : A) → (q : Vec A n)
            → Vec A $ lengthₗ $ intersperseₗ t $ toList q
intersperse q = fromList ∘ intersperseₗ q ∘ Data.Vec.toList
\end{code}

\chapter{le skicu fancu}
\section{la'oi .\F{plicu'a}.}
ni'o ga jonai ga je ga je la'oi .\B K.\ vasru la'o zoi.\ (\B x \Sym, \B y) .zoi.\ gi la'oi .\B q.\ selvau la'oi .\B x.\ gi ko'a goi la'o zoi.\ \F{plicu'a} \B q \B n \B K .zoi.\ du la'oi .\B y.\ gi ga jonai ga je lo nilzilcmi be la'oi .\B k.\ cu zmadu li pa gi ko'a du la'o zoi.\ \F{plicu'a} \B q \B n \Sym\$ \F{tail} \B K .zoi.\ gi ko'a du la'oi .\B n.

to .i li renoreci pi'e pa pi'e pare cu detri le nu le mu'oi glibau.\ parsing expression .glibau.\ gerna cu na mapti di'u\ldots noi ke'a drani  .i lo skami cu mabla .u'e nai toi

\begin{code}
plicu'a : ∀ {a} {A : Set a} → ℕ → A → List $ List ℕ × A → A
plicu'a _ d []ₗ = d
plicu'a q x ((a , b) ∷ₗ xs) = if q elem a then b else plicu'a q x xs
  where
  _elem_ : ℕ → List ℕ → Bool
  _elem_ _ []ₗ = false
  _elem_ x (y ∷ₗ ys) = (x ≡ᵇ y) ∨ (x elem ys)
\end{code}

\section{la'oi .\F{intdMm}.}
ni'o la'o zoi.\ \F{intdMm} \B a \B b .zoi.\ vasru lo ro kacna'u poi ke'a dubjavmau la'oi .\B a.\ je cu mleca la'oi .\B b.

\begin{code}
intdMm : ℕ → ℕ → List ℕ
intdMm a b = drop a $ upTo b
\end{code}

\section{la'oi .\F{toBnam}.}

\begin{code}
toBnam : Fin 128 → ℕ
toBnam q = plicu'a q' q' ns
  where
  q' : ℕ
  q' = toℕ q
  du40 = 40 ∷ 41 ∷ 60 ∷ 62 ∷ 91 ∷ 93 ∷ 123 ∷ 125 ∷ []ₗ
  cmalu = intdMm 97 123
  ns : List $ List ℕ × ℕ
  ns = (du40 , 40) ∷ (cmalu , q' ∸ 32) ∷ []ₗ
\end{code}

\section{la'oi .\F{toCase}.}
\newcommand\BQ{la'oi .\B q.}
\newcommand\toCase{la'o zoi.\ \F{toCase \B q} .zoi.}
ni'o ga jonai ga je \B q .asycy'i'is.\ sinxa lo latmo glibau lerfu gi \toCase\ du la'oi .\F{Latmo}.\ gi ga jonai ga je la'oi .\B q.\ 

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
  curly = 123 ∷ 125 ∷ []ₗ
  ns : List $ List ℕ × Case
  ns = (cukla , Cukla) ∷ (namcu , Namcu) ∷
       (jganu , Jganu) ∷ (barda , Barda) ∷
       (kurfa , Kurfa) ∷ (curly , Curly) ∷
       (cmalu , Cmalu) ∷ []ₗ
\end{code}

\section{la'oi .\F{toLtyp}.}

\begin{code}
toLtyp : Fin 128 → LTyp
toLtyp q = plicu'a q' Vrici ns
  where
  q' : ℕ
  q' = toℕ q
  kalri = 40 ∷ 60 ∷ 91 ∷ 123 ∷ []ₗ
  ganlo = 41 ∷ 61 ∷ 93 ∷ 125 ∷ []ₗ
  latmo = intdMm 65 91 ++ intdMm 97 123
  xrabo = intdMm 48 58
  ns : List $ List ℕ × LTyp
  ns = (kalri , Kalri) ∷ (ganlo , Ganlo) ∷
       (xrabo , Xrabo) ∷ (latmo , Latmo) ∷ []ₗ
\end{code}

\section{la'oi .\F{toLerfu}.}
ni'o ga jonai ga je la'oi .\B n.\ mleca li parebi gi ko'a goi la'o zoi.\ \F{toLerfu} \B n .zoi.\ me'oi .\F{just}.\ be lo sinxa lo .asycy'i'is.\ lerfu poi meirmoi la'oi .\B n.\ fo le'i ro .asyci'is.\ lerfu gi ko'a me'oi .\F{nothing}.

\begin{code}
toLerfu : ℕ → Maybe Lerfu
toLerfu = finToLerfu ◈ readMaybe 10 ∘ show
  where
  finToLerfu : Fin 128 → Lerfu
  finToLerfu a = record {ctyp = lt; case = cs; bnam = a}
    where
    lt : LTyp
    lt = toLtyp a
    cs : Case
    cs = toCase a
\end{code}

\section{la'oi .\F{genturfa'i}.}
ni'o ga jonai ga je la'oi .\B x.\ .aski gi ga je ko'a goi la'o zoi.\ \F{genturfa'i} \B x.\ .zoi.\ du la'oi .\B x.\ lo ni ce'u vasru gi ro da poi ke';a kacna'u je cu mleca lo nilzilcmi be ko'a zo'u lo meirmoi be da bei fo ko'a cu sinxa lo meirmoi be da bei la'oi .\B x.\ gi ko'a du la'oi .\F{nothing}.

\begin{code}
genturfa'i : String → Maybe $ List Lerfu
genturfa'i = sikh ∘ map c2l? ∘ toListₗ
  where
  _<$>ₘ_ = RawMonad._<$>_ maybeMonad
  sikh : List $ Maybe Lerfu → Maybe $ List Lerfu
  sikh (just x ∷ₗ xs) = _∷_ x <$>ₘ sikh xs
  sikh (nothing ∷ₗ _) = nothing
  sikh []ₗ = just []ₗ
  c2l? : Char → Maybe Lerfu
  c2l? = toLerfu ∘ C2N
\end{code}

\chapter{le fancu be fi lo .uniks.\ midnoi}

\section{la'oi .\F{spkCL}.}
ni'o lo nu xamgu .uniks.\ bo co'e la'o zoi.\ \F{spkCL} \B x .zoi.\ cu rinka lo nu selsnapra lo velski be lo me'oi .\F{ltyp}.\ be la'oi .\B x.

\begin{code}
spkCL : Lerfu → Midnoi
spkCL q = "mplayer " ++ ddvs ++ f (Lerfu.ctyp q)
  where
  f : LTyp → String
  f = map Data.Char.toLower ∘ show
\end{code}

\section{la'oi .\F{spkCC}.}
ni'o lo nu xamgu .uniks.\ bo co'e la'o zoi.\ \F{spkCC} \B x .zoi.\ cu rinka lo nu selsnapra lo velski be lo me'oi .case.\ be la'oi .\B x.

\begin{code}
spkCC : Lerfu → Midnoi
spkCC q = "mplayer " ++ ddvs ++ f (Lerfu.case q)
  where
  f : Case → String
  f = map Data.Char.toLower ∘ show
\end{code}

\section{la'oi .\F{spkCF}.}
ni'o lo nu xamgu .uniks.\ bo co'e la'o zoi.\ \F{spkCF} \B x .zoi.\ cu rinka lo nu selsnapra lo velski be lo me'oi .\F{bnam}.\ be la'oi .\B x.

\begin{code}
spkCF : Lerfu → Midnoi
spkCF q = "mplayer " ++ ddvs ++ f (Lerfu.bnam q)
  where
  f : Fin 128 → String
  f = show ∘ toℕ
\end{code}

\section{la'oi .\F{doit}.}

\begin{code}
doit : ∀ {a} → String → IO {a} ⊤
doit = liftx ∘ doit'
  where
  postulate doit' : String → PIO Unit
  {-# FOREIGN GHC import System.IO #-}
  {-# FOREIGN GHC import Data.Text #-}
  {-# FOREIGN GHC import Control.Monad #-}
  {-# FOREIGN GHC import System.Process #-}
  {-# COMPILE GHC doit' = \_ -> void . runCommand . unpack #-}
\end{code}

\section{la'oi .\F{spk}.}
ni'o ga naja co'e zoi zoi.\ \F{spk} \B q .zoi.\ gi lo skami cu bacru pe'a ru'e la'oi .\B q.

\begin{code}
spk : ∀ {a} → Lerfu → IO {a} ⊤
spk l = vecMapM′ doit $ intersperse denpaXiPa $ spks l
  where
  vecMapM′ : ∀ {a b} → {n : ℕ} → {A : Set a}
           → (A → IO {b} ⊤) → Vec A n → IO {b} ⊤
  vecMapM′ f = IO.List.mapM′ f ∘ toList
  denpaXiPa : Midnoi
  denpaXiPa = "sleep " ++ₛ show selsniduXiPa
  spks : Lerfu → Vec Midnoi 3
  spks l = mapᵥ (flip _$_ l) $ spkCL ∷ᵥ spkCC ∷ᵥ spkCF ∷ᵥ []ᵥ
\end{code}

\section{la'oi .\F{bacru}.}
ni'o ga naja co'e zoi zoi.\ \F{bacru} \B q .zoi.\ gi lo srana be lo skami cu selsnapra lo sinxa be la'o zoi.\ \B q .zoi.

\begin{code}
bacru : ∀ {a} → List Lerfu → IO {a} ⊤
bacru = ignore ∘ IO.List.mapM spkJaDnp ∘ ass
  where
  denpu : ∀ {a} → IO {a} ⊤
  denpu = doit $ "sleep " ++ show selsniduXiRe
  ass : List Lerfu → List $ Fin 1 ⊎ Lerfu
  ass = intersperseₗ (inj₁ $ fromℕ 0) ∘ map inj₂
  spkJaDnp : ∀ {a} → Fin 1 ⊎ Lerfu → IO {a} ⊤
  spkJaDnp = [_,_] (const denpu) spk
\end{code}

\section{la'oi .\F{main}.}
\begin{code}
main = run $ getLine >>=ᵢₒ maybe bacru spojaPe'aRu'e ∘ genturfa'i
  where
  spojaPe'aRu'e : ∀ {a} → IO {a} ⊤
  spojaPe'aRu'e = liftx $ erroy $ jbo ++ "\n\n" ++ eng
    where
    jbo = "ni'o pruce lo lerfu poi \
          \ke'a na srana la .asycy'i'is."
    eng = "Inputs a non-ASCII character."
    postulate erroy : String → PIO Unit
    {-# COMPILE GHC erroy = \_ -> hPutStrLn stderr . unpack #-}
\end{code}
\end{document}
