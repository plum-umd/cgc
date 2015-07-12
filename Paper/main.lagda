\documentclass[preprint,nocopyrightspace]{sigplanconf}
\usepackage{hyperref}
\usepackage{MnSymbol}
\usepackage{url}
\usepackage{galois}
\usepackage{agda}
\usepackage{amsthm}
\usepackage{unicode-math}
\usepackage{verbatim}
\usepackage{newunicodechar}
\usepackage{listings}
\usepackage{mathpartir}
\usepackage{pifont}
\usepackage{enumitem}
\usepackage{balance}
\usepackage{float}
\usepackage{tikz}
\usepackage{pgfplots}


\hypersetup{
  pdfauthor = {David Darais, David Van Horn},
  pdftitle = {Mechanically Verified Calculational Abstract Interpretation},
  pdfkeywords = 
  {Abstract interpretation} 
  {Galois connections} 
  {dependently typed programming} 
  {mechanized metatheory} 
  {static analysis}
}

\floatstyle{boxed}
\restylefloat{figure}

\setlist{noitemsep}
\newcommand\secendswithagda{\relax} % {\vspace{-2em}}

%% Tikz {-{
\usetikzlibrary{matrix,arrows}
\newenvironment{customlegend}[1][]{%
    \begingroup
    % inits/clears the lists (which might be populated from previous
    % axes):
    \csname pgfplots@init@cleared@structures\endcsname
    \pgfplotsset{#1}%
}{%
    % draws the legend:
    \csname pgfplots@createlegend\endcsname
    \endgroup
}%
\def\addlegendimage{\csname pgfplots@addlegendimage\endcsname}
%% Tikz }-}


% Comment out in-line proofs.
% Uncomment to remove proofs.
% \renewenvironment{proof}{\comment}{\endcomment}
%\newcommand\dvh[1]{\marginpar{DVH: #1}}
\newcommand\dvh[1]{\relax}
\newcommand\dcd[1]{\relax}

% Put around in-line Agda text.
\newcommand\A[1]{{\small\(#1\)}}

%https://stackoverflow.com/questions/2920859/is-there-a-way-to-override-latexs-errors-about-double-subscripts-and-superscrip
%\catcode`\_ = 13 \def_#1{\sb{#1}{}}
\catcode`\^ = 13 \def^#1{\sp{#1}{}}

% XXX: can't seem to make sub- and super-scripts work simultaneously.
% work around: always write sub, then super, e.g. x₁ᵐ


\setmainfont[Ligatures=TeX]{Times New Roman}
\setmonofont{DejaVu Sans Mono}

%\setmathfont{STIX Math}
\newfontfamily\missing{STIX Math}
\newcommand\jesus[1]{\newunicodechar{#1}{{\missing #1}}}
\jesus{⊔}
\jesus{𝑖}
\jesus{𝑓}
\jesus{𝑠}
\jesus{𝑡}
\jesus{⟪}
\jesus{⟫}

\newfontfamily\dejavu{DejaVu Sans Mono}
\newfontfamily\asana{Asana-Math.otf}
%\jesus{⟐}
%\jesus{⨄}

\newcommand{\incomp}{\parallel}

\newcommand{\⟅}[1]{&&⟅\mbox{ #1 }⟆}
\newcommand{\⟆}[1]{\\ &\qquad ⟅\mbox{ #1 }⟆}
\newunicodechar{⋕}{\ensuremath{^♯}}
\newunicodechar{𝒫}{\ensuremath{\wp}}
\newunicodechar{⟐}{\ensuremath{\mathbin{⟐}}}
\newunicodechar{↗}{\ensuremath{\rhookrightarrow}}
\newunicodechar{↘}{\ensuremath{\lhookrightarrow}}
\newunicodechar{ᵐ}{\ensuremath{^{m}}}
\newunicodechar{ᶜ}{\ensuremath{^c}}
\newunicodechar{ᵃ}{\ensuremath{^a}}
\newunicodechar{ᵇ}{\ensuremath{^b}}
\newunicodechar{ᵉ}{\ensuremath{^e}}
\newunicodechar{ᵛ}{\ensuremath{^v}}
\newunicodechar{ʳ}{\ensuremath{^r}}
\newunicodechar{ᵘ}{\ensuremath{^u}}
\newunicodechar{ᴬ}{\ensuremath{^A}}
\newunicodechar{ᴮ}{\ensuremath{^B}}
\newunicodechar{⸢}{\ensuremath{\ulcorner}}
\newunicodechar{⸣}{\ensuremath{\urcorner}}
\newunicodechar{‣}{\filledtriangleright}
\newunicodechar{⊴}{{\ensuremath{\preceq}}}
\newunicodechar{⌾}{{\ensuremath{\ominus}}}
\newunicodechar{◇}{{\diamond}}
\newunicodechar{⦂}{:}

\newcommand{\cmark}{\ding{51}}

\newtheorem{lemma}{Lemma}
\newtheorem{theorem}{Theorem}

\AgdaHide{
\begin{code}
{-# OPTIONS --type-in-type #-}
-- We present Agda definitions without universe
-- annotations using the \verb|--type-in-type| compiler flag and with
-- several undefined helper functions for the purpose of
-- presentation. Our full development doesn't rely on
-- \verb|--type-in-type|, is fully universe polymorphic, fully defines
-- all helper functions and theorems, and does not rely on axioms.


module main where

-- A small prelude --

-- sometimes we leave things undefined...
postulate
  … : ∀ {A : Set} → A

-- INFIX
infix 3 _≡_
infix 3 _≢_
infixr 5 _+_
infix  5 _-_

infixr 6 _⨯_
infix  6 _/_
infix  6 _%_
infixr 5 _⨄_
infixr 6 _×_
infixr 3 _,_
infixr 4 _↔_
infixr 9 _∘_
infix 8 _⊑_
infix 8 _≈_
infix 9 _⌾⸢⊑⸣_ 
infixr 9 _⌾⸢≈⸣_
infixr 9 _⌾⸢⊴⸢mon⸣⸣_
infix 8 _∈_
infixr 4 _⇒_
infixl 20 _⋅_
infixr 9 _⊙_
infixr 9 _⟐_
infix 5 _⇄ᶜ_
infix 4 _⇄_
infix 4 _⇄ᵐ_



data _≡_ {A : Set} (x : A) : A → Set where
  ↯ : x ≡ x

data void : Set where

¬ : Set → Set
¬ A = A → void

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

data ℕ : Set where
  Zero : ℕ
  Suc : ℕ → ℕ

data ℤ : Set where
  Neg : ℕ → ℤ
  Zero : ℤ
  Pos : ℕ → ℤ

record ℤ⁺ : Set where
  constructor mk[ℤ⁺]
  field
    x : ℤ
    ≢Zero : x ≢ Zero

postulate
  suc : ℤ → ℤ
  pred : ℤ → ℤ
  _+_ : ℤ → ℤ → ℤ
  _-_ : ℤ → ℤ → ℤ
  _⨯_ : ℤ → ℤ → ℤ
  _/_ : ℤ → ℤ⁺ → ℤ
  _%_ : ℤ → ℤ⁺ → ℤ

data _⨄_ (A : Set) (B : Set) : Set where
  Inl : A → A ⨄ B
  Inr : B → A ⨄ B

record _×_ (A : Set) (B : Set) : Set where
  constructor _,_
  field
    π₁ : A
    π₂ : B
open _×_ public

syntax Σ (λ x → e) = ∃ x 𝑠𝑡 e
infixr 2 Σ
infixr 2 ∃_,,_
record Σ {A : Set} (B : ∀ (x : A) → Set) : Set where
  constructor ∃_,,_
  field
    dπ₁ : A
    dπ₂ : B dπ₁
open Σ public

syntax Σ: A (λ x → e) = ∃ x ⦂ A 𝑠𝑡 e
infixr 2 Σ:
Σ: : (A : Set) (B : ∀ (x : A) → Set) → Set
Σ: A B = ∃ x 𝑠𝑡 B x

_↔_ : Set → Set → Set
A ↔ B = (A → B) × (B → A)

_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
(g ∘ f) x = g (f x)
\end{code}}

\begin{document}

\special{papersize=8.5in,11in}
\setlength{\pdfpageheight}{\paperheight}
\setlength{\pdfpagewidth}{\paperwidth}

\conferenceinfo{CONF 'yy}{Month d--d, 20yy, City, ST, Country} 
\copyrightyear{20yy} 
\copyrightdata{978-1-nnnn-nnnn-n/yy/mm} 
\doi{nnnnnnn.nnnnnnn}

% Uncomment one of the following two, if you are not going for the 
% traditional copyright transfer agreement.

%\exclusivelicense                % ACM gets exclusive license to publish, 
                                  % you retain copyright

%\permissiontopublish             % ACM gets nonexclusive license to publish
                                  % (paid open-access papers, 
                                  % short abstracts)

%\titlebanner{banner above paper title}        % These are ignored unless
%\preprintfooter{short description of paper}   % 'preprint' option specified.

\title{Mechanically Verified Calculational Abstract Interpretation}
%\title{VMCAI: Verified Mechanically, Calculational Abstract Interpretation}

\authorinfo{David Darais}
           {University of Maryland}
           {davdar@cs.umd.edu}
\authorinfo{David Van Horn}
           {University of Maryland}
           {dvanhorn@cs.umd.edu}

%\authorinfo\relax\relax\relax

\maketitle
\begin{abstract}
Calculational abstract interpretation, long advocated by Cousot, is
a technique for deriving correct-by-construction abstract interpreters
from the formal semantics of programming languages.

This paper addresses the problem of deriving
correct-by-\emph{verified}-construction abstract interpreters with the use of a
proof assistant.
%
We identify several technical challenges to overcome with the aim of
supporting verified calculational abstract interpretation that is
faithful to existing pencil-and-paper proofs, supports calculation
with Galois connections generally, and enables the extraction of
verified static analyzers from these proofs.

To meet these challenges, we develop a theory of Galois connections in
monadic style that include a \emph{specification effect}.  Effectful
calculations may reason classically, while pure calculations have
extractable computational content.  Moving between the worlds of
specification and implementation is enabled by our metatheory.

To validate our approach, we give the first mechanically verified
proof of correctness for Cousot's ``Calculational design of a generic
abstract interpreter.''  Our proof ``by calculus'' closely follows the
original paper-and-pencil proof and supports the extraction of a
verified static analyzer.
\end{abstract}

% \category{CR-number}{subcategory}{third-level}

% general terms are not compulsory anymore, 
% you may leave them out
%% \terms
%% term1, term2

\keywords
Abstract interpretation, Galois connections, dependently typed programming, mechanized metatheory, static analysis

\section{Introduction}
\label{sec:introduction}

Abstract interpretation
\cite{dvanhorn:Cousot:1977:AI,dvanhorn:Cousot1979Systematic} is a
foundational and unifying theory of semantics and abstraction
developed by P.~Cousot and R.~Cousot, which has had notable impact on
the theory and practice of program analysis and verification.
%
Traditionally, static analyses and verification frameworks such as
type systems, program logics, or constraint-based analyses start by
first postulating a specification of an abstract semantics.  Only
afterward is this abstraction proved correct with respect to the
language's semantics.
%
This proof establishes \emph{post facto} that the analysis or logic
\emph{is} an abstract interpretation of the underlying language
semantics.

P.~Cousot has also advocated an alternative approach to the design of
abstract interpreters called \emph{calculational} abstract
interpretation~\cite{dvanhorn:Cousot98-5, local:cousot-mit},
which involves systematically applying abstraction functions to a
programming language semantics in order to \emph{derive} an
abstraction.  Abstract interpretations derived in the calculational
style are correct by construction (assuming no missteps are made in
the calculation) and need not be proved sound after the fact.


This paper addresses the problem of mechanically verifying the
derivations of calculational abstract interpretation using a proof
assistant.  We identify several technical challenges to modelling the
theory of abstract interpretation in a constructive, dependent type
theory and then develop solutions to these challenges.  Paramount in
overcoming these challenges is effectively representing Galois
connections and maintaining a modality between specifications and
implementations to enable program extraction.  To do this, we propose
a novel form of Galois connections endowed with monadic structure
which we dub \emph{Kleisli Galois connections}.  This monadic
structure maintains a distinction between calculation at the
specification level, which may be non-constructive, and at the
implementation level, which must be constructive.  Remarkably,
calculations are able to move back and forth between these modalities
and verified programs may be extracted from the end result of
calculation.


To establish the adequacy of our theory, we prove it is sound and
complete with respect to a subset of traditional Galois connections,
and isomorphic to a space of fully constructive Galois connections,
diagrammed in figure~\ref{fig:gc-venn}.
%
To establish the utility of our theory, we construct a framework for
abstract interpretation with Kleisli Galois connections in the
dependently typed programming language and proof-assistant,
Agda~\cite{local:norell:thesis}.
%
To validate our method, we re-derive Cousot's generic compositional
static analyzer for an imperative language by abstract interpretation
of the language's formal semantics.  Consequently we obtain a verified
proof of the calculation and extract a verified implementation of
Cousot's static analyzer.


\begin{figure}
\begin{center}
\input{snd-cpt.tikz}
\end{center}
\caption{Relations between classical Galois connections and their Kleisli and
constructive counterparts.}
\label{fig:gc-venn}
\end{figure}


\paragraph{Contributions}
This paper contributes:
\begin{enumerate}
\item a framework for mechanically verified abstract interpretation
  that supports calculation and program extraction,
\item a theory of specification effects in Galois connections,  and
\item a verified proof of Cousot's generic abstract interpreter
  derived by calculus.
\end{enumerate}

To supplement these contributions, we provide two artifacts.  The
first is the source code of this document, which is a literate Agda
program and verified at typesetting-time.  For presentation purposes,
it assumes a few lemmas and is less general than it could be.  The
second artifact is a stand-alone Agda program that develops all of the
results in this paper in full detail, including the mathematically
stated theorems and lemmas.  Claims are marked with a ``\cmark''
whenever they have been proved in Agda.  (All claims are checked.)
%
The full development is found at:
\begin{center}
{\scriptsize\url{https://github.com/plum-umd/mvcai}}
\end{center}

Although largely self-contained, this paper assumes a basic
familiarity with abstract interpretation and dependently typed
programming.  There are excellent tutorials on both
(\cite{local:CousotCousot04-WCC, local:cousot-mit} and
\cite{dvanhorn:Norell2009Dependently,dvanhorn:Bove2009Brief},
respectively).




\section{Calculational Abstract Interpretation}
\label{sec:cai}

To demonstrate our approach to mechanizing Galois connections we
present the calculation of a generic abstract interpreter, as
originally presented by Cousot~\cite{dvanhorn:Cousot98-5}.
%
The setup is a simple arithmetic expression language which includes a
random number expression, and is otherwise standard.  The syntax and
semantics is given in figure~\ref{fig:lang}.



A collecting semantics is defined as a monotonic (written \(↗\))
predicate transformer using \(\_⊢\_↦\_\):
\begin{align*}
  & eval ∈ exp → 𝒫(env) ↗ 𝒫(val)\\
  & eval[e](R) ≔ \{ v\ |\ ∃ ρ ∈ R : ρ ⊢ e ↦ v \}
\end{align*}

In the setting of abstract interpretation, an analysis for a program
\(e\) is performed by: (1) defining another semantics \(eval⋕\),
where \(eval⋕\) is shown to soundly approximate the semantics of
\(eval\), and (2) executing the \(eval⋕[e]\) semantics and
observing the output.
%
There are many different methods for arriving at \(eval⋕\),
however the calculational approach prescribes a methodology for
defining \(eval⋕\) through calculus, the results of which are
correct by construction.

To arrive at \(eval⋕\) through calculus we fist establish an abstraction
for the domain \(𝒫(env) ↗ 𝒫(val)\), which we call \(env⋕ ↗ val⋕\). After
abstracting the domain, we induce a \emph{best specification} for any abstract
semantics \(eval⋕ ∈ env⋕ ↗ val⋕\). Then we perform calculation on this
specification to arrive at a \emph{definition} for \(eval⋕\). Key in this
methodology is the requirement that \(eval⋕\) be an \emph{algorithm},
otherwise we would just define \(eval⋕\) to be the induced best
specification and be done.

We induce the best specification for \(eval\) by: (1) constructing
an abstraction for values \(val⋕\) and proving it is a valid
abstraction of \(𝒫(val)\), (2) constructing an abstraction for
environments \(env⋕\) and proving it is a valid abstraction of
\(𝒫(env)\), (3) lifting these abstractions pointwise to \(env⋕ ↗
val⋕\) and proving it is a valid abstraction of \(𝒫(env) ↗ 𝒫(val)\),
and (4) inducing \(α^{e→v}(eval)\) as the best abstraction of
\(eval\) using the results from (3).


\paragraph{Abstracting values}

We pick a simple sign abstraction for \(val⋕\), however our final
calculated abstract interpreter will be fully generic to \(val⋕\), as is
done in Cousot's original derivation~\cite{dvanhorn:Cousot98-5}.
\begin{align*}
v⋕ ∈ val⋕ ≔ \{-,0,+,⊤,⊥\}
\end{align*}
The set \(val⋕\) has the partial ordering \(⊥ ⊑ - \incomp 0 \incomp + ⊑
⊤\) where \(\_ \incomp \_\) is notation for incomparable.  

Justifying that \(val⋕\) is a valid abstraction takes the form of a
Galois connection: 
\[𝒫(val) \galois{αᵛ}{γᵛ} val⋕\text.\] 
Galois connections are mappings between concrete objects and abstract objects
which satisfy soundness and completeness properties. For \(val⋕\), the Galois
connection with \(𝒫(val)\) is defined:
\begin{align*}
αᵛ    &∈ 𝒫(val) ↗ val⋕                       & γᵛ    &∈ val⋕ ↗ 𝒫(val)  \\
αᵛ(V) &≔ - \mbox{ if }  ∃ v ∈ V : v < 0           & γᵛ(-) &≔ \{ v\ |\ v < 0 \}   \\
      &⊔\ \ 0 \  \mbox{ if }  0 ∈ V               & γᵛ(0) &≔ \{ 0 \}             \\
      &⊔\   +  \mbox{ if }  ∃ v ∈ V : v > 0       & γᵛ(+) &≔ \{ v\ |\ v > 0 \}   \\
      &                                           & γᵛ(⊤) &≔ ℤ                   \\
      &                                           & γᵛ(⊥) &≔ ∅
\end{align*}
\(αᵛ\) is called the \emph{abstraction} function, which maps concrete sets of
numbers in \(𝒫(val)\) to a finite, symbolic representations in \(val⋕\).
\(γᵛ\) is called the \emph{concretization} function, mapping abstract symbols
in \(val⋕\) concrete sets in \(𝒫(val)\).

% {{{
\begin{figure}
{\small
\[
\begin{array}{rclcll}
n & ∈ & lit    & ≔ & ℤ                    &\mbox{integer literals}\\
x & ∈ & var    &   &                      &\mbox{variables}\\
u & ∈ & unary  & ⩴ & +\ |\ -              &\mbox{unary operators}\\
b & ∈ & binary & ⩴ & +\ |\ -\ |\ ⨯\ |\ \% &\mbox{binary operator}\\
e & ∈ & exp    & ⩴ & n                    &\mbox{integer literal}\\
  &   &        & | & x                    &\mbox{variable}\\
  &   &        & | & rand                 &\mbox{random integer}\\
  &   &        & | & u\;e                 &\mbox{unary operator}\\
  &   &        & | & e\;b\;e              &\mbox{binary operator}
\end{array}
\]

\begin{align*}
v        &∈ val ≔ ℤ                     &&\mbox{values}\\
⟦\_⟧ᵘ    &∈ unary → (val → val)         &&\mbox{unary op denot.}\\
⟦\_⟧ᵇ    &∈ binary → (val × val ⇀ val)  &&\mbox{binary op denot.}\\
\\
ρ        &∈ env ≔ var ⇀ val             &&\mbox{environments}\\
\_⊢\_↦\_ &∈ 𝒫(env × exp × val)          &&\mbox{eval. relation}
\end{align*}
%
\begin{mathpar}
\inferrule{\ }{ρ ⊢ n ↦ n} %[integer literals]

\inferrule{\ }{ρ ⊢ x ↦ ρ(x)} %[variables]

\inferrule{n ∈ ℤ}{ρ ⊢ rand ↦ n} %[random integers]

\inferrule{ρ ⊢ e ↦ v}{ρ ⊢ u\;e ↦ ⟦u⟧ᵘ(v)} %[unary operators]

\inferrule{ρ ⊢ e₁ ↦ v₁ \\ ρ ⊢ e₂ ↦ v₂}{ρ ⊢ e₁\;b\;e₂ ↦ ⟦b⟧ᵇ(v₁,v₂)} %[binary operators]
\end{mathpar}}
\caption{Syntax and semantics}
\label{fig:lang}
\end{figure}
% }}}

This Galois connection is \emph{extensive}: properties of values in
\(val⋕\) imply properties of related concrete values in \(𝒫(val)\).
It is \emph{reductive}: \(αᵛ\) is the best possible abstraction given
\(γᵛ\).

\begin{lemma}[\(extensiveᵛ\)]
\label{thm:extensive}
\(γᵛ ∘ αᵛ\) is extensive, that is: 
\begin{equation*}
∀(V ∈ 𝒫(val)). V ⊆ γᵛ(αᵛ(V))\text.
\end{equation*}
\end{lemma}%

\begin{lemma}[\(reductiveᵛ\)]
\label{thm:reductive}
\(αᵛ ∘ γᵛ\) is reductive, that is: 
\begin{equation*}
∀ (v⋕ : val⋕). αᵛ(γᵛ(v⋕)) ⊑ v⋕\text.
\end{equation*}
\end{lemma}
\noindent

\paragraph{Abstracting environments}

We abstract \(𝒫(env)\) with \(env⋕\):
\begin{gather*}
ρ⋕ ∈ env⋕ ≔ var ⇀ val⋕
\end{gather*}

Justifying that \(env⋕\) is a valid abstraction is done
through a Galois connection \(𝒫(env) \galois{αᵉ}{γᵉ} env⋕\):
\begin{align*}
αᵉ    &: 𝒫(env)       ↗ env⋕                         \\
% αᵉ    &: 𝒫(var ⇀ val) ↗ var ⇀ \hat{val}                   \\
αᵉ(R) &≔ λ(x). αᵛ(\{ρ(x)\ |\ ρ ∈ R\})                  \\
γᵉ          &: env⋕              ↗ 𝒫(env)                  \\
% γᵉ          &: (var ⇀ \hat{val}) ↗ 𝒫(var → val)                 \\
γᵉ(ρ⋕) &≔ \{ρ\ |\ ∀(x). ρ(x) ∈ γᵛ(ρ⋕(x))\}
\end{align*}
\begin{lemma}[\(extensiveᵉ\)]
\label{thm:extensivee}
\(αᵉ ∘ γᵉ\) is extensive, that is:
\begin{equation*}
∀(R ∈ 𝒫(env)). R ⊆ γᵉ(αᵉ(R))\text.
\end{equation*}
\end{lemma}

\begin{lemma}[\(reductiveᵉ\)]
\label{thm:reductivee}
\(γᵉ ∘ αᵉ\) is reductive, that is:
\begin{equation*}
  ∀(ρ⋕ ∈ env⋕). αᵉ(γᵉ(ρ⋕)) ⊑ ρ⋕\text.
\end{equation*}
\end{lemma}

% {{{
\begin{figure*}
{\small
\[\arraycolsep=1.2pt\def\arraystretch{1.2}
\begin{array}{@{}l@{}l@{\qquad}ll}
\multicolumn{3}{@{}l}{\mbox{\bf Numeric literals}}\\
  & αᵛ(\{ v\ |\ ∃ ρ ∈ γʳ(ρ⋕) : ρ ⊢ n ↦ v \})\\
  & = αᵛ(\{n\}) 
    \⟅{ definition of \(ρ ⊢ n ↦ v\) }\\
  & ≜ eval⋕[n](ρ⋕)
  \⟅{ by defining \(eval⋕[n](ρ⋕) ≔ αᵛ(\{n\})\) }\\[.8em]
\multicolumn{3}{@{}l}{\mbox{\bf Variable Reference}}\\
  & αᵛ (\{ v\ |\ ∃ ρ ∈ γʳ ( ρ⋕) : ρ ⊢ x ↦ v \} )\\
  & = αᵛ(\{ρ(x)\ |\ ρ ∈ γʳ(ρ⋕)\})
  \⟅{ definition of \(ρ ⊢ x ↦ v\) }\\
  & = α^{e→v}(λ(R). \{ ρ(x)\ |\ ρ ∈ R \})(ρ⋕)
  \⟅{ definition of \(α^{e→v}\) }\\ 
  & ⊑ ρ⋕(x)
  \⟅{ Fact: \(α^{e→v}(λ(ρ). \{ ρ(x) | ρ ∈ R \}) ⊑ (λ(ρ⋕). ρ⋕(x))\) }\\
  & ≜ eval⋕[x](ρ⋕)
  \⟅{ by defining \(eval⋕[x](ρ⋕) ≔ ρ⋕(x)\) }\\[.8em]
\multicolumn{3}{@{}l}{\mbox{\bf Unary operators}}\\
  & αᵛ({ v | ∃ ρ ∈ γʳ(ρ^) : ρ ⊢ u\;e ↦ v})\\
  & = αᵛ(\{ ⟦u⟧ᵘ(v) | ∃ ρ ∈ γʳ(ρ⋕) : ρ ⊢ e ↦ v\}) 
  \⟅{ definition of \(ρ ⊢ u\;e ↦ v\) }\\
  & ⊑ αᵛ(\{ ⟦u⟧ᵘ(v)\ |\ v ∈ γᵛ(αᵛ(\{v'\ |\ ∃ ρ ∈ γʳ(ρ⋕) : ρ ⊢ e ↦ v \})) \}) 
  \⟅{ \(αᵛ\) monotone and \(γᵛ ∘ αᵛ\) extensive }\\
  & = αᵛ(\{ ⟦u⟧ᵘ(v)\ |\ v ∈ γᵛ(α^{e→v}(eval[e])(ρ⋕)) \})
  \⟅{ definition of \(α^{e→v}\) and \(eval[e]\) }\\
  & ⊑ αᵛ(\{ ⟦u⟧ᵘ(v)\ |\ v ∈ γᵛ(eval⋕[e](ρ⋕)) \})
  \⟅{ \(αᵛ\) monotonic and inductive hypothesis for \(e\) }\\
  & = α^{v→v}(λ(V). \{ ⟦u⟧ᵘ(v)\ |\ v ∈ V \})(eval⋕[e](ρ⋕))
  \⟅{ definition of \(α^{v→v}\) }\\
  & ⊑ ⟦u⟧ᵘ⋕(eval⋕[e](ρ⋕))
  \⟅{ by assuming \(α^{v→v}(λ(V) → \{ ⟦u⟧ᵘ(v)\ |\ v ∈ V \}) ⊑ ⟦u⟧ᵘ⋕\) }\\
  & ≜ eval⋕[u\;e](ρ⋕)
  \⟅{ by defining \(eval⋕[u\;e](ρ⋕) ≔ ⟦u⟧ᵘ⋕(eval⋕[e](ρ⋕))\) }
\end{array}
\]}
\caption{Cousot's \emph{classical} calculation of the Generic Abstract Interpreter}
\label{fig:classic}
\end{figure*}
% }}}


\paragraph{Abstracting the function space}

To abstract \(𝒫(env) ↗ 𝒫(val)\), we abstract its
components pointwise with \(env⋕ ↗ val⋕\), and justify the
abstraction with another Galois connection.
\begin{align*}
α^{e→v}    &: (𝒫(env) ↗ 𝒫(val)) ↗ (env⋕ ↗ val⋕)\\
α^{e→v}(f) &≔ αᵛ ∘ f ∘ γᵉ\\
γ^{e→v}          &: (env⋕ ↗ val⋕) ↗ (𝒫(env) ↗ 𝒫(val))\\
γ^{e→v}(f⋕) &≔ γᵛ ∘ f⋕ ∘ αᵉ
\end{align*}

\begin{lemma}[\(extensive^{e→v}\)]
\label{thm:extensive-pointwise}
\(γ^{e→v} ∘ α^{e→v}\) is extensive, that is:
\begin{equation*}
∀(f ∈ 𝒫(env) ↗ 𝒫(val)). f ⊑ γ^{e→v}(α^{e→v}(f))\text.
\end{equation*}

\end{lemma}
\begin{lemma}[\(reductive^{e→v}\)]
\label{thm:reductive-pointwise}
\(α^{e→v} ∘ γ^{e→v}\) is reductive, that is:
\begin{equation*}
∀(f⋕ ∈ env⋕ ↗ val⋕). α^{e→v}(γ^{e→v}(f⋕)) ⊑ f⋕\text.
\end{equation*}
\end{lemma}

\paragraph{Inducing a best specification}

A best specification for any abstraction of \(eval\) is induced from the
Galois connection \[𝒫(env) ↗ 𝒫(val) \galois{α^{e→v}}{γ^{e→v}} env⋕ ↗ val⋕\] as
\(α^{e→v}(eval)\), or \(αᵛ ∘ eval ∘ γᵉ\). An abstract semantics
\(eval⋕\) can then be shown to satisfy this specification through an
ordered relationship \(α^{e→v}(eval) ⊑ eval⋕\).

The process of calculation is to construct \(eval⋕\) through a chain
of ordered reasoning:
\(α^{e→v}(eval[e]) = αᵛ ∘ eval[e] ∘ γᵉ ⊑ ... ⊑ eval⋕[e]\)
such that \(eval⋕\) is an algorithm, at which point we have defined
\(eval⋕[e]\) through calculation.

\subsection{Calculating the Abstract Interpreter}

The calculation of \(eval⋕\) begins by expanding definitions:
\begin{align*}
  & α^{e→v}(eval[e])(ρ⋕)\\
  & = αᵛ(eval[e](γʳ(ρ⋕)))                  \⟅{ definition of \(α^{e→v}\) }\\
  & = αᵛ(\{ v\ |\ ∃ ρ ∈ γʳ(ρ⋕) : ρ ⊢ e ↦ v \}) \⟅{ definition of \(eval[e]\) }
\end{align*}
In case \(γʳ(ρ⋕) = ∅\), then have \(α^{e→v}(eval[e])(ρ⋕) = αᵛ(∅) =
⊥\).  Otherwise, we proceed by induction on \(e\), assuming \(γʳ(ρ⋕)\)
is nonempty.




\begin{figure}[t]
\begin{code}

val = ℤ
size = ℕ
data var : size → Set where
  Zero  : ∀ {Γ}         → var (Suc Γ)
  Suc   : ∀ {Γ} → var Γ → var (Suc Γ)

data unary   : Set where [+] [-]             : unary
data binary  : Set where [+] [-] [⨯] [/] [%] : binary

data exp (Γ : size) : Set where
  Num       : ℤ → exp Γ
  Var       : var Γ → exp Γ
  Rand      : exp Γ
  Unary[_]  : unary → exp Γ → exp Γ
  Binary[_] : binary → exp Γ → exp Γ → exp Γ

⟦_⟧ᵘ : unary → val → val
⟦ [+] ⟧ᵘ = suc
⟦ [-] ⟧ᵘ = pred

data _∈⟦_⟧ᵇ_ : val → binary → val × val → Set where
  [+]  :  ∀ {v₁ v₂} →          (v₁ + v₂)             ∈⟦ [+] ⟧ᵇ (v₁ , v₂)
  [-]  :  ∀ {v₁ v₂} →          (v₁ - v₂)             ∈⟦ [-] ⟧ᵇ (v₁ , v₂)
  [⨯]  :  ∀ {v₁ v₂} →          (v₁ ⨯ v₂)             ∈⟦ [⨯] ⟧ᵇ (v₁ , v₂)
  [/]  :  ∀ {v₁ v₂} 
          → (p : v₂ ≢ Zero) →  (v₁ / mk[ℤ⁺] v₂ p)    ∈⟦ [/] ⟧ᵇ (v₁ , v₂)
  [%]  :  ∀ {v₁ v₂} 
          → (p : v₂ ≢ Zero) →  (v₁ % mk[ℤ⁺] v₂ p)    ∈⟦ [%] ⟧ᵇ (v₁ , v₂)

data env : size → Set where
  [] : env Zero
  _∷_ : ∀ {Γ} → val → env Γ → env (Suc Γ)

_[_] : ∀ {Γ} → env Γ → var Γ → val
(v ∷ ρ) [ Zero   ] = v
(v ∷ ρ) [ Suc x  ] = ρ [ x ]

data _⊢_↦_ {Γ} : env Γ → exp Γ → val → Set where
  Num    :  ∀ {ρ n}                 → ρ ⊢ Num n              ↦ n
  Var    :  ∀ {ρ x}                 → ρ ⊢ Var x              ↦ ρ [ x ]
  Rand   :  ∀ {ρ n}                 → ρ ⊢ Rand               ↦ n
  Unary  :  ∀ {ρ o e v₁ v₂}
            → v₂ ≡ ⟦ o ⟧ᵘ v₁        → ρ ⊢ e                  ↦ v₁ 
                                    → ρ ⊢ Unary[ o ] e       ↦ v₂
  Binary :  ∀ {ρ o e₁ e₂ v₁ v₂ v₃}  
            → v₃ ∈⟦ o ⟧ᵇ (v₁ , v₂)  → ρ ⊢ e₁                 ↦ v₁ 
                                    → ρ ⊢ e₂                 ↦ v₂ 
                                    → ρ ⊢ Binary[ o ] e₁ e₂  ↦ v₃
\end{code}%
\caption{Syntax and semantics in Agda}
\label{fig:lang-agda}
\end{figure}



In figure~\ref{fig:classic}, we show the calculations for literals,
variables, and unary operator expressions. 
This calculation is generic, meaning it is parameterized by implementations for
abstracting random numbers, and unary and binary operators.
The parameters for the unary operator case are an abstract unary denotation
\(⟦\_⟧ᵘ⋕ ∈ val⋕ ↗ val⋕\) and a proof that it abstracts concrete unary
denotation:
\[α^{v→v}(λ(V). \{ ⟦u⟧ᵘ(v)\ |\ v ∈ V \})(v⋕) ⊑ ⟦u⟧ᵘ⋕(v⋕)\]
The calculation for the remaining forms can be found in Cousot's
notes~\cite[lec.~16]{local:cousot-mit}. This calculation serves to contrast the
constructive calculation we develop in
section~\ref{sec:constructive-calculation}, which is more amenable to
verification and extraction in Agda.

\section{Mechanization: The Easy Parts}
\label{sec:difficulties}


We aim to mechanize calculations of the style presented in
figure~\ref{fig:classic}.  Some parts are easy; we start with those.

Figure~\ref{fig:lang-agda} gives the syntax and semantics in Agda.
%
Variables are modelled as an index into an environment of statically
known size; otherwise, the syntax of \(exp\) translates directly.
%
The meaning of unary operators is given by a function,
\A{\AgdaFunction{⟦\_⟧ᵘ}}, while binary operators are defined
relationally, \A{\AgdaFunction{\_∈⟦\_⟧ᵇ\_}}, to account for the
partiality of \A{\AgdaInductiveConstructor{[/]}} and
\A{\AgdaInductiveConstructor{[\%]}}, which take elements of
\A{\AgdaDatatype{ℤ⁺}}: integers paired with a proof of being
non-zero.
%
Environments are modelled intentionally as a list of values, rather
than extensionally with Agda's function space.  Environments are
statically well-formed to contain a value mapping for every variable,
resulting in a total lookup function \A{\AgdaFunction{\_[\_]}}.
Partiality is eliminated from the definition of environment lookup by static
well-formedness.
%
The relational semantics is defined using a dependent inductive type,
\A{\AgdaFunction{\_⊢\_↦\_}}.

To encode \(eval\), we create powersets using \emph{characteristic
  functions}, assuming set-theoretic primitives (defined later), where
the judgement \A{\AgdaBound{x}} \A{\AgdaFunction{∈}}
\A{\AgdaFunction{mk[𝒫](}}\A{\AgdaBound{φ}}\A{\AgdaFunction{)}} holds
\emph{iff} \A{\AgdaBound{φ}(}\A{\AgdaBound{x}}\A{\AgdaBound{)}} is
inhabited.

\AgdaHide{
\begin{code}
module PostulatedPowerset where
  postulate
\end{code}}
\begin{code}

    𝒫      : Set → Set
    mk[𝒫]  : ∀ {A} → (A → Set) → 𝒫 A
    _∈_    : ∀ {A} → A → 𝒫 A → Set

\end{code}
%
The \A{\AgdaFunction{eval}} function is then defined using an existential type inside
of a characteristic function:

\begin{code}

  eval[_] : ∀ {Γ} → exp Γ → 𝒫 (env Γ) → 𝒫 val
  eval[ e ] R = mk[𝒫] (λ v → ∃ ρ 𝑠𝑡 (ρ ∈ R) × (ρ ⊢ e ↦ v))

\end{code}






\section{Constructive Abstract Interpretation}
\label{sec:new}

\begin{figure*}
\label{fig:constr}
{\small
\[\arraycolsep=1.2pt\def\arraystretch{1.2}
\begin{array}{@{}l@{}lll}
\multicolumn{3}{@{}l}{\mbox{\bf Numeric literals}}\\
& αᵐᵛ*(evalᵐ[n]*(γᵐʳ(ρ⋕)))\\
& = αᵐᵛ*(\{ v\ |\ ∃ ρ ∈ γᵐʳ(ρ⋕) : ρ ⊢ n ↦ v \}) 
  \⟅{ definition of \(evalᵐ[n]*\) }\\
& ⊑ αᵐᵛ*(return(n))
  \⟅{ definition of \(ρ ⊢ n ↦ v\) }\\
& = αᵐᵛ(n)
  \⟅{ monad right unit }\\
& = return(ηᵛ(n))
  \⟅{ induced \(ηᵛ\) from \(αᵐᵛ\) }\\
& ≜ return(evalᵐ⋕[n](ρ⋕))
  \⟅{ by defining \(evalᵐ⋕[n](ρ⋕) ≔ ηᵛ(n)\) }
\\[.8em]
\multicolumn{3}{@{}l}{\mbox{\bf Variable references}}\\
& αᵐᵛ*(evalᵐ[x]*(γᵐʳ(ρ⋕)))\\
& = αᵐᵛ*(\{ v\ |\ ∃ ρ ∈ γᵐʳ(ρ⋕) : ρ ⊢ x ↦ v \})
  \⟅{ definition of \(evalᵐ[x]*\) }\\
& = αᵐᵛ*(\{ ρ(x)\ |\ ρ ∈ γᵐʳ(ρ⋕)\})
  \⟅{ definition of \(ρ ⊢ x ↦ v\) }\\
& = αᵐᵛ*((λ(ρ). return(ρ(x)))*(γᵐʳ(ρ⋕))) 
  \⟅{ monad unit and associativity }\\
& = α^{e→ᵐv}(λ(ρ). return(ρ(x)))(ρ⋕)
  \⟅{ definition of \(α^{e→ᵐv}\) }\\
& ⊑ return(ρ⋕(x))
  \⟅{ Fact: \(α^{e→ᵐv}(λ(ρ). return(ρ(x))) ⊑ (λ(ρ⋕). return(ρ⋕(x)))\) }\\
& ≜ return(evalᵐ⋕[x](ρ⋕))
  \⟅{ by defining \(evalᵐ⋕[x](ρ⋕) ≔ ρ⋕[x]\) }\\[.8em]
%
\multicolumn{3}{@{}l}{\mbox{\bf  Unary operators}}\\
%
& αᵐᵛ*(evalᵐ[u\;e]*(γᵐʳ(ρ⋕))) \\
& = αᵐᵛ*(\{ ⟦u⟧ᵘ(v)\ |\ ∃ ρ ∈ γᵐʳ(ρ⋕) : ρ ⊢ e ↦ v\})
  \⟅{ definition of \(evalᵐ[u\;e]*\) }\\
& = αᵐᵛ*((λ(v). return(⟦u⟧ᵘ(v)))*(\{ v\ |\ ∃ ρ ∈ γᵐʳ(ρ⋕) : ρ ⊢ e ↦ v\}))
  \⟅{ monad unit and associativity }\\
  & ⊑ αᵐᵛ*((λ(v). return(⟦u⟧ᵘ(v)))*\\
& \qquad (\{ v\ |\ v ∈ γᵐᵛ*(αᵐᵛ*(\{v'\ |\ ∃ ρ ∈ γᵐʳ(ρ⋕) : ρ ⊢ e ↦ v'\}))\}))
  \⟅{ \(γᵐᵛ ⟐ αᵐᵛ\) extensive }\\
  & = αᵐᵛ*((λ(v). return(⟦u⟧ᵘ(v)))*(\{ v\ |\ v ∈ γᵐᵛ*(α^{e→ᵐv}(evalᵐ[e])(ρ⋕)) \})) 
  \⟅{ definition of \(α^{e→ᵐv}\) and \(evalᵐ[e]\) }\\
  & ⊑ αᵐᵛ*((λ(v). return(⟦u⟧ᵘ(v)))*(γᵐᵛ*(return(evalᵐ⋕[e](ρ⋕)))))
  \⟅{ monotonicity of \(αᵛ\), \(return\) and \(*\), 
    and IH for \(e\) }\\
    & = α^{v→ᵐv}(λ(v). return(⟦u⟧ᵘ(v)))*(return(evalᵐ⋕[e](ρ⋕)))
  \⟅{ definition of \(α^{v→ᵐv}\) and monad associativity }\\
  & ⊑ (λ(v⋕). return(⟦u⟧ᵘ⋕(v⋕)))*(return(evalᵐ⋕[e](ρ⋕)))
  \⟅{ by assuming \(α^{v→ᵐv}(λ(v). return(⟦u⟧ᵘ(v)))(v⋕) ⊑ return(⟦u⟧ᵘ⋕(v⋕))\) }\\
& = return(⟦u⟧ᵘ⋕(evalᵐ⋕[e](ρ⋕)))                       
  \⟅{ monad right unit }\\
& ≜ return(evalᵐ⋕[u\;e])(ρ⋕)                  
  \⟅{ by defining \(evalᵐ⋕[u\;e](ρ⋕) ≔ ⟦u⟧ᵘ(evalᵐ⋕(ρ⋕))\) }
\end{array}
\]}
\caption{Our \emph{constructive} calculation of the Generic Abstract Interpreter}
\end{figure*}


The Galois connections presented in the section~\ref{sec:cai} are not
immediately amenable to encoding in Agda, or constructive logic in general. The
heart of the problem is the definition of \(αᵛ\):
\nopagebreak
\[
\begin{array}{rcl}
αᵛ(V) &≔& - \mbox{ if }  ∃ v ∈ V : v < 0               \\
      &⊔&\ \ 0 \  \mbox{ if }  0 ∈ V                   \\
      &⊔&\   +  \mbox{ if }  ∃ v ∈ V : v > 0       
\end{array}
\]
%
A literal translation of \(αᵛ\) to constructive logic would require
\emph{deciding} predicates such as \(∃ v ∈ V : v < 0\) in order to return a
value of type \(val⋕\), however such predicates are in general
undecidable.

There are a number of known options for encoding \(αᵛ\), each of which has
shortcomings for our goal of extracting computation from the result of a
verified calculation.

\paragraph{Non-solution 1: Admit Excluded Middle}

One option to defining \(αᵛ\) is to to postulate the law of excluded middle:

\AgdaHide{
\begin{code}
postulate
\end{code}}
\begin{code}

  excluded-middle : ∀ (P : Set) → P ⨄ (¬ P)

\end{code}
This axiom imbues the logic with classical reasoning, is logically
consistent, and would allow us to perform case analysis on the existential
predicate \(∃ v ∈ V :v < 0\) to complete a definition for \(αᵛ\). This approach
has the drawback that definitions no longer carry computational content, and
cannot be extracted or computed with in general.

\paragraph{Non-solution 2: Work in Powerset}

Another option is to always work inside the powerset type \(𝒫\),
meaning \(αᵛ\) would have type \(𝒫(val) ↗ 𝒫(val⋕)\). This
approach also allows for a successful definition of \(αᵛ\), but again
suffers from not being a computation.  Functions at type \(𝒫(val) ↗
𝒫(val⋕)\) cannot be executed to produce values at type
\(val⋕\), which is the end goal. 

\paragraph{Non-solution 3: Only use Concretization}

The state of the art in mechanizing abstract interpreters is to use
``\(γ\)-only'' encodings of soundness and completeness
properties~\cite{dvanhorn:Jourdan2015FormallyVerified}. However, this
approach has a number of drawbacks: it does not support calculation,
it gives the engineer no guidance as to whether or not their \(γ\)
is sensible (sound and complete w.r.t. \(α\)), and it is less
compositional than the Galois connection framework.

\subsection{Our Solution: A Specification Effect}

The problem of encoding Galois connections in constructive logic exists with an
apparent dichotomy: if the construction is too classical then one cannot
extract computation from the result, and if it is too constructive it prevents
the definition of classical structures like Galois connections. We find a
solution to this problem through a new Galois connection framework which marks
the transition from constructive to classical with a \emph{monadic effect}.
Classical and constructive reasoning can then be combined within the same
framework, and classical constructions can be promoted to constructive ones
after they are shown to be effect-free.

We find a solution to the problem of encoding calculational abstract
interpretation in constructive logic by reformulating the definition of a
Galois connection into the powerset Kleisli category. This approach:
\begin{enumerate}
\item is rooted in the first principles of Galois connections,
\item allows for the definition of Galois connections which would otherwise
      require classical reasoning (like excluded middle),
\item supports abstract interpretation by calculus, and
\item allows for the extraction of algorithms from calculations.
\end{enumerate}

The transition to the powerset Kleisli category results in abstraction and
concretization mappings which have a \emph{specification effect}, meaning they
return a classical powerset value, which we model non-constructively. The laws
that accompany the Galois connection will then introduce and eliminate this
effect. Combined with monad laws, which also introduce and eliminate monadic
effects, we are able to mix constructive and classical reasoning and extract an
algorithm from the result of calculation, after all introduced effects have
been eliminated.

\subsection{Kleisli Galois Connections}
\label{sec:kleisli-galois-connections}

Kleisli Galois connections are formed by re-targeting the classical Galois
connection framework from the category of posets to the powerset
Kleisli category. The morphisms in this category are monotonic monadic
functions \(A ↗ 𝒫(B)\) rather than their classical counterparts \(A ↗
B\). Powersets \(𝒫(A)\) are required to be monotonic themselves, meaning they
are \emph{downward closed}, i.e. \(X ∈ 𝒫(A)\) is monotonic if and only if
\(∀(x,y). x ∈ X → y ⊑ x → y ∈ X\).

The reflexive morphism in the powerset Kleisli category is \(return\), rather
than \(id\), where \(return\) is defined as the downward closure of the
singleton set:
\begin{align*}
& return ∈ ∀(A). A ↗ 𝒫(A)               \\
& return(x) = \{ y\ |\ y ⊑ x \}
\end{align*}

The monadic bind operator, which we call \emph{extension} and notate
\(\_∗\) in the tradition of Moggi~\cite{davdar:Moggi:1989:Monads}, is defined
using a dependent sum, or existential type:
\begin{align*}
  & \_∗ ∈ ∀(A,B). (A ↗ 𝒫(B)) ↗ (𝒫(A) ↗ 𝒫(B))\\
  & f∗(X) = \{ y\ |\ ∃ x ∈ X : y ∈ f(x) \}
\end{align*}

To establish that \(𝒫\) forms a monad with \(return\) and
\(\_∗\) we prove left-unit, right-unit and associativity laws.

\begin{lemma}[𝒫-monad] 
\label{lem:power-monad}
\(𝒫\) forms a monad with \(return\) and \(\_*\), meaning the following
properties hold:
\begin{align*}
   left\text-unit  &: ∀(X).      return∗(X)       = X                       \\
   right\text-unit &: ∀(f,x).    f*(return(x))    = f(x)                    \\
   associativity   &: ∀(f,g,X).  g*(f*(X))        = (λ(x). g*(f(x)))*(X)
\end{align*}
\end{lemma}

Composition in the powerset Kleisli category is notated \(\_⟐\_\) and
defined with \(\_*\):
\begin{align*}
& \_⟐\_ ∈ ∀(A,B,C). (B ↗ 𝒫(C)) → (A ↗ 𝒫(B)) → A ↗ 𝒫(C)\\
& (g ⟐ f)(x) = g∗(f(x))
\end{align*}

A Kleisli Galois connection \(A \galois{αᵐ}{γᵐ} B\), which we always notate
with superscripts \(αᵐ\) and \(γᵐ\), is analogous to that of classical Galois
connection but with monadic morphisms, unit and composition:
\begin{align*}
& αᵐ ∈ A ↗ 𝒫(B)\\
& γᵐ ∈ B ↗ 𝒫(A)\\
& extensiveᵐ : ∀(x). return(x) ⊑ γᵐ∗(αᵐ(x))\\
& reductiveᵐ : ∀(x⋕). αᵐ∗(γᵐ(x⋕)) ⊑ return(x⋕)
\end{align*}

The presence of \(return\) as the identity is significant: \(return\) marks the
transition from pure values to those which have a ``specification effect''.
\(extensiveᵐ\) states that \(γᵐ ⟐ αᵐ\) is a pure computation \emph{at best},
and \(reductiveᵐ\) states that \(αᵐ ⟐ γ\) is a pure computation \emph{at
worst}. The consequence of this will be important during calculation: appealing
to \(extensiveᵐ\) and \(reductiveᵐ\) will introduce and eliminate the
specification effect, respectively.

\subsection{Lifting Kleisli Galois Connections}

The end goal of our calculation is stated as a partial order relationship
using a classical Galois connection: \(α^{e→v}(eval) ⊑
eval⋕\). If we wish to work with Kleisli Galois connections, we must
build bridges between Kleisli results and classical ones. This bridge is stated
as an isomorphism between Kleisli Galois connections and a subset of classical
Galois connections that hold computational content, as shown in
section~\ref{sec:introduction} figure~\ref{fig:gc-venn}. In addition to the
Galois connections themselves, we map proofs of relatedness between Kleisli and
classical Galois connections, so long as the classical result is of the form
\(α^{A→B}(f*) ⊑ f⋕*\) where \(f\) and \(f⋕\) are monadic functions.

In order to leverage Kleisli Galois connections for our calculation we must
recognize \(eval\) as the extension of a monotonic monadic function
\(evalᵐ\). Recall the definition of \(eval\):
\begin{align*}
     eval[e] &∈ 𝒫(env) ↗ 𝒫(val)  \\
  eval[e](R) &≔ \{ v \ |\ ∃ ρ ∈ R : ρ ⊢ e ↦ v \}
\end{align*}
This is the extension of the monadic powerset function:
\(evalᵐ\):
\begin{align*}
     evalᵐ[e] &∈ env ↗ 𝒫(val) \\
  evalᵐ[e](ρ) &≔ \{ v \ |\ ρ ⊢ e ↦ v \}
\end{align*}
where, by definition of \(\_*\):
\begin{align*}
  evalᵐ[e]*(R) = \{ v \ |\ ∃ ρ ∈ R : ρ ⊢ e ↦ v \} = eval[e](R)
\end{align*}
This observation enables us to construct a Kleisli Galois connection:
\[env → 𝒫(val) \galois{α^{e→ᵐv}}{γ^{e→ᵐv}} env⋕ → 𝒫(val⋕)\] 
and calculation
\[α^{e→ᵐv}(eval[e]) ⊑ eval⋕[e]\text,\]
and lift the results to classical ones automatically via the \emph{soundness} of
the mapping from Kleisli to classical. Furthermore, we know that any classical
Galois connection and classical calculation of \(eval⋕\) can be encoded as
Kleisli via the \emph{completeness} of the Kleisli to classical mapping. We
give precise definitions for \emph{soundness} and \emph{completeness} in
section~\ref{sec:foundations}.

\subsection{Constructive Galois Connections}

When performing calculation to discover \({evalᵐ}⋕[e]\) from the induced
specification \(α^{e→ᵐv}(evalᵐ[e])\), we will require that the result be an
algorithm, which we can now state precisely as having no monadic effect.
The goal will then be to calculate the pure function \({evalᵐ}⋕[e] ∈ env⋕ ↗
val⋕\) such that 
\[ α^{e→ᵐv}(evalᵐ[e])(ρ⋕) ⊑ return({evalᵐ}⋕[e](ρ⋕)) \]
However, at present, such a calculation will be problematic. Take for instance,
the definition we would like to end up with for numeric literal expressions:
\[ {evalᵐ}⋕[n](ρ⋕) ≔ αᵐᵛ(n) \]
This defines the abstract interpretation of a numeric literal as the immediate
lifting of that literal to an abstract value. However this definition is not
valid, since \(αᵐᵛ ∈ val ↗ 𝒫(val⋕)\) introduces a specification effect. The
problem becomes magnified when we wish to parameterize over \(αᵐᵛ\), as Cousot
does in his original derivation. 

One idea is to restrict all \(αᵐ\) mappings to be pure, and only parameterize
over abstractions for \(val\) which have pure mappings. We take morally this
approach, although later we show that it is not a restriction at all, and
arises naturally through an isomorphism between Kleisli Galois connections and
those which have pure abstraction functions, which we call \emph{constructive
Galois connections}. This isomorphism is visualized on the right-hand-side of
figure~\ref{fig:gc-venn}, and proofs are given in
section~\ref{sec:foundations}.

A constructive Galois connection is a variant of Kleisli Galois connection
where the abstraction function \(αᵐ\) is required to have no specification
effect, which we call \(η\) following the convention of
\cite[p.~237]{dvanhorn:Neilson:1999} where it is called an ``extraction
function'':
\begin{align*}
&  η : A ↗ B\\
&  γᶜ : B ↗ 𝒫(A)\\
&  extensiveᶜ : return(x) ⊑ γ*return(η(x))                   \\
&  reductiveᶜ : (λ(x). return(η(x)))*γ(x⋕) ⊑ return(x⋕)
\end{align*}
We can now define the abstract interpretation for numeric literals as:
\[ {evalᵐ}⋕[n](ρ⋕) ≔ ηᵛ(n) \]
which is a pure computation that can be extracted and executed.

\subsection{Calculating the Interpreter, Constructively}
\label{sec:constructive-calculation}

We now recast Cousot's calculational derivation of a generic abstract
interpreter in the setting of Kleisli Galois connections. In the next section
we show how the constructive version is translatable to Agda. As before, we
only show numeric literals, variable reference and unary operators; see our
full Agda development for constructive calculations of the remaining cases.

Recall the constructive calculation goal, which is to discover a
\emph{pure} function \(evalᵐ⋕\) such that
\begin{align*}
  & α^{e→ᵐv}(evalᵐ)(ρ⋕) ⊑ return(evalᵐ⋕(ρ⋕))
\end{align*}
This goal makes it clear that we are starting with a specification
\(evalᵐ : env ↗ 𝒫(val)\), and working towards a pure computation
\(evalᵐ⋕ : env⋕ ↗ val⋕\). The process of calculation
will eliminate the ``specification effect'' from the induced specification
\(α^{e→ᵐv}(evalᵐ)\) using monad laws and the reductive and expansive properties
of Kleisli Galois connections.

The setting assumes Kleisli Galois connections for the abstractions of 
values 
\(val \galois{αᵐᵛ}{γᵐᵛ} val⋕\),
environments
\(env \galois{αᵐᵉ}{γᵐᵉ} env⋕\)
and their induced classical Galois connection for the monadic function space
\(val ↗ 𝒫(env) \galois{α^{e→ᵐv}}{γ^{e→ᵐv}} val⋕ ↗ 𝒫(env⋕)\).
When needed we replace \(αᵐ(x)\) with an equivalent pure extraction function
\(return(η(x))\) using the isomorphism between Kleisli and constructive Galois
connections.

We begin calculating from the specification \(α^{e→ᵐv}(evalᵐ)\) by unfolding
definitions:
\begin{align*}
  & α^{e→ᵐv}(evalᵐ[e])(ρ⋕)\\
  & = (αᵐᵛ ⟐ evalᵐ[e] ⟐ γᵐʳ)(ρ⋕) \⟅{ definition of \(α^{e→ᵐv}\) }\\
  & = αᵐᵛ*(evalᵐ[e]*(γᵐʳ(ρ⋕)))        \⟅{ monad associtivity }
\end{align*}
and proceed by induction on \(e\). The calculations for numeric literals,
variables and unary operators are show in figure~\ref{fig:constr}.
The parameters for the unary operator case in the constructive setting are an
abstract unary denotation \(⟦\_⟧ᵘ⋕ ∈ val⋕ ↗ val⋕\) and a proof that it
abstracts concrete unary denotation: \[α^{v→ᵐv}(λ(v). return(⟦u⟧ᵘ(v)))(v⋕) ⊑
return(⟦u⟧ᵘ⋕(v⋕)) \]

The biggest difference between our constructive derivation and Cousot's
classical derivation is the presence of monadic unit \(return\) and extension
operator \(\_*\). In the process of calculation, monadic unit and associativity
laws are used in combination with extensive and reductive properties to
calculate toward a pure value, at which point the result is both a pure
computation and an abstraction of \(eval[e]\) simultaneously by construction.


\section{Galois Connection Metatheory in Agda}
\label{sec:galois-agda}

\dvh{This needs an intro}

We now encode our constructive calculation of the Generic Abstract
Interpreter in Agda, both to verify the results mechanically and to
extract an executable version of the resulting abstract
interpreter.

We mechanize the calculation of the interpreter first by developing a theory of
posets, its monotonic function space, and a non-constructive powerset type,
which we prove is a monad. Then we develop theories of classical, Kleisli and
constructive Galois connections, as well as their soundness and completeness
relationships. Finally, we embed the constructive calculation in Agda, arriving
at at an executable algorithm, and lift its correctness property to the
classical correctness criteria initially specified by Cousot.


\subsection{Posets in Agda}

We begin by defining \A{\AgdaDatatype{PreOrd}}, a relation which is reflexive
and transitive. \A{\AgdaDatatype{PreOrd}} is a \emph{type class}, meaning
top-level instance definitions will be automatically selected by Agda
during type inference.

\begin{code}

record PreOrd (A : Set) : Set where
  field
    _⊴_ : A → A → Set
    xRx⸢⊴⸣ : ∀ {x} → x ⊴ x
    _⌾⸢⊴⸣_ : ∀ {x y z} → y ⊴ z → x ⊴ y → x ⊴ z

\end{code}
\AgdaHide{
\begin{code}
  infix 8 _⊴_
  infix 9 _⌾⸢⊴⸣_
\end{code}}
\AgdaHide{
\begin{code}
open PreOrd {{...}} public
\end{code}}
%
We then define posets in Agda:

\begin{code}

data POSet : Set where
  ⇧ : (A : Set) → {{PO : PreOrd A}} → POSet

\end{code}
The double curly brackets around \A{\AgdaDatatype{PO}} indicate that the argument
should be inferred through \emph{type class resolution}, which we rely on
heavily in our development. 

To construct a \A{\AgdaDatatype{POSet}} (rather than the builtin
\AgdaPrimitiveType{Set}), we create another datatype \A{\AgdaDatatype{⟪\_⟫}}, which
selects the domain of a \A{\AgdaDatatype{POSet}}.

\begin{code}

dom : POSet → Set
dom (⇧ A {{PO}}) = A
    
data ⟪_⟫ (A : POSet) : Set where
  ↑⟨_⟩ : dom A → ⟪ A ⟫

\end{code}
The reason for introducing a new datatype \A{\AgdaDatatype{⟪\_⟫}} is purely
technical; it allows us to block reduction of elements of
\A{\AgdaInductiveConstructor{⇧}} \A{\AgdaBound{A}} until we witness its lifting
from a value
\A{\AgdaBound{x}} \A{\AgdaSymbol{:}} \A{\AgdaFunction{dom}} \A{\AgdaBound{A}} into \A{\AgdaInductiveConstructor{↑⟨}} \A{\AgdaBound{x}}
\A{\AgdaInductiveConstructor{⟩}} \A{\AgdaSymbol{:}} \A{\AgdaDatatype{POSet}} \A{\AgdaBound{A}}.

Next, we induce a partial order on \A{\AgdaDatatype{POSet}} from the antisymmetric
closure of the supplied pre order lifted to elements of \A{\AgdaDatatype{⟪\_⟫}}:


\begin{code}

[_]_⊴⸢dom⸣_ : ∀ (A : POSet) → dom A → dom A → Set
[ ⇧ A {{PO}} ] x ⊴⸢dom⸣ y = x ⊴ y
    
data _⊑_ {A : POSet} : ⟪ A ⟫ → ⟪ A ⟫ → Set where
  ↑⟨_⟩ : ∀ {x y : dom A} → [ A ] x ⊴⸢dom⸣ y → ↑⟨ x ⟩ ⊑ ↑⟨ y ⟩

\end{code}
This definition of \A{\AgdaDatatype{\_⊑\_}} is designed to also block reduction
until the liftings of \A{\AgdaBound{x}} and \A{\AgdaBound{y}} are likewise witnessed
through pattern matching.

We induce equivalence as the antisymmetric closure of \A{\AgdaDatatype{\_⊑\_}}.

\begin{code}

data _≈_ {A : POSet} (x y : ⟪ A ⟫) : Set where
  _,_ :  x ⊑ y → y ⊑ x → x ≈ y

\end{code}
We prove reflexivity, transitivity and antisymmetry for \A{\AgdaDatatype{\_⊑\_}}, as
well as reflexivity, transitivity and symmetry for \A{\AgdaDatatype{\_≈\_}}:

\begin{code}

xRx⸢⊑⸣ : ∀ {A : POSet} {x : ⟪ A ⟫} → x ⊑ x
_⌾⸢⊑⸣_ : ∀ {A : POSet} {x y z : ⟪ A ⟫} → y ⊑ z → x ⊑ y → x ⊑ z
⋈⸢≈⸣ : ∀ {A : POSet} {x y : ⟪ A ⟫} → x ⊑ y → y ⊑ x → x ≈ y
xRx⸢≈⸣ : ∀ {A : POSet} {x y : ⟪ A ⟫} → x ≈ y → x ⊑ y
_⌾⸢≈⸣_ : ∀ {A : POSet} {x y z : ⟪ A ⟫} → y ≈ z → x ≈ y → x ≈ z
◇⸢≈⸣ : ∀ {A : POSet} {x y : ⟪ A ⟫} → x ≈ y → y ≈ x

\end{code}
\AgdaHide{
\begin{code}
xRx⸢⊑⸣ {A = ⇧ A {{PO}}} {x = ↑⟨ x ⟩} = ↑⟨ xRx⸢⊴⸣ ⟩
_⌾⸢⊑⸣_ {A = ⇧ A {{PO}}} ↑⟨ y⊴z ⟩ ↑⟨ x⊴y ⟩ = ↑⟨ y⊴z ⌾⸢⊴⸣ x⊴y ⟩
⋈⸢≈⸣ x⊑y y⊑x = x⊑y , y⊑x
xRx⸢≈⸣ (x⊑y , _) = x⊑y
(y⊑z , z⊑y) ⌾⸢≈⸣ (x⊑y , y⊑x) = (y⊑z ⌾⸢⊑⸣ x⊑y , y⊑x ⌾⸢⊑⸣ z⊑y)
◇⸢≈⸣ (x⊑y , y⊑x) = (y⊑x , x⊑y)
\end{code}}

Now we can define the two most important posets: the function space and
powerset.

\subsection{Monotonic Functions in Agda}

To construct a poset for monotonic functions we carry proofs of
monotonicity around with each function. 

\begin{code}

data mon (A B : POSet) : Set where
  mk[mon] : (f : ⟪ A ⟫ → ⟪ B ⟫) → 
    {f-proper : ∀ {x y} → x ⊑ y → f x ⊑ f y} → mon A B

\end{code}

The \A{\AgdaRecord{PreOrd}} for \A{\AgdaDatatype{mon}} is the pointwise
ordering of \A{\AgdaDatatype{⊑}}:

\begin{code}

data _⊴⸢mon⸣_ {A B : POSet} : mon A B → mon A B → Set where
  ↑⟨_⟩ : ∀ {f : ⟪ A ⟫ → ⟪ B ⟫} {f-proper : ∀ {x y} → x ⊑ y → f x ⊑ f y}
           {g : ⟪ A ⟫ → ⟪ B ⟫} {g-proper : ∀ {x y} → x ⊑ y → g x ⊑ g y}
         → (∀ {x} → f x ⊑ g x)
         → mk[mon] f {f-proper} ⊴⸢mon⸣ mk[mon] g {g-proper}

\end{code}
\AgdaHide{
\begin{code}
xRx⸢⊴⸢mon⸣⸣ : ∀ {A B : POSet} {F : mon A B} → F ⊴⸢mon⸣ F
xRx⸢⊴⸢mon⸣⸣ {F = mk[mon] f {f-proper}} = ↑⟨ f-proper xRx⸢⊑⸣ ⟩

_⌾⸢⊴⸢mon⸣⸣_ : ∀ {A B : POSet} {F G H : mon A B} → G ⊴⸢mon⸣ H → F ⊴⸢mon⸣ G → F ⊴⸢mon⸣ H
↑⟨ g⊴h ⟩ ⌾⸢⊴⸢mon⸣⸣ ↑⟨ f⊴g ⟩ = ↑⟨ g⊴h ⌾⸢⊑⸣ f⊴g ⟩

instance
  PreOrd[mon] : ∀ {A B : POSet} → PreOrd (mon A B)
  PreOrd[mon] = record { _⊴_ = _⊴⸢mon⸣_ ; xRx⸢⊴⸣ = xRx⸢⊴⸢mon⸣⸣ ; _⌾⸢⊴⸣_ = _⌾⸢⊴⸢mon⸣⸣_ }
\end{code}}
%
We lift \A{\AgdaDatatype{mon}} to a \A{\AgdaDatatype{POSet}} with \A{\AgdaFunction{\_⇒\_}}:

\begin{code}
  
_⇒_ : POSet → POSet → POSet
A ⇒ B = ⇧ (mon A B)

\end{code}
%
Application in \A{\AgdaFunction{\_⇒\_}} is \A{\AgdaFunction{\_⋅\_}}:

\begin{code}

_⋅_ : ∀ {A B : POSet} → ⟪ A ⇒ B ⟫ → ⟪ A ⟫ → ⟪ B ⟫
↑⟨ mk[mon] f {f-proper} ⟩ ⋅ x = f x

\end{code}
We define a helper function for creating values in \A{\AgdaFunction{\_⇒\_}} which
require no monotonicity proof (which we use for demonstration purposes only):

\begin{code}

mk[⇒] : ∀ {A B : POSet} → (⟪ A ⟫ → ⟪ B ⟫) → ⟪ A ⇒ B ⟫
mk[⇒] f = ↑⟨ mk[mon] f {f-proper} ⟩ where
  postulate f-proper : ∀ {x y} → x ⊑ y → f x ⊑ f y

\end{code}
For example, composition is defined as \A{\AgdaFunction{\_⊙\_}}:

\begin{code}

_⊙_ : ∀ {A B C : POSet} → ⟪ B ⇒ C ⟫ → ⟪ A ⇒ B ⟫ → ⟪ A ⇒ C ⟫
g ⊙ f = mk[⇒] (λ x → g ⋅ (f ⋅ x))

\end{code}
\AgdaHide{
\begin{code}

mk[↑⇒] :  ∀ {A : Set} {{A-PO : PreOrd A}} {B : POSet} 
  → (A → ⟪ B ⟫) → ⟪ ⇧ A ⇒ B ⟫

mk[↑⇒↑] : ∀ {A : Set} {{A-PO : PreOrd A}} {B : Set} {{B-PO : PreOrd B}} 
  → (A → B) → ⟪ ⇧ A ⇒ ⇧ B ⟫

mk[↑⇒] {A = A} {B = B} f = mk[⇒] ↑f
  where
    ↑f : ⟪ ⇧ A ⟫ → ⟪ B ⟫
    ↑f ↑⟨ x ⟩ = f x

mk[↑⇒↑] {A = A} {B = B} f = mk[⇒] ↑f↑
  where
    ↑f↑ : ⟪ ⇧ A ⟫ → ⟪ ⇧ B ⟫
    ↑f↑ ↑⟨ x ⟩ = ↑⟨ f x ⟩

[⋅] : ∀ {A B : POSet} → ⟪ (A ⇒ B) ⇒ A ⇒ B ⟫
[⋅] = mk[⇒] (λ f → mk[⇒] (λ x → f ⋅ x))

id : {A : POSet} → ⟪ A ⇒ A ⟫
id = mk[⇒] (λ x → x)

[⊙] : ∀ {A B C : POSet} → ⟪ (B ⇒ C) ⇒ (A ⇒ B) ⇒ (A ⇒ C) ⟫
[⊙] = mk[⇒] (λ g → mk[⇒] (λ f → g ⊙ f))

\end{code}}

\secendswithagda

\subsection{Monotonic Powerset in Agda}

We define powersets as monotonic characteristic functions into Agda's
\A{\AgdaDatatype{Set}} type.

\begin{code}

data pow (A : POSet) : Set where
  mk[pow] : (φ : ⟪ A ⟫ → Set) → 
    {φ-proper : ∀ {x y} → y ⊑ x → φ x → φ y} → pow A

\end{code}
Whereas \A{\AgdaFunction{mk[⇒]}} \A{\AgdaBound{f}}
\A{\AgdaBound{\{f\text-proper\}}} constructs a monotonic function from
\A{\AgdaBound{f}}, \A{\AgdaFunction{mk[𝒫]}} \A{\AgdaBound{φ}}
\A{\AgdaBound{\{φ\text-proper\}}} constructs a set from a monotonic
characteristic function \A{\AgdaBound{φ}}.
Antitonicity of the argument to \A{\AgdaBound{φ}} in the statement of
\A{\AgdaBound{φ\text{-}proper}} is required to ensure sets are downward
closed.

The preorder for \A{\AgdaDatatype{pow}} is implication:

\begin{code}

data _⊴⸢pow⸣_ {A : POSet} : pow A → pow A → Set where
  ↑⟨_⟩ : ∀ {φ₁ : ⟪ A ⟫ → Set} {φ₁-proper : ∀ {x y} → y ⊑ x → φ₁ x → φ₁ y} 
           {φ₂ : ⟪ A ⟫ → Set} {φ₂-proper : ∀ {x y} → y ⊑ x → φ₂ x → φ₂ y}
         → (∀ {x} → φ₁ x → φ₂ x)
         → mk[pow] φ₁ {φ₁-proper} ⊴⸢pow⸣ mk[pow] φ₂ {φ₂-proper}

\end{code}
\AgdaHide{
\begin{code}
instance
  PreOrd[pow] : ∀ {A : POSet} → PreOrd (pow A)
  PreOrd[pow] = record { _⊴_ = _⊴⸢pow⸣_ ; xRx⸢⊴⸣ = … ; _⌾⸢⊴⸣_ = … }

\end{code}}
\noindent
We lift \A{\AgdaDatatype{pow}} into the 
\A{\AgdaDatatype{POSet}} type as \A{\AgdaDatatype{𝒫}}.

\begin{code}

𝒫 : POSet → POSet
𝒫 A = ⇧ (pow A)

\end{code}
\noindent
The set-containment judgement is \A{\AgdaFunction{\_∈\_}}.


\begin{code}
  
_∈_ : ∀ {A : POSet} → ⟪ A ⟫ → ⟪ 𝒫 A ⟫ → Set
x ∈ ↑⟨ mk[pow] φ {φ-proper} ⟩ = φ x

\end{code}
And like functions we provide a cheat for creating monotonic sets without the
burden of monotonicity proof.

\begin{code}

mk[𝒫] : ∀ {A : POSet} → (⟪ A ⟫ → Set) → ⟪ 𝒫 A ⟫
mk[𝒫] φ = ↑⟨ mk[pow] φ {φ-proper} ⟩ where
  postulate φ-proper : ∀ {x y} → y ⊑ x → φ x → φ y

\end{code}
\AgdaHide{
\begin{code}
mk[𝒫↑] : ∀ {A : Set} {{PO : PreOrd A}} → (A → Set) → ⟪ 𝒫 (⇧ A) ⟫
mk[𝒫↑] {A = A} φ = mk[𝒫] ↑φ
  where
    ↑φ : ⟪ ⇧ A ⟫ → Set
    ↑φ ↑⟨ x ⟩ = φ x

\end{code}}

\secendswithagda

\subsection{Powerset Monad in Agda}

The powerset monad has unit \A{\AgdaFunction{return}}, where
\A{\AgdaFunction{return}} \A{\AgdaBound{x}} is the set of all elements
smaller than \A{\AgdaBound{x}}, as defined by a characteristic
function:

\begin{code}

return : ∀ {A : POSet} → ⟪ A ⇒ 𝒫 A ⟫
return = mk[⇒] (λ x → mk[𝒫] (λ y → y ⊑ x))

\end{code}
\noindent
We lift the \A{\AgdaFunction{return}} operation to functions, which we call
\A{\AgdaFunction{pure}}.

\begin{code}

pure : ∀ {A B : POSet} → ⟪ (A ⇒ B) ⇒ A ⇒ 𝒫 B ⟫
pure = mk[⇒] (λ f → mk[⇒] (λ x → return ⋅ (f ⋅ x)))

\end{code}
\noindent
Monadic extension is \A{\AgdaFunction{\_*}}.

\begin{code}

_* : ∀ {A B : POSet} → ⟪ A ⇒ 𝒫 B ⟫ → ⟪ 𝒫 A ⇒ 𝒫 B ⟫
f * = mk[⇒] (λ X → mk[𝒫] (λ y → ∃ x 𝑠𝑡 (x ∈ X) × y ∈ f ⋅ x))

\end{code}
\AgdaHide{
\begin{code}
[*] : ∀ {A B : POSet} → ⟪ (A ⇒ 𝒫 B) ⇒ (𝒫 A ⇒ 𝒫 B) ⟫
[*] = mk[⇒] (λ f → f *)
\end{code}}

\noindent
We use \A{\AgdaFunction{\_*}} to define Kleisli composition,
\A{\AgdaFunction{\_⟐\_}}:


\begin{code}

_⟐_ : ∀ {A B C : POSet} → ⟪ B ⇒ 𝒫 C ⟫ → ⟪ A ⇒ 𝒫 B ⟫ → ⟪ A ⇒ 𝒫 C ⟫
g ⟐ f = mk[⇒] (λ x → g * ⋅ (f ⋅ x))

\end{code}
\AgdaHide{
\begin{code}
[⟐] : ∀ {A B C : POSet} → ⟪ (B ⇒ 𝒫 C) ⇒ (A ⇒ 𝒫 B) ⇒ (A ⇒ 𝒫 C) ⟫
[⟐] = mk[⇒] (λ g → mk[⇒] (λ f → g ⟐ f))
\end{code}}

\noindent
Finally, we prove (and omit) monads laws analogous to those in
lemma~\ref{lem:power-monad}.

\AgdaHide{
\begin{code}

postulate
  left-unit[*] : ∀ {A : POSet} {X : ⟪ 𝒫 A ⟫} → return * ⋅ X ≈ X
  right-unit[*][_] : ∀ {A B : POSet} (f : ⟪ A ⇒ 𝒫 B ⟫) {x : ⟪ A ⟫} 
                   → f * ⋅ (return ⋅ x) ≈ f ⋅ x
  associative[*][_,_,_] : ∀ {A B C} 
    (g : ⟪ B ⇒ 𝒫 C ⟫) (f : ⟪ A ⇒ 𝒫 B ⟫) (X : ⟪ 𝒫 A ⟫) 
    → (g ⟐ f) * ⋅ X ≈ g * ⋅ (f * ⋅ X)
  left-unit[⟐] : ∀ {A B : POSet} {f : ⟪ A  ⇒ 𝒫 B ⟫} → return ⟐ f ≈ f
  right-unit[⟐] : ∀ {A B : POSet} {f : ⟪ A  ⇒ 𝒫 B ⟫} → f ⟐ return ≈ f
  associative[⟐][_,_,_] : ∀ {A B C D : POSet} 
    (h : ⟪ C ⇒ 𝒫 D ⟫) (g : ⟪ B ⇒ 𝒫 C ⟫) (f : ⟪ A ⇒ 𝒫 B ⟫) 
    → (h ⟐ g) ⟐ f ≈ h ⟐ g ⟐ f

\end{code}}

\begin{figure}
\begin{code}

record _⇄_ (A B : POSet) : Set where  -- Classical
  field
    α[_] : ⟪ A ⇒ B ⟫
    γ[_] : ⟪ B ⇒ A ⟫
    extensive[_] :  ∀ {x : ⟪ A ⟫} 
                    → x ⊑ γ[_] ⋅ (α[_] ⋅ x)
    reductive[_] :  ∀ {x⋕ : ⟪ B ⟫} 
                    → α[_] ⋅ (γ[_] ⋅ x⋕) ⊑ x⋕

record _⇄ᵐ_ (A B : POSet) : Set where  -- Kleisli
  field
    αᵐ[_] : ⟪ A ⇒ 𝒫 B ⟫
    γᵐ[_] : ⟪ B ⇒ 𝒫 A ⟫
    extensiveᵐ[_] :  ∀ {x : ⟪ A ⟫} 
                     → return ⋅ x ⊑ γᵐ[_] * ⋅ (αᵐ[_] ⋅ x)
    reductiveᵐ[_] :  ∀ {x⋕ : ⟪ B ⟫} 
                     → αᵐ[_] * ⋅ (γᵐ[_] ⋅ x⋕) ⊑ return ⋅ x⋕

\end{code}
\AgdaHide{
\begin{code}
  postulate
    extensiveᵐ[⟐][_] : return ⊑ γᵐ[_] ⟐ αᵐ[_]
    reductiveᵐ[⟐][_] : αᵐ[_] ⟐ γᵐ[_] ⊑ return
\end{code}}
\begin{code}

record _⇄ᶜ_ (A B : POSet) : Set where  -- Constructive
  field
    η[_] : ⟪ A ⇒ B ⟫
    γᶜ[_] : ⟪ B ⇒ 𝒫 A ⟫
    extensiveᶜ[_] :  ∀ {x : ⟪ A ⟫} 
                     → return ⋅ x ⊑ γᶜ[_] * ⋅ (pure ⋅ η[_] ⋅ x)
    reductiveᶜ[_] :  ∀ {x⋕ : ⟪ B ⟫} 
                     → (pure ⋅ η[_]) * ⋅ (γᶜ[_] ⋅ x⋕) ⊑ return ⋅ x⋕
\end{code}
\AgdaHide{
\begin{code}
  postulate
    extensiveᶜ[*][_] :  ∀ {X : ⟪ 𝒫 A ⟫} 
                        → X ⊑ γᶜ[_] * ⋅ ((pure ⋅ η[_]) * ⋅ X)
    reductiveᶜ[*][_] :  ∀ {X⋕ : ⟪ 𝒫 B ⟫} 
                        → (pure ⋅ η[_]) * ⋅ (γᶜ[_] * ⋅ X⋕) ⊑ X⋕
    soundᶜ[_] :         ∀ {x : ⟪ A ⟫} 
                        → x ∈ γᶜ[_] ⋅ (η[_] ⋅ x)
    completeᶜ[_] :      ∀ {x⋕ : ⟪ B ⟫} {x : ⟪ A ⟫} 
                        → x ∈ γᶜ[_] ⋅ x⋕ → η[_] ⋅ x ⊑ x⋕
\end{code}}
\AgdaHide{
\begin{code}
open _⇄_
open _⇄ᵐ_
open _⇄ᶜ_
\end{code}}
\caption{Classical, Kleisli, and constructive Galois connections.}
\label{fig:signatures}
\end{figure}

\dvh{Fix up text now that code is lifted to figure.}

\AgdaHide{
\begin{code}
mk[⇄ᶜ↑] :
  ∀ {A : Set} {{A-PO : PreOrd A}}
    {B : Set} {{B-PO : PreOrd B}}
    (η : A → B)
    (γᶜ : B → A → Set)
    (soundᶜ : ∀ x → γᶜ (η x) x)
    (completeᶜ : ∀ {x⋕ x} → γᶜ x⋕ x → η x ⊴ x⋕)
  → ⇧ A ⇄ᶜ ⇧ B
mk[⇄ᶜ↑] {A = A} {B = B} η γᶜ soundᶜ completeᶜ = record
  { η[_] = mk[↑⇒↑] η
  ; γᶜ[_] = mk[↑⇒] (λ x⋕ → mk[𝒫↑] (λ x → γᶜ x⋕ x))
  ; extensiveᶜ[_] = …
  ; reductiveᶜ[_] = … }
\end{code}}



\section{Calculational Abstract Interpretation in Agda}
\label{sec:mechanized}

We show Agda types for classical, Kleisli and constructive Galois connections
in figure~\ref{fig:signatures}. Using these definitions we calculate an
abstract interpreter in Agda following the constructive approach described in
section~\ref{sec:new} in the following steps:

\begin{enumerate}
\item Define a constructive Galois connection between \(env\) and
  \(env⋕\).

\item Lift (1) and a parameterized Galois connection for \(val\) pointwise to
  the monotonic function space.
\item Induce the specification for an abstraction of a monadic
  semantic function \(evalᵐ[e]\) as \(α^{e→ᵐv}(evalᵐ[e])\).

\item Calculate over \(α^{e→ᵐv}(evalᵐ[ e ])\) until we arrive at a pure function
   \(pure(evalᵐ⋕[e])\).

\item Lift the relationship \(α^{e→ᵐv}(evalᵐ[e]) ⊑ pure(evalᵐ⋕[e])\)
  to the classical abstraction of function extensions \(α^{(e→ᵐv)*}(evalᵐ[e]*)
  ⊑ pure(evalᵐ⋕[e])*\) through a mechanized proof of soundness of Kleisli
  Galois connections w.r.t. classical.
\end{enumerate}

\subsection{Abstracting Environments in Agda}

We define a \emph{constructive} Galois connection between
\A{\AgdaDatatype{env}} and \A{\AgdaDatatype{env⋕}} rather than Kleisli
because it results in nicer definitions.  First we parameterize by an
abstraction for values, which we do with an Agda module:

\AgdaHide{
\begin{code}
discrete-PreOrd : ∀ {A} → PreOrd A
discrete-PreOrd = record { _⊴_ = _≡_ ; xRx⸢⊴⸣ = … ; _⌾⸢⊴⸣_ = … }
\end{code}}
\AgdaHide{
\begin{code}

instance
  PreOrd[val] : PreOrd val
  PreOrd[val] = discrete-PreOrd
    
  PreOrd[env] : ∀ {Γ} → PreOrd (env Γ)
  PreOrd[env] = discrete-PreOrd

\end{code}}
%

\begin{code}

module §-env⋕ (val⋕ : POSet) (⇄val⇄ : ⇧ val ⇄ᶜ val⋕) where

\end{code}
\AgdaHide{
\begin{code}
  infixr 8 _⌾⸢⊴ᵉ⸣_
\end{code}}
%
Abstract environments take the form of another list-like inductive datatype:

\begin{code}

  data env⋕ : size → Set where
    [] : env⋕ Zero
    _∷_ : ∀ {Γ} → ⟪ val⋕ ⟫ → env⋕ Γ → env⋕ (Suc Γ)

  _[_]⋕ : ∀ {Γ} → env⋕ Γ → var Γ → ⟪ val⋕ ⟫
  (v⋕ ∷ ρ) [ Zero ]⋕ = v⋕
  (v⋕ ∷ ρ) [ Suc x ]⋕ = ρ [ x ]⋕

\end{code}
\noindent
The ordering for \A{\AgdaDatatype{env⋕}} is the pointwise ordering:

\begin{code}

  data _⊴ᵉ_ : ∀ {Γ} → env⋕ Γ → env⋕ Γ → Set where
    [] : [] ⊴ᵉ []
    _∷_ : ∀ {Γ} {ρ₁ ρ₂ : env⋕ Γ} {v₁ v₂}
      → v₁ ⊑ v₂ → ρ₁ ⊴ᵉ ρ₂ → (v₁ ∷ ρ₁) ⊴ᵉ (v₂ ∷ ρ₂)

\end{code}
\noindent
The environment abstraction function \A{\AgdaFunction{ηᵉ}} is the pointwise
application of \A{\AgdaField{η[}} \A{\AgdaFunction{⇄val⇄}} \A{\AgdaField{]}}:

\AgdaHide{
\begin{code}
  xRx⸢⊴ᵉ⸣ : ∀ {Γ} {ρ⋕ : env⋕ Γ} → ρ⋕ ⊴ᵉ ρ⋕
  xRx⸢⊴ᵉ⸣ {ρ⋕ = []} = []
  xRx⸢⊴ᵉ⸣ {ρ⋕ = v⋕ ∷ ρ⋕} = xRx⸢⊑⸣ ∷ xRx⸢⊴ᵉ⸣ {ρ⋕ = ρ⋕}

  _⌾⸢⊴ᵉ⸣_ : ∀ {Γ} {ρ₁⋕ ρ₂⋕ ρ₃⋕ : env⋕ Γ} → ρ₂⋕ ⊴ᵉ ρ₃⋕ → ρ₁⋕ ⊴ᵉ ρ₂⋕ → ρ₁⋕ ⊴ᵉ ρ₃⋕
  [] ⌾⸢⊴ᵉ⸣ [] = []
  (v₂⋕⊑v₃⋕ ∷ ρ₂⋕⊴ρ₃⋕) ⌾⸢⊴ᵉ⸣ (v₁⋕⊑v₂⋕ ∷ ρ₁⋕⊴ρ₂⋕) = (v₂⋕⊑v₃⋕ ⌾⸢⊑⸣ v₁⋕⊑v₂⋕) ∷ (ρ₂⋕⊴ρ₃⋕ ⌾⸢⊴ᵉ⸣ ρ₁⋕⊴ρ₂⋕)

  instance
    PreOrd[env⋕] : ∀ {Γ} → PreOrd (env⋕ Γ)
    PreOrd[env⋕] = record { _⊴_ = _⊴ᵉ_ ; xRx⸢⊴⸣ = xRx⸢⊴ᵉ⸣ ; _⌾⸢⊴⸣_ = _⌾⸢⊴ᵉ⸣_ }
\end{code}}

\begin{code}

    ηᵉ : ∀ {Γ} → env Γ → env⋕ Γ
    ηᵉ [] = []
    ηᵉ (n ∷ ρ) = η[ ⇄val⇄ ] ⋅ ↑⟨ n ⟩ ∷ ηᵉ ρ

\end{code}
\noindent
The concretization function \A{\AgdaFunction{γᶜᵉ}} is the pointwise concretization
of \A{\AgdaField{γᶜ[}} \A{\AgdaFunction{⇄val⇄}} \A{\AgdaField{]}}:

\begin{code}

    data _∈γᵉ_ : ∀ {Γ} → env Γ → env⋕ Γ → Set where
      [] : [] ∈γᵉ []
      _∷_ : ∀ {Γ} {ρ : env Γ} {ρ⋕ : env⋕ Γ} {n n⋕} 
            → ↑⟨ n ⟩ ∈ γᶜ[ ⇄val⇄ ] ⋅ n⋕ → ρ ∈γᵉ ρ⋕ → (n ∷ ρ) ∈γᵉ (n⋕ ∷ ρ⋕)

\end{code}
The \A{\AgdaFunction{ηᵉ}} and \A{\AgdaFunction{\_∈γᵉ\_}} functions are
sound and complete by pointwise applications of soundness and
completness from \A{\AgdaFunction{⇄val⇄}}:
\begin{code}

    soundᶜᵉ : ∀ {Γ} (ρ : env Γ) → ρ ∈γᵉ ηᵉ ρ
    soundᶜᵉ [] = []
    soundᶜᵉ (x ∷ ρ) = soundᶜ[ ⇄val⇄ ] ∷ soundᶜᵉ ρ

    completeᶜᵉ : ∀ {Γ} {ρ : env Γ} {ρ⋕} → ρ ∈γᵉ ρ⋕ → ηᵉ ρ ⊴ ρ⋕
    completeᶜᵉ [] = []
    completeᶜᵉ (n∈γ[n⋕] ∷ ρ∈γ[ρ⋕]) = 
      completeᶜ[ ⇄val⇄ ] n∈γ[n⋕] ∷ completeᶜᵉ ρ∈γ[ρ⋕]

\end{code}
From these definitions, we construct
\A{\AgdaFunction{⇄env⇄}}
\A{\AgdaSymbol{:}}
\A{\AgdaSymbol{∀}}
\A{\AgdaBound \{Γ\}}
\A{\AgdaSymbol{→}}
\A{\AgdaInductiveConstructor{⇧}}
\A{\AgdaFunction{(}}%
\A{\AgdaDatatype{env}}
\A{\AgdaBound{Γ}}%
\A{\AgdaFunction{)}}
\A{\AgdaFunction{η⇄γ}}
\A{\AgdaInductiveConstructor{⇧}}
\A{\AgdaFunction{(}}%
\A{\AgdaDatatype{env⋕}}
\A{\AgdaBound{Γ}}%
\A{\AgdaFunction{)}} using a helper
function \A{\AgdaFunction{mk[⇄ᶜ↑]}} for lifting primitive definitions
(non-\A{\AgdaDatatype{POSet}}) to Galois connections.

\begin{code}

    ⇄env⇄ : ∀ {Γ} → ⇧ (env Γ) ⇄ᶜ ⇧ (env⋕ Γ)
    ⇄env⇄ = mk[⇄ᶜ↑] ηᵉ (λ ρ⋕ ρ → ρ ∈γᵉ ρ⋕) soundᶜᵉ completeᶜᵉ

\end{code}

\secendswithagda

\subsection{Inducing a Best Specification in Agda}

The monadic semantics is encoded with the evaluation relation:

\begin{code}

evalᵐ[_] : ∀ {Γ} → exp Γ → ⟪ ⇧ (env Γ) ⇒ 𝒫 (⇧ val) ⟫
evalᵐ[ e ] = mk[↑⇒] (λ ρ → mk[𝒫↑] (λ v → ρ ⊢ e ↦ v))

\end{code}
To induce a best abstraction we first encode the pointwise lifting of two Kleisli Galois connections
\A{\AgdaBound{⇄A⇄}} and \A{\AgdaBound{⇄B⇄}} to classical pointwise Galois
connections over the monadic function space as (\A{\AgdaBound{⇄A⇄}}
\A{\AgdaFunction{⇒⸢⇄ᵐ⸣}} \A{\AgdaBound{⇄B⇄}}). 

\begin{code}

_⇒⸢⇄ᵐ⸣_ :  ∀ {A₁ A₂ B₁ B₂ : POSet} 
           → A₁ ⇄ᵐ A₂ → B₁ ⇄ᵐ B₂ → (A₁ ⇒ 𝒫 B₁) ⇄ (A₂ ⇒ 𝒫 B₂)
_⇒⸢⇄ᵐ⸣_ {A₁} {A₂} {B₁} {B₂} ⇄A⇄ ⇄B⇄ = record
  { α[_] = mk[⇒] (λ f → αᵐ[ ⇄B⇄ ] ⟐ f ⟐ γᵐ[ ⇄A⇄ ])
  ; γ[_] = mk[⇒] (λ f⋕ → γᵐ[ ⇄B⇄ ] ⟐ f⋕ ⟐ αᵐ[ ⇄A⇄ ])
  ; extensive[_] = … ; reductive[_] = … }

\end{code}
\AgdaHide{
\begin{code}
_⇒⸢⇄ᶜ⸣_ : ∀ {A₁ A₂ B₁ B₂ : POSet} → A₁ ⇄ᶜ A₂ → B₁ ⇄ᶜ B₂ → (A₁ ⇒ 𝒫 B₁) ⇄ (A₂ ⇒ 𝒫 B₂)
_⇒⸢⇄ᶜ⸣_ {A₁} {A₂} {B₁} {B₂} ⇄A⇄ ⇄B⇄ = record
  { α[_] = mk[⇒] (λ f → pure ⋅ η[ ⇄B⇄ ] ⟐ f ⟐ γᶜ[ ⇄A⇄ ])
  ; γ[_] = mk[⇒] (λ f⋕ → γᶜ[ ⇄B⇄ ] ⟐ f⋕ ⟐ pure ⋅ η[ ⇄A⇄ ])
  ; extensive[_] = … ; reductive[_] = … }
\end{code}}
%
We can now state the specification for \A{\AgdaFunction{evalᵐ[}}
  \A{\AgdaBound{e}} \A{\AgdaFunction{]}} as a pure function which
approximating \A{\AgdaField{α[}} \A{\AgdaFunction{⇄env⇄
      ⇒⸢⇄ᶜ⸣}} \A{\AgdaFunction{⇄val⇄}} \A{\AgdaField{]}}
\A{\AgdaFunction{⋅}} \A{\AgdaFunction{evalᵐ[}} \A{\AgdaBound{e}}
  \A{\AgdaFunction{]}}.


\AgdaHide{
\begin{code}
infix  0 do_
infixr 0 _‣_
postulate
  -- see full development for definitions
  ⟬_⟭ : ∀ {A : POSet} → ⟪ A ⟫ → Set
  _⇰_ : Set → Set → Set
  [proof-mode]_∎ : ∀ {A : POSet} {x y : ⟪ A ⟫} → ⟬ x ⟭ ⇰ ⟬ y ⟭ → x ⊑ y
  do_ : ∀ {A : POSet} → {x y : ⟪ A ⟫} → ⟬ x ⟭ ⇰ ⟬ y ⟭ → ⟬ x ⟭ ⇰ ⟬ y ⟭
  _‣_ : ∀ {A : POSet} {x y z : ⟪ A ⟫} → ⟬ x ⟭ ⇰ ⟬ y ⟭ → ⟬ y ⟭ ⇰ ⟬ z ⟭ → ⟬ x ⟭ ⇰ ⟬ z ⟭
  begin_end : ∀ {A : POSet} {x y : ⟪ A ⟫} → ⟬ x ⟭ ⇰ ⟬ y ⟭ → ⟬ x ⟭ ⇰ ⟬ y ⟭
  [[_]] : ∀ {A : POSet} (x : ⟪ A ⟫) → ⟬ x ⟭ ⇰ ⟬ x ⟭
  ⟅_⟆[⊑] : ∀ {A : POSet} {x y : ⟪ A ⟫} → x ⊑ y → ⟬ x ⟭ ⇰ ⟬ y ⟭
  ⟅_⟆[≈] : ∀ {A : POSet} {x y : ⟪ A ⟫} → x ≈ y → ⟬ x ⟭ ⇰ ⟬ y ⟭
  ⟅_⟆[≡] : ∀ {A : POSet} {x y : ⟪ A ⟫} → x ≡ y → ⟬ x ⟭ ⇰ ⟬ y ⟭
  [focus-in_] : ∀ {A B : POSet} (op : ⟪ A ⇒ B ⟫) {x₁ x₂ : ⟪ A ⟫} → ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭ → ⟬ op ⋅ x₁ ⟭ ⇰ ⟬ op ⋅ x₂ ⟭
  [focus-left_𝑜𝑓_] : ∀ {A B C : POSet} (op : ⟪ A ⇒ B ⇒ C ⟫) (y : ⟪ B ⟫) {x₁ x₂ : ⟪ A ⟫}  → ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭ → ⟬ op ⋅ x₁ ⋅ y ⟭ ⇰ ⟬ op ⋅ x₂ ⋅ y ⟭
  [focus-right_𝑜𝑓_] : ∀ {A B C : POSet} (op : ⟪ A ⇒ B ⇒ C ⟫) (x : ⟪ A ⟫) {y₁ y₂ : ⟪ B ⟫} → ⟬ y₁ ⟭ ⇰ ⟬ y₂ ⟭ → ⟬ op ⋅ x ⋅ y₁ ⟭ ⇰ ⟬ op ⋅ x ⋅ y₂ ⟭
\end{code}}




\subsection{Calculating the Interpreter, in Agda}

Before calculating we must lift the various semantic functions to the monotonic
function space, like \A{\AgdaFunction{⟦\_⟧ᵘ}}, \A{\AgdaFunction{\_[\_]}} and
\A{\AgdaFunction{\_[\_]⋕}}:

\AgdaHide{
\begin{code}
postulate
  val⋕ : POSet
  ⇄val⇄ : ⇧ val ⇄ᶜ val⋕

open §-env⋕ val⋕ ⇄val⇄
\end{code}}

\begin{code}

↑⟦_⟧ᵘ : unary → ⟪ ⇧ val ⇒ ⇧ val ⟫
lookup[_] : ∀ {Γ} → var Γ → ⟪ ⇧ (env Γ) ⇒ ⇧ val ⟫
lookup⋕[_] : ∀ {Γ} → var Γ → ⟪ ⇧ (env⋕ Γ) ⇒ val⋕ ⟫

\end{code}
\AgdaHide{
\begin{code}  

↑⟦ u ⟧ᵘ = mk[↑⇒↑] (λ v → ⟦ u ⟧ᵘ v)
lookup[ x ] = mk[↑⇒↑] (λ ρ → ρ [ x ])
lookup⋕[ x ] = mk[↑⇒] (λ ρ⋕ → ρ⋕ [ x ]⋕)
\end{code}}

\noindent
Our calculation will be parameterized by an abstraction for
\A{\AgdaFunction{↑⟦\_⟧ᵘ}}:

\begin{code}

postulate
  ↑⟦_⟧ᵘ⋕ : unary → ⟪ val⋕ ⇒ val⋕ ⟫
  α[⟦⟧ᵘ] : ∀ {u v⋕} → α[ ⇄val⇄ ⇒⸢⇄ᶜ⸣ ⇄val⇄ ] ⋅ (pure ⋅ ↑⟦ u ⟧ᵘ) ⋅ v⋕ 
                       ⊑ pure ⋅ ↑⟦ u ⟧ᵘ⋕ ⋅ v⋕
\end{code}
%
We are now set up to calculate
\A{\AgdaFunction{evalᵐ⋕[}}
  \A{\AgdaBound{e}}
  \A{\AgdaFunction{]}}
from its specification
\A{\AgdaField{α[}}
  \A{\AgdaFunction{⇄env⇄}}
  \A{\AgdaFunction{⇒⸢⇄ᶜ⸣}}
  \A{\AgdaFunction{⇄val⇄}}
  \A{\AgdaFunction{]}}
\A{\AgdaFunction{⋅}}
\A{\AgdaFunction{evalᵐ[}}
  \A{\AgdaBound{e}}
  \A{\AgdaFunction{]}}. 
Because we want to ``discover''
\A{\AgdaFunction{evalᵐ⋕[}}
  \A{\AgdaBound{e}}
  \A{\AgdaFunction{]}},
rather than verify it a-posteriori, we state its existence
and then calculate its implementation:
\AgdaHide{
\begin{code}
postulate
  α[lookup] : ∀ {Γ} {x : var Γ} {ρ⋕ : ⟪ ⇧ (env⋕ Γ) ⟫} → α[ ⇄env⇄ ⇒⸢⇄ᶜ⸣ ⇄val⇄ ] ⋅ (pure ⋅ lookup[ x ]) ⋅ ρ⋕ ⊑ pure ⋅ lookup⋕[ x ] ⋅ ρ⋕
postulate
  β-evalᵐ[Num] : ∀ {Γ n} {R : ⟪ 𝒫 (⇧ (env Γ)) ⟫} → evalᵐ[ Num n ] * ⋅ R ⊑ return ⋅ ↑⟨ n ⟩
  β-evalᵐ[Var] : ∀ {Γ} {x : var Γ} → evalᵐ[ Var x ] ≈ pure ⋅ lookup[ x ]
  β-evalᵐ[Unary] : ∀ {Γ} {u : unary} {e : exp Γ} → evalᵐ[ Unary[ u ] e ] ≈ (pure ⋅ ↑⟦ u ⟧ᵘ) ⟐ evalᵐ[ e ]

\end{code}}

\begin{code}

evalᵐ⋕[_] : ∀ {Γ} → exp Γ → ⟪ ⇧ (env⋕ Γ) ⇒ val⋕ ⟫

\end{code}
\AgdaHide{
\begin{code}
evalᵐ⋕[ Num n ] = mk[⇒] (λ ρ⋕ → η[ ⇄val⇄ ] ⋅ ↑⟨ n ⟩)
evalᵐ⋕[ Var x ] = mk[⇒] (λ ρ⋕ → lookup⋕[ x ] ⋅ ρ⋕)
evalᵐ⋕[ Rand ] = …
evalᵐ⋕[ Unary[ u ] e ] = mk[⇒] (λ ρ⋕ → ↑⟦ u ⟧ᵘ⋕ ⋅ (evalᵐ⋕[ e ] ⋅ ρ⋕))
evalᵐ⋕[ Binary[ b ] e₁ e₂ ] = …
\end{code}}
%
\noindent
We begin by stating the type of our calculation:

\begin{code}

α[evalᵐ] :  ∀ {Γ} (e : exp Γ) (ρ⋕ : ⟪ ⇧ (env⋕ Γ) ⟫) 
            →  α[ ⇄env⇄ ⇒⸢⇄ᶜ⸣ ⇄val⇄ ] ⋅ evalᵐ[ e ] ⋅ ρ⋕ 
               ⊑ return ⋅ (evalᵐ⋕[ e ] ⋅ ρ⋕)

\end{code}
and proceed by induction, the first case being numeric expressions.
Each case will make use of our ``proof mode'' library, which we have developed in
pure Agda to support calculation-style notation.

\paragraph{Numeric literals}  

We begin by stating the goal. We do this using our proof mode library with
notation \A{\AgdaFunction{[[\_]]}}:

\begin{code}

α[evalᵐ] (Num n) ρ⋕ = [proof-mode]
  do  [[ α[ ⇄env⇄ ⇒⸢⇄ᶜ⸣ ⇄val⇄ ] ⋅ evalᵐ[ Num n ] ⋅ ρ⋕ ]]

\end{code}
\noindent
This state is definitionally equal to the expansion of
\A{\AgdaField{α[\_]}}:

\begin{code}

  ‣  [[ (pure ⋅ η[ ⇄val⇄ ] ⟐ evalᵐ[ Num n ] ⟐ γᶜ[ ⇄env⇄ ]) ⋅ ρ⋕ ]]

\end{code}
\noindent
Next we unfold the definition of \A{\AgdaFunction{\_⟐\_}}, also by Agda computation:

\begin{code}

  ‣  [[ (pure ⋅ η[ ⇄val⇄ ]) * ⋅ (evalᵐ[ Num n ] * ⋅ (γᶜ[ ⇄env⇄ ] ⋅ ρ⋕)) ]]

\end{code}
The next step is to focus to the right of the application and replace 
\A{\AgdaFunction{evalᵐ[}}
  \A{\AgdaInductiveConstructor{Num}}
  \A{\AgdaBound{n}}
  \A{\AgdaFunction{]}}
\A{\AgdaFunction{*}}
\A{\AgdaFunction{⋅}}
\A{\AgdaBound{R}} 
with its denotation
\A{\AgdaFunction{return}}
\A{\AgdaFunction{⋅}}
\A{\AgdaInductiveConstructor{↑⟨}}
\A{\AgdaBound{n}}
\A{\AgdaInductiveConstructor{⟩}}, which we prove by an auxiliary lemma
\A{\AgdaFunction{β-evalᵐ[Num]}}:


\dvh{I don't see the use of the aux.}

\begin{code}

  ‣  [focus-right [⋅] 𝑜𝑓 (pure ⋅ η[ ⇄val⇄ ]) * ] begin
     do  [[ evalᵐ[ Num n ] * ⋅ (γᶜ[ ⇄env⇄ ] ⋅ ρ⋕) ]]
     ‣   ⟅ β-evalᵐ[Num] {R = γᶜ[ ⇄env⇄ ] ⋅ ρ⋕ } ⟆[⊑]
     ‣   [[ return ⋅ ↑⟨ n ⟩ ]]
     end
  ‣  [[ (pure ⋅ η[ ⇄val⇄ ]) * ⋅ (return ⋅ ↑⟨ n ⟩) ]]

\end{code}
Next we use the monad right-unit law to eliminate the application of an
extension to a pure value:

\begin{code}

  ‣  ⟅ right-unit[*][ pure ⋅ η[ ⇄val⇄ ] ] ⟆[≈]
  ‣  [[ pure ⋅ η[ ⇄val⇄ ] ⋅ ↑⟨ n ⟩ ]]
  ‣  [[ return ⋅ (η[ ⇄val⇄ ] ⋅ ↑⟨ n ⟩) ]]

\end{code}
It is at this point which we have reached a pure computation, absent
of any specification effect. We declare this expression then to be the
definition of 
\A{\AgdaFunction{evalᵐ⋕[}}
  \A{\AgdaInductiveConstructor{Num}}
  \A{\AgdaBound{n}}
  \A{\AgdaFunction{]}}
and conclude:

\begin{code}

  ‣  [[ return ⋅ (evalᵐ⋕[ Num n ] ⋅ ρ⋕) ]]  ∎

\end{code}

\secendswithagda

\paragraph{Variables}

The calculation for variables is more interesting, as it doesn't ignore the
environment 
\A{\AgdaFunction{γᶜ[}}
  \A{\AgdaBound{⇄env⇄}}
  \A{\AgdaFunction{]}}
\A{\AgdaFunction{⋅}}
\A{\AgdaBound{ρ⋕}}. We begin again by stating the goal:

\begin{code}

α[evalᵐ] (Var x) ρ⋕ = [proof-mode]
  do [[ α[ ⇄env⇄ ⇒⸢⇄ᶜ⸣ ⇄val⇄ ] ⋅ evalᵐ[ Var x ] ⋅ ρ⋕ ]]

\end{code}
\noindent
As before, the first thing we do is unfold the definition of \A{\AgdaField{α[\_]}}:

\begin{code}

  ‣  [[ (pure ⋅ η[ ⇄val⇄ ] ⟐ evalᵐ[ Var x ] ⟐ γᶜ[ ⇄env⇄ ]) ⋅ ρ⋕ ]]
  ‣  [[ (pure ⋅ η[ ⇄val⇄ ]) * ⋅ (evalᵐ[ Var x ] * ⋅ (γᶜ[ ⇄env⇄ ] ⋅ ρ⋕)) ]]

\end{code}
\noindent
Next we focus to the right of the left-most, and left of the rightmost
\A{\AgdaFunction{\_⟐\_}} operator:

\begin{code}

  ‣  [focus-right [⋅] 𝑜𝑓 (pure ⋅ η[ ⇄val⇄ ]) * ] begin
     do  [[ evalᵐ[ Var x ] * ⋅ (γᶜ[ ⇄env⇄ ] ⋅ ρ⋕) ]]
     ‣   [focus-left [⋅] 𝑜𝑓 γᶜ[ ⇄env⇄ ] ⋅ ρ⋕ ] begin
         do  [[ evalᵐ[ Var x ] * ]]

\end{code}
\noindent
Here we recognize that the \emph{specification} for the semantics of
\A{\AgdaInductiveConstructor{Var}} \A{\AgdaBound{x}} is equivalent to
the \emph{computation} of looking up a variable in the environment,
using an auxiliary proof \A{\AgdaFunction{β-Faexp[Var]}}:

\begin{code}

  ‣  [focus-in [*] ] begin
     do  [[ evalᵐ[ Var x ] ]]
     ‣   ⟅ β-evalᵐ[Var] {x = x} ⟆[≈]
     ‣   [[ pure ⋅ lookup[ x ] ]]
     end
  ‣  [[ (pure ⋅ lookup[ x ]) * ]]
  end

\end{code}
Next we exploit the relationship between concrete environment lookup
and abstract environment lookup: 
\A{\AgdaField{α[}}
  \A{\AgdaFunction{⇄val⇄}} 
  \A{\AgdaFunction{⇒⸢⇄ᶜ⸣}} 
  \A{\AgdaFunction{⇄val⇄}}
  \A{\AgdaField{]}}
\A{\AgdaFunction{⋅}}
\A{\AgdaFunction{(pure}}
\A{\AgdaFunction{⋅}}
\A{\AgdaFunction{lookup[}}
  \A{\AgdaBound{x}}
  \A{\AgdaFunction{]})}
\A{\AgdaFunction{⊑}}
\A{\AgdaFunction{pure}}
\A{\AgdaFunction{⋅}}
\A{\AgdaFunction{lookup⋕[}}
  \A{\AgdaBound{x}}
  \A{\AgdaFunction{]}}. To arrive at
\A{\AgdaField{α[}}
    \A{\AgdaFunction{⇄val⇄}}
    \A{\AgdaFunction{⇒⸢⇄ᶜ⸣}}
    \A{\AgdaFunction{⇄val⇄}} 
    \A{\AgdaFunction{]}}
  \A{\AgdaFunction{⋅}}
  \A{\AgdaFunction{(pure}}
  \A{\AgdaFunction{⋅}}  
    \A{\AgdaFunction{lookup[}}
    \A{\AgdaBound{x}}
    \A{\AgdaFunction{])}},
  we first reason by extensiveness of \A{\AgdaFunction{⇄val⇄}}:

\begin{code}

  ‣  [[  (pure ⋅ lookup[ x ]) * ⋅ (γᶜ[ ⇄env⇄ ] ⋅ ρ⋕) ]]
  ‣  ⟅ extensiveᶜ[*][ ⇄val⇄ ] ⟆[⊑]
  ‣  [[  γᶜ[ ⇄val⇄ ] * ⋅ ((pure ⋅ η[ ⇄val⇄ ]) * ⋅ 
        ((pure ⋅ lookup[ x ]) * ⋅ (γᶜ[ ⇄env⇄ ] ⋅ ρ⋕))) ]]

\end{code}
\noindent
We identify the argument to the application as
\A{\AgdaField{α[}}
  \A{\AgdaFunction{⇄env⇄}}
  \A{\AgdaFunction{⇒⸢⇄ᶜ⸣}}
  \A{\AgdaFunction{⇄val⇄}}
  \A{\AgdaField{]}}
\A{\AgdaFunction{⋅}}
\A{\AgdaFunction{(pure}}
\A{\AgdaFunction{⋅}}
\A{\AgdaFunction{lookup[}}
  \A{\AgdaBound{x}}
  \A{\AgdaFunction{])}}
and weaken by its abstraction:

\begin{code}

     ‣  [focus-right [⋅] 𝑜𝑓 γᶜ[ ⇄val⇄ ] * ] begin
        do  [[ (pure ⋅ η[ ⇄val⇄ ]) * ⋅ ((pure ⋅ lookup[ x ]) * ⋅ (γᶜ[ ⇄env⇄ ] ⋅ ρ⋕)) ]]
        ‣   [[ α[ ⇄env⇄ ⇒⸢⇄ᶜ⸣ ⇄val⇄ ] ⋅ (pure ⋅ lookup[ x ]) ⋅ ρ⋕ ]]
        ‣   ⟅ α[lookup] {x = x} {ρ⋕} ⟆[⊑]
        ‣   [[ pure ⋅ lookup⋕[ x ] ⋅ ρ⋕ ]]
        ‣   [[ return ⋅ (lookup⋕[ x ] ⋅ ρ⋕) ]]
        end
     ‣  [[ γᶜ[ ⇄val⇄ ] * ⋅ (return ⋅ (lookup⋕[ x ] ⋅ ρ⋕)) ]]
     end
  ‣  [[ (pure ⋅ η[ ⇄val⇄ ]) * ⋅ (γᶜ[ ⇄val⇄ ] * ⋅ (return ⋅ (lookup⋕[ x ] ⋅ ρ⋕))) ]]

\end{code}
Finally we apply the reductive property of \A{\AgdaFunction{⇄val⇄}}:

\begin{code}

  ‣  ⟅ reductiveᶜ[*][ ⇄val⇄ ] ⟆[⊑]
  ‣  [[ return ⋅ (lookup⋕[ x ] ⋅ ρ⋕) ]]

\end{code}
\noindent
and declare the result as defining
\A{\AgdaFunction{eval⋕[}} \A{\AgdaInductiveConstructor{Var}}
  \A{\AgdaBound{x}} \A{\AgdaFunction{]}} and conclude:

\begin{code}

  ‣  [[ return ⋅ (evalᵐ⋕[ Var x ] ⋅ ρ⋕) ]]  ∎

\end{code}

\secendswithagda

\paragraph{Unary operators}

The calculation of unary operators is interesting because it leverages an
inductive hypothesis for the calculation.

\begin{code}

α[evalᵐ] (Unary[ o ] e) ρ⋕ with α[evalᵐ] e ρ⋕
... | IH = [proof-mode]
  do [[ α[ ⇄env⇄ ⇒⸢⇄ᶜ⸣ ⇄val⇄ ] ⋅ evalᵐ[ Unary[ o ] e ] ⋅ ρ⋕ ]]

\end{code}
In Agda, the \A{\AgdaKeyword{with}} notation is a variation of let-binding which
also performs dependent pattern matching refinements (although this
example doesn't use dependent pattern matching). We proceed as before
by expanding the definition of \A{\AgdaField{α[\_]}}.

\begin{code}

  ‣  [[  (pure ⋅ η[ ⇄val⇄ ] ⟐ evalᵐ[ Unary[ o ] e ] ⟐ γᶜ[ ⇄env⇄ ]) ⋅ ρ⋕ ]]
  ‣  [[  (pure ⋅ η[ ⇄val⇄ ]) * ⋅ 
         (evalᵐ[ Unary[ o ] e ] * ⋅ (γᶜ[ ⇄env⇄ ] ⋅ ρ⋕)) ]]

\end{code}
\noindent
As before we focus between then \A{\AgdaFunction{\_⟐\_}}s.

\begin{code}

  ‣  [focus-right [⋅] 𝑜𝑓 (pure ⋅ η[ ⇄val⇄ ]) * ] begin
     do  [[ evalᵐ[ Unary[ o ] e ] * ⋅ (γᶜ[ ⇄env⇄ ] ⋅ ρ⋕) ]]
     ‣   [focus-left [⋅] 𝑜𝑓 γᶜ[ ⇄env⇄ ] ⋅ ρ⋕ ] begin
         do  [[ evalᵐ[ Unary[ o ] e ] * ]]

\end{code}
\noindent
We then replace the \A{\AgdaFunction{evalᵐ[}}
  \A{\AgdaInductiveConstructor{Unary[}} \A{\AgdaBound{o}}
    \A{\AgdaInductiveConstructor{]}} \A{\AgdaBound{e}}
  \A{\AgdaFunction{]}} \emph{specification} with an equivalent
\emph{computation}: \A{\AgdaFunction{pure}} \A{\AgdaFunction{⋅}}
\A{\AgdaFunction{↑⟦}} \A{\AgdaBound{o}} \A{\AgdaFunction{⟧ᵘ}}.

\begin{code}

  ‣  [focus-in [*] ] begin
     do  [[ evalᵐ[ Unary[ o ] e ] ]]
     ‣   ⟅ β-evalᵐ[Unary] ⟆[≈]
     ‣   [[ pure ⋅ ↑⟦ o ⟧ᵘ ⟐ evalᵐ[ e ] ]]
     end
  ‣  [[ (pure ⋅ ↑⟦ o ⟧ᵘ ⟐ evalᵐ[ e ]) * ]]
  end

\end{code}
\noindent
We then reassociate.

\begin{code}

  ‣  [[ (pure ⋅ ↑⟦ o ⟧ᵘ ⟐ evalᵐ[ e ]) * ⋅ (γᶜ[ ⇄env⇄ ] ⋅ ρ⋕) ]]
  ‣  ⟅ associative[*][ pure ⋅ ↑⟦ o ⟧ᵘ , evalᵐ[ e ] , γᶜ[ ⇄env⇄ ] ⋅ ρ⋕ ] ⟆[≈]
  ‣  [[ (pure ⋅ ↑⟦ o ⟧ᵘ) * ⋅ (evalᵐ[ e ] * ⋅ (γᶜ[ ⇄env⇄ ] ⋅ ρ⋕)) ]]

\end{code}
\noindent
We focus to the argument of the application and apply extensiveness of
\A{\AgdaFunction{⇄val⇄}}:

\begin{code}

  ‣  [focus-right [⋅] 𝑜𝑓 (pure ⋅ ↑⟦ o ⟧ᵘ) * ] begin
     do  [[ evalᵐ[ e ] * ⋅ (γᶜ[ ⇄env⇄ ] ⋅ ρ⋕) ]]
     ‣   ⟅ extensiveᶜ[*][ ⇄val⇄ ] ⟆[⊑]
     ‣   [[  γᶜ[ ⇄val⇄ ] * ⋅ ((pure ⋅ η[ ⇄val⇄ ]) * ⋅ 
             (evalᵐ[ e ] * ⋅ (γᶜ[ ⇄env⇄ ] ⋅ ρ⋕))) ]]

\end{code}
\noindent
We recognize the argument to be 
\A{\AgdaField{α[}} %
\A{\AgdaFunction{⇄env⇄}} %
\A{\AgdaFunction{⇒⸢⇄ᶜ⸣}} %
\A{\AgdaFunction{⇄val⇄}} %
\A{\AgdaField{]}} %
\A{\AgdaFunction{⋅}} %
\A{\AgdaFunction{evalᵐ[}} %
  \A{\AgdaBound{e}} %
  \A{\AgdaFunction{]}} %
\A{\AgdaFunction{⋅}} %
\A{\AgdaBound{ρ⋕}}, %
which we can weaken to 
\A{\AgdaFunction{pure}} %
\A{\AgdaFunction{⋅}} %
\A{\AgdaFunction{evalᵐ⋕[}} %
  \A{\AgdaBound{e}} %
  \A{\AgdaFunction{]}} %
\A{\AgdaFunction{⋅}} %
\A{\AgdaBound{ρ⋕}} %
from the inductive hypothesis:

\begin{code}

  ‣  [focus-right [⋅] 𝑜𝑓 γᶜ[ ⇄val⇄ ] * ] begin
     do  [[ (pure ⋅ η[ ⇄val⇄ ]) * ⋅ (evalᵐ[ e ] * ⋅ (γᶜ[ ⇄env⇄ ] ⋅ ρ⋕)) ]]
     ‣   [[ α[ ⇄env⇄ ⇒⸢⇄ᶜ⸣ ⇄val⇄ ] ⋅ evalᵐ[ e ] ⋅ ρ⋕ ]]
     ‣   ⟅ IH ⟆[⊑]
     ‣   [[ pure ⋅ evalᵐ⋕[ e ] ⋅ ρ⋕ ]]
     ‣   [[ return ⋅ (evalᵐ⋕[ e ] ⋅ ρ⋕) ]]
     end
  ‣  [[ γᶜ[ ⇄val⇄ ] * ⋅ (return ⋅ (evalᵐ⋕[ e ] ⋅ ρ⋕)) ]]

\end{code}
\noindent
We apply the monad right unit to eliminate the extension:

\begin{code}

    ‣  ⟅ right-unit[*][ γᶜ[ ⇄val⇄ ] ] ⟆[≈]
    ‣  [[ γᶜ[ ⇄val⇄ ] ⋅ (evalᵐ⋕[ e ] ⋅ ρ⋕) ]]
    end
  ‣  [[ (pure ⋅ ↑⟦ o ⟧ᵘ) * ⋅ (γᶜ[ ⇄val⇄ ] ⋅ (evalᵐ⋕[ e ] ⋅ ρ⋕)) ]]
  end

\end{code}
\noindent
Next we recognize this as an abstraction of \A{\AgdaFunction{⟦}}
  \A{\AgdaBound{u}} \A{\AgdaFunction{⟧ᵘ}}, for which we have
parameterized the calculation:

\begin{code}

  ‣  [[  (pure ⋅ η[ ⇄val⇄ ]) * ⋅ 
         ((pure ⋅ ↑⟦ o ⟧ᵘ) * ⋅ (γᶜ[ ⇄val⇄ ] ⋅ (evalᵐ⋕[ e ] ⋅ ρ⋕))) ]]
  ‣  [[ α[ ⇄val⇄ ⇒⸢⇄ᶜ⸣ ⇄val⇄ ] ⋅ (pure ⋅ ↑⟦ o ⟧ᵘ) ⋅ (evalᵐ⋕[ e ] ⋅ ρ⋕) ]]
  ‣  ⟅ α[⟦⟧ᵘ] ⟆[⊑]
  ‣  [[ pure ⋅ ↑⟦ o ⟧ᵘ⋕ ⋅ (evalᵐ⋕[ e ] ⋅ ρ⋕) ]]
  ‣  [[ return ⋅ (↑⟦ o ⟧ᵘ⋕ ⋅ (evalᵐ⋕[ e ] ⋅ ρ⋕)) ]]

\end{code}
\noindent
We declare the result to be the definition of \A{\AgdaFunction{eval⋕}} and conclude:

\begin{code}

  ‣  [[ return ⋅ (evalᵐ⋕[ Unary[ o ] e ] ⋅ ρ⋕) ]]  ∎

\end{code}
\AgdaHide{
\begin{code}
α[evalᵐ] Rand = …
α[evalᵐ] (Binary[ b ] e₁ e₂) = …
\end{code}
}
%
\noindent
We can then define \A{\AgdaFunction{evalᵐ⋕}} as the result of calculation:

\input{eval-defn-scrape.tex}

\subsection{End to End: Connection to the Collecting Semantics}

Recall that the original collecting semantics we wish to abstract,
\(eval\), is the extension of the monadic semantics,
\(evalᵐ*\). To establish the final proof of abstraction, we
promote the partial order of the previous section between monadic
functions: \AgdaHide{
\begin{code}
module §-dummy {Γ} (e : exp Γ) where
  postulate
    _*⸢⇄ᶜ⸣ : ∀ {A₁ A₂ : POSet} → A₁ ⇄ᶜ A₂ → (𝒫 A₁ ⇄ 𝒫 A₂)
    _⇒⸢⇄⸣_ :  ∀ {A₁ A₂ B₁ B₂ : POSet} 
              → A₁ ⇄ A₂ → B₁ ⇄ B₂ → (A₁ ⇒ B₁) ⇄ (A₂ ⇒ B₂)

\end{code}}

\begin{code}

  α[eval] :  α[ ⇄env⇄ ⇒⸢⇄ᶜ⸣ ⇄val⇄ ] ⋅ evalᵐ[ e ] 
             ⊑ pure ⋅ evalᵐ⋕[ e ]

\end{code}
\AgdaHide{
\begin{code}
  α[eval] = …
\end{code}}
%
\noindent
to a partial ordering between extended functions:

\begin{code}

  α[eval*] :  α[ (⇄env⇄ *⸢⇄ᶜ⸣) ⇒⸢⇄⸣ (⇄val⇄  *⸢⇄ᶜ⸣) ] ⋅ evalᵐ[ e ] * 
              ⊑ (pure ⋅ evalᵐ⋕[ e ]) *

\end{code}
\AgdaHide{
\begin{code}
  α[eval*] = …
\end{code}}
where \A{\AgdaFunction{\_*⸢⇄ᶜ⸣}} is the promotion operator from
Kleisli to classical Galois connections, and
\A{\AgdaFunction{\_⇒⸢⇄⸣\_}} is the standard classical Galois connection
pointwise lifting operator.

We define \A{\AgdaFunction{\_*⸢⇄ᶜ⸣}} following the proof of inclusion
from Kleisli Galois connections into classical Galois connections:

\begin{code}

_*⸢⇄ᶜ⸣ : ∀ {A₁ A₂ : POSet} → A₁ ⇄ᶜ A₂ → (𝒫 A₁ ⇄ 𝒫 A₂)
⇄A⇄ *⸢⇄ᶜ⸣ = record
  { α[_] = (pure ⋅ η[ ⇄A⇄ ]) *
  ; γ[_] = γᶜ[ ⇄A⇄ ] *
  ; extensive[_] = … ; reductive[_] = … }

\end{code}
%
\AgdaHide{
\begin{code}

_⇒⸢⇄⸣_ :  ∀ {A₁ A₂ B₁ B₂ : POSet} 
          → A₁ ⇄ A₂ → B₁ ⇄ B₂ → (A₁ ⇒ B₁) ⇄ (A₂ ⇒ B₂)
⇄A⇄ ⇒⸢⇄⸣ ⇄B⇄ = record
  { α[_] = mk[⇒] (λ f  → α[ ⇄B⇄ ] ⊙ f  ⊙ γ[ ⇄A⇄ ])
  ; γ[_] = mk[⇒] (λ f⋕ → γ[ ⇄B⇄ ] ⊙ f⋕ ⊙ α[ ⇄A⇄ ])
  ; extensive[_] = … ; reductive[_] = … }
\end{code}}
%
\noindent
and we prove soundness and completeness following the definitions given in
section~\ref{sec:foundations}:
%
\begin{code}


sound/complete :
  ∀ {A₁ A₂ B₁ B₂ : POSet}
    (⇄A⇄ : A₁ ⇄ᶜ A₂) (⇄B⇄ : B₁ ⇄ᶜ B₂)
    (f : ⟪ A₁ ⇒ 𝒫 B₁ ⟫) (f⋕ : ⟪ A₂ ⇒ 𝒫 B₂ ⟫)
  → (∀ x⋕ →  α[ ⇄A⇄ ⇒⸢⇄ᶜ⸣ ⇄B⇄ ] ⋅ f ⋅ x⋕ 
             ⊑ f⋕ ⋅ x⋕)
  ↔ (∀ X⋕ →  α[ ⇄A⇄ *⸢⇄ᶜ⸣ ⇒⸢⇄⸣ ⇄B⇄ *⸢⇄ᶜ⸣ ] ⋅ f * ⋅ X⋕ 
             ⊑ f⋕ * ⋅ X⋕)
sound/complete = …

\end{code}
\noindent
\(α[eval*]\) is then defined as an application of the soundness direction of
\(sound/complete\):

\begin{code}

α[evalᵐ*] :  ∀ {Γ} (e : exp Γ) (R⋕ : ⟪ 𝒫 (⇧ (env⋕ Γ)) ⟫) 
  → α[ (⇄env⇄ *⸢⇄ᶜ⸣) ⇒⸢⇄⸣ (⇄val⇄  *⸢⇄ᶜ⸣) ] ⋅ evalᵐ[ e ] * ⋅ R⋕ 
  ⊑ (pure ⋅ evalᵐ⋕[ e ]) * ⋅ R⋕
α[evalᵐ*] e R⋕ = 
  π₁ (sound/complete ⇄env⇄ ⇄val⇄ evalᵐ[ e ] (pure ⋅ evalᵐ⋕[ e ])) 
  (α[evalᵐ] e) R⋕

\end{code}
The next section describes the soundness and completeness result which we rely
on in this section in more detail, and develops the foundations of Kleisli
Galois connections.

\section{Foundations of Kleisli Galois Connections}
\label{sec:foundations}

Kleisli Galois connections are formed by re-targeting the classical
Galois connection framework from the category of posets to the
powerset Kleisli category, where morphisms are monotonic monadic functions, as
described in section~\ref{sec:kleisli-galois-connections}.
  
\dvh{Should I be worried that in all this talk of Galois connections,
  the ordering on posets is never made explicit?}
\dcd{is this fixed??}
% see issue #15

Unfolding the definition of \(extensiveᵐ\) and \(reductiveᵐ\) from
section~\ref{sec:kleisli-galois-connections}     we reveal equivalent, more
intuitive properties, which we call \(soundnessᵐ\) and \(completenessᵐ\):
\begin{align*}
soundnessᵐ    &: ∀(x). ∃(y).   y ∈ αᵐ(x) ∧ x ∈ γᵐ(y)\\
completenessᵐ &: ∀(x₁⋕,x₂⋕,x). x ∈ γᵐ(x₁⋕) ∧ x₂⋕ ∈ αᵐ(x) → x₂⋕ ⊑ x₁⋕
\end{align*}

These definitions provide a \emph{relational} setup for
the soundness and completeness of \(αᵐ\) and \(γᵐ\). In fact, the
model for the monadic space \(A → 𝒫(B)\) is precisely \(A ↗ B ↘
Set\),\footnote{Here \(↘\) denotes antitonic functions;
  \(Set\) is ordered by implication.} i.e. monotonic relations
over \(A\) and \(B\).  We have therefore recovered a relational
setting for soundness and completeness of abstractions between sets,
purely by following the natural consequences of instantiating the
Galois connection framework to the powerset Kleisli category.

\subsection{Lifting Kleisli Galois Connections}

The final step of our calculational relies on bridging the gap between Kleisli
and classical Galois connections. This bridge enables us to construct a Kleisli
Galois connection
\[env → 𝒫(val) \galois{α^{e→ᵐv}}{γ^{e→ᵐv}} env⋕ → 𝒫(val⋕)\] 
and calculation
\(α^{e→ᵐv}(evalᵐ[e]) ⊑ evalᵐ⋕[e]\text.\) and lift both systematically to
classical results, and to do so without any loss of generality. We formalize
these notions in the following theorems:

\begin{theorem}[GC-Soundness] 
\label{thm:kleisli-classical-soundness}
For every Kleisli Galois connection \[A \galois{αᵐ}{γᵐ} B\]
there exists a classical Galois connection
\[𝒫(A) \galois{α*}{γ*} 𝒫(B)\]
where \(α* ≔ αᵐ*\) and \(γ* ≔ γᵐ*\).
\end{theorem}

\begin{theorem}[GC-Completeness]
\label{thm:kleisli-classical-completeness}
For every classical Galois connection
\[𝒫(A) \galois{α}{γ} 𝒫(B)\] 
where \(α\) and \(γ\) are of the form \(α = αᵐ*\) and \(γ = γᵐ*\),
there exists a Kleisli Galois connection
\[A \galois{αᵐ}{γᵐ} B\]
\end{theorem}
\noindent
Next we show how to lift Kleisli Galois connections pointwise to a classical
Galois connection over extensions:
\begin{lemma}[Pointwise-lifting-extensions]
Given Kleisli Galois connections \[A₁ \galois{αᵐᴬ}{γᵐᴬ} A₂ \quad B₁ \galois{αᵐᴮ}{γᵐᴮ} B₂ \]
there exists a classical Galois connection \[𝒫(A₁) ↗ 𝒫(B₁) \galois{α^{(A→ᵐB)*}}{γ^{(A→ᵐB)*}} 𝒫(A₂) ↗ 𝒫(B₂) \]
where 
\begin{align*}
α^{(A→ᵐB)*}(F) & ≔ αᵐᴮ* ∘ F ∘ γᵐᴬ* & γ^{(A→ᵐB)*}(F⋕) & ≔ γᵐᴮ* ∘ F⋕ ∘ γᵐᴬ*
\end{align*}
\end{lemma}
\noindent
And finally we establish an isomorphism of partial ordering between monadic
functions and their extensions:
\begin{theorem}[Soundness] 
\label{thm:kleisli-classical-pointwise-soundness}
Given Kleisli Galois connections \[A₁ \galois{αᵐᴬ}{γᵐᴬ} A₂ \quad B₁ \galois{αᵐᴮ}{γᵐᴮ} B₂ \]
and functions \( f ∈ A₁ ↗ 𝒫(B₁) \) and \( f⋕ ∈ A₂ ↗ 𝒫(B₂) \),
partial orders under the Kleisli pointwise lifting 
imply partial orders under extension:
\[
α^{A→ᵐB}(f) ⊑ f⋕ ⇒ α^{(A→ᵐB)*}(f*) ⊑ f⋕*\text.
\]
\end{theorem}

\begin{theorem}[Completeness]
Given Kleisli Galois connections \[A₁ \galois{αᵐᴬ}{γᵐᴬ} A₂ \quad B₁ \galois{αᵐᴮ}{γᵐᴮ} B₂ \]
and functions \( f ∈ A₁ ↗ 𝒫(B₁) \) and \( f⋕ ∈ A₂ ↗ 𝒫(B₂) \),
partial orders under the Kleisli pointwise lifting for extensions 
imply partial orders without extension:
\[
α^{(A→ᵐB)*}(f*) ⊑ f⋕* ⇒ α^{A→ᵐB}(f) ⊑ f⋕\text.
\]
\end{theorem}

\subsection{Constructive Galois Connections}

Analogously to Kleisli Galois connection, we state extensiveness and
reductiveness as equivalent soundness and completeness properties:
\begin{align*}
  soundnessᶜ &: ∀(x). x ∈ γ(η(x))\\
  completenessᶜ &: ∀(x⋕,x). x ∈ γ(x⋕) ⇒ η(x) ⊑ x⋕
\end{align*}

These statements have even stronger intuitive meaning that that of
Kleisli Galois connections. \(soundnessᶜ\) states that \(x\) must be
in the concretization of its abstraction, and \(completenessᶜ\) states
that the best abstraction for \(x\), i.e.~\(η(x)\), must be better any
other abstraction for \(x\), i.e.~\(x⋕\).

Constructive Galois connections are initially motivated by the need for pure
abstraction functions during the process of calculation, and simultaneously
from the observation that abstraction functions are often pure function in
practice. What is surprising is that constructive Galois connections are not a
special case of Kleisli Galois connections: \emph{all} Kleisli Galois
connections are constructive.

\begin{theorem}
The set of Kleisli Galois connections is isomorphic to the set of
constructive Galois connections.
\end{theorem}
\begin{proof}
The easy direction is constructing a Kleisli Galois connection from a
constructive Galois connection. Given a constructive Galois connection 
\(A \galois{η}{γᶜ} B \), we construct the following Kleisli Galois connection:
\begin{align*}
  & αᵐ : A → 𝒫(B)   && γᵐ : B → 𝒫(A)\\
  & αᵐ = pure(η)    && γᵐ = γᶜ
\end{align*}
%
Proofs for extensiveness and reductiveness follow definitionally.

The next step is to construct a Constructive Galois connection from a
Kleisli Galois connection \(A \galois{αᵐ}{γᵐ} B\). This at first seems
paradoxical, since it requires constructing an abstraction
\emph{function} \(η : A → B\) from the given abstraction
\emph{specification} \(αᵐ : A → 𝒫(B)\). However, we are able exploit
the property of \(soundnessᵐ\), which is equivalent to \(extensiveᵐ\),
from the definition of Kleisli Galois connections to define \(η\).

Recall the soundness judgement for Kleisli Galois connections, which arise
directly from the definition of \(return\) and \(\_*\).
\begin{gather*}
  soundnessᵐ : ∀(x). ∃(y). y ∈ α(x) ∧ x ∈ γ(y)
\end{gather*}
Given a proof of \(soundnessᵐ\), we use the axiom of choice to extract the
existentially quantified \(y\) given an \(x\). In fact, the axiom of choice is not
an axiom in constructive logic, rather it is a \emph{theorem} of choice, which can
be written in Agda.

\begin{code}
  
choice  : ∀ {A B} {P : A → B → Set} → (∀ x → ∃ y 𝑠𝑡 P x y) → A → B
choice f x with f x
... | ∃ y ,, P[x,y] = y

\end{code}
Using the axiom of choice we easily define \(η\) and \(γᶜ\).
\begin{align*}
  & η ∈ A ↗ B                                             && γᶜ ∈ B ↗ 𝒫(A)\\
  & η(x) = y \mbox{ where }(∃ y : y ∈ αᵐ(x) ∧ x ∈ γᵐ(y))  && γᶜ = γᵐ             
\end{align*}

In order for \(η\) and \(γᶜ\) to be a valid Galois connection we must still
prove extensiveness and reductiveness. To do so we instead prove \(soundnessᶜ\)
and \(completenessᶜ\), which are equivalent to \(extensiveᶜ\) and
\(reductiveᶜ\). These proofs follow from the soundness evidence attached to
\(η(x)\) and its use of the axiom of choice.


\begin{lemma}[\(soundnessᶜ\)]
\label{thm:soundnessc}
  \(∀(x). x ∈ γᶜ(η(x))\).
\end{lemma}

\begin{lemma}[\(completenessᶜ\)]
\label{thm:completenessc}
  \(∀(x⋕,x). x ∈ γᶜ(x⋕) → η(x) ⊑ x⋕\).
\end{lemma}

Finally, to establish the isomorphism, we show that transforming a Kleisli
Galois connection into a constructive one and back results in the same Galois
connection. To show this we apply the following lemma,
 a restatement of its classical analogue
\cite[p.239]{dvanhorn:Neilson:1999} in the Kleisli setting:
\begin{lemma}[Kleisli-Uniqueness]
\label{thm:kleisli-uniqueness}
  Given two Kleisli Galois connections \(A \galois{α₁ᵐ}{γ₁ᵐ} B\) and \(A
  \galois{α₂ᵐ}{γ₂ᵐ} B\), \(α₁ᵐ = α₂ᵐ\) if and only if \(γ₁ᵐ = γ₂ᵐ\)
\end{lemma}

To use this lemma, we recognize that the concretization functions
\(γᵐ\) and \(γᶜ\) are definitionally the same for both mappings
between Kleisli and constructive Galois connections.  It then follows
that \(αᵐ\) and \(pure(η)\) must be equal.

\end{proof}

The consequence of the isomorphism between Kleisli and constructive Galois
connections is that we may work directly with constructive Galois connections
without any loss of generality. Furthermore, we can assume a pure ``extraction
function'' \(η\) for every Kleisli abstraction function \(αᵐ\) where \(αᵐ =
pure(η)\). 

Finally, our proof of isomorphism gives a foundational explanation for
\emph{why} some Galois connections happen to have fully computational functions
as their abstraction functions. These pure abstraction functions are no
accident; they are induced by the Kleisli Galois connection setup embedded in
constructive logic, where the axiom of choice is definable as a theorem with
computational content.


\section{Related Work}

This work connects two long strands of research: abstract
interpretation and dependently typed programming.  The former is
founded on the pioneering work of Cousot and
Cousot~\cite{dvanhorn:Cousot:1977:AI,dvanhorn:Cousot1979Systematic};
the latter on that of Martin-L\"of~\cite{local:lof}, embodied in
Norell's Agda~\cite{local:norell:thesis}.  A key technical insight of
ours is to use a monadic structure for Galois connections and proofs
by calculus, following the example of
Moggi~\cite{davdar:Moggi:1989:Monads} for the $\lambda$-calculus.

\paragraph{Calculational abstract interpretation}

Cousot describes the calculation approach to abstract interpretation
by example in his lecture notes \cite{local:cousot-mit}, the
foundations for which can be found in \cite{dvanhorn:Cousot98-5}, and
recently introduced a unifying calculus for Galois
connections~\cite{dvanhorn:Cousot2014Galois}.
%
Other notable uses of calculational abstract interpretation include
the calculational derivation of higher order control flow
analysis~\cite{davdar:midtgaard:2008:calculational-cfa} and the
calculation of polynomial time graph
algorithms~\cite{dvanhorn:Sergey2012Calculating}.

Our work mechanizes Cousot's calculations, and provides a suitable foundation
for mechanizing other instances of calculational abstract interpretation.

\paragraph{Calculational program design}

Related to the calculation of abstract interpreters is the calculation
of programs, long advocated by Bird and others as calculational
program design
\cite{local:algebra-of-programming,local:Bird90:Calculus}.

Calculational program design has been successfully mechanized in proof
assistants~\cite{dvanhorn:Tesson2011Program}. This practice does not
encounter the non-constructive metatheory issues which show up in
mechanizing calculational abstract interpreters. In mechanized
calculational program design, specifications are fully constructive,
whose inhabitants can be readily executed as programs. In abstract
interpretations the specifications are inherently non-constructive,
which leads to the need for new theoretical machinery.

\paragraph{Verified static analyses}

Verified abstract interpretation has seen many promising results
\cite{local:Pich:these,dvanhorn:Cachera2010Certified,dvanhorn:Blazy2013Formal,dvanhorn:Barthe2007Certified},
scaling up recently to large-scale real-world static analyzers
\cite{dvanhorn:Jourdan2015FormallyVerified}.
%
Mechanized abstract interpretation has yet to benefit from being built
on a solid, compositional Galois connection framework. Until now
approach have used either ``α-only'' or ``γ-only'' encodings of
soundness and (sometimes) completeness. Our techniques for isolating
specification effects should readily apply to these existing
approaches.

\paragraph{Monadic abstract interpretation}

The use of monads in abstract interpretation has recently been used to
good
effect~\cite{dvanhorn:Sergey2013Monadic,local:DBLP:journals/corr/DaraisMH14}.
However that work uses monads to structure the language semantics,
whereas our approach has been to use monadic structure in the Galois
connections and proofs by calculus.

\paragraph{Galculator}

The \emph{Galculator}~\cite{dvanhorn:Silva2008Galculator} is a proof
assistant founded on an algebra of Galois connections.  This tool is
similar to ours in that it mechanically verifies Galois connection
calculations; additionally it fully automates the calculational
derivations themselves.  Our approach is more general, supporting
arbitrary set-theoretic reasoning and embeded within a general purpose
proof assistant, however their approach is fully automated for the
small set of derivations which reside within their supported
theory. We foresee a marriage of the two approaches, where simple
algebraic calculations are derived automatically, yet more complicated
connections are still expressible and provable within the same
mechanized framework.

\paragraph{Future directions}

Now that we have established a foundation for constructive Galois
connection calculation, we see value in verifying larger derivations
(e.g.~\cite{dvanhorn:midtgaard-jensen-sas-08,
  dvanhorn:Sergey2012Calculating}).
%
Furthermore we would like to explore whether or not our techniques
have any benefit in the space of general-purpose program calculations
\emph{\`a la} Bird.

There have also been recent developments on compositional abstract
interpretation frameworks~\cite{local:DBLP:journals/corr/DaraisMH14}
where abstract interpreter implementations and their proofs of
soundness via Galois connection are systematically derived
side-by-side. Their framework relies on correctness properties
transported by \emph{Galois transformers}, which we believe would
greatly benefit from mechanization, because they hold both
computational and specification content.

\section{Conclusions}


Over fifteen years ago, when concluding ``The calculational design of
a generic abstract interpreter''~\cite[p.~85]{dvanhorn:Cousot98-5},
Cousot wrote:
\begin{quotation}
\noindent
The emphasis in these notes has been on the correctness of the design
by calculus. The mechanized verification of this formal development
using a proof assistant can be foreseen with automatic extraction of a
correct program from its correctness proof.
\end{quotation}
%
This paper realizes that vision, giving the first mechanically
verified proof of correctness for Cousot's abstract interpreter.  Our
proof ``by calculus'' closely follows the original paper-and-pencil
proof.  The primary discrepancy being the use of monadic reasoning to
isolate \emph{specification effects}.  By maintaining this monadic
discipline, we are able to verify calculations by Galois connections
\emph{and} extract computation content from pure results.  The
resulting static analyzer is correct by verified construction and
therefore does not suffer from bugs present in the
original.\footnote{\scriptsize\url{http://www.di.ens.fr/~cousot/aisoftware/Marktoberdorf98/Bug_History}}

\acks

We gratefully acknowledge the Colony Club in Washington, DC~for
providing a fruitful environment in which to do this research.

\balance
\bibliographystyle{abbrvnat}
\bibliography{dvh-bibliography,dcd-bibliography,local}


\end{document}
