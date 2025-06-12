---
tags:
  - ACT
  - CategoryTheory
  - co-Fibrations
  - FiberedCategories
  - DoubleCategories
date: 2025-06-03T14:55:00
type: Project Notes
summary: 
status: Uncomplete
---
## 1. Introduction

In this note we provide an introduction to examples of fibrations in the context of modules of systems (c.f. [[Towards a Double Operadic Theory of Systems - Scrap Notes]]). This includes posetal fibrations, which we discuss first, as well as lattice fibrations and distributive lattice fibrations (recall that a lattice is a poset that has finite products and coproducts, while a distributive lattice has the property that products preserve coproducts in each variable separately, or equivalently coproducts preserve products in each variable separately). This theory is closely related to computation in continuous dynamics, as presented by Sophie Libkind in a Berkeley Seminar talk[^1], we begin with a review of.

### 1.1. Motivation: Computation in Continuous Dynamics 

We begin with considering *affordances of a low-level system*. Throughout let $X$ be a smooth manifold, and let $\phi_0:\mathbb{R}\times X\to X$ be a *global flow* corresponding to some complete vector field $V:X\to TX$. To study such a manifold with attached global flow, we can look at its attractors. To make this more formal we need a notion of eventuality.

>[!def] Eventuality
>For $N \subseteq X$, the **eventual set** of $N$ is
>$$\text{Ev}(N,\phi_0) := \omega(N,\phi_0) := \bigcap_{t\geq 0}\overline{\phi_0((t,\infty),N)}$$

Then using the notion of eventuality we can define attractors.

>[!def] Attractors
>A subset $A \subseteq X$ is an **attractor** if there exists a compact neighborhood $N \subseteq X$ of $A$ such that 
>$$A = \text{Ev}(N,\phi_0)$$
>We say that $N \subseteq X$ is an **attracting neighborhood** if $\text{Ev}(N,\phi_0)\subseteq \text{int}\,N$.

Note that an attractor is always a compact subset in this context, and further a subset is an attractor precisely when it is the eventual set of some attracting neighborhood.

We will write $\text{Att}(\phi_0)$ for the set of attractors of $\phi_0$, and $\text{ANbhd}(\phi_0)$ for the set of attracting neighborhoods of $\phi_0$. By definition we have a surjection $\text{Ev}(-,\phi_0):\text{ANbhd}(\phi_0)\twoheadrightarrow \text{Att}(\phi_0)$, which is further a map of lattices.

We can upgrade our analysis by instead considering a **parametrized flow** $\phi:\mathbb{R}\to \mathsf{End}(X)^\Lambda$, for some parameter space $\Lambda$, associated to a parametrized vector field $V:\Lambda \times X \to TX$. In this case, we get a pre-sheaf
$$\text{Att}_\phi^{pre}:\mathsf{Open}(\Lambda)^{op}\to \mathsf{Set},\;U\mapsto \left\{N \in \mathsf{Compact}(X)\Big\vert \begin{array}{c}
\forall \lambda \in U \\ N \in \text{ANbhd}(\phi_\lambda)
\end{array}\right\}/\sim_U$$
where $N_1\sim_UN_2$ if and only if for all $\lambda \in U$, $\text{Ev}(N_1,\phi_\lambda) = \text{Ev}(N_2,\phi_\lambda)$.

Let $\text{Att}_\phi$ denote the sheafification of $\text{Att}_\phi^{pre}$ with respect to the standard open cover topology on the domain. We say that $\sigma \in \text{Att}_\phi(U)$ is an **attractor that continues over $U$**. It turns out that $\text{Att}_\phi$ factors through the category of bounded distributive lattices (we would like this to be complete bounded distributive lattices)

>[!proposition] Stalks of Attractor Sheaf
>The stalks of the attractor sheaf are given by $\text{Att}_{\phi,\lambda} = \text{Att}(\phi_\lambda)$.

`\begin{proof}`
Note that the stalks agree with those of the pre-sheaf, by the universal property of sheafification. Additionally, for $N \subseteq X$ compact,
$$\{\lambda \in \Lambda\mid N \in \text{ANbhd}(\phi_\lambda)\}=\{\lambda\in \Lambda\mid\bigcap_{t\geq 0}\overline{\phi_\lambda((t,\infty),N)}\subseteq \text{int}\,N\}$$
is open in $\Lambda$ **TBC**
`\end{proof}`

Now, let $\mathsf{APath}(\Lambda)$ be the category with objects open sets in $\Lambda$, and morphisms $V\to W$ tuples $(U_1,...,U_n)$ with $V=U_1$, $W=U_n$, and $U_i\cap U_{i+1}\neq \emptyset$. Then we can define a new functor $\mathsf{Att}_\phi:\mathsf{APath}(\Lambda)\to \mathsf{CdLat}$ which acts the same on objects, and such that if $(U_1,...,U_n)$ is a morphism, we define $\mathsf{Att}_\phi(U_1)\to \mathsf{Att}_\phi(U_n)$ to be given by the diagram
```latexsvg
\documentclass[]{standalone}
\usepackage{mathrsfs}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{tikz-cd}
\usetikzlibrary{decorations.pathmorphing}
\usetikzlibrary{calc}
\tikzset{curve/.style={settings={#1},to path={(\tikztostart)
	.. controls ($(\tikztostart)!\pv{pos}!(\tikztotarget)!\pv{height}!270:(\tikztotarget)$)
	and ($(\tikztostart)!1-\pv{pos}!(\tikztotarget)!\pv{height}!270:(\tikztotarget)$)
	.. (\tikztotarget)\tikztonodes}},
	settings/.code={\tikzset{quiver/.cd,#1}
		\def\pv##1{\pgfkeysvalueof{/tikz/quiver/##1}}},
	quiver/.cd,pos/.initial=0.35,height/.initial=0}

\tikzset{tail reversed/.code={\pgfsetarrowsstart{tikzcd to}}}
\tikzset{2tail/.code={\pgfsetarrowsstart{Implies[reversed]}}}
\tikzset{2tail reversed/.code={\pgfsetarrowsstart{Implies}}}
\tikzset{no body/.style={/tikz/dash pattern=on 0 off 1mm}}
\begin{document}
\hspace{2cm}
\begin{tikzcd}
	{\mathsf{Att}_\phi(U_1)} &&&& {\mathsf{Att}_\phi(U_2)} &&&& {\mathsf{Att}_\phi(U_n)} \\
	\\
	&& {\mathsf{Att}_\phi(U_1\cap U_2)} &&&& \cdots
	\arrow["{\vert_{U_1\cap U_2}}"', from=1-1, to=3-3]
	\arrow[""{name=0, anchor=center, inner sep=0}, "{\vert_{U_1\cap U_2}}", from=1-5, to=3-3]
	\arrow["{\vert_{U_2\cap U_3}}"', from=1-5, to=3-7]
	\arrow[""{name=1, anchor=center, inner sep=0}, "{\vert_{U_{n-1}\cap U_n}}", from=1-9, to=3-7]
	\arrow[""{name=2, anchor=center, inner sep=0}, "{\vert_{U_1\cap U_2}^*}", curve={height=-24pt}, from=3-3, to=1-5]
	\arrow[""{name=3, anchor=center, inner sep=0}, "{\vert_{U_{n-1}\cap U_n}^*}", curve={height=-24pt}, from=3-7, to=1-9]
	\arrow["\dashv"{anchor=center, rotate=-45}, draw=none, from=2, to=0]
	\arrow["\dashv"{anchor=center, rotate=-42}, draw=none, from=3, to=1]
\end{tikzcd}
\hspace{2cm}
\end{document}
```
where the left adjoints are constructed using the fact that we have arbitrary meets.


So far we've been looking at low-level systems. Next, we want to consider high-level computation of such systems. First, we can think of a *context dependent discrete dynamical system* as a functor $\mathcal{C}\to \mathsf{Set}$. If instead we look at functors into some other full subcategory of $\mathsf{Cat}$, such as $\mathsf{Poset}$, then we obtain other kinds of structured context dependent dynamical systems. For instance, with $\mathsf{Poset}$ we get *hierarchical context dependent discrete dynamical systems*.

## 2. (op)Posetal Fibrations

(op)Posetal fibrations are a special kind of fibered category (c.f. [[Basic Fibered Categories]]). Indeed, recall that $\mathsf{Poset}$, the category of posets, is a full subcategory of the category of categories, $\mathsf{Cat}$. Thus, from [[Basic Fibered Categories#^11c5c8]] and the discussion following [[Basic Fibered Categories#^b6547c]], for any category $\mathcal{B}$, we have a strict $2$-equivalence of strict $2$-categories 
$$
\int_\mathcal{B}:\mathsf{Fun}_p(\mathcal{B}^{op},\mathsf{Poset}) \leftrightarrows \mathsf{FibPos}(\mathcal{B}):\mathsf{St}$$
where on the left we have the $2$-category of pseudo-functors, pseudo-transformations, and modifications, while on the right we have Grothendieck fibrations over $\mathcal{B}$, morphisms of fibered categories over $\mathcal{B}$, and natural transformations over $\mathcal{B}$ of such morphisms. Further, we can upgrade this to a $\mathscr{F}$-equivalence using [[Characterizing Structured Fibrations using F-Categories#^4411ff]]:
$$\int_\mathcal{B}:\mathbb{F}\mathsf{un}_{p}^p((\mathcal{B}^{op})^+,\mathsf{Poset}^+)\leftrightarrows \mathbb{F}\mathsf{ibPos}_{p}(\mathcal{B}^+):\mathbb{S}\mathsf{t}$$
and
$$
\int_\mathcal{B}:\mathbb{F}\mathsf{un}_{p}^p(\mathcal{B}^+,\mathsf{Poset}^+)\leftrightarrows \mathbb{O}\mathsf{pfibPos}_{p}(\mathcal{B}^+):\mathbb{S}\mathsf{t}$$

^1c26ad
where now on the right we are restricting to Cloven (op)fibrations to make sense of tight morphisms. 


By a **Posetal fibration** we will mean a Grothendieck opfibration over $\mathsf{Poset}$, as in the second equivalence above. 

Now, let's try to understand the objects on the right of [[Fibrations as Example of Modules of Systems#^1c26ad]] a bit better. Explicitly, an object on the right fits into a lax comma square
```latexsvg
\documentclass[]{standalone}
\usepackage{mathrsfs}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{tikz-cd}
\begin{document}
\hspace{2cm}
\begin{tikzcd}
	{\mathcal{P}} &&&& {[0]} \\
	\\
	{\mathcal{B}} && {\mathsf{Poset}^{op}} && {\mathsf{Cat}^{op}}
	\arrow[from=1-1, to=1-5]
	\arrow[from=1-1, to=3-1]
	\arrow[""{name=0, anchor=center, inner sep=0}, from=1-5, to=3-5]
	\arrow["X"', from=3-1, to=3-3]
	\arrow[""{name=1, anchor=center, inner sep=0}, hook, from=3-3, to=3-5]
	\arrow[shorten <=7pt, shorten >=7pt, Rightarrow, from=1, to=0]
\end{tikzcd}
\hspace{2cm}
\end{document}
```
so that $\mathcal{P} = X\downdownarrows_\ell [0]$, which by pasting of comma objects is equivalent to the following iteration of a $2$-pullback and a lax comma object,
```latexsvg
\documentclass[]{standalone}
\usepackage{mathrsfs}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{tikz-cd}
\usetikzlibrary{decorations.pathmorphing}
\usetikzlibrary{calc}
\tikzset{curve/.style={settings={#1},to path={(\tikztostart)
	.. controls ($(\tikztostart)!\pv{pos}!(\tikztotarget)!\pv{height}!270:(\tikztotarget)$)
	and ($(\tikztostart)!1-\pv{pos}!(\tikztotarget)!\pv{height}!270:(\tikztotarget)$)
	.. (\tikztotarget)\tikztonodes}},
	settings/.code={\tikzset{quiver/.cd,#1}
		\def\pv##1{\pgfkeysvalueof{/tikz/quiver/##1}}},
	quiver/.cd,pos/.initial=0.35,height/.initial=0}

\tikzset{tail reversed/.code={\pgfsetarrowsstart{tikzcd to}}}
\tikzset{2tail/.code={\pgfsetarrowsstart{Implies[reversed]}}}
\tikzset{2tail reversed/.code={\pgfsetarrowsstart{Implies}}}
\tikzset{no body/.style={/tikz/dash pattern=on 0 off 1mm}}
\begin{document}
\hspace{2cm}
\begin{tikzcd}
	{\mathcal{P}} && {\mathsf{Poset}^{op}_{*,c}} && {[0]} \\
	& {^.\lrcorner} \\
	{\mathcal{B}} && {\mathsf{Poset}^{op}} && {\mathsf{Cat}^{op}}
	\arrow[from=1-1, to=1-3]
	\arrow[from=1-1, to=3-1]
	\arrow[from=1-3, to=1-5]
	\arrow[from=1-3, to=3-3]
	\arrow[""{name=0, anchor=center, inner sep=0}, from=1-5, to=3-5]
	\arrow["X"', from=3-1, to=3-3]
	\arrow[""{name=1, anchor=center, inner sep=0}, hook, from=3-3, to=3-5]
	\arrow[shorten <=7pt, shorten >=7pt, Rightarrow, from=1, to=0]
\end{tikzcd}
\hspace{2cm}
\end{document}
```
or even
```latexsvg
\documentclass[]{standalone}
\usepackage{mathrsfs}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{tikz-cd}
\usetikzlibrary{decorations.pathmorphing}
\usetikzlibrary{calc}
\tikzset{curve/.style={settings={#1},to path={(\tikztostart)
	.. controls ($(\tikztostart)!\pv{pos}!(\tikztotarget)!\pv{height}!270:(\tikztotarget)$)
	and ($(\tikztostart)!1-\pv{pos}!(\tikztotarget)!\pv{height}!270:(\tikztotarget)$)
	.. (\tikztotarget)\tikztonodes}},
	settings/.code={\tikzset{quiver/.cd,#1}
		\def\pv##1{\pgfkeysvalueof{/tikz/quiver/##1}}},
	quiver/.cd,pos/.initial=0.35,height/.initial=0}

\tikzset{tail reversed/.code={\pgfsetarrowsstart{tikzcd to}}}
\tikzset{2tail/.code={\pgfsetarrowsstart{Implies[reversed]}}}
\tikzset{2tail reversed/.code={\pgfsetarrowsstart{Implies}}}
\tikzset{no body/.style={/tikz/dash pattern=on 0 off 1mm}}
\begin{document}
\hspace{2cm}
\begin{tikzcd}
	{\mathcal{P}} && {[0]} && {[0]} \\
	&&& {^.\lrcorner} \\
	{\mathcal{B}} && {\mathsf{Poset}^{op}} && {\mathsf{Cat}^{op}}
	\arrow[from=1-1, to=1-3]
	\arrow[from=1-1, to=3-1]
	\arrow[from=1-3, to=1-5]
	\arrow[""{name=0, anchor=center, inner sep=0}, from=1-3, to=3-3]
	\arrow[from=1-5, to=3-5]
	\arrow[""{name=1, anchor=center, inner sep=0}, "X"', from=3-1, to=3-3]
	\arrow[hook, from=3-3, to=3-5]
	\arrow[shorten <=8pt, shorten >=8pt, Rightarrow, from=1, to=0]
\end{tikzcd}
\hspace{2cm}
\end{document}
```
since $\mathsf{Poset}\hookrightarrow \mathsf{Cat}$ is a fully-faithful embedding containing the terminal category $[0]$. **ADD REF/Proof** 


For the covariant case we get lax comma and $2$-pullback diagrams
```latexsvg
\documentclass[]{standalone}
\usepackage{mathrsfs}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{tikz-cd}
\usetikzlibrary{decorations.pathmorphing}
\usetikzlibrary{calc}
\tikzset{curve/.style={settings={#1},to path={(\tikztostart)
	.. controls ($(\tikztostart)!\pv{pos}!(\tikztotarget)!\pv{height}!270:(\tikztotarget)$)
	and ($(\tikztostart)!1-\pv{pos}!(\tikztotarget)!\pv{height}!270:(\tikztotarget)$)
	.. (\tikztotarget)\tikztonodes}},
	settings/.code={\tikzset{quiver/.cd,#1}
		\def\pv##1{\pgfkeysvalueof{/tikz/quiver/##1}}},
	quiver/.cd,pos/.initial=0.35,height/.initial=0}

\tikzset{tail reversed/.code={\pgfsetarrowsstart{tikzcd to}}}
\tikzset{2tail/.code={\pgfsetarrowsstart{Implies[reversed]}}}
\tikzset{2tail reversed/.code={\pgfsetarrowsstart{Implies}}}
\tikzset{no body/.style={/tikz/dash pattern=on 0 off 1mm}}
\begin{document}
\hspace{2cm}
\begin{tikzcd}
	{\mathcal{P}} &&&& {[0]} \\
	\\
	{\mathcal{B}} && {\mathsf{Poset}} && {\mathsf{Cat}}
	\arrow[from=1-1, to=1-5]
	\arrow[from=1-1, to=3-1]
	\arrow[""{name=0, anchor=center, inner sep=0}, from=1-5, to=3-5]
	\arrow["X"', from=3-1, to=3-3]
	\arrow[""{name=1, anchor=center, inner sep=0}, hook, from=3-3, to=3-5]
	\arrow[shorten <=7pt, shorten >=7pt, Rightarrow, from=0, to=1]
\end{tikzcd}
\hspace{2cm}
\end{document}
```
```latexsvg
\documentclass[]{standalone}
\usepackage{mathrsfs}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{tikz-cd}
\usetikzlibrary{decorations.pathmorphing}
\usetikzlibrary{calc}
\tikzset{curve/.style={settings={#1},to path={(\tikztostart)
	.. controls ($(\tikztostart)!\pv{pos}!(\tikztotarget)!\pv{height}!270:(\tikztotarget)$)
	and ($(\tikztostart)!1-\pv{pos}!(\tikztotarget)!\pv{height}!270:(\tikztotarget)$)
	.. (\tikztotarget)\tikztonodes}},
	settings/.code={\tikzset{quiver/.cd,#1}
		\def\pv##1{\pgfkeysvalueof{/tikz/quiver/##1}}},
	quiver/.cd,pos/.initial=0.35,height/.initial=0}

\tikzset{tail reversed/.code={\pgfsetarrowsstart{tikzcd to}}}
\tikzset{2tail/.code={\pgfsetarrowsstart{Implies[reversed]}}}
\tikzset{2tail reversed/.code={\pgfsetarrowsstart{Implies}}}
\tikzset{no body/.style={/tikz/dash pattern=on 0 off 1mm}}
\begin{document}
\hspace{2cm}
\begin{tikzcd}
	{\mathcal{P}} && {\mathsf{Poset}_{*,\ell}} && {[0]} \\
	& {^.\lrcorner} \\
	{\mathcal{B}} && {\mathsf{Poset}} && {\mathsf{Cat}}
	\arrow[from=1-1, to=1-3]
	\arrow[from=1-1, to=3-1]
	\arrow[from=1-3, to=1-5]
	\arrow[from=1-3, to=3-3]
	\arrow[""{name=0, anchor=center, inner sep=0}, from=1-5, to=3-5]
	\arrow["X"', from=3-1, to=3-3]
	\arrow[""{name=1, anchor=center, inner sep=0}, hook, from=3-3, to=3-5]
	\arrow[shorten <=7pt, shorten >=7pt, Rightarrow, from=0, to=1]
\end{tikzcd}
\hspace{2cm}
\end{document}
```
and
```latexsvg
\documentclass[]{standalone}
\usepackage{mathrsfs}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{tikz-cd}
\usetikzlibrary{decorations.pathmorphing}
\usetikzlibrary{calc}
\tikzset{curve/.style={settings={#1},to path={(\tikztostart)
	.. controls ($(\tikztostart)!\pv{pos}!(\tikztotarget)!\pv{height}!270:(\tikztotarget)$)
	and ($(\tikztostart)!1-\pv{pos}!(\tikztotarget)!\pv{height}!270:(\tikztotarget)$)
	.. (\tikztotarget)\tikztonodes}},
	settings/.code={\tikzset{quiver/.cd,#1}
		\def\pv##1{\pgfkeysvalueof{/tikz/quiver/##1}}},
	quiver/.cd,pos/.initial=0.35,height/.initial=0}

\tikzset{tail reversed/.code={\pgfsetarrowsstart{tikzcd to}}}
\tikzset{2tail/.code={\pgfsetarrowsstart{Implies[reversed]}}}
\tikzset{2tail reversed/.code={\pgfsetarrowsstart{Implies}}}
\tikzset{no body/.style={/tikz/dash pattern=on 0 off 1mm}}
\begin{document}
\hspace{2cm}
\begin{tikzcd}
	{\mathcal{P}} && {[0]} && {[0]} \\
	&&& {^.\lrcorner} \\
	{\mathcal{B}} && {\mathsf{Poset}} && {\mathsf{Cat}}
	\arrow[from=1-1, to=1-3]
	\arrow[from=1-1, to=3-1]
	\arrow[from=1-3, to=1-5]
	\arrow[""{name=0, anchor=center, inner sep=0}, from=1-3, to=3-3]
	\arrow[from=1-5, to=3-5]
	\arrow[""{name=1, anchor=center, inner sep=0}, "X"', from=3-1, to=3-3]
	\arrow[hook, from=3-3, to=3-5]
	\arrow[shorten <=7pt, shorten >=7pt, Rightarrow, from=0, to=1]
\end{tikzcd}
\hspace{2cm}
\end{document}
```
respectively.


Thus, if we use the universal bundles $\mathsf{Poset}_{*,\ell}\to \mathsf{Poset}$ and $\mathsf{Poset}_{*,c}\to \mathsf{Poset}$ we can stay within the purview of $2$-pullbacks, especially since we will be mostly focused on strict $2$-functors, in which case we get split fibrations. In this case we can consider the $2$-category $2\mathsf{Cat}$ of $2$-categories, $2$-functors, and $2$-natural transformations. Then for a $2$-category $\mathcal{K}$, let $2\mathsf{Cat}_{/\mathcal{K}}:=2\mathsf{Cat}^{[1]}\times_{t,2\mathsf{Cat}}\{\mathcal{K}\}$ be the slice $2$-category (which is a lax pullback), and let $\mathsf{Cat}_{/\mathcal{K}}:= \mathsf{Cat}\times_{2\mathsf{Cat},s}2\mathsf{Cat}_{/\mathcal{K}}$. Then if $\mathcal{K}\subseteq 2\mathsf{Cat}$ is a full sub-2-category, the Grothendieck construction gives a strict $2$-equivalence
$$
\int:\mathsf{Cat}_{/\mathcal{K}}\leftrightarrows \mathsf{SplitOpfib}_{\mathcal{K}}:\mathsf{St}$$
where on $1$-cells we have the assignment
```latexsvg
\documentclass[]{standalone}
\usepackage{mathrsfs}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{tikz-cd}
\usetikzlibrary{decorations.pathmorphing}
\usetikzlibrary{calc}
\tikzset{curve/.style={settings={#1},to path={(\tikztostart)
	.. controls ($(\tikztostart)!\pv{pos}!(\tikztotarget)!\pv{height}!270:(\tikztotarget)$)
	and ($(\tikztostart)!1-\pv{pos}!(\tikztotarget)!\pv{height}!270:(\tikztotarget)$)
	.. (\tikztotarget)\tikztonodes}},
	settings/.code={\tikzset{quiver/.cd,#1}
		\def\pv##1{\pgfkeysvalueof{/tikz/quiver/##1}}},
	quiver/.cd,pos/.initial=0.35,height/.initial=0}

\tikzset{tail reversed/.code={\pgfsetarrowsstart{tikzcd to}}}
\tikzset{2tail/.code={\pgfsetarrowsstart{Implies[reversed]}}}
\tikzset{2tail reversed/.code={\pgfsetarrowsstart{Implies}}}
\tikzset{no body/.style={/tikz/dash pattern=on 0 off 1mm}}
\begin{document}
\hspace{2cm}
\begin{tikzcd}
	{\mathcal{C}} &&&& {\int X} && {\int YF} && {\int Y} \\
	&& {\mathcal{K}} & \mapsto &&&& {^.\lrcorner} \\
	{\mathcal{D}} &&&& {\mathcal{C}} && {\mathcal{C}} && {\mathcal{D}}
	\arrow[""{name=0, anchor=center, inner sep=0}, "X", from=1-1, to=2-3]
	\arrow["F"', from=1-1, to=3-1]
	\arrow["{\int\alpha}", from=1-5, to=1-7]
	\arrow[from=1-5, to=3-5]
	\arrow[from=1-7, to=1-9]
	\arrow[from=1-7, to=3-7]
	\arrow[from=1-9, to=3-9]
	\arrow[""{name=1, anchor=center, inner sep=0}, "Y"', from=3-1, to=2-3]
	\arrow[equals, from=3-5, to=3-7]
	\arrow["F"', from=3-7, to=3-9]
	\arrow["\alpha", shorten <=4pt, shorten >=4pt, Rightarrow, from=0, to=1]
\end{tikzcd}
\hspace{2cm}
\end{document}
```
and on $2$-cells we have the assignment
```latexsvg
\documentclass[]{standalone}
\usepackage{mathrsfs}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{tikz-cd}
\usetikzlibrary{decorations.pathmorphing}
\usetikzlibrary{calc}
\tikzset{curve/.style={settings={#1},to path={(\tikztostart)
	.. controls ($(\tikztostart)!\pv{pos}!(\tikztotarget)!\pv{height}!270:(\tikztotarget)$)
	and ($(\tikztostart)!1-\pv{pos}!(\tikztotarget)!\pv{height}!270:(\tikztotarget)$)
	.. (\tikztotarget)\tikztonodes}},
	settings/.code={\tikzset{quiver/.cd,#1}
		\def\pv##1{\pgfkeysvalueof{/tikz/quiver/##1}}},
	quiver/.cd,pos/.initial=0.35,height/.initial=0}

\tikzset{tail reversed/.code={\pgfsetarrowsstart{tikzcd to}}}
\tikzset{2tail/.code={\pgfsetarrowsstart{Implies[reversed]}}}
\tikzset{2tail reversed/.code={\pgfsetarrowsstart{Implies}}}
\tikzset{no body/.style={/tikz/dash pattern=on 0 off 1mm}}
\begin{document}
\hspace{2cm}
\begin{tikzcd}
	&&&&&&&& {\int X} &&& {\int YF} \\
	{\mathcal{C}} &&&& {\mathcal{C}} &&&&&& {\int YG} &&& {\int Y} \\
	&& {\mathcal{K}} & {=} &&& {\mathcal{K}} & \mapsto && {\mathcal{C}} && {\mathcal{C}} \\
	{\mathcal{D}} &&&& {\mathcal{D}} &&&& {\mathcal{C}} && {\mathcal{C}} &&& {\mathcal{D}}
	\arrow["{\int\alpha}", from=1-9, to=1-12]
	\arrow["{\int\beta}"', from=1-9, to=2-11]
	\arrow[from=1-9, to=3-10]
	\arrow[from=1-9, to=4-9]
	\arrow["{\int\Gamma}", shorten <=4pt, shorten >=4pt, Rightarrow, from=1-12, to=2-11]
	\arrow[from=1-12, to=2-14]
	\arrow[dashed, from=1-12, to=3-12]
	\arrow[""{name=0, anchor=center, inner sep=0}, "X", from=2-1, to=3-3]
	\arrow["G"', from=2-1, to=4-1]
	\arrow[""{name=1, anchor=center, inner sep=0}, "X", from=2-5, to=3-7]
	\arrow[""{name=2, anchor=center, inner sep=0}, "F", curve={height=-12pt}, from=2-5, to=4-5]
	\arrow[""{name=3, anchor=center, inner sep=0}, "G"', curve={height=12pt}, from=2-5, to=4-5]
	\arrow[from=2-11, to=2-14]
	\arrow[from=2-11, to=4-11]
	\arrow[from=2-14, to=4-14]
	\arrow[equals, dashed, from=3-10, to=3-12]
	\arrow[equals, from=3-10, to=4-9]
	\arrow[equals, from=3-12, to=4-11]
	\arrow[""{name=4, anchor=center, inner sep=0}, "F", from=3-12, to=4-14]
	\arrow[""{name=5, anchor=center, inner sep=0}, "Y"', from=4-1, to=3-3]
	\arrow[""{name=6, anchor=center, inner sep=0}, "Y"', from=4-5, to=3-7]
	\arrow[equals, from=4-9, to=4-11]
	\arrow[""{name=7, anchor=center, inner sep=0}, "G"', from=4-11, to=4-14]
	\arrow["\beta", shorten <=4pt, shorten >=4pt, Rightarrow, from=0, to=5]
	\arrow["\alpha", shorten <=4pt, shorten >=4pt, Rightarrow, from=1, to=6]
	\arrow["\Gamma", shorten <=5pt, shorten >=5pt, Rightarrow, from=2, to=3]
	\arrow["\Gamma"', shorten <=4pt, shorten >=4pt, Rightarrow, from=4, to=7]
\end{tikzcd}
\hspace{2cm}
\end{document}
```
where $\int \Gamma$ is the natural transformation which at $(C,x) \in \int X$ is given by $(\Gamma_C,\text{id}):(F(C),\alpha_C(x))\to (G(C),\beta_C(x))$. 


Now that we understand our context, let's try and parse out the data of a split $\mathcal{K}$-opfibration a bit more cleanly. Explicitly, a split $\mathcal{K}$-opfibration $p:\mathcal{E}\to \mathcal{B}$ is a Grothendieck opfibration such that for every $b \in \mathcal{B}$, $p^{-1}(b) \in \mathcal{K}$, together with a coherent choice of cocartesian lifts which assemble into functors $f_*:p^{-1}(b)\to p^{-1}(c)$ for all $f:b \to c$ in $\mathcal{B}$ in a way which is functorial, and for which each $e \in p^{-1}(b)$ comes with a map $f^\#:e \to f_*e$ which is universal in the sense that for any other map $g:e\to e'$ with $h:c \to p(e')$ satisfying $hf = p(g)$, there exists a unique map $h':f_*e\to e'$ such that $h'f^\# = g$. In particular, $\mathcal{E}$ has an orthogonal factorization system $(\mathsf{vert},\mathsf{cart})$ which provides a functor
$$(\mathsf{vert},\mathsf{cart}):\mathcal{E}^{[1]}\to \mathsf{vert}\times_{t,\mathcal{E},s}\mathsf{cart}$$
which is a section to the composition map $\circ:\mathsf{vert}\times_{t,\mathcal{E},s}\mathsf{cart}\to \mathcal{E}^{[1]}$, and from [[Basic Fibered Categories#^398caa]] this functor can be constructed so that for each $f:e\to e'$ in $\mathcal{E}$, $\mathsf{vert}(f)$ lies over $\text{id}_{p(e)}$.

>[!observation] Summary of Split $\mathcal{K}$-Opfibration Data
>A $\mathcal{K}$-opfibration is equivalent to an opfibration $p:\mathcal{E}\to \mathcal{B}$ such that for every $b \in \mathcal{B}$, $p^{-1}(b) \in \mathcal{K}$, together with a coherent choice of cocartesian lifts which assemble into functors $f_*:p^{-1}(b)\to p^{-1}(c)$ for all $f:b \to c$ in $\mathcal{B}$ in a way which is functorial in $f$.

Now, the reason for considering posetal fibrations is that we want to understand the resulting model of systems (c.f. [[Towards a Double Operadic Theory of Systems - Scrap Notes#^f6daa2]]) 
$$\mathbb{S}\mathsf{pan}(\mathsf{Cat},(\mathsf{all},\mathsf{posfib}))([0],-)$$
In other words, in this context a system is a posetal fibration $\int X\to \mathcal{C}$ (equivalently $\mathcal{C}\xrightarrow{X}\mathsf{Poset}$) and an interaction is a span $\mathcal{C}\xleftarrow{F}\int Y\xrightarrow{p_Y}\mathcal{D}$ where $F$ is an arbitrary functor and $Y:\mathcal{D}\to \mathsf{Poset}$ is a posetal fibration.

>[!question]
>Do we want the maps in the middle of a map of spans to be maps of posetal fibrations?

When this interaction acts on the system represented by the posetal fibration $\int X\to \mathcal{C}$, we get a new system given by pullback:
```latexsvg
\documentclass[]{standalone}
\usepackage{mathrsfs}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{tikz-cd}
\usetikzlibrary{decorations.pathmorphing}
\usetikzlibrary{calc}
\tikzset{curve/.style={settings={#1},to path={(\tikztostart)
	.. controls ($(\tikztostart)!\pv{pos}!(\tikztotarget)!\pv{height}!270:(\tikztotarget)$)
	and ($(\tikztostart)!1-\pv{pos}!(\tikztotarget)!\pv{height}!270:(\tikztotarget)$)
	.. (\tikztotarget)\tikztonodes}},
	settings/.code={\tikzset{quiver/.cd,#1}
		\def\pv##1{\pgfkeysvalueof{/tikz/quiver/##1}}},
	quiver/.cd,pos/.initial=0.35,height/.initial=0}

\tikzset{tail reversed/.code={\pgfsetarrowsstart{tikzcd to}}}
\tikzset{2tail/.code={\pgfsetarrowsstart{Implies[reversed]}}}
\tikzset{2tail reversed/.code={\pgfsetarrowsstart{Implies}}}
\tikzset{no body/.style={/tikz/dash pattern=on 0 off 1mm}}
\begin{document}
\hspace{2cm}
\begin{tikzcd}
	&&&& {\int_\mathcal{C} X\circ F} \\
	&& {\int_\mathcal{C} X} &&&& {\int_\mathcal{D} Y} \\
	\bullet &&&& {\mathcal{C}} &&&& {\mathcal{D}}
	\arrow[from=1-5, to=2-3]
	\arrow["{p_{F\circ X}}", from=1-5, to=2-7]
	\arrow["\lrcorner"{anchor=center, pos=0.125, rotate=-45}, draw=none, from=1-5, to=3-5]
	\arrow[from=2-3, to=3-1]
	\arrow["{p_X}"', from=2-3, to=3-5]
	\arrow["F", from=2-7, to=3-5]
	\arrow["{p_Y}"', from=2-7, to=3-9]
\end{tikzcd}
\hspace{2cm}
\end{document}
```
In order to ensure this is well-defined we need that the composite $p_Y\circ p_{F\circ X}$ is still a posetal fibration (it is always a cocartesian fibration by [[Basic Fibered Categories#^49d4b3]]). Let $Y\odot XF:\mathcal{D}\to \mathsf{Cat}$ denote that functor classified by the cocartesian fibration. From [[Characterizing Structured Fibrations using F-Categories#^aee298]] we have that on objects this functor is given by
$$Y\odot XF(d) = \text{colim}^c\,XF\vert_{p_Y^{-1}(d)}$$
where the colax colimit on the right is computed in $\mathsf{Cat}$. We will compute this functor in two ways
1. We will show directly that $Y\odot XF(d)$ is a poset
2. We will compute the colax colimit directly and show it lives in $\mathsf{Poset}$

**Approach 1:** First, note that $Y\odot XF(d)$ has object set equal to $\coprod_{x \in p_Y^{-1}(d)}p_{XF}^{-1}(x)$. Then if $x \in p_Y^{-1}(d)$, $y,z \in p^{-1}_{XF}(x)$, then the collection of maps from $y$ to $z$ is either empty, or a singleton if $y \leq z$ in $p^{-1}_{XF}(x)$. If $x,y \in p^{-1}_Y(d)$, $a \in p^{-1}_{XF}(x)$ and $b \in p^{-1}_{XF}(y)$, then the hom-set from $a$ to $b$ is non-empty if and only if $x \leq y$ and there exists a cocartesian lift of $x$ at $a$ with codomain $\leq b$. By [[Basic Fibered Categories#^9bd130]] and the fact that hom sets within a fiber are poset enriched, at most one such cocartesian lift exists, and hence it follows that $Y\odot XF(d)$ is indeed a poset, with elements pairs $(x \in p_Y^{-1}(d),a \in p_{XF}^{-1}(x))$, and with $(x,a) \leq (y,b)$ if and only if $x \leq y$ in $Y(d)$ and $XF(x \leq y)(a) \leq b$ in $XF(y)$.

If in addition $Y$ and $X$ factor through the subcategory of complete lattices and complete lattice maps, then for a family $\{(x_a,w_a)\}_{a \in A}$ in $Y\odot XF(d)$, we can form the meet $\bigwedge_{a \in A}x_a$. Then take $S = \{u \in XF(\bigwedge_{a \in A}x_a)\mid XF(\bigwedge_{a \in A}x_a \leq x_b)(u) \leq w_b,\forall b\in A\}$ to consist of those elements which are less than or equal to all the $w_b$ after pushing forward. Then $S$ at least contains the bot element, and we can consider the pair $(\bigwedge_{a \in A}x_a,\bigvee S) \in Y\odot XF(d)$. Then $(\bigwedge_{a \in A}x_a,\bigvee S) \leq (x_b,w_b)$ for all $b \in B$, by construction, and if $(y,u)$ is another pair with this property, then $y \leq \bigwedge_{a \in A}x_a$, and so $XF(y \leq \bigwedge_{a \in A}x_a)(u)$ is in $S$, implying $XF(y \leq \bigwedge_{a \in A}x_a)(u) \leq \bigvee S$, and hence $(y,u) \leq (\bigwedge_{a\in A}x_a,\bigvee S)$. Dually, the meet of this family is **TBC**


Similarly, if $Y$ and $X$ factor through the subcategory of lattices and lattice maps, then for a pair $(x,a)$ and $(y,b)$ in $Y\odot XF(d)$, we can form the meet $x\wedge y$. Let $a' = XF(x \leq x\lor y)(a)$ and $b' = XF(y \leq x\lor y)(b)$ and form $c = a'\wedge b'$. Consider the set $S = \{u \in XF(x\wedge y)\mid XF(x\wedge y\leq x\lor y)(u) \leq c\}$. Let $U(S)$ denote the complete lattice of upper sets in $S$. If $U(S)$ has a finite set as an element, then $S$ has a join in $XF(x\wedge y)$. 

>[!question]
>Do this always hold?




**Approach 2:** Recall that for a $2$-functor $H:\mathcal{A}\to \mathcal{B}$ between strict $2$-categories, the colax colimit of $H$ is equivalent to the $C:\mathcal{A}^{op}\to \mathsf{Cat}$ weighted colimit of $H$, where $C$ sends an object $a$ to the category $\mathcal{A}(a,-)$ whose objects are $1$-cells $a\to b$, and whose morphisms are triangular cells
```latexsvg
\documentclass[]{standalone}
\usepackage{mathrsfs}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{tikz-cd}
\usetikzlibrary{decorations.pathmorphing}
\usetikzlibrary{calc}
\tikzset{curve/.style={settings={#1},to path={(\tikztostart)
	.. controls ($(\tikztostart)!\pv{pos}!(\tikztotarget)!\pv{height}!270:(\tikztotarget)$)
	and ($(\tikztostart)!1-\pv{pos}!(\tikztotarget)!\pv{height}!270:(\tikztotarget)$)
	.. (\tikztotarget)\tikztonodes}},
	settings/.code={\tikzset{quiver/.cd,#1}
		\def\pv##1{\pgfkeysvalueof{/tikz/quiver/##1}}},
	quiver/.cd,pos/.initial=0.35,height/.initial=0}

\tikzset{tail reversed/.code={\pgfsetarrowsstart{tikzcd to}}}
\tikzset{2tail/.code={\pgfsetarrowsstart{Implies[reversed]}}}
\tikzset{2tail reversed/.code={\pgfsetarrowsstart{Implies}}}
\tikzset{no body/.style={/tikz/dash pattern=on 0 off 1mm}}
\begin{document}
\hspace{2cm}
\begin{tikzcd}
	& a \\
	b && c
	\arrow["f"', from=1-2, to=2-1]
	\arrow[""{name=0, anchor=center, inner sep=0}, "g", from=1-2, to=2-3]
	\arrow[""{name=1, anchor=center, inner sep=0}, "h"', from=2-1, to=2-3]
	\arrow["\alpha", shorten <=4pt, shorten >=4pt, Rightarrow, from=1, to=0]
\end{tikzcd}
\hspace{2cm}
\end{document}
```
Then we have that
$$
\text{colim}^c\,XF\vert_{p_Y^{-1}(d)}\cong p^{-1}_Y(d)_{-/}*_{p^{-1}_Y(d)}\,XF\vert_{p^{-1}_Y(d)}
$$
so that 
$$
\begin{align}
Y\odot XF(d) &= \int^{(d,x):p^{-1}_Y(d)}p^{-1}_Y(d)_{(d,x)/}\times XF(d,x) \\ \\
&\cong \text{coeq}\left(\coprod_{(d,x)\leq(d,y)\in p^{-1}_Y(d)}(p^{-1}_Y(d)_{(d,y)/}\times XF(d,x))\rightrightarrows \coprod_{(d,x)}(p^{-1}_Y(d)_{(d,x)/}\times XF(d,x))\right)
\end{align}
$$
Since $p_Y^{-1}(d)$ is a poset, so is $p^{-1}_Y(d)_{(d,x)/}$, and in fact this is just the sub-upper closed poset of $p^{-1}_Y(d)$ generated by $(d,x)$. Then $p^{-1}_Y(d)_{(d,x)/}\times XF(d,x)$ is just the product poset, viewed as a category. Then the coequalizer tells us that if $x \leq y \leq z$ is in $p^{-1}_Y(d)$, and if $w \in XF(d,x)$, then we identify $(z,w)\sim (z,XF(d,x\leq y)(w))$, so in particular we identify $(z,w)\sim (z,XF(d,x\leq z)(w))$.


Thus, we get an equivalence relation on the objects of $\coprod_{(d,x)}(p^{-1}_Y(d)_{(d,x)/}\times XF(d,x))$, where $(x,(y,w))\sim (a,(b,t))$ if and only if $y=b$, and there exists a zig-zag of inequalities
```latexsvg
\documentclass[]{standalone}
\usepackage{mathrsfs}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{tikz-cd}
\usetikzlibrary{decorations.pathmorphing}
\usetikzlibrary{calc}
\tikzset{curve/.style={settings={#1},to path={(\tikztostart)
	.. controls ($(\tikztostart)!\pv{pos}!(\tikztotarget)!\pv{height}!270:(\tikztotarget)$)
	and ($(\tikztostart)!1-\pv{pos}!(\tikztotarget)!\pv{height}!270:(\tikztotarget)$)
	.. (\tikztotarget)\tikztonodes}},
	settings/.code={\tikzset{quiver/.cd,#1}
		\def\pv##1{\pgfkeysvalueof{/tikz/quiver/##1}}},
	quiver/.cd,pos/.initial=0.35,height/.initial=0}

\tikzset{tail reversed/.code={\pgfsetarrowsstart{tikzcd to}}}
\tikzset{2tail/.code={\pgfsetarrowsstart{Implies[reversed]}}}
\tikzset{2tail reversed/.code={\pgfsetarrowsstart{Implies}}}
\tikzset{no body/.style={/tikz/dash pattern=on 0 off 1mm}}
\begin{document}
\hspace{2cm}
\begin{tikzcd}
	x && {x_1} && {x_{2n-1}} && y \\
	& {x_0} && \cdots && {x_{2n}}
	\arrow["\leq"{marking, allow upside down}, draw=none, from=2-2, to=1-1]
	\arrow["\leq"{marking, allow upside down}, draw=none, from=2-2, to=1-3]
	\arrow["\leq"{marking, allow upside down}, draw=none, from=2-4, to=1-3]
	\arrow["\leq"{marking, allow upside down}, draw=none, from=2-4, to=1-5]
	\arrow["\leq"{marking, allow upside down}, draw=none, from=2-6, to=1-5]
	\arrow["\leq"{marking, allow upside down}, draw=none, from=2-6, to=1-7]
\end{tikzcd}
\hspace{2cm}
\end{document}
```
together with $u_i \in XF(d,x_{2i})$, $0 \leq i \leq n$, such that $x_i \leq y$ for  all $i$, $XF(x_0\leq x)(u_0) = w$, $XF(x_{2n}\leq y)(u_n) = t$, and for each $0 \leq i \leq n-1$, $XF(x_{2i}\leq x_{2i+1})(u_i) = XF(x_{2i+2}\leq x_{2i+1})(u_{i+1})$. 


We can extend these relations to a generalized congruence on $\coprod_{(d,x)}(p^{-1}_Y(d)_{(d,x)/}\times XF(d,x))$, where a pair of maps $((x,(y,w)) \leq (x,(y',w'))),((a,(b,t))\leq (a,(b',t')))$ is composable if and only if $(x,(y',w'))\sim (a,(b,t))$, so in particular $y' = b$ is necessary.


It follows that $Y\odot XF(d)$ has objects given by pairs $(z,w)$ for $z \in Y(d)$ and $w \in XF(d,z)$, with
$$Y\odot XF(d)((z,w),(z',w'))$$
non-empty if and only if $z \leq z'$ and $w' = XF(z \leq z')(w'')$ for some $w'' \in XF(d,z)$, with 

>[!example] Complete Lattice Case
>If in the above discussion $p^{-1}_Y(d)$ is a complete lattice and $XF:p^{-1}_Y(d)\to \mathsf{Poset}$ preserves pullbacks, then $(x,(y,w))\sim (a,(b,t))$ if and only if $y=b$ and there exists $u \in XF(x\wedge a)$ such that $XF(x\wedge a \leq x)(u) = w$ and $X(x\wedge a\leq a)(u) = t$.

>[!example] Injective Poset Map Case
>Suppose that in the above example $X(f):X(a)\to X(b)$ is injective for all $a,b \in \mathcal{C}$. 


### 2.1. (op)Lattice Fibrations via Structured Grothendieck Constructions

An alternative approach to (op)lattice fibrations can be given using the theory of structure Grothendieck constructions, and specifically the $\mathscr{F}$-equivalences in [[Characterizing Structured Fibrations using F-Categories#^b6354f]], where we take $\mathcal{A} = \mathcal{A}_{ex}$ to be the $\mathscr{F}$-sketch associated to finitely complete and cocomplete objects (**REF**), and we take $\mathcal{K} = \mathsf{Poset}$, so that
$$
\mathbb{F}\mathsf{un}_p(\mathbb{B}^{op},\mathsf{Lat}^+)\simeq \mathbb{S}\mathsf{pFib}^{\mathsf{ex}}_p(\mathbb{B};\mathsf{Pos})\;\;\text{ and }\;\;\mathbb{F}\mathsf{un}_p(\mathbb{B},\mathsf{Lat}^+)\simeq \mathbb{S}\mathsf{pOpfib}^{\mathsf{ex}}_p(\mathbb{B};\mathsf{Pos})
$$
we get characterizations of lattice fibrations as finitely complete and cocomplete posetal fibration **EXPAND ON THIS**.



### 2.2. Span Construction using Comma Objects

In this section we aim to expand the span construction of an adequate triple in [[Towards a Double Operadic Theory of Systems - Scrap Notes#^ce4e37]] to a span construction for certain $2$-categories admitting comma objects. We start by defining an analogue of adequate triples in this context:


>[!def] Adequate Comma Triple
>An **adequate comma triple** $(\mathcal{C},(L,R))$ consists of a $2$-category $\mathcal{C}$ together with two wide subcategories $L$ and $R$ (thought of as classes of maps) such that for any cospan $x\xrightarrow{r \in R}z\xleftarrow{\ell \in L}y$, the comma square below exists,
>```latexsvg
> \documentclass[]{standalone}
> \usepackage{mathrsfs}
> \usepackage{amssymb}
> \usepackage{amsmath}
> \usepackage{tikz-cd}
> \usetikzlibrary{decorations.pathmorphing}
> \usetikzlibrary{calc}
> \tikzset{curve/.style={settings={#1},to path={(\tikztostart)
> 	 .. controls ($(\tikztostart)!\pv{pos}!(\tikztotarget)!\pv{height}!270:(\tikztotarget)$)
> 	 and ($(\tikztostart)!1-\pv{pos}!(\tikztotarget)!\pv{height}!270:(\tikztotarget)$)
> 	 .. (\tikztotarget)\tikztonodes}},
> 	 settings/.code={\tikzset{quiver/.cd,#1}
> 	 	 \def\pv##1{\pgfkeysvalueof{/tikz/quiver/##1}}},
> 	 quiver/.cd,pos/.initial=0.35,height/.initial=0}
> \tikzset{tail reversed/.code={\pgfsetarrowsstart{tikzcd to}}}
> \tikzset{2tail/.code={\pgfsetarrowsstart{Implies[reversed]}}}
> \tikzset{2tail reversed/.code={\pgfsetarrowsstart{Implies}}}
> \tikzset{no body/.style={/tikz/dash pattern=on 0 off 1mm}}
> \begin{document}
> \hspace{2cm}
> \begin{tikzcd}
> 	{\ell \downarrow r} && y \\
> 	\\
> 	x && z
> 	\arrow["{r' \in R}", dashed, from=1-1, to=1-3]
> 	\arrow["{\ell' \in L}"', dashed, from=1-1, to=3-1]
> 	\arrow[""{name=0, anchor=center, inner sep=0}, "{\ell \in L}", from=1-3, to=3-3]
> 	\arrow[""{name=1, anchor=center, inner sep=0}, "{r \in R}"', from=3-1, to=3-3]
> 	\arrow[shorten <=7pt, shorten >=7pt, Rightarrow, from=0, to=1]
> \end{tikzcd}
> \hspace{2cm}
> \end{document}
> ```
> and the arrow $r'$ is in $R$ and $\ell'$ is in $L$ for all such comma squares. We will call these comma squares *$L$-$R$ comma objects*.

We have a $2$-category $\mathcal{A}\mathsf{dCTr}$ of adequate comma triples, $2$-functors preserving $L$, $R$, and $L$-$R$ comma objects, and arbitrary $2$-natural transformations.

We now would like to define a span construction on $\mathcal{A}\mathsf{dCTr}$. On an adequate comma triple $(\mathcal{C},L,R)$ we want $\mathbb{S}\mathsf{pan}(\mathcal{C},(L,R))$ to have as objects the objects of $\mathcal{C}$, tight category $\mathcal{C}_0$ the underlying category of $\mathcal{C}$, loose morphisms spans in $\mathcal{C}$ of the form $a\xleftarrow{\ell \in L}c\xrightarrow{r \in R}b$, and squares maps of spans. To define the composite of two spans we take comma objects:
```latexsvg
\documentclass[]{standalone}
\usepackage{mathrsfs}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{tikz-cd}
\usetikzlibrary{decorations.pathmorphing}
\usetikzlibrary{calc}
\tikzset{curve/.style={settings={#1},to path={(\tikztostart)
	.. controls ($(\tikztostart)!\pv{pos}!(\tikztotarget)!\pv{height}!270:(\tikztotarget)$)
	and ($(\tikztostart)!1-\pv{pos}!(\tikztotarget)!\pv{height}!270:(\tikztotarget)$)
	.. (\tikztotarget)\tikztonodes}},
	settings/.code={\tikzset{quiver/.cd,#1}
		\def\pv##1{\pgfkeysvalueof{/tikz/quiver/##1}}},
	quiver/.cd,pos/.initial=0.35,height/.initial=0}

\tikzset{tail reversed/.code={\pgfsetarrowsstart{tikzcd to}}}
\tikzset{2tail/.code={\pgfsetarrowsstart{Implies[reversed]}}}
\tikzset{2tail reversed/.code={\pgfsetarrowsstart{Implies}}}
\tikzset{no body/.style={/tikz/dash pattern=on 0 off 1mm}}
\begin{document}
\hspace{2cm}
\begin{tikzcd}
	&&&& {\ell'\downarrow r} \\
	&& b &&&& d \\
	a &&&& c &&&& e
	\arrow["{\ell'' \in L}"', from=1-5, to=2-3]
	\arrow["{r'' \in R}", from=1-5, to=2-7]
	\arrow["{\ell \in L}"', from=2-3, to=3-1]
	\arrow[""{name=0, anchor=center, inner sep=0}, "{r\in R}"', from=2-3, to=3-5]
	\arrow[""{name=1, anchor=center, inner sep=0}, "{\ell' \in L}", from=2-7, to=3-5]
	\arrow["{r' \in R}"', from=2-7, to=3-9]
	\arrow[shorten <=13pt, shorten >=13pt, Rightarrow, from=1, to=0]
\end{tikzcd}
\hspace{2cm}
\end{document}
```
If we have two spans, we can either form the composite on the top, or the composite on the bottom in . These are isomorphic due to the fact that [[Fibrations in 2-Categories#^40f417]] implies they are uniquely isomorphic to the diagram in the middle
```latexsvg
\documentclass[]{standalone}
\usepackage{mathrsfs}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{tikz-cd}
\usetikzlibrary{decorations.pathmorphing}
\usetikzlibrary{calc}
\tikzset{curve/.style={settings={#1},to path={(\tikztostart)
	.. controls ($(\tikztostart)!\pv{pos}!(\tikztotarget)!\pv{height}!270:(\tikztotarget)$)
	and ($(\tikztostart)!1-\pv{pos}!(\tikztotarget)!\pv{height}!270:(\tikztotarget)$)
	.. (\tikztotarget)\tikztonodes}},
	settings/.code={\tikzset{quiver/.cd,#1}
		\def\pv##1{\pgfkeysvalueof{/tikz/quiver/##1}}},
	quiver/.cd,pos/.initial=0.35,height/.initial=0}

\tikzset{tail reversed/.code={\pgfsetarrowsstart{tikzcd to}}}
\tikzset{2tail/.code={\pgfsetarrowsstart{Implies[reversed]}}}
\tikzset{2tail reversed/.code={\pgfsetarrowsstart{Implies}}}
\tikzset{no body/.style={/tikz/dash pattern=on 0 off 1mm}}
\begin{document}
\hspace{2cm}
\begin{tikzcd}
	&&&&&& {h\downarrow r'r''} \\
	&&&& {\ell'\downarrow r} \\
	&& b &&&& d &&&& x \\
	a &&&& c &&&& e &&&& y \\
	&&&&&& {\ell'\downarrow r\times_dh\downarrow r'} \\
	&&&& {\ell'\downarrow r} &&&& {h\downarrow r'} \\
	&& b &&&& d &&&& x \\
	a &&&& c &&&& e &&&& y \\
	&&&&&& {h'\ell'\downarrow r} \\
	&&&&&&&& {h\downarrow r'} \\
	&& b &&&& d &&&& x \\
	a &&&& c &&&& e &&&& y
	\arrow[from=1-7, to=2-5]
	\arrow[from=1-7, to=3-11]
	\arrow["{\ell'' \in L}"', from=2-5, to=3-3]
	\arrow["{r'' \in R}", from=2-5, to=3-7]
	\arrow["{\ell \in L}"', from=3-3, to=4-1]
	\arrow[""{name=0, anchor=center, inner sep=0}, "{r\in R}"', from=3-3, to=4-5]
	\arrow[""{name=1, anchor=center, inner sep=0}, "{\ell' \in L}", from=3-7, to=4-5]
	\arrow[""{name=2, anchor=center, inner sep=0}, "{r' \in R}"', from=3-7, to=4-9]
	\arrow["\cong"{marking, allow upside down, pos=0.6}, draw=none, from=3-7, to=5-7]
	\arrow[""{name=3, anchor=center, inner sep=0}, "{h \in L}", from=3-11, to=4-9]
	\arrow["{g \in R}", from=3-11, to=4-13]
	\arrow["{h'' \in L}"', from=5-7, to=6-5]
	\arrow["{r''' \in R}", from=5-7, to=6-9]
	\arrow["\lrcorner"{anchor=center, pos=0.125, rotate=-45}, draw=none, from=5-7, to=7-7]
	\arrow["{\ell'' \in L}"', from=6-5, to=7-3]
	\arrow["{r'' \in R}", from=6-5, to=7-7]
	\arrow["{h' \in L}"', from=6-9, to=7-7]
	\arrow["{\widetilde{r'}\in R}", from=6-9, to=7-11]
	\arrow["{\ell \in L}"', from=7-3, to=8-1]
	\arrow[""{name=4, anchor=center, inner sep=0}, "{r\in R}"', from=7-3, to=8-5]
	\arrow[""{name=5, anchor=center, inner sep=0}, "{\ell' \in L}", from=7-7, to=8-5]
	\arrow[""{name=6, anchor=center, inner sep=0}, "{r' \in R}"', from=7-7, to=8-9]
	\arrow["\cong"{marking, allow upside down, pos=0.6}, draw=none, from=7-7, to=9-7]
	\arrow[""{name=7, anchor=center, inner sep=0}, "{h \in L}", from=7-11, to=8-9]
	\arrow["{g \in R}", from=7-11, to=8-13]
	\arrow[from=9-7, to=10-9]
	\arrow[from=9-7, to=11-3]
	\arrow["{h' \in L}"', from=10-9, to=11-7]
	\arrow["{\widetilde{r'} \in R}", from=10-9, to=11-11]
	\arrow["{\ell \in L}"', from=11-3, to=12-1]
	\arrow[""{name=8, anchor=center, inner sep=0}, "{r\in R}"', from=11-3, to=12-5]
	\arrow[""{name=9, anchor=center, inner sep=0}, "{\ell' \in L}", from=11-7, to=12-5]
	\arrow[""{name=10, anchor=center, inner sep=0}, "{r' \in R}"', from=11-7, to=12-9]
	\arrow[""{name=11, anchor=center, inner sep=0}, "{h \in L}", from=11-11, to=12-9]
	\arrow["{g \in R}", from=11-11, to=12-13]
	\arrow[shorten <=15pt, shorten >=15pt, Rightarrow, from=1, to=0]
	\arrow[shorten <=15pt, shorten >=15pt, Rightarrow, from=3, to=2]
	\arrow[shorten <=15pt, shorten >=15pt, Rightarrow, from=5, to=4]
	\arrow[shorten <=15pt, shorten >=15pt, Rightarrow, from=7, to=6]
	\arrow[shorten <=15pt, shorten >=15pt, Rightarrow, from=9, to=8]
	\arrow[shorten <=15pt, shorten >=15pt, Rightarrow, from=11, to=10]
\end{tikzcd}
\hspace{2cm}
\end{document}
```
Thus, this defines a loose composition that is associative up to natural isomorphism **ADD DETAILS ABOUT ASSOCIATIVITY USING COHERENCE FOR BICATEGORIES**. On maps of spans the composition induces a unique new map of spans
```latexsvg
\documentclass[]{standalone}
\usepackage{mathrsfs}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{tikz-cd}
\usetikzlibrary{decorations.pathmorphing}
\usetikzlibrary{calc}
\tikzset{curve/.style={settings={#1},to path={(\tikztostart)
	.. controls ($(\tikztostart)!\pv{pos}!(\tikztotarget)!\pv{height}!270:(\tikztotarget)$)
	and ($(\tikztostart)!1-\pv{pos}!(\tikztotarget)!\pv{height}!270:(\tikztotarget)$)
	.. (\tikztotarget)\tikztonodes}},
	settings/.code={\tikzset{quiver/.cd,#1}
		\def\pv##1{\pgfkeysvalueof{/tikz/quiver/##1}}},
	quiver/.cd,pos/.initial=0.35,height/.initial=0}

\tikzset{tail reversed/.code={\pgfsetarrowsstart{tikzcd to}}}
\tikzset{2tail/.code={\pgfsetarrowsstart{Implies[reversed]}}}
\tikzset{2tail reversed/.code={\pgfsetarrowsstart{Implies}}}
\tikzset{no body/.style={/tikz/dash pattern=on 0 off 1mm}}
\begin{document}
\hspace{2cm}
\begin{tikzcd}
	&&&&&& {h\downarrow r} \\
	&&&& b &&&& d \\
	&& a && {h'\downarrow r'} && c &&&& e \\
	&& {b'} &&&& {d'} \\
	{a'} &&&& {c'} &&&& {e'}
	\arrow[from=1-7, to=2-5]
	\arrow[from=1-7, to=2-9]
	\arrow[from=1-7, to=3-5]
	\arrow["\ell"', from=2-5, to=3-3]
	\arrow[""{name=0, anchor=center, inner sep=0}, "r", dashed, from=2-5, to=3-7]
	\arrow["\beta"{description}, from=2-5, to=4-3]
	\arrow[""{name=1, anchor=center, inner sep=0}, "h"', from=2-9, to=3-7]
	\arrow["k", from=2-9, to=3-11]
	\arrow["\delta"{description}, from=2-9, to=4-7]
	\arrow["\alpha"', from=3-3, to=5-1]
	\arrow[from=3-5, to=4-3]
	\arrow[from=3-5, to=4-7]
	\arrow["\gamma"{description, pos=0.4}, dashed, from=3-7, to=5-5]
	\arrow["\epsilon", from=3-11, to=5-9]
	\arrow["{\ell'}"', from=4-3, to=5-1]
	\arrow[""{name=2, anchor=center, inner sep=0}, "{r'}", from=4-3, to=5-5]
	\arrow[""{name=3, anchor=center, inner sep=0}, "{h'}"', from=4-7, to=5-5]
	\arrow["{k'}", from=4-7, to=5-9]
	\arrow[shorten <=13pt, shorten >=13pt, Rightarrow, from=1, to=0]
	\arrow[shorten <=13pt, shorten >=13pt, Rightarrow, from=3, to=2]
\end{tikzcd}
\hspace{2cm}
\end{document}
```
where the unique map on top is induced by the universal property of the comma object $h'\downarrow r'$ applied to the diagram
```latexsvg
\documentclass[]{standalone}
\usepackage{mathrsfs}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{tikz-cd}
\usetikzlibrary{decorations.pathmorphing}
\usetikzlibrary{calc}
\tikzset{curve/.style={settings={#1},to path={(\tikztostart)
	.. controls ($(\tikztostart)!\pv{pos}!(\tikztotarget)!\pv{height}!270:(\tikztotarget)$)
	and ($(\tikztostart)!1-\pv{pos}!(\tikztotarget)!\pv{height}!270:(\tikztotarget)$)
	.. (\tikztotarget)\tikztonodes}},
	settings/.code={\tikzset{quiver/.cd,#1}
		\def\pv##1{\pgfkeysvalueof{/tikz/quiver/##1}}},
	quiver/.cd,pos/.initial=0.35,height/.initial=0}

\tikzset{tail reversed/.code={\pgfsetarrowsstart{tikzcd to}}}
\tikzset{2tail/.code={\pgfsetarrowsstart{Implies[reversed]}}}
\tikzset{2tail reversed/.code={\pgfsetarrowsstart{Implies}}}
\tikzset{no body/.style={/tikz/dash pattern=on 0 off 1mm}}
\begin{document}
\hspace{2cm}
\begin{tikzcd}
	&& {h\downarrow r} &&&&&& {h\downarrow r} \\
	b &&&& d \\
	&& c &&& {=} &&& {h'\downarrow r'} \\
	{b'} &&&& {d'} && {b'} &&&& {d'} \\
	&& {c'} &&&&&& c
	\arrow[from=1-3, to=2-1]
	\arrow[from=1-3, to=2-5]
	\arrow["{\delta\downarrow_\gamma\beta}", from=1-9, to=3-9]
	\arrow[""{name=0, anchor=center, inner sep=0}, "r", from=2-1, to=3-3]
	\arrow["\beta"', from=2-1, to=4-1]
	\arrow[""{name=1, anchor=center, inner sep=0}, "h"', from=2-5, to=3-3]
	\arrow["\delta", from=2-5, to=4-5]
	\arrow["\gamma"{description, pos=0.4}, from=3-3, to=5-3]
	\arrow[from=3-9, to=4-7]
	\arrow[from=3-9, to=4-11]
	\arrow["{r'}", from=4-1, to=5-3]
	\arrow["{h'}"', from=4-5, to=5-3]
	\arrow[""{name=2, anchor=center, inner sep=0}, "{r'}", from=4-7, to=5-9]
	\arrow[""{name=3, anchor=center, inner sep=0}, "{h'}"', from=4-11, to=5-9]
	\arrow[shorten <=13pt, shorten >=13pt, Rightarrow, from=1, to=0]
	\arrow[shorten <=13pt, shorten >=13pt, Rightarrow, from=3, to=2]
\end{tikzcd}
\hspace{2cm}
\end{document}
```
In general $\mathbb{S}\mathsf{pan}(\mathcal{C},(L,R))$ does not have units for loose composition, so this construction only produces a virtual double category with composites, rather than a pseudo-double category.

>[!claim] Existence of Units
>The virtual double category $\mathbb{S}\mathsf{pan}(\mathcal{C},(L,R))$ has loose units if and only if for all $r \in R$ and $\ell \in L$, the $2$-pullback squares below are comma objects
>```latexsvg
> \documentclass[]{standalone}
> \usepackage{mathrsfs}
> \usepackage{amssymb}
> \usepackage{amsmath}
> \usepackage{tikz-cd}
> \usetikzlibrary{decorations.pathmorphing}
> \usetikzlibrary{calc}
> \tikzset{curve/.style={settings={#1},to path={(\tikztostart)
> 	 .. controls ($(\tikztostart)!\pv{pos}!(\tikztotarget)!\pv{height}!270:(\tikztotarget)$)
> 	 and ($(\tikztostart)!1-\pv{pos}!(\tikztotarget)!\pv{height}!270:(\tikztotarget)$)
> 	 .. (\tikztotarget)\tikztonodes}},
> 	 settings/.code={\tikzset{quiver/.cd,#1}
> 	 	 \def\pv##1{\pgfkeysvalueof{/tikz/quiver/##1}}},
> 	 quiver/.cd,pos/.initial=0.35,height/.initial=0}
> \tikzset{tail reversed/.code={\pgfsetarrowsstart{tikzcd to}}}
> \tikzset{2tail/.code={\pgfsetarrowsstart{Implies[reversed]}}}
> \tikzset{2tail reversed/.code={\pgfsetarrowsstart{Implies}}}
> \tikzset{no body/.style={/tikz/dash pattern=on 0 off 1mm}}
> \begin{document}
> \hspace{2cm}
> \begin{tikzcd}
> 	a && b & {} & c \\
> 	& {^.\lrcorner} && {\llcorner^.} \\
> 	a && b && c
> 	\arrow["r", from=1-1, to=1-3]
> 	\arrow[equals, from=1-1, to=3-1]
> 	\arrow[equals, from=1-3, to=3-3]
> 	\arrow["\ell"', from=1-5, to=1-3]
> 	\arrow[equals, from=1-5, to=3-5]
> 	\arrow["r"', from=3-1, to=3-3]
> 	\arrow["\ell", from=3-5, to=3-3]
> \end{tikzcd}
> \hspace{2cm}
> \end{document}
> ```

`\begin{proof}`
**$\impliedby$:** is immediate by definition of loose composition in $\mathbb{S}\mathsf{pan}(\mathcal{C},(L,R))$.

**$\implies$:** **NOT SUPER SURE YET**
- [ ] **TODO:** prove forward implication.
`\end{proof}`


Note that for $1$-categories viewed as locally discrete $2$-categories, comma objects coincide with pullbacks, so we get a fully-faithful $2$-embedding $\mathcal{A}\mathsf{dTr}\hookrightarrow \mathcal{A}\mathsf{dCTr}$.

>[!theorem] Span construction for adequate comma triples
>There exists a cartesian $2$-functor $\mathbb{S}\mathsf{pan}:\mathcal{A}\mathsf{dCTr}\to v\mathcal{D}\mathsf{bl}_{\mathsf{comp}}$ sending an adequate comma triple $(\mathcal{C},L,R)$ to its span construction $\mathbb{S}\mathsf{pan}(\mathcal{C},(L,R))$, as above. Further, this $2$-functor restricts to the usual span construction $\mathbb{S}\mathsf{pan}:\mathcal{A}\mathsf{dTr}\to \mathcal{D}\mathsf{bl}$ for adequate triples.

`\begin{proof}`
**TBD**
`\end{proof}`






#### 2.2.1. References

[^1]: Berkeley Seminar: Sophie Libkind, Computation in Continuous Dynamics. (2023). https://www.youtube.com/watch?v=RA6F9KWAnUg. Accessed 3 June 2025
