# 4. The constant slot as the price of a global budget

The first question is what *kind* of term the constant slot is. In the closure calculus a global constraint at one level
appears as a price at the level above (Section 2.3). This section makes that precise in three steps: a general theorem
about when a budget carries a positive price, an adequacy residual that can serve as the budgeted quantity, and an
allocation model in which the price shows the features usually attributed to a constant term. The comparison with
holographic min-cut duality is stated at the end.

## 4.1 When a budget has a positive price

Let $\mathcal A$ be a convex subset of a real vector space, $J:\mathcal A\to\mathbb R$ a convex cost and
$e:\mathcal A\to\mathbb R$ a convex budgeted quantity. The optimal cost at budget level $B$ is

$$V(B)=\inf\{\,J(x) : x\in\mathcal A,\ e(x)\le B\,\}.$$

\begin{theorem}[Closure price]\label{thm:price}
Suppose that $x^\star$ attains $V(B)$, that $V$ is finite on a neighborhood of $B$, and that $V$ is differentiable at
$B$ with $V'(B)<0$. Then $p=-V'(B)>0$, the budget binds, $e(x^\star)=B$, and
$$J(x^\star)\;\le\;J(x)+p\,\bigl(e(x)-B\bigr)\qquad\text{for every }x\in\mathcal A .$$
In particular $x^\star$ minimizes the Lagrangian $J+p\,(e-B)$ over all of $\mathcal A$, the primal and dual optimal
values agree, and any other certificate with these properties has the same price.
\end{theorem}

The theorem constructs the price from the value function itself; no Lagrange multiplier, constraint qualification or
convexity of $V$ is assumed. It is mechanized in Lean, together with several variants (Appendix C): objectives taking
the value $+\infty$ outside an effective domain, matrix-valued budgets $E(x)\preceq\mathcal B$ with a positive
semidefinite matrix price, prices obtained from a Slater point without any differentiability of $V$, and a full
stationarity condition split into objective, budget and domain terms under a relative-interior qualification.

Two hypotheses deserve comment. A binding budget alone does not give a positive price: minimizing $x^2$ subject to
$x\le 0$ makes the constraint active at $x=0$, Slater's condition holds, and the multiplier is zero. Strict sensitivity,
$V'(B)<0$, is what forces positivity, and the theorem shows that it also forces the budget to bind. Second, the theorem
fixes the *existence and form* of the price, not its value, which depends on $B$ and on $J$.

## 4.2 An adequacy residual as the budgeted quantity

In the calculus the natural budgeted quantity is the part of one family of descriptions that another family cannot
explain. For whitened finite matrices $L$ (native probes) and $D$ (dissolving probes), let $P_L$ be the orthogonal
projector onto the row space of $L$, built with the Moore–Penrose inverse. The **adequacy residual** is

$$\Xi \;=\; D\,(I-P_L)\,D^{\top}\;\succeq\;0 .$$

\begin{proposition}[Adequacy residual]\label{prop:schur}
For every native rank, including singular $LL^{\top}$:
(i) $\Xi=0$ if and only if $D=AL$ for some matrix $A$, if and only if $\ker L\subseteq\ker D$;
(ii) for every linear explanation $A$,
$(D-AL)(D-AL)^{\top}=\Xi+(A-A_\star)LL^{\top}(A-A_\star)^{\top}$ with $A_\star=DL^{+}$, so $\Xi$ is the
Loewner-smallest residual;
(iii) for fixed $L$ and affine $D(x)$, the map $x\mapsto\Xi$ is Loewner-convex, with derivative
$H(I-P_L)D^{\top}+D(I-P_L)H^{\top}$ in direction $H$.
\end{proposition}

All three parts are mechanized. Part (iii) makes $\operatorname{tr}(W\Xi)$, for a positive semidefinite audit weight
$W$, a convex budgeted quantity to which \Cref{thm:price} applies; the mechanized examples include a complete
Schur-budget instance with its optimizer, value and derivative. If $W$ is only semidefinite, a zero trace need not mean
$\Xi=0$. When the native probes vary as well, convexity can fail, and a mechanized example shows this.

## 4.3 An allocation model

The theorem says when a price exists. To see what the price *does*, consider $N=32$ patches with allocations
$x_i\ge 0$, each with a concave local utility

$$u_i(x_i)=w_i\log(1+x_i)-\tfrac12 c_i x_i^2+b\,x_i,$$

and one global budget $\sum_i x_i\le B$. The weights $w_i$ and curvatures $c_i$ are fixed, deliberately heterogeneous
arrays (Appendix A.1), and $b$ is a common linear offset, zero unless stated otherwise. For every finite family with
$w_i,c_i>0$, every offset and every $B\ge0$, the problem has a unique optimizer, constructed explicitly, with a budget
price $p(B)$ that is unique for $B>0$ and nonincreasing in $B$. Writing the optimal *cost* as
$V(B)=-\max\sum_iu_i(x_i)$, $V$ is continuously differentiable for $B>0$ with $V'(B)=-p(B)$, including where the set of
active patches changes. These statements are
mechanized, and the original 32-patch inputs are reified exactly in Lean. Three properties follow.

**One price over unequal allocations.** At the optimum every patch with $x_i>0$ satisfies $u_i'(x_i)=p$, and every patch
with $x_i=0$ satisfies $u_i'(0)\le p$. In the original inputs at $B\approx22.24$ all allocations are positive and differ
from patch to patch ($0.735,\,0.800,\,0.828,\,0.878,\ldots$), while the price is one number, $0.46112<p<0.46113$. The
heterogeneity is essential: with identical patches the uniformity would be trivial. *Control:* replacing the global
budget by per-patch budgets with the same total gives unequal per-patch prices ($0.494,\,0.548,\,0.568,\ldots$). A single
price comes from the globality of the constraint. It does not mean that the price ignores local detail: changing the
local weights at the same budget changes the price.

**A common offset shifts the price, not the allocation.** Adding the same linear term $b\,x_i$ to every patch adds
$b\sum_i x_i=bB$ to the objective on the binding face of the budget. For an active budget the optimizer is therefore
unchanged and the price becomes $p+b$, provided $p+b\ge0$ so that the budget still binds; for the original inputs this
holds for every $b\in[-\tfrac14,\tfrac14]$. A literal constant added to the objective would change neither the optimizer
nor the price; the linear offset is the analog of a constant energy density times a volume share. In floating point at
$b=\pm0.2$ the allocation moved by at most $5.7\times10^{-14}$ and the price shifted by $b$ to within $3.3\times10^{-14}$.
*Control:* without the global budget the same offset moves the allocation, by $0.56$ to $0.67$ in floating point; the
exact proof certifies a displacement larger than $1/2$ for one patch. The offset is screened only because the budget
binds.

**The price vanishes when the budget is slack.** Across the ten budgets of the sweep, seven bind with positive price and
three are strictly slack with price exactly zero. While the budget binds, the price falls as the budget grows
($0.806,\,0.661,\,0.538,\,0.461,\,0.297,\,0.132,\,0.014$), and it agrees with minus a central finite difference of the
optimal cost to $3.6\times10^{-11}$, the largest discrepancy in the sweep.

\begin{figure}[t]
\centering
\includegraphics[width=\textwidth]{F2_dual.pdf}
\caption{\textbf{The allocation model.} \emph{Left:} marginal utilities of several heterogeneous patches meet one global
price at their optimal allocations (dots); in the per-patch-budget control every patch receives the same allocation but
the prices differ (grey crosses).
\emph{Center:} a common linear offset $b\,x_i$ with $b=\pm0.2$ leaves the allocation unchanged to floating-point
precision when the global budget binds, while the price shifts by $b$; without the budget the same offset moves the
allocation. \emph{Right:} the price from the optimality conditions agrees with minus the finite-difference derivative of the
optimal cost and is zero once the budget is slack. Floating-point outputs; the corresponding exact statements are
proved in Lean.}
\label{fig:dual}
\end{figure}

Together these are the familiar features of a constant term: one value shared by all patches, insensitivity of the state
to a uniform offset, and absence when the constraint is not active. In unimodular gravity the cosmological constant
appears as an integration constant decoupled from vacuum energy [@HenneauxTeitelboim1989], and in vacuum-energy
sequestering a global constraint with a Lagrange multiplier removes the Standard-Model vacuum energy from the
gravitational dynamics [@KaloperPadilla2014]. The allocation model shows the same pattern in a finite, checkable
setting. It does not show that physical vacuum energy decouples.

## 4.4 Comparison with min-cut duality

The Ryu–Takayanagi prescription relates boundary entanglement entropy to a bulk minimal area [@RyuTakayanagi2006], and
in discrete flow formulations max-flow/min-cut is a linear-programming duality [@FreedmanHeadrick2017]. Here we compare
the closure price with a declared finite min-cut model. The precise finite relation is the following.
For capacities $c$, the minimal cut cost $A(c)$ is the optimal value of the dual problem. A minimizing cut supplies a
supergradient of $A$ whose components are its cut-incidence coefficients; where the minimizing cut is unique and stable,
these are the marginal prices of the individual edge capacities, and they are not the area. For a fixed capacity shape
$c_0$ and a common scale $s\ge0$, however, $A(s\,c_0)=s\,A(c_0)$, so the area *is* the marginal price of the common scale
at $s=1$. A slack regime with zero price exists only if a throughput ceiling is added. The finite-minimum, weak-duality,
tight-certificate and common-scale laws are mechanized; on the 14-edge graph used in the Six Birds corpus, the
minimizing cuts, their stability margins and the individual capacity prices are checked in exact rational arithmetic
(254 boundary masks, 8{,}128 cut–flow inequalities). Area and closure
price are therefore both outputs of an optimization duality, but they play different roles: one is an optimal value
under a declared scaling, the other a multiplier. We use the comparison as an analogy only. A proposed rule under which
entanglement entropies compose like cut areas fails on an explicit, normalized two-qubit contraction, whose entropy drops
from $H(3/4)$ to $H(9/10)<H(3/4)$.

## 4.5 Summary

Under the attainment, finiteness, convexity and sensitivity hypotheses of \Cref{thm:price}, a global budget carries one
positive scalar price. For the separable allocation problem with the budget $\sum_ix_i\le B$, that price is shared by every
patch with a positive allocation; for an originally binding budget, a common linear utility term $b\,x_i$ leaves the
optimizer unchanged and changes the price to $p+b$, provided $p+b\ge0$; and the price is zero when the budget is slack. These are statements about optimization problems. Whether the physical cosmological constant is such a
price is a separate question, which would require a map from the budget to a gravitational field equation; it is not
addressed here. The next two sections ask what the models say about the range of admissible values and about the value
itself.
