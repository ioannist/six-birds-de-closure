# 7. Is the present epoch typical? Measures over the window

Section 5 showed that the record window bounds the coincidence ratio $R=|\lambda|/\rho_m(a_{\rm rec})$ from above but does
not pin it near unity. Typicality is a further question: it needs a way to weight values of $\lambda$ inside the window.
Neither model of Sections 5 and 6 supplies such a weighting, and Section 6.4 showed that in the ledger-closed model no
translation-invariant one exists. So a measure must be declared. This section declares five, computes what each implies
for $R$, and then proves two general limits on what any argument of this kind can conclude.

## 7.1 The probe

On the record-window model of Section 5, a denser grid places 36 logarithmically spaced positive values of $\lambda$
inside the window, together with a sliver of negative values and $\lambda=0$. For each value and each of the twelve seeds
we record whether the seed passes, its number of distinguishable records $N_{\rm rec}$, its collapsed fraction
$f_{\rm coll}$ [@PressSchechter1974], its first-record epoch $a_{\rm rec}$ and the epoch $a_\lambda$ at which
$\rho_m(a_\lambda)=|\lambda|$. Five measure classes were declared before any verdict was computed:

| class | weight | rationale |
|-----|----------------|---------------------------------------------|
| M1 | flat in $\lambda$ | the linear prior behind the classic typicality argument |
| M2 | flat in $\log\lambda$ | the scale-invariant alternative |
| M3 | flat in $\lambda$, times $N_{\rm rec}$ | each record counted as one observer-analog |
| M4 | flat in $\lambda$, times $f_{\rm coll}$ | a collapsed-fraction weight, as in [@MartelShapiroWeinberg1998] |
| M5 | flat in $\log\lambda$, times $N_{\rm rec}$ | whether record weighting can concentrate a logarithmic prior |

Each grid value receives the mass its class assigns to its cell. That mass is shared equally among the twelve seeds, and
each seed that passes contributes its own value of $R$ with its share multiplied by its own record weight. Quantiles are
taken from the resulting weighted empirical distribution. Logarithmic classes use the declared positive cutoff $10^{-5}$,
and $\lambda=0$ is excluded from distributions of $\log R$. The pre-registered criterion says that a class
*concentrates* $R$ if the probability that $\log_{10}R$ lies within one decade of its largest supported value is at least
$0.8$, and the central 90% interval of $\log_{10}R$ is at most 1.5 decades wide. The expectation recorded in advance was
that linear classes with record weights would concentrate and logarithmic ones would not.

## 7.2 Results

The table and Figure \ref{fig:measure} are floating-point computations on the sampled grid, using numerically integrated
growth histories.

| class | $P(\text{top decade})$ | 90% width of $\log_{10}R$ (decades) | median $a_\lambda/a_{\rm rec}$ | meets criterion |
|------------------|------------|--------------|---------------|-----------|
| M1 flat $\lambda$ | 0.331 | 1.82 | 1.36 | no |
| M2 flat $\log\lambda$ | 0.041 | 4.96 | 8.71 | no |
| M3 $\lambda$, $\times N_{\rm rec}$ | 0.194 | 2.22 | 1.71 | no |
| M4 $\lambda$, $\times f_{\rm coll}$ | 0.194 | 2.22 | 1.71 | no |
| M5 $\log\lambda$, $\times N_{\rm rec}$ | 0.009 | 4.42 | 13.80 | no |

No class meets the criterion, and none does in any of the three declared robustness variants ($N=32$, $N=128$,
$\delta_c=2$); the largest top-decade probability among them is $0.68$, for M1 at $N=128$. Classes M3 and M4 coincide
exactly, because on every passing seed $f_{\rm coll}=N_{\rm rec}/N$ with $N$ fixed, so the two weights are proportional.

Two comparisons survive the negative verdict. Linear classes place the typical first record close to the epoch of
$\lambda$-domination, with median $a_\lambda/a_{\rm rec}$ between $1.36$ and $1.71$, while logarithmic classes place it
an order of magnitude earlier. And record weighting does not help concentration: it *broadens* the linear distribution
(top-decade probability $0.33\to0.19$, width $1.82\to2.22$ decades), because record counts fall as growth is suppressed
at large $\lambda$, and it does not rescue the logarithmic prior. The top decade is measured from the largest supported
seed value of $R$, so it is sensitive to rare seeds; it was not adjusted after the fact. No measure built from the
model's own structure was constructed, so the comparison is among declared classes only.

\begin{figure}[t]
\centering
\includegraphics[width=\textwidth]{F5_measure.pdf}
\caption{\textbf{Declared measures over the record window.} \emph{(a)} Central 90\% interval and median of $\log_{10}R$
for each class in the base run, with the probability of the top decade (shaded). \emph{(b)} Median and 90\% interval of
the epoch ratio $a_\lambda/a_{\rm rec}$ in the base run, with the medians of the three robustness variants. Blue: classes
flat in $\lambda$; orange: classes flat in $\log\lambda$.}
\label{fig:measure}
\end{figure}

## 7.3 What a prior must supply

The computation above uses a frozen grid. Two theorems show that the conclusion does not hinge on the particular classes.

\begin{proposition}[Fixed-support bound]\label{prop:fixedsupport}
On the frozen base grid, with every admitted grid value kept in the support and seeds weighted equally, every prior that
reweights only the grid values gives a top-decade probability of at most $8/11<4/5$; with record weights the bound is
$57/80$. Both bounds are sharp.
\end{proposition}

The bound comes from the fact that, at each grid value, at most eight of the eleven or twelve passing seeds fall in the top
decade, and a reweighting of grid values only mixes these conditional fractions. The algebra is mechanized; the counts
are checked exactly from the frozen data. Changing the support, the seeds, the observable or the model is outside the
statement.

\begin{proposition}[Smooth priors need not concentrate]\label{prop:smoothprior}
For every $\varepsilon>0$ and $\eta\in(0,1)$ there is a smooth, strictly positive, normalized density on the positive part
of the window, of the form $\pi(\lambda)\propto e^{-k\lambda}$, that gives probability greater than $1-\eta$ to admitted
values at which every seed's ratio is below $\varepsilon$. One construction works simultaneously for the 32-, 64- and
128-patch populations and throughout the threshold and amplitude ranges of Section 5.3.
\end{proposition}

This is mechanized for the actual model. A simple numerical instance makes the point: on $[0,1]$ the density
proportional to $e^{-\lambda/0.01}$ is smooth and positive yet gives the interval $[0.1,1]$ a mass of only about
$4.5\times10^{-5}$. Regularity of a prior near $\lambda=0$ therefore says nothing about how much mass it puts near the
upper edge.

Taken together with Section 6.4, these results say what a typicality argument for the coincidence would need: a prior
family specified with quantitative bounds over the whole window, pushed forward through the joint distribution of
records and seeds. Neither smoothness, nor the form of the window, nor record counting supplies it. This is the familiar
crux of anthropic measure arguments [@BoussoPolchinski2000], made precise for a model whose window and first-record
ratio bounds are proved exactly. The paper does not endorse any prior and draws no anthropic conclusion.
