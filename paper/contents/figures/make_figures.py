#!/usr/bin/env python3
"""Generate the publication figures for the paper.

Quantitative panels are drawn from the result artifacts under results/ and from
data/orbit_traces.csv (written by orbit_traces.py); the overview panel (F1) uses
drawing primitives only. Outputs: F1_overview, F2_dual, F3_window, F4_orbits,
F5_measure, F6_audits as .pdf (vector) and .png (raster).

Deterministic; no observed-cosmology values enter any carrier panel.
"""
from __future__ import annotations

import csv
import json
import math
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch

ROOT = Path(__file__).resolve().parents[3]
RES = ROOT / "results"
OUT = Path(__file__).resolve().parent

# ----------------------------------------------------------------------------
# style
# ----------------------------------------------------------------------------
OKABE = {
    "blue": "#0072B2",
    "orange": "#E69F00",
    "green": "#009E73",
    "red": "#D55E00",
    "purple": "#CC79A7",
    "sky": "#56B4E9",
    "yellow": "#F0E442",
    "black": "#000000",
    "grey": "#888888",
}

plt.rcParams.update(
    {
        "font.family": "serif",
        "font.size": 8.5,
        "mathtext.fontset": "stix",
        "axes.linewidth": 0.8,
        "axes.labelsize": 8.5,
        "axes.titlesize": 9.0,
        "xtick.labelsize": 7.5,
        "ytick.labelsize": 7.5,
        "legend.fontsize": 7.0,
        "legend.frameon": False,
        "figure.dpi": 110,
        "savefig.dpi": 300,
        "pdf.fonttype": 42,
    }
)


def read_csv(path: Path) -> list[dict[str, str]]:
    with open(path, newline="") as fh:
        return list(csv.DictReader(fh))


def f(x: str) -> float:
    return float(x)


def save(fig, name: str) -> None:
    fig.savefig(OUT / f"{name}.pdf")
    fig.savefig(OUT / f"{name}.png", dpi=150)
    plt.close(fig)
    print(f"[ok] {name}")


def panel_label(ax, label: str) -> None:
    ax.text(
        -0.14, 1.06, label, transform=ax.transAxes, fontsize=10,
        fontweight="bold", va="top", ha="left",
    )


def box(ax, x, y, w, h, text, fc="#f2f2f2", ec="0.25", fs=7.5, weight="normal", tc="black"):
    p = FancyBboxPatch(
        (x, y), w, h, boxstyle="round,pad=0.012,rounding_size=0.02",
        linewidth=0.9, edgecolor=ec, facecolor=fc, mutation_aspect=1.0,
    )
    ax.add_patch(p)
    ax.text(x + w / 2, y + h / 2, text, ha="center", va="center", fontsize=fs,
            fontweight=weight, color=tc, linespacing=1.35)
    return p


def arrow(ax, x0, y0, x1, y1, color="0.25", lw=1.1, style="-|>", shrink=2.0, ls="-"):
    a = FancyArrowPatch(
        (x0, y0), (x1, y1), arrowstyle=style, mutation_scale=9,
        linewidth=lw, color=color, shrinkA=shrink, shrinkB=shrink, linestyle=ls,
    )
    ax.add_patch(a)


# ----------------------------------------------------------------------------
# F1 — overview (schematic)
# ----------------------------------------------------------------------------
def fig1() -> None:
    """Overview: the question, what each part of the paper establishes, and what stays open."""
    fig, ax = plt.subplots(figsize=(7.0, 3.2))
    ax.set_xlim(0, 10)
    ax.set_ylim(0.6, 6.15)
    ax.axis("off")

    ax.text(1.05, 5.92, "question", ha="center", fontsize=7.4, color="0.35", style="italic")
    ax.text(4.68, 5.92, "result (declared models and readouts)", ha="center",
            fontsize=7.4, color="0.35", style="italic")
    ax.text(9.15, 5.92, "not established", ha="center", fontsize=7.4, color="0.35", style="italic")

    rows = [
        ("What kind of term\nis the constant slot?",
         "One positive budget price under the hypotheses of §4.1;\na common linear term only shifts it while the budget binds  (§4)",
         "theorem + Lean", "#dbe9f6"),
        ("What fixes its value?",
         "Convergence readouts leave the background undetermined;\nwith a global ledger it becomes a gauge modulus  (§6)",
         "theorem + Lean", "#f6e4db"),
        ("Which values allow\nrecords?",
         "$\\geq$10 of 12 seeds keep records iff $-1/8000<\\lambda\\leq\\lambda_+$,\n$3<\\lambda_+<3.4$; the coincidence ratio is not pinned  (§5)",
         "theorem + Lean", "#dff0e4"),
        ("Is our epoch typical?",
         "Depends on the declared prior: no tested prior meets\nthe criterion; smoothness near zero is not enough  (§7)",
         "computation,\ncounterexample", "#fff3cf"),
        ("What do the data say?",
         "Constant-compatible rewrite; regular density through the\ncrossing; SN–BAO subset dependence flagged  (§8)",
         "pre-registered\naudit", "#efe3f2"),
    ]
    y0, h, gap = 4.72, 0.86, 0.12
    for i, (q, res, kind, fc) in enumerate(rows):
        y = y0 - i * (h + gap)
        box(ax, 0.05, y, 2.0, h, q, fc="#f2f2f2", fs=6.6)
        box(ax, 2.3, y, 4.85, h, res, fc=fc, fs=5.75)
        ax.text(7.24, y + h / 2, kind, ha="left", va="center", fontsize=5.8, color="0.35", style="italic")
        arrow(ax, 2.05, y + h / 2, 2.3, y + h / 2)
    ax.text(7.55, 5.92, "evidence", ha="center", fontsize=7.4, color="0.35", style="italic")
    box(ax, 8.32, 0.0 + y0 - 4 * (h + gap), 1.66, 5 * h + 4 * gap,
        "identifying the price\nwith physical $\\Lambda$\n\na value of $\\Lambda$\n\na physical prior\nover $\\lambda$\n\nghost absence or\nstability of a fluid\n\na causal closure\nmechanism in data",
        fc="white", ec="0.55", fs=6.1, tc="0.25")
    save(fig, "F1_overview")


# ----------------------------------------------------------------------------
# F2 — allocation model
# ----------------------------------------------------------------------------
def fig2() -> None:
    const = read_csv(RES / "DE_dual" / "constancy.csv")
    sweep = read_csv(RES / "DE_dual" / "dual_sweep.csv")
    vac = read_csv(RES / "DE_dual" / "vacuum_shift.csv")
    local = read_csv(RES / "DE_dual" / "controls" / "local_budget_control.csv")

    lam_star = f(const[0]["global_dual"])

    fig, axes = plt.subplots(1, 3, figsize=(7.0, 2.45))
    fig.subplots_adjust(left=0.075, right=0.99, top=0.86, bottom=0.20, wspace=0.42)

    # (a) one price over heterogeneous allocations -------------------------
    ax = axes[0]
    sel = const[:: max(1, len(const) // 7)][:7]
    xs = [i / 200 * 1.8 for i in range(201)]
    for i, row in enumerate(sel):
        w, c = f(row["weight"]), f(row["curvature"])
        ax.plot(xs, [w / (1 + x) - c * x for x in xs], lw=0.9,
                color=plt.cm.viridis(i / max(1, len(sel) - 1)), alpha=0.85)
        ax.plot(f(row["x_star"]), lam_star, "o", ms=3.2, color="black", zorder=5)
    ax.axhline(lam_star, color=OKABE["red"], lw=1.1, ls="--")
    ax.text(1.82, lam_star + 0.05, "one global price $p$",
            color=OKABE["red"], fontsize=6.8, ha="right")
    # local-budget control: per-patch budgets of equal total give equal allocations but unequal prices
    ld = [f(r["local_dual"]) for r in local]
    lx = [f(r["x_star"]) for r in local]
    ax.scatter(lx, ld, s=6, marker="x", color=OKABE["grey"], lw=0.6, zorder=4)
    ax.annotate("per-patch budgets:\nsame allocation,\nunequal prices", xy=(lx[0], max(ld)),
                xytext=(0.95, 1.18), fontsize=6.2, color="0.3",
                arrowprops=dict(arrowstyle="-", lw=0.6, color="0.5"))
    ax.set_xlabel("allocation $x$")
    ax.set_ylabel("marginal utility $u_i'(x)$")
    ax.set_xlim(0, 1.85)
    ax.set_ylim(0.0, 1.45)
    ax.set_title("unequal allocations, one price", fontsize=7.6)
    panel_label(ax, "a")

    # (b) vacuum-shift screening ------------------------------------------
    ax = axes[1]
    bvals, svals, cs = [], [], []
    for r in vac:
        if f(r["offset"]) == 0.0:
            continue
        if r["variant"].startswith("budget_dual"):
            bvals.append(max(f(r["max_abs_x_shift_from_base"]), 1e-16))
            cs.append(f(r["offset"]))
        else:
            svals.append(max(f(r["max_abs_x_shift_from_base"]), 1e-16))
    xpos = [0, 1]
    wd = 0.32
    ax.bar([x - wd / 2 for x in xpos], bvals, wd, color=OKABE["blue"],
           label="global budget")
    ax.bar([x + wd / 2 for x in xpos], svals, wd, color=OKABE["orange"],
           label="no budget (control)")
    ax.set_yscale("log")
    ax.set_ylim(1e-16, 30)
    ax.set_xticks(xpos)
    ax.set_xticklabels([f"$b={c:+.1f}$" for c in cs])
    ax.set_ylabel("allocation shift  $\\max_i|\\Delta x_i|$")
    ax.axhline(1, color="0.8", lw=0.6)
    ax.text(0.5, 3e-13, "allocation unchanged to $5.7\\times10^{-14}$;\n"
            "price shifts by $b$ (to $3.3\\times10^{-14}$)",
            ha="center", fontsize=6.2, color=OKABE["blue"])
    ax.legend(loc="upper left", fontsize=6.0)
    ax.set_title("common offset $b\\,x_i$", fontsize=7.6)
    panel_label(ax, "b")

    # (c) lambda*(B) and slack collapse ------------------------------------
    ax = axes[2]
    B = [f(r["budget"]) for r in sweep]
    lam = [f(r["dual_shadow_price"]) for r in sweep]
    fd = [f(r["finite_diff_minus_dcost_dB"]) for r in sweep]
    unc = f(sweep[0]["unconstrained_sum"])
    ax.plot(B, lam, "-o", ms=3.2, lw=1.0, color=OKABE["blue"], label="optimality-condition price $p(B)$")
    ax.plot(B, fd, "s", ms=3.6, mfc="none", mec=OKABE["red"], mew=0.8,
            label="$-\\,\\mathrm{d}V^*/\\mathrm{d}B$ (finite diff.)")
    ax.axvline(unc, color="0.5", lw=0.8, ls=":")
    ax.axvspan(unc, max(B) * 1.02, color="0.92")
    ax.text(unc * 1.04, 0.25, "slack:\nprice $=0$", fontsize=6.4, color="0.35")
    ax.set_xlabel("global budget $B$")
    ax.set_ylabel("price $p$")
    ax.set_xlim(min(B) * 0.9, max(B) * 1.02)
    ax.legend(loc="upper right", fontsize=6.0)
    ax.set_title("price versus budget", fontsize=7.6)
    panel_label(ax, "c")

    save(fig, "F2_dual")


# ----------------------------------------------------------------------------
# F3 — record window
# ----------------------------------------------------------------------------
def fig_window() -> None:
    summ = read_csv(RES / "DE_window" / "lambda_summary.csv")
    lam = [f(r["lambda"]) for r in summ]
    rsf = [f(r["rs_pass_fraction"]) for r in summ]
    neg = -1.0 / 8000.0
    LT = 1e-5

    fig, axes = plt.subplots(1, 3, figsize=(7.0, 2.6), width_ratios=[1.25, 0.62, 1.1])
    fig.subplots_adjust(left=0.075, right=0.99, top=0.86, bottom=0.2, wspace=0.42)

    # (a) sampled pass fraction and the exact window -----------------------------
    ax = axes[0]
    ax.set_xscale("symlog", linthresh=LT)
    ax.axvspan(neg, 3.0, color="#dff0e4", zorder=0)
    ax.axvspan(3.0, 3.4, color="#9fd6b4", zorder=0)
    ax.plot(lam, rsf, "o-", ms=2.8, lw=0.9, color="0.35")
    ax.axhline(0.8, color="0.6", lw=0.7, ls=":")
    ax.text(-25, 0.84, "gate: 10 of 12 seeds", fontsize=6.0, color="0.4")
    ax.text(3e-3, 0.5, "certified\ninside", fontsize=6.6, ha="center", color=OKABE["green"])
    ax.set_xlabel("$\\lambda$  (carrier units; symlog)")
    ax.set_ylabel("fraction passing seed predicate")
    ax.set_ylim(-0.06, 1.1)
    ax.set_xticks([-10, -1e-3, 0, 1e-3, 1, 100])
    ax.set_title("sampled sweep and exact window", fontsize=7.6)
    panel_label(ax, "a")

    # (b) certified positive endpoints ------------------------------------------
    ax = axes[1]
    brackets = [("$N=32$", 1.3, 1.7), ("$N=64$", 3.0, 3.4), ("$N=128$", 5.0, 6.25)]
    for i, (lab, lo, hi) in enumerate(brackets):
        ax.plot([lo, hi], [i, i], lw=4, color=OKABE["green"], solid_capstyle="butt")
    ax.plot([3.0, 3.4], [1.35, 1.35], lw=2, color="0.45", solid_capstyle="butt")
    ax.text(3.2, 1.6, "eternal $u_\\infty$", fontsize=5.8, ha="center", color="0.3")
    ax.set_yticks(range(3))
    ax.set_yticklabels([b[0] for b in brackets], fontsize=6.6)
    ax.set_ylim(-0.6, 2.6)
    ax.set_xlim(0, 7)
    ax.set_xlabel("certified bracket for $\\lambda_+$")
    ax.set_title("positive endpoint", fontsize=7.6)
    panel_label(ax, "b")

    # (c) coincidence ratio: sampled medians and certified bounds ----------------
    ax = axes[2]
    Rl, Rv = [], []
    for r in summ:
        if r["rs_lambda_pass"] == "True" and f(r["lambda"]) != 0.0:
            try:
                Rv.append(f(r["median_lambda_to_matter_at_first_record"]))
                Rl.append(f(r["lambda"]))
            except ValueError:
                pass
    ax.set_xscale("symlog", linthresh=LT)
    ax.set_yscale("log")
    ax.plot(Rl, Rv, "o", ms=3.0, color="0.35")
    ax.axhline(425 / 8, color=OKABE["green"], lw=0.9, ls="--")
    ax.text(-1.2e-4, 425 / 8 * 1.6, "upper bound $425/8$ (all seeds)", fontsize=5.9, color="0.25")
    ax.add_patch(plt.Rectangle((3.0, 3 / 8), 0.4, 425 / 8 - 3 / 8, color=OKABE["green"], alpha=0.8, lw=0))
    ax.axhline(1.0, color="0.6", lw=0.7, ls=":")
    ax.set_ylim(1e-7, 600)
    ax.set_xticks([-1e-4, 0, 1e-4, 1e-2, 1])
    ax.set_xlabel("$\\lambda$  (inside the window; symlog)")
    ax.set_ylabel("$R=|\\lambda|/\\rho_m(a_{\\rm rec})$", labelpad=1)
    ax.set_title("coincidence ratio at first record", fontsize=7.6)
    panel_label(ax, "c")

    save(fig, "F3_window")


# ----------------------------------------------------------------------------
# F4 — finite budget versus limit (lattice model)
# ----------------------------------------------------------------------------
def fig_orbits() -> None:
    rows = read_csv(OUT / "data" / "orbit_traces.csv")
    tr: dict[tuple[str, float], list[tuple[int, float]]] = {}
    for r in rows:
        tr.setdefault((r["family"], f(r["value"])), []).append((int(r["n"]), f(r["max_residual"])))

    fig, axes = plt.subplots(1, 2, figsize=(7.0, 2.7), sharey=True)
    fig.subplots_adjust(left=0.085, right=0.985, top=0.85, bottom=0.18, wspace=0.08)
    panels = [
        (axes[0], "offset", [(-8, "$-8$ (passes at 60)"), (-5, "$-5$"), (-3, "$-3$"), (10, "$+10$")],
         "background offsets at $\\kappa=0.3$"),
        (axes[1], "kappa", [(10, "$\\kappa=10$"), (15, "$\\kappa=15$"), (20, "$\\kappa=20$"), (30, "$\\kappa=30$")],
         "couplings at zero offset"),
    ]
    cols = [OKABE["grey"], OKABE["blue"], OKABE["orange"], OKABE["green"]]
    for ax, fam, cases, title in panels:
        ax.axvspan(0, 60, color="0.93", zorder=0)
        ax.axhline(1e-8, color="0.35", lw=0.8, ls="--")
        for (v, lab), col in zip(cases, cols):
            pts = tr[(fam, float(v))]
            ls = (0, (4, 2)) if (fam, v) == ("kappa", 30) else "-"
            ax.plot([n for n, _ in pts], [max(x, 1e-17) for _, x in pts], lw=1.2, color=col, label=lab, ls=ls)
        ax.set_yscale("log")
        ax.set_xlim(0, 400)
        ax.set_ylim(1e-17, 30)
        ax.set_xlabel("update $n$")
        ax.set_title(title, fontsize=7.8)
        if fam == "offset":
            ax.legend(loc="upper right", fontsize=6.3)
        else:
            ax.legend(loc="lower left", bbox_to_anchor=(0.15, 0.17), fontsize=6.3)
        ax.text(30, 1e-12, "60-update\nbudget", ha="center", fontsize=6.2, color="0.35")
    axes[0].text(395, 2.2e-8, "tolerance $10^{-8}$", ha="right", fontsize=6.2, color="0.35")
    axes[0].set_ylabel("largest of the four residuals")
    axes[1].text(395, 0.04, "$\\kappa=20,30$: bounded two-cycles", ha="right", fontsize=6.2, color="0.25")
    axes[1].text(215, 3e-6, "$\\kappa=15$ passes from $n\\approx176$", fontsize=6.2, color="0.25")
    panel_label(axes[0], "a")
    axes[1].text(-0.03, 1.06, "b", transform=axes[1].transAxes, fontsize=10, fontweight="bold", va="top")
    save(fig, "F4_orbits")

# ----------------------------------------------------------------------------
# F5 — measure probe
# ----------------------------------------------------------------------------
def fig_measure() -> None:
    base_dir = RES / "math_review_2026-10-01"
    variants = {"base": "base_measure_verdicts.csv", "N32": "N32_measure_verdicts.csv",
                "N128": "N128_measure_verdicts.csv", "dc2": "delta_c_2p0_measure_verdicts.csv"}
    tabs = {k: {r["measure_id"]: r for r in read_csv(base_dir / v)} for k, v in variants.items()}
    rows = tabs["base"]
    order = ["M1_flat_lambda", "M2_flat_log_lambda", "M3_flat_lambda_times_N_rec",
             "M4_flat_lambda_times_f_coll", "M5_flat_log_lambda_times_N_rec"]
    labels = ["M1  flat $d\\lambda$", "M2  flat $d\\log\\lambda$",
              "M3  $d\\lambda\\times N_{\\rm rec}$", "M4  $d\\lambda\\times f_{\\rm coll}$",
              "M5  $d\\log\\lambda\\times N_{\\rm rec}$"]
    linear = [True, False, True, True, False]

    fig, axes = plt.subplots(1, 2, figsize=(7.0, 2.65))
    fig.subplots_adjust(left=0.16, right=0.98, top=0.86, bottom=0.2, wspace=0.5)

    # (a) induced log10 R intervals -----------------------------------------
    ax = axes[0]
    top = f(rows[order[0]]["top_log10R"])
    ax.axvspan(top - 1, top, color="#fff0c2", zorder=0)
    ax.text(top - 0.5, 4.55, "top\ndecade", fontsize=6.0, ha="center", va="center", color="0.4")
    for i, (mid, lin) in enumerate(zip(order, linear)):
        r = rows[mid]
        q05, med, q95 = f(r["log10R_q05"]), f(r["log10R_median"]), f(r["log10R_q95"])
        col = OKABE["blue"] if lin else OKABE["orange"]
        y = len(order) - 1 - i
        ax.plot([q05, q95], [y, y], lw=2.4, color=col, solid_capstyle="butt")
        ax.plot(med, y, "o", ms=4.2, color=col, mec="black", mew=0.4)
        ax.text(top + 0.12, y, f"$P_{{\\rm top}}={f(r['p_R_within_one_decade_top']):.2f}$",
                fontsize=6.2, va="center", color="0.25")
    ax.set_yticks(range(len(order)))
    ax.set_yticklabels(labels[::-1], fontsize=6.8)
    ax.set_xlabel("$\\log_{10} R$ at first record  (5–95% interval, median)")
    ax.set_xlim(-6.2, 2.6)
    ax.set_ylim(-0.6, len(order) - 0.2)
    ax.set_title("no declared class concentrates $R$ (base run)", fontsize=7.6)
    panel_label(ax, "a")

    # (b) epoch ratios, base and robustness variants --------------------------
    ax = axes[1]
    marks = {"base": ("o", 4.6), "N32": ("^", 3.4), "N128": ("v", 3.4), "dc2": ("D", 2.8)}
    for i, (mid, lin) in enumerate(zip(order, linear)):
        col = OKABE["blue"] if lin else OKABE["orange"]
        r = rows[mid]
        q05, med, q95 = (f(r["epoch_ratio_q05"]), f(r["epoch_ratio_median"]), f(r["epoch_ratio_q95"]))
        ax.errorbar(i - 0.12, med, yerr=[[med - q05], [q95 - med]], fmt="o", ms=4.6,
                    color=col, capsize=2.5, lw=1.0, mec="black", mew=0.4)
        for j, k in enumerate(["N32", "N128", "dc2"]):
            m, ms = marks[k]
            ax.plot(i + 0.08 + 0.08 * j, f(tabs[k][mid]["epoch_ratio_median"]), m, ms=ms, color=col,
                    mec="black", mew=0.3)
    ax.axhline(1.0, color="0.45", lw=0.9, ls="--")
    ax.text(4.4, 0.62, "first record at $\\lambda$-domination", fontsize=6.0, ha="right", color="0.35")
    ax.set_yscale("log")
    ax.set_ylim(0.5, 100)
    ax.set_xticks(range(len(order)))
    ax.set_xticklabels(["M1", "M2", "M3", "M4", "M5"])
    ax.set_ylabel("$a_\\lambda / a_{\\rm rec}$")
    ax.set_title("epoch ratio at first record", fontsize=7.6)
    hndl = [plt.Line2D([], [], marker="o", ls="", color=OKABE["blue"], label="linear-class prior"),
            plt.Line2D([], [], marker="o", ls="", color=OKABE["orange"], label="log-class prior"),
            plt.Line2D([], [], marker="^", ls="", color="0.5", label="$N=32$"),
            plt.Line2D([], [], marker="v", ls="", color="0.5", label="$N=128$"),
            plt.Line2D([], [], marker="D", ls="", ms=3, color="0.5", label="$\\delta_c=2$")]
    ax.legend(handles=hndl, loc="upper left", fontsize=5.9, ncol=2, markerscale=0.7)
    panel_label(ax, "b")

    save(fig, "F5_measure")


# ----------------------------------------------------------------------------
# F6 — real-data audits
# ----------------------------------------------------------------------------
def fig_audits() -> None:
    chart = read_csv(RES / "DE_audit" / "B1b_chart_comparison.csv")
    cal = read_csv(RES / "DE_audit" / "B2_calibration.csv")

    z = [f(r["z"]) for r in chart]
    wfl = [f(r["w_fluid"]) for r in chart]
    dh = [f(r["Delta_H_additive"]) for r in chart]
    zc = 0.4388443779066967  # exact CPL root for the frozen best-fit decimals

    nulls = sorted(f(r["staging_score"]) for r in cal if r["kind"] == "lcdm_null")
    cutoff = nulls[-1]  # finite-rank cutoff for n=20, alpha=1/20: the largest null score
    S_real = 9.629761049875103
    eps = [0.01, 0.02, 0.05, 0.1, 0.2]
    inj: dict[tuple[str, float], list[float]] = {}
    for r in cal:
        if r["kind"] != "lcdm_null":
            inj.setdefault((r["class"], f(r["epsilon"])), []).append(f(r["staging_score"]))
    rate = {c: [sum(x > cutoff for x in inj[(c, e)]) / len(inj[(c, e)]) for e in eps]
            for c in ("sn_localized", "bao_localized")}

    fig = plt.figure(figsize=(7.0, 2.75))
    gs = fig.add_gridspec(2, 3, width_ratios=[1.15, 1.0, 0.7], hspace=0.12, wspace=0.55,
                          left=0.075, right=0.985, top=0.88, bottom=0.17)
    axw = fig.add_subplot(gs[0, 0])
    axd = fig.add_subplot(gs[1, 0], sharex=axw)
    axp = fig.add_subplot(gs[:, 1])
    axv = fig.add_subplot(gs[:, 2])

    # (a) one history, two charts (stacked, shared redshift axis) ----------------
    axw.plot(z, wfl, lw=1.2, color=OKABE["blue"])
    axw.axhline(-1.0, color="0.45", lw=0.8, ls="--")
    axw.axvline(zc, color=OKABE["red"], lw=0.7, ls=":")
    axw.plot(zc, -1.0, "o", ms=4, color=OKABE["red"], zorder=5)
    axw.text(zc + 0.08, -0.86, f"$w=-1$ at $z={zc:.4f}$", fontsize=6.2, color="0.25")
    axw.set_ylabel("$w(z)$")
    axw.tick_params(labelbottom=False)
    axw.set_title("one expansion history, two charts", fontsize=7.6)
    axd.plot(z, dh, lw=1.2, color=OKABE["blue"])
    axd.axvline(zc, color=OKABE["red"], lw=0.7, ls=":")
    axd.set_ylim(0.45, 0.8)
    axd.set_ylabel("$\\Delta_H(z)$")
    axd.set_xlabel("redshift $z$")
    axd.text(2.45, 0.73, "positive, smooth", fontsize=6.2, ha="right", color="0.25")
    fig.text(0.008, 0.955, "a", fontsize=10, fontweight="bold", va="top")

    # (b) power under the finite-rank cutoff ----------------------------------
    ax = axp
    ax.plot(eps, rate["sn_localized"], "-o", ms=3.6, lw=1.0, color=OKABE["blue"], label="SN-localized tilt")
    ax.plot(eps, rate["bao_localized"], "-s", ms=3.6, lw=1.0, color=OKABE["orange"], label="BAO-localized tilt")
    ax.axhline(0.8, color="0.45", lw=0.8, ls="--")
    ax.text(0.0105, 0.72, "rate $0.8$", fontsize=6.2, color="0.4")
    ax.set_xscale("log")
    ax.set_xlabel("injected distortion $\\varepsilon$")
    ax.set_ylabel("detection rate (20 mocks each)")
    ax.set_ylim(-0.05, 1.1)
    ax.legend(loc="upper left", fontsize=6.2)
    ax.set_title("staging audit: power", fontsize=7.6)
    panel_label(ax, "b")

    # (c) real score against the null ------------------------------------------
    ax = axv
    ax.hist(nulls, bins=10, orientation="horizontal", color="0.82", edgecolor="0.55", lw=0.5)
    ax.axhline(cutoff, color="0.3", lw=0.9, ls="--")
    ax.text(0.97, cutoff + 0.15, "cutoff", fontsize=6.0, color="0.3",
            transform=ax.get_yaxis_transform(), ha="right")
    ax.plot([0.5], [S_real], "*", ms=10, color=OKABE["red"], zorder=5, transform=ax.get_yaxis_transform())
    ax.text(0.04, S_real + 0.45, "data: $S=9.63$", fontsize=6.2, color="0.2", transform=ax.get_yaxis_transform())
    ax.set_xlabel("null count")
    ax.set_ylabel("staging score $S$")
    ax.set_ylim(0, 11.4)
    ax.set_title("staging audit: verdict", fontsize=7.6)
    panel_label(ax, "c")

    save(fig, "F6_audits")


if __name__ == "__main__":
    fig1()
    fig2()
    fig_window()
    fig_orbits()
    fig_measure()
    fig_audits()
    print("all figures written to", OUT)
