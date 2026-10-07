# Appendix D — Review record

**External review (June 2026).** Before the first release, the package was given to an external reviewer with the frozen
repository archive and seven questions: whether a demarcation is a legitimate contribution, whether the models' outputs
are built in, whether the real-data firing reflects the instrument or a known systematic and whether the change of
injected alternatives amounted to tuning, whether an imported result could carry its grade without local reproduction,
whether the treatment of coincidence sharpens or relocates the problem, whether any observed cosmological value entered a
model, and what the overall grade should be. According to the review record, the reviewer re-ran the model and measure
test suites, asked for imported results to be marked as such and for physical wording to be scoped to the models, and
regarded the value question as unresolved by the package. The present version takes the same view of the value question.

**Mathematical audit (October 2026).** Every claim was then checked against its proof or computation, and the supporting
mathematics was rebuilt where needed: the closure-price theorem was mechanized in general form; the record window was
proved as an exact continuum statement; the lattice model's orbits were classified exactly; the measure pushforward was
recomputed on the joint distribution of parameter values and seeds; the staging threshold was given a conservative rank
rule; and the cross-paper imports were re-examined against their current sources. This audit was carried out by the
author's own tooling, combining Lean kernel checking, independent reimplementation and adversarial self-review; it is not
an independent human review. Appendix E lists the resulting differences from the first version.
