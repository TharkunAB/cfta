# Train preferences between valid hole fits

The existing corpus scorer learns how often tokens occur in source code.
This experiment learns which complete fit to prefer among the alternatives
for one hole. Each training case has a preferred program and a fixed pool
of programs that GHC has already checked for that hole.

The objective is the mean conditional log-likelihood, with an L2 prior.
Each hole has its own normalizer. A shared set of parent-position-token
corrections adjusts the existing corpus score. Merely normalizing each
pool would not change its order. Training changes the shared corrections.

The implementation prepares sparse feature counts once. It uses stable
log-sum-exp for each pool and the existing L-BFGS fitter. Exact duplicate
programs have one probability. Different programs that share features
retain separate probability mass. No preferred program is inserted into
a pool automatically.

A preference file includes its original corpus counts and the corrections.
The plugin loads it through the existing `model=FILE` option. With no
corrections, it uses the existing scorer directly. GHC still checks each
proposed program. A preference file does not change structural term ranks.

This is a conditional-ranking extension of the existing CFTA training
work. The context features follow the parent annotation used by the corpus
scorer. It does not reproduce PHOG's context-navigation learner or claim
that the paper experiments improved real hole fits.

The work depends on PRs 194, 195, 196, and the training-report change.
The temporary `integration/hole-fit-training` base records these dependencies.
The preference PR contains only the changes after that base.

Commands, file examples, validation, and measurements follow below when
the implementation is complete.
