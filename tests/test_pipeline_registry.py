"""
Tests for `amaya.preprocessing.pipeline.build_registry` (plan step 3):

(a) registration order is deterministic;
(b) each descriptor's `config_flag` names a real `OptimizationsConfig` attribute;
(c) `-O all` (every `OptimizationsConfig` flag enabled) yields all 17 non-finalize passes;
(d) every user-visible registry name appears in `run-amaya.py`'s `opt_to_config_field`.
"""
import ast
import re
from pathlib import Path

from amaya.config import OptimizationsConfig, SolverConfig
from amaya.preprocessing.pipeline import Pass_Tier, build_registry


REPO_ROOT = Path(__file__).resolve().parent.parent


def _load_opt_to_config_field() -> dict:
    """`run-amaya.py` is a top-level script (no `if __name__` guard, calls `sys.exit`), so it
    cannot be imported directly in a test process. Extract the `opt_to_config_field` dict literal
    from its source instead - it is a plain str->str mapping, safe to `ast.literal_eval`."""
    source = (REPO_ROOT / 'run-amaya.py').read_text()
    match = re.search(r'opt_to_config_field\s*=\s*(\{.*?\n\})', source, re.S)
    assert match is not None, 'could not find opt_to_config_field in run-amaya.py'
    return ast.literal_eval(match.group(1))


def _all_enabled_config() -> SolverConfig:
    solver_config = SolverConfig()
    for flag_name in vars(solver_config.optimizations):
        setattr(solver_config.optimizations, flag_name, True)
    return solver_config


def test_registration_order_is_deterministic():
    solver_config = _all_enabled_config()

    names_a = [d.name for d in build_registry(solver_config)]
    names_b = [d.name for d in build_registry(solver_config)]

    assert names_a == names_b
    assert len(names_a) == len(set(names_a)), 'duplicate pass name in the registry'


def test_every_config_flag_names_a_real_optimizations_config_attribute():
    solver_config = _all_enabled_config()
    valid_attrs = set(vars(OptimizationsConfig()))

    for descriptor in build_registry(solver_config):
        if descriptor.config_flag is not None:
            assert descriptor.config_flag in valid_attrs, \
                f'{descriptor.name}: unknown config flag {descriptor.config_flag!r}'


def test_all_optimizations_enabled_yields_the_17_non_finalize_passes():
    solver_config = _all_enabled_config()

    registry = build_registry(solver_config)
    non_finalize = [d for d in registry if d.tier != Pass_Tier.FINALIZE]

    assert len(non_finalize) == 17
    assert len(non_finalize) == len(set(d.name for d in non_finalize))


def test_default_config_only_registers_unconditional_and_default_true_passes():
    solver_config = SolverConfig()

    registry = build_registry(solver_config)

    for descriptor in registry:
        if descriptor.config_flag is not None:
            assert getattr(solver_config.optimizations, descriptor.config_flag) is True


def test_every_user_visible_registry_name_is_known_to_the_cli():
    # A user-visible pass is one gated by a config flag; the flag itself (not necessarily the
    # pass name) must be reachable via some `-O` option, since two passes can share one flag
    # (`model-reasoning` / `unconstrained-vars`, see OPTIMIZATION_PIPELINE.md §5.4).
    opt_to_config_field = _load_opt_to_config_field()
    reachable_flags = set(opt_to_config_field.values())
    solver_config = _all_enabled_config()

    for descriptor in build_registry(solver_config):
        if descriptor.tier == Pass_Tier.FINALIZE or descriptor.config_flag is None:
            continue
        assert descriptor.config_flag in reachable_flags, \
            f'{descriptor.name!r} is gated on {descriptor.config_flag!r}, which no -O flag reaches'


def test_shared_config_flag_covers_model_reasoning_and_unconstrained_vars():
    solver_config = _all_enabled_config()
    by_name = {d.name: d for d in build_registry(solver_config)}

    assert by_name['model-reasoning'].config_flag == 'reason_about_models'
    assert by_name['unconstrained-vars'].config_flag == 'reason_about_models'


def test_flatten_connectives_is_registered_unconditionally():
    solver_config = SolverConfig()  # every optional flag off, `flatten_connectives` included
    solver_config.optimizations.flatten_connectives = False

    registry = build_registry(solver_config)

    assert any(d.name == 'flatten-connectives' for d in registry)
