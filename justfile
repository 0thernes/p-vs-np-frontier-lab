# Task runner for p-vs-np-frontier-lab (Build Standard v1.2.0, A31 & B01)
set shell := ["bash", "-euo", "pipefail", "-c"]

default:
    @just --list

setup:
    python3 -m pip install -r requirements.lock.txt

lean:
    cd lean && lake build && lake env lean VerifyAxioms.lean

test:
    python3 -m pytest -v tests/test_all.py

lint:
    python3 -m ruff check experiments/ scripts/ tests/ || true
    python3 -m mypy --ignore-missing-imports scripts/ tests/ || true

axioms:
    python3 scripts/check_readme_axioms.py

site:
    python3 scripts/build_blueprint.py

reproduce:
    python3 -m pytest -v tests/test_all.py
    python3 scripts/check_readme_axioms.py
    python3 scripts/build_blueprint.py
    sha256sum -c MANIFEST.sha256
    bash scripts/audit-repo.sh .

audit:
    bash scripts/audit-repo.sh .
