"""The integration test: export the fixture library, build what comes out,
and check it the way the Lax archive will. Needs the fixture built
(`lake build` in tests/fixture) and `lean`, `lake` on PATH."""
import glob
import json
import os
import shutil
import subprocess
import sys

import pytest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FIXTURE = os.path.join(ROOT, "tests", "fixture")
ID = "900001"

pytestmark = pytest.mark.skipif(
    not os.path.isfile(os.path.join(FIXTURE, ".lake", "build", "lib", "lean", "Fixture", "Main.olean")),
    reason="the fixture is not built (run `lake build` in tests/fixture)")


def run(cmd, cwd, env=None):
    r = subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True)
    assert r.returncode == 0, f"{' '.join(cmd)}\n{r.stdout[-3000:]}\n{r.stderr[-3000:]}"
    return r


def seed_packages(package_dir, extra_path=None):
    """Point the package's Lake workspace at the fixture's dependency
    checkouts, so that building it needs no clone of Mathlib."""
    src = json.load(open(os.path.join(FIXTURE, "lake-manifest.json")))
    keep = [p for p in src["packages"]]
    manifest = dict(src, name=os.path.basename(package_dir), packages=keep)
    if extra_path:
        manifest["packages"] = [{"type": "path", "dir": extra_path[0], "name": extra_path[1],
                                 "manifestFile": "lake-manifest.json", "inherited": False,
                                 "configFile": "lakefile.toml"}] + keep
    json.dump(manifest, open(os.path.join(package_dir, "lake-manifest.json"), "w"), indent=2)
    pk = os.path.join(package_dir, ".lake", "packages")
    os.makedirs(pk, exist_ok=True)
    for p in keep:
        dst = os.path.join(pk, p["name"])
        if not os.path.exists(dst):
            os.symlink(os.path.realpath(os.path.join(FIXTURE, ".lake", "packages", p["name"])), dst)


@pytest.fixture(scope="module")
def submission(tmp_path_factory):
    out = tmp_path_factory.mktemp("sub")
    # what `lax init` leaves: a manifest with the id, and what `lax submit` adds
    (out / "manifest.yaml").write_text(
        f'specVersion: "1"\nid: lax-{ID}\nleanVersion: "v4.33.0"\n'
        f'mathlibVersion: "db584cd6d46c92f209a44c0f1c829460d327499d"\ntitle: sub\nauthors: []\n'
        f'bibEntries: []\nissue:\n  repositoryId: 1320232165\n  number: 1\n')
    (out / "concepts" / f"Lax{ID}").mkdir(parents=True)
    (out / "concepts" / f"Lax{ID}" / "Main.lean").write_text(
        f"import Mathlib.Logic.Basic\n\n/-!\n---\ntitle: The fixture's theorem\ntype: theorem\n---\n"
        f"Stands in for a concept.\n-/\n\nnamespace Lax{ID}.Main\n\naxiom holds : 1 + 1 = 2\n\nend Lax{ID}.Main\n")
    (out / "proofs" / f"Lax{ID}Proofs").mkdir(parents=True)
    (out / "proofs" / f"Lax{ID}Proofs" / "Bridge.lean").write_text(
        f"import Lax{ID}.Main\nimport Lax{ID}Proofs.Fixture.Main\n\nnamespace Lax{ID}Proofs\n\n"
        f"/--\n---\nconclusion: Lax{ID}.Main.holds\n---\nFrom the vendored library.\n-/\n"
        f"theorem holds : 1 + 1 = 2 := by\n  have := Lax{ID}Proofs.Fixture.rooted\n  rfl\n\nend Lax{ID}Proofs\n")
    cache = tmp_path_factory.mktemp("cache")
    run([sys.executable, os.path.join(ROOT, "lax_export.py"), os.path.join(FIXTURE, "export.yaml"),
         "--out", str(out), "--cache", str(cache), "--no-environment-check"], ROOT)
    return out


def test_layout_and_manifest(submission):
    manifest = open(submission / "manifest.yaml").read()
    assert f'id: "lax-{ID}"' in manifest and 'title: "lax-export fixture"' in manifest
    assert "issue:" in manifest and "number: 1" in manifest          # what lax submit wrote survives
    assert (submission / "LICENSE").read_text().rstrip().endswith("Copyright 2026 Pierre Senellart")
    assert not (submission / "NOTICE").exists()                     # the fixture is Apache 2.0 too
    assert (submission / "abstract.md").read_text().startswith("A fixture for")
    roots = (submission / "proofs" / f"Lax{ID}Proofs.lean").read_text()
    assert f"import Lax{ID}Proofs.Bridge" in roots
    assert (submission / "concepts" / f"Lax{ID}.lean").read_text() == f"import Lax{ID}.Main\n"


def test_slicing(submission):
    vend = submission / "proofs" / f"Lax{ID}Proofs" / "Fixture"
    written = sorted(os.path.relpath(f, vend) for f in glob.glob(str(vend / "**" / "*.lean"), recursive=True))
    assert "Extra.lean" not in written                                # imported, never reached
    assert "Syntax.lean" in written and "Command.lean" in written     # notation modules, in full
    basic = (vend / "Basic.lean").read_text()
    assert "unused_lemma" not in basic
    assert "instance : CoeFun" in basic and "theorem box_apply" in basic   # silent declarations kept
    assert "import Lax900001Proofs.Fixture.Extra" not in basic
    foreign = (vend / "Foreign.lean").read_text()
    assert f"def _root_.Lax{ID}Proofs.Foreign.Nat.fixtureDouble" in foreign
    assert f"export Lax{ID}Proofs.Foreign.Nat (fixtureDouble" in foreign  # field notation alias
    assert f"deriving instance DecidableEq for Lax{ID}Proofs.Foreign.Nat.FixtureColor" in foreign
    assert f"instance _root_.Lax{ID}Proofs.Foreign.Nat.instInhabitedFixtureColor" in foreign
    assert "def fixtureSeven : Nat :=" in foreign                      # the expanded command
    assert "mk_const fixtureSeven" not in foreign                    # the invocation is gone


def test_build_and_check(submission):
    seed_packages(str(submission / "concepts"))
    seed_packages(str(submission / "proofs"), ("../concepts", f"Lax{ID}"))
    run(["lake", "build"], str(submission / "concepts"))
    run(["lake", "build"], str(submission / "proofs"))
    lean_path = ":".join(sorted(set(
        os.path.dirname(os.path.realpath(d)) if False else d
        for d in glob.glob(str(submission / "*" / ".lake" / "build" / "lib" / "lean"))
        + glob.glob(os.path.join(FIXTURE, ".lake", "packages", "*", ".lake", "build", "lib", "lean")))))
    env = dict(os.environ, LEAN_PATH=lean_path)
    r = run(["lean", "--run", os.path.join(ROOT, "Check.lean"), f"Lax{ID}Proofs",
             f"Lax{ID}Proofs.Fixture.main", f"Lax{ID}Proofs.Fixture.rooted", f"Lax{ID}Proofs.holds"],
            str(submission / "proofs"), env)
    assert "outside prefix: 0" in r.stdout, r.stdout
    assert "[propext, Classical.choice, Quot.sound]" in r.stdout or "[]" in r.stdout
