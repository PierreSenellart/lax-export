"""Tests of the parts of lax_export that need neither Lean nor git."""
import os
import textwrap

import pytest
import yaml

import lax_export as le


def test_rewriter_moves_the_prefix_and_root_declarations():
    rw = le.rewriter("Lib", "Lax1Proofs.Lib")
    assert rw("import Lib.A\nnamespace Lib\nopen Lib.B in\n") == \
        "import Lax1Proofs.Lib.A\nnamespace Lax1Proofs.Lib\nopen Lax1Proofs.Lib.B in\n"
    assert rw("def _root_.Lib.X.y := 1") == "def _root_.Lax1Proofs.Lib.X.y := 1"
    assert rw("Library.Lib Libx Lib' Other.Lib") == "Library.Lib Libx Lib' Other.Lib"


def test_generated_constants_are_attributed_to_their_declaration():
    ranged = {"Lib.Foo": {}, "Lib.Foo.bar": {}}
    assert le.attribute_generated("Lib.Foo.rec", ranged) == "Lib.Foo"
    assert le.attribute_generated("Lib.Foo.bar.match_1.eq_1", ranged) == "Lib.Foo.bar"
    assert le.attribute_generated("Other.thing", ranged) is None


def test_is_url():
    assert le.is_url("https://github.com/x/y")
    assert le.is_url("git@github.com:x/y.git")
    assert not le.is_url("/home/me/lib")
    assert not le.is_url("../lib")


def test_manifest_dump_quotes_scalars_and_uses_literal_blocks():
    text = le.dump_manifest({"specVersion": "1", "id": "lax-7", "title": "T",
                             "authors": [{"name": "A", "orcid": "0000-0002-1825-0097"}],
                             "bibEntries": ["@misc{k,\n  title = {x}\n}\n"],
                             "unlisted": True, "issue": {"repositoryId": 1, "number": 2}})
    assert 'orcid: "0000-0002-1825-0097"' in text
    assert "- |\n  @misc{k," in text
    assert "unlisted: true" in text
    assert yaml.safe_load(text)["issue"] == {"repositoryId": 1, "number": 2}


def test_fully_built_needs_oleans_and_ileans_newer_than_sources(tmp_path):
    lib = tmp_path / "lib"
    (lib / "L").mkdir(parents=True)
    (lib / "L" / "A.lean").write_text("def a := 1\n")
    build = lib / ".lake" / "build" / "lib" / "lean" / "L"
    build.mkdir(parents=True)
    mathlib = lib / ".lake" / "packages" / "mathlib" / ".lake" / "build" / "lib" / "lean"
    mathlib.mkdir(parents=True)
    (mathlib / "Mathlib.olean").write_text("")
    assert not le.fully_built(str(lib), "L")
    (build / "A.olean").write_text("")
    (build / "A.ilean").write_text("")
    assert le.fully_built(str(lib), "L")
    os.utime(lib / "L" / "A.lean", (10 ** 10, 10 ** 10))      # source newer than the build
    assert not le.fully_built(str(lib), "L")


def _config(tmp_path, body):
    path = tmp_path / "export.yaml"
    path.write_text(textwrap.dedent(body))
    return str(path)


def test_config_loads_the_example(tmp_path):
    cfg = le.load_config(os.path.join(le.HERE, "examples", "np-core.yaml"))
    assert cfg["prefix"] == "DescriptiveComplexity"
    assert "DescriptiveComplexity.SAT_NP_complete" in cfg["target"]
    assert cfg["manifest"]["title"].startswith("Descriptive complexity")
    assert cfg["out"] == os.path.join(le.HERE, "examples")


def test_config_requires_the_essentials_and_rejects_unknown_keys(tmp_path):
    with pytest.raises(SystemExit, match="`targets` is required"):
        le.load_config(_config(tmp_path, """
            library: .
            prefix: L
            manifest: {title: t}
            abstract: a
            """))
    with pytest.raises(SystemExit, match="unknown keys"):
        le.load_config(_config(tmp_path, """
            library: .
            prefix: L
            targets: [L.x]
            manifest: {title: t}
            abstract: a
            bogus: 1
            """))
    with pytest.raises(SystemExit, match="not in the Lax archive's schema"):
        le.load_config(_config(tmp_path, """
            library: .
            prefix: L
            targets: [L.x]
            manifest: {title: t, license: MIT}
            abstract: a
            """))
    with pytest.raises(SystemExit, match="each author"):
        le.load_config(_config(tmp_path, """
            library: .
            prefix: L
            targets: [L.x]
            manifest: {title: t, authors: [{name: a, email: x}]}
            abstract: a
            """))


def test_config_paths_are_relative_to_the_file(tmp_path):
    (tmp_path / "abs.md").write_text("The abstract.\n")
    cfg = le.load_config(_config(tmp_path, """
        library: ../lib
        prefix: L
        targets: [L.x]
        manifest: {title: t}
        abstract_file: abs.md
        out: sub
        """))
    assert cfg["library"] == os.path.normpath(os.path.join(str(tmp_path), "../lib"))
    assert cfg["abstract"] == "The abstract.\n"
    assert cfg["out"] == os.path.join(str(tmp_path), "sub")


def test_licenses_apache_mit_and_copyleft(tmp_path):
    apache = open(os.path.join(le.HERE, "LICENSE"), encoding="utf-8").read()
    for name, text, notice, refused in (
            ("apache", apache, False, False),
            ("mit", "MIT License\n\nPermission is hereby granted, free of charge, to any person\n", True, False),
            ("gpl", "GNU GENERAL PUBLIC LICENSE\nVersion 3, 29 June 2007\n", False, True)):
        src = tmp_path / name / "src"
        out = tmp_path / name / "out"
        src.mkdir(parents=True)
        (src / "LICENSE").write_text(text)
        if refused:
            with pytest.raises(SystemExit, match="neither Apache 2.0 nor a permissive"):
                le.write_licenses(str(src), str(out), "2026 Someone", False)
            le.write_licenses(str(src), str(out), "2026 Someone", True)
        else:
            le.write_licenses(str(src), str(out), "2026 Someone", False)
        written = (out / "LICENSE").read_text()
        assert written.startswith(apache.rstrip("\n")[:40])
        assert written.rstrip().endswith("Copyright 2026 Someone")
        assert (out / "NOTICE").exists() == (notice or refused)


def test_existing_manifest(tmp_path):
    assert le.existing_manifest(str(tmp_path)) == {}
    (tmp_path / "manifest.yaml").write_text('id: lax-5\nissue:\n  repositoryId: 1\n  number: 2\n')
    assert le.existing_manifest(str(tmp_path))["issue"]["number"] == 2
